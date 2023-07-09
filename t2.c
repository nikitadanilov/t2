/* -*- C -*- */

/* See https://github.com/nikitadanilov/t2/blob/master/LICENCE for licencing information. */

#include <stdbool.h>
#include <assert.h>
#include <stdlib.h>
#include <stdarg.h>
#include <errno.h>
#include <string.h>
#include <stdio.h>
#include <ctype.h>
#include <stdatomic.h>
#include <signal.h>
#include <pthread.h>
#include <setjmp.h>
#include <limits.h>
#include <execinfo.h>
#include <stdalign.h>
#include <unistd.h>
#include <time.h>
#include <fcntl.h>
#define _LGPL_SOURCE
#define URCU_INLINE_SMALL_FUNCTIONS
#include <urcu/urcu-memb.h>
#include <urcu/rcuhlist.h>
#include "t2.h"
#include "config.h"

enum {
        MAX_TREE_HEIGHT =      10,
        MAX_TREE_TYPE   =    1024,
        MAX_NODE_TYPE   =    1024,
        MAX_ERR_CODE    =    1024,
        MAX_ERR_DEPTH   =      16,
        MAX_CACHELINE   =      64
};

/* @macro */

#define LIKELY(x)   __builtin_expect(!!(x), 1)
#define UNLIKELY(x) __builtin_expect(!!(x), 0)

#define MSG_PREP(_fmt)                          \
({                                              \
        static const struct msg_ctx __ctx = {   \
                .func = __func__,               \
                .file = __FILE__,               \
                .lineno = __LINE__,             \
                .fmt = (_fmt)                   \
        };                                      \
        &__ctx;                                 \
})
#define IMMANENTISE(fmt, ...) immanentise(MSG_PREP(fmt), __VA_ARGS__)
#if DEBUG
#define ASSERT(expr) (LIKELY(expr) ? (void)0 : IMMANENTISE("Assertion failed: %s", #expr))
#else
#define ASSERT(expr) ((void)sizeof((expr), 0))
#endif
#define EXPENSIVE_ASSERT(expr) ((void)0) /* ASSERT(expr) */
#define SOF(x) ((int32_t)sizeof(x))
#define ARRAY_SIZE(a)                           \
({                                              \
        SASSERT(IS_ARRAY(a));                   \
        (int)(sizeof(a) / sizeof(a[0]));        \
})
#define IS_ARRAY(x) (!__builtin_types_compatible_p(typeof(&(x)[0]), typeof(x)))
#define IS_IN(idx, array)                               \
({                                                      \
        SASSERT(IS_ARRAY(array));                       \
        ((unsigned long)(idx)) < ARRAY_SIZE(array);     \
})
#define COF(ptr, type, member) ((type *)((char *)(ptr) - (char *)(&((type *)0)->member)))
#define LOG(fmt, ...) llog(MSG_PREP(fmt) , ## __VA_ARGS__)
#define ERROR_INFO(errcode, fmt, a0, a1)                \
({                                                      \
        typeof(errcode) __errc = (int)(errcode);        \
        EDESCR(__errc, fmt, a0, a1);                    \
        __errc;                                         \
})
#define ERROR(errcode)  ERROR_INFO(errcode, "", 0, 0)
#define EPTR(errcode) ((void *)ERROR((int64_t)(errcode)))
#define ERRCODE(val) ((int)(intptr_t)(val))
#define EISERR(val) UNLIKELY((uint64_t)(val) >= (uint64_t)-MAX_ERR_CODE)
#define EISOK(val) (!EISERR(val))
#define EDESCR(err, fmt, a0, a1) edescr(MSG_PREP(fmt), err, (uint64_t)a0, (uint64_t)a1)

#define NOFAIL(expr)                            \
({                                              \
        int result = (expr);                    \
        ASSERT(result == 0);                    \
})

/* Returns the number of array elements that satisfy given criteria. */
#define COUNT(var, nr, ...)                             \
({                                                      \
        unsigned __nr = (nr);                           \
        unsigned var;                                   \
        unsigned count;                                 \
                                                        \
        for (count = var = 0; var < __nr; ++var) {      \
                if (__VA_ARGS__)                        \
                        ++count;                        \
        }                                               \
        count;                                          \
})

/*
 * Returns a conjunction (logical AND) of an expression evaluated over a range
 *
 * Declares an unsigned integer variable named "var" in a new scope and
 * evaluates user-supplied expression (the last argument) with "var" iterated
 * over successive elements of [0 .. NR - 1] range, while this expression
 * returns true. Returns true iff the whole range was iterated over.
 *
 * This function is useful for invariant checking.
 *
 * bool foo_invariant(const struct foo *f)
 * {
 *        return FORALL(i, ARRAY_SIZE(f->f_nr_bar), f->f_bar[i].b_count > 0);
 * }
 */
#define FORALL(var, nr, ...)                                    \
({                                                              \
        unsigned __nr = (nr);                                   \
        unsigned var;                                           \
                                                                \
        for (var = 0; var < __nr && ({ __VA_ARGS__ ; }); ++var) \
                ;                                               \
        var == __nr;                                            \
})

/*
 * Returns a disjunction (logical OR) of an expression evaluated over a range.
 *
 * bool haystack_contains(int needle)
 * {
 *         return EXISTS(i, ARRAY_SIZE(haystack), haystack[i] == needle);
 * }
 */
#define EXISTS(var, nr, ...) !FORALL(var, (nr), !(__VA_ARGS__))

/*
 * Reduces ("aggregates") given expression over an interval.
 *
 * @see http://en.wikipedia.org/wiki/Fold_(higher-order_function)
 *
 * Example uses
 *
 * sum = REDUCE(i, ARRAY_SIZE(a), 0, + a[i]);
 * product = REDUCE(i, ARRAY_SIZE(b), 1, * b[i]);
 */
#define REDUCE(var, nr, init, exp)              \
({                                              \
        unsigned __nr = (nr);                   \
        unsigned var;                           \
        typeof(init) __accum = (init);          \
                                                \
        for (var = 0; var < __nr; ++var) {      \
                __accum = __accum exp;          \
        }                                       \
        __accum;                                \
})

/*
 * Folds given expression over an interval.
 *
 * This is a generalised version of REDUCE().
 *
 * @see http://en.wikipedia.org/wiki/Fold_(higher-order_function)
 *
 * Example uses
 *
 * sum = FOLD(i, s, ARRAY_SIZE(a), 0, s + a[i]);
 * max = FOLD(i, m, ARRAY_SIZE(b), INT_MIN, MAX(m, a[i]));
 */
#define FOLD(var, accum, nr, init, exp)         \
({                                              \
        unsigned __nr = (nr);                   \
        unsigned var;                           \
        typeof(init) accum = (init);            \
                                                \
        for (var = 0; var < __nr; ++var) {      \
                accum = exp;                    \
        }                                       \
        accum;                                  \
})

#define SASSERT(cond) _Static_assert((cond), #cond)

#define SET0(obj)                               \
({                                              \
        SASSERT(!IS_ARRAY(obj));                \
        memset((obj), 0, sizeof *(obj));        \
})

#define IS0(obj) FORALL(i, sizeof *(obj), ((char *)obj)[i] == 0)

#define MAX(a, b)                               \
({                                              \
        typeof(a) __a = (a);                    \
        typeof(a) __b = (b);                    \
        __a > __b ? __a : __b;                  \
})

#define MIN(a, b)                               \
({                                              \
        typeof(a) __a = (a);                    \
        typeof(a) __b = (b);                    \
        __a < __b ? __a : __b;                  \
})

#define SLOT_DEFINE(s, n)                                               \
        struct t2_buf __key;                                            \
        struct t2_buf __val;                                            \
        struct slot s = { .node = n, .rec = { .key = &__key, .val = &__val } }

#define BUF_VAL(v) (struct t2_buf){ .nr = 1, .seg = { [0] = { .len = SOF(v), .addr = &(v) } } }

#define CINC(cnt) (++__t_counters.cnt)
#define CDEC(cnt) (--__t_counters.cnt)
#define CVAL(cnt) (__t_counters.cnt)
#define GVAL(cnt) (__g_counters.cnt)
#define CADD(cnt, d) (__t_counters.cnt += (d))
#define CMOD(cnt, d) ({ struct counter_var *v = &(__t_counters.cnt); v->sum += (d); v->nr++; })

#define SCALL(mod, method, ...)                         \
({                                                      \
        struct t2_storage *__stor = (mod)->stor;        \
        __stor->op->method(__stor , ##  __VA_ARGS__);   \
})

/* Is Parallel Programming Hard, And, If So, What Can You Do About It? */
#define ACCESS_ONCE(x)     (*(volatile typeof(x) *)&(x))
#define READ_ONCE(x)       ({ typeof(x) ___x = ACCESS_ONCE(x); ___x; })
#define WRITE_ONCE(x, val) do { ACCESS_ONCE(x) = (val); } while (0)
#define barrier()          __asm__ __volatile__("": : :"memory")

/* @types */

struct node;

enum bucket_flags {
        DIRTY    = 1ull << 0,
        ACCESSED = 1ull << 1
};

struct bucket {
        alignas(MAX_CACHELINE) struct cds_hlist_head chain;
        pthread_mutex_t                              lock;
        uint64_t                                     flags;
};

struct ht {
        int            shift;
        struct bucket *buckets;
};

struct t2 {
        struct ht                  ht;
        _Atomic(uint64_t)          bolt;
        int32_t                    writescan;
        int32_t                    cleanscan;
        const struct t2_tree_type *ttypes[MAX_TREE_TYPE];
        const struct node_type    *ntypes[MAX_NODE_TYPE];
        struct t2_storage         *stor;
};

SASSERT(MAX_TREE_HEIGHT <= 255); /* Level is 8 bit. */

struct t2_tree {
        struct t2_tree_type *ttype;
        taddr_t              root;
        uint32_t             id;
};

struct slot {
        struct node   *node;
        int            idx;
        struct t2_rec  rec;
};

enum optype {
        LOOKUP,
        DELETE,
        INSERT,
        NEXT,

        OP_NR
};

struct ewma {
        uint32_t count;
        uint32_t cur;
        uint32_t last;
        uint32_t avg;
};

enum node_flags {
        HEARD_BANSHEE = 1ull << 0,
        NOCACHE       = 1ull << 1,
        MODIFIED      = 1ull << 2
};

struct node {
        struct cds_hlist_node   hash;
        taddr_t                 addr;
        uint64_t                seq;
        atomic_int              ref;
        const struct node_type *ntype;
        uint64_t                flags;
        void                   *data;
        struct t2              *mod;
        struct ewma             kelvin;
        uint64_t                cookie;
        pthread_rwlock_t        lock;
        struct rcu_head         rcu;
};

enum lock_mode {
        NONE,
        READ,
        WRITE
};

enum rung_flags {
        PINNED = 1ull << 0,
        ALUSED = 1ull << 1,
        SEPCHG = 1ull << 2
};

enum policy_id {
        SPLIT_RIGHT, /* Knuth */
        SPLIT_LR,
        SHIFT,       /* Try to shift to the left and right neighbours. */

        POLICY_NR
};

struct pstate {
        enum policy_id id;
        union {
                struct split_right {
                } sr;
                struct shift {
                        int32_t shift_le;
                        int32_t shift_ln;
                        int32_t shift_rn;
                        int32_t shift_re;
                } sh;
        } u;
};

struct sibling {
        struct node   *node;
        enum lock_mode lm;
        uint64_t       seq;
};

struct rung {
        struct node   *node;
        uint64_t       seq;
        uint64_t       flags;
        enum lock_mode lm;
        int32_t        pos;
        struct node   *allocated;
        struct sibling brother[2];
        struct t2_buf  keyout;
        struct t2_buf  valout;
        struct pstate  pd;
        struct t2_buf  scratch;
};

struct path {
        struct t2_rec  *rec;
        enum optype     opt;
        int             used;
        struct rung     rung[MAX_TREE_HEIGHT];
        struct t2_tree *tree;
        struct node    *newroot;
};

struct policy {
        int (*plan_insert)(struct path *p, int idx);
        int (*plan_delete)(struct path *p, int idx);
        int (*exec_insert)(struct path *p, int idx);
        int (*exec_delete)(struct path *p, int idx);
};

struct node_type {
        int16_t     id;
        const char *name;
        struct t2  *mod;
        int         shift;
};

enum {
        NODE_MAGIX = 0x1f2e3d4c
};

struct header {
        int8_t   level;
        uint8_t  pad8;
        uint16_t ntype;
        uint32_t magix;
        uint32_t csum;
        uint32_t treeid;
};

struct msg_ctx {
        const char *func;
        const char *file;
        int         lineno;
        const char *fmt;
};

enum dir {
        LEFT  = -1,
        RIGHT = +1
};

struct counter_var {
        int64_t sum;
        int64_t nr;
};

struct counters { /* Must be all 64-bit integers, see counters_fold(). */
        int64_t node;
        int64_t rlock;
        int64_t wlock;
        int64_t rcu;
        int64_t peek;
        int64_t alloc;
        int64_t traverse;
        int64_t traverse_start;
        int64_t traverse_iter;
        int64_t wscan_clean;
        int64_t wscan_dirty;
        int64_t wscan_node;
        int64_t wscan_busy;
        int64_t wscan_written;
        int64_t cscan_accessed;
        int64_t cscan_not_accessed;
        int64_t cscan_node;
        int64_t cscan_cleaned;
        int64_t read;
        int64_t read_bytes;
        int64_t write;
        int64_t write_bytes;
        struct level_counters {
                int64_t insert_balance;
                int64_t delete_balance;
                int64_t get;
                int64_t search;
                int64_t bin_iter;
                int64_t lin_iter;
                int64_t nospc;
                int64_t dirmove;
                int64_t insert;
                int64_t delete;
                int64_t recget;
                int64_t moves;
                int64_t make;
                int64_t shift;
                int64_t shift_one;
                int64_t merge;
                struct counter_var nr;
                struct counter_var free;
                struct counter_var keysize;
                struct counter_var valsize;
        } l[MAX_TREE_HEIGHT];
};

struct error_descr {
        int                   err;
        const struct msg_ctx *ctx;
        uint64_t              v0;
        uint64_t              v1;
};

/* @static */

static void buf_copy(const struct t2_buf *dst, const struct t2_buf *src);
static int32_t buf_len(const struct t2_buf *b);
static int buf_cmp(const struct t2_buf *dst, const struct t2_buf *src);
static int buf_alloc(struct t2_buf *dst, struct t2_buf *src);
static void buf_free(struct t2_buf *b);
static int32_t rec_len(const struct t2_rec *r);
static int  ht_init(struct ht *ht, int shift);
static void ht_fini(struct ht *ht);
static void ht_clean(struct ht *ht);
static struct bucket *ht_bucket(struct ht *ht, taddr_t addr);
static struct node *ht_lookup(struct ht *ht, taddr_t addr);
static void ht_insert(struct ht *ht, struct node *n);
static void ht_delete(struct node *n);
static int val_copy(struct t2_rec *r, struct node *n, struct slot *s);
static void buf_clip(struct t2_buf *b, uint32_t mask, void *origin);
static void buf_clip_node(struct t2_buf *b, const struct node *n);
static taddr_t internal_search(struct node *n, struct t2_rec *r, int32_t *pos);
static taddr_t internal_get(const struct node *n, int32_t pos);
static struct node *internal_child(const struct node *n, int32_t pos, bool peek);
static int leaf_search(struct node *n, struct t2_rec *r, struct slot *s);
static void immanentise(const struct msg_ctx *ctx, ...) __attribute__((noreturn));
static void *mem_alloc(size_t size);
static void *mem_alloc_align(size_t size);
static void  mem_free(void *ptr);
static int cacheline_size();
static void llog(const struct msg_ctx *ctx, ...);
static void edescr(const struct msg_ctx *ctx, int err, uint64_t a0, uint64_t a1);
static void eclear();
static void eprint();
static void put(struct node *n);
static void put_locked(struct node *n, struct bucket *bucket);
static void ref(struct node *n);
static void touch(struct node *n);
static struct node *peek(struct t2 *mod, taddr_t addr);
static struct node *alloc(struct t2_tree *t, int8_t level);
static struct node *neighbour(struct path *p, int idx, enum dir d, enum lock_mode mode);
static bool can_insert(const struct node *n, const struct t2_rec *r);
static bool keep(const struct node *n);
static int dealloc(struct node *n);
static uint8_t level(const struct node *n);
static bool is_leaf(const struct node *n);
static int32_t nr(const struct node *n);
static int32_t nsize(const struct node *n);
static void lock(struct node *n, enum lock_mode mode);
static void unlock(struct node *n, enum lock_mode mode);
static struct header *nheader(const struct node *n);
static void rcu_lock();
static void rcu_unlock();
static int simple_insert(struct slot *s);
static void simple_delete(struct slot *s);
static void simple_get(struct slot *s);
static void simple_make(struct node *n);
static int32_t simple_nr(const struct node *n);
static int32_t simple_free(const struct node *n);
static int simple_can_insert(const struct slot *s);
static int32_t simple_used(const struct node *n);
static bool simple_can_merge(const struct node *n0, const struct node *n1);
static void simple_print(struct node *n);
static bool simple_invariant(const struct node *n);
static void range_print(void *orig, int32_t nsize, void *start, int32_t nob);
static int shift(struct node *d, struct node *s, const struct slot *insert, enum dir dir);
static int merge(struct node *d, struct node *s, enum dir dir);
static struct t2_buf *ptr_buf(struct node *n, struct t2_buf *b);
static struct t2_buf *addr_buf(taddr_t *addr, struct t2_buf *b);
static void counters_check();
static void counters_print();
static void counters_clear();
static void counters_fold();
static bool is_sorted(struct node *n);
static int signal_init();
static void signal_fini();
static void stacktrace();
static int lookup(struct t2_tree *t, struct t2_rec *r);
static int insert(struct t2_tree *t, struct t2_rec *r);
static int delete(struct t2_tree *t, struct t2_rec *r);
static bool cookie_is_valid(const struct t2_cookie *k);
static void cookie_invalidate(uint64_t *addr);
static void cookie_make(uint64_t *addr);
static void cookie_complete(struct path *p, struct node *n);
static void cookie_load(uint64_t *addr, struct t2_cookie *k);
static void mutex_lock(pthread_mutex_t *lock);
static void mutex_unlock(pthread_mutex_t *lock);
static void writeout(struct t2 *mod, int32_t toscan, int32_t towrite);
static void clean(struct t2 *mod, int32_t toscan, int32_t toclean);
static void kmod(struct ewma *a, uint32_t t);
static uint32_t kavg(struct ewma *a, uint32_t t);

static __thread struct counters __t_counters = {};
static __thread struct error_descr estack[MAX_ERR_DEPTH] = {};
static __thread int edepth = 0;
static __thread bool thread_registered = false;
static __thread volatile struct {
        volatile jmp_buf *buf;
} addr_check = {};
static struct counters __g_counters = {};
static pthread_mutex_t __g_counters_lock = PTHREAD_MUTEX_INITIALIZER;

struct t2 *t2_init(struct t2_storage *storage, int hshift) {
        int result;
        struct t2 *mod = mem_alloc(sizeof *mod);
        ASSERT(cacheline_size() / MAX_CACHELINE * MAX_CACHELINE == cacheline_size());
        t2_thread_register();
        eclear();
        if (mod != NULL) {
                result = signal_init();
                if (LIKELY(result == 0)) {
                        mod->stor = storage;
                        result = SCALL(mod, init);
                        if (LIKELY(result == 0)) {
                                result = ht_init(&mod->ht, hshift);
                                if (result != 0) {
                                        SCALL(mod, fini);
                                }
                        }
                        if (result != 0) {
                                signal_fini();
                        }
                }
        } else {
                result = ERROR(-ENOMEM);
        }
        if (result != 0) {
                mem_free(mod);
                t2_thread_degister();
                return EPTR(result);
        } else {
                return mod;
        }
}

void t2_fini(struct t2 *mod) {
        eclear();
        urcu_memb_barrier();
        SCALL(mod, fini);
        ht_clean(&mod->ht);
        ht_fini(&mod->ht);
        mod->stor->op->fini(mod->stor);
        signal_fini();
        mem_free(mod);
        t2_thread_degister();
}


void t2_tree_type_register(struct t2 *mod, struct t2_tree_type *ttype) {
        ASSERT(IS_IN(ttype->id, mod->ttypes));
        ASSERT(mod->ttypes[ttype->id] == NULL);
        ASSERT(ttype->mod == NULL);
        mod->ttypes[ttype->id] = ttype;
        ttype->mod = mod;
        eclear();
}


void t2_tree_type_degister(struct t2_tree_type *ttype)
{
        ASSERT(IS_IN(ttype->id, ttype->mod->ttypes));
        ASSERT(ttype->mod->ttypes[ttype->id] == ttype);
        ttype->mod->ttypes[ttype->id] = NULL;
        ttype->mod = NULL;
        eclear();
}

void t2_node_type_register(struct t2 *mod, struct node_type *ntype) {
        ASSERT(IS_IN(ntype->id, mod->ntypes));
        ASSERT(mod->ntypes[ntype->id] == NULL);
        ASSERT(ntype->mod == NULL);
        mod->ntypes[ntype->id] = ntype;
        ntype->mod = mod;
        eclear();
}


void t2_node_type_degister(struct node_type *ntype)
{
        ASSERT(IS_IN(ntype->id, ntype->mod->ntypes));
        ASSERT(ntype->mod->ntypes[ntype->id] == ntype);
        ntype->mod->ttypes[ntype->id] = NULL;
        ntype->mod = NULL;
        eclear();
}

int t2_error(int idx, char *buf, int nob, int *err) {
        if (0 <= idx && idx < edepth) {
                struct error_descr *ed = &estack[idx];
                *err = ed->err;
                return snprintf(buf, nob, ed->ctx->fmt, ed->v0, ed->v1);
        } else {
                return -EINVAL;
        }
}

void t2_error_print() {
        eprint();
}

void t2_thread_register() {
        ASSERT(!thread_registered);
        urcu_memb_register_thread();
        thread_registered = true;
}

void t2_thread_degister() {
        ASSERT(thread_registered);
        urcu_memb_unregister_thread();
        counters_fold();
        thread_registered = false;
}

enum {
        TADDR_SIZE_MASK =              0xfull,
        TADDR_LOW0_MASK =            0x1f0ull,
        TADDR_ADDR_MASK = 0xfffffffffffe00ull,
        TADDR_REST_MASK = ~0ull & ~(TADDR_SIZE_MASK | TADDR_LOW0_MASK | TADDR_ADDR_MASK),
        TADDR_MIN_SHIFT = 9
};

static bool taddr_is_valid(taddr_t addr) {
        return (addr & (TADDR_LOW0_MASK | TADDR_LOW0_MASK)) == 0;
}

static uint64_t taddr_saddr(taddr_t addr) {
        return addr & TADDR_ADDR_MASK;
}

static int taddr_ssize(taddr_t addr) {
        return 1 << ((addr & TADDR_SIZE_MASK) + TADDR_MIN_SHIFT);
}

static taddr_t taddr_make(uint64_t addr, int shift) {
        ASSERT((addr & TADDR_ADDR_MASK) == addr);
        shift -= TADDR_MIN_SHIFT;
        ASSERT((shift & TADDR_SIZE_MASK) == shift);
        return addr | shift;
}

static struct t2_buf zero = { .nr = 1 };

struct t2_tree *t2_tree_create(struct t2_tree_type *ttype) {
        ASSERT(thread_registered);
        eclear();
        struct t2_tree *t = mem_alloc(sizeof *t);
        if (t != NULL) {
                t->ttype = ttype;
                struct node *root = alloc(t, 0);
                if (EISOK(root)) {
                        int result;
                        t->root = root->addr;
                        put(root); /* Release earlier to keep counters happy. */
                        result = insert(t, &(struct t2_rec) { .key = &zero, .val = &zero });
                        if (result != 0) {
                                t = EPTR(result);
                        }
                        return t;
                } else {
                        return EPTR(root);
                }
        } else {
                return EPTR(-ENOMEM);
        }
}

static int rec_insert(struct node *n, int32_t idx, struct t2_rec *r) {
        return simple_insert(&(struct slot) { .node = n, .idx = idx, .rec  = *r });
}

static void rec_delete(struct node *n, int32_t idx) {
        simple_delete(&(struct slot) { .node = n, .idx = idx });
}

static void rec_get(struct slot *s, int32_t idx) {
        s->idx = idx;
        simple_get(s);
}

static int cookie_node_complete(struct t2_tree *t, struct t2_rec *r, struct node *n, enum optype opt) {
        ASSERT(r->key->nr == 1);
        int result;
        bool found;
        SLOT_DEFINE(s, n);
        rec_get(&s, 0);
        if (buf_cmp(s.rec.key, r->key) > 0) {
                return -ESTALE;
        }
        rec_get(&s, nr(n) - 1);
        if (buf_cmp(s.rec.key, r->key) < 0) {
                return -ESTALE;
        }
        found = leaf_search(n, r, &s);
        switch (opt) {
        case LOOKUP:
                result = found ? val_copy(r, n, &s) : -ENOENT;
                break;
        case INSERT:
                if (!found) {
                        result = rec_insert(n, s.idx + 1, r);
                        if (result == -ENOSPC) {
                                result = -ESTALE;
                        }
                } else {
                        result = -EEXIST;
                }
                break;
        case DELETE:
                if (!keep(n)) {
                        result = -ESTALE;
                } else if (found) {
                        rec_delete(n, s.idx);
                        result = 0;
                } else {
                        result = -ENOENT;
                }
                break;
        case NEXT:
                result = -ESTALE;
                break; /* TODO: implement. */
        default:
                IMMANENTISE("Wrong opt: %i", opt);
        }
        return result;
}

static int cookie_try(struct t2_tree *t, struct t2_rec *r, enum optype opt) {
        enum lock_mode mode = opt == LOOKUP || opt == NEXT ? READ : WRITE;
        rcu_lock();
        if (cookie_is_valid(&r->cookie)) {
                struct node *n = COF(r->cookie.hi, struct node, cookie);
                if (is_leaf(n) && nr(n) > 0) { /* TODO: More checks? */
                        int result;
                        ref(n);
                        rcu_unlock();
                        lock(n, mode); /* TODO: Lock-less lookup. */
                        /* TODO: re-check node. */
                        result = cookie_node_complete(t, r, n, opt);
                        touch(n);
                        unlock(n, mode);
                        put(n);
                        return result;
                }
        }
        rcu_unlock();
        return -ESTALE;
}

static uint64_t node_seq(const struct node *n) {
        uint64_t seq = READ_ONCE(n->seq);
        __sync_synchronize();
        return seq & ~(uint64_t)1;
}

static void node_seq_increase(struct node *n) {
        __sync_synchronize();
        n->seq++;
}

static bool node_seq_is_valid(const struct node *n, uint64_t expected) {
        uint64_t seq;
        __sync_synchronize();
        seq = READ_ONCE(n->seq);
        return seq == expected;
}

/* @node */

static bool is_stable(const struct node *n) {
        return (n->seq & 1) == 0;
}

static void lock(struct node *n, enum lock_mode mode) {
        ASSERT(mode == NONE || mode == READ || mode == WRITE);
        ASSERT(CVAL(rcu) == 0);
        if (LIKELY(mode == NONE)) {
                ;
        } else if (mode == WRITE) {
                NOFAIL(pthread_rwlock_wrlock(&n->lock));
                ASSERT(is_stable(n));
                CINC(wlock);
        } else if (mode == READ) {
                NOFAIL(pthread_rwlock_rdlock(&n->lock));
                CINC(rlock);
        }
}

static void unlock(struct node *n, enum lock_mode mode) {
        ASSERT(mode == NONE || mode == READ || mode == WRITE);
        if (LIKELY(mode == NONE)) {
                ;
        } else if (mode == WRITE) {
                if (!is_stable(n)) {
                        node_seq_increase(n);
                }
                NOFAIL(pthread_rwlock_unlock(&n->lock));
                CDEC(wlock);
        } else if (mode == READ) {
                NOFAIL(pthread_rwlock_unlock(&n->lock));
                CDEC(rlock);
        }
}

static struct node *peek(struct t2 *mod, taddr_t addr) {
        CINC(peek);
        return ht_lookup(&mod->ht, addr);
}

static struct node *nalloc(struct t2 *mod, taddr_t addr) {
        struct node *n    = mem_alloc(sizeof *n);
        void        *data = mem_alloc_align(taddr_ssize(addr));
        int          result;
        CINC(alloc);
        if (LIKELY(n != NULL && data != NULL)) {
                result = pthread_rwlock_init(&n->lock, NULL);
                if (LIKELY(result == 0)) {
                        n->addr = addr;
                        n->mod = mod;
                        n->data = data;
                        n->ref = 1;
                        cookie_make(&n->cookie);
                        CINC(node);
                        return n;
                }
        } else {
                result = ERROR(-ENOMEM);
        }
        mem_free(n);
        mem_free(data);
        return EPTR(result);
}

static void nfini(struct node *n) {
        ASSERT(n->ref == 0);
        cookie_invalidate(&n->cookie);
        NOFAIL(pthread_rwlock_destroy(&n->lock));
        mem_free(n->data);
        SET0(n);
        mem_free(n);
}

static struct node *ninit(struct t2 *mod, taddr_t addr) {
        struct node *n = nalloc(mod, addr);
        if (EISOK(n)) {
                struct node     *other;
                pthread_mutex_t *bucket = &ht_bucket(&mod->ht, addr)->lock;
                mutex_lock(bucket);
                other = ht_lookup(&mod->ht, addr);
                if (LIKELY(other == NULL)) {
                        ht_insert(&mod->ht, n);
                } else {
                        n->ref = 0;
                        CDEC(node);
                        nfini(n);
                        n = other;
                        ref(n);
                }
                mutex_unlock(bucket);
                touch(n);
        }
        return n;
}

static void ref(struct node *n) {
        n->ref++;
        CINC(node);
}

static void ndelete(struct node *n) {
        struct bucket *bucket = ht_bucket(&n->mod->ht, n->addr);
        mutex_lock(&bucket->lock);
        n->flags |= NOCACHE | HEARD_BANSHEE;
        put_locked(n, bucket);
        mutex_unlock(&bucket->lock);
}

static struct node *get(struct t2 *mod, taddr_t addr) {
        struct node *n = ninit(mod, addr);
        ASSERT(CVAL(rcu) == 0);
        if (EISOK(n)) {
                lock(n, WRITE);
                if (LIKELY(n->ntype == NULL)) {
                        int result = SCALL(n->mod, read, n->addr, n->data);
                        if (LIKELY(result == 0)) {
                                struct header *h = n->data;
                                /* TODO: check node. */
                                if (LIKELY(IS_IN(h->ntype, n->mod->ntypes) && n->mod->ntypes[h->ntype] != NULL)) {
                                        rcu_assign_pointer(n->ntype, n->mod->ntypes[h->ntype]);
                                } else {
                                        result = ERROR(-ESTALE);
                                }
                                CINC(read);
                                CADD(read_bytes, taddr_ssize(n->addr));
                        }
                        if (UNLIKELY(result != 0)) {
                                unlock(n, WRITE);
                                ndelete(n);
                                return EPTR(result);
                        }
                }
                unlock(n, WRITE);
        }
        return n;
}

static struct node *alloc(struct t2_tree *t, int8_t level) {
        struct t2        *mod   = t->ttype->mod;
        struct node_type *ntype = t->ttype->ntype(t, level);
        taddr_t           addr  = SCALL(mod, alloc, ntype->shift, ntype->shift);
        struct node      *n;
        ASSERT(CVAL(rcu) == 0);
        if (EISOK(addr)) {
                n = ninit(mod, addr);
                if (EISOK(n)) {
                        *nheader(n) = (struct header) {
                                .magix  = NODE_MAGIX,
                                .ntype  = ntype->id,
                                .level  = level,
                                .treeid = t->id
                        };
                        n->ntype = ntype;
                        n->flags |= MODIFIED;
                        simple_make(n);
                }
        } else {
                n = EPTR(addr);
        }
        return n;
}

static void free_callback(struct rcu_head *head) {
        struct node *n = COF(head, struct node, rcu);
        if (n->ref == 0) {
                nfini(n);
        }
}

static void put_final(struct node *n) {
        n->flags |= HEARD_BANSHEE;
        ht_delete(n);
        call_rcu_memb(&n->rcu, &free_callback);
}

static void put_locked(struct node *n, struct bucket *b) {
        ASSERT(n->ref > 0);
        EXPENSIVE_ASSERT(n->data != NULL ? is_sorted(n) : true);
        if (--n->ref == 0) {
                /* TODO: lru. */
                if (n->flags & NOCACHE) {
                        put_final(n);
                } else if (n->flags & MODIFIED) {
                        b->flags |= ACCESSED | DIRTY;
                } else {
                        b->flags |= ACCESSED;
                }
        }
        CDEC(node);
}

static void put(struct node *n) {
        struct bucket *bucket = ht_bucket(&n->mod->ht, n->addr);
        mutex_lock(&bucket->lock);
        put_locked(n, bucket);
        mutex_unlock(&bucket->lock);
}

static int dealloc(struct node *n) {
        struct t2 *mod = n->mod;
        ndelete(n);
        SCALL(mod, free, n->addr);
        return 0;
}


static struct header *nheader(const struct node *n) {
        return n->data;
}

static uint8_t level(const struct node *n) {
        return nheader(n)->level;
}

static bool is_leaf(const struct node *n) {
        return level(n) == 0;
}

static int32_t nr(const struct node *n) {
        return simple_nr(n);
}

static int32_t nsize(const struct node *n) {
        return (int32_t)1 << n->ntype->shift;
}

static void rcu_lock() {
        urcu_memb_read_lock();
        ASSERT(CVAL(rcu) == 0);
        CINC(rcu);
}

static void rcu_unlock() {
        CDEC(rcu);
        urcu_memb_read_unlock();
}

static void rcu_quiescent() {
        urcu_memb_quiescent_state();
}


/* @policy */

static int32_t prefix_separator(const struct t2_buf *l, struct t2_buf *r) {
        ASSERT(buf_cmp(l, r) < 0);
        ASSERT(r->nr == 1);
        return r->seg[0].len; /* TODO: Cannot handle delete properly. */
        do {
                r->seg[0].len--;
        } while (buf_cmp(l, r) < 0);
        return ++r->seg[0].len;
}

static void rec_todo(struct path *p, int idx, struct slot *out) {
        if (idx + 1 == p->used) {
                *out->rec.key = *p->rec->key;
                *out->rec.val = *p->rec->val;
        } else {
                ASSERT(idx + 1 < p->used);
                *out->rec.key = p->rung[idx + 1].keyout;
                *out->rec.val = p->rung[idx + 1].valout;
        }
}

static void internal_parent_rec(struct path *p, int idx) {
        struct rung  *r = &p->rung[idx];
        SLOT_DEFINE(s, r->node);
        int32_t       maxlen;
        int32_t       keylen;
        ASSERT(nr(r->node) > 0);
        ASSERT(r->allocated != NULL);
        rec_todo(p, idx, &s);
        maxlen = buf_len(s.rec.key);
        r->keyout = *s.rec.key;
        for (int32_t i = 0; i < nr(r->node); ++i) {
                rec_get(&s, i);
                buf_clip_node(s.rec.key, r->node);
                keylen = buf_len(s.rec.key);
                if (keylen > maxlen) {
                        maxlen = keylen;
                        r->keyout = *s.rec.key;
                }
        }
        ptr_buf(r->allocated, &r->valout);
}

static int newnode(struct path *p, int idx) {
       struct rung *r = &p->rung[idx];
       if (r->allocated == NULL) {
               r->allocated = alloc(p->tree, level(r->node));
               if (EISERR(r->allocated)) {
                       return ERROR(ERRCODE(r->allocated));
               }
       }
       if (idx == 0) { /* Hodie natus est radici frater. */
               if (LIKELY(p->used < MAX_TREE_HEIGHT)) {
                       p->newroot = alloc(p->tree, level(r->node) + 1);
                       if (EISERR(r->allocated)) {
                               return ERROR(ERRCODE(p->newroot));
                       } else {
                               return +1; /* Done. */
                       }
               } else {
                       return ERROR(-E2BIG);
               }
       }
       return 0;
}

static int split_right_plan_insert(struct path *p, int idx) {
        int result = newnode(p, idx);
        if (result >= 0) {
                internal_parent_rec(p, idx);
        }
        return result;
}

static int split_right_exec_insert(struct path *p, int idx) {
        struct rung *r = &p->rung[idx];
        struct node *left = r->node;
        struct node *right = r->allocated;
        SLOT_DEFINE(s, NULL);
        int result = 0;
        rec_todo(p, idx, &s);
        /* Maybe ->plan() overestimated keysize and shift is not needed. */
        if (right != NULL && !can_insert(left, &s.rec)) {
                s.idx = r->pos + 1;
                result = shift(right, left, &s, RIGHT);
                ASSERT(nr(left) > 0);
                ASSERT(nr(right) > 0);
                r->flags |= ALUSED;
        }
        if (LIKELY(result == 0)) {
                if (r->pos < nr(left)) {
                        s.node = left;
                        s.idx  = r->pos;
                } else {
                        ASSERT(right != NULL);
                        s.node = right;
                        s.idx  = r->pos - nr(left);
                }
                s.idx++;
                ASSERT(s.idx <= nr(s.node));
                NOFAIL(simple_insert(&s));
                EXPENSIVE_ASSERT(result != 0 || is_sorted(s.node));
                if (r->flags & ALUSED) {
                        struct t2_buf lkey = {};
                        struct t2_buf rkey;
                        if (is_leaf(right)) {
                                s.node = left;
                                rec_get(&s, nr(left) - 1);
                                lkey = *s.rec.key;
                        }
                        s.node = right;
                        rec_get(&s, 0);
                        rkey = *s.rec.key;
                        if (is_leaf(right)) {
                                prefix_separator(&lkey, &rkey);
                        }
                        NOFAIL(buf_alloc(&r->scratch, &rkey));
                        r->keyout = r->scratch;
                        ptr_buf(right, &r->valout);
                        return +1;
                }
        }
        return result;
}

static struct sibling *brother(struct rung *r, enum dir d) {
        ASSERT(d == LEFT || d == RIGHT);
        return &r->brother[d > 0];
}

static int split_right_plan_delete(struct path *p, int idx) {
        struct node *right = neighbour(p, idx, RIGHT, WRITE);
        if (EISERR(right)) {
                return ERROR(ERRCODE(right));
        } else {
                return 0;
        }
}

static bool can_merge(struct node *n0, struct node *n1) {
        return simple_can_merge(n0, n1);
}

static void delete_update(struct path *p, int idx, struct slot *s) {
        ASSERT(idx + 1 < p->used);
        simple_get(s);
        simple_delete(s);
        if (p->rung[idx + 1].flags & SEPCHG) {
                struct node  *child = brother(&p->rung[idx + 1], RIGHT)->node;
                struct t2_buf cptr;
                SLOT_DEFINE(sub, child);
                {       /* A new scope for the second SLOT_DEFINE(). */
                        SLOT_DEFINE(leaf, p->rung[p->used - 1].node);
                        ASSERT(child != NULL && !is_leaf(child));
                        rec_get(&sub, 0);
                        *s->rec.key = *sub.rec.key;
                        *s->rec.val = *ptr_buf(child, &cptr);
                        /* Take the rightmost key in the leaf. */
                        rec_get(&leaf, nr(leaf.node) - 1);
                        prefix_separator(leaf.rec.key, s->rec.key);
                        NOFAIL(simple_insert(s));
                }
        }
}

static int split_right_exec_delete(struct path *p, int idx) {
        int result = 0;
        struct rung *r = &p->rung[idx];
        struct node *right = brother(r, RIGHT)->node;
        SLOT_DEFINE(s, r->node);
        if (!is_leaf(r->node)) {
                if (r->pos + RIGHT < nr(r->node)) {
                        s.idx = r->pos + 1;
                        delete_update(p, idx, &s);
                } else {
                        ASSERT(right != NULL);
                        s.node = right;
                        s.idx = 0;
                        delete_update(p, idx, &s);
                        r->flags |= SEPCHG;
                        result = +1;
                }
        }
        if (right != NULL && can_merge(r->node, right)) {
                NOFAIL(merge(r->node, right, LEFT)); /* TODO: deallocate the empty node. */
                EXPENSIVE_ASSERT(is_sorted(r->node));
                r->flags &= ~SEPCHG;
                result = +1;
        }
        return result;
}

static bool can_fit(const struct node *left, const struct node *middle, const struct node *right, const struct t2_rec *rec) {
        return true;
}

static int shift_plan_insert(struct path *p, int idx) {
        struct rung *r = &p->rung[idx];
        int          result;
        struct node *left  = neighbour(p, idx,  LEFT, WRITE);
        struct node *right = neighbour(p, idx, RIGHT, WRITE);
        if (UNLIKELY(EISOK(left) && EISOK(right))) {
                if (can_fit(left, r->node, right, NULL)) {
                        return 0;
                }
                result = newnode(p, idx);
        } else {
                if (EISERR(right)) {
                        result = ERROR(ERRCODE(right));
                }
                if (EISERR(left)) {
                        result = ERROR(ERRCODE(left));
                }
        }
        return result;
}

static int shift_exec_insert(struct path *p, int idx) {
        return 0;
}

static const struct policy dispatch[POLICY_NR] = {
        [SPLIT_RIGHT] = {
                .plan_insert = &split_right_plan_insert,
                .plan_delete = &split_right_plan_delete,
                .exec_insert = &split_right_exec_insert,
                .exec_delete = &split_right_exec_delete,
        },
        [SHIFT] = {
                .plan_insert = &shift_plan_insert,
                .exec_insert = &shift_exec_insert
        }
};

static enum policy_id policy_select(const struct path *p, int idx) {
        return SPLIT_RIGHT;
}

/* @tree */

static void path_init(struct path *p, struct t2_tree *t, struct t2_rec *r, enum optype opt) {
        ASSERT(p->used == 0);
        SASSERT(NONE == 0);
        p->tree = t;
        p->rec  = r;
        p->opt  = opt;
}

static void dirty(struct node *n, enum lock_mode lm) {
        if (n != NULL && lm == WRITE) {
                ASSERT(is_stable(n));
                node_seq_increase(n);
                n->flags |= MODIFIED;
        }
}

static void path_dirty(struct path *p) {
        for (int i = p->used - 1; i >= 0; --i) {
                struct rung    *r     = &p->rung[i];
                struct sibling *left  = brother(r, LEFT);
                struct sibling *right = brother(r, RIGHT);
                dirty(r->node, r->lm);
                dirty(left->node, left->lm);
                dirty(right->node, right->lm);
        }
}

static void path_lock(struct path *p) {
        /* Top to bottom, left to right. */
        for (int i = p->used - 1; i >= 0; --i) {
                struct rung *r = &p->rung[i];
                struct sibling *left  = brother(r, LEFT);
                struct sibling *right = brother(r, RIGHT);
                if (left->node != NULL) {
                        lock(left->node, left->lm);
                }
                lock(r->node, r->lm);
                if (right->node != NULL) {
                        lock(right->node, right->lm);
                }
        }
}

static void path_fini(struct path *p) { /* TODO: path_reset(p, &next). */
        while (--p->used >= 0) {
                struct rung *r = &p->rung[p->used];
                struct sibling *left  = brother(r, LEFT);
                struct sibling *right = brother(r, RIGHT);
                if (UNLIKELY(right->node != NULL)) {
                        unlock(right->node, right->lm);
                        put(right->node);
                }
                unlock(r->node, r->lm);
                if (UNLIKELY(left->node != NULL)) {
                        unlock(left->node, left->lm);
                        put(left->node);
                }
                if (r->flags & PINNED) {
                        put(r->node);
                }
                if (UNLIKELY(r->allocated != NULL)) {
                        if (LIKELY(r->flags & ALUSED)) {
                                put(r->allocated);
                        } else {
                                dealloc(r->allocated);
                        }
                }
                buf_free(&r->scratch);
                SET0(r);
        }
        p->used = 0;
        if (UNLIKELY(p->newroot != NULL)) {
                dealloc(p->newroot);
                p->newroot = NULL;
        }
}

static void path_pin(struct path *p) {
        for (int i = p->used - 1; i >= 0; --i) {
                struct rung *r = &p->rung[i];
                if (!(r->flags & PINNED)) {
                        ref(r->node);
                        r->flags |= PINNED;
                }
        }
}

static bool rung_validity_invariant(const struct path *p, int i) {
        const struct rung *r    = &p->rung[i];
        const struct node *n    = r->node;
        const struct rung *prev = &p->rung[i - 1];
        return is_stable(n) &&
                (!is_leaf(n) ? r->pos < nr(n) : true) &&
                (i == 0 ? p->tree->root == n->addr :
                 (prev->lm != WRITE) || (n->addr == internal_get(prev->node, prev->pos) &&
                                         level(prev->node) == level(n) + 1)) &&
                (i == p->used - 1) == is_leaf(n);
}

static bool rung_is_valid(const struct path *p, int i) {
        const struct rung *r        = &p->rung[i];
        struct sibling    *left     = brother((struct rung *)r, LEFT);
        struct sibling    *right    = brother((struct rung *)r, RIGHT);
        bool               is_valid = node_seq_is_valid(r->node, r->seq) &&
                (left->node  != NULL ? node_seq_is_valid(left->node,  left->seq)  : true) &&
                (right->node != NULL ? node_seq_is_valid(right->node, right->seq) : true);
        ASSERT(is_valid && r->lm == WRITE ? rung_validity_invariant(p, i) : true);
        return is_valid;
}

static struct rung *path_add(struct path *p, struct node *n, uint64_t seq, uint64_t flags) {
        ASSERT(IS_IN(p->used, p->rung));
        p->rung[p->used] = (struct rung) {
                .node  = n,
                .seq   = seq,
                .flags = flags,
                .pos   = 0
        };
        return &p->rung[p->used++];
}

static bool path_is_valid(const struct path *p) {
        return FORALL(i, p->used, rung_is_valid(p, i));
}

static bool can_insert(const struct node *n, const struct t2_rec *r) {
        const struct slot s = {
                .node = (struct node *)n,
                .idx  = -1, /* Unknown position. */
                .rec  = *r
        };
        return simple_can_insert(&s);
}

static int32_t utmost(const struct node *n, enum dir d) {
        return d == LEFT ? 0 : nr(n) - 1;
}

static struct node *neighbour(struct path *p, int idx, enum dir d, enum lock_mode mode) {
        struct node    *down = NULL;
        struct rung    *r    = &p->rung[idx];
        struct sibling *br   = brother(r, d);
        int             i;
        if (br->node != NULL) {
                ASSERT(br->lm == mode);
                return br->node;
        }
        for (i = idx - 1; i >= 0; --i) {
                r = &p->rung[i];
                ASSERT(brother(r, d)->node == NULL);
                if (r->pos != utmost(r->node, d)) {
                        break;
                }
        }
        if (i < 0) {
                return NULL;
        }
        ASSERT(r->lm == NONE || r->lm == mode);
        r->lm = mode;
        down = internal_child(r->node, r->pos + d, false);
        while (down != NULL && EISOK(down)) {
                r = &p->rung[++i];
                ASSERT(r->lm == NONE || r->lm == mode);
                r->lm = mode;
                *brother(r, d) = (struct sibling) { .node = down, .lm = mode, .seq = node_seq(down) };
                if (i == idx) {
                        break;
                }
                SASSERT(LEFT == -RIGHT);
                down = internal_child(down, utmost(down, -d), false);
        }
        return down;
}

static int insert_prep(struct path *p) {
        struct t2_rec  irec = {};
        int            idx = p->used - 1;
        struct t2_rec *rec = p->rec;
        int            result = 0;
        SLOT_DEFINE(s, p->rung[idx].node);
        if (leaf_search(p->rung[idx].node, rec, &s)) {
                return -EEXIST;
        }
        p->rung[idx].pos = s.idx;
        do {
                struct rung *r = &p->rung[idx];
                r->lm = WRITE;
                if (can_insert(r->node, rec)) {
                        break;
                } else {
                        r->pd.id = policy_select(p, idx);
                        result = dispatch[r->pd.id].plan_insert(p, idx);
                        if (result > 0) {
                                result = 0;
                                break;
                        }
                        rec = &irec;
                        rec->key = &r->keyout;
                        rec->val = &r->valout;
                }
        } while (--idx >= 0 && LIKELY(result == 0));
        path_lock(p);
        return result;
}

static bool keep(const struct node *n) {
        /* Take level into account? */
        return simple_free(n) < 3 * nsize(n) / 4;
}

static int delete_prep(struct path *p) {
        int idx    = p->used - 1;
        int result = 0;
        SLOT_DEFINE(s, p->rung[idx].node);
        if (!leaf_search(p->rung[idx].node, p->rec, &s)) {
                return -ENOENT;
        }
        p->rung[idx].pos = s.idx;
        do {
                struct rung *r = &p->rung[idx];
                r->lm = WRITE;
                if (keep(r->node)) {
                        break;
                } else {
                        r->pd.id = policy_select(p, idx);
                        result = dispatch[r->pd.id].plan_delete(p, idx);
                        if (result > 0) {
                                result = 0;
                                break;
                        }
                }
        } while (--idx >= 0 && LIKELY(result == 0));
        path_lock(p);
        return result;
}

SASSERT((enum dir)T2_LESS == LEFT && (enum dir)T2_MORE == RIGHT);

static int next_prep(struct path *p) {
        struct node      *sibling;
        struct rung      *r      = &p->rung[p->used - 1];
        struct t2_cursor *c      = (void *)p->rec->vcb;
        int               result = 0;
        SLOT_DEFINE(s, r->node);
        if (!leaf_search(r->node, p->rec, &s) && (enum dir)c->dir == RIGHT) {
                s.idx++;
        }
        r->pos = s.idx;
        r->lm = READ;
        sibling = neighbour(p, p->used - 1, (enum dir)c->dir, READ);
        if (EISERR(sibling)) {
                result = ERROR(ERRCODE(sibling));
        }
        path_lock(p);
        return result;
}

static int lookup_complete(struct path *p, struct node *n) {
        SLOT_DEFINE(s, NULL);
        return leaf_search(n, p->rec, &s) ? val_copy(p->rec, n, &s) : -ENOENT;
}

static struct t2_buf *ptr_buf(struct node *n, struct t2_buf *b) {
        return addr_buf(&n->addr, b);
}

static struct t2_buf *addr_buf(taddr_t *addr, struct t2_buf *b) {
        ASSERT(*addr != 0);
        *b = BUF_VAL(*addr);
        while (((int8_t *)b->seg[0].addr)[b->seg[0].len - 1] == 0) {
                b->seg[0].len--;
        }
        return b;
}

static int root_add(struct path *p) {
        /*
         * TODO: It is desirable to never move the tree root.
         *
         * To achieve this, move half of the records from the old root to the
         * new root and the other half to the allocated node. Then make the
         * latter 2 nodes the only children of the old root. Then increase the
         * old root's level.
         */
        struct node  *oldroot = p->rung[0].node;
        struct t2_buf ptr;
        int           result;
        SLOT_DEFINE(s, oldroot);
        if (UNLIKELY(buf_len(&p->rung[0].keyout) == 0 && buf_len(&p->rung[0].valout) == 0)) {
                return 0; /* Nothing to do. */
        }
        rec_get(&s, 0);
        s.node = p->newroot;
        s.rec.val = ptr_buf(oldroot, &ptr);
        result = simple_insert(&s);
        if (LIKELY(result == 0)) {
                s.idx = 1;
                ASSERT(p->rung[0].pd.id == SPLIT_RIGHT); /* For now. */
                s.rec.key = &p->rung[0].keyout;
                s.rec.val = &p->rung[0].valout;
                result = simple_insert(&s);
                if (LIKELY(result == 0)) {
                        p->rung[0].flags |= ALUSED;
                        /* Barrier? */
                        p->tree->root = p->newroot->addr;
                        put(p->newroot);
                        p->newroot = NULL;
                }
        }
        return result;
}

static int insert_balance(struct path *p) {
        int idx;
        int result = 0;
        for (idx = p->used - 1; idx >= 0; --idx) {
                struct rung *r = &p->rung[idx];
                ASSERT(r->lm == WRITE);
                CINC(l[level(r->node)].insert_balance);
                result = dispatch[r->pd.id].exec_insert(p, idx);
                if (result <= 0) {
                        break;
                }
                result = 0;
        }
        if (UNLIKELY(idx < 0 && LIKELY(result == 0))) {
                if (p->newroot != NULL) {
                        result = root_add(p); /* Move this to policy? */
                }
        }
        return result;
}

static int insert_complete(struct path *p, struct node *n) {
        int result = rec_insert(n, p->rung[p->used - 1].pos + 1, p->rec);
        if (result == -ENOSPC) {
                result = insert_balance(p);
        }
        cookie_complete(p, n);
        return result;
}

static int delete_balance(struct path *p) {
        int idx;
        int result = 0;
        for (idx = p->used - 1; idx >= 0; --idx) {
                struct rung *r = &p->rung[idx];
                ASSERT(r->lm == WRITE);
                CINC(l[level(r->node)].delete_balance);
                result = dispatch[r->pd.id].exec_delete(p, idx);
                if (result <= 0) {
                        break;
                }
                result = 0;
        }
        /* TODO: Delete root? */
        return result;
}

static int delete_complete(struct path *p, struct node *n) {
        int result = 0;
        rec_delete(n, p->rung[p->used - 1].pos);
        if (!keep(n)) {
                result = delete_balance(p);
        }
        cookie_complete(p, n);
        return result;
}

static int next_complete(struct path *p, struct node *n) {
        struct rung      *r      = &p->rung[p->used - 1];
        struct t2_cursor *c      = (void *)p->rec->vcb;
        int               result = +1;
        SLOT_DEFINE(s, n);
        for (s.idx = r->pos; 0 <= s.idx && s.idx < nr(n); s.idx += c->dir) {
                simple_get(&s);
                result = c->op->next(c, &s.rec);
                if (result <= 0) {
                        break;
                }
        }
        if (result > 0) {
                struct node *sibling = brother(r, (enum dir)c->dir)->node;
                if (LIKELY(sibling != NULL && nr(sibling) > 0)) { /* Rightmost leaf can be empty. */
                        s.node = sibling;
                        rec_get(&s, utmost(sibling, -c->dir)); /* Cute. */
                } else {
                        return 0;
                }
        }
        if (result >= 0) {
                int32_t keylen = buf_len(s.rec.key);
                if (LIKELY(keylen <= c->maxlen)) {
                        c->curkey.seg[0].len = c->maxlen;
                        buf_copy(&c->curkey, s.rec.key);
                        c->curkey.seg[0].len = keylen;
                } else {
                        result = ERROR(-ENAMETOOLONG);
                }
        }
        cookie_complete(p, s.node);
        return result;
}

static void rcu_leave(struct path *p) {
        path_pin(p);
        rcu_unlock();
}

static bool rcu_try(struct path *p) {
        bool result;
        result = EXISTS(i, p->used, p->rung[i].node->flags & HEARD_BANSHEE);
        if (result) {
                urcu_memb_barrier();
                path_fini(p);
        }
        return result;
}

static bool rcu_enter(struct path *p) {
        bool result = rcu_try(p);
        rcu_lock();
        return result;
}

enum { BOLT_EPOCH_SHIFT = 14 };

static void touch(struct node *n) {
        kmod(&n->kelvin, n->mod->bolt >> BOLT_EPOCH_SHIFT);
}

enum {
        DONE  = 1,
        AGAIN = 2
};

static int traverse_complete(struct path *p, int result) {
        if (UNLIKELY(rcu_try(p))) {
                rcu_lock();
                return AGAIN;
        } else if (UNLIKELY(result == -ESTALE)) {
                path_fini(p);
                rcu_lock();
                return AGAIN;
        } else if (UNLIKELY(result != 0)) {
                return result;
        } else if (UNLIKELY(!path_is_valid(p))) {
                path_fini(p);
                rcu_lock();
                return AGAIN;
        } else {
                path_dirty(p);
                return DONE;
        }
}

static int traverse(struct path *p) {
        struct t2 *mod   = p->tree->ttype->mod;
        int        tries = 0;
        int        result;
        uint64_t   next = 0;
        ASSERT(p->used == 0);
        ASSERT(p->opt == LOOKUP || p->opt == INSERT || p->opt == DELETE || p->opt == NEXT);
        CINC(traverse);
        rcu_lock();
        while (true) {
                struct node *n;
                struct rung *r;
                uint64_t     flags = 0;
                ASSERT(CVAL(rcu) == 1);
                CINC(traverse_iter);
                if (UNLIKELY(tries++ > 10)) {
                        if (false && (tries & (tries - 1)) == 0) {
                                LOG("Looping: %i", tries);
                        }
                }
                if (p->used == 0) {
                        CINC(traverse_start);
                        next = p->tree->root;
                }
                n = peek(mod, next);
                if (EISERR(n)) {
                        result = ERROR(ERRCODE(n));
                        rcu_unlock();
                        break;
                } else if (n == NULL || rcu_dereference(n->ntype) == NULL) {
                        rcu_leave(p);
                        n = get(mod, next);
                        if (rcu_enter(p)) {
                                continue;
                        }
                        if (EISERR(n)) {
                                if (ERRCODE(n) == -ESTALE) {
                                        path_fini(p);
                                        continue;
                                } else {
                                        result = ERROR(ERRCODE(n));
                                        rcu_unlock();
                                        break;
                                }
                        } else {
                                CINC(l[level(n)].get);
                                flags |= PINNED;
                        }
                } else if (!is_stable(n)) { /* This is racy, but OK. */
                        rcu_leave(p);
                        lock(n, READ); /* Wait for stabilisation. */
                        unlock(n, READ);
                        if (rcu_enter(p)) {
                                continue;
                        }
                } else {
                        touch(n);
                }
                if (UNLIKELY(p->used == ARRAY_SIZE(p->rung))) {
                        path_fini(p);
                        continue;
                }
                r = path_add(p, n, node_seq(n), flags);
                CMOD(l[level(n)].nr, nr(n));
                CMOD(l[level(n)].free, simple_free(n));
                if (is_leaf(n)) {
                        if (p->opt == LOOKUP) {
                                result = lookup_complete(p, n);
                                if (!path_is_valid(p)) {
                                        path_fini(p);
                                } else {
                                        rcu_unlock();
                                        break;
                                }
                        } else if (p->opt == INSERT) {
                                rcu_leave(p);
                                result = traverse_complete(p, insert_prep(p));
                                if (result == DONE) {
                                        result = insert_complete(p, n);
                                        break;
                                } else if (result < 0) {
                                        break;
                                }
                        } else if (p->opt == DELETE) {
                                rcu_leave(p);
                                result = traverse_complete(p, delete_prep(p));
                                if (result == DONE) {
                                        result = delete_complete(p, n);
                                        break;
                                } else if (result < 0) {
                                        break;
                                }
                        } else {
                                rcu_leave(p);
                                result = traverse_complete(p, next_prep(p));
                                if (result == DONE) {
                                        result = next_complete(p, n);
                                        break;
                                } else if (result < 0) {
                                        break;
                                }
                        }
                } else {
                        next = internal_search(n, p->rec, &r->pos);
                        if (EISERR(next)) {
                                result = ERROR(ERRCODE(next));
                                rcu_unlock();
                                break;
                        }
                }
        }
        ASSERT(CVAL(rcu) == 0);
        return result;
}

static int traverse_result(struct t2_tree *t, struct t2_rec *r, enum optype opt) {
        int result;
        counters_check();
        t->ttype->mod->bolt++;
        result = cookie_try(t, r, opt);
        if (result == -ESTALE) {
                struct path p = {};
                path_init(&p, t, r, opt);
                result = traverse(&p);
                path_fini(&p);
        }
        counters_check();
        return result;
}

static int lookup(struct t2_tree *t, struct t2_rec *r) {
        return traverse_result(t, r, LOOKUP);
}

static int insert(struct t2_tree *t, struct t2_rec *r) {
        return traverse_result(t, r, INSERT);
}

static int delete(struct t2_tree *t, struct t2_rec *r) {
        return traverse_result(t, r, DELETE);
}

static int next(struct t2_cursor *c) {
        struct t2_buf val = {};
        struct t2_rec r = {
                .key = &c->curkey,
                .val = &val,
                .vcb = (void *)c /* Erm... */
        };
        return traverse_result(c->tree, &r, NEXT);
}

int t2_lookup(struct t2_tree *t, struct t2_rec *r) {
        ASSERT(thread_registered);
        eclear();
        return lookup(t, r);
}

int t2_delete(struct t2_tree *t, struct t2_rec *r) {
        ASSERT(thread_registered);
        eclear();
        return delete(t, r);
}

int t2_insert(struct t2_tree *t, struct t2_rec *r) {
        ASSERT(thread_registered);
        eclear();
        return insert(t, r);
}

int t2_cursor_init(struct t2_cursor *c, struct t2_buf *key) {
        ASSERT(thread_registered);
        ASSERT(buf_len(key) <= buf_len(&c->curkey));
        ASSERT(c->curkey.nr == 1);
        ASSERT(c->dir == T2_LESS || c->dir == T2_MORE);
        eclear();
        buf_copy(&c->curkey, key);
        c->maxlen = buf_len(&c->curkey);
        c->curkey.seg[0].len = buf_len(key);
        return 0;
}

void t2_cursor_fini(struct t2_cursor *c) {
        ASSERT(thread_registered);
        eclear();
        c->curkey.seg[0].len = c->maxlen;
}

int t2_cursor_next(struct t2_cursor *c) {
        ASSERT(thread_registered);
        eclear();
        return next(c);
}

int t2_lookup_ptr(struct t2_tree *t, void *key, int32_t ksize, void *val, int32_t vsize) {
        struct t2_buf kbuf = { .nr = 1, .seg = { [0] = { .addr = key, .len = ksize } } };
        struct t2_buf vbuf = { .nr = 1, .seg = { [0] = { .addr = val, .len = vsize } } };
        struct t2_rec r = {
                .key = &kbuf,
                .val = &vbuf
        };
        ASSERT(thread_registered);
        eclear();
        return lookup(t, &r);
}

int t2_insert_ptr(struct t2_tree *t, void *key, int32_t ksize, void *val, int32_t vsize) {
        struct t2_buf kbuf = { .nr = 1, .seg = { [0] = { .addr = key, .len = ksize } } };
        struct t2_buf vbuf = { .nr = 1, .seg = { [0] = { .addr = val, .len = vsize } } };
        struct t2_rec r = {
                .key = &kbuf,
                .val = &vbuf
        };
        ASSERT(thread_registered);
        eclear();
        return insert(t, &r);
}

int t2_delete_ptr(struct t2_tree *t, void *key, int32_t ksize) {
        struct t2_buf kbuf = { .nr = 1, .seg = { [0] = { .addr = key, .len = ksize } } };
        struct t2_rec r = {
                .key = &kbuf,
        };
        ASSERT(thread_registered);
        eclear();
        return delete(t, &r);
}


/* @cookie */

#if ON_LINUX

static int cacheline_size() {
        return sysconf(_SC_LEVEL1_DCACHE_LINESIZE);
}

static bool addr_is_valid(void *addr) {
        bool result;
        jmp_buf buf;
        ASSERT(addr_check.buf == NULL);
        if (setjmp(buf) != 0) {
                result = false;
        } else {
                addr_check.buf = &buf;
                uint64_t val = *(volatile uint64_t *)addr;
                addr_check.buf = NULL;
                (void)val;
                result = true;
        }
        return result;
}

#elif ON_DARWIN

#include <sys/sysctl.h>

static int cacheline_size() {
        size_t cacheline = 0;
        size_t size      = sizeof(cacheline);
        NOFAIL(sysctlbyname("hw.cachelinesize", &cacheline, &size, NULL, 0));
        return cacheline;
}

/* https://stackoverflow.com/questions/56177752/safely-checking-a-pointer-for-validity-in-macos */
static bool addr_is_valid(void *addr) {
        vm_map_t                       task    = mach_task_self();
        mach_vm_address_t              address = (mach_vm_address_t)addr;
        mach_msg_type_number_t         count   = VM_REGION_BASIC_INFO_COUNT_64;
        mach_vm_size_t                 size    = 0;
        vm_region_basic_info_data_64_t info;
        mach_port_t                    object_name;
        kern_return_t                  ret;
        ret = mach_vm_region(task, &address, &size, VM_REGION_BASIC_INFO_64, (vm_region_info_t)&info, &count, &object_name);
        return ret == KERN_SUCCESS &&
                address <= ((mach_vm_address_t)addr) &&
                ((mach_vm_address_t)(addr + sizeof(uint64_t))) <= address + size &&
                (info.protection & (VM_PROT_READ | VM_PROT_WRITE)) == (VM_PROT_READ | VM_PROT_WRITE);
}

#endif

static uint64_t cgen = 0;

static void cookie_complete(struct path *p, struct node *n) {
        cookie_load(&n->cookie, &p->rec->cookie);
}

static void cookie_load(uint64_t *addr, struct t2_cookie *k) {
        k->lo = *addr;
        k->hi = (uint64_t)addr;
}

static bool cookie_is_valid(const struct t2_cookie *k) {
        void *addr = (void *)k->hi;
        return addr != NULL && addr_is_valid(addr) && *(uint64_t *)addr == k->lo;
}

static void cookie_invalidate(uint64_t *addr) {
        *addr = 0;
}

static void cookie_make(uint64_t *addr) {
        *addr = ++cgen;
}

/* @cache */

static void pageout(struct node *n) {
        if (LIKELY(n->flags & MODIFIED)) {
                int result = SCALL(n->mod, write, n->addr, n->data);
                if (LIKELY(result == 0)) {
                        CINC(write);
                        CADD(write_bytes, taddr_ssize(n->addr));
                        n->flags &= ~MODIFIED;
                } else {
                        LOG("Pageout failure: %"PRIx64": %i\n", n->addr, result);
                }
        }
}

static void writeout(struct t2 *mod, int32_t toscan, int32_t towrite) {
        int32_t scan0   = mod->writescan;
        int32_t scan    = scan0;
        int32_t scanned = 0;
        int32_t written = 0;
        int32_t mask    = (1 << mod->ht.shift) - 1;
        ASSERT(mod->ht.shift < 32);
        ASSERT((scan0 & mask) == scan0);
        while (true) {
                struct bucket *bucket;
                bool           clean;
                while (!(mod->ht.buckets[scan].flags & DIRTY)) {
                        CINC(wscan_clean);
                        if (++scanned >= toscan) {
                                mod->writescan = scan;
                                return;
                        }
                        scan = (scan + 1) & mask;
                        if (scan == scan0) {
                                return;
                        }
                }
                CINC(wscan_dirty);
                bucket = &mod->ht.buckets[scan];
                mutex_lock(&bucket->lock);
                do {
                        struct cds_hlist_head *head = &bucket->chain;
                        struct node           *n;
                        struct node           *next;
                        clean = true;
                        cds_hlist_for_each_entry_safe_2(n, next, head, hash) {
                                CINC(wscan_node);
                                if (n->ref > 0) {
                                        CINC(wscan_busy);
                                        continue;
                                }
                                if (n->flags & MODIFIED) {
                                        CINC(wscan_written);
                                        ref(n);
                                        mutex_unlock(&bucket->lock);
                                        lock(n, READ);
                                        pageout(n);
                                        unlock(n, READ);
                                        clean = false;
                                        written++;
                                        mutex_lock(&bucket->lock);
                                        put_locked(n, bucket);
                                        break;
                                }
                        }
                } while (!clean);
                bucket->flags &= ~DIRTY;
                mutex_unlock(&bucket->lock);
                scan = (scan + 1) & mask;
                if (written >= towrite) {
                        mod->writescan = scan;
                        return;
                }
        }
}

static void clean(struct t2 *mod, int32_t toscan, int32_t toclean) {
        int32_t scan0   = mod->cleanscan;
        int32_t scan    = scan0;
        int32_t scanned = 0;
        int32_t cleaned = 0;
        int32_t mask    = (1 << mod->ht.shift) - 1;
        ASSERT(mod->ht.shift < 32);
        ASSERT((scan0 & mask) == scan0);
        while (true) {
                struct bucket         *bucket = &mod->ht.buckets[scan];
                struct cds_hlist_head *head;
                struct node           *n;
                struct node           *next;
                if (bucket->flags & ACCESSED) {
                        CINC(cscan_accessed);
                        bucket->flags &= ~ACCESSED;
                } else {
                        CINC(cscan_not_accessed);
                        mutex_lock(&bucket->lock);
                        head = &bucket->chain;
                        cds_hlist_for_each_entry_safe_2(n, next, head, hash) {
                                CINC(cscan_node);
                                if (n->ref == 0 && !(n->flags & MODIFIED)) {
                                        CINC(cscan_cleaned);
                                        put_final(n);
                                        cleaned++;
                                }
                        }
                        mutex_unlock(&bucket->lock);
                }
                if (++scanned >= toscan || cleaned >= toclean) {
                        mod->writescan = scan;
                        return;
                }
                scan = (scan + 1) & mask;
                if (scan == scan0) {
                        return;
                }
        }
}

/* @lib */

__attribute__((noreturn)) static void immanentise(const struct msg_ctx *ctx, ...)
{
        va_list args;
        fprintf(stderr, "%s (%s/%i): Immanentising the eschaton: ", ctx->func, ctx->file, ctx->lineno);
        va_start(args, ctx);
        vfprintf(stderr, ctx->fmt, args);
        va_end(args);
        puts(".\n");
        stacktrace();
        abort();
}

bool t2_is_eptr(void *ptr) {
        return (unsigned long)ptr >= (unsigned long)-MAX_ERR_CODE;
}

void *t2_errptr(int errcode) {
        ASSERT(0 <= errcode && errcode <= MAX_ERR_CODE);
        return (void *)(uint64_t)-errcode;
}

static void *mem_alloc_align(size_t size) {
        void *out = NULL;
        int   result = posix_memalign(&out, size, size);
        if (result == 0) {
                memset(out, 0, size);
        }
        return out;
}

static void *mem_alloc(size_t size) {
        void *out = malloc(size);
        if (out != NULL) {
                memset(out, 0, size);
                return out;
        } else {
                return EPTR(-ENOMEM);
        }
}

static void mem_free(void *ptr) {
        free(ptr);
}

static void llog(const struct msg_ctx *ctx, ...) {
        va_list args;
        fprintf(stderr, "%s (%s/%i): ", ctx->func, ctx->file, ctx->lineno);
        va_start(args, ctx);
        vfprintf(stderr, ctx->fmt, args);
        va_end(args);
        puts(".");
}

static int32_t min_32(int32_t a, int32_t b) {
        return a < b ? a : b;
}

static int32_t max_32(int32_t a, int32_t b) {
        return a > b ? a : b;
}

static int nlz(uint32_t x) { /* Hacker's Delight. */
        x = x | (x >>  1);
        x = x | (x >>  2);
        x = x | (x >>  4);
        x = x | (x >>  8);
        x = x | (x >> 16);
        return __builtin_popcount(~x);
}

static int ilog2(uint32_t x) {
        return 31 - nlz(x);
}

static void edescr(const struct msg_ctx *ctx, int err, uint64_t a0, uint64_t a1) {
        if (edepth < (int)ARRAY_SIZE(estack)) {
                estack[edepth++] = (struct error_descr) {
                        .err = err,
                        .ctx = ctx,
                        .v0  = a0,
                        .v1  = a1
                };
        }
}

static void eclear() {
        edepth = 0;
}

static void eprint() {
        for (int i = 0; i < edepth; ++i) {
                struct error_descr *ed = &estack[i];
                printf("[%s] (%i): ", strerror(-ed->err), ed->err);
                llog(ed->ctx, ed->v0, ed->v1);
        }
}

static void counters_check() {
        if (CVAL(node) != 0) {
                LOG("Leaked node: %i", CVAL(node));
        }
        if (CVAL(rlock) != 0) {
                LOG("Leaked rlock: %i", CVAL(rlock));
        }
        if (CVAL(wlock) != 0) {
                LOG("Leaked wlock: %i", CVAL(wlock));
        }
        if (CVAL(rcu) != 0) {
                LOG("Leaked rcu: %i", CVAL(rcu));
        }
}

static void counter_print(int offset, const char *label) {
        printf("%-15s ", label);
        for (int i = 0; i < ARRAY_SIZE(GVAL(l)); ++i) {
                printf("%10"PRId64" ", *(uint64_t *)(((void *)&GVAL(l[i])) + offset));
        }
        puts("");
}

static void counter_var_print(int offset, const char *label) {
        printf("%-15s ", label);
        for (int i = 0; i < ARRAY_SIZE(CVAL(l)); ++i) {
                struct counter_var *v = (((void *)&GVAL(l[i])) + offset);
                printf("%10.1f ", v->nr ? 1.0 * v->sum / v->nr : 0.0);
        }
        puts("");
}

#define COUNTER_PRINT(counter) \
        counter_print(offsetof(struct level_counters, counter), #counter)

#define COUNTER_VAR_PRINT(counter) \
        counter_var_print(offsetof(struct level_counters, counter), #counter)

static void counters_print() {
        counters_fold();
        printf("peek:               %10"PRId64"\n", GVAL(peek));
        printf("alloc:              %10"PRId64"\n", GVAL(alloc));
        printf("traverse:           %10"PRId64"\n", GVAL(traverse));
        printf("traverse.start:     %10"PRId64"\n", GVAL(traverse_start));
        printf("traverse.iter:      %10"PRId64"\n", GVAL(traverse_iter));
        printf("wscan.clean:        %10"PRId64"\n", GVAL(wscan_clean));
        printf("wscan.dirty:        %10"PRId64"\n", GVAL(wscan_dirty));
        printf("wscan.node:         %10"PRId64"\n", GVAL(wscan_node));
        printf("wscan.busy:         %10"PRId64"\n", GVAL(wscan_busy));
        printf("wscan.written:      %10"PRId64"\n", GVAL(wscan_written));
        printf("cscan.accessed:     %10"PRId64"\n", GVAL(cscan_accessed));
        printf("cscan.not_accessed: %10"PRId64"\n", GVAL(cscan_not_accessed));
        printf("cscan.node:         %10"PRId64"\n", GVAL(cscan_node));
        printf("cscan.cleaned:      %10"PRId64"\n", GVAL(cscan_cleaned));
        printf("read:               %10"PRId64"\n", GVAL(read));
        printf("read.bytes:         %10"PRId64"\n", GVAL(read_bytes));
        printf("write:              %10"PRId64"\n", GVAL(write));
        printf("write.bytes:        %10"PRId64"\n", GVAL(write_bytes));
        printf("%15s ", "");
        for (int i = 0; i < ARRAY_SIZE(CVAL(l)); ++i) {
                printf("%10i ", i);
        }
        puts("");
        COUNTER_PRINT(insert_balance);
        COUNTER_PRINT(delete_balance);
        COUNTER_PRINT(get);
        COUNTER_PRINT(search);
        COUNTER_PRINT(insert);
        COUNTER_PRINT(delete);
        COUNTER_PRINT(bin_iter);
        COUNTER_PRINT(lin_iter);
        COUNTER_PRINT(nospc);
        COUNTER_PRINT(dirmove);
        COUNTER_PRINT(recget);
        COUNTER_PRINT(moves);
        COUNTER_PRINT(make);
        COUNTER_PRINT(shift);
        COUNTER_PRINT(shift_one);
        COUNTER_PRINT(merge);
        COUNTER_VAR_PRINT(nr);
        COUNTER_VAR_PRINT(free);
        COUNTER_VAR_PRINT(keysize);
        COUNTER_VAR_PRINT(valsize);
}

static void counters_clear() {
        SET0(&__g_counters);
}

static void counters_fold() {
        uint64_t *dst = (uint64_t *)&__g_counters;
        uint64_t *src = (uint64_t *)&__t_counters;
        SASSERT(sizeof __g_counters % sizeof(int64_t) == 0);
        mutex_lock(&__g_counters_lock);
        for (long unsigned i = 0; i < (sizeof __g_counters / sizeof(int64_t)); ++i) {
                dst[i] += src[i];
        }
        mutex_unlock(&__g_counters_lock);
        SET0(&__t_counters);
}

static __thread int insigsegv = 0;
static struct sigaction osa = {};
static int signal_set = 0;

static void stacktrace() {
    int    size;
    void  *tracebuf[512];

    size = backtrace(tracebuf, ARRAY_SIZE(tracebuf));
    backtrace_symbols_fd(tracebuf, size, 1);
}

static void sigsegv(int signo, siginfo_t *si, void *uctx) {
        volatile jmp_buf *buf = addr_check.buf;
        if (UNLIKELY(insigsegv++ > 0)) {
                abort(); /* Don't try to print anything. */
        }
        if (ON_LINUX && LIKELY(buf != NULL)) {
                addr_check.buf = NULL;
                --insigsegv;
                longjmp((void *)*buf, 1);
        }
        printf("\nGot: %i errno: %i addr: %p code: %i pid: %i uid: %i ucontext: %p\n",
               signo, si->si_errno, si->si_addr, si->si_code, si->si_pid, si->si_uid, uctx);
        stacktrace();
        --insigsegv;
        if (osa.sa_handler != SIG_DFL && osa.sa_handler != SIG_IGN) {
                if (osa.sa_flags & SA_SIGINFO) {
                        (*osa.sa_sigaction)(signo, si, uctx);
                }
        } else {
                abort();
        }
}

static int signal_init() {
        struct sigaction sa = {
                .sa_sigaction = &sigsegv,
                .sa_flags     = SA_SIGINFO | SA_NODEFER,
        };
        int result = 0;
        if (signal_set == 0) {
                result = sigaction(SIGSEGV, &sa, &osa);
                if (LIKELY(result == 0)) {
                        signal_set = 1;
                }
        }
        return result;
}

static void signal_fini() {
        ASSERT(signal_set > 0);
        if (--signal_set == 0) {
                sigaction(SIGSEGV, &osa, NULL);
        }
}

static void mutex_lock(pthread_mutex_t *lock) {
        NOFAIL(pthread_mutex_lock(lock));
}

static void mutex_unlock(pthread_mutex_t *lock) {
        NOFAIL(pthread_mutex_unlock(lock));
}

/* @ht */

static int ht_init(struct ht *ht, int shift) {
        ht->shift = shift;
        ht->buckets = mem_alloc(sizeof ht->buckets[0] << shift);
        if (ht->buckets != NULL) {
                for (int i = 0; i < (1 << shift); ++i) {
                        NOFAIL(pthread_mutex_init(&ht->buckets[i].lock, NULL));
                }
                return 0;
        }
        return ERROR(-ENOMEM);
}

static void ht_fini(struct ht *ht) {
        for (int i = 0; i < (1 << ht->shift); i++) {
                NOFAIL(pthread_mutex_destroy(&ht->buckets[i].lock));
                ASSERT(ht->buckets[i].chain.next == NULL);
        }
        mem_free(ht->buckets);
}

static void ht_clean(struct ht *ht) {
        for (int i = 0; i < (1 << ht->shift); i++) {
                struct cds_hlist_head *head = &ht->buckets[i].chain;
                struct node           *scan;
                struct node           *next;
                mutex_lock(&ht->buckets[i].lock);
                cds_hlist_for_each_entry_safe_2(scan, next, head, hash) {
                        ht_delete(scan);
                        nfini(scan);
                }
                mutex_unlock(&ht->buckets[i].lock);
        }
}

static uint64_t ht_hash(taddr_t addr) {
        uint64_t x = addr;             /* ChatGPT made me do it. */
        x = (~x) + (x << 21);          /* x = (x << 21) - x - 1; */
        x = x ^ (x >> 24);
        x = (x + (x << 3)) + (x << 8); /* x * 265 */
        x = x ^ (x >> 14);
        x = (x + (x << 2)) + (x << 4); /* x * 21 */
        x = x ^ (x >> 28);
        x = x + (x << 31);
        return x;
}

static struct bucket *ht_bucket(struct ht *ht, taddr_t addr) {
       uint64_t hash = ht_hash(addr) & ((1 << ht->shift) - 1);
       return &ht->buckets[hash];
}

static struct node *ht_lookup(struct ht *ht, taddr_t addr) {
        struct cds_hlist_head *head = &ht_bucket(ht, addr)->chain;
        struct node           *scan;
        cds_hlist_for_each_entry_rcu_2(scan, head, hash) {
                if (scan->addr == addr && LIKELY((scan->flags & HEARD_BANSHEE) == 0)) {
                        return scan;
                }
        }
        return NULL;
}

static void ht_insert(struct ht *ht, struct node *n) {
        struct bucket *b = &ht->buckets[ht_hash(n->addr) & ((1 << ht->shift) - 1)];
        cds_hlist_add_head_rcu(&n->hash, &b->chain);
}

static void ht_delete(struct node *n) {
        cds_hlist_del_rcu(&n->hash);
}

/* @avg */

static uint32_t kval(struct ewma *a) {
        return a->count + (a->avg >> (a->cur - a->last));
}

static void kmod(struct ewma *a, uint32_t t) {
        if (t == a->cur) {
                a->count++;
        } else {
                a->avg   = kval(a);
                a->last  = a->cur;
                a->cur   = t;
                a->count = 1;
        }
}

static uint32_t kavg(struct ewma *a, uint32_t t) {
        return t == a->cur ? a->avg : kval(a) >> (t - a->cur);
}

/* @buf */

static int val_copy(struct t2_rec *r, struct node *n, struct slot *s) { /* r := s */
        struct t2_buf *key    = s->rec.key;
        struct t2_buf *val    = s->rec.val;
        int            result = 0;
        if (s->idx < 0) {
                return ERROR(-ERANGE);
        }
        if (r->kcb != NULL) {
                r->kcb(key, r->arg);
        } else {
                ASSERT(r->key->nr > 0);
                if (LIKELY(buf_len(r->key) >= buf_len(key))) {
                        buf_copy(r->key, key);
                } else {
                        r->key->seg[0].len = buf_len(key);
                        result = ERROR(-ENAMETOOLONG);
                }
        }
        if (r->vcb != NULL) {
                r->vcb(val, r->arg);
        } else {
                ASSERT(r->val->nr > 0);
                if (LIKELY(buf_len(r->val) >= buf_len(val))) {
                        buf_copy(r->val, val);
                } else {
                        r->val->seg[0].len = buf_len(val);
                        result = ERROR(-ENAMETOOLONG);
                }
        }
        return result;
}

static int int32_cmp(int32_t a, int32_t b) {
        return a < b ? -1 : a != b; /* sic. */
}

static int buf_cmp(const struct t2_buf *b0, const struct t2_buf *b1) {
        ASSERT(b0->nr == 1);
        ASSERT(b1->nr == 1);
        uint32_t len0 = b0->seg[0].len;
        uint32_t len1 = b1->seg[0].len;
        return memcmp(b0->seg[0].addr, b1->seg[0].addr, len0 < len1 ? len0 : len1) ?: int32_cmp(len0, len1);
}

static void buf_copy(const struct t2_buf *dst, const struct t2_buf *src) {
        int     didx = 0;
        int32_t doff = 0;
        int     sidx = 0;
        int32_t soff = 0;
        ASSERT(buf_len(dst) >= buf_len(src));
        while (sidx < src->nr && didx < dst->nr) {
                int32_t nob = min_32(src->seg[sidx].len - soff, dst->seg[didx].len - doff);
                memmove(dst->seg[didx].addr + doff, src->seg[sidx].addr + soff, nob);
                doff += nob;
                soff += nob;
                if (doff == dst->seg[didx].len) {
                        ++didx;
                        doff = 0;
                }
                if (soff == src->seg[sidx].len) {
                        ++sidx;
                        soff = 0;
                }
        }
}

static int32_t buf_len(const struct t2_buf *b) {
        int32_t len = 0;
        for (int i = 0; i < b->nr; ++i) {
                len += b->seg[i].len;
        }
        return len;
}

static int32_t rec_len(const struct t2_rec *r) {
        return buf_len(r->key) + buf_len(r->val);
}

static int buf_alloc(struct t2_buf *dst, struct t2_buf *src) {
        int32_t len = buf_len(src);
        ASSERT(dst->seg[0].addr == NULL);
        dst->nr = 1;
        dst->seg[0].len = len;
        dst->seg[0].addr = mem_alloc(len);
        if (dst->seg[0].addr != NULL) {
                buf_copy(dst, src);
                return 0;
        } else {
                SET0(dst);
                return ERROR(-ENOMEM);
        }
}

static void buf_free(struct t2_buf *b) {
        for (int32_t i = 0; i < b->nr; ++i) {
                mem_free(b->seg[i].addr);
                SET0(&b->seg[i]);
        }
}

/* @simple */

struct dir_element {
        int32_t koff; /* Start of the key. */
        int32_t voff; /* End of the value. */
};

struct sheader { /* Simple node format. */
        struct header head;
        int32_t       dir_off;
        int16_t       nr;
        int16_t       pad;
};

static struct dir_element *sdir(struct sheader *sh) {
        return (void *)sh + sh->dir_off; /* Always within node. */
}

static struct dir_element *sat(struct sheader *sh, int pos) {
        return sdir(sh) + pos; /* Always within node. */
}

static bool is_in(int32_t lo, int32_t v, int32_t hi) {
        return lo <= v && v <= hi;
}

static int32_t dirsize(int32_t n) {
        return n * SOF(struct dir_element);
}

static bool scheck(struct sheader *sh, const struct node_type *nt) {
        int32_t size = (int32_t)1 << nt->shift;
        int32_t dend = sh->dir_off + dirsize(sh->nr + 1);
        return  is_in(SOF(*sh), sh->dir_off, size) &&
                is_in(SOF(*sh), dend, size) &&
                FORALL(i, sh->nr + 1,
                       is_in(SOF(*sh), sat(sh, i)->koff, sh->dir_off) &&
                       is_in(dend, sat(sh, i)->voff, size));
                FORALL(i, sh->nr,
                       sat(sh, i)->koff  < sat(sh, i + 1)->koff &&
                       sat(sh, i)->voff >= sat(sh, i + 1)->voff);
}

static int32_t sdirsize(struct sheader *sh) {
        return dirsize(sh->nr + 1);
}

static int32_t sdirend(struct sheader *sh) {
        return sh->dir_off + sdirsize(sh);
}

static int32_t skeyoff(struct sheader *sh, int pos, int32_t *size) {
        struct dir_element *del = sat(sh, pos);
        *size = sat(sh, pos + 1)->koff - del->koff;
        return del->koff;
}

static void *skey(struct sheader *sh, int pos, int32_t *size) {
        return (void *)sh + skeyoff(sh, pos, size);
}

static void *sval(struct sheader *sh, int pos, int32_t *size) {
        struct dir_element *del = sat(sh, pos + 1);
        *size = sat(sh, pos)->voff  - del->voff;
        return (void *)sh + del->voff;
}

static char cmpch(int cmp) {
        return cmp < 0 ? '<' : cmp == 0 ? '=' : '>';
}

static void range_print(void *orig, int32_t nsize, void *start, int32_t nob);

static int skeycmp(struct sheader *sh, int pos, void *key, int32_t klen, uint32_t mask) {
        int32_t ksize;
        int32_t koff = skeyoff(sh, pos, &ksize) & mask;
        ksize = min_32(ksize & mask, mask + 1 - koff);
        CMOD(l[sh->head.level].keysize, ksize);
        return memcmp((void *)sh + koff, key, ksize < klen ? ksize : klen) ?: int32_cmp(ksize, klen);
}

static struct sheader *simple_header(const struct node *n) {
        return n->data;
}

static void buf_clip(struct t2_buf *b, uint32_t mask, void *origin) {
        ASSERT(b->nr == 1);
        int32_t off = (b->seg[0].addr - origin) & mask;
        b->seg[0].addr = origin + off;
        b->seg[0].len  = min_32(b->seg[0].len & mask, mask + 1 - off);
}

static void buf_clip_node(struct t2_buf *b, const struct node *n) {
        buf_clip(b, nsize(n) - 1, n->data);
}

enum { LINEAR = 1 }; /* Effects of switching to linear search seem to be minimal. */

static bool simple_search(struct node *n, struct t2_rec *rec, struct slot *out) {
        ASSERT(rec->key->nr == 1);
        bool            found = false;
        struct sheader *sh    = simple_header(n);
        int             l     = -1;
        int             r     = sh->nr;
        void           *kaddr = rec->key->seg[0].addr;
        int32_t         klen  = rec->key->seg[0].len;
        int             cmp   = -1;
        uint32_t        mask  = nsize(n) - 1;
        ASSERT((nsize(n) & mask) == 0);
        ASSERT(((uint64_t)sh & mask) == 0);
        EXPENSIVE_ASSERT(scheck(sh, n->ntype));
        CINC(l[level(n)].search);
        while (r - l > LINEAR) {
                int m = (l + r) >> 1;
                CINC(l[level(n)].bin_iter);
                cmp = skeycmp(sh, m, kaddr, klen, mask);
                if (cmp > 0) {
                        r = m;
                } else {
                        l = m;
                        if (cmp == 0) {
                                found = true;
                                goto here;
                        }
                }
        }
        while (r - l > 1) {
                CINC(l[level(n)].lin_iter);
                cmp = skeycmp(sh, ++l, kaddr, klen, mask);
                if (cmp >= 0) {
                        if (cmp > 0) {
                                --l;
                        } else {
                                found = true;
                        }
                        break;
                }
        }
 here:
        out->idx = l;
        if (0 <= l && l < sh->nr) {
                struct t2_buf *key = out->rec.key;
                struct t2_buf *val = out->rec.val;
                key->nr = 1;
                key->seg[0].addr = skey(sh, l, &key->seg[0].len);
                buf_clip(key, mask, sh);
                val->nr = 1;
                val->seg[0].addr = sval(sh, l, &val->seg[0].len);
                buf_clip(val, mask, sh);
                CMOD(l[level(n)].keysize, key->seg[0].len);
                CMOD(l[level(n)].valsize, key->seg[0].len);
        }
        return found;
}

static taddr_t internal_addr(const struct slot *s) {
        taddr_t addr = 0;
        buf_clip_node(s->rec.key, s->node);
        buf_clip_node(s->rec.val, s->node);
        s->rec.val->seg[0].len = min_32(s->rec.val->seg[0].len, sizeof addr);
        ASSERT(s->rec.val->nr > 0 && s->rec.val->seg[0].len >= 0);
        memcpy(&addr, s->rec.val->seg[0].addr, s->rec.val->seg[0].len);
        return taddr_is_valid(addr) ? addr : 0;
}

static taddr_t internal_search(struct node *n, struct t2_rec *r, int32_t *pos) {
        SLOT_DEFINE(s, n);
        SET0(s.rec.key);
        SET0(s.rec.val);
        s.rec.key->nr = 1;
        s.rec.val->nr = 1;
        (void)simple_search(n, r, &s);
        if (s.idx < 0) {
                rec_get(&s, 0);
        }
        *pos = s.idx;
        return internal_addr(&s);
}

static taddr_t internal_get(const struct node *n, int32_t pos) {
        if (LIKELY(0 <= pos && pos < nr(n) && !is_leaf(n))) {
                SLOT_DEFINE(s, (struct node *)n);
                rec_get(&s, pos);
                return internal_addr(&s);
        } else {
                return 0; /* Concurrent modification. */
        }
}

static struct node *internal_child(const struct node *n, int32_t pos, bool peekp) {
        return (peekp ? peek : get)(n->mod, internal_get(n, pos));
}

static int leaf_search(struct node *n, struct t2_rec *r, struct slot *s) {
        bool found;
        s->rec.key->nr = 1;
        s->rec.val->nr = 1;
        found = simple_search(n, r, s);
        buf_clip_node(s->rec.key, n);
        buf_clip_node(s->rec.val, n);
        return found;
}

static int32_t sfreekey(struct node *n) {
        struct sheader *sh  = simple_header(n);
        return sh->dir_off - sat(sh, sh->nr)->koff;
}

static int32_t sfreeval(struct node *n) {
        struct sheader *sh  = simple_header(n);
        return sat(sh, sh->nr)->voff - sdirend(sh);
}

static int32_t simple_free(const struct node *n) {
        struct sheader     *sh  = simple_header(n);
        struct dir_element *end = sat(sh, sh->nr);
        return end->voff - end->koff - sdirsize(sh);
}

static void move(void *sh, int32_t start, int32_t end, int delta) {
        ASSERT(start <= end);
        memmove(sh + start + delta, sh + start, end - start);
        CADD(l[((struct sheader *)sh)->head.level].moves, end - start);
}

static void sdirmove(struct sheader *sh, int32_t nsize,
                     int32_t knob, int32_t vnob, int32_t nr) {
        int32_t dir_off = (knob * (nsize - SOF(*sh))) / (knob + vnob) -
                dirsize(nr + 1) / 2 + SOF(*sh);
        dir_off = min_32(max_32(dir_off, knob + SOF(*sh)),
                         nsize - vnob - dirsize(nr + 1));
        ASSERT(knob + SOF(*sh) <= dir_off);
        ASSERT(dir_off + dirsize(nr + 1) + vnob <= nsize);
        move(sh, sh->dir_off, sdirend(sh), dir_off - sh->dir_off);
        sh->dir_off = dir_off;
}

static int simple_can_insert(const struct slot *s) {
        return simple_free(s->node) >= rec_len(&s->rec) + SOF(struct dir_element);
}

static int32_t simple_used(const struct node *n) {
        struct sheader     *sh  = simple_header(n);
        struct dir_element *beg = sat(sh, 0);
        struct dir_element *end = sat(sh, sh->nr);
        return end->koff - beg->koff + beg->voff - end->voff;
}

static bool simple_can_merge(const struct node *n0, const struct node *n1) {
        return simple_free(n0) >= simple_used(n1) + dirsize(simple_nr(n1));
}

static int simple_insert(struct slot *s) {
        struct t2_buf       buf;
        struct sheader     *sh   = simple_header(s->node);
        struct dir_element *end  = sat(sh, sh->nr);
        struct dir_element *piv;
        int32_t             klen = buf_len(s->rec.key);
        int32_t             vlen = buf_len(s->rec.val);
        ASSERT(s->idx <= sh->nr);
        EXPENSIVE_ASSERT(scheck(sh, s->node->ntype));
        CINC(l[sh->head.level].insert);
        if (simple_free(s->node) < klen + vlen + SOF(struct dir_element)) {
                CINC(l[sh->head.level].nospc);
                return -ENOSPC;
        }
        if (sfreekey(s->node) < klen || sfreeval(s->node) < vlen + SOF(*end)) {
                struct dir_element *beg = sat(sh, 0);
                sdirmove(sh, beg->voff, end->koff - beg->koff + klen,
                         beg->voff - end->voff + vlen, sh->nr + 1);
                end = sat(sh, sh->nr);
                CINC(l[sh->head.level].dirmove);
        }
        piv = sat(sh, s->idx);
        move(sh, piv->koff, end->koff, +klen);
        move(sh, end->voff, piv->voff, -vlen);
        for (int32_t i = ++sh->nr; i > s->idx; --i) {
                struct dir_element *prev = sat(sh, i - 1);
                *sat(sh, i) = (struct dir_element){
                        .koff = prev->koff + klen,
                        .voff = prev->voff - vlen
                };
        }
        buf.nr = 1;
        buf.seg[0].addr = skey(sh, s->idx, &buf.seg[0].len);
        ASSERT(buf.seg[0].len == klen);
        buf_copy(&buf, s->rec.key);
        buf.seg[0].addr = sval(sh, s->idx, &buf.seg[0].len);
        ASSERT(buf.seg[0].len == vlen);
        buf_copy(&buf, s->rec.val);
        EXPENSIVE_ASSERT(scheck(sh, s->node->ntype));
        return 0;
}

static void simple_delete(struct slot *s) {
        struct sheader     *sh   = simple_header(s->node);
        struct dir_element *end  = sat(sh, sh->nr);
        struct dir_element *piv  = sat(sh, s->idx);
        struct dir_element *inn  = sat(sh, s->idx + 1);
        int32_t             klen = inn->koff - piv->koff;
        int32_t             vlen = piv->voff - inn->voff;
        ASSERT(s->idx < sh->nr);
        EXPENSIVE_ASSERT(scheck(sh, s->node->ntype));
        CINC(l[sh->head.level].delete);
        move(sh, inn->koff, end->koff, -klen);
        move(sh, end->voff, inn->voff, +vlen);
        for (int32_t i = s->idx; i < sh->nr; ++i) {
                struct dir_element *next = sat(sh, i + 1);
                *sat(sh, i) = (struct dir_element){
                        .koff = next->koff - klen,
                        .voff = next->voff + vlen
                };
        }
        --sh->nr;
        EXPENSIVE_ASSERT(scheck(sh, s->node->ntype));
}

static void simple_get(struct slot *s) {
        struct sheader *sh = simple_header(s->node);
        s->rec.key->nr = 1;
        s->rec.val->nr = 1;
        s->rec.key->seg[0].addr = skey(sh, s->idx, &s->rec.key->seg[0].len);
        s->rec.val->seg[0].addr = sval(sh, s->idx, &s->rec.val->seg[0].len);
        EXPENSIVE_ASSERT(scheck(sh, s->node->ntype));
        CINC(l[sh->head.level].recget);
}

static void simple_make(struct node *n) {
        int32_t         size = nsize(n);
        struct sheader *sh   = simple_header(n);
        sh->dir_off = SOF(*sh) + (size - SOF(*sh)) / 2;
        *sat(sh, 0) = (struct dir_element){ .koff = SOF(*sh), .voff = size };
        CINC(l[sh->head.level].make);
}

static int32_t simple_nr(const struct node *n) {
        return simple_header(n)->nr;
}

static void range_print(void *orig, int32_t nsize, void *start, int32_t nob) {
        static const char hexdigit[] = "0123456789abcdef";
        int32_t off = (int32_t)(start - orig);
        printf("[%4u .. %4u : ", off, off + nob);
        if (is_in(0, off, nsize) &&
            is_in(0, off + nob, nsize)) {
                for (int32_t i = 0; i < nob; ++i) {
                        int ch = ((char *)orig)[off + i];
                        printf("%c%c ", hexdigit[(ch >> 4) & 0xf], hexdigit[ch & 0xf]);
                }
        } else {
                printf("out of range");
        }
        printf("]");
}

static void simple_print(struct node *n) {
        int32_t         size = nsize(n);
        struct sheader *sh   = simple_header(n);
        if (n == NULL) {
                printf("nil node");
        }
        printf("addr: %"PRIx64" tree: %"PRIx32" level: %u ntype: %u nr: %u size: %u dir_off: %u dir_end: %u (%p)\n",
               n->addr, sh->head.treeid, sh->head.level, sh->head.ntype,
               sh->nr, size, sh->dir_off, sdirend(sh), n);
        for (int32_t i = 0; i <= sh->nr; ++i) {
                struct dir_element *del = sat(sh, i);
                printf("        %4u %4u %4u: ", i, del->koff, del->voff);
                if (i < sh->nr) {
                        int32_t kvsize;
                        void   *addr = skey(sh, i, &kvsize);
                        range_print(sh, size, addr, kvsize);
                        printf(" ");
                        addr = sval(sh, i, &kvsize);
                        range_print(sh, size, addr, kvsize);
                        if (!is_leaf(n)) {
                                printf("    (%p)", peek(n->mod, internal_get(n, i)));
                        }
                }
                printf("\n");
        }
}

static void buf_print(const struct t2_buf *b) {
        ASSERT(b->nr == 1);
        range_print(b->seg[0].addr, b->seg[0].len, b->seg[0].addr, b->seg[0].len);
}

static void rec_print(const struct t2_rec *r) {
        printf("key: ");
        buf_print(r->key);
        printf(" val: ");
        buf_print(r->val);
}

static int shift_one(struct node *d, struct node *s, enum dir dir) {
        struct t2_buf key = {};
        struct t2_buf val = {};
        struct slot   dst = { .node = d, .rec = { .key = &key, .val = &val } };
        struct slot   src = { .node = s, .rec = { .key = &key, .val = &val } };
        ASSERT(nr(s) > 0);
        rec_get(&src, utmost(s, dir));
        dst.idx = dir == LEFT ? nr(d) : 0;
        CINC(l[level(d)].shift_one);
        return simple_insert(&dst) ?: (simple_delete(&src), 0);
}

static int shift(struct node *d, struct node *s, const struct slot *point, enum dir dir) {
        int result = 0;
        ASSERT(dir == LEFT || dir == RIGHT);
        ASSERT(point->idx >= 0 && point->idx <= nr(s));
        ASSERT(simple_free(d) > simple_free(s));
        ASSERT(4 * rec_len(&point->rec) < min_32(nsize(d), nsize(s)));
        CINC(l[level(d)].shift);
        while (LIKELY(result == 0)) {
                SLOT_DEFINE(slot, s);
                rec_get(&slot, utmost(s, dir));
                if (simple_free(d) - simple_free(s) > rec_len(&slot.rec)) {
                        result = shift_one(d, s, dir);
                } else {
                        break;
                }
        }
        ASSERT(can_insert(point->idx <= nr(s) ? s : d, &point->rec));
        return result;
}

static int merge(struct node *d, struct node *s, enum dir dir) {
        int result = 0;
        while (LIKELY(result == 0) && nr(s) > 0) {
                result = shift_one(d, s, dir);
        }
        CINC(l[level(d)].merge);
        return result;
}

#if UT

/* @mock */

struct mock_storage {
        struct t2_storage gen;
};

static int mso_init(struct t2_storage *storage) {
        return 0;
}

static void mso_fini(struct t2_storage *storage) {
}

static taddr_t mso_alloc(struct t2_storage *storage, int shift_min, int shift_max) {
        void *addr;
        taddr_t result = posix_memalign(&addr, 1ul << TADDR_MIN_SHIFT,
                                        1ul << shift_max);
        if (LIKELY(result == 0)) {
                ASSERT(((uint64_t)addr & TADDR_ADDR_MASK) == (uint64_t)addr);
                memset(addr, 0, 1ul << shift_max);
                result = taddr_make((uint64_t)addr, shift_max);
        } else {
                result = ERROR(-result);
        }
        return result;
}

static void mso_free(struct t2_storage *storage, taddr_t addr) {
        free((void *)taddr_saddr(addr));
}

static int mso_read(struct t2_storage *storage, taddr_t addr, void *dst) {
        if (taddr_ssize(addr) <= 4096 && FORALL(i, taddr_ssize(addr) / 8, addr_is_valid((void *)taddr_saddr(addr) + 8 * i))) {
                memcpy(dst, (void *)taddr_saddr(addr), taddr_ssize(addr));
                return 0;
        } else {
                return -ESTALE;
        }
}

static int mso_write(struct t2_storage *storage, taddr_t addr, void *src) {
        memcpy((void *)taddr_saddr(addr), src, taddr_ssize(addr));
        return 0;
}

static struct t2_storage_op mock_storage_op = {
        .name     = "mock-storage-op",
        .init     = &mso_init,
        .fini     = &mso_fini,
        .alloc    = &mso_alloc,
        .free     = &mso_free,
        .read     = &mso_read,
        .write    = &mso_write
};

static __attribute__((unused)) struct t2_storage mock_storage = {
        .op = &mock_storage_op
};

/* @file */

struct file_storage {
        struct t2_storage gen;
        const char       *filename;
        pthread_mutex_t   lock;
        int               fd;
        uint64_t          free;
};

static int file_init(struct t2_storage *storage) {
        struct file_storage *fs = COF(storage, struct file_storage, gen);
        fs->fd = open(fs->filename, O_RDWR | O_CREAT, 0777);
        if (fs->fd > 0) {
                fs->free = 512;
                return pthread_mutex_init(&fs->lock, NULL);
        } else {
                return ERROR(-errno);
        }
}

static void file_fini(struct t2_storage *storage) {
        struct file_storage *fs = COF(storage, struct file_storage, gen);
        if (fs->fd > 0) {
                pthread_mutex_destroy(&fs->lock);
                close(fs->fd);
                fs->fd = -1;
        }
}

static taddr_t file_alloc(struct t2_storage *storage, int shift_min, int shift_max) {
        struct file_storage *fs = COF(storage, struct file_storage, gen);
        taddr_t              result;
        mutex_lock(&fs->lock);
        result = taddr_make((uint64_t)fs->free, shift_min);
        fs->free += (uint64_t)1 << shift_min;
        mutex_unlock(&fs->lock);
        return result;
}

static void file_free(struct t2_storage *storage, taddr_t addr) {
}

static int file_read(struct t2_storage *storage, taddr_t addr, void *dst) {
        struct file_storage *fs    = COF(storage, struct file_storage, gen);
        uint64_t             off   = taddr_saddr(addr);
        int                  count = taddr_ssize(addr);
        int                  result;
        if (UNLIKELY(off >= fs->free)) {
                return -ESTALE;
        }
        result = pread(fs->fd, dst, count, off);
        if (LIKELY(result == count)) {
                return 0;
        } else if (result < 0) {
                return ERROR(result);
        } else {
                printf("%"PRIx64" %i %i\n", off, count, result);
                return ERROR(-EIO);
        }
}

static int file_write(struct t2_storage *storage, taddr_t addr, void *src) {
        struct file_storage *fs    = COF(storage, struct file_storage, gen);
        uint64_t             off   = taddr_saddr(addr);
        int                  count = taddr_ssize(addr);
        int                  result;
        if (UNLIKELY(off >= fs->free)) {
                return -ESTALE;
        }
        result = pwrite(fs->fd, src, count, off);
        if (LIKELY(result == count)) {
                return 0;
        } else if (result < 0) {
                return ERROR(result);
        } else {
                return ERROR(-EIO);
        }
}

static struct t2_storage_op file_storage_op = {
        .name     = "file-storage-op",
        .init     = &file_init,
        .fini     = &file_fini,
        .alloc    = &file_alloc,
        .free     = &file_free,
        .read     = &file_read,
        .write    = &file_write
};

static struct file_storage file_storage = {
        .gen      = { .op = &file_storage_op },
        .filename = "./pages"
};

/* @ut */

static struct t2_storage *ut_storage = &file_storage.gen;

static void usuite(const char *suite) {
        printf("        %s\n", suite);
}

static const char *test = NULL;

static void utestdone() {
        printf("done.\n");
        test = NULL;
}

static void utest(const char *t) {
        if (test != NULL) {
                utestdone();
        }
        printf("                . %-15s ", t);
        test = t;
}

static void populate(struct slot *s, struct t2_buf *key, struct t2_buf *val) {
        struct sheader *sh = simple_header(s->node);
        for (int32_t i = 0; simple_free(s->node) >=
                     buf_len(key) + buf_len(val) + SOF(struct dir_element); ++i) {
                NOFAIL(simple_insert(s));
                ASSERT(sh->nr == i + 1);
                ((char *)key->seg[0].addr)[1]++;
                ((char *)val->seg[0].addr)[1]++;
                s->idx = (s->idx + 7) % sh->nr;
        }
}

static void buf_init_str(struct t2_buf *b, const char *s) {
        b->nr = 1;
        b->seg[0].len  = (int32_t)strlen(s) + 1;
        b->seg[0].addr = (void *)s;
}

static bool is_sorted(struct node *n) {
        struct sheader *sh = simple_header(n);
        SLOT_DEFINE(ss, n);
        char   *keyarea = NULL;
        int32_t keysize = 0;
        for (int32_t i = 0; i < sh->nr; ++i) {
                rec_get(&ss, i);
                if (i > 0) {
                        int cmp = skeycmp(sh, i, keyarea, keysize, nsize(n) - 1);
                        if (cmp <= 0) {
                                printf("Misordered at %i: ", i);
                                range_print(keyarea, keysize,
                                            keyarea, keysize);
                                printf(" %c ", cmpch(cmp));
                                range_print(n->data, nsize(n),
                                            ss.rec.key->seg[0].addr,
                                            ss.rec.key->seg[0].len);
                                printf("\n");
                                simple_print(n);
                                return false;
                        }
                }
                keyarea = ss.rec.key->seg[0].addr;
                keysize = ss.rec.key->seg[0].len;
        }
        return true;
}

static struct node_type ntype = {
        .id    = 8,
        .name  = "simple-ut",
        .shift = 9
};

static struct node_type *tree_ntype(struct t2_tree *t, int level) {
        return &ntype;
}

static struct t2_tree_type ttype = {
        .id       = 7,
        .name     = "tree-type-ut",
        .ntype    = &tree_ntype
};

static void simple_ut() {
        struct node n = {
                .ntype = &ntype,
                .addr  = taddr_make(0x100000, ntype.shift),
                .data  = mem_alloc_align(1ul << ntype.shift)
        };
        ASSERT(n.data != NULL);
        struct sheader *sh = simple_header(&n);
        char key0[] = "KEY0";
        char val0[] = "VAL0--";
        struct t2_buf val;
        struct t2_buf key;
        struct slot s = {
                .node = &n,
                .idx = 0,
                .rec = {
                        .key = &key,
                        .val = &val
                }
        };
        int result;
        buf_init_str(&key, key0);
        buf_init_str(&val, val0);
        usuite("simple-node");
        utest("make");
        simple_make(&n);
        ASSERT(sh->nr == 0);
        utest("insert");
        populate(&s, &key, &val);
        result = simple_insert(&s);
        ASSERT(result == -ENOSPC);
        utest("get");
        for (int32_t i = 0; i < sh->nr; ++i) {
                rec_get(&s, i);
                ASSERT(buf_len(s.rec.key) == (int32_t)strlen(key0) + 1);
                ASSERT(buf_len(s.rec.val) == (int32_t)strlen(val0) + 1);
        }
        utest("delete");
        for (int32_t i = sh->nr - 1; i >= 0; --i) {
                s.idx = (s.idx + 7) % sh->nr;
                simple_delete(&s);
                ASSERT(sh->nr == i);
        }
        s.idx = 0;
        while (nr(&n) > 0) {
                simple_delete(&s);
        }
        utest("search");
        key0[1] = 'a';
        while (simple_free(&n) > buf_len(&key) + buf_len(&val) + SOF(struct dir_element)) {
                result = simple_search(&n, &s.rec, &s);
                ASSERT(!result);
                ASSERT(-1 <= s.idx && s.idx < nr(&n));
                s.idx++;
                key = BUF_VAL(key0);
                val = BUF_VAL(val0);
                NOFAIL(simple_insert(&s));
                ASSERT(is_sorted(&n));
                key0[1] += 251; /* Co-prime with 256. */
                if (key0[1] == 'a') {
                        key0[2]++;
                }
                val0[1]++;
        }
        utestdone();
}

static struct node *node_alloc_ut(struct t2 *mod, uint64_t blk) {
        struct node *n = mem_alloc(sizeof *n);
        n->addr = taddr_make(blk & TADDR_ADDR_MASK, 9);
        n->mod = mod;
        return n;
}

static void ht_ut() {
        const uint64_t N = 10000;
        struct t2 mod = {};
        usuite("ht");
        utest("collision");
        for (uint64_t i = 0; i < N; ++i) {
                for (uint64_t j = 0; j < i; ++j) {
                        ASSERT(ht_hash(i) != ht_hash(j));
                        ASSERT(ht_hash(2 * N + i * i * i) != ht_hash(2 * N + j * j * j));
                }
        }
        ht_init(&mod.ht, 10);
        utest("insert");
        for (uint64_t i = 0; i < N; ++i) {
                ht_insert(&mod.ht, node_alloc_ut(&mod, ht_hash(i)));
        }
        utest("lookup");
        for (uint64_t i = 0; i < N; ++i) {
                taddr_t blk = taddr_make(ht_hash(i) & TADDR_ADDR_MASK, 9);
                struct node *n = ht_lookup(&mod.ht, blk);
                ASSERT(n != NULL);
                ASSERT(n->addr == blk);
        }
        utest("delete");
        for (uint64_t i = 0; i < N; ++i) {
                taddr_t blk = taddr_make(ht_hash(i) & TADDR_ADDR_MASK, 9);
                struct node *n = ht_lookup(&mod.ht, blk);
                ht_delete(n);
        }
        utest("fini");
        ht_fini(&mod.ht);
        utestdone();
}

static void traverse_ut() {
        taddr_t addr = taddr_make(0x100000, ntype.shift);
        struct node n = {
                .ntype = &ntype,
                .addr  = addr,
                .data  = mem_alloc_align(1ul << ntype.shift)
        };
        ASSERT(n.data != NULL);
        struct sheader *sh = simple_header(&n);
        *sh = (struct sheader) {
                .head = {
                        .magix = NODE_MAGIX,
                        .ntype = ntype.id,
                        .level = 0,
                }
        };
        char key0[] = "0";
        char val0[] = "+";
        struct t2_buf val;
        struct t2_buf key;
        struct slot s = {
                .node = &n,
                .idx = 0,
                .rec = {
                        .key = &key,
                        .val = &val
                }
        };
        struct t2_tree t = {
                .ttype = &ttype,
                .root  = addr
        };
        struct path p = {
                .tree = &t,
                .opt  = LOOKUP,
                .rec  = &s.rec
        };
        int result;
        usuite("traverse");
        utest("t2_init");
        struct t2 *mod = t2_init(ut_storage, 10);
        t2_node_type_register(mod, &ntype);
        ttype.mod = mod;
        buf_init_str(&key, key0);
        buf_init_str(&val, val0);
        n.mod = mod;
        utest("prepare");
        simple_make(&n);
        ht_insert(&mod->ht, &n);
        for (int i = 0; i < 20; ++i, key0[0] += 2) {
                result = simple_search(&n, &s.rec, &s);
                ASSERT(!result);
                s.idx++;
                buf_init_str(&key, key0);
                buf_init_str(&val, val0);
                NOFAIL(simple_insert(&s));
                ASSERT(is_sorted(&n));
        }
        utest("existing");
        key0[0] = '0';
        NOFAIL(traverse(&p));
        key0[0] = '2';
        p.used = 0;
        NOFAIL(traverse(&p));
        key0[0] = '8';
        p.used = 0;
        NOFAIL(traverse(&p));
        utest("too-small");
        key0[0] = ' ';
        p.used = 0;
        result = traverse(&p);
        ASSERT(result == -ENOENT);
        utest("non-existent");
        key0[0] = '1';
        p.used = 0;
        result = traverse(&p);
        ASSERT(result == -ENOENT);
        ht_delete(&n);
        utest("t2_fini");
        t2_node_type_degister(&ntype);
        t2_fini(mod);
        utestdone();
}

static void insert_ut() {
        usuite("insert");
        utest("init");
        char key0[] = "0";
        char val0[] = "+";
        struct t2_buf val;
        struct t2_buf key;
        struct t2_tree t = {
                .ttype = &ttype
        };
        struct t2 *mod = t2_init(ut_storage, 10);
        struct t2_rec r = {
                .key = &key,
                .val = &val
        };
        int result;
        ASSERT(EISOK(mod));
        t2_node_type_register(mod, &ntype);
        ttype.mod = mod;
        buf_init_str(&key, key0);
        buf_init_str(&val, val0);
        struct node *n = alloc(&t, 0);
        ASSERT(n != NULL && EISOK(n));
        simple_make(n);
        t.root = n->addr;
        put(n);
        utest("insert-1");
        NOFAIL(t2_insert(&t, &r));
        utest("eexist");
        result = t2_insert(&t, &r);
        ASSERT(result == -EEXIST);
        utest("fini");
        t2_node_type_degister(&ntype);
        t2_fini(mod);
        utestdone();
}

static void tree_ut() {
        usuite("tree");
        utest("init");
        char key0[] = "0";
        char val0[] = "+";
        struct t2_buf val;
        struct t2_buf key;
        struct t2_tree *t;
        struct t2 *mod;
        struct t2_rec r = {
                .key = &key,
                .val = &val
        };
        uint64_t k64;
        uint64_t v64;
        int result;
        mod = t2_init(ut_storage, 20);
        ttype.mod = NULL;
        t2_tree_type_register(mod, &ttype);
        t2_node_type_register(mod, &ntype);
        t = t2_tree_create(&ttype);
        ASSERT(EISOK(t));
        buf_init_str(&key, key0);
        buf_init_str(&val, val0);
        utest("insert-1");
        NOFAIL(t2_insert(t, &r));
        utest("eexist");
        result = t2_insert(t, &r);
        ASSERT(result == -EEXIST);
        utest("5K");
        key = BUF_VAL(k64);
        val = BUF_VAL(v64);
        for (k64 = 0; k64 < 5000; ++k64) {
                NOFAIL(t2_insert(t, &r));
        }
        utest("20K");
        key = BUF_VAL(k64);
        val = BUF_VAL(v64);
        for (int i = 0; i < 20000; ++i) {
                k64 = ht_hash(i);
                v64 = ht_hash(i + 1);
                NOFAIL(t2_insert(t, &r));
        }
        utest("50K");
        for (int i = 0; i < 50000; ++i) {
                k64 = ht_hash(i);
                v64 = ht_hash(i + 1);
                result = t2_insert(t, &r);
                ASSERT(result == (i < 20000 ? -EEXIST : 0));
        }
        utest("check");
        for (int i = 0; i < 50000; ++i) {
                k64 = ht_hash(i);
                NOFAIL(t2_lookup(t, &r));
                ASSERT(v64 == ht_hash(i + 1));
        }
        utest("fini");
        t2_node_type_degister(&ntype);
        t2_fini(mod);
        utestdone();
}

static void fill(char *x, int nr) {
        for (int i = 0; i < nr; ++i) {
                x[i] = rand() & 0xff;
        }
}

static void stress_ut() {
        struct t2      *mod;
        struct t2_tree *t;
        char key[1ul << ntype.shift];
        char val[1ul << ntype.shift];
        struct t2_buf keyb = BUF_VAL(key);
        struct t2_buf valb = BUF_VAL(val);
        struct t2_rec r = {
                .key = &keyb,
                .val = &valb
        };
        int32_t maxsize = ((int32_t)1 << (ntype.shift - 3)) - 10;
        int exist = 0;
        int32_t ksize;
        int32_t vsize;
        int     result;
        usuite("stress");
        utest("init");
        mod = t2_init(ut_storage, 20);
        ASSERT(EISOK(mod));
        ttype.mod = NULL;
        t2_tree_type_register(mod, &ttype);
        t2_node_type_register(mod, &ntype);
        t = t2_tree_create(&ttype);
        ASSERT(EISOK(t));
        utest("probe");
        long U = 500000;
        for (long i = 0; i < U; ++i) {
                ksize = sizeof i;
                vsize = rand() % maxsize;
                ASSERT(ksize < SOF(key));
                ASSERT(vsize < SOF(val));
                ASSERT(4 * (ksize + vsize) < ((int32_t)1 << ntype.shift));
                *(long *)key = i;
                fill(val, vsize);
                keyb.seg[0] = (struct t2_seg){ .len = ksize, .addr = &key };
                valb.seg[0] = (struct t2_seg){ .len = vsize, .addr = &val };
                NOFAIL(t2_insert(t, &r));
                for (int j = 0; j < 10; ++j) {
                        long probe = rand();
                        *(long *)key = probe;
                        keyb.seg[0] = (struct t2_seg){ .len = ksize,      .addr = &key };
                        valb = BUF_VAL(val);
                        result = t2_lookup(t, &r);
                        ASSERT((result ==       0) == (probe <= i) &&
                               (result == -ENOENT) == (probe >  i));
                }
                if ((i % (U/10)) == 0 && i > 0) {
                        struct node *r = get(mod, t->root);
                        printf("\n        %10li: %5i / %4.2f%%", i, level(r) + 1,
                               100.0 * exist / (U/10));
                        put(r);
                        exist = 0;
                }
                writeout(t->ttype->mod, 1000, 10);
                clean(t->ttype->mod, 1000, 1000);
        }
        for (long j = 0; j < U; ++j) {
                *(long *)key = j;
                keyb.seg[0] = (struct t2_seg){ .len = ksize,    .addr = &key };
                valb.seg[0] = (struct t2_seg){ .len = SOF(val), .addr = &val };
                NOFAIL(t2_lookup(t, &r));
        }
        utest("rand");
        U *= 1;
        for (int i = 0; i < U; ++i) {
                ksize = rand() % maxsize;
                vsize = rand() % maxsize;
                ASSERT(ksize < SOF(key));
                ASSERT(vsize < SOF(val));
                ASSERT(4 * (ksize + vsize) < ((int32_t)1 << ntype.shift));
                fill(key, ksize);
                fill(val, vsize);
                keyb.seg[0] = (struct t2_seg){ .len = ksize, .addr = &key };
                valb.seg[0] = (struct t2_seg){ .len = vsize, .addr = &val };
                result = t2_insert(t, &r);
                ASSERT(result == 0 || result == -EEXIST);
                if (result == -EEXIST) {
                        exist++;
                }
                if ((i % (U/10)) == 0 && i > 0) {
                        struct node *r = get(mod, t->root);
                        printf("\n        %10i: %5i / %4.2f%%", i, level(r) + 1,
                               100.0 * exist / (U/10));
                        put(r);
                        exist = 0;
                }
                writeout(t->ttype->mod, 1000, 10);
                clean(t->ttype->mod, 1000, 1000);
        }
        utest("fini");
        t2_node_type_degister(&ntype);
        t2_fini(mod);
        utestdone();
}

static void delete_ut() {
        struct t2      *mod;
        struct t2_tree *t;
        char key[1ul << ntype.shift];
        char val[1ul << ntype.shift];
        struct t2_buf keyb = BUF_VAL(key);
        struct t2_buf valb = BUF_VAL(val);
        struct t2_rec r = {
                .key = &keyb,
                .val = &valb
        };
        int32_t maxsize = ((int32_t)1 << (ntype.shift - 3)) - 10;
        int exist = 0;
        int noent = 0;
        int32_t ksize;
        int32_t vsize;
        int     result;
        usuite("delete");
        utest("init");
        mod = t2_init(ut_storage, 20);
        ASSERT(EISOK(mod));
        ttype.mod = NULL;
        t2_tree_type_register(mod, &ttype);
        t2_node_type_register(mod, &ntype);
        t = t2_tree_create(&ttype);
        ASSERT(EISOK(t));
        utest("1K*1K");
        long U = 1000;
        for (long i = 0; i < U; ++i) {
                ksize = sizeof i;
                vsize = rand() % maxsize;
                ASSERT(ksize < SOF(key));
                ASSERT(vsize < SOF(val));
                ASSERT(4 * (ksize + vsize) < ((int32_t)1 << ntype.shift));
                *(long *)key = i;
                fill(val, vsize);
                keyb.seg[0] = (struct t2_seg){ .len = ksize, .addr = &key };
                valb.seg[0] = (struct t2_seg){ .len = vsize, .addr = &val };
                NOFAIL(t2_insert(t, &r));
        }
        for (long i = U - 1; i >= 0; --i) {
                for (long j = 0; j < U; ++j) {
                        ksize = sizeof i;
                        *(long *)key = j;
                        keyb.seg[0] = (struct t2_seg){ .len = ksize,    .addr = &key };
                        valb.seg[0] = (struct t2_seg){ .len = SOF(val), .addr = &val };
                        result = t2_lookup(t, &r);
                        ASSERT((result == 0) == (j <= i) && (result == -ENOENT) == (j > i));
                }
                ksize = sizeof i;
                vsize = rand() % maxsize;
                ASSERT(ksize < SOF(key));
                ASSERT(vsize < SOF(val));
                ASSERT(4 * (ksize + vsize) < ((int32_t)1 << ntype.shift));
                *(long *)key = i;
                keyb.seg[0] = (struct t2_seg){ .len = ksize, .addr = &key };
                valb.seg[0] = (struct t2_seg){ .len = vsize, .addr = &val };
                NOFAIL(t2_delete(t, &r));
        }
        for (long i = 0; i < U; ++i) {
                ksize = sizeof i;
                vsize = rand() % maxsize;
                *(long *)key = i;
                keyb.seg[0] = (struct t2_seg){ .len = ksize,    .addr = &key };
                valb.seg[0] = (struct t2_seg){ .len = SOF(val), .addr = &val };
                result = t2_lookup(t, &r);
                ASSERT(result == -ENOENT);
        }
        utest("rand");
        U = 100000;
        int inserts = 0;
        int deletes = 0;
        for (int i = 0; i < U; ++i) {
                ksize = rand() % maxsize + (ht_hash(i) & 1); /* Beat prng cycles. */
                vsize = rand() % maxsize + (ht_hash(i) & 3);
                ASSERT(ksize < SOF(key));
                ASSERT(vsize < SOF(val));
                ASSERT(4 * (ksize + vsize) < ((int32_t)1 << ntype.shift));
                fill(key, ksize);
                keyb.seg[0] = (struct t2_seg){ .len = ksize, .addr = &key };
                if (rand() & 1) {
                        fill(val, vsize);
                        valb.seg[0] = (struct t2_seg){ .len = vsize, .addr = &val };
                        result = t2_insert(t, &r);
                        ASSERT(result == 0 || result == -EEXIST);
                        if (result == -EEXIST) {
                                exist++;
                        }
                        inserts++;
                } else {
                        result = t2_delete(t, &r);
                        ASSERT(result == 0 || result == -ENOENT);
                        if (result == -ENOENT) {
                                noent++;
                        }
                        deletes++;
                }
                if ((i % (U/10)) == 0 && i > 0) {
                        struct node *r = get(mod, t->root);
                        printf("\n        %10i: %5i / %4.2f%% / %4.2f%%", i, level(r) + 1,
                               100.0 * exist / inserts, 100.0 * noent / deletes);
                        put(r);
                        exist = 0;
                        noent = 0;
                        inserts = 0;
                        deletes = 0;
                }
        }
        utest("fini");
        t2_node_type_degister(&ntype);
        t2_fini(mod);
        utestdone();
}

static long cit;
static int cnext(struct t2_cursor *c, const struct t2_rec *rec) {
        ++cit;
        return +1;
}

static void next_ut() {
        struct t2      *mod;
        struct t2_tree *t;
        char key[1ul << ntype.shift];
        char val[1ul << ntype.shift];
        struct t2_buf keyb = BUF_VAL(key);
        struct t2_buf valb = BUF_VAL(val);
        struct t2_rec r = {
                .key = &keyb,
                .val = &valb
        };
        usuite("next");
        utest("init");
        mod = t2_init(ut_storage, 20);
        ASSERT(EISOK(mod));
        ttype.mod = NULL;
        t2_tree_type_register(mod, &ttype);
        t2_node_type_register(mod, &ntype);
        t = t2_tree_create(&ttype);
        ASSERT(EISOK(t));
        struct t2_cursor_op cop = {
                .next = &cnext
        };
        struct t2_cursor c = {
                .curkey = keyb,
                .tree   = t,
                .op     = &cop,
                .maxlen = SOF(key)
        };
        utest("populate");
        long U = 10000;
        for (long i = 0; i < U; ++i) {
                keyb = BUF_VAL(i);
                valb = BUF_VAL(i);
                NOFAIL(t2_insert(t, &r));
        }
        utest("smoke");
        for (long i = 0, del = 0; i < U; ++i, del += 7, del %= U) {
                unsigned long ulongmax = ~0ul;
                struct t2_buf maxkey = BUF_VAL(ulongmax);
                keyb = BUF_VAL(del);
                valb = BUF_VAL(del);
                NOFAIL(t2_delete(t, &r));
                c.dir = T2_MORE;
                t2_cursor_init(&c, &zero);
                cit = 0;
                while (t2_cursor_next(&c) > 0) {
                        ;
                }
                t2_cursor_fini(&c);
                ASSERT(cit == U - i);
                c.dir = T2_LESS;
                t2_cursor_init(&c, &maxkey);
                cit = 0;
                while (t2_cursor_next(&c) > 0) {
                        ;
                }
                t2_cursor_fini(&c);
                ASSERT(cit == U - i);
        }
        utest("fini");
        t2_node_type_degister(&ntype);
        t2_fini(mod);
        utestdone();
}

static void cookie_ut() {
        uint64_t v[10];
        struct t2_cookie k;
        int result;
        NOFAIL(signal_init());
        cookie_make(&v[0]);
        cookie_load(&v[0], &k);
        result = cookie_is_valid(&k);
        ASSERT(result);
        for (uint64_t b = 0; b <= 0xff; ++b) {
                void *addr = (void *)((b << 20) ^ (uint64_t)&v[0]);
                addr_is_valid(addr);
        }
        if (!ON_DARWIN) { /* Code segment is not writable. */
                result = addr_is_valid((void *)&cookie_ut);
                ASSERT(result);
                result = addr_is_valid((void *)&t2_init);
                ASSERT(result);
        }
        result = addr_is_valid((void *)&__t_counters); /* TLS */
        ASSERT(result);
        result = addr_is_valid((void *)&cit);
        ASSERT(result);
        signal_fini();
        LOG("Testing stacktrace");
        stacktrace(); /* Test it here. */
}

static void error_ut() {
        int e0 = ERROR(-ENOMEM);
        int e1 = ERROR_INFO(e0, "error: %i", 6, 0);
        int e2 = ERROR_INFO(-EINVAL, "bump!", 0, 0);
        int e3 = ERROR_INFO(e2, "at: %s (%p)", "fowl", &error_ut);
        char buf[256];
        (void)e1;
        eprint();
        for (int i = -1; i < 5; ++i) {
                int err = 0;
                int result = t2_error(i, buf, sizeof buf, &err);
                printf("%i: %i %i %s\n", i, result, err, buf);
        }
        t2_error_print();
        eclear();
        eprint();
        for (int i = 0; i < 100; ++i) {
                e3 = ERROR_INFO(e3, "More! %i", i, 0);
        }
        eprint();
}

static void inc(char *key, int len) {
        int i;
        ASSERT(FORALL(j, len, '0' <= key[j] && key[j] <= '9'));
        for (i = len - 1; i >= 0 && key[i] == '9'; --i) {
                ;
        }
        if (i >= 0) {
                key[i]++;
        }
        while (++i < len) {
                key[i] = '0';
        }
}

void seq_ut() {
        char key[] = "999999999";
        char val[] = "*VALUE*";
        struct t2_buf keyb;
        struct t2_buf valb;
        struct t2_rec r = {};
        struct t2      *mod;
        struct t2_tree *t;
        usuite("seq");
        utest("init");
        mod = t2_init(ut_storage, 20);
        ASSERT(EISOK(mod));
        ttype.mod = NULL;
        t2_tree_type_register(mod, &ttype);
        t2_node_type_register(mod, &ntype);
        t = t2_tree_create(&ttype);
        ASSERT(EISOK(t));
        utest("populate");
        long U = 1000000;
        for (long i = 0; i < U; ++i) {
                keyb = BUF_VAL(key);
                valb = BUF_VAL(val);
                r.key = &keyb;
                r.val = &valb;
                NOFAIL(t2_insert(t, &r));
                inc(key, (sizeof key) - 1);
        }
        utest("fini");
        t2_node_type_degister(&ntype);
        t2_fini(mod);
        utestdone();
}

void lib_ut() {
        usuite("lib");
        utest("minmax");
#define MINMAX(l, g) (min_32(l, g) == l && min_32(g, l) == l && max_32(l, g) == g && max_32(g, l) == g)
        ASSERT(MINMAX(0, 1));
        ASSERT(MINMAX(0, 1000));
        ASSERT(MINMAX(0, INT_MAX));
        ASSERT(MINMAX(-1, 0));
        ASSERT(MINMAX(-1000, 0));
        ASSERT(MINMAX(INT_MIN / 2, 0));
        ASSERT(MINMAX(1, 1));
        ASSERT(MINMAX(-1000, 1));
        ASSERT(MINMAX(INT_MIN / 2, 1000));
        ASSERT(MINMAX(INT_MIN / 2, INT_MAX / 2));
#undef MINMAX
        utestdone();
}

enum { THREADS = 17, OPS = 50000 };

#define MAXSIZE (((int32_t)1 << (ntype.shift - 3)) - 10)

static void random_buf(char *buf, int32_t max, int32_t *out) {
        *out = rand() % max;
        fill(buf, *out);
}

void *lookup_worker(void *arg) {
        struct t2_tree *t = arg;
        char kbuf[8];
        char vbuf[MAXSIZE];
        int32_t ksize;
        t2_thread_register();
        for (long i = 0; i < OPS; ++i) {
                random_buf(kbuf, sizeof kbuf, &ksize);
                int result = t2_lookup_ptr(t, kbuf, ksize, vbuf, sizeof vbuf);
                if (result != 0 && result != -ENOENT) {
                        printf("%i\n", result);
                        t2_error_print();
                }
                ASSERT(result == 0 || result == -ENOENT);
        }
        t2_thread_degister();
        return NULL;
}

void *insert_worker(void *arg) {
        struct t2_tree *t = arg;
        char kbuf[8];
        char vbuf[MAXSIZE];
        int32_t ksize;
        int32_t vsize;
        t2_thread_register();
        for (long i = 0; i < OPS; ++i) {
                random_buf(kbuf, sizeof kbuf, &ksize);
                random_buf(vbuf, sizeof vbuf, &vsize);
                int result = t2_insert_ptr(t, kbuf, ksize, vbuf, vsize);
                ASSERT(result == 0 || result == -EEXIST);
        }
        t2_thread_degister();
        return NULL;
}

void *delete_worker(void *arg) {
        struct t2_tree *t = arg;
        char kbuf[8];
        int32_t ksize;
        t2_thread_register();
        for (long i = 0; i < OPS; ++i) {
                random_buf(kbuf, sizeof kbuf, &ksize);
                int result = t2_delete_ptr(t, kbuf, ksize);
                ASSERT(result == 0 || result == -ENOENT);
        }
        t2_thread_degister();
        return NULL;
}

void *next_worker(void *arg) {
        struct t2_tree *t = arg;
        char key[8];
        struct t2_cursor_op cop = {
                .next = &cnext
        };
        struct t2_cursor c = {
                .curkey = BUF_VAL(key),
                .tree   = t,
                .op     = &cop
        };
        t2_thread_register();
        for (long i = 0; i < OPS; ++i) {
                char start[8];
                struct t2_buf startkey = BUF_VAL(start);
                random_buf(startkey.seg[0].addr, sizeof key, &startkey.seg[0].len);
                c.dir = (i % 2 == 0) ? T2_MORE : T2_LESS;
                t2_cursor_init(&c, &startkey);
                for (int i = 0; i < 10 && t2_cursor_next(&c) > 0; ++i) {
                        ;
                }
                t2_cursor_fini(&c);
        }
        t2_thread_degister();
        return NULL;
}

void mt_ut() {
        struct t2      *mod;
        struct t2_tree *t;
        pthread_t tid[4*THREADS];
        char kbuf[8];
        char vbuf[MAXSIZE];
        int32_t ksize;
        int32_t vsize;
        int     result;
        usuite("mt");
        utest("init");
        mod = t2_init(ut_storage, 20);
        ASSERT(EISOK(mod));
        ttype.mod = NULL;
        t2_tree_type_register(mod, &ttype);
        t2_node_type_register(mod, &ntype);
        t = t2_tree_create(&ttype);
        ASSERT(EISOK(t));
        utest("populate");
        for (long i = 0; i < OPS; ++i) {
                random_buf(kbuf, sizeof kbuf, &ksize);
                random_buf(vbuf, sizeof vbuf, &vsize);
                result = t2_insert_ptr(t, kbuf, ksize, vbuf, vsize);
                ASSERT(result == 0 || result == -EEXIST);
        }
        utest("lookup");
        for (int i = 0; i < THREADS; ++i) {
                NOFAIL(pthread_create(&tid[i], NULL, &lookup_worker, t));
        }
        for (int i = 0; i < THREADS; ++i) {
                pthread_join(tid[i], NULL);
        }
        utest("insert");
        for (int i = 0; i < THREADS; ++i) {
                NOFAIL(pthread_create(&tid[i], NULL, &insert_worker, t));
        }
        for (int i = 0; i < THREADS; ++i) {
                pthread_join(tid[i], NULL);
        }
        utest("insert+lookup");
        for (int i = 0; i < THREADS; ++i) {
                NOFAIL(pthread_create(&tid[i], NULL, &lookup_worker, t));
        }
        for (int i = THREADS; i < 2*THREADS; ++i) {
                NOFAIL(pthread_create(&tid[i], NULL, &insert_worker, t));
        }
        for (int i = 0; i < 2*THREADS; ++i) {
                pthread_join(tid[i], NULL);
        }
        utest("all");
        for (int i = 0; i < THREADS; ++i) {
                NOFAIL(pthread_create(&tid[i], NULL, &delete_worker, t));
        }
        for (int i = THREADS; i < 2*THREADS; ++i) {
                NOFAIL(pthread_create(&tid[i], NULL, &insert_worker, t));
        }
        for (int i = 2*THREADS; i < 3*THREADS; ++i) {
                NOFAIL(pthread_create(&tid[i], NULL, &next_worker, t));
        }
        for (int i = 3*THREADS; i < 4*THREADS; ++i) {
                NOFAIL(pthread_create(&tid[i], NULL, &lookup_worker, t));
        }
        for (int i = 0; i < 4*THREADS; ++i) {
                pthread_join(tid[i], NULL);
        }
        utest("fini");
        t2_node_type_degister(&ntype);
        t2_fini(mod);
        utestdone();
}

int main(int argc, char **argv) {
        setbuf(stdout, NULL);
        setbuf(stderr, NULL);
        lib_ut();
        simple_ut();
        ht_ut();
        traverse_ut();
        insert_ut();
        tree_ut();
        counters_clear();
        stress_ut();
        counters_print();
        delete_ut();
        next_ut();
        cookie_ut();
        error_ut();
        seq_ut();
        counters_print();
        counters_clear();
        mt_ut();
        counters_print();
        return 0;
}

#endif /* UT */

/*
 * To do:
 *
 * - integrate rcu: https://github.com/urcu/userspace-rcu/blob/master/include/urcu/rculist.h (rculfhash.c)
 *
 * - abstract node and tree type operations (no direct simple_* calls)
 *
 * - multi-segment buffers
 *
 * - prefix compression for keys
 *
 * - checksums (re-use user-supplied ones)
 *
 * - other node formats: fixed-sized keys and values. Key prefixes in the directory
 *
 * - large keys and values stored outside of nodes
 *
 * - "streams" (sequential, random)
 *
 * - decaying node temperature (see bits/avg.c)
 *
 * - cache replacement (arc, clock?)
 *
 * - transaction engine hooks
 *
 * - tools: dump, load, repair
 *
 * - in-place operations
 *
 * - single-move shift
 *
 * - invariants for key data-strctures
 *
 * - simple node: expand and shrink directory left or right, as cheaper
 *
 * - update value (and key?) in place
 *
 * - pre-allocated struct path (to reduce stack pressure)
 *
 * - node format that avoids memmove (always add at the end, compact as needed)
 *
 * - balancing policies (per-level?)
 *
 * - check validity of user input (4 records in a node, etc.)
 *
 * - handle IO failures
 *
 * - avoid dynamic allocations in *_balance(), pre-allocate in *_prepare()
 *
 * - consider recording the largest key in the sub-tree rooted at an internal node. This allows separating keys at internal levels
 *
 * - simple node: store key offsets separately from value offsets
 *
 * - replace cookie with get(), benchmark (sigprocmask is expensive).
 *
 * Done:
 *
 * + path locking and re-checking (allocate new nodes outside of the lock)
 *
 * + error reporting: per-thread error propagation stack, (mostly) static error descriptors
 *
 * + metrics
 *
 * + iterator, cursor
 *
 * + variably-sized taddr_t encoding in internal nodes
 *
 * + binary search is inefficient (infinity keys)
 *
 * + cookies to avoid tree traversal
 *
 * + simple node functions should be robust in the face of concurrent modifications
 *
 * References:
 *
 * - D. Knuth, The Art of Computer Programming, Volume 3: Sorting and
 *   Searching; 6.2.4. Multiway Trees.
 *
 * - D. Lomet, The evolution of effective B-tree: page organization and
 *   techniques: a personal account (https://dl.acm.org/doi/pdf/10.1145/603867.603878)
 *
 * - R. Bayer, K. Unterauer, Prefix B-Trees (https://dl.acm.org/doi/abs/10.1145/320521.320530)
 */

/*
 *  Local variables:
 *  c-indentation-style: "K&R"
 *  c-basic-offset: 8
 *  tab-width: 8
 *  scroll-step: 1
 *  indent-tabs-mode: nil
 *  End:
 */
