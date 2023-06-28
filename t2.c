/* -*- C -*- */

/*
 * To do:
 *
 * - integrate rcu: https://github.com/urcu/userspace-rcu/blob/master/include/urcu/rculist.h
 *
 * - simple node functions should be robust in the face of concurrent modifications
 *
 * - path locking and re-checking (allocate new nodes outside of the lock)
 *
 * - abstract node and tree type operations (no direct simple_* calls)
 *
 * - error reporting: per-thread error propagation stack, (mostly) static error descriptors
 *
 * - binary search is inefficient (infinity keys)
 *
 * - multi-segment buffers
 *
 * - prefix compression for keys
 *
 * - variably-sized taddr_t encoding in internal nodes
 *
 * - checksums (re-use user-supplied ones)
 *
 * - other node formats: fixed-sized keys and values. Key prefixes in the directory
 *
 * - large keys and values stored outside of nodes
 *
 * - "streams" (sequential, random)
 *
 * - cookies to avoid tree traversal
 *
 * - decaying node temperature (see bits/avg.c)
 *
 * - cache replacement (arc, clock?)
 *
 * - transaction engine hooks
 *
 * - metrics
 *
 * - tools: dump, load, repair
 *
 * - iterator, cursor
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
 * - check validity of user input (2 records in a node, etc.)
 *
 * - handle IO failures
 *
 * - avoid dynamic allocations in *_balance(), pre-allocate in *_prepare().
 *
 * - consider recording the largest key in the sub-tree rooted at an internal node. This allows separating keys at internal levels.
 *
 * References:
 *
 * - D. Knuth, The Art of Computer Programming, Volume 3: Sorting and
 *   Searching; 6.2.4. Multiway Trees.
 *
 * - D. Lomet, The evolution of effective B-tree: page organization and
 *   techniques: a personal account (https://dl.acm.org/doi/pdf/10.1145/603867.603878)
 *
 * - R. Bayer, K. Unterauer, Prefix B-Trees
 */

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
#define _LGPL_SOURCE
#define URCU_INLINE_SMALL_FUNCTIONS
#include <urcu/urcu-memb.h>
#include "t2.h"

enum {
        MAX_TREE_HEIGHT =   10,
        MAX_TREE_TYPE   = 1024,
        MAX_NODE_TYPE   = 1024,
        MAX_ERR_CODE    = 1024
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
#define ASSERT(expr) (LIKELY(expr) ? (void)0 : IMMANENTISE("Assertion failed: %s", #expr));
#define EXPENSIVE_ASSERT(expr) ((void)0) /* ASSERT(expr) */
#define ARRAY_SIZE(a) (sizeof(a) / sizeof(a[0]))
#define IS_ARRAY(x) (!__builtin_types_compatible_p(typeof(&(x)[0]), typeof(x)))
#define IS_IN(idx, array)                               \
({                                                      \
        ASSERT(IS_ARRAY(array));                        \
        ((unsigned long)(idx)) < ARRAY_SIZE(array);     \
})
#define COF(ptr, type, member) ((type *)((char *)(ptr) - (char *)(&((type *)0)->member)))
#define LOG(fmt, ...) llog(MSG_PREP(fmt), __VA_ARGS__)
#define ERROR(errcode)                          \
({                                              \
        typeof(errcode) __errc = (errcode);     \
        __errc;                                 \
})
#define EPTR(errcode) ((void *)(uint64_t)(errcode))
#define ERRCODE(val) ((uint64_t)(val))
#define EISERR(val) UNLIKELY((uint64_t)(val) >= (uint64_t)-MAX_ERR_CODE)
#define EISOK(val) (!EISERR(val))

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

#define BUF_VAL(v) (struct t2_buf){ .nr = 1, .seg = { [0] = { .len = sizeof(v), .addr = &(v) } } }

#define CINC(cnt) (++__t_counters.cnt)
#define CDEC(cnt) (--__t_counters.cnt)
#define CVAL(cnt) (__t_counters.cnt)

/* @types */

struct node;

struct link {
        struct link *next;
        struct link *prev;
};

struct ht {
        int          shift;
        struct link *chains;
};

struct t2 {
        const struct t2_tree_type *ttypes[MAX_TREE_TYPE];
        const struct node_type    *ntypes[MAX_NODE_TYPE];
        struct t2_storage         *stor;
        struct ht                  ht;
};

SASSERT(MAX_TREE_HEIGHT <= 255); /* Level is 8 bit. */

struct t2_tree {
        struct t2_tree_type *ttype;
        taddr_t              root;
        uint64_t             id;
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
        NEXT
};

enum node_flags {
        HEARD_BANSHEE = 1ull << 0
};

struct node {
        struct link             hash;
        taddr_t                 addr;
        uint64_t                seq;
        atomic_int              ref;
        const struct node_type *ntype;
        uint64_t                flags;
        void                   *data;
        struct t2              *mod;
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
        int         id;
        const char *name;
        struct t2  *mod;
        int         shift;
};

enum {
        NODE_MAGIX = 0x1f2e3d4c
};

struct header {
        uint32_t magix;
        uint32_t csum;
        uint16_t ntype;
        int8_t   level;
        uint8_t  pad;
        uint64_t treeid;
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

struct counters {
        int32_t node;
        int32_t rlock;
        int32_t wlock;
        int32_t rcu;
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
static struct node *ht_lookup(struct ht *ht, taddr_t addr);
static void ht_insert(struct ht *ht, struct node *n);
static void ht_delete(struct node *n);
static void link_init(struct link *l);
static void link_fini(struct link *l);
static int val_copy(struct t2_rec *r, struct node *n, struct slot *s);
static taddr_t internal_search(struct node *n, struct t2_rec *r, int32_t *pos);
static taddr_t internal_get(const struct node *n, int32_t pos);
static struct node *internal_child(const struct node *n, int32_t pos, bool peek);
static int leaf_search(struct node *n, struct t2_rec *r, struct slot *s);
static void immanentise(const struct msg_ctx *ctx, ...) __attribute__((noreturn));
static void *mem_alloc(size_t size);
static void  mem_free(void *ptr);
static void llog(const struct msg_ctx *ctx, ...);
static void put(struct node *n);
static void ref(struct node *n);
static struct node *alloc(struct t2_tree *t, int level);
static struct node *neighbour(struct path *p, int idx, enum dir d, enum lock_mode mode);
static bool can_insert(const struct node *n, const struct t2_rec *r);
static int dealloc(struct t2_tree *t, struct node *n);
static uint8_t level(const struct node *n);
static bool is_leaf(const struct node *n);
static int32_t nr(const struct node *n);
static int32_t nsize(const struct node *n);
static void lock(struct node *n, enum lock_mode mode);
static void unlock(struct node *n, enum lock_mode mode);
static struct header *nheader(const struct node *n);
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
static int shift(struct node *d, struct node *s, const struct slot *insert, enum dir dir);
static int merge(struct node *d, struct node *s, enum dir dir);
static struct t2_buf *ptr_buf(struct node *n, struct t2_buf *b);
static struct t2_buf *addr_buf(taddr_t *addr, struct t2_buf *b);
static void counters_check(void);
static bool is_sorted(struct node *n);
static int signal_init(void);
static void signal_fini(void);
static void stacktrace(void);
static int lookup(struct t2_tree *t, struct t2_rec *r);
static int insert(struct t2_tree *t, struct t2_rec *r);
static int delete(struct t2_tree *t, struct t2_rec *r);

static __thread struct counters __t_counters = {};

struct t2 *t2_init(struct t2_storage *storage, int hshift) {
        int result;
        struct t2 *mod = mem_alloc(sizeof *mod);
        t2_thread_register();
        if (mod != NULL) {
                result = signal_init();
                if (result == 0) {
                        mod->stor = storage;
                        result = storage->op->init(storage);
                        if (result == 0) {
                                result = ht_init(&mod->ht, hshift);
                                if (result != 0) {
                                        storage->op->fini(storage);
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
}


void t2_tree_type_degister(struct t2_tree_type *ttype)
{
        ASSERT(IS_IN(ttype->id, ttype->mod->ttypes));
        ASSERT(ttype->mod->ttypes[ttype->id] == ttype);
        ttype->mod->ttypes[ttype->id] = NULL;
        ttype->mod = NULL;
}

void t2_node_type_register(struct t2 *mod, struct node_type *ntype) {
        ASSERT(IS_IN(ntype->id, mod->ntypes));
        ASSERT(mod->ntypes[ntype->id] == NULL);
        ASSERT(ntype->mod == NULL);
        mod->ntypes[ntype->id] = ntype;
        ntype->mod = mod;
}


void t2_node_type_degister(struct node_type *ntype)
{
        ASSERT(IS_IN(ntype->id, ntype->mod->ntypes));
        ASSERT(ntype->mod->ntypes[ntype->id] == ntype);
        ntype->mod->ttypes[ntype->id] = NULL;
        ntype->mod = NULL;
}

static __thread bool thread_registered = false;

void t2_thread_register(void) {
        ASSERT(!thread_registered);
        urcu_memb_register_thread();
        thread_registered = true;
}

void t2_thread_degister(void) {
        ASSERT(thread_registered);
        urcu_memb_unregister_thread();
        thread_registered = false;
}

#define SCALL(mod, method, ...)                         \
({                                                      \
        struct t2_storage *__stor = (mod)->stor;        \
        __stor->op->method(__stor, __VA_ARGS__);        \
})

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

static struct t2_buf zero = {};

static int zerokey_insert(struct t2_tree *t) {
	return insert(t, &(struct t2_rec) { .key = &zero, .val = &zero });
}

struct t2_tree *t2_tree_create(struct t2_tree_type *ttype) {
        ASSERT(thread_registered);
        struct t2_tree *t = mem_alloc(sizeof *t);
        if (t != NULL) {
                t->ttype = ttype;
                struct node *root = alloc(t, 0);
                if (EISOK(root)) {
                        int result;
                        t->root = root->addr;
                        put(root); /* Release earlier to keep counters happy. */
                        result = zerokey_insert(t);
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

static int cookie_try(struct t2_tree *t, struct t2_rec *r, enum optype opt) {
        return -ESTALE;
}

static uint64_t node_seq(const struct node *n) {
        /* Barrier? */
        return n->seq;
}

/* @node */

static bool is_stable(const struct node *n) {
        return (n->seq & 1) == 0;
}

static void lock(struct node *n, enum lock_mode mode) {
        int result;
        ASSERT(mode == NONE || mode == READ || mode == WRITE);
        ASSERT(CVAL(rcu) == 0);
        if (mode == WRITE) {
                result = pthread_rwlock_wrlock(&n->lock);
                ASSERT(result == 0);
                ASSERT(is_stable(n));
                n->seq++;
                CINC(wlock);
        } else if (mode == READ) {
                result = pthread_rwlock_rdlock(&n->lock);
                CINC(rlock);
        }
}

static void unlock(struct node *n, enum lock_mode mode) {
        int result;
        ASSERT(mode == NONE || mode == READ || mode == WRITE);
        if (mode == WRITE) {
                n->seq++;
                ASSERT(is_stable(n));
                result = pthread_rwlock_unlock(&n->lock);
                ASSERT(result == 0);
                CDEC(wlock);
        } else if (mode == READ) {
                result = pthread_rwlock_unlock(&n->lock);
                ASSERT(result == 0);
                CDEC(rlock);
        }
}

static struct node *peek(struct t2 *mod, taddr_t addr) {
        return ht_lookup(&mod->ht, addr);
}

static struct node *ninit(struct t2 *mod, taddr_t addr) {
        struct node *n    = mem_alloc(sizeof *n); /* Allocate them together? */
        void        *data = mem_alloc(taddr_ssize(addr));
        int          result;
        if (LIKELY(n != NULL && data != NULL)) {
                int result = pthread_rwlock_init(&n->lock, NULL);
                if (LIKELY(result == 0)) {
                        link_init(&n->hash);
                        n->addr = addr;
                        n->mod = mod;
                        n->data = data;
                        ht_insert(&mod->ht, n);
                        n->ref = 1;
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
        pthread_rwlock_destroy(&n->lock);
        ht_delete(n);
        mem_free(n->data);
        SET0(n);
        mem_free(n);
}

static void ref(struct node *n) {
        ASSERT(CVAL(rcu) > 0 || n->ref > 0);
        n->ref++;
        CINC(node);
}

static struct node *get(struct t2 *mod, taddr_t addr) {
        struct node *n = ht_lookup(&mod->ht, addr);
        ASSERT(CVAL(rcu) == 0);
        if (n == NULL) {
                n = ninit(mod, addr);
                if (EISOK(n)) {
                        int result = SCALL(n->mod, read, n->addr, n->data);
                        if (result == 0) {
                                struct header *h = n->data;
                                if (IS_IN(h->ntype, n->mod->ntypes) && n->mod->ntypes[h->ntype] != NULL) {
                                        n->ntype = n->mod->ntypes[h->ntype];
                                } else {
                                        put(n);
                                        result = ERROR(-EIO);
                                }
                        } else {
                                put(n);
                                n = EPTR(result);
                        }
                }
        } else {
                n->ref++;
                CINC(node);
        }
        return n;
}

static struct node *alloc(struct t2_tree *t, int level) {
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
                        simple_make(n);
                }
        } else {
                n = EPTR(addr);
        }
        return n;
}

static int dealloc(struct t2_tree *t, struct node *n) {
        SCALL(t->ttype->mod, free, n->addr);
        n->data = NULL;
        put(n);
        return 0;
}

static void put(struct node *n) {
        ASSERT(n->ref > 0);
        EXPENSIVE_ASSERT(n->data != NULL ? is_sorted(n) : true);
        CDEC(node);
        if (--n->ref == 0) {
                /* TODO: lru. */
        }
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
        return 1ul << n->ntype->shift;
}

static void rcu_lock(void) {
        urcu_memb_read_lock();
        ASSERT(CVAL(rcu) == 0);
        CINC(rcu);
}

static void rcu_unlock(void) {
        CDEC(rcu);
        urcu_memb_read_unlock();
}

static void rcu_quiescent(void) {
        urcu_memb_quiescent_state();
}


/* @policy */

static int32_t prefix_separator(const struct t2_buf *l, struct t2_buf *r) {
        ASSERT(buf_cmp(l, r) < 0);
        ASSERT(r->nr == 1);
        do {
                r->seg[0].len--;
        } while (buf_cmp(l, r) < 0);
        return ++r->seg[0].len;
}

static void rec_todo(struct path *p, int idx, struct slot *out) {
        if (idx + 1 == p->used) {
                *out->rec.key = *p->rec->key;
                *out->rec.val = *p->rec->key;
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
                s.idx = i;
                simple_get(&s);
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
        struct rung *r = &p->rung[idx];
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
        if (result == 0) {
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
                result = simple_insert(&s);
                EXPENSIVE_ASSERT(result != 0 || is_sorted(s.node));
                if (result == 0 && (r->flags & ALUSED)) {
                        struct t2_buf lkey;
                        struct t2_buf rkey;
                        if (is_leaf(right)) {
                                s.node = left;
                                s.idx = nr(left) - 1;
                                simple_get(&s);
                                lkey = *s.rec.key;
                        }
                        s.node = right;
                        s.idx = 0;
                        simple_get(&s);
                        rkey = *s.rec.key;
                        if (is_leaf(right)) {
                                prefix_separator(&lkey, &rkey);
                        }
                        result = buf_alloc(&r->scratch, &rkey);
                        ASSERT(result == 0);
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
        simple_delete(s);
        if (p->rung[idx + 1].flags & SEPCHG) {
                int           result;
                struct node  *child = brother(&p->rung[idx + 1], RIGHT)->node;
                struct t2_buf cptr;
                SLOT_DEFINE(sub, child);
                ASSERT(child != NULL && !is_leaf(child));
                sub.idx = 0;
                simple_get(&sub);
                *s->rec.key = *sub.rec.key;
                *s->rec.val = *ptr_buf(child, &cptr);
                result = simple_insert(s);
                ASSERT(result == 0);
        }
}

static int split_right_exec_delete(struct path *p, int idx) {
        int result = 0;
        struct rung *r = &p->rung[idx];
        struct node *right = brother(r, RIGHT)->node;
        SLOT_DEFINE(s, r->node);
        if (!is_leaf(r->node)) {
                if (r->pos + 1 < nr(r->node)) {
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
                result = merge(r->node, right, LEFT);
                ASSERT(result == 0);
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
        ASSERT(IS0(p));
        SASSERT(NONE == 0);
        p->tree = t;
        p->rec  = r;
        p->opt  = opt;
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
                if (right->node != NULL) {
                        unlock(right->node, right->lm);
                        put(right->node);
                }
                unlock(r->node, r->lm);
                if (left->node != NULL) {
                        unlock(left->node, left->lm);
                        put(left->node);
                }
                if (r->flags & PINNED) {
                        put(r->node);
                }
                if (r->allocated != NULL) {
                        if (r->flags & ALUSED) {
                                put(r->allocated);
                        } else {
                                dealloc(p->tree, r->allocated);
                        }
                }
                buf_free(&r->scratch);
                SET0(r);
        }
        p->used = 0;
        if (p->newroot != NULL) {
                dealloc(p->tree, p->newroot);
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

static bool rung_is_valid(const struct path *p, int i) {
        const struct rung *r    = &p->rung[i];
        const struct rung *prev = &p->rung[i - 1];
        const struct node *n    = r->node;
        return  n != NULL &&
                n->data != NULL &&
                node_seq(n) == r->seq + (r->lm == WRITE) && /* Account for our own lock. */
                is_stable(n) == (r->lm != WRITE) &&
                !is_leaf(n) ? r->pos < nr(n) : true &&
                (i == 0 ? p->tree->root == n->addr :
                          n->addr == internal_get(prev->node, prev->pos) &&
                          level(prev->node) == level(n) + 1) &&
                (i == p->used - 1) == is_leaf(n);
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
        r->lm = mode;
        down = internal_child(r->node, r->pos + d, false);
        while (down != NULL && EISOK(down)) {
                r = &p->rung[++i];
                r->lm = mode;
                *brother(r, d) = (struct sibling) { .node = down, .lm = mode };
                ASSERT(level(r->node) == level(down));
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
        } while (--idx >= 0 && result == 0);
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
        } while (--idx >= 0 && result == 0);
        path_lock(p);
        return result;
}

SASSERT(T2_LESS == LEFT && T2_MORE == RIGHT);

static int next_prep(struct path *p) {
        struct node      *sibling;
        struct rung      *r      = &p->rung[p->used - 1];
        struct t2_cursor *c      = (void *)p->rec->vcb;
        int               result = 0;
        SLOT_DEFINE(s, r->node);
        if (!leaf_search(r->node, p->rec, &s) && c->dir == RIGHT) {
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
        *b = BUF_VAL(*addr);
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
        if (buf_len(&p->rung[0].keyout) == 0 && buf_len(&p->rung[0].valout) == 0) {
                return 0; /* Nothing to do. */
        }
        s.idx = 0;
        simple_get(&s);
        s.node = p->newroot;
        s.rec.val = ptr_buf(oldroot, &ptr);
        result = simple_insert(&s);
        if (result == 0) {
                s.idx = 1;
                ASSERT(p->rung[0].pd.id == SPLIT_RIGHT); /* For now. */
                s.rec.key = &p->rung[0].keyout;
                s.rec.val = &p->rung[0].valout;
                result = simple_insert(&s);
                if (result == 0) {
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
                result = dispatch[r->pd.id].exec_insert(p, idx);
                if (result <= 0) {
                        break;
                }
                result = 0;
        }
        if (UNLIKELY(idx < 0 && result == 0)) {
                if (p->newroot != NULL) {
                        result = root_add(p); /* Move this to policy? */
                }
        }
        return result;
}

static int insert_complete(struct path *p, struct node *n) {
        int result = simple_insert(&(struct slot) {
                        .node = n,
                        .idx  = p->rung[p->used - 1].pos + 1,
                        .rec  = *p->rec
                });
        if (result == -ENOSPC) {
                result = insert_balance(p);
        }
        return result;
}

static int delete_balance(struct path *p) {
        int idx;
        int result = 0;
        for (idx = p->used - 1; idx >= 0; --idx) {
                struct rung *r = &p->rung[idx];
                ASSERT(r->lm == WRITE);
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
        simple_delete(&(struct slot) {
                        .node = n,
                        .idx  = p->rung[p->used - 1].pos
                });
        if (!keep(n)) {
                result = delete_balance(p);
        }
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
                        s.idx = utmost(sibling, -c->dir); /* Cute. */
                        simple_get(&s);
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
        return result;
}

static void rcu_leave(struct path *p) {
        path_pin(p);
        rcu_unlock();
}

static bool rcu_try(struct path *p) {
        bool result = false;
        if (result) {
                path_fini(p);
        }
        return result;
}

static int traverse(struct path *p) {
        struct t2 *mod   = p->tree->ttype->mod;
        int        tries = 0;
        int        result;
        uint64_t   next;
        ASSERT(p->used == 0);
        ASSERT(p->opt == LOOKUP || p->opt == INSERT || p->opt == DELETE || p->opt == NEXT);
        rcu_lock();
        while (true) {
                struct node *n;
                struct rung *r;
                uint64_t     flags = 0;
                ASSERT(CVAL(rcu) == 1);
                if (UNLIKELY(tries++ > 10 && (tries & (tries - 1)) == 0)) {
                        LOG("Looping: %i", tries);
                }
                if (p->used == 0) {
                        next = p->tree->root;
                }
                n = peek(mod, next);
                if (EISERR(n)) {
                        result = ERROR(ERRCODE(n));
                        rcu_unlock();
                        break;
                } else if (n == NULL) {
                        rcu_leave(p);
                        n = get(mod, next);
                        if (rcu_try(p)) {
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
                                flags |= PINNED;
                        }
                } else if (!is_stable(n)) {
                        rcu_leave(p);
                        lock(n, WRITE); /* Wait for stabilisation. */
                        unlock(n, WRITE);
                        if (rcu_try(p)) {
                                continue;
                        }
                }
                r = path_add(p, n, node_seq(n), flags);
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
                                result = insert_prep(p);
                                if (result != 0) {
                                        break;
                                } else if (!path_is_valid(p)) {
                                        path_fini(p);
                                        rcu_lock();
                                } else {
                                        result = insert_complete(p, n);
                                        break;
                                }
                        } else if (p->opt == DELETE) {
                                rcu_leave(p);
                                result = delete_prep(p);
                                if (result != 0) {
                                        break;
                                } else if (!path_is_valid(p)) {
                                        path_fini(p);
                                        rcu_lock();
                                } else {
                                        result = delete_complete(p, n);
                                        break;
                                }
                        } else {
                                rcu_leave(p);
                                result = next_prep(p);
                                if (result != 0) {
                                        break;
                                } else if (!path_is_valid(p)) {
                                        path_fini(p);
                                        rcu_lock();
                                } else {
                                        result = next_complete(p, n);
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
        struct path p = {};
        path_init(&p, t, r, opt);
        result = traverse(&p);
        path_fini(&p);
        return result;
}

static int lookup(struct t2_tree *t, struct t2_rec *r) {
        int result;
        counters_check();
        result = cookie_try(t, r, LOOKUP);
        if (result == -ESTALE) {
                result = traverse_result(t, r, LOOKUP);
        }
        counters_check();
        return result;
}

static int insert(struct t2_tree *t, struct t2_rec *r) {
        int result;
        counters_check();
        result = cookie_try(t, r, INSERT);
        if (result == -ESTALE) {
                result = traverse_result(t, r, INSERT);
        }
        counters_check();
        return result;
}

static int delete(struct t2_tree *t, struct t2_rec *r) {
        int result;
        counters_check();
        result = cookie_try(t, r, DELETE);
        if (result == -ESTALE) {
                result = traverse_result(t, r, DELETE);
        }
        counters_check();
        return result;
}

static int next(struct t2_cursor *c) {
        int result;
        struct t2_buf val = {};
        struct t2_rec r = {
                .key = &c->curkey,
                .val = &val,
                .vcb = (void *)c /* Erm... */
        };
        counters_check();
        result = cookie_try(c->tree, &r, NEXT);
        if (result == -ESTALE) {
                result = traverse_result(c->tree, &r, NEXT);
        }
        counters_check();
        return result;
}

int t2_lookup(struct t2_tree *t, struct t2_rec *r) {
        ASSERT(thread_registered);
        return lookup(t, r);
}

int t2_delete(struct t2_tree *t, struct t2_rec *r) {
        ASSERT(thread_registered);
        return delete(t, r);
}

int t2_insert(struct t2_tree *t, struct t2_rec *r) {
        ASSERT(thread_registered);
        return insert(t, r);
}

int t2_cursor_init(struct t2_cursor *c, struct t2_buf *key) {
        ASSERT(thread_registered);
        ASSERT(buf_len(key) <= buf_len(&c->curkey));
        ASSERT(c->curkey.nr == 1);
        ASSERT(c->dir == T2_LESS || c->dir == T2_MORE);
        buf_copy(&c->curkey, key);
        c->maxlen = buf_len(&c->curkey);
        c->curkey.seg[0].len = buf_len(key);
        return 0;
}

void t2_cursor_fini(struct t2_cursor *c) {
        ASSERT(thread_registered);
        c->curkey.seg[0].len = c->maxlen;
}

int t2_cursor_next(struct t2_cursor *c) {
        ASSERT(thread_registered);
        return next(c);
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

static void counters_check(void) {
        if (__t_counters.node != 0) {
                LOG("Leaked node: %i", __t_counters.node);
        }
        if (__t_counters.rlock != 0) {
                LOG("Leaked rlock: %i", __t_counters.rlock);
        }
        if (__t_counters.wlock != 0) {
                LOG("Leaked wlock: %i", __t_counters.wlock);
        }
        if (__t_counters.rcu != 0) {
                LOG("Leaked rcu: %i", __t_counters.rcu);
        }
}

static __thread int insigsegv = 0;
static struct sigaction osa = {};
static int signal_set = 0;

#include <execinfo.h>

static void stacktrace(void) {
    int    size;
    char **syms;
    void  *tracebuf[512];

    size = backtrace(tracebuf, ARRAY_SIZE(tracebuf));
    syms = backtrace_symbols(tracebuf, size);
    for (int i = 0; i < size; i++) {
            if (syms != NULL) {
                    printf("%s\n", syms[i]);
            } else {
                    printf("%p\n", tracebuf[i]);
            }
    }
    free(syms);
}

static void sigsegv(int signo, siginfo_t *si, void *uctx) {
        if (insigsegv++ > 0) {
                abort(); /* Don't try to print anything. */
        }
        printf("\nGot: %i errno: %i code: %i pid: %i uid: %i ucontext: %p\n",
               signo, si->si_errno, si->si_code, si->si_pid, si->si_uid, uctx);
        stacktrace();
        if (osa.sa_handler != SIG_DFL && osa.sa_handler != SIG_IGN) {
                if (osa.sa_flags & SA_SIGINFO) {
                        (*osa.sa_sigaction)(signo, si, uctx);
                }
        }
        --insigsegv;
}

static int signal_init(void) {
        struct sigaction sa = {
                .sa_sigaction = &sigsegv,
                .sa_flags     = SA_SIGINFO | SA_NODEFER | SA_RESETHAND,
        };
        int result = 0;
        if (signal_set == 0) {
                result = sigaction(SIGSEGV, &sa, &osa);
                if (result == 0) {
                        signal_set = 1;
                }
        }
        return result;
}

static void signal_fini(void) {
        ASSERT(signal_set > 0);
        if (--signal_set == 0) {
                sigaction(SIGSEGV, &osa, NULL);
        }
}
/* @ht */

static void link_init(struct link *l) {
        l->next = l->prev = l;
}

static void link_fini(struct link *l) {
        ASSERT(l->next == l && l->prev == l);
}

static int ht_init(struct ht *ht, int shift) {
        ht->shift = shift;
        ht->chains = mem_alloc(sizeof ht->chains[0] << shift);
        if (ht->chains != NULL) {
                for (int i = 0; i < (1 << shift); i++) {
                        link_init(&ht->chains[i]);
                }
                return 0;
        }
        return ERROR(-ENOMEM);
}

static void ht_fini(struct ht *ht) {
        for (int i = 0; i < (1 << ht->shift); i++) {
                link_fini(&ht->chains[i]);
        }
        mem_free(ht->chains);
}

static void ht_clean(struct ht *ht) {
        for (int i = 0; i < (1 << ht->shift); i++) {
                struct link *head = &ht->chains[i];
                for (struct link *scan = head->next, *next = scan->next; scan != head; scan = next, next = scan->next) {
                        nfini((struct node *)scan);
                }
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

static struct node *ht_lookup(struct ht *ht, taddr_t addr) {
        unsigned     hash = ht_hash(addr) & ((1 << ht->shift) - 1);
        struct link *scan;
        struct link *head = &ht->chains[hash];
        for (scan = head->next; scan != head; scan = scan->next) {
                if (((struct node *)scan)->addr == addr) {
                        return (void *)scan;
                }
        }
        return NULL;
}

static void ht_insert(struct ht *ht, struct node *n) {
        unsigned     hash = ht_hash(n->addr) & ((1 << ht->shift) - 1);
        struct link *head = &ht->chains[hash];
        head->next->prev = &n->hash;
        n->hash.next     = head->next;
        n->hash.prev     = head;
        head->next       = &n->hash;
}

static void ht_delete(struct node *n) {
        ASSERT(n->hash.prev != &n->hash);
        ASSERT(n->hash.next != &n->hash);
        n->hash.next->prev = n->hash.prev;
        n->hash.prev->next = n->hash.next;
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

static int32_t buf_remain(const struct t2_buf *buf, int idx, uint32_t off) {
        int32_t nob = 0;
        if (idx < buf->nr) {
                for (nob = buf->seg[idx].len - off; idx < buf->nr; idx++) {
                        nob += buf->seg[idx].len;
                }
        }
        return nob;
}

static int int32_cmp(int32_t a, int32_t b) {
        return a < b ? -1 : a != b; /* sic. */
}

static int buf_cmp(const struct t2_buf *b0, const struct t2_buf *b1) {
        ASSERT(b0->nr == 1);
        ASSERT(b1->nr == 1); /* From skeycmp(). */
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
        return (void *)sh + sh->dir_off;
}

static struct dir_element *sat(struct sheader *sh, int pos) {
        return sdir(sh) + pos;
}

static bool is_in(int32_t lo, int32_t v, int32_t hi) {
        return lo <= v && v <= hi;
}

static int32_t dirsize(int32_t n) {
        return n * sizeof(struct dir_element);
}

static bool scheck(struct sheader *sh, const struct node_type *nt) {
        int32_t size = 1ul << nt->shift;
        int32_t dend = sh->dir_off + dirsize(sh->nr + 1);
        return  is_in(sizeof *sh, sh->dir_off, size) &&
                is_in(sizeof *sh, dend, size) &&
                FORALL(i, sh->nr + 1,
                       is_in(sizeof *sh, sat(sh, i)->koff, sh->dir_off) &&
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

static void *skey(struct sheader *sh, int pos, int32_t *size) {
        ASSERT(0 <= pos && pos < sh->nr);
        struct dir_element *del = sat(sh, pos);
        *size = sat(sh, pos + 1)->koff - del->koff;
        return (void *)sh + del->koff;
}

static void *sval(struct sheader *sh, int pos, int32_t *size) {
        ASSERT(0 <= pos && pos < sh->nr);
        struct dir_element *del = sat(sh, pos + 1);
        *size = sat(sh, pos)->voff  - del->voff;
        return (void *)sh + del->voff;
}

static char cmpch(int cmp) {
        return cmp < 0 ? '<' : cmp == 0 ? '=' : '>';
}

static void print_range(void *orig, int32_t nsize, void *start, int32_t nob);

static int skeycmp(struct sheader *sh, int pos, void *key, int32_t klen) {
        int32_t ksize;
        void *kstart = skey(sh, pos, &ksize);
        if (pos == -1) {
                return -1;
        } else if (pos == sh->nr) {
                return +1;
        } else {
                return memcmp(kstart, key, ksize < klen ? ksize : klen) ?: int32_cmp(ksize, klen);
        }
}

static struct sheader *simple_header(const struct node *n) {
        return n->data;
}

static bool simple_search(struct node *n, struct t2_rec *rec, struct slot *out) {
        ASSERT(rec->key->nr <= 1);
        bool            found = false;
        struct sheader *sh    = simple_header(n);
        int             l     = -1;
        int             r     = sh->nr;
        struct t2_buf  *key   = out->rec.key;
        struct t2_buf  *val   = out->rec.val;
        int             cmp;
        EXPENSIVE_ASSERT(scheck(sh, n->ntype));
        while (l + 1 < r) {
                int m = (l + r) >> 1;
                cmp = skeycmp(sh, m, rec->key->seg[0].addr, rec->key->seg[0].len);
                if (cmp > 0) {
                        r = m;
                } else {
                        l = m;
                        if (cmp == 0) {
                                found = true;
                                break;
                        }
                }
        }
        out->idx = l;
        if (0 <= l && l < sh->nr) {
                key->nr = 1;
                key->seg[0].addr = skey(sh, l, &key->seg[0].len);
                val->nr = 1;
                val->seg[0].addr = sval(sh, l, &val->seg[0].len);
        }
        return found;
}

static taddr_t internal_addr(const struct slot *s) {
        taddr_t addr;
        ASSERT(s->rec.val->nr > 0 && s->rec.val->seg[0].len >= sizeof(taddr_t));
        addr = *(taddr_t *)s->rec.val->seg[0].addr;
        ASSERT(taddr_is_valid(addr));
        return addr;
}

static taddr_t internal_search(struct node *n, struct t2_rec *r, int32_t *pos) {
        SLOT_DEFINE(s, NULL); /* !sanitise */
        (void)simple_search(n, r, &s);
        if (s.idx < 0) {
                s.node = n;
                s.idx = 0;
                simple_get(&s);
        }
        ASSERT(0 <= s.idx && s.idx < nr(n));
        *pos = s.idx;
        return internal_addr(&s);
}

static taddr_t internal_get(const struct node *n, int32_t pos) { /* !sanitise */
        ASSERT(0 <= pos && pos < nr(n));
        ASSERT(!is_leaf(n));
        SLOT_DEFINE(s, (struct node *)n);
        s.idx = pos;
        simple_get(&s);
        return internal_addr(&s);
}

static struct node *internal_child(const struct node *n, int32_t pos, bool peekp) {
        return (peekp ? peek : get)(n->mod, internal_get(n, pos));
}

static int leaf_search(struct node *n, struct t2_rec *r, struct slot *s) {
        return simple_search(n, r, s);
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
}

static void sdirmove(struct sheader *sh, int32_t nsize,
                     int32_t knob, int32_t vnob, int32_t nr) {
        int32_t dir_off = (knob * (nsize - sizeof *sh)) / (knob + vnob) -
                dirsize(nr + 1) / 2 + sizeof *sh;
        dir_off = min_32(max_32(dir_off, knob + sizeof *sh),
                         nsize - vnob - dirsize(nr + 1));
        ASSERT(knob + sizeof *sh <= dir_off);
        ASSERT(dir_off + dirsize(nr + 1) + vnob <= nsize);
        move(sh, sh->dir_off, sdirend(sh), dir_off - sh->dir_off);
        sh->dir_off = dir_off;
}

static int simple_can_insert(const struct slot *s) {
        return simple_free(s->node) >= rec_len(&s->rec) + sizeof(struct dir_element);
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
        if (simple_free(s->node) < klen + vlen + sizeof(struct dir_element)) {
                return -ENOSPC;
        }
        if (sfreekey(s->node) < klen || sfreeval(s->node) < vlen + sizeof *end) {
                struct dir_element *beg = sat(sh, 0);
                sdirmove(sh, beg->voff, end->koff - beg->koff + klen,
                         beg->voff - end->voff + vlen, sh->nr + 1);
                end = sat(sh, sh->nr);
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
        ASSERT(0 <= s->idx && s->idx < sh->nr);
        s->rec.key->nr = 1;
        s->rec.val->nr = 1;
        s->rec.key->seg[0].addr = skey(sh, s->idx, &s->rec.key->seg[0].len);
        s->rec.val->seg[0].addr = sval(sh, s->idx, &s->rec.val->seg[0].len);
        EXPENSIVE_ASSERT(scheck(sh, s->node->ntype));
}

static void simple_make(struct node *n) {
        int32_t         size = nsize(n);
        struct sheader *sh   = simple_header(n);
        sh->dir_off = sizeof *sh + (size - sizeof *sh) / 2;
        *sat(sh, 0) = (struct dir_element){ .koff = sizeof *sh, .voff = size };
}

static int32_t simple_nr(const struct node *n) {
        return simple_header(n)->nr;
}

static void print_range(void *orig, int32_t nsize, void *start, int32_t nob) {
        static const char hexdigit[] = "0123456789abcdef";
        int32_t off = start - orig;
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
        printf("addr: %"PRIx64" tree: %"PRIx64" level: %u ntype: %u nr: %u size: %u dir_off: %u dir_end: %u (%p)\n",
               n->addr, sh->head.treeid, sh->head.level, sh->head.ntype,
               sh->nr, size, sh->dir_off, sdirend(sh), n);
        for (int32_t i = 0; i <= sh->nr; ++i) {
                struct dir_element *del = sat(sh, i);
                printf("        %4u %4u %4u: ", i, del->koff, del->voff);
                if (i < sh->nr) {
                        int32_t kvsize;
                        print_range(sh, size, skey(sh, i, &kvsize), kvsize);
                        printf(" ");
                        print_range(sh, size, sval(sh, i, &kvsize), kvsize);
                        if (!is_leaf(n)) {
                                printf("    (%p)", peek(n->mod, internal_get(n, i)));
                        }
                }
                printf("\n");
        }
}

static void buf_print(const struct t2_buf *b) {
        ASSERT(b->nr == 1);
        print_range(b->seg[0].addr, b->seg[0].len, b->seg[0].addr, b->seg[0].len);
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
        src.idx = dir == RIGHT ? nr(s) - 1 : 0;
        simple_get(&src);
        dst.idx = dir == LEFT ? nr(d) : 0;
        return simple_insert(&dst) ?: (simple_delete(&src), 0);
}

static int shift(struct node *d, struct node *s, const struct slot *point, enum dir dir) {
        int result = 0;
        ASSERT(dir == LEFT || dir == RIGHT);
        ASSERT(point->idx >= 0 && point->idx <= nr(s));
        ASSERT(simple_free(d) > simple_free(s));
        ASSERT(4 * rec_len(&point->rec) < min_32(nsize(d), nsize(s)));
        while (result == 0) {
                SLOT_DEFINE(slot, s);
                slot.idx = dir == RIGHT ? nr(s) - 1 : 0;
                simple_get(&slot);
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
        while (result == 0 && nr(s) > 0) {
                result = shift_one(d, s, dir);
        }
        return result;
}

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
        if (result == 0) {
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
        memcpy(dst, (void *)taddr_saddr(addr), taddr_ssize(addr));
        return 0;
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

static struct t2_storage mock_storage = {
        .op = &mock_storage_op
};

/* @ut */

static void usuite(const char *suite) {
        printf("        %s\n", suite);
}

static const char *test = NULL;

static void utestdone(void) {
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
        for (int32_t i = 0; simple_free(s->node) >
                     buf_len(key) + buf_len(val) + sizeof(struct dir_element); ++i) {
                ASSERT(simple_insert(s) == 0);
                ASSERT(sh->nr == i + 1);
                ((char *)key->seg[0].addr)[1]++;
                ((char *)val->seg[0].addr)[1]++;
                s->idx = (s->idx + 7) % sh->nr;
        }
}

static void buf_init_str(struct t2_buf *b, const char *s) {
        b->nr = 1;
        b->seg[0].len  = strlen(s) + 1;
        b->seg[0].addr = (void *)s;
}

static bool is_sorted(struct node *n) {
        struct sheader *sh = simple_header(n);
        struct t2_buf kk;
        struct t2_buf vv;
        struct slot ss = {
                .node = n,
                .rec = { .key = &kk, .val = &vv }
        };
        char keyarea[nsize(n)];
        int32_t keysize;
        memset(keyarea, 0, nsize(n));
        for (int32_t i = 0; i < sh->nr; ++i) {
                ss.idx = i;
                simple_get(&ss);
                ASSERT(ss.rec.key->seg[0].len <= sizeof keyarea);
                if (i > 0) {
                        int cmp = skeycmp(sh, i, keyarea, keysize);
                        if (cmp <= 0) {
                                printf("Misordered at %i: ", i);
                                print_range(keyarea, sizeof keyarea,
                                            keyarea, sizeof keyarea);
                                printf(" %c ", cmpch(cmp));
                                print_range(n->data, 1ul << nsize(n),
                                            ss.rec.key->seg[0].addr,
                                            ss.rec.key->seg[0].len);
                                printf("\n");
                                simple_print(n);
                                return false;
                        }
                }
                keysize = ss.rec.key->seg[0].len;
                memcpy(keyarea, ss.rec.key->seg[0].addr, keysize);
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

static void simple_ut(void) {
        char body[1ul << ntype.shift];
        struct node n = {
                .ntype = &ntype,
                .addr  = taddr_make(0x100000, ntype.shift),
                .data  = body,
        };
        char body1[1ul << ntype.shift];
        struct node n1 = {
                .ntype = &ntype,
                .addr  = taddr_make(0x200000, ntype.shift),
                .data  = body1,
        };
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
        memset(body, 0, sizeof body);
        buf_init_str(&key, key0);
        buf_init_str(&val, val0);
        usuite("simple-node");
        utest("make");
        simple_make(&n);
        ASSERT(sh->nr == 0);
        utest("insert");
        populate(&s, &key, &val);
        ASSERT(simple_insert(&s) == -ENOSPC);
        utest("get");
        for (int32_t i = 0; i < sh->nr; ++i) {
                s.idx = i;
                simple_get(&s);
                ASSERT(buf_len(s.rec.key) == strlen(key0) + 1);
                ASSERT(buf_len(s.rec.val) == strlen(val0) + 1);
        }
        utest("delete");
        for (int32_t i = sh->nr - 1; i >= 0; --i) {
                s.idx = (s.idx + 7) % sh->nr;
                simple_delete(&s);
                ASSERT(sh->nr == i);
        }
        utest("search");
        key0[1] = 'a';
        while (simple_free(&n) > buf_len(&key) + buf_len(&val) + sizeof(struct dir_element)) {
                ASSERT(!simple_search(&n, &s.rec, &s));
                s.idx++;
                buf_init_str(&key, key0);
                buf_init_str(&val, val0);
                ASSERT(simple_insert(&s) == 0);
                ASSERT(is_sorted(&n));
                key0[1] += 251; /* Co-prime with 256. */
                val0[1]++;
        }
        utestdone();
}

static struct node *node_alloc_ut(uint64_t blk) {
        struct node *n = mem_alloc(sizeof *n);
        n->addr = taddr_make(blk & TADDR_ADDR_MASK, 9);
        return n;
}

static void ht_ut() {
        const uint64_t N = 10000;
        struct ht ht;
        usuite("ht");
        utest("collision");
        for (uint64_t i = 0; i < N; ++i) {
                for (uint64_t j = 0; j < i; ++j) {
                        ASSERT(ht_hash(i) != ht_hash(j));
                        ASSERT(ht_hash(2 * N + i * i * i) != ht_hash(2 * N + j * j * j));
                }
        }
        ht_init(&ht, 10);
        utest("insert");
        for (uint64_t i = 0; i < N; ++i) {
                ht_insert(&ht, node_alloc_ut(ht_hash(i)));
        }
        utest("lookup");
        for (uint64_t i = 0; i < N; ++i) {
                taddr_t blk = taddr_make(ht_hash(i) & TADDR_ADDR_MASK, 9);
                struct node *n = ht_lookup(&ht, blk);
                ASSERT(n != NULL);
                ASSERT(n->addr == blk);
        }
        utest("delete");
        for (uint64_t i = 0; i < N; ++i) {
                taddr_t blk = taddr_make(ht_hash(i) & TADDR_ADDR_MASK, 9);
                struct node *n = ht_lookup(&ht, blk);
                ht_delete(n);
        }
        utest("fini");
        ht_fini(&ht);
        utestdone();
}

static void traverse_ut() {
        taddr_t addr = taddr_make(0x100000, ntype.shift);
        char body[1ul << ntype.shift];
        struct node n = {
                .ntype = &ntype,
                .addr  = addr,
                .data  = body,
        };
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
        usuite("traverse");
        utest("t2_init");
        struct t2 *mod = t2_init(&mock_storage, 10);
        t2_node_type_register(mod, &ntype);
        ttype.mod = mod;
        memset(body, 0, sizeof body);
        buf_init_str(&key, key0);
        buf_init_str(&val, val0);
        utest("prepare");
        simple_make(&n);
        ht_insert(&mod->ht, &n);
        for (int i = 0; i < 20; ++i, key0[0] += 2) {
                ASSERT(!simple_search(&n, &s.rec, &s));
                s.idx++;
                buf_init_str(&key, key0);
                buf_init_str(&val, val0);
                ASSERT(simple_insert(&s) == 0);
                ASSERT(is_sorted(&n));
        }
        utest("existing");
        key0[0] = '0';
        ASSERT(traverse(&p) == 0);
        key0[0] = '2';
        p.used = 0;
        ASSERT(traverse(&p) == 0);
        key0[0] = '8';
        p.used = 0;
        ASSERT(traverse(&p) == 0);
        utest("too-small");
        key0[0] = ' ';
        p.used = 0;
        ASSERT(traverse(&p) == -ENOENT);
        utest("non-existent");
        key0[0] = '1';
        p.used = 0;
        ASSERT(traverse(&p) == -ENOENT);
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
        struct t2 *mod = t2_init(&mock_storage, 10);
        struct t2_rec r = {
                .key = &key,
                .val = &val
        };
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
        ASSERT(t2_insert(&t, &r) == 0);
        utest("eexist");
        ASSERT(t2_insert(&t, &r) == -EEXIST);
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
        mod = t2_init(&mock_storage, 20);
        ttype.mod = NULL;
        t2_tree_type_register(mod, &ttype);
        t2_node_type_register(mod, &ntype);
        t = t2_tree_create(&ttype);
        ASSERT(EISOK(t));
        buf_init_str(&key, key0);
        buf_init_str(&val, val0);
        utest("insert-1");
        ASSERT(t2_insert(t, &r) == 0);
        utest("eexist");
        ASSERT(t2_insert(t, &r) == -EEXIST);
        utest("5K");
        for (k64 = 0; k64 < 5000; ++k64) {
                key = BUF_VAL(k64);
                val = BUF_VAL(v64);
                ASSERT(t2_insert(t, &r) == 0);
        }
        utest("20K");
        for (int i = 0; i < 20000; ++i) {
                k64 = ht_hash(i);
                v64 = ht_hash(i + 1);
                key = BUF_VAL(k64);
                val = BUF_VAL(v64);
                ASSERT(t2_insert(t, &r) == 0);
        }
        utest("50K");
        for (int i = 0; i < 50000; ++i) {
                k64 = ht_hash(i);
                v64 = ht_hash(i + 1);
                key = BUF_VAL(k64);
                val = BUF_VAL(v64);
                ASSERT(t2_insert(t, &r) == (i < 20000 ? -EEXIST : 0));
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
        int32_t maxsize = (1ul << (ntype.shift - 3)) - 10;
        int exist = 0;
        int32_t ksize;
        int32_t vsize;
        int     result;
        usuite("stress");
        utest("init");
        mod = t2_init(&mock_storage, 20);
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
                ASSERT(ksize < sizeof key);
                ASSERT(vsize < sizeof val);
                ASSERT(4 * (ksize + vsize) < (1ul << ntype.shift));
                *(long *)key = i;
                fill(val, vsize);
                keyb.seg[0] = (struct t2_seg){ .len = ksize, .addr = &key };
                valb.seg[0] = (struct t2_seg){ .len = vsize, .addr = &val };
                result = t2_insert(t, &r);
                ASSERT(result == 0);
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
        }
        for (long j = 0; j < U; ++j) {
                *(long *)key = j;
                keyb.seg[0] = (struct t2_seg){ .len = ksize,      .addr = &key };
                valb.seg[0] = (struct t2_seg){ .len = sizeof val, .addr = &val };
                ASSERT(t2_lookup(t, &r) == 0);
        }
        utest("rand");
        U *= 10;
        for (int i = 0; i < U; ++i) {
                ksize = rand() % maxsize;
                vsize = rand() % maxsize;
                ASSERT(ksize < sizeof key);
                ASSERT(vsize < sizeof val);
                ASSERT(4 * (ksize + vsize) < (1ul << ntype.shift));
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
        int32_t maxsize = (1ul << (ntype.shift - 3)) - 10;
        int exist = 0;
        int noent = 0;
        int32_t ksize;
        int32_t vsize;
        int     result;
        usuite("delete");
        utest("init");
        mod = t2_init(&mock_storage, 20);
        ASSERT(EISOK(mod));
        ttype.mod = NULL;
        t2_tree_type_register(mod, &ttype);
        t2_node_type_register(mod, &ntype);
        t = t2_tree_create(&ttype);
        ASSERT(EISOK(t));
        utest("5K*5K");
        long U = 5000;
        for (long i = 0; i < U; ++i) {
                ksize = sizeof i;
                vsize = rand() % maxsize;
                ASSERT(ksize < sizeof key);
                ASSERT(vsize < sizeof val);
                ASSERT(4 * (ksize + vsize) < (1ul << ntype.shift));
                *(long *)key = i;
                fill(val, vsize);
                keyb.seg[0] = (struct t2_seg){ .len = ksize, .addr = &key };
                valb.seg[0] = (struct t2_seg){ .len = vsize, .addr = &val };
                result = t2_insert(t, &r);
                ASSERT(result == 0);
        }
        for (long i = U - 1; i >= 0; --i) {
                for (long j = 0; j < U; ++j) {
                        ksize = sizeof i;
                        vsize = rand() % maxsize;
                        ASSERT(ksize < sizeof key);
                        ASSERT(vsize < sizeof val);
                        ASSERT(4 * (ksize + vsize) < (1ul << ntype.shift));
                        *(long *)key = j;
                        keyb.seg[0] = (struct t2_seg){ .len = ksize, .addr = &key };
                        valb.seg[0] = (struct t2_seg){ .len = sizeof val, .addr = &val };
                        result = t2_lookup(t, &r);
                        ASSERT((result == 0) == (j <= i) && (result == -ENOENT) == (j > i));
                }
                ksize = sizeof i;
                vsize = rand() % maxsize;
                ASSERT(ksize < sizeof key);
                ASSERT(vsize < sizeof val);
                ASSERT(4 * (ksize + vsize) < (1ul << ntype.shift));
                *(long *)key = i;
                keyb.seg[0] = (struct t2_seg){ .len = ksize, .addr = &key };
                valb.seg[0] = (struct t2_seg){ .len = vsize, .addr = &val };
                result = t2_delete(t, &r);
                ASSERT(result == 0);
        }
        for (long i = 0; i < U; ++i) {
                ksize = sizeof i;
                vsize = rand() % maxsize;
                ASSERT(ksize < sizeof key);
                ASSERT(vsize < sizeof val);
                ASSERT(4 * (ksize + vsize) < (1ul << ntype.shift));
                *(long *)key = i;
                keyb.seg[0] = (struct t2_seg){ .len = ksize, .addr = &key };
                valb.seg[0] = (struct t2_seg){ .len = sizeof val, .addr = &val };
                result = t2_lookup(t, &r);
                ASSERT(result == -ENOENT);
        }
        utest("rand");
        U = 100000000;
        int inserts = 0;
        int deletes = 0;
        for (int i = 0; i < U; ++i) {
                ksize = rand() % maxsize + (ht_hash(i) & 1); /* Beat prng cycles. */
                vsize = rand() % maxsize + (ht_hash(i) & 3);
                ASSERT(ksize < sizeof key);
                ASSERT(vsize < sizeof val);
                ASSERT(4 * (ksize + vsize) < (1ul << ntype.shift));
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
                if ((i % (U/100)) == 0 && i > 0) {
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

static void rand_ut() {
        int64_t i;
        usuite("prng");
        utest("cycle");
        rand();
        rand();
        long s = rand();
        for (i = 0; LIKELY(rand() != s); ++i) {
                ;
        }
        printf("Cycle: %"PRId64"\n", i);
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
        int     result;
        usuite("next");
        utest("init");
        mod = t2_init(&mock_storage, 20);
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
                .maxlen = sizeof key
        };
        utest("populate");
        long U = 10000;
        for (long i = 0; i < U; ++i) {
                keyb = BUF_VAL(i);
                valb = BUF_VAL(i);
                result = t2_insert(t, &r);
                ASSERT(result == 0);
        }
        utest("smoke");
        for (long i = 0, del = 0; i < U; ++i, del += 7, del %= U) {
                unsigned long ulongmax = ~0ul;
                struct t2_buf maxkey = BUF_VAL(ulongmax);
                keyb = BUF_VAL(del);
                valb = BUF_VAL(del);
                result = t2_delete(t, &r);
                ASSERT(result == 0);
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

int main(int argc, char **argv) {
        setbuf(stdout, NULL);
        setbuf(stderr, NULL);
        rand_ut();
        simple_ut();
        ht_ut();
        traverse_ut();
        insert_ut();
        tree_ut();
        stress_ut();
        delete_ut();
        next_ut();
        return 0;
}

/*
 *  Local variables:
 *  c-indentation-style: "K&R"
 *  c-basic-offset: 8
 *  tab-width: 8
 *  scroll-step: 1
 *  indent-tabs-mode: nil
 *  End:
 */
