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
#include <urcu/list.h>
#include "t2.h"
#include "config.h"

enum {
        MAX_TREE_HEIGHT   =      10,
        MAX_TREE_TYPE     =    1024,
        MAX_NODE_TYPE     =    1024,
        MAX_ERR_CODE      =    1024,
        MAX_ERR_DEPTH     =      16,
        MAX_CACHELINE     =      64,
        MAX_SEPARATOR_CUT =      10,
        MAX_PREFIX        =      32
};

/* @macro */

#if !defined(DEBUG)
#define DEBUG (1)
#endif

#if !defined(COUNTERS)
#define COUNTERS (1)
#endif

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
#define IMMANENTISE(fmt, ...) immanentise(MSG_PREP(fmt) , ## __VA_ARGS__)
#if DEBUG
#define ASSERT(expr) (LIKELY(expr) ? (void)0 : IMMANENTISE("Assertion failed: %s", #expr))
#else
#define ASSERT(expr) ASSUME(expr)
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

#define NOFAIL(expr)                                            \
({                                                              \
        int result = (expr);                                    \
        if (UNLIKELY(result != 0)) {                            \
                IMMANENTISE(#expr " failed with %i.", result);  \
        }                                                       \
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
#define EXISTS(var, nr, ...) (!FORALL(var, (nr), !(__VA_ARGS__)))

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

#if COUNTERS
#define CINC(cnt) (++__t_counters.cnt)
#define CDEC(cnt) (--__t_counters.cnt)
#define CVAL(cnt) (__t_counters.cnt)
#define GVAL(cnt) (__g_counters.cnt)
#define GDVAL(cnt) (__G_counters.cnt)
#define CADD(cnt, d) (__t_counters.cnt += (d))
#define CMOD(cnt, d) ({ struct counter_var *v = &(__t_counters.cnt); v->sum += (d); v->nr++; })
#define DMOD(cnt, d) ({ struct double_var *v = &(__d_counters.cnt); v->sum += (d); v->nr++; })
#define COUNTERS_ASSERT(expr) ASSERT(expr)
#else
#define CINC(cnt)    ((void)0)
#define CDEC(cnt)    ((void)0)
#define CVAL(cnt)    ((void)0)
#define GVAL(cnt)    ((void)0)
#define GDVAL(cnt)   ((void)0)
#define CADD(cnt, d) ((void)(d))
#define CMOD(cnt, d) ((void)(d))
#define DMOD(cnt, d) ((void)(d))
#define COUNTERS_ASSERT(expr)
#endif /* COUNTERS */

#define KINC(cnt) ({ ci.cnt++; ci.sum++; })
#define KDEC(cnt) ({ ci.cnt--; ci.sum++; })

#define SCALL(mod, method, ...)                         \
({                                                      \
        struct t2_storage *__stor = (mod)->stor;        \
        __stor->op->method(__stor , ##  __VA_ARGS__);   \
})

#define DEFAULT_FORMAT (1)

#if DEFAULT_FORMAT
#define NCALL(n, ...) ((void)(n), simple_ ## __VA_ARGS__)
#else
#define NCALL(n, ...) ((n)->ntype->ops-> __VA_ARGS__)
#endif

/* Is Parallel Programming Hard, And, If So, What Can You Do About It? */
#define ACCESS_ONCE(x)     (*(volatile typeof(x) *)&(x))
#define READ_ONCE(x)       ({ typeof(x) ___x = ACCESS_ONCE(x); ___x; })
#define WRITE_ONCE(x, val) do { ACCESS_ONCE(x) = (val); } while (0)
#define BARRIER()          __asm__ __volatile__("": : :"memory")

/* @types */

struct node;

struct bucket {
        struct cds_hlist_head chain;
};

struct bucketlock {
        alignas(MAX_CACHELINE) pthread_mutex_t lock;
};

struct ht {
        int                shift;
        struct bucket     *buckets;
        struct bucketlock *bucketlocks;
};

enum {
        TADDR_SIZE_MASK =              0xfull,
        TADDR_LOW0_MASK =            0x1f0ull,
        TADDR_ADDR_MASK = 0xfffffffffffe00ull,
        TADDR_REST_MASK = ~0ull & ~(TADDR_SIZE_MASK | TADDR_LOW0_MASK | TADDR_ADDR_MASK),
        TADDR_MIN_SHIFT = 9
};

struct freelist {
        alignas(MAX_CACHELINE) pthread_mutex_t lock;
        struct cds_list_head                   head;
};

struct pool {
        struct freelist free[TADDR_SIZE_MASK + 1];
};

struct cache {
        alignas(MAX_CACHELINE) pthread_mutex_t lock;
        uint64_t                               bolt;
        int32_t                                nr;
        int32_t                                busy;
        int32_t                                dirty;
        int32_t                                incache;
        alignas(MAX_CACHELINE) struct pool     pool;
        alignas(MAX_CACHELINE) pthread_mutex_t guard;
        struct cds_list_head                   cold;
        alignas(MAX_CACHELINE) pthread_mutex_t condlock;
        pthread_cond_t                         need;
        pthread_cond_t                         got;
        int32_t                                scan;
        int                                    shift;
        pthread_t                              md;
};

struct slot;
struct node;
struct path;

struct node_type_ops {
        int     (*insert)    (struct slot *);
        void    (*delete)    (struct slot *);
        void    (*get)       (struct slot *);
        int     (*load)      (struct node *n);
        void    (*make)      (struct node *n);
        void    (*print)     (struct node *n);
        bool    (*search)    (struct node *n, struct path *p, struct slot *out);
        bool    (*can_merge) (const struct node *n0, const struct node *n1);
        int     (*can_insert)(const struct slot *s);
        int32_t (*nr)        (const struct node *n);
        int32_t (*free)      (const struct node *n);
        int32_t (*used)      (const struct node *n);
        int     (*keycmp)    (const struct node *n, int pos, void *addr, int32_t len, uint64_t mask);
};

struct t2 {
        alignas(MAX_CACHELINE) struct ht         ht;
        alignas(MAX_CACHELINE) struct cache      cache;
        const struct t2_tree_type               *ttypes[MAX_TREE_TYPE];
        const struct t2_node_type               *ntypes[MAX_NODE_TYPE];
        struct t2_storage                       *stor;
        bool                                     shutdown;
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

struct mapel {
        int32_t l;
        int32_t delta;
};

struct radixmap {
        uint8_t       pbuf[MAX_PREFIX];
        struct t2_buf prefix;
        struct mapel  zero_sentinel;
        struct mapel  idx[256];
};

enum node_flags {
        HEARD_BANSHEE = 1ull << 0,
        NOCACHE       = 1ull << 1,
        DIRTY         = 1ull << 2
};

struct node {
        struct cds_hlist_node      hash;
        taddr_t                    addr;
        uint64_t                   flags;
        uint64_t                   seq;
        atomic_int                 ref;
        struct cds_list_head       cache;
        const struct t2_node_type *ntype;
        void                      *data;
        struct t2                 *mod;
        struct radixmap           *radix;
        uint64_t                   cookie;
        pthread_rwlock_t           lock;
        struct rcu_head            rcu;
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
        int             used;
        taddr_t         next;
        struct rung     rung[MAX_TREE_HEIGHT];
        struct t2_tree *tree;
        struct t2_rec  *rec;
        enum optype     opt;
        struct node    *newroot;
};

struct policy {
        int (*plan_insert)(struct path *p, int idx);
        int (*plan_delete)(struct path *p, int idx);
        int (*exec_insert)(struct path *p, int idx);
        int (*exec_delete)(struct path *p, int idx);
};

struct t2_node_type {
        const struct node_type_ops *ops;
        int                         shift;
        int16_t                     id;
        const char                 *name;
        struct t2                  *mod;
};

enum {
        NODE_MAGIX = 0x1f2e3d4c
};

struct header {
        struct ewma kelvin;
        int8_t      level;
        uint8_t     pad8;
        uint16_t    ntype;
        uint32_t    magix;
        uint32_t    csum;
        uint32_t    treeid;
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

#if COUNTERS
struct counter_var {
        int64_t sum;
        int64_t nr;
};

struct double_var {
        double  sum;
        int64_t nr;
};

struct counters { /* Must be all 64-bit integers, see counters_fold(). */
        int64_t node;
        int64_t rlock;
        int64_t wlock;
        int64_t rcu;
        int64_t peek;
        int64_t alloc;
        int64_t alloc_pool;
        int64_t alloc_fresh;
        int64_t traverse;
        int64_t traverse_restart;
        int64_t traverse_iter;
        int64_t chain;
        int64_t cookie_miss;
        int64_t cookie_hit;
        int64_t read;
        int64_t read_bytes;
        int64_t write;
        int64_t write_bytes;
        int64_t scan;
        int64_t scan_bucket;
        int64_t throttle_limit;
        int64_t throttle_wait;
        int64_t cull_trylock;
        int64_t cull_limit;
        int64_t cull_node;
        int64_t cull_cleaned;
        struct level_counters {
                int64_t insert_balance;
                int64_t delete_balance;
                int64_t get;
                int64_t search;
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
                int64_t scan_node;
                int64_t scan_cached;
                int64_t scan_busy;
                int64_t scan_hot;
                int64_t scan_pageout;
                int64_t scan_cold;
                int64_t scan_heated;
                int64_t radixmap_updated;
                struct counter_var nr;
                struct counter_var free;
                struct counter_var modified;
                struct counter_var keysize;
                struct counter_var valsize;
                struct counter_var repage;
                struct counter_var sepcut;
                struct counter_var radixmap_left;
                struct counter_var radixmap_right;
                struct counter_var search_span;
                struct counter_var recpos;
                struct counter_var prefix;
        } l[MAX_TREE_HEIGHT];
};

struct double_counters {
        struct double_level_counters {
                struct double_var temperature;
        } l[MAX_TREE_HEIGHT];
};
#endif /* COUNTERS */

struct error_descr {
        int                   err;
        const struct msg_ctx *ctx;
        uint64_t              v0;
        uint64_t              v1;
};

struct node_ref {
        struct node *node;
        int          nr;
        void        *trace[8];
};

struct cacheinfo {
        int     sum;
        int32_t touched;
        int32_t added;
        int32_t busy;
        int32_t dirty;
        int32_t cached;
};

/* @static */

static void buf_copy(const struct t2_buf *dst, const struct t2_buf *src);
static int32_t buf_prefix(const struct t2_buf *dst, const struct t2_buf *src);
static int32_t buf_len(const struct t2_buf *b);
static int buf_cmp(const struct t2_buf *dst, const struct t2_buf *src);
static int buf_alloc(struct t2_buf *dst, struct t2_buf *src);
static void buf_free(struct t2_buf *b);
static int32_t rec_len(const struct t2_rec *r);
static int  ht_init(struct ht *ht, int shift);
static void ht_fini(struct ht *ht);
static void ht_clean(struct ht *ht);
static uint32_t ht_bucket(struct ht *ht, taddr_t addr);
static struct cds_hlist_head *ht_head(struct ht *ht, uint32_t bucket);
static pthread_mutex_t *ht_lock(struct ht *ht, uint32_t bucket);
static struct node *ht_lookup(struct ht *ht, taddr_t addr, uint32_t bucket);
static void ht_insert(struct ht *ht, struct node *n, uint32_t bucket);
static void ht_delete(struct node *n);
static void pool_clean(struct t2 *mod);
static int val_copy(struct t2_rec *r, struct node *n, struct slot *s);
static void buf_clip(struct t2_buf *b, uint32_t mask, void *origin);
static void buf_clip_node(struct t2_buf *b, const struct node *n);
static taddr_t internal_search(struct node *n, struct path *p, int32_t *pos);
static taddr_t internal_get(const struct node *n, int32_t pos);
static struct node *internal_child(const struct node *n, int32_t pos, bool peek);
static int leaf_search(struct node *n, struct path *p, struct slot *s);
static void immanentise(const struct msg_ctx *ctx, ...) __attribute__((noreturn));
static void *mem_alloc(size_t size);
static void *mem_alloc_align(size_t size, int alignment);
static void  mem_free(void *ptr);
static int32_t max_32(int32_t a, int32_t b);
static int32_t min_32(int32_t a, int32_t b);
static int cacheline_size();
static uint64_t threadid(void);
static void llog(const struct msg_ctx *ctx, ...);
static void edescr(const struct msg_ctx *ctx, int err, uint64_t a0, uint64_t a1);
static void eclear();
static void eprint();
static void put(struct node *n);
static void put_locked(struct node *n);
static void ref(struct node *n);
static void touch(struct node *n);
static uint64_t temperature(struct node *n);
static uint64_t bolt(const struct node *n);
static struct node *peek(struct t2 *mod, taddr_t addr);
static struct node *alloc(struct t2_tree *t, int8_t level);
static struct node *neighbour(struct path *p, int idx, enum dir d, enum lock_mode mode);
static void path_add(struct path *p, struct node *n, uint64_t flags);
static bool can_insert(const struct node *n, const struct t2_rec *r);
static bool keep(const struct node *n);
static int dealloc(struct node *n);
static uint8_t level(const struct node *n);
static bool is_leaf(const struct node *n);
static int32_t nr(const struct node *n);
static int32_t nsize(const struct node *n);
static int32_t utmost(const struct node *n, enum dir d);
static void lock(struct node *n, enum lock_mode mode);
static void unlock(struct node *n, enum lock_mode mode);
static void dirty(struct node *n, enum lock_mode lm);
static void radixmap_update(struct node *n);
static struct header *nheader(const struct node *n);
static void rcu_lock();
static void rcu_unlock();
static void rcu_leave(struct path *p, struct node *extra);
static bool rcu_try(struct path *p, struct node *extra);
static bool rcu_enter(struct path *p, struct node *extra);
static int simple_insert(struct slot *s);
static void simple_delete(struct slot *s);
static void simple_get(struct slot *s);
static void simple_make(struct node *n);
static int simple_load(struct node *n);
static bool simple_search(struct node *n, struct path *p, struct slot *out);
static int32_t simple_nr(const struct node *n);
static int32_t simple_free(const struct node *n);
static int simple_can_insert(const struct slot *s);
static int32_t simple_used(const struct node *n);
static bool simple_can_merge(const struct node *n0, const struct node *n1);
static void simple_print(struct node *n);
static bool simple_invariant(const struct node *n);
static int simple_keycmp(const struct node *n, int pos, void *addr, int32_t len, uint64_t mask);
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
static int signal_init(void);
static void signal_fini(void);
static void stacktrace(void);
static void debugger_attach(void);
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
static void cache_clean(struct t2 *mod);
static void *maxwelld(struct t2 *mod);
static void mscan(struct t2 *mod, int32_t toscan, int32_t towrite, int32_t tocache);
static void writeout(struct t2 *mod);
static void cache_sync(struct t2 *mod);
static void throttle(struct t2 *mod);
static void kmod(struct ewma *a, uint32_t t);
static uint64_t kavg(struct ewma *a, uint32_t t);
static void ref_add(struct node *n);
static void ref_del(struct node *n);
static void ref_print(void);

#if COUNTERS
static __thread struct counters __t_counters = {};
static __thread struct double_counters __d_counters = {};
static struct counters __g_counters = {};
static struct double_counters __G_counters = {};
static pthread_mutex_t __g_counters_lock = PTHREAD_MUTEX_INITIALIZER;
#endif
static __thread struct error_descr estack[MAX_ERR_DEPTH] = {};
static __thread int edepth = 0;
static __thread bool thread_registered = false;
static __thread struct cacheinfo ci = {};
static __thread volatile struct {
        volatile jmp_buf *buf;
} addr_check = {};
static struct node_type_ops simple_ops;
static char *argv0;

struct t2 *t2_init(struct t2_storage *storage, int hshift, int cshift) {
        int result;
        struct t2 *mod = mem_alloc(sizeof *mod);
        ASSERT(cacheline_size() / MAX_CACHELINE * MAX_CACHELINE == cacheline_size());
        t2_thread_register();
        eclear();
        result = signal_init();
        if (LIKELY(result == 0)) {
                if (LIKELY(mod != NULL)) {
                        mod->cache.shift = cshift;
                        NOFAIL(pthread_mutex_init(&mod->cache.lock, NULL));
                        NOFAIL(pthread_mutex_init(&mod->cache.guard, NULL));
                        NOFAIL(pthread_mutex_init(&mod->cache.condlock, NULL));
                        NOFAIL(pthread_cond_init(&mod->cache.need, NULL));
                        NOFAIL(pthread_cond_init(&mod->cache.got, NULL));
                        CDS_INIT_LIST_HEAD(&mod->cache.cold);
                        for (int i = 0; i < ARRAY_SIZE(mod->cache.pool.free); ++i) {
                                NOFAIL(pthread_mutex_init(&mod->cache.pool.free[i].lock, NULL));
                                CDS_INIT_LIST_HEAD(&mod->cache.pool.free[i].head);
                        }
                        mod->stor = storage;
                        result = SCALL(mod, init);
                        if (LIKELY(result == 0)) {
                                result = ht_init(&mod->ht, hshift);
                                if (LIKELY(result == 0)) {
                                        result = pthread_create(&mod->cache.md, NULL, (void *(*)(void *))&maxwelld, mod);
                                        if (result != 0) {
                                                ht_fini(&mod->ht);
                                        }
                                }
                                if (result != 0) {
                                        SCALL(mod, fini);
                                }
                        }
                } else {
                        result = ERROR(-ENOMEM);
                }
                if (result != 0) {
                        signal_fini();
                }
        }
        return result != 0 ? EPTR(result) : mod;
}

enum { BOLT_EPOCH_SHIFT = 16 };

void t2_fini(struct t2 *mod) {
        eclear();
        urcu_memb_barrier();
        SET0(&ci);
        mod->shutdown = true;
        mutex_lock(&mod->cache.condlock);
        NOFAIL(pthread_cond_signal(&mod->cache.need));
        mutex_unlock(&mod->cache.condlock);
        pthread_join(mod->cache.md, NULL);
        writeout(mod);
        SCALL(mod, fini);
        cache_clean(mod);
        ht_clean(&mod->ht);
        ht_fini(&mod->ht);
        ASSERT(cds_list_empty(&mod->cache.cold));
        mod->stor->op->fini(mod->stor);
        signal_fini();
        pool_clean(mod);
        for (int i = 0; i < ARRAY_SIZE(mod->cache.pool.free); ++i) {
                NOFAIL(pthread_mutex_destroy(&mod->cache.pool.free[i].lock));
                ASSERT(cds_list_empty(&mod->cache.pool.free[i].head));
        }
        NOFAIL(pthread_cond_destroy(&mod->cache.got));
        NOFAIL(pthread_cond_destroy(&mod->cache.need));
        NOFAIL(pthread_mutex_destroy(&mod->cache.condlock));
        NOFAIL(pthread_mutex_destroy(&mod->cache.guard));
        NOFAIL(pthread_mutex_destroy(&mod->cache.lock));
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

void t2_node_type_register(struct t2 *mod, struct t2_node_type *ntype) {
        ASSERT(IS_IN(ntype->id, mod->ntypes));
        ASSERT(mod->ntypes[ntype->id] == NULL);
        ASSERT(ntype->mod == NULL);
        ASSERT(ntype->shift <= 32);
        mod->ntypes[ntype->id] = ntype;
        ntype->mod = mod;
        eclear();
}


void t2_node_type_degister(struct t2_node_type *ntype)
{
        ASSERT(IS_IN(ntype->id, ntype->mod->ntypes));
        ASSERT(ntype->mod->ntypes[ntype->id] == ntype);
        ntype->mod->ntypes[ntype->id] = NULL;
        ntype->mod = NULL;
        eclear();
}

struct t2_node_type *t2_node_type_init(int16_t id, const char *name, int shift, uint64_t flags) {
        struct t2_node_type *nt = mem_alloc(sizeof *nt);
        if (nt != NULL) {
                nt->id    = id;
                nt->name  = name;
                nt->shift = shift;
                nt->ops   = &simple_ops;
        }
        return nt;
}

void t2_node_type_fini(struct t2_node_type *nt) {
        ASSERT(nt->mod == NULL);
        mem_free(nt);
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
        ASSERT((shift & TADDR_SIZE_MASK) == (uint64_t)shift);
        return addr | shift;
}

static uint64_t zerodata = 0;
static struct t2_buf zero = { .nr = 1, .seg = { [0] = { .len = 0, .addr = &zerodata } } };

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

struct t2_tree *t2_tree_open(struct t2_tree_type *ttype, taddr_t root) {
        ASSERT(thread_registered);
        eclear();
        struct t2_tree *t = mem_alloc(sizeof *t);
        if (t != NULL) {
                t->ttype = ttype;
                t->root  = root;
                return t;
        } else {
                return EPTR(-ENOMEM);
        }
}

void t2_tree_close(struct t2_tree *t) {
        mem_free(t);
}

static int rec_insert(struct node *n, int32_t idx, struct t2_rec *r) {
        CMOD(l[level(n)].recpos, 100 * idx / (nr(n) + 1));
        return NCALL(n, insert(&(struct slot) { .node = n, .idx = idx, .rec  = *r }));
}

static void rec_delete(struct node *n, int32_t idx) {
        NCALL(n, delete(&(struct slot) { .node = n, .idx = idx }));
}

static void rec_get(struct slot *s, int32_t idx) {
        s->idx = idx;
        NCALL(s->node, get(s));
}

static int cookie_node_complete(struct t2_tree *t, struct path *p, struct node *n, enum optype opt) {
        struct t2_rec *r = p->rec;
        int            result;
        bool           found;
        ASSERT(r->key->nr == 1);
        SLOT_DEFINE(s, n);
        rec_get(&s, 0);
        if (buf_cmp(s.rec.key, r->key) > 0) {
                return -ESTALE;
        }
        rec_get(&s, nr(n) - 1);
        if (buf_cmp(s.rec.key, r->key) < 0) {
                return -ESTALE;
        }
        found = leaf_search(n, p, &s);
        switch (opt) {
        case LOOKUP:
                result = found ? val_copy(r, n, &s) : -ENOENT;
                break;
        case INSERT:
                if (!found) {
                        result = rec_insert(n, s.idx + 1, r);
                        if (result == -ENOSPC) {
                                result = -ESTALE;
                        } else if (result == 0) {
                                dirty(n, WRITE);
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
                        dirty(n, WRITE);
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

static int cookie_try(struct path *p) {
        return -ESTALE; /* Cookies do not seem to be very useful. */
        enum lock_mode mode = p->opt == LOOKUP || p->opt == NEXT ? READ : WRITE;
        struct t2_rec *r    = p->rec;
        ASSERT(p->used == -1);
        rcu_lock();
        if (cookie_is_valid(&r->cookie)) {
                struct node *n = COF(r->cookie.hi, struct node, cookie);
                if (is_leaf(n) && nr(n) > 0) { /* TODO: More checks? */
                        int result;
                        rcu_leave(p, n);
                        lock(n, mode); /* TODO: Lock-less lookup. */
                        if (LIKELY(!rcu_try(p, n))) {
                                /* TODO: re-check node. */
                                result = cookie_node_complete(p->tree, p, n, p->opt);
                                unlock(n, mode);
                                put(n);
                                return result;
                        } else {
                                unlock(n, mode);
                                return -ESTALE;
                        }
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
        COUNTERS_ASSERT(CVAL(rcu) == 0);
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
        touch(n);
        if (LIKELY(mode == NONE)) {
                ;
        } else if (mode == WRITE) {
                if (!is_stable(n)) {
                        radixmap_update(n);
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
        return ht_lookup(&mod->ht, addr, ht_bucket(&mod->ht, addr));
}

static struct node *pool_get(struct t2 *mod, taddr_t addr) {
        struct freelist *free = &mod->cache.pool.free[addr & TADDR_SIZE_MASK];
        struct node     *n    = NULL;
        mutex_lock(&free->lock);
        if (!cds_list_empty(&free->head)) {
                n = COF(free->head.next, struct node, cache);
                cds_list_del_init(&n->cache);
                CINC(alloc_pool);
        }
        mutex_unlock(&free->lock);
        return n;
}

static struct node *nalloc(struct t2 *mod, taddr_t addr) {
        struct node *n = pool_get(mod, addr);
        CINC(alloc);
        if (UNLIKELY(n == NULL)) {
                throttle(mod);
                n = pool_get(mod, addr);
                if (UNLIKELY(n == NULL)) {
                        void *data = mem_alloc_align(taddr_ssize(addr), taddr_ssize(addr));
                        n = mem_alloc(sizeof *n);
                        if (LIKELY(n != NULL && data != NULL)) {
                                CINC(alloc_fresh);
                                NOFAIL(pthread_rwlock_init(&n->lock, NULL));
                                CDS_INIT_LIST_HEAD(&n->cache);
                                n->data = data;
                        } else {
                                mem_free(n);
                                mem_free(data);
                                return EPTR(-ENOMEM);
                        }
                }
        }
        n->addr = addr;
        n->mod = mod;
        n->ref = 1;
        cookie_make(&n->cookie);
        CINC(node);
        ref_add(n);
        KINC(busy);
        return n;
}

static void nfini(struct node *n) {
        struct freelist *free = &n->mod->cache.pool.free[n->addr & TADDR_SIZE_MASK];
        ASSERT(n->ref == 0);
        ASSERT(cds_list_empty(&n->cache));
        ASSERT(!(n->flags & DIRTY));
        memset(n->data, 0, taddr_ssize(n->addr));
        cookie_invalidate(&n->cookie);
        n->seq   = 0;
        n->flags = 0;
        n->ntype = NULL;
        n->addr  = 0;
        cookie_invalidate(&n->cookie);
        mutex_lock(&free->lock);
        cds_list_add(&n->cache, &free->head);
        mutex_unlock(&free->lock);
}

static struct node *ninit(struct t2 *mod, taddr_t addr) {
        struct node *n;
        n = nalloc(mod, addr);
        if (EISOK(n)) {
                struct node     *other;
                uint32_t         bucket = ht_bucket(&mod->ht, addr);
                pthread_mutex_t *lock   = ht_lock(&mod->ht, bucket);
                mutex_lock(lock);
                other = ht_lookup(&mod->ht, addr, bucket);
                if (LIKELY(other == NULL)) {
                        ht_insert(&mod->ht, n, bucket);
                        KINC(added);
                } else {
                        n->ref = 0;
                        CDEC(node);
                        KDEC(busy);
                        ref_del(n);
                        nfini(n);
                        n = other;
                        ref(n);
                }
                mutex_unlock(lock);
        }
        return n;
}

static void ref(struct node *n) {
        n->ref++;
        CINC(node);
        ref_add(n);
        KINC(busy);
}

static void ndelete(struct node *n) {
        pthread_mutex_t *lock = ht_lock(&n->mod->ht, ht_bucket(&n->mod->ht, n->addr));
        mutex_lock(lock);
        n->flags |= NOCACHE | HEARD_BANSHEE;
        if (LIKELY(n->flags & DIRTY)) {
                n->flags &= ~DIRTY;
                KDEC(dirty);
        }
        put_locked(n);
        mutex_unlock(lock);
}

static struct node *get(struct t2 *mod, taddr_t addr) {
        struct node *n = ninit(mod, addr);
        COUNTERS_ASSERT(CVAL(rcu) == 0);
        if (EISOK(n)) {
                lock(n, WRITE);
                if (LIKELY(n->ntype == NULL)) {
                        int result = SCALL(n->mod, read, n->addr, n->data);
                        if (LIKELY(result == 0)) {
                                struct header *h = nheader(n);
                                /* TODO: check node. */
                                if (LIKELY(IS_IN(h->ntype, n->mod->ntypes) && n->mod->ntypes[h->ntype] != NULL)) {
                                        rcu_assign_pointer(n->ntype, n->mod->ntypes[h->ntype]);
                                        CMOD(l[level(n)].repage, bolt(n) - h->kelvin.cur);
                                        node_seq_increase(n);
                                        NCALL(n, load(n));
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
                CINC(l[level(n)].get);
        }
        return n;
}

static struct node *alloc(struct t2_tree *t, int8_t level) {
        struct t2           *mod   = t->ttype->mod;
        struct t2_node_type *ntype = t->ttype->ntype(t, level);
        taddr_t              addr  = SCALL(mod, alloc, ntype->shift, ntype->shift);
        struct node      *n;
        COUNTERS_ASSERT(CVAL(rcu) == 0);
        if (EISOK(addr)) {
                n = ninit(mod, addr);
                if (EISOK(n)) {
                        lock(n, WRITE);
                        *nheader(n) = (struct header) {
                                .magix  = NODE_MAGIX,
                                .ntype  = ntype->id,
                                .level  = level,
                                .treeid = t->id
                        };
                        n->ntype = ntype;
                        n->flags |= DIRTY;
                        KINC(dirty);
                        NCALL(n, make(n));
                        unlock(n, WRITE);
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
        if (!cds_list_empty(&n->cache)) {
                cds_list_del_init(&n->cache);
                KDEC(cached);
        }
        call_rcu_memb(&n->rcu, &free_callback);
        KDEC(added);
}

static void put_locked(struct node *n) {
        ASSERT(n->ref > 0);
        EXPENSIVE_ASSERT(n->data != NULL ? is_sorted(n) : true);
        ref_del(n);
        KDEC(busy);
        if (--n->ref == 0) {
                if (n->flags & NOCACHE) {
                        put_final(n);
                }
        }
        CDEC(node);
}

static void put(struct node *n) {
        pthread_mutex_t *lock = ht_lock(&n->mod->ht, ht_bucket(&n->mod->ht, n->addr));
        mutex_lock(lock);
        put_locked(n);
        mutex_unlock(lock);
}

static int dealloc(struct node *n) {
        struct t2 *mod = n->mod;
        ndelete(n);
        SCALL(mod, free, n->addr);
        return 0;
}

static uint64_t temperature(struct node *n) {
        return kavg(&nheader(n)->kelvin, bolt(n));
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
        return NCALL(n, nr(n));
}

static int32_t nsize(const struct node *n) {
        return (int32_t)1 << n->ntype->shift;
}

static void rcu_lock() {
        urcu_memb_read_lock();
        COUNTERS_ASSERT(CVAL(rcu) == 0);
        CINC(rcu);
}

static void rcu_unlock() {
        CDEC(rcu);
        urcu_memb_read_unlock();
}

static void rcu_quiescent() {
        urcu_memb_quiescent_state();
}

static void radixmap_update(struct node *n) {
        struct radixmap *m;
        int32_t          i;
        int16_t          ch;
        int32_t          prev = -1;
        int32_t          pidx = -1;
        int32_t          plen;
        SLOT_DEFINE(s, n);
        if (is_stable(n)) {
                return;
        }
        if (UNLIKELY(n->radix == NULL)) {
                n->radix = mem_alloc(sizeof *n->radix);
                if (UNLIKELY(n->radix == NULL)) {
                        return;
                }
                n->radix->prefix.nr = 1;
                n->radix->prefix.seg[0].addr = &n->radix->pbuf[0];
        }
        m = n->radix;
        CINC(l[level(n)].radixmap_updated);
        if (LIKELY(nr(n) > 1)) {
                struct t2_buf l;
                struct t2_buf r;
                rec_get(&s, 0);
                l = *s.rec.key;
                rec_get(&s, nr(n) - 1);
                r = *s.rec.key;
                plen = min_32(buf_prefix(&l, &r), ARRAY_SIZE(m->pbuf));
                memcpy(m->prefix.seg[0].addr, l.seg[0].addr, plen);
                m->prefix.seg[0].len = plen;
        } else {
                plen = m->prefix.seg[0].len = 0;
        }
        CMOD(l[level(n)].prefix, plen);
        for (i = 0; i < nr(n); ++i) {
                rec_get(&s, i);
                if (LIKELY(s.rec.key->seg[0].len > plen)) {
                        ch = ((uint8_t *)s.rec.key->seg[0].addr)[plen];
                } else {
                        ch = -1;
                        pidx = 0;
                        ASSERT(i == 0);
                }
                if (prev < ch) {
                        for (; prev < ch; ++prev) {
                                m->idx[prev] = (struct mapel){ pidx, i - pidx };
                        }
                        pidx = i;
                }
        }
        for (; prev < ARRAY_SIZE(m->idx); ++prev) {
                m->idx[prev] = (struct mapel){ pidx, i - pidx };
        }
}

/* @policy */

#define USE_PREFIX_SEPARATORS (1)

static int32_t prefix_separator(const struct t2_buf *l, struct t2_buf *r, int level) {
        ASSERT(buf_cmp(l, r) < 0);
        ASSERT(r->nr == 1);
        if (USE_PREFIX_SEPARATORS) {
                int i;
                for (i = 0; i < MAX_SEPARATOR_CUT; ++i) {
                        r->seg[0].len--;
                        if (buf_cmp(l, r) >= 0) {
                                ++r->seg[0].len;
                                break;
                        }
                }
                CMOD(l[level].sepcut, i);
        }
        return r->seg[0].len;
}

static void rec_todo(struct path *p, int idx, struct slot *out) {
        if (idx == p->used) {
                *out->rec.key = *p->rec->key;
                *out->rec.val = *p->rec->val;
        } else {
                ASSERT(idx < p->used);
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
               if (LIKELY(p->used + 1 < MAX_TREE_HEIGHT)) {
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
                NOFAIL(NCALL(s.node, insert(&s)));
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
                                prefix_separator(&lkey, &rkey, level(left));
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
        return NCALL(n0, can_merge(n0, n1));
}

static void delete_update(struct path *p, int idx, struct slot *s) {
        ASSERT(idx < p->used);
        NCALL(s->node, delete(s));
        if (p->rung[idx + 1].flags & SEPCHG) {
                struct node  *child = brother(&p->rung[idx + 1], RIGHT)->node;
                struct t2_buf cptr;
                SLOT_DEFINE(sub, child);
                {       /* A new scope for the second SLOT_DEFINE(). */
                        SLOT_DEFINE(leaf, p->rung[p->used].node);
                        ASSERT(child != NULL && !is_leaf(child));
                        rec_get(&sub, 0);
                        *s->rec.key = *sub.rec.key;
                        *s->rec.val = *ptr_buf(child, &cptr);
                        /* Take the rightmost key in the leaf. */
                        rec_get(&leaf, nr(leaf.node) - 1);
                        prefix_separator(leaf.rec.key, s->rec.key, level(s->node));
                        NOFAIL(NCALL(s->node, insert(s)));
                }
        }
}

static bool utmost_path(struct path *p, int idx, enum dir d) {
        return FORALL(i, idx, p->rung[i].lm == WRITE ? p->rung[i].pos == utmost(p->rung[i].node, d) : true);
}

static int split_right_exec_delete(struct path *p, int idx) {
        int result = 0;
        struct rung *r = &p->rung[idx];
        struct node *right = brother(r, RIGHT)->node;
        SLOT_DEFINE(s, r->node);
        if (!is_leaf(r->node)) {
                if (UNLIKELY(nr(p->rung[idx + 1].node) == 0)) { /* Rightmost in the tree. */
                        ASSERT(utmost_path(p, idx, RIGHT));
                        s.idx = r->pos;
                        NCALL(s.node, delete(&s));
                } else if (r->pos + 1 < nr(r->node)) {
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
                ASSERT(nr(right) > 0);
                NOFAIL(merge(r->node, right, LEFT)); /* TODO: deallocate the empty node. */
                ASSERT(nr(r->node) > 0);
                EXPENSIVE_ASSERT(is_sorted(r->node));
                r->flags &= ~SEPCHG;
                result = +1;
        } else if (UNLIKELY(nr(r->node) == 0)) {
                ASSERT(utmost_path(p, idx, RIGHT));
                return +1;
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
        SASSERT(NONE == 0);
        p->used = -1;
        p->tree = t;
        p->rec  = r;
        p->opt  = opt;
}

static void dirty(struct node *n, enum lock_mode lm) {
        if (n != NULL && lm == WRITE) {
                ASSERT(is_stable(n));
                node_seq_increase(n);
                if (!(n->flags & DIRTY)) {
                        n->flags |= DIRTY;
                        KINC(dirty);
                }
        }
}

static void path_dirty(struct path *p) {
        for (int i = p->used; i >= 0; --i) {
                struct rung    *r     = &p->rung[i];
                struct sibling *left  = brother(r, LEFT);
                struct sibling *right = brother(r, RIGHT);
                dirty(r->node, r->lm);
                dirty(left->node, left->lm);
                dirty(right->node, right->lm);
                dirty(r->allocated, WRITE);
        }
        dirty(p->newroot, WRITE);
}

static void path_lock(struct path *p) {
        /* Top to bottom, left to right. */
        if (UNLIKELY(p->newroot != NULL)) {
                lock(p->newroot, WRITE);
        }
        for (int i = 0; i <= p->used; ++i) {
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
                if (r->allocated != NULL) {
                        lock(r->allocated, WRITE);
                }
        }
}

static void path_fini(struct path *p) {
        for (; p->used >= 0; --p->used) {
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
                        unlock(r->allocated, WRITE);
                        if (LIKELY(r->flags & ALUSED)) {
                                put(r->allocated);
                        } else {
                                dealloc(r->allocated);
                        }
                }
                buf_free(&r->scratch);
        }
        p->used = -1;
        if (UNLIKELY(p->newroot != NULL)) {
                unlock(p->newroot, WRITE);
                put(p->newroot);
        }
}

static void path_reset(struct path *p) {
        path_fini(p);
        memset(&p->rung, 0, sizeof p->rung);
        p->newroot = NULL;
        p->next = p->tree->root;
        CINC(traverse_restart);
}

static void path_pin(struct path *p) {
        for (int i = p->used; i >= 0; --i) {
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
                (i == p->used) == is_leaf(n);
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

static void path_add(struct path *p, struct node *n, uint64_t flags) {
        struct rung *r = &p->rung[++p->used];
        ASSERT(IS_IN(p->used + 1, p->rung));
        r->node = n;
        r->seq  = node_seq(n);
        r->flags = flags;
}

static bool path_is_valid(const struct path *p) {
        return p->rung[0].node->addr == p->tree->root && FORALL(i, p->used + 1, rung_is_valid(p, i));
}

static bool can_insert(const struct node *n, const struct t2_rec *r) {
        const struct slot s = {
                .node = (struct node *)n,
                .idx  = -1, /* Unknown position. */
                .rec  = *r
        };
        return NCALL(n, can_insert(&s));
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

static bool should_split(const struct node *n) {
        /* Keep enough free space in the internal nodes, to be able to update the delimiting key. */
        return USE_PREFIX_SEPARATORS ? (level(n) >= 2 && NCALL(n, free(n)) < MAX_SEPARATOR_CUT) : false;
}

static int insert_prep(struct path *p) {
        struct t2_rec  irec = {};
        int            idx = p->used;
        struct t2_rec *rec = p->rec;
        int            result = 0;
        SLOT_DEFINE(s, p->rung[idx].node);
        if (leaf_search(p->rung[idx].node, p, &s)) {
                return -EEXIST;
        }
        p->rung[idx].pos = s.idx;
        do {
                struct rung *r = &p->rung[idx];
                r->lm = WRITE;
                if (can_insert(r->node, rec) && !should_split(r->node)) {
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
        return NCALL(n, free(n)) < 3 * nsize(n) / 4;
}

static int delete_prep(struct path *p) {
        int idx    = p->used;
        int result = 0;
        SLOT_DEFINE(s, p->rung[idx].node);
        if (!leaf_search(p->rung[idx].node, p, &s)) {
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
        struct rung      *r      = &p->rung[p->used];
        struct t2_cursor *c      = (void *)p->rec->vcb;
        int               result = 0;
        SLOT_DEFINE(s, r->node);
        if (!leaf_search(r->node, p, &s) && (enum dir)c->dir == RIGHT) {
                s.idx++;
        }
        r->pos = s.idx;
        r->lm = READ;
        sibling = neighbour(p, p->used, (enum dir)c->dir, READ);
        if (EISERR(sibling)) {
                result = ERROR(ERRCODE(sibling));
        }
        path_lock(p);
        return result;
}

static int lookup_complete(struct path *p, struct node *n) {
        SLOT_DEFINE(s, NULL);
        return leaf_search(n, p, &s) ? val_copy(p->rec, n, &s) : -ENOENT;
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
        SLOT_DEFINE(s, oldroot);
        if (UNLIKELY(buf_len(&p->rung[0].keyout) == 0 && buf_len(&p->rung[0].valout) == 0)) {
                return 0; /* Nothing to do. */
        }
        rec_get(&s, 0);
        s.node = p->newroot;
        s.rec.val = ptr_buf(oldroot, &ptr);
        NOFAIL(NCALL(s.node, insert(&s)));
        s.idx = 1;
        ASSERT(p->rung[0].pd.id == SPLIT_RIGHT); /* For now. */
        s.rec.key = &p->rung[0].keyout;
        s.rec.val = &p->rung[0].valout;
        NOFAIL(NCALL(s.node, insert(&s)));
        p->rung[0].flags |= ALUSED;
        /* Barrier? */
        p->tree->root = p->newroot->addr;
        return 0;
}

static int insert_balance(struct path *p) {
        int idx;
        int result = 0;
        for (idx = p->used; idx >= 0; --idx) {
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
        int result = rec_insert(n, p->rung[p->used].pos + 1, p->rec);
        if (result == -ENOSPC) {
                result = insert_balance(p);
        }
        cookie_complete(p, n);
        return result;
}

static int delete_balance(struct path *p) {
        int idx;
        int result = 0;
        for (idx = p->used; idx >= 0; --idx) {
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
        rec_delete(n, p->rung[p->used].pos);
        if (!keep(n)) {
                result = delete_balance(p);
        }
        cookie_complete(p, n);
        return result;
}

static int next_complete(struct path *p, struct node *n) {
        struct rung      *r      = &p->rung[p->used];
        struct t2_cursor *c      = (void *)p->rec->vcb;
        int               result = +1;
        SLOT_DEFINE(s, n);
        for (s.idx = r->pos; 0 <= s.idx && s.idx < nr(n); s.idx += c->dir) {
                NCALL(n, get(&s));
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

static void rcu_leave(struct path *p, struct node *extra) {
        path_pin(p);
        if (extra != NULL) {
                ref(extra);
        }
        rcu_unlock();
}

static bool rcu_try(struct path *p, struct node *extra) {
        bool result;
        result = EXISTS(i, p->used + 1, p->rung[i].node->flags & HEARD_BANSHEE) || (extra != NULL && (extra->flags & HEARD_BANSHEE));
        if (UNLIKELY(result)) {
                urcu_memb_barrier();
                path_reset(p);
                if (extra != NULL) {
                        put(extra);
                }
        }
        return result;
}

static bool rcu_enter(struct path *p, struct node *extra) {
        bool result = rcu_try(p, extra);
        rcu_lock();
        return result;
}

enum { CACHE_SYNC_THRESHOLD = 32 };

static void cache_sync(struct t2 *mod) { /* TODO: Leaks on thread exit. */
        if (ci.sum > CACHE_SYNC_THRESHOLD) {
                mutex_lock(&mod->cache.lock);
                mod->cache.bolt    += ci.touched;
                mod->cache.busy    += ci.busy;
                mod->cache.nr      += ci.added;
                mod->cache.dirty   += ci.dirty;
                mod->cache.incache += ci.cached;
                mutex_unlock(&mod->cache.lock);
                SET0(&ci);
        }
}

static uint64_t bolt(const struct node *n) {
        return (n->mod->cache.bolt + ci.touched) >> BOLT_EPOCH_SHIFT;
}

static void touch(struct node *n) {
        kmod(&nheader(n)->kelvin, bolt(n));
        KINC(touched);
}

enum {
        DONE  = 1,
        AGAIN = 2
};

static int traverse_complete(struct path *p, int result) {
        if (UNLIKELY(rcu_try(p, NULL))) {
                rcu_lock();
                return AGAIN;
        } else if (UNLIKELY(result == -ESTALE)) {
                path_reset(p);
                rcu_lock();
                return AGAIN;
        } else if (UNLIKELY(result != 0)) {
                return result;
        } else if (UNLIKELY(!path_is_valid(p))) {
                path_reset(p);
                rcu_lock();
                return AGAIN;
        } else {
                if (p->opt != NEXT) {
                        path_dirty(p);
                }
                return DONE;
        }
}

static int traverse(struct path *p) {
        struct t2 *mod   = p->tree->ttype->mod;
        int        result;
        ASSERT(p->used == -1);
        ASSERT(p->opt == LOOKUP || p->opt == INSERT || p->opt == DELETE || p->opt == NEXT);
        CINC(traverse);
        p->next = p->tree->root;
        rcu_lock();
        while (true) {
                struct node *n;
                uint64_t     flags = 0;
                COUNTERS_ASSERT(CVAL(rcu) == 1);
                CINC(traverse_iter);
                n = peek(mod, p->next);
                if (n == NULL || rcu_dereference(n->ntype) == NULL) {
                        rcu_leave(p, NULL);
                        n = get(mod, p->next);
                        if (EISERR(n)) {
                                if (ERRCODE(n) == -ESTALE) {
                                        path_reset(p);
                                        rcu_lock();
                                        continue;
                                } else {
                                        result = ERROR(ERRCODE(n));
                                        break;
                                }
                        } else {
                                if (UNLIKELY(rcu_enter(p, n))) {
                                        continue;
                                }
                                flags |= PINNED;
                        }
                } else {
                        if (!is_stable(n)) { /* This is racy, but OK. */
                                rcu_leave(p, n);
                                lock(n, READ); /* Wait for stabilisation. */
                                unlock(n, READ);
                                if (UNLIKELY(rcu_enter(p, n))) {
                                        continue;
                                }
                                flags |= PINNED;
                        }
                }
                if (UNLIKELY(p->used + 1 == ARRAY_SIZE(p->rung))) {
                        path_reset(p);
                        continue;
                }
                path_add(p, n, flags);
                if (is_leaf(n)) {
                        if (p->opt == LOOKUP) {
                                result = lookup_complete(p, n);
                                if (!path_is_valid(p)) {
                                        path_reset(p);
                                } else {
                                        rcu_unlock();
                                        break;
                                }
                        } else if (p->opt == INSERT) {
                                rcu_leave(p, NULL);
                                result = traverse_complete(p, insert_prep(p));
                                if (result == DONE) {
                                        result = insert_complete(p, n);
                                        break;
                                } else if (result < 0) {
                                        break;
                                }
                        } else if (p->opt == DELETE) {
                                rcu_leave(p, NULL);
                                result = traverse_complete(p, delete_prep(p));
                                if (result == DONE) {
                                        result = delete_complete(p, n);
                                        break;
                                } else if (result < 0) {
                                        break;
                                }
                        } else {
                                rcu_leave(p, NULL);
                                result = traverse_complete(p, next_prep(p));
                                if (result == DONE) {
                                        result = next_complete(p, n);
                                        break;
                                } else if (result < 0) {
                                        break;
                                }
                        }
                } else {
                        p->next = internal_search(n, p, &p->rung[p->used].pos);
                }
        }
        COUNTERS_ASSERT(CVAL(rcu) == 0);
        return result;
}

static int traverse_result(struct t2_tree *t, struct t2_rec *r, enum optype opt) {
        int         result;
        struct path p = {};
        counters_check();
        path_init(&p, t, r, opt);
        result = cookie_try(&p);
        if (result == -ESTALE) {
                CINC(cookie_miss);
                result = traverse(&p);
        } else {
                CINC(cookie_hit);
        }
        cache_sync(t->ttype->mod);
        path_fini(&p);
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
        ASSERT(buf_len(r->key) > 0);
        eclear();
        return delete(t, r);
}

int t2_insert(struct t2_tree *t, struct t2_rec *r) {
        ASSERT(thread_registered);
        ASSERT(buf_len(r->key) > 0);
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

enum { FREE_BATCH = 16 };

static void cache_clean(struct t2 *mod) {
        struct node *tail;
        mutex_lock(&mod->cache.guard);
        while (!cds_list_empty(&mod->cache.cold)) {
                tail = COF(mod->cache.cold.prev, struct node, cache);
                cds_list_del_init(&tail->cache);
        }
        mutex_unlock(&mod->cache.guard);
}

static bool is_hot(struct node *n, int shift) {
        return (kavg(&nheader(n)->kelvin, bolt(n)) >>
                ((n->addr & TADDR_SIZE_MASK) + (64 - BOLT_EPOCH_SHIFT) + (shift - BOLT_EPOCH_SHIFT))) != 0;
}

enum cachestate {
        BUSY,
        HOT,
        UNCLEAN,
        COLD
};

static enum cachestate nstate(struct node *n, int shift) {
        __attribute__((unused)) uint8_t lev = level(n);
        CINC(l[lev].scan_node);
        if (n->ref > 0) {
                CINC(l[lev].scan_busy);
                return BUSY;
        } else if (is_hot(n, shift)) {
                CINC(l[lev].scan_hot);
                return HOT;
        } else if (n->flags & DIRTY) {
                CINC(l[lev].scan_pageout);
                return UNCLEAN;
        } else {
                CINC(l[lev].scan_cold);
                return COLD;
        }
}

static void cull(struct t2 *mod) {
        struct cache *c     = &mod->cache;
        int           shift = c->shift;
        if (c->nr + ci.added >= (1 << c->shift)) {
                CINC(cull_limit);
                mutex_lock(&c->guard);
                for (int i = 0; i < FREE_BATCH && LIKELY(!cds_list_empty(&c->cold)); ++i) {
                        struct node     *tail = COF(c->cold.prev, struct node, cache);
                        pthread_mutex_t *lock = ht_lock(&mod->ht, ht_bucket(&mod->ht, tail->addr));
                        int              try  = pthread_mutex_trylock(lock);
                        if (LIKELY(try == 0)) {
                                CINC(cull_node);
                                if (nstate(tail, shift) == COLD) {
                                        CINC(cull_cleaned);
                                        put_final(tail);
                                }
                                mutex_unlock(lock);
                        } else {
                                CINC(cull_trylock);
                                ASSERT(try == EBUSY);
                                break;
                        }
                }
                mutex_unlock(&c->guard);
        }
}

static void throttle(struct t2 *mod) {
        struct cache *c = &mod->cache;
        if (c->nr + ci.added >= (1 << c->shift)) {
                CINC(throttle_limit);
                if (UNLIKELY(cds_list_empty(&c->cold))) {
                        mutex_lock(&c->condlock);
                        pthread_cond_signal(&c->need);
                        if (cds_list_empty(&c->cold)) {
                                pthread_cond_wait(&c->got, &c->condlock);
                                CINC(throttle_wait);
                        }
                        mutex_unlock(&c->condlock);
                }
                cull(mod);
        }
}

static void pageout(struct node *n) {
        lock(n, READ);
        if (LIKELY(n->flags & DIRTY)) {
                int result = SCALL(n->mod, write, n->addr, n->data);
                if (LIKELY(result == 0)) {
                        CINC(write);
                        CADD(write_bytes, taddr_ssize(n->addr));
                        n->flags &= ~DIRTY;
                        KDEC(dirty);
                } else {
                        LOG("Pageout failure: %"PRIx64": %i/%i.\n", n->addr, result, errno);
                }
        }
        unlock(n, READ);
}

static void bucket_scan(struct t2 *mod, int shift, int32_t bucket, int32_t *toscan, int32_t *towrite, int32_t *tocache) {
        bool                   done;
        struct cds_hlist_head *head = ht_head(&mod->ht, bucket);
        pthread_mutex_t       *lock = ht_lock(&mod->ht, bucket);
        CINC(scan_bucket);
        if (head->next == NULL) {
                return;
        }
        mutex_lock(lock);
        do {
                struct node *n;
                done = true;
                cds_hlist_for_each_entry_2(n, head, hash) {
                        struct node *tail;
                        (*toscan)--;
                        if (!cds_list_empty(&n->cache)) {
                                CINC(l[level(n)].scan_cached);
                                continue;
                        }
                        switch(nstate(n, shift)) {
                        case BUSY:
                        case HOT:
                                continue;
                        case UNCLEAN:
                                ref(n);
                                mutex_unlock(lock);
                                pageout(n);
                                (*towrite)--;
                                mutex_lock(lock);
                                put_locked(n);
                                done = false;
                                break;
                        case COLD:
                                mutex_lock(&mod->cache.guard);
                                ASSERT(cds_list_empty(&n->cache));
                                cds_list_add(&n->cache, &mod->cache.cold);
                                tail = COF(mod->cache.cold.prev, struct node, cache);
                                if (nstate(tail, shift) == COLD) {
                                        cds_list_move(&n->cache, &mod->cache.cold);
                                        KINC(cached);
                                } else {
                                        cds_list_del_init(&tail->cache);
                                        CINC(l[level(tail)].scan_heated);
                                }
                                mutex_unlock(&mod->cache.guard);
                                (*tocache)--;
                        }
                        if (!done) {
                                break;
                        }
                }
        } while (!done);
        mutex_unlock(lock);
}

static void mscan(struct t2 *mod, int32_t toscan, int32_t towrite, int32_t tocache) {
        int32_t scan0   = mod->cache.scan;
        int32_t scan    = scan0;
        int32_t mask    = (1 << mod->ht.shift) - 1;
        int     shift   = mod->cache.shift;
        ASSERT(mod->ht.shift < 32);
        ASSERT((scan0 & mask) == scan0);
        CINC(scan);
        while (toscan > 0 && towrite > 0 && tocache > 0) {
                bucket_scan(mod, shift, scan, &toscan, &towrite, &tocache);
                cache_sync(mod);
                scan = (scan + 1) & mask;
                if (scan == scan0) {
                        break;
                }
        }
        mod->cache.scan = scan;
}

enum { MAXWELL_SLEEP = 1 };

static void *maxwelld(struct t2 *mod) {
        struct cache *c = &mod->cache;
        while (!mod->shutdown) {
                struct timeval  cur;
                struct timespec deadline;
                gettimeofday(&cur, NULL);
                deadline.tv_sec  = cur.tv_sec + MAXWELL_SLEEP;
                deadline.tv_nsec = 0;
                mutex_lock(&c->condlock);
                if (c->nr + CACHE_SYNC_THRESHOLD < (1 << c->shift)) {
                        pthread_cond_timedwait(&c->need, &c->condlock, &deadline);
                }
                mutex_unlock(&c->condlock);
                mscan(mod, FREE_BATCH * 10, FREE_BATCH * 2, FREE_BATCH * 2);
                cull(mod);
                counters_fold();
                cache_sync(mod);
                mutex_lock(&c->condlock);
                pthread_cond_broadcast(&c->got);
                mutex_unlock(&c->condlock);
        }
        return NULL;
}

static void writeout(struct t2 *mod) {
        int32_t scan = 0;
        do {
                struct cds_hlist_head *head = &mod->ht.buckets[scan].chain;
                struct node           *n;
                cds_hlist_for_each_entry_2(n, head, hash) {
                        if (n->flags & DIRTY) {
                                pageout(n);
                        }
                }
                scan = (scan + 1) & ((1 << mod->ht.shift) - 1);
        } while (scan != 0);
}

/* @lib */

__attribute__((noreturn)) static void immanentise(const struct msg_ctx *ctx, ...)
{
        va_list args;
        fprintf(stderr, "%s (%s/%i): Immanentising the eschaton: ", ctx->func, ctx->file, ctx->lineno);
        va_start(args, ctx);
        vfprintf(stderr, ctx->fmt, args);
        va_end(args);
        puts("");
        stacktrace();
        printf("pid: %lu tid: %lu pthread: %"PRIx64" errno: %i\n",
               (unsigned long)getpid(), (unsigned long)threadid(), (uint64_t)pthread_self(), errno);
        eprint();
        debugger_attach();
        abort();
}

bool t2_is_eptr(void *ptr) {
        return (unsigned long)ptr >= (unsigned long)-MAX_ERR_CODE;
}

void *t2_errptr(int errcode) {
        ASSERT(0 <= errcode && errcode <= MAX_ERR_CODE);
        return (void *)(uint64_t)-errcode;
}

static void *mem_alloc_align(size_t size, int alignment) {
        void *out = NULL;
        int   result = posix_memalign(&out, alignment, size);
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
        puts("");
}

static int32_t min_32(int32_t a, int32_t b) {  /* Hacker's Delight. */
        return b + ((a - b) & ((a - b) >> 31));
}

static int32_t max_32(int32_t a, int32_t b) {
        return a - ((a - b) & ((a - b) >> 31));
}

static int ilog2(uint32_t x) {
        x = x | (x >>  1);
        x = x | (x >>  2);
        x = x | (x >>  4);
        x = x | (x >>  8);
        x = x | (x >> 16);
        return __builtin_popcount(x) - 1;
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

#if COUNTERS

static void counters_check() {
        if (CVAL(node) != 0) {
                LOG("Leaked node: %i.", CVAL(node));
                ref_print();
                ASSERT(false);
        }
        if (CVAL(rlock) != 0) {
                LOG("Leaked rlock: %i.", CVAL(rlock));
        }
        if (CVAL(wlock) != 0) {
                LOG("Leaked wlock: %i.", CVAL(wlock));
        }
        if (CVAL(rcu) != 0) {
                LOG("Leaked rcu: %i.", CVAL(rcu));
        }
}

static void counter_print(int offset, const char *label) {
        printf("%-20s ", label);
        for (int i = 0; i < ARRAY_SIZE(GVAL(l)); ++i) {
                printf("%10"PRId64" ", *(uint64_t *)(((void *)&GVAL(l[i])) + offset));
        }
        puts("");
}

static void counter_var_print(int offset, const char *label) {
        printf("%-20s ", label);
        for (int i = 0; i < ARRAY_SIZE(CVAL(l)); ++i) {
                struct counter_var *v = (((void *)&GVAL(l[i])) + offset);
                printf("%10.1f ", v->nr ? 1.0 * v->sum / v->nr : 0.0);
        }
        puts("");
}

static void double_var_print(int offset, const char *label) {
        printf("%-20s ", label);
        for (int i = 0; i < ARRAY_SIZE(CVAL(l)); ++i) {
                struct double_var *v = (((void *)&GDVAL(l[i])) + offset);
                printf("%10.4f ", v->nr ? 1.0 * v->sum / v->nr : 0.0);
        }
        puts("");
}

#define COUNTER_PRINT(counter) \
        counter_print(offsetof(struct level_counters, counter), #counter)

#define COUNTER_VAR_PRINT(counter) \
        counter_var_print(offsetof(struct level_counters, counter), #counter)

#define DOUBLE_VAR_PRINT(counter) \
        double_var_print(offsetof(struct double_level_counters, counter), #counter)

static void counters_print() {
        counters_fold();
        printf("peek:               %10"PRId64"\n", GVAL(peek));
        printf("alloc:              %10"PRId64"\n", GVAL(alloc));
        printf("alloc.pool:         %10"PRId64"\n", GVAL(alloc_pool));
        printf("alloc.fresh:        %10"PRId64"\n", GVAL(alloc_fresh));
        printf("traverse:           %10"PRId64"\n", GVAL(traverse));
        printf("traverse.restart:   %10"PRId64"\n", GVAL(traverse_restart));
        printf("traverse.iter:      %10"PRId64"\n", GVAL(traverse_iter));
        printf("chain:              %10"PRId64"\n", GVAL(chain));
        printf("cookie.miss:        %10"PRId64"\n", GVAL(cookie_miss));
        printf("cookie.hit:         %10"PRId64"\n", GVAL(cookie_hit));
        printf("read:               %10"PRId64"\n", GVAL(read));
        printf("read.bytes:         %10"PRId64"\n", GVAL(read_bytes));
        printf("write:              %10"PRId64"\n", GVAL(write));
        printf("write.bytes:        %10"PRId64"\n", GVAL(write_bytes));
        printf("scan:               %10"PRId64"\n", GVAL(scan));
        printf("scan.bucket:        %10"PRId64"\n", GVAL(scan_bucket));
        printf("throttle.limit:     %10"PRId64"\n", GVAL(throttle_limit));
        printf("throttle.wait:      %10"PRId64"\n", GVAL(throttle_wait));
        printf("cull.trylock:       %10"PRId64"\n", GVAL(cull_trylock));
        printf("cull.limit:         %10"PRId64"\n", GVAL(cull_limit));
        printf("cull.node:          %10"PRId64"\n", GVAL(cull_node));
        printf("cull.cleaned:       %10"PRId64"\n", GVAL(cull_cleaned));
        printf("%20s ", "");
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
        COUNTER_PRINT(nospc);
        COUNTER_PRINT(dirmove);
        COUNTER_PRINT(recget);
        COUNTER_PRINT(moves);
        COUNTER_PRINT(make);
        COUNTER_PRINT(shift);
        COUNTER_PRINT(shift_one);
        COUNTER_PRINT(merge);
        COUNTER_PRINT(scan_node);
        COUNTER_PRINT(scan_cached);
        COUNTER_PRINT(scan_busy);
        COUNTER_PRINT(scan_hot);
        COUNTER_PRINT(scan_pageout);
        COUNTER_PRINT(scan_cold);
        COUNTER_PRINT(scan_heated);
        COUNTER_PRINT(radixmap_updated);
        COUNTER_VAR_PRINT(search_span);
        COUNTER_VAR_PRINT(radixmap_left);
        COUNTER_VAR_PRINT(radixmap_right);
        COUNTER_VAR_PRINT(nr);
        COUNTER_VAR_PRINT(free);
        COUNTER_VAR_PRINT(recpos);
        COUNTER_VAR_PRINT(modified);
        COUNTER_VAR_PRINT(keysize);
        COUNTER_VAR_PRINT(valsize);
        COUNTER_VAR_PRINT(repage);
        COUNTER_VAR_PRINT(sepcut);
        COUNTER_VAR_PRINT(prefix);
        DOUBLE_VAR_PRINT(temperature);
}

static void counters_clear() {
        SET0(&__g_counters);
        SET0(&__G_counters);
}

static void counters_fold() {
        uint64_t          *dst = (void *)&__g_counters;
        uint64_t          *src = (void *)&__t_counters;
        struct double_var *ds  = (void *)&__d_counters;
        struct double_var *dd  = (void *)&__G_counters;
        SASSERT(sizeof __g_counters % sizeof(int64_t) == 0);
        mutex_lock(&__g_counters_lock);
        for (long unsigned i = 0; i < (sizeof __g_counters / sizeof(int64_t)); ++i) {
                dst[i] += src[i];
        }
        for (long unsigned i = 0; i < (sizeof __d_counters / sizeof *ds); ++i) {
                dd[i].sum += ds[i].sum;
                dd[i].nr  += ds[i].nr;
        }
        mutex_unlock(&__g_counters_lock);
        SET0(&__t_counters);
}

#else /* COUNTERS */

static void counters_check() {
}

static void counters_print() {
}

static void counters_clear() {
}

static void counters_fold() {
}

#endif /* COUNTERS */

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
        debugger_attach();
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

#define REF_DEBUG (0)

#if REF_DEBUG

static __thread struct node_ref refs[8] = {};

static void ref_add(struct node *n) {
        for (int i = 0; i < ARRAY_SIZE(refs); ++i) {
                if (refs[i].node == NULL) {
                        refs[i].trace[0] = __builtin_return_address(2);
                        refs[i].node = n;
                        break;
                }
        }
}

static void ref_del(struct node *n) {
        for (int i = 0; i < ARRAY_SIZE(refs); ++i) {
                if (refs[i].node == n) {
                        refs[i].node = NULL;
                        break;
                }
        }
}

static void ref_print(void) {
        printf("Leaked references:\n");
        for (int i = 0; i < ARRAY_SIZE(refs); ++i) {
                if (refs[i].node != NULL) {
                        printf("%p\n", refs[i].node);
                        backtrace_symbols_fd(refs[i].trace, 1, 1);
                }
        }
}
#else
static void ref_add(struct node *n) {
}

static void ref_del(struct node *n) {
}

static void ref_print(void) {
}
#endif

#if ON_DARWIN
static uint64_t threadid(void)
{
        uint64_t tid;
        NOFAIL(pthread_threadid_np(NULL, &tid));
        return tid;
}
#elif ON_LINUX
static uint64_t threadid(void)
{
        return syscall(SYS_gettid);
}
#endif

static void debugger_attach(void) {
        int         result;
        const char *debugger = getenv("DEBUGGER");
        if (debugger == NULL) {
                return;
        }
        if (argv0 == NULL) {
                puts("Quod est nomen meum?");
                return;
        }
        result = fork();
        if (result > 0) {
                pause();
        } else if (result == 0) {
                const char *argv[4];
                char        pidbuf[16];
                argv[0] = debugger;
                argv[1] = argv0;
                argv[2] = pidbuf;
                argv[3] = NULL;
                snprintf(pidbuf, sizeof pidbuf, "%i", getppid());
                execvp(debugger, (void *)argv);
                exit(1);
        }
}

/* @ht */

static int ht_init(struct ht *ht, int shift) {
        ht->shift       = shift;
        ht->buckets     = mem_alloc_align(sizeof ht->buckets[0]     << shift, MAX_CACHELINE);
        ht->bucketlocks = mem_alloc_align(sizeof ht->bucketlocks[0] << shift, MAX_CACHELINE);
        if (ht->buckets != NULL && ht->bucketlocks != NULL) {
                for (int i = 0; i < (1 << shift); ++i) {
                        NOFAIL(pthread_mutex_init(&ht->bucketlocks[i].lock, NULL));
                }
                return 0;
        }
        mem_free(ht->buckets);
        mem_free(ht->bucketlocks);
        return ERROR(-ENOMEM);
}

static void ht_fini(struct ht *ht) {
        for (int i = 0; i < (1 << ht->shift); i++) {
                NOFAIL(pthread_mutex_destroy(&ht->bucketlocks[i].lock));
                ASSERT(ht->buckets[i].chain.next == NULL);
        }
        mem_free(ht->buckets);
        mem_free(ht->bucketlocks);
}

static void ht_clean(struct ht *ht) {
        for (int i = 0; i < (1 << ht->shift); i++) {
                struct cds_hlist_head *head = &ht->buckets[i].chain;
                struct node           *scan;
                struct node           *next;
                mutex_lock(&ht->bucketlocks[i].lock);
                cds_hlist_for_each_entry_safe_2(scan, next, head, hash) {
                        ht_delete(scan);
                        nfini(scan);
                }
                mutex_unlock(&ht->bucketlocks[i].lock);
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

static uint32_t ht_bucket(struct ht *ht, taddr_t addr) {
       return ht_hash(addr) & ((1 << ht->shift) - 1);
}

static struct cds_hlist_head *ht_head(struct ht *ht, uint32_t bucket) {
        return &ht->buckets[bucket].chain;
}

static pthread_mutex_t *ht_lock(struct ht *ht, uint32_t bucket) {
        return &ht->bucketlocks[bucket].lock;
}

static struct node *ht_lookup(struct ht *ht, taddr_t addr, uint32_t bucket) {
        struct cds_hlist_head *head = ht_head(ht, bucket);
        struct cds_hlist_node *scan = rcu_dereference(head)->next;
        struct node           *n;
#define CHAINLINK do {                                                    \
        n = COF(scan, struct node, hash);                                 \
        if (LIKELY(n->addr == addr && (n->flags & HEARD_BANSHEE) == 0)) { \
                __builtin_prefetch(n->data);                              \
                CINC(chain);                                              \
                return n;                                                 \
        }                                                                 \
        scan = rcu_dereference(scan->next);                               \
        if (LIKELY(scan == NULL)) {                                       \
                return NULL;                                              \
        }                                                                 \
} while (0)
        if (scan != NULL) {
                CHAINLINK;
                CHAINLINK;
                CHAINLINK;
                CHAINLINK;
                while (true) {
                        CHAINLINK;
                }
        } else {
                return NULL;
        }
#undef CHAINLINK
}

static void ht_insert(struct ht *ht, struct node *n, uint32_t bucket) {
        cds_hlist_add_head_rcu(&n->hash, ht_head(ht, bucket));
}

static void ht_delete(struct node *n) {
        cds_hlist_del_rcu(&n->hash);
}

/* @pool */

static void pool_clean(struct t2 *mod) {
        for (int i = 0; i < ARRAY_SIZE(mod->cache.pool.free); ++i) {
                struct freelist *free = &mod->cache.pool.free[i];
                mutex_lock(&free->lock);
                while (!cds_list_empty(&free->head)) {
                        struct node *n = COF(free->head.next, struct node, cache);
                        cds_list_del(&n->cache);
                        NOFAIL(pthread_rwlock_destroy(&n->lock));
                        mem_free(n->radix);
                        mem_free(n->data);
                        mem_free(n);
                }
                mutex_unlock(&free->lock);
        }
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

static uint64_t kavg(struct ewma *a, uint32_t t) { /* Typical unit: quarter of nano-Kelvin (of nabi-Kelvin, technically). */
        return ((uint64_t)kval(a) << (63 - BOLT_EPOCH_SHIFT)) >> (t - a->cur);
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
        return memcmp(b0->seg[0].addr, b1->seg[0].addr, min_32(len0, len1)) ?: int32_cmp(len0, len1);
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

static int32_t buf_prefix(const struct t2_buf *dst, const struct t2_buf *src) {
        int32_t i;
        int32_t len = min_32(dst->nr, src->nr) > 0 ? min_32(dst->seg[0].len, src->seg[0].len) : 0;
        ASSERT(dst->nr <= 1);
        ASSERT(src->nr <= 1);
        for (i = 0; i < len; ++i) {
                if (((char *)dst->seg[0].addr)[i] != ((char *)src->seg[0].addr)[i]) {
                        break;
                }
        }
        return i;

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
        int32_t       nr;
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

static bool scheck(struct sheader *sh, const struct t2_node_type *nt) {
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
        __builtin_prefetch((void *)sh + koff);
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

static int uint64_cmp(uint64_t a, uint64_t b) {
        return a < b ? -1 : a != b;
}

static bool simple_search(struct node *n, struct path *p, struct slot *out) {
        struct t2_rec  *rec   = p->rec;
        bool            found = false;
        struct sheader *sh    = simple_header(n);
        int             l     = -1;
        int             delta = nr(n) + 1;
        void           *kaddr = rec->key->seg[0].addr;
        int32_t         klen  = rec->key->seg[0].len;
        int             cmp   = -1;
        uint32_t        mask  = nsize(n) - 1;
        int32_t         span;
        uint8_t __attribute__((unused)) lev = level(n);
        ASSERT(rec->key->nr == 1);
        ASSERT((nsize(n) & mask) == 0);
        ASSERT(((uint64_t)sh & mask) == 0);
        EXPENSIVE_ASSERT(scheck(sh, n->ntype));
        CINC(l[lev].search);
        CMOD(l[lev].nr,          nr(n));
        CMOD(l[lev].free,        NCALL(n, free(n)));
        CMOD(l[lev].modified,    !!(n->flags & DIRTY));
        DMOD(l[lev].temperature, (float)temperature(n) / (1ull << (63 - BOLT_EPOCH_SHIFT + (n->addr & TADDR_SIZE_MASK))));
        if (UNLIKELY(nr(n) == 0)) {
                goto here;
        } else if (LIKELY(n->radix != NULL)) {
                int16_t ch;
                int32_t plen = n->radix->prefix.seg[0].len;
                cmp = memcmp(n->radix->prefix.seg[0].addr, kaddr, min_32(plen, klen)) ?: klen < plen ? +1 : 0;
                if (UNLIKELY(cmp != 0)) {
                        l = cmp > 0 ? -1 : nr(n) - 1;
                        goto here;
                }
                ch = LIKELY(klen > plen) ? ((uint8_t *)kaddr)[plen] : -1;
                l     = n->radix->idx[ch].l;
                delta = n->radix->idx[ch].delta;
                CMOD(l[lev].radixmap_left,  l + 1);
                CMOD(l[lev].radixmap_right, nr(n) - l - delta);
                if (UNLIKELY(l < 0)) {
                        goto here;
                }
                cmp = skeycmp(sh, l, kaddr, klen, mask);
                if (cmp > 0) {
                        l--;
                } else if (cmp == 0) {
                        found = true;
                        goto here;
                }
                l = max_32(min_32(nr(n) - 1, l), -1);
                delta = min_32(delta, nr(n) - l);
        }
        CMOD(l[lev].search_span, delta);
        span = 1 << ilog2(delta);
        if (span != delta && skeycmp(sh, l + span, kaddr, klen, mask) <= 0) {
                l += delta - span;
        }
#define RANGE(x, prefetchp)                                                  \
        case 1 << (x):                                                       \
                span >>= 1;                                                  \
                if (prefetchp) {                                             \
                        __builtin_prefetch(sat(sh, l + span + (span >> 1))); \
                        __builtin_prefetch(sat(sh, l + span - (span >> 1))); \
                }                                                            \
                cmp = skeycmp(sh, l + span, kaddr, klen, mask);              \
                if (cmp <= 0) {                                              \
                        l += span;                                           \
                        if (cmp == 0) {                                      \
                                found = true;                                \
                                goto here;                                   \
                        }                                                    \
                }                                                            \
                __attribute__((fallthrough));
        switch (span) {
        default:
                IMMANENTISE("Impossible span: %i.", span);
                RANGE(16,  true)
                RANGE(15,  true)
                RANGE(14,  true)
                RANGE(13,  true)
                RANGE(12,  true)
                RANGE(11,  true)
                RANGE(10,  true)
                RANGE( 9,  true)
                RANGE( 8,  true)
                RANGE( 7,  true)
                RANGE( 6,  true)
                RANGE( 5,  true)
                RANGE( 4, false)
                RANGE( 3, false)
                RANGE( 2, false)
                RANGE( 1, false)
        case 1:
                ;
        }
#undef RANGE
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
                CMOD(l[lev].keysize, key->seg[0].len);
                CMOD(l[lev].valsize, key->seg[0].len);
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

static taddr_t internal_search(struct node *n, struct path *p, int32_t *pos) {
        SLOT_DEFINE(s, n);
        COUNTERS_ASSERT(CVAL(rcu) > 0);
        SET0(s.rec.key);
        SET0(s.rec.val);
        s.rec.key->nr = 1;
        s.rec.val->nr = 1;
        (void)NCALL(n, search(n, p, &s));
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

static int leaf_search(struct node *n, struct path *p, struct slot *s) {
        bool found;
        s->rec.key->nr = 1;
        s->rec.val->nr = 1;
        found = NCALL(n, search(n, p, s));
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
                __builtin_prefetch(prev - 1);
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

static int simple_load(struct node *n) {
        return 0;
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
        return NCALL(d, insert(&dst)) ?: (NCALL(s, delete(&src)), 0);
}

static int shift(struct node *d, struct node *s, const struct slot *point, enum dir dir) {
        int result = 0;
        ASSERT(dir == LEFT || dir == RIGHT);
        ASSERT(point->idx >= 0 && point->idx <= nr(s));
        ASSERT(NCALL(d, free(d)) > NCALL(s, free(s)));
        ASSERT(4 * rec_len(&point->rec) < min_32(nsize(d), nsize(s)));
        CINC(l[level(d)].shift);
        while (LIKELY(result == 0)) {
                SLOT_DEFINE(slot, s);
                rec_get(&slot, utmost(s, dir));
                if (NCALL(d, free(d)) - NCALL(s, free(s)) > rec_len(&slot.rec)) {
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

static int simple_keycmp(const struct node *n, int pos, void *addr, int32_t len, uint64_t mask) {
        return skeycmp(simple_header(n), pos, addr, len, mask);
}

static struct node_type_ops simple_ops = {
        .insert     = &simple_insert,
        .delete     = &simple_delete,
        .get        = &simple_get,
        .make       = &simple_make,
        .print      = &simple_print,
        .search     = &simple_search,
        .can_merge  = &simple_can_merge,
        .can_insert = &simple_can_insert,
        .nr         = &simple_nr,
        .free       = &simple_free,
        .used       = &simple_used,
        .keycmp     = &simple_keycmp
};

#if UT || BN

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
                NOFAIL(pthread_mutex_destroy(&fs->lock));
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
                return -ESTALE;
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

/* non-static */ struct t2_storage *bn_storage = &file_storage.gen;
taddr_t bn_tree_root(const struct t2_tree *t) {
        return t->root;
}

uint64_t bn_file_free(struct t2_storage *storage) {
        struct file_storage *fs = COF(storage, struct file_storage, gen);
        return fs->free;
}

void bn_file_free_set(struct t2_storage *storage, uint64_t free) {
        struct file_storage *fs = COF(storage, struct file_storage, gen);
        fs->free = free;
}

uint64_t bn_bolt(const struct t2 *mod) {
        return mod->cache.bolt;
}

void bn_bolt_set(struct t2 *mod, uint64_t bolt) {
        mod->cache.bolt = bolt;
}

void bn_counters_print(void) {
        counters_print();
        counters_clear();
}

void bn_counters_fold(void) {
        counters_fold();
}

#endif /* UT || BN */

/* @ut */

#if UT

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
                radixmap_update(s->node);
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

static struct t2_node_type ntype = {
        .id    = 8,
        .name  = "simple-ut",
        .shift = 9
};

static struct t2_node_type *tree_ntype(struct t2_tree *t, int level) {
        return &ntype;
}

static struct t2_tree_type ttype = {
        .id       = 7,
        .name     = "tree-type-ut",
        .ntype    = &tree_ntype
};

static void simple_ut() {
        struct t2 mod = {};
        struct node n = {
                .ntype = &ntype,
                .addr  = taddr_make(0x100000, ntype.shift),
                .data  = mem_alloc_align(1ul << ntype.shift, 1ul << ntype.shift),
                .seq   = 1,
                .mod   = &mod
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
        radixmap_update(&n);
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
                radixmap_update(&n);
                ASSERT(sh->nr == i);
        }
        s.idx = 0;
        while (nr(&n) > 0) {
                simple_delete(&s);
                radixmap_update(&n);
        }
        utest("search");
        key0[1] = 'a';
        while (simple_free(&n) > buf_len(&key) + buf_len(&val) + SOF(struct dir_element)) {
                struct path p = { .rec = &s.rec };
                result = simple_search(&n, &p, &s);
                ASSERT(!result);
                ASSERT(-1 <= s.idx && s.idx < nr(&n));
                s.idx++;
                key = BUF_VAL(key0);
                val = BUF_VAL(val0);
                NOFAIL(simple_insert(&s));
                radixmap_update(&n);
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
                struct node *n = node_alloc_ut(&mod, ht_hash(i));
                ht_insert(&mod.ht, n, ht_bucket(&mod.ht, n->addr));
        }
        utest("lookup");
        for (uint64_t i = 0; i < N; ++i) {
                taddr_t blk = taddr_make(ht_hash(i) & TADDR_ADDR_MASK, 9);
                struct node *n = ht_lookup(&mod.ht, blk, ht_bucket(&mod.ht, blk));
                ASSERT(n != NULL);
                ASSERT(n->addr == blk);
        }
        utest("delete");
        for (uint64_t i = 0; i < N; ++i) {
                taddr_t blk = taddr_make(ht_hash(i) & TADDR_ADDR_MASK, 9);
                struct node *n = ht_lookup(&mod.ht, blk, ht_bucket(&mod.ht, blk));
                ht_delete(n);
        }
        utest("fini");
        ht_fini(&mod.ht);
        utestdone();
}

enum {
        HT_SHIFT = 20,
        CA_SHIFT = 20
};

static void traverse_ut() {
        taddr_t addr = taddr_make(0x100000, ntype.shift);
        struct node n = {
                .ntype = &ntype,
                .addr  = addr,
                .data  = mem_alloc_align(1ul << ntype.shift, 1ul << ntype.shift),
                .seq   = 1
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
        struct t2 *mod = t2_init(ut_storage, HT_SHIFT, CA_SHIFT);
        t2_node_type_register(mod, &ntype);
        ttype.mod = mod;
        buf_init_str(&key, key0);
        buf_init_str(&val, val0);
        n.mod = mod;
        utest("prepare");
        simple_make(&n);
        ht_insert(&mod->ht, &n, ht_bucket(&mod->ht, n.addr));
        for (int i = 0; i < 20; ++i, key0[0] += 2) {
                struct path p = { .rec = &s.rec };
                result = simple_search(&n, &p, &s);
                ASSERT(!result);
                s.idx++;
                buf_init_str(&key, key0);
                buf_init_str(&val, val0);
                NOFAIL(simple_insert(&s));
                radixmap_update(&n);
                ASSERT(is_sorted(&n));
        }
        n.seq = 2;
        utest("existing");
        key0[0] = '0';
        p.used = -1;
        NOFAIL(traverse(&p));
        key0[0] = '2';
        p.used = -1;
        NOFAIL(traverse(&p));
        key0[0] = '8';
        p.used = -1;
        NOFAIL(traverse(&p));
        utest("too-small");
        key0[0] = ' ';
        p.used = -1;
        result = traverse(&p);
        ASSERT(result == -ENOENT);
        utest("non-existent");
        key0[0] = '1';
        p.used = -1;
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
        struct t2 *mod = t2_init(ut_storage, HT_SHIFT, CA_SHIFT);
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
        mod = t2_init(ut_storage, HT_SHIFT, CA_SHIFT);
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
        mod = t2_init(ut_storage, HT_SHIFT, CA_SHIFT);
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
                        keyb.seg[0] = (struct t2_seg){ .len = ksize, .addr = &key };
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
                keyb.seg[0] = (struct t2_seg){ .len = ksize,    .addr = &key };
                valb.seg[0] = (struct t2_seg){ .len = SOF(val), .addr = &val };
                NOFAIL(t2_lookup(t, &r));
        }
        utest("rand");
        U *= 1;
        for (int i = 0; i < U; ++i) {
                ksize = rand() % (maxsize - 1) + 1;
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
        mod = t2_init(ut_storage, HT_SHIFT, CA_SHIFT);
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
                ksize = rand() % maxsize + (ht_hash(i) & 1) + 1; /* Beat prng cycles. */
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
        mod = t2_init(ut_storage, HT_SHIFT, CA_SHIFT);
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
        usuite("cookie");
        utest("init");
        NOFAIL(signal_init());
        cookie_make(&v[0]);
        cookie_load(&v[0], &k);
        result = cookie_is_valid(&k);
        ASSERT(result);
        utest("addr-is-valid");
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
        result = addr_is_valid((void *)&edepth); /* TLS */
        ASSERT(result);
        result = addr_is_valid((void *)&cit);
        ASSERT(result);
        signal_fini();
        utest("stacktrace");
        LOG("Testing stacktrace.");
        stacktrace(); /* Test it here. */
        utestdone();
}

static void error_ut() {
        usuite("error");
        utest("macros");
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
        utestdone();
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
        mod = t2_init(ut_storage, HT_SHIFT, CA_SHIFT);
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
        utest("ilog2");
        ASSERT(ilog2  (0) == -1);
        ASSERT(ilog2  (1) ==  0);
        ASSERT(ilog2  (2) ==  1);
        ASSERT(ilog2  (3) ==  1);
        ASSERT(ilog2  (4) ==  2);
        ASSERT(ilog2  (5) ==  2);
        ASSERT(ilog2  (8) ==  3);
        ASSERT(ilog2(256) ==  8);
        ASSERT(ilog2(257) ==  8);
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
        mod = t2_init(ut_storage, HT_SHIFT, CA_SHIFT);
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

static void open_ut() {
        struct t2      *mod;
        struct t2_tree *t;
        pthread_t tid[4*THREADS];
        char kbuf[8];
        char vbuf[MAXSIZE];
        int32_t ksize;
        int32_t vsize;
        int     result;
        taddr_t root;
        uint64_t free;
        uint64_t bolt;
        usuite("open");
        utest("populate");
        mod = t2_init(ut_storage, HT_SHIFT, CA_SHIFT);
        ASSERT(EISOK(mod));
        ttype.mod = NULL;
        t2_tree_type_register(mod, &ttype);
        t2_node_type_register(mod, &ntype);
        t = t2_tree_create(&ttype);
        ASSERT(EISOK(t));
        for (long i = 0; i < 4*OPS; ++i) {
                random_buf(kbuf, sizeof kbuf, &ksize);
                random_buf(vbuf, sizeof vbuf, &vsize);
                result = t2_insert_ptr(t, kbuf, ksize, vbuf, vsize);
                ASSERT(result == 0 || result == -EEXIST);
        }
        root = t->root;
        free = file_storage.free;
        bolt = mod->cache.bolt;
        t2_tree_close(t);
        t2_tree_type_degister(&ttype);
        t2_node_type_degister(&ntype);
        t2_fini(mod);
        utest("open");
        mod = t2_init(ut_storage, HT_SHIFT, CA_SHIFT);
        ASSERT(EISOK(mod));
        ttype.mod = NULL;
        t2_tree_type_register(mod, &ttype);
        t2_node_type_register(mod, &ntype);
        file_storage.free = free;
        mod->cache.bolt = bolt;
        t = t2_tree_open(&ttype, root);
        ASSERT(EISOK(t));
        utest("ops");
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
        argv0 = argv[0];
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
        open_ut();
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
 * + decaying node temperature (see bits/avg.c)
 *
 * + cache replacement (arc, clock?)
 *
 * + replace cookie with get(), benchmark (sigprocmask is expensive).
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
