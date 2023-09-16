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
#include <sys/stat.h>
#include <sys/uio.h>
#include <sys/time.h>
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

#if !defined(TRANSACTIONS)
#define TRANSACTIONS (1)
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

#define BUF_VAL(v) (struct t2_buf){ .len = SOF(v), .addr = &(v) }

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

#define DEFAULT_TE (1)

#define TXDO(te, val) ((te) != NULL ? (val) : ((typeof(val))0))

#if TRANSACTIONS
#if DEFAULT_TE
#define TXCALL(te, ...) TXDO(te, wal_ ## __VA_ARGS__)
#else
#define TXCALL(te, ...) TXDO(te, (te)-> __VA_ARGS__)
#endif
#else
#define TXCALL(te, ...) TXDO(NULL, (te)-> __VA_ARGS__)
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
struct mod;

struct node_type_ops {
        int     (*insert)    (struct slot *, struct mod *);
        void    (*delete)    (struct slot *, struct mod *);
        void    (*get)       (struct slot *);
        int     (*load)      (struct node *n);
        void    (*make)      (struct node *n);
        void    (*print)     (struct node *n);
        void    (*fini)      (const struct node *n);
        bool    (*search)    (struct node *n, struct path *p, struct slot *out);
        bool    (*can_merge) (const struct node *n0, const struct node *n1);
        int     (*can_insert)(const struct slot *s);
        int32_t (*nr)        (const struct node *n);
        int32_t (*free)      (const struct node *n);
        int32_t (*used)      (const struct node *n);
};

struct t2 {
        alignas(MAX_CACHELINE) struct ht         ht;
        alignas(MAX_CACHELINE) struct cache      cache;
        const struct t2_tree_type               *ttypes[MAX_TREE_TYPE];
        const struct t2_node_type               *ntypes[MAX_NODE_TYPE];
        struct t2_storage                       *stor;
        struct t2_te                            *te;
        bool                                     shutdown;
};

SASSERT(MAX_TREE_HEIGHT <= 255); /* Level is 8 bit. */

struct t2_tree {
        struct t2_tree_type *ttype;
        taddr_t              root;
        uint32_t             id;
};

struct page;

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
        uint32_t      utmost;
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

enum ext_id {
        HDR,
        KEY,
        VAL,
        DIR,

        M_NR
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
        lsn_t                      lsn;
        uint64_t                   cookie;
        pthread_rwlock_t           lock;
        struct rcu_head            rcu;
};

enum lock_mode {
        NONE,
        READ,
        WRITE
};

struct ext {
        int32_t start;
        int32_t end;
};

struct mod {
        struct ext ext[M_NR];
};

struct page {
        struct node    *node;
        uint64_t        seq;
        enum lock_mode  lm;
        struct mod      mod;
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
        struct page    page;
        uint64_t       flags;
        int32_t        pos;
        struct page    allocated;
        struct page    brother[2];
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
        struct t2_tx   *tx;
        struct page     newroot;
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
        int64_t wal_space;
        int64_t wal_write;
        int64_t wal_write_sync;
        int64_t wal_cur_aged;
        int64_t wal_get_ready;
        int64_t wal_get_wait;
        int64_t wal_get_wait_time;
        struct counter_var wal_space_nr;
        struct counter_var wal_space_nob;
        struct counter_var wal_write_seg;
        struct counter_var wal_write_nob;
        struct counter_var wal_busy;
        struct counter_var wal_ready;
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
                struct counter_var pageout_cluster;
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
static uint64_t now(void);
static int32_t max_32(int32_t a, int32_t b);
static int32_t min_32(int32_t a, int32_t b);
static int ilog2(uint32_t x);
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
static struct node *look(struct t2 *mod, taddr_t addr);
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
static void touch_unlock(struct node *n, enum lock_mode mode);
static void dirty(struct page *g);
static void radixmap_update(struct node *n);
static struct header *nheader(const struct node *n);
static void rcu_lock();
static void rcu_unlock();
static void rcu_leave(struct path *p, struct node *extra);
static bool rcu_try(struct path *p, struct node *extra);
static bool rcu_enter(struct path *p, struct node *extra);
static int simple_insert(struct slot *s, struct mod *mod);
static void simple_delete(struct slot *s, struct mod *mod);
static void simple_get(struct slot *s);
static void simple_make(struct node *n);
static int simple_load(struct node *n);
static bool simple_search(struct node *n, struct path *p, struct slot *out);
static int32_t simple_nr(const struct node *n);
static int32_t simple_free(const struct node *n);
static int simple_can_insert(const struct slot *s);
static int32_t simple_used(const struct node *n);
static bool simple_can_merge(const struct node *n0, const struct node *n1);
static void simple_fini(struct node *n);
static void simple_print(struct node *n);
static bool simple_invariant(const struct node *n);
static int simple_keycmp(const struct node *n, int pos, void *addr, int32_t len, uint64_t mask);
static void range_print(void *orig, int32_t nsize, void *start, int32_t nob);
static int shift(struct page *d, struct page *s, const struct slot *insert, enum dir dir);
static int merge(struct page *d, struct page *s, enum dir dir);
static struct t2_buf *ptr_buf(struct node *n, struct t2_buf *b);
static struct t2_buf *addr_buf(taddr_t *addr, struct t2_buf *b);
static struct t2_tx *wal_make(struct t2_te *te);
static int  wal_init   (struct t2_te *engine, struct t2 *mod);
static void wal_fini   (struct t2_te *engine);
static int  wal_diff   (struct t2_te *engine, struct t2_tx *trax, int32_t nob, int nr, struct t2_txrec *txr, int32_t rtype);
static int  wal_ante   (struct t2_te *engine, struct t2_tx *trax, int32_t nob, int nr, struct t2_txrec *txr);
static int  wal_post   (struct t2_te *engine, struct t2_tx *trax, int32_t nob, int nr, struct t2_txrec *txr);
static int  wal_open   (struct t2_te *engine, struct t2_tx *trax);
static void wal_close  (struct t2_te *engine, struct t2_tx *trax);
static int  wal_wait   (struct t2_te *engine, struct t2_tx *trax, const struct timespec *deadline, bool force);
static void wal_done   (struct t2_te *engine, struct t2_tx *trax);
static bool wal_canpage(struct t2_te *engine, struct t2_node *n);
static void wal_dirty  (struct t2_te *engine, lsn_t lsn);
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
static int insert(struct t2_tree *t, struct t2_rec *r, struct t2_tx *tx);
static int delete(struct t2_tree *t, struct t2_rec *r, struct t2_tx *tx);
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
static void cache_fini(struct t2 *mod);
static void cache_sync(struct t2 *mod);
static void throttle(struct t2 *mod);
static void kmod(struct ewma *a, uint32_t t);
static uint64_t kavg(struct ewma *a, uint32_t t);
static void ref_add(struct node *n);
static void ref_del(struct node *n);
static void ref_print(void);
static int cds_list_length(const struct cds_list_head *head);

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

struct t2 *t2_init(struct t2_storage *storage, struct t2_te *te, int hshift, int cshift) {
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
                                        if (LIKELY(result == 0)) {
                                                result = TXCALL(te, init(te, mod));
                                                if (result == 0) {
                                                        mod->te = te;
                                                } else {
                                                        cache_fini(mod);
                                                }
                                        }
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
        cache_fini(mod);
        SCALL(mod, fini);
        cache_clean(mod);
        ht_clean(&mod->ht);
        ht_fini(&mod->ht);
        ASSERT(cds_list_empty(&mod->cache.cold));
        mod->stor->op->fini(mod->stor);
        if (mod->te != NULL) {
                TXCALL(mod->te, fini(mod->te));
        }
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

static int taddr_sshift(taddr_t addr) {
        return (addr & TADDR_SIZE_MASK) + TADDR_MIN_SHIFT;
}

static int taddr_ssize(taddr_t addr) {
        return 1 << taddr_sshift(addr);
}

static taddr_t taddr_make(uint64_t addr, int shift) {
        ASSERT((addr & TADDR_ADDR_MASK) == addr);
        shift -= TADDR_MIN_SHIFT;
        ASSERT((shift & TADDR_SIZE_MASK) == (uint64_t)shift);
        return addr | shift;
}

static uint64_t zerodata = 0;
static struct t2_buf zero = { .len = 0, .addr = &zerodata };

struct t2_tree *t2_tree_create(struct t2_tree_type *ttype, struct t2_tx *tx) {
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
                        result = insert(t, &(struct t2_rec) { .key = &zero, .val = &zero }, tx);
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

static int rec_insert(struct node *n, int32_t idx, struct t2_rec *r, struct mod *mod) {
        CMOD(l[level(n)].recpos, 100 * idx / (nr(n) + 1));
        return NCALL(n, insert(&(struct slot) { .node = n, .idx = idx, .rec  = *r }, mod));
}

static void rec_delete(struct node *n, int32_t idx, struct mod *mod) {
        NCALL(n, delete(&(struct slot) { .node = n, .idx = idx }, mod));
}

static void rec_get(struct slot *s, int32_t idx) {
        s->idx = idx;
        NCALL(s->node, get(s));
}

static int cookie_node_complete(struct t2_tree *t, struct path *p, struct node *n, enum optype opt) {
        struct t2_rec *r = p->rec;
        int            result;
        bool           found;
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
                        result = rec_insert(n, s.idx + 1, r, NULL); /* TODO: Update modification tracking. */
                        if (result == -ENOSPC) {
                                result = -ESTALE;
                        }
                } else {
                        result = -EEXIST;
                }
                break;
        case DELETE:
                if (found) {
                        if (keep(n)) {
                                rec_delete(n, s.idx, NULL);
                                result = 0;
                        } else {
                                result = -ESTALE;
                        }
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
                                /* TODO: Re-check node. */
                                result = cookie_node_complete(p->tree, p, n, p->opt);
                                if (result == 0) {
                                        dirty(NULL); /* TODO: Modification tracking. */
                                        /* TODO: Add to the transaction. */
                                }
                                touch_unlock(n, mode);
                                put(n);
                                return result;
                        } else {
                                touch_unlock(n, mode);
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

static void touch_unlock(struct node *n, enum lock_mode mode) {
        touch(n);
        unlock(n, mode);
}

static struct node *peek(struct t2 *mod, taddr_t addr) {
        CINC(peek);
        return ht_lookup(&mod->ht, addr, ht_bucket(&mod->ht, addr));
}

static struct node *look(struct t2 *mod, taddr_t addr) {
        uint32_t         bucket = ht_bucket(&mod->ht, addr);
        pthread_mutex_t *lock   = ht_lock(&mod->ht, bucket);
        struct node     *n;
        mutex_lock(lock);
        n = ht_lookup(&mod->ht, addr, bucket);
        if (n != NULL) {
                ref(n);
        }
        mutex_unlock(lock);
        return n;
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
        NCALL(n, fini(n));
        cookie_invalidate(&n->cookie);
        n->seq   = 0;
        n->flags = 0;
        n->ntype = NULL;
        n->addr  = 0;
        if (n->radix != NULL) {
                n->radix->prefix.len = -1;
        }
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
                        struct iovec io     = { .iov_base = n->data, .iov_len = taddr_ssize(addr) };
                        int          result = SCALL(n->mod, read, n->addr, 1, &io);
                        if (LIKELY(result == 0)) {
                                struct header *h = nheader(n);
                                /* TODO: check node. */
                                if (LIKELY(IS_IN(h->ntype, n->mod->ntypes) && n->mod->ntypes[h->ntype] != NULL &&
                                           n->mod->ntypes[h->ntype]->shift == taddr_sshift(addr))) {
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
                n->radix->prefix.addr = &n->radix->pbuf[0];
        }
        m = n->radix;
        CINC(l[level(n)].radixmap_updated);
        if (LIKELY(nr(n) > 1)) {
                if (m->utmost || m->prefix.len == -1) {
                        struct t2_buf l;
                        struct t2_buf r;
                        rec_get(&s, 0);
                        l = *s.rec.key;
                        rec_get(&s, nr(n) - 1);
                        r = *s.rec.key;
                        plen = min_32(buf_prefix(&l, &r), ARRAY_SIZE(m->pbuf));
                        memcpy(m->prefix.addr, l.addr, plen);
                        m->prefix.len = plen;
                        m->utmost = 0;
                } else {
                        plen = m->prefix.len;
                }
        } else {
                plen = m->prefix.len = 0;
        }
        CMOD(l[level(n)].prefix, plen);
        for (i = 0; i < nr(n); ++i) {
                rec_get(&s, i);
                if (LIKELY(s.rec.key->len > plen)) {
                        ch = ((uint8_t *)s.rec.key->addr)[plen];
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
        if (USE_PREFIX_SEPARATORS) {
                int i;
                for (i = 0; i < MAX_SEPARATOR_CUT; ++i) {
                        r->len--;
                        if (buf_cmp(l, r) >= 0) {
                                ++r->len;
                                break;
                        }
                }
                CMOD(l[level].sepcut, i);
        }
        return r->len;
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
        SLOT_DEFINE(s, r->page.node);
        int32_t       maxlen;
        int32_t       keylen;
        ASSERT(nr(r->page.node) > 0);
        ASSERT(r->allocated.node != NULL);
        rec_todo(p, idx, &s);
        maxlen = buf_len(s.rec.key);
        r->keyout = *s.rec.key;
        for (int32_t i = 0; i < nr(r->page.node); ++i) {
                rec_get(&s, i);
                buf_clip_node(s.rec.key, r->page.node);
                keylen = buf_len(s.rec.key);
                if (keylen > maxlen) {
                        maxlen = keylen;
                        r->keyout = *s.rec.key;
                }
        }
        ptr_buf(r->allocated.node, &r->valout);
}

static int newnode(struct path *p, int idx) {
       struct rung *r = &p->rung[idx];
       if (r->allocated.node == NULL) {
               r->allocated.node = alloc(p->tree, level(r->page.node));
               if (EISERR(r->allocated.node)) {
                       return ERROR(ERRCODE(r->allocated.node));
               }
               r->allocated.lm = WRITE;
       }
       if (idx == 0) { /* Hodie natus est radici frater. */
               if (LIKELY(p->used + 1 < MAX_TREE_HEIGHT)) {
                       p->newroot.node = alloc(p->tree, level(r->page.node) + 1);
                       if (EISERR(r->allocated.node)) {
                               return ERROR(ERRCODE(p->newroot.node));
                       } else {
                               p->newroot.lm = WRITE;
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
        struct node *left = r->page.node;
        struct node *right = r->allocated.node;
        SLOT_DEFINE(s, NULL);
        int result = 0;
        rec_todo(p, idx, &s);
        /* Maybe ->plan() overestimated keysize and shift is not needed. */
        if (right != NULL && !can_insert(left, &s.rec)) {
                s.idx = r->pos + 1;
                result = shift(&r->allocated, &r->page, &s, RIGHT);
                ASSERT(nr(left) > 0);
                ASSERT(nr(right) > 0);
                r->flags |= ALUSED;
        }
        if (LIKELY(result == 0)) {
                struct page *p;
                if (r->pos < nr(left)) {
                        s.node = left;
                        s.idx  = r->pos;
                        p = &r->page;
                } else {
                        ASSERT(right != NULL);
                        s.node = right;
                        s.idx  = r->pos - nr(left);
                        p = &r->allocated;
                }
                s.idx++;
                ASSERT(s.idx <= nr(s.node));
                NOFAIL(NCALL(s.node, insert(&s, &p->mod)));
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

static struct page *brother(struct rung *r, enum dir d) {
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

static void delete_update(struct path *p, int idx, struct slot *s, struct page *g) {
        ASSERT(idx < p->used);
        ASSERT(g->node == s->node);
        NCALL(s->node, delete(s, &g->mod));
        if (p->rung[idx + 1].flags & SEPCHG) {
                struct node  *child = brother(&p->rung[idx + 1], RIGHT)->node;
                struct t2_buf cptr;
                SLOT_DEFINE(sub, child);
                {       /* A new scope for the second SLOT_DEFINE(). */
                        SLOT_DEFINE(leaf, p->rung[p->used].page.node);
                        ASSERT(child != NULL && !is_leaf(child));
                        rec_get(&sub, 0);
                        *s->rec.key = *sub.rec.key;
                        *s->rec.val = *ptr_buf(child, &cptr);
                        /* Take the rightmost key in the leaf. */
                        rec_get(&leaf, nr(leaf.node) - 1);
                        prefix_separator(leaf.rec.key, s->rec.key, level(s->node));
                        NOFAIL(NCALL(s->node, insert(s, &g->mod)));
                }
        }
}

static bool utmost_path(struct path *p, int idx, enum dir d) {
        return FORALL(i, idx, p->rung[i].page.lm == WRITE ? p->rung[i].pos == utmost(p->rung[i].page.node, d) : true);
}

static int split_right_exec_delete(struct path *p, int idx) {
        int result = 0;
        struct rung *r = &p->rung[idx];
        struct node *right = brother(r, RIGHT)->node;
        SLOT_DEFINE(s, r->page.node);
        if (!is_leaf(r->page.node)) {
                if (UNLIKELY(nr(p->rung[idx + 1].page.node) == 0)) { /* Rightmost in the tree. */
                        ASSERT(utmost_path(p, idx, RIGHT));
                        s.idx = r->pos;
                        NCALL(s.node, delete(&s, &r->page.mod));
                } else if (r->pos + 1 < nr(r->page.node)) {
                        s.idx = r->pos + 1;
                        delete_update(p, idx, &s, &r->page);
                } else {
                        ASSERT(right != NULL);
                        s.node = right;
                        s.idx = 0;
                        delete_update(p, idx, &s, brother(r, RIGHT));
                        r->flags |= SEPCHG;
                        result = +1;
                }
        }
        if (right != NULL && can_merge(r->page.node, right)) {
                ASSERT(nr(right) > 0);
                NOFAIL(merge(&r->page, brother(r, RIGHT), LEFT)); /* TODO: deallocate the empty node. */
                ASSERT(nr(r->page.node) > 0);
                EXPENSIVE_ASSERT(is_sorted(r->page.node));
                r->flags &= ~SEPCHG;
                result = +1;
        } else if (UNLIKELY(nr(r->page.node) == 0)) {
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
                if (can_fit(left, r->page.node, right, NULL)) {
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

static void path_init(struct path *p, struct t2_tree *t, struct t2_rec *r, struct t2_tx *tx, enum optype opt) {
        SASSERT(NONE == 0);
        p->used = -1;
        p->tree = t;
        p->rec  = r;
        p->tx   = tx;
        p->opt  = opt;
}

static void dirty(struct page *g) {
        struct node *n = g->node;
        if (n != NULL && g->lm == WRITE) {
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
                dirty(&r->page);
                dirty(&r->brother[0]);
                dirty(&r->brother[1]);
                dirty(&r->allocated);
        }
        dirty(&p->newroot);
}

static void path_lock(struct path *p) {
        /* Top to bottom, left to right. */
        if (UNLIKELY(p->newroot.node != NULL)) {
                lock(p->newroot.node, WRITE);
        }
        for (int i = 0; i <= p->used; ++i) {
                struct rung *r = &p->rung[i];
                struct page *left  = brother(r, LEFT);
                struct page *right = brother(r, RIGHT);
                if (left->node != NULL) {
                        lock(left->node, left->lm);
                }
                lock(r->page.node, r->page.lm);
                if (right->node != NULL) {
                        lock(right->node, right->lm);
                }
                if (r->allocated.node != NULL) {
                        lock(r->allocated.node, WRITE);
                }
        }
}

static void path_fini(struct path *p) {
        for (; p->used >= 0; --p->used) {
                struct rung *r = &p->rung[p->used];
                struct page *left  = brother(r, LEFT);
                struct page *right = brother(r, RIGHT);
                if (UNLIKELY(right->node != NULL)) {
                        touch_unlock(right->node, right->lm);
                        put(right->node);
                }
                touch_unlock(r->page.node, r->page.lm);
                if (UNLIKELY(left->node != NULL)) {
                        touch_unlock(left->node, left->lm);
                        put(left->node);
                }
                if (r->flags & PINNED) {
                        put(r->page.node);
                }
                if (UNLIKELY(r->allocated.node != NULL)) {
                        touch_unlock(r->allocated.node, WRITE);
                        if (LIKELY(r->flags & ALUSED)) {
                                put(r->allocated.node);
                        } else {
                                dealloc(r->allocated.node);
                        }
                }
                buf_free(&r->scratch);
        }
        p->used = -1;
        if (UNLIKELY(p->newroot.node != NULL)) {
                touch_unlock(p->newroot.node, WRITE);
                put(p->newroot.node);
        }
}

static void path_reset(struct path *p) {
        path_fini(p);
        memset(&p->rung, 0, sizeof p->rung);
        SET0(&p->newroot.node);
        p->next = p->tree->root;
        CINC(traverse_restart);
}

static void path_pin(struct path *p) {
        for (int i = p->used; i >= 0; --i) {
                struct rung *r = &p->rung[i];
                if (!(r->flags & PINNED)) {
                        ref(r->page.node);
                        r->flags |= PINNED;
                }
        }
}

static int txadd(struct page *g, struct t2_txrec *txr, int32_t *nob) {
        struct node *n   = g->node;
        struct mod  *mod = &g->mod;
        int          pos = 0;
        if (n != NULL && g->lm == WRITE) {
                for (int i = 0; i < ARRAY_SIZE(mod->ext); ++i) {
                        if (mod->ext[i].end > mod->ext[i].start) {
                                txr[pos] = (struct t2_txrec) {
                                        .node = (void *)n,
                                        .addr = n->addr,
                                        .off  = mod->ext[i].start,
                                        .part = {
                                                .len  = mod->ext[i].end - mod->ext[i].start,
                                                .addr = n->data + mod->ext[i].start
                                        }
                                };
                                *nob += txr[pos].part.len;
                                pos++;
                        }
                }
        }
        return pos;
}

static void path_txadd(struct path *p) {
        if (TRANSACTIONS && p->tx != NULL) { /* TODO: Log node allocations and de-allocations. */
                struct t2_txrec txr[((p->used + 1) * 4 + 1) * M_NR]; /* VLA. */
                struct t2_te   *te  = p->tree->ttype->mod->te;
                int             pos = 0;
                int32_t         nob = 0;
                for (int i = 0; i <= p->used; ++i) {
                        struct rung *r = &p->rung[p->used];
                        pos += txadd(brother(r, LEFT),  &txr[pos], &nob);
                        pos += txadd(&r->page,          &txr[pos], &nob);
                        pos += txadd(brother(r, RIGHT), &txr[pos], &nob);
                        if (r->flags & ALUSED) {
                                pos += txadd(&r->allocated, &txr[pos], &nob);
                        }
                }
                pos += txadd(&p->newroot, &txr[pos], &nob);
                TXCALL(te, post(te, p->tx, nob, pos, txr));
        }
}

static bool rung_validity_invariant(const struct path *p, int i) {
        const struct rung *r    = &p->rung[i];
        const struct node *n    = r->page.node;
        const struct rung *prev = &p->rung[i - 1];
        return is_stable(n) &&
                (!is_leaf(n) ? r->pos < nr(n) : true) &&
                (i == 0 ? p->tree->root == n->addr :
                 (prev->page.lm != WRITE) || (n->addr == internal_get(prev->page.node, prev->pos) &&
                                         level(prev->page.node) == level(n) + 1)) &&
                (i == p->used) == is_leaf(n);
}

static bool rung_is_valid(const struct path *p, int i) {
        const struct rung *r        = &p->rung[i];
        struct page       *left     = brother((struct rung *)r, LEFT);
        struct page       *right    = brother((struct rung *)r, RIGHT);
        bool               is_valid = node_seq_is_valid(r->page.node, r->page.seq) &&
                (left->node  != NULL ? node_seq_is_valid(left->node,  left->seq)  : true) &&
                (right->node != NULL ? node_seq_is_valid(right->node, right->seq) : true);
        ASSERT(is_valid && r->page.lm == WRITE ? rung_validity_invariant(p, i) : true);
        return is_valid;
}

static void path_add(struct path *p, struct node *n, uint64_t flags) {
        struct rung *r = &p->rung[++p->used];
        ASSERT(IS_IN(p->used + 1, p->rung));
        r->page.node = n;
        r->page.seq  = node_seq(n);
        r->flags     = flags;
}

static bool path_is_valid(const struct path *p) {
        return p->rung[0].page.node->addr == p->tree->root && FORALL(i, p->used + 1, rung_is_valid(p, i));
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
        struct page    *br   = brother(r, d);
        int             i;
        if (br->node != NULL) {
                ASSERT(br->lm == mode);
                return br->node;
        }
        for (i = idx - 1; i >= 0; --i) {
                r = &p->rung[i];
                ASSERT(brother(r, d)->node == NULL);
                if (r->pos != utmost(r->page.node, d)) {
                        break;
                }
        }
        if (i < 0) {
                return NULL;
        }
        ASSERT(r->page.lm == NONE || r->page.lm == mode);
        r->page.lm = mode;
        down = internal_child(r->page.node, r->pos + d, false);
        while (down != NULL && EISOK(down)) {
                r = &p->rung[++i];
                ASSERT(r->page.lm == NONE || r->page.lm == mode);
                r->page.lm = mode;
                *brother(r, d) = (struct page) { .node = down, .lm = mode, .seq = node_seq(down) };
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
        SLOT_DEFINE(s, p->rung[idx].page.node);
        if (leaf_search(p->rung[idx].page.node, p, &s)) {
                return -EEXIST;
        }
        p->rung[idx].pos = s.idx;
        do {
                struct rung *r = &p->rung[idx];
                r->page.lm = WRITE;
                if (can_insert(r->page.node, rec) && !should_split(r->page.node)) {
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
        SLOT_DEFINE(s, p->rung[idx].page.node);
        if (!leaf_search(p->rung[idx].page.node, p, &s)) {
                return -ENOENT;
        }
        p->rung[idx].pos = s.idx;
        do {
                struct rung *r = &p->rung[idx];
                r->page.lm = WRITE;
                if (keep(r->page.node)) {
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
        SLOT_DEFINE(s, r->page.node);
        if (!leaf_search(r->page.node, p, &s) && (enum dir)c->dir == RIGHT) {
                s.idx++;
        }
        r->pos = s.idx;
        r->page.lm = READ;
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
        while (((int8_t *)b->addr)[b->len - 1] == 0) {
                b->len--;
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
        struct node  *oldroot = p->rung[0].page.node;
        struct t2_buf ptr;
        SLOT_DEFINE(s, oldroot);
        if (UNLIKELY(buf_len(&p->rung[0].keyout) == 0 && buf_len(&p->rung[0].valout) == 0)) {
                return 0; /* Nothing to do. */
        }
        rec_get(&s, 0);
        s.node = p->newroot.node;
        s.rec.val = ptr_buf(oldroot, &ptr);
        NOFAIL(NCALL(s.node, insert(&s, &p->newroot.mod)));
        s.idx = 1;
        ASSERT(p->rung[0].pd.id == SPLIT_RIGHT); /* For now. */
        s.rec.key = &p->rung[0].keyout;
        s.rec.val = &p->rung[0].valout;
        NOFAIL(NCALL(s.node, insert(&s, &p->newroot.mod)));
        p->rung[0].flags |= ALUSED;
        /* Barrier? */
        p->tree->root = p->newroot.node->addr;
        return 0;
}

static int insert_balance(struct path *p) {
        int idx;
        int result = 0;
        for (idx = p->used; idx >= 0; --idx) {
                struct rung *r = &p->rung[idx];
                ASSERT(r->page.lm == WRITE);
                CINC(l[level(r->page.node)].insert_balance);
                result = dispatch[r->pd.id].exec_insert(p, idx);
                if (result <= 0) {
                        break;
                }
                result = 0;
        }
        if (UNLIKELY(idx < 0 && LIKELY(result == 0))) {
                if (p->newroot.node != NULL) {
                        result = root_add(p); /* Move this to policy? */
                }
        }
        return result;
}

static int insert_complete(struct path *p, struct node *n) {
        struct rung *r = &p->rung[p->used];
        int result = rec_insert(n, r->pos + 1, p->rec, &r->page.mod);
        if (result == -ENOSPC) {
                result = insert_balance(p);
        }
        cookie_complete(p, n);
        path_txadd(p);
        return result;
}

static int delete_balance(struct path *p) {
        int idx;
        int result = 0;
        for (idx = p->used; idx >= 0; --idx) {
                struct rung *r = &p->rung[idx];
                ASSERT(r->page.lm == WRITE);
                CINC(l[level(r->page.node)].delete_balance);
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
        rec_delete(n, p->rung[p->used].pos, &p->rung[p->used].page.mod);
        if (!keep(n)) {
                result = delete_balance(p);
        }
        cookie_complete(p, n);
        path_txadd(p);
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
                        c->curkey.len = c->maxlen;
                        buf_copy(&c->curkey, s.rec.key);
                        c->curkey.len = keylen;
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
        result = EXISTS(i, p->used + 1, p->rung[i].page.node->flags & HEARD_BANSHEE) || (extra != NULL && (extra->flags & HEARD_BANSHEE));
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

static int traverse_result(struct t2_tree *t, struct t2_rec *r, struct t2_tx *tx, enum optype opt) {
        int         result;
        struct path p = {};
        counters_check();
        path_init(&p, t, r, tx, opt);
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
        return traverse_result(t, r, NULL, LOOKUP);
}

static int insert(struct t2_tree *t, struct t2_rec *r, struct t2_tx *tx) {
        return traverse_result(t, r, tx, INSERT);
}

static int delete(struct t2_tree *t, struct t2_rec *r, struct t2_tx *tx) {
        return traverse_result(t, r, tx, DELETE);
}

static int next(struct t2_cursor *c) {
        struct t2_buf val = {};
        struct t2_rec r = {
                .key = &c->curkey,
                .val = &val,
                .vcb = (void *)c /* Erm... */
        };
        return traverse_result(c->tree, &r, NULL, NEXT);
}

int t2_lookup(struct t2_tree *t, struct t2_rec *r) {
        ASSERT(thread_registered);
        eclear();
        return lookup(t, r);
}

int t2_delete(struct t2_tree *t, struct t2_rec *r, struct t2_tx *tx) {
        ASSERT(thread_registered);
        ASSERT(buf_len(r->key) > 0);
        eclear();
        return delete(t, r, tx);
}

int t2_insert(struct t2_tree *t, struct t2_rec *r, struct t2_tx *tx) {
        ASSERT(thread_registered);
        ASSERT(buf_len(r->key) > 0);
        eclear();
        return insert(t, r, tx);
}

int t2_cursor_init(struct t2_cursor *c, struct t2_buf *key) {
        ASSERT(thread_registered);
        ASSERT(buf_len(key) <= buf_len(&c->curkey));
        ASSERT(c->dir == T2_LESS || c->dir == T2_MORE);
        eclear();
        buf_copy(&c->curkey, key);
        c->maxlen = buf_len(&c->curkey);
        c->curkey.len = buf_len(key);
        return 0;
}

void t2_cursor_fini(struct t2_cursor *c) {
        ASSERT(thread_registered);
        eclear();
        c->curkey.len = c->maxlen;
}

int t2_cursor_next(struct t2_cursor *c) {
        ASSERT(thread_registered);
        eclear();
        return next(c);
}

int t2_lookup_ptr(struct t2_tree *t, void *key, int32_t ksize, void *val, int32_t vsize) {
        struct t2_buf kbuf = { .addr = key, .len = ksize };
        struct t2_buf vbuf = { .addr = val, .len = vsize };
        struct t2_rec r = {
                .key = &kbuf,
                .val = &vbuf
        };
        ASSERT(thread_registered);
        eclear();
        return lookup(t, &r);
}

int t2_insert_ptr(struct t2_tree *t, void *key, int32_t ksize, void *val, int32_t vsize, struct t2_tx *tx) {
        struct t2_buf kbuf = { .addr = key, .len = ksize };
        struct t2_buf vbuf = { .addr = val, .len = vsize };
        struct t2_rec r = {
                .key = &kbuf,
                .val = &vbuf
        };
        ASSERT(thread_registered);
        eclear();
        return insert(t, &r, tx);
}

int t2_delete_ptr(struct t2_tree *t, void *key, int32_t ksize, struct t2_tx *tx) {
        struct t2_buf kbuf = { .addr = key, .len = ksize };
        struct t2_rec r = {
                .key = &kbuf,
        };
        ASSERT(thread_registered);
        eclear();
        return delete(t, &r, tx);
}

struct t2_tx *t2_tx_make(struct t2 *mod) {
        return TXCALL(mod->te, make(mod->te));
}

int t2_tx_open(struct t2 *mod, struct t2_tx *tx) {
        return TXCALL(mod->te, open(mod->te, tx));
}

void t2_tx_close(struct t2 *mod, struct t2_tx *tx) {
        TXCALL(mod->te, close(mod->te, tx));
}

int t2_tx_wait (struct t2 *mod, struct t2_tx *tx, const struct timespec *deadline, bool force) {
        return TXCALL(mod->te, wait(mod->te, tx, deadline, force));
}

void t2_tx_done (struct t2 *mod, struct t2_tx *tx) {
        return TXCALL(mod->te, done(mod->te, tx));
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

static void node_iovec(struct node *n, struct iovec *v) {
        v->iov_base = n->data;
        v->iov_len  = nsize(n);
}

static bool pageable(const struct node *n) {
        return (n->flags & DIRTY) && n->ref <= 1;
}

enum {
        MAX_CLUSTER = 256
};

static void pageout(struct node *n) {
        struct node  *cluster[MAX_CLUSTER];
        struct iovec  vec[MAX_CLUSTER + 1];
        int           nr;
        taddr_t       cur;
        taddr_t       next;
        taddr_t       whole;
        int           result;
        int           shift;
        lock(n, READ);
        if (LIKELY(pageable(n))) {
                node_iovec(n, &vec[0]);
                for (cur = n->addr, nr = 1; nr < ARRAY_SIZE(cluster); ++nr, cur = next) {
                        struct node *right;
                        next = taddr_make(taddr_saddr(cur) + taddr_ssize(cur), taddr_sshift(cur));
                        right = look(n->mod, next);
                        if (right != NULL) {
                                lock(right, READ);
                                if (pageable(right)) {
                                        cluster[nr] = right;
                                        node_iovec(right, &vec[nr]);
                                } else {
                                        unlock(right, READ);
                                        put(right);
                                        break;
                                }
                        } else {
                                break;
                        }
                }
                shift = ilog2(nr);
                for (int i = 1 << shift; i < nr; ++i) {
                        unlock(cluster[i], READ);
                        put(cluster[i]);
                }
                whole = taddr_make(taddr_saddr(n->addr), shift + taddr_sshift(n->addr));
                result = SCALL(n->mod, write, whole, 1 << shift, vec);
                CMOD(l[level(n)].pageout_cluster, nr);
                if (LIKELY(result == 0)) {
                        CINC(write);
                        CADD(write_bytes, taddr_ssize(whole));
                        n->flags &= ~DIRTY;
                        KDEC(dirty);
                        for (int i = 1; i < (1 << shift); ++i) {
                                cluster[i]->flags &= ~DIRTY;
                                KDEC(dirty);
                        }
                } else {
                        LOG("Pageout failure: %"PRIx64": %i/%i.\n", n->addr, result, errno);
                }
                for (int i = 1; i < 1 << shift; ++i) {
                        unlock(cluster[i], READ);
                        put(cluster[i]);
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

static void cache_fini(struct t2 *mod) {
        mutex_lock(&mod->cache.condlock);
        mod->shutdown = true;
        NOFAIL(pthread_cond_signal(&mod->cache.need));
        mutex_unlock(&mod->cache.condlock);
        pthread_join(mod->cache.md, NULL);
        writeout(mod);
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
                        ASSERT(!(n->flags & DIRTY));
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
        if (LIKELY(out != NULL)) {
                memset(out, 0, size);
        }
        return out;
}

static void mem_free(void *ptr) {
        free(ptr);
}

static uint64_t now(void) {
        struct timeval t;
        NOFAIL(gettimeofday(&t, NULL));
        return t.tv_sec * 1000000 + t.tv_usec;
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

static int cds_list_length(const struct cds_list_head *head) {
        const struct cds_list_head *scan;
        int                         length = 0;
        cds_list_for_each_prev(scan, head) {
                ++length;
        }
        return length;
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

static void counter_var_print1(struct counter_var *v, const char *label) {
        printf("%-21s %10.1f\n", label, v->nr ? 1.0 * v->sum / v->nr : 0.0);
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
        printf("wal.space:          %10"PRId64"\n", GVAL(wal_space));
        counter_var_print1(&GVAL(wal_space_nr),  "wal.space_nr");
        counter_var_print1(&GVAL(wal_space_nob), "wal.space_nob");
        printf("wal.write:          %10"PRId64"\n", GVAL(wal_write));
        printf("wal.write_sync:     %10"PRId64"\n", GVAL(wal_write_sync));
        counter_var_print1(&GVAL(wal_write_seg), "wal.write_seg");
        counter_var_print1(&GVAL(wal_write_nob), "wal.write_nob");
        printf("wal.cur_aged:       %10"PRId64"\n", GVAL(wal_cur_aged));
        printf("wal.get_ready:      %10"PRId64"\n", GVAL(wal_get_ready));
        printf("wal.get_wait:       %10"PRId64"\n", GVAL(wal_get_wait));
        printf("wal.get_wait_time:  %10"PRId64"\n", GVAL(wal_get_wait_time));
        counter_var_print1(&GVAL(wal_busy),      "wal.busy");
        counter_var_print1(&GVAL(wal_ready),     "wal.ready");
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
        COUNTER_VAR_PRINT(pageout_cluster);
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
                if (LIKELY(buf_len(r->key) >= buf_len(key))) {
                        buf_copy(r->key, key);
                } else {
                        r->key->len = buf_len(key);
                        result = ERROR(-ENAMETOOLONG);
                }
        }
        if (r->vcb != NULL) {
                r->vcb(val, r->arg);
        } else {
                if (LIKELY(buf_len(r->val) >= buf_len(val))) {
                        buf_copy(r->val, val);
                } else {
                        r->val->len = buf_len(val);
                        result = ERROR(-ENAMETOOLONG);
                }
        }
        return result;
}

static int int32_cmp(int32_t a, int32_t b) {
        return a < b ? -1 : a != b; /* sic. */
}

static int buf_cmp(const struct t2_buf *b0, const struct t2_buf *b1) {
        uint32_t len0 = b0->len;
        uint32_t len1 = b1->len;
        return memcmp(b0->addr, b1->addr, min_32(len0, len1)) ?: int32_cmp(len0, len1);
}

static void buf_copy(const struct t2_buf *dst, const struct t2_buf *src) {
        ASSERT(buf_len(dst) >= buf_len(src));
        memcpy(dst->addr, src->addr, src->len);
}

static int32_t buf_prefix(const struct t2_buf *dst, const struct t2_buf *src) {
        int32_t i;
        int32_t len = min_32(dst->len, src->len);
        for (i = 0; i < len; ++i) {
                if (((char *)dst->addr)[i] != ((char *)src->addr)[i]) {
                        break;
                }
        }
        return i;

}

static int32_t buf_len(const struct t2_buf *b) {
        return b->len;
}

static int32_t rec_len(const struct t2_rec *r) {
        return buf_len(r->key) + buf_len(r->val);
}

static int buf_alloc(struct t2_buf *dst, struct t2_buf *src) {
        int32_t len = buf_len(src);
        ASSERT(dst->addr == NULL);
        dst->len = len;
        dst->addr = mem_alloc(len);
        if (dst->addr != NULL) {
                buf_copy(dst, src);
                return 0;
        } else {
                SET0(dst);
                return ERROR(-ENOMEM);
        }
}

static void buf_free(struct t2_buf *b) {
        mem_free(b->addr);
        SET0(b);
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

static int skeycmp(struct sheader *sh, int pos, int32_t prefix, void *key, int32_t klen, uint32_t mask) {
        int32_t ksize;
        int32_t koff = (skeyoff(sh, pos, &ksize) + prefix) & mask;
        __builtin_prefetch((void *)sh + koff);
        ksize -= prefix;
        klen  -= prefix;
        ksize = min_32(ksize & mask, mask + 1 - koff);
        CMOD(l[sh->head.level].keysize, ksize);
        return memcmp((void *)sh + koff, key + prefix, ksize < klen ? ksize : klen) ?: int32_cmp(ksize, klen);
}

static struct sheader *simple_header(const struct node *n) {
        return n->data;
}

static void buf_clip(struct t2_buf *b, uint32_t mask, void *origin) {
        int32_t off = (b->addr - origin) & mask;
        b->addr = origin + off;
        b->len  = min_32(b->len & mask, mask + 1 - off);
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
        void           *kaddr = rec->key->addr;
        int32_t         klen  = rec->key->len;
        int             cmp   = -1;
        uint32_t        mask  = nsize(n) - 1;
        int32_t         plen  = 0;
        int32_t         span;
        uint8_t __attribute__((unused)) lev = level(n);
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
                plen = n->radix->prefix.len;
                cmp = memcmp(n->radix->prefix.addr, kaddr, min_32(plen, klen)) ?: klen < plen ? +1 : 0;
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
                cmp = skeycmp(sh, l, plen, kaddr, klen, mask);
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
        if (span != delta && skeycmp(sh, l + span, plen, kaddr, klen, mask) <= 0) {
                l += delta - span;
        }
#define RANGE(x, prefetchp)                                                  \
        case 1 << (x):                                                       \
                span >>= 1;                                                  \
                if (prefetchp) {                                             \
                        __builtin_prefetch(sat(sh, l + span + (span >> 1))); \
                        __builtin_prefetch(sat(sh, l + span - (span >> 1))); \
                }                                                            \
                cmp = skeycmp(sh, l + span, plen, kaddr, klen, mask);        \
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
                key->addr = skey(sh, l, &key->len);
                buf_clip(key, mask, sh);
                val->addr = sval(sh, l, &val->len);
                buf_clip(val, mask, sh);
                CMOD(l[lev].keysize, key->len);
                CMOD(l[lev].valsize, key->len);
        }
        return found;
}

static taddr_t internal_addr(const struct slot *s) {
        taddr_t addr = 0;
        buf_clip_node(s->rec.key, s->node);
        buf_clip_node(s->rec.val, s->node);
        s->rec.val->len = min_32(s->rec.val->len, sizeof addr);
        ASSERT(s->rec.val->len >= 0);
        memcpy(&addr, s->rec.val->addr, s->rec.val->len);
        return taddr_is_valid(addr) ? addr : 0;
}

static taddr_t internal_search(struct node *n, struct path *p, int32_t *pos) {
        SLOT_DEFINE(s, n);
        COUNTERS_ASSERT(CVAL(rcu) > 0);
        SET0(s.rec.key);
        SET0(s.rec.val);
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

static void ext_merge(struct ext *ext, int32_t start, int32_t end) {
        ext->start = min_32(ext->start, start);
        ext->end   = max_32(ext->end,   end);
}

static void move(void *sh, int32_t start, int32_t end, int delta) {
        ASSERT(start <= end);
        memmove(sh + start + delta, sh + start, end - start);
        CADD(l[((struct sheader *)sh)->head.level].moves, end - start);
}

static void sdirmove(struct sheader *sh, int32_t nsize, int32_t knob, int32_t vnob, int32_t nr, struct mod *mod) {
        int32_t dir_off = (knob * (nsize - SOF(*sh))) / (knob + vnob) -
                dirsize(nr + 1) / 2 + SOF(*sh);
        int32_t delta;
        dir_off = min_32(max_32(dir_off, knob + SOF(*sh)),
                         nsize - vnob - dirsize(nr + 1));
        ASSERT(knob + SOF(*sh) <= dir_off);
        ASSERT(dir_off + dirsize(nr + 1) + vnob <= nsize);
        delta = dir_off - sh->dir_off;
        move(sh, sh->dir_off, sdirend(sh), delta);
        ext_merge(&mod->ext[DIR], sh->dir_off + delta, sdirend(sh) + delta);
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

static void simple_fini(struct node *n) {
        SET0(simple_header(n));
}

static int simple_insert(struct slot *s, struct mod *mod) {
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
                         beg->voff - end->voff + vlen, sh->nr + 1, mod);
                end = sat(sh, sh->nr);
                CINC(l[sh->head.level].dirmove);
        }
        piv = sat(sh, s->idx);
        move(sh, piv->koff, end->koff, +klen);
        move(sh, end->voff, piv->voff, -vlen);
        ext_merge(&mod->ext[KEY], piv->koff, end->koff + klen); /* Captures buf_copy() below. */
        ext_merge(&mod->ext[VAL], end->voff - vlen, piv->voff);
        for (int32_t i = ++sh->nr; i > s->idx; --i) {
                struct dir_element *prev = sat(sh, i - 1);
                __builtin_prefetch(prev - 1);
                *sat(sh, i) = (struct dir_element){
                        .koff = prev->koff + klen,
                        .voff = prev->voff - vlen
                };
        }
        ext_merge(&mod->ext[DIR], sh->dir_off + (s->idx + 1) * sizeof *piv,
                  sh->dir_off + (sh->nr + 1) * sizeof *piv);
        buf.addr = skey(sh, s->idx, &buf.len);
        ASSERT(buf.len == klen);
        buf_copy(&buf, s->rec.key);
        buf.addr = sval(sh, s->idx, &buf.len);
        ASSERT(buf.len == vlen);
        buf_copy(&buf, s->rec.val);
        EXPENSIVE_ASSERT(scheck(sh, s->node->ntype));
        if (LIKELY(s->node->radix != NULL)) {
                s->node->radix->utmost |= (s->idx == 0 || s->idx == nr(s->node) - 1);
        }
        ASSERT(mod->ext[HDR].start == 0);
        mod->ext[HDR].end = sizeof *sh;
        return 0;
}

static void simple_delete(struct slot *s, struct mod *mod) {
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
        ext_merge(&mod->ext[KEY], inn->koff - klen, end->koff - klen);
        ext_merge(&mod->ext[VAL], end->voff + vlen, inn->voff + vlen);
        for (int32_t i = s->idx; i < sh->nr; ++i) {
                struct dir_element *next = sat(sh, i + 1);
                *sat(sh, i) = (struct dir_element){
                        .koff = next->koff - klen,
                        .voff = next->voff + vlen
                };
        }
        ext_merge(&mod->ext[DIR], sh->dir_off + s->idx * sizeof *piv,
                  sh->dir_off + sh->nr * sizeof *piv);
        --sh->nr;
        EXPENSIVE_ASSERT(scheck(sh, s->node->ntype));
        if (LIKELY(s->node->radix != NULL)) {
                s->node->radix->utmost |= (s->idx == 0 || s->idx == nr(s->node));
        }
        ASSERT(mod->ext[HDR].start == 0);
        mod->ext[HDR].end = sizeof *sh;
}

static void simple_get(struct slot *s) {
        struct sheader *sh = simple_header(s->node);
        s->rec.key->addr = skey(sh, s->idx, &s->rec.key->len);
        s->rec.val->addr = sval(sh, s->idx, &s->rec.val->len);
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
        range_print(b->addr, b->len, b->addr, b->len);
}

static void rec_print(const struct t2_rec *r) {
        printf("key: ");
        buf_print(r->key);
        printf(" val: ");
        buf_print(r->val);
}

static int shift_one(struct page *dp, struct page *sp, enum dir dir) {
        struct node  *d   = dp->node;
        struct node  *s   = sp->node;
        struct t2_buf key = {};
        struct t2_buf val = {};
        struct slot   dst = { .node = d, .rec = { .key = &key, .val = &val } };
        struct slot   src = { .node = s, .rec = { .key = &key, .val = &val } };
        ASSERT(nr(s) > 0);
        rec_get(&src, utmost(s, dir));
        dst.idx = dir == LEFT ? nr(d) : 0;
        CINC(l[level(d)].shift_one);
        return NCALL(d, insert(&dst, &dp->mod)) ?: (NCALL(s, delete(&src, &dp->mod)), 0);
}

static int shift(struct page *dst, struct page *src, const struct slot *point, enum dir dir) {
        struct node *d = dst->node;
        struct node *s = src->node;
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
                        result = shift_one(dst, src, dir);
                } else {
                        break;
                }
        }
        ASSERT(can_insert(point->idx <= nr(s) ? s : d, &point->rec));
        return result;
}

static int merge(struct page *dst, struct page *src, enum dir dir) {
        int result = 0;
        while (LIKELY(result == 0) && nr(src->node) > 0) {
                result = shift_one(dst, src, dir);
        }
        CINC(l[level(dst->node)].merge);
        return result;
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
};

/* @wal */

static void (*ut_lsnset)(struct t2_node *node, lsn_t lsn);
static int  (*ut_apply)(struct t2 *mod, struct t2_txrec *txr);

void t2_lsnset(struct t2_node *node, lsn_t lsn) {
        if (!UT || ut_lsnset == NULL) {
                struct node *n = (void *)node;
                n->lsn = lsn;
        } else {
                (*ut_lsnset)(node, lsn);
        }
}

lsn_t t2_lsnget(const struct t2_node *node) {
        struct node *n = (void *)node;
        return n->lsn;
}

taddr_t t2_addr(const struct t2_node *node) {
        struct node *n = (void *)node;
        return n->addr;
}

int t2_apply(struct t2 *mod, struct t2_txrec *txr) {
        if (!UT || ut_apply == NULL) {
                struct node *n = get(mod, txr->addr);
                if (EISOK(n)) {
                        memcpy(n->data + txr->off, txr->part.addr, txr->part.len);
                        n->flags |= DIRTY;
                        return 0;
                } else {
                        return ERRCODE(n);
                }
        } else {
                return (*ut_apply)(mod, txr);
        }
}

enum rec_type {
        HEADER = 'H',
        FOOTER = 'F',
        UNDO   = 'U',
        REDO   = 'R'
};

static const int64_t REC_MAGIX = 0xa50d4e3333337221ll;

struct wal_superblock {
        int64_t magix;
};

struct wal_rec {
        int64_t magix;
        int32_t len;
        int32_t rtype;
        union {
                struct {
                        taddr_t node;
                        int32_t off;
                } update;
                struct {
                        lsn_t   log_start;
                        lsn_t   max_synced;
                } header;
        } u;
        uint8_t data[0];
};

struct wal_tx {
        struct t2_tx base;
        lsn_t        id;
};

enum { WAL_MAX_BUF_SEG = 1024 }; /* __IOV_MAX on Linux and UIO_MAXIOV on Darwin are both 1024. */

struct wal_buf {
        int32_t              used;
        int32_t              nob;
        lsn_t                start;
        struct cds_list_head link;
        struct iovec         seg[WAL_MAX_BUF_SEG];
};

enum {
        STEAL = 1 << 0, /* Undo needed. */
        FORCE = 1 << 1, /* Redo not needed. */
        MAKE  = 1 << 2, /* Delete existing log. */
        KEEP  = 1 << 3  /* Do not truncate the log on finalisation. */
};

struct wal_te {
        struct t2_te          base;
        struct t2            *mod;
        lsn_t                 lsn;
        uint32_t              flags;
        pthread_mutex_t       lock;
        pthread_cond_t        logwait;
        pthread_cond_t        bufwait;
        pthread_cond_t        bufwrite;
        bool                  shutdown;
        lsn_t                 max_persistent;
        lsn_t                 max_synced;
        lsn_t                 max_written;
        lsn_t                 log_start;
        lsn_t                 log_start_persistent;
        lsn_t                 log_pruned;
        time_t                last_sync;
        int                   fd;
        int                   buf_size;
        struct wal_buf       *cur;
        struct cds_list_head  ready;
        struct cds_list_head  busy;
        int                   cur_age;
        pthread_t             writer;
        const char           *logname;
        bool                  recovered;
        int                   nr_bufs;
};

enum {
        WAL_SLEEP_SEC  = 1,
        WAL_SLEEP_NSEC = 0,
        WAL_AGE_LIMIT  = 2,
        WAL_MAX_WRITES = 7, /* Shift. */
        WAL_SYNC_NOB   = 1 << 27,
        WAL_SYNC_AGE   = 1
};

static bool wal_invariant(const struct wal_te *en) {
        return
                cds_list_length(&en->busy) + cds_list_length(&en->ready) + (en->cur != NULL) == en->nr_bufs &&
                (en->flags & ~(STEAL|FORCE|MAKE|KEEP)) == 0 &&
                en->log_start_persistent <= en->log_start &&
                en->log_start <= en->max_persistent &&
                en->max_persistent <= en->max_synced &&
                en->max_synced <= en->max_written &&
                en->max_written <= en->lsn &&
                ((en->log_start_persistent | en->log_start | en->max_persistent | en->max_synced | en->max_written) & (en->buf_size - 1)) == 0 &&
                en->cur != NULL ? cds_list_empty(&en->cur->link) : true;
}

static void wal_report(const struct wal_te *te) {
        return;
        printf("lsp: %14"PRId64" ls: %14"PRId64" %mp: %14"PRId64" %ms: %14"PRId64" mw: %14"PRId64" lsn: %14"PRId64" ready: %2d busy: %2d\n",
               te->log_start_persistent, te->log_start, te->max_persistent, te->max_synced, te->max_written,
               te->lsn, cds_list_length(&te->ready), cds_list_length(&te->busy));
}

static void *wal_space(struct wal_te *en, int nr, int32_t nob, int32_t *out) {
        ASSERT(wal_invariant(en));
        int32_t size = nob + nr * sizeof(struct wal_rec);
        void   *buf  = mem_alloc(size);
        if (LIKELY(buf != NULL)) {
                *out = size;
        }
        CINC(wal_space);
        CMOD(wal_space_nr, nr);
        CMOD(wal_space_nob, nob);
        return buf;
}

static void wal_buf_release(struct wal_buf *buf) {
        for (int i = 1; i < buf->used; ++i) {
                mem_free(buf->seg[i].iov_base);
                buf->seg[i].iov_base = NULL;
        }
}

static int wal_buf_alloc(struct wal_te *en) {
        struct wal_buf *buf = mem_alloc(sizeof *buf);
        if (LIKELY(buf != NULL)) {
                cds_list_add(&buf->link, &en->ready);
                return 0;
        } else {
                return ERROR(-ENOMEM);
        }
}

static void wal_buf_fini(struct wal_buf *buf) {
        cds_list_del_init(&buf->link);
        mem_free(buf);
}

static bool wal_should_fsync(const struct wal_te *en) {
        return  en->busy.next->next == &en->busy || /* 0 or 1 busy buffers. */
                time(NULL) - en->last_sync > WAL_SYNC_AGE ||
                en->max_written - en->max_synced > WAL_SYNC_NOB;
}

#if ON_DARWIN
static int wal_sync(int fd) {
        /* F_BARRIERFSYNC is more efficient, but the tree and the log can be on different devices. */
        return fcntl(fd, F_FULLFSYNC, 0);
}

static void wal_log_prune(struct wal_te *en) {
        struct fpunchhole hole = {
                .fp_offset = en->buf_size,
                .fp_length = en->log_start_persistent - en->buf_size
        };
        fcntl(en->fd, F_PUNCHHOLE, &hole);
}

#elif ON_LINUX
static int wal_sync(int fd) {
        return fdatasync(fd);
}

static void wal_log_prune(struct wal_te *en) {
        fallocate(en->fd, FALLOC_FL_PUNCH_HOLE | FALLOC_FL_KEEP_SIZE, en->buf_size, en->log_start_persistent - en->buf_size);
}

#endif

static int wal_write(struct wal_te *en, struct wal_buf *buf) {
        int            result;
        struct wal_rec header = {
                .magix = REC_MAGIX,
                .rtype = HEADER,
                .len   = 0,
                .u     = {
                        .header = {
                                .log_start  = en->log_start,
                                .max_synced = en->max_synced
                        }
                }
        };
        struct wal_rec footer = {
                .magix = REC_MAGIX,
                .rtype = FOOTER,
                .len   = en->buf_size - buf->nob
        };
        ASSERT(wal_invariant(en));
        mutex_unlock(&en->lock);
        ASSERT(buf->start != 0);
        buf->seg[0]         = (struct iovec) { .iov_base = &header, .iov_len  = sizeof header };
        buf->seg[buf->used] = (struct iovec) { .iov_base = &footer, .iov_len  = sizeof footer };
        result = pwritev(en->fd, buf->seg, buf->used + 1, buf->start);
        CINC(wal_write);
        CMOD(wal_write_seg, buf->used + 1);
        CMOD(wal_write_nob, buf->nob);
        mutex_lock(&en->lock);
        if (LIKELY(result == buf->nob)) {
                cds_list_del(&buf->link);
                CMOD(wal_busy, cds_list_length(&en->busy));
                ASSERT(buf->start + en->buf_size > en->max_written);
                en->max_written = buf->start + en->buf_size;
                wal_buf_release(buf);
                cds_list_add(&buf->link, &en->ready);
                NOFAIL(pthread_cond_signal(&en->bufwait));
                CMOD(wal_ready, cds_list_length(&en->ready));
                if (wal_should_fsync(en)) {
                        mutex_unlock(&en->lock);
                        result = wal_sync(en->fd);
                        CINC(wal_write_sync);
                        mutex_lock(&en->lock);
                        if (LIKELY(result == 0)) { /* Assume single log writer. */
                                en->max_persistent = en->max_synced;
                                en->max_synced = en->max_written;
                                en->log_start_persistent = en->log_start;
                                en->last_sync = time(NULL);
                        } else {
                                result = ERROR(-errno);
                        }
                } else {
                        result = 0;
                }
        } else { /* TODO: Handle list linkage. */
                LOG("Log write failure %s+%"PRId64"+%"PRId64": %i/%i.\n", en->logname, buf->start, buf->nob, result, errno);
                result = ERROR(result < 0 ? -errno : -EIO);
        }
        ASSERT(wal_invariant(en));
        return result;
}

static bool wal_fits(struct wal_te *en, struct wal_buf *buf, int32_t size) {
        return buf->nob + size <= en->buf_size && buf->used < ARRAY_SIZE(buf->seg) - 1;
}

static void wal_buf_start(struct wal_te *en) {
        struct wal_buf *buf = en->cur = COF(en->ready.next, struct wal_buf, link);
        CMOD(wal_ready, cds_list_length(&en->ready));
        cds_list_del_init(&buf->link);
        buf->start = en->lsn;
        buf->used = 1;
        buf->nob = 2 * sizeof(struct wal_rec);
        en->cur_age = time(NULL);
}

static void wal_buf_end(struct wal_te *en) {
        ASSERT(en->lsn < en->cur->start + en->buf_size);
        cds_list_add(&en->cur->link, &en->busy);
        CMOD(wal_busy, cds_list_length(&en->busy));
        en->lsn = en->cur->start + en->buf_size;
        en->cur = NULL;
        NOFAIL(pthread_cond_signal(&en->bufwrite));
}

static void wal_get(struct wal_te *en, int32_t size) {
        while (true) {
                while (UNLIKELY(en->cur == NULL)) {
                        if (!cds_list_empty(&en->ready)) {
                                CINC(wal_get_ready);
                                wal_buf_start(en);
                                ASSERT(wal_fits(en, en->cur, size));
                                return;
                        } else {
                                uint64_t start = now();
                                CINC(wal_get_wait);
                                NOFAIL(pthread_cond_wait(&en->bufwait, &en->lock));
                                CADD(wal_get_wait_time, now() - start);
                        }
                }
                if (LIKELY(wal_fits(en, en->cur, size))) {
                        break;
                }
                wal_buf_end(en);
        }
}

static lsn_t wal_attach(struct wal_te *en, int32_t size, void *data) {
        lsn_t lsn;
        mutex_lock(&en->lock);
        ASSERT(wal_invariant(en));
        wal_get(en, size);
        lsn = en->lsn;
        en->lsn += size;
        en->cur->seg[en->cur->used++] = (struct iovec){ .iov_base = data, .iov_len = size };
        en->cur->nob += size;
        ASSERT(wal_invariant(en));
        mutex_unlock(&en->lock);
        return lsn;
}

static struct wal_rec *wal_next(struct wal_rec *rec) {
        return (void *)&rec->data[rec->len];
}

static int wal_diff(struct t2_te *engine, struct t2_tx *trax, int32_t nob, int nr, struct t2_txrec *txr, int32_t rtype) {
        struct wal_te  *en  = COF(engine, struct wal_te, base);
        struct wal_tx  *tx  = COF(trax, struct wal_tx, base);
        struct wal_rec *rec;
        void           *space;
        int32_t         size;
        ASSERT(en->recovered);
        rec = space = wal_space(en, nr, nob, &size);
        if (UNLIKELY(rec == NULL)) {
                return ERROR(-ENOMEM);
        }
        for (int i = 0; i < nr; ++i) {
                ASSERT((void *)rec + sizeof *rec + txr[i].part.len <= space + size);
                *rec = (struct wal_rec) {
                        .magix = REC_MAGIX,
                        .rtype = rtype,
                        .len   = txr[i].part.len,
                        .u = {
                                .update = {
                                        .off  = txr[i].off,
                                        .node = txr[i].addr
                                }
                        }
                };
                memcpy(rec->data, txr[i].part.addr, rec->len);
                rec = wal_next(rec);
        }
        rec = space;
        tx->id = wal_attach(en, size, space);
        for (int i = 0; i < nr; ++i) {
                t2_lsnset(txr[i].node, tx->id);
        }
        return 0;
}

static int wal_ante(struct t2_te *engine, struct t2_tx *trax, int32_t nob, int nr, struct t2_txrec *txr) {
        return wal_diff(engine, trax, nob, nr, txr, UNDO);
}

static int wal_post(struct t2_te *engine, struct t2_tx *trax, int32_t nob, int nr, struct t2_txrec *txr) {
        return wal_diff(engine, trax, nob, nr, txr, REDO);
}

static void wal_fini(struct t2_te *engine) {
        struct wal_te *en = COF(engine, struct wal_te, base);
        mutex_lock(&en->lock);
        ASSERT(wal_invariant(en));
        if (en->cur != NULL) {
                wal_buf_end(en);
        }
        wal_get(en, 0);
        wal_buf_end(en);
        en->shutdown = true;
        NOFAIL(pthread_cond_signal(&en->bufwrite));
        mutex_unlock(&en->lock);
        pthread_join(en->writer, NULL);
        ASSERT(cds_list_empty(&en->busy));
        if (en->fd >= 0) {
                wal_sync(en->fd);
                close(en->fd);
                if (!(en->flags & KEEP)) {
                        unlink(en->logname);
                }
        }
        if (en->cur != NULL) {
                wal_buf_fini(en->cur);
        }
        while (!cds_list_empty(&en->ready)) {
                wal_buf_fini(COF(en->ready.next, struct wal_buf, link));
        }
        ASSERT(cds_list_empty(&en->ready));
        NOFAIL(pthread_cond_destroy(&en->bufwrite));
        NOFAIL(pthread_cond_destroy(&en->bufwait));
        NOFAIL(pthread_cond_destroy(&en->logwait));
        NOFAIL(pthread_mutex_destroy(&en->lock));
        mem_free(en);
}

struct t2_te *wal_prep(const char *logname, int nr_bufs, int buf_size, int32_t flags) {
        struct wal_te *en     = mem_alloc(sizeof *en);
        int            result = 0;
        ASSERT(nr_bufs > 0);
        if (en != NULL) {
                en->base.ante    = &wal_ante;
                en->base.init    = &wal_init;
                en->base.post    = &wal_post;
                en->base.fini    = &wal_fini;
                en->base.make    = &wal_make;
                en->base.wait    = &wal_wait;
                en->base.done    = &wal_done;
                en->base.canpage = &wal_canpage;
                en->base.dirty   = &wal_dirty;
                en->base.name    = "wal";

                CDS_INIT_LIST_HEAD(&en->ready);
                CDS_INIT_LIST_HEAD(&en->busy);
                NOFAIL(pthread_mutex_init(&en->lock, NULL));
                NOFAIL(pthread_cond_init(&en->logwait, NULL));
                NOFAIL(pthread_cond_init(&en->bufwait, NULL));
                NOFAIL(pthread_cond_init(&en->bufwrite, NULL));
                en->flags = flags;
                en->buf_size = buf_size;
                en->logname = logname;
                if (flags & MAKE) {
                        unlink(logname); /* Do not bother checking for errors. */
                }
                en->fd = open(logname, O_RDWR);
                if (en->fd < 0) {
                        if (errno == ENOENT) {
                                en->fd = open(logname, O_RDWR | O_CREAT, S_IRUSR | S_IWUSR);
                                if (en->fd >= 0) {
                                        result = ftruncate(en->fd, buf_size);
                                } else {
                                        result = ERROR(-errno);
                                }
                        } else {
                                result = ERROR(-errno);
                        }
                }
                if (result == 0) {
                        en->nr_bufs = nr_bufs;
                        for (int i = 0; result == 0 && i < nr_bufs; ++i) {
                                result = wal_buf_alloc(en);
                        }
                } else {
                        result = ERROR(-errno);
                }
                if (result != 0) {
                        wal_fini(&en->base);
                }
        } else {
                result = ERROR(-ENOMEM);
        }
        return result == 0 ? &en->base : EPTR(result);
}

static bool wal_rec_invariant(const struct wal_rec *rec, lsn_t lsn) {
        return  rec->magix == REC_MAGIX &&
                (rec->rtype == HEADER || rec->rtype == FOOTER || rec->rtype == UNDO || rec->rtype == REDO) &&
                rec->rtype == HEADER ? (rec->len == 0 &&
                                        rec->u.header.log_start > 0 && rec->u.header.log_start <= lsn &&
                                        rec->u.header.max_synced > 0 && rec->u.header.max_synced <= lsn &&
                                        rec->u.header.log_start <= rec->u.header.max_synced) : true;
}

static bool wal_buf_is_valid(struct wal_te *en, struct wal_rec *rec, lsn_t lsn) {
        return wal_rec_invariant(rec, lsn) && rec->rtype == HEADER;
}

static int wal_replay(struct wal_te *en, void *space, lsn_t start, lsn_t end) {
        struct wal_rec *rec;
        int             result = 0;
        ASSERT((en->flags & (FORCE|STEAL)) == 0); /* Redo-Noundo */
        for (rec = space; result == 0 && (void *)rec < space + end - start; rec = wal_next(rec)) {
                if (!wal_rec_invariant(rec, start + (void *)rec - space)) {
                        result = ERROR(-EIO);
                } else if (rec->rtype == REDO) {
                        struct t2_txrec txr = {
                                .addr = rec->u.update.node,
                                .off  = rec->u.update.off,
                                .part = {
                                        .len  = rec->len,
                                        .addr = &rec->data
                                }
                        };
                        result = t2_apply(en->mod, &txr);
                }
        }
        return result;
}

static int wal_recover_log(struct wal_te *en, lsn_t start, lsn_t end) {
        void           *space = mem_alloc(end - start);
        int64_t         result;
        if (space == NULL) {
                return ERROR(-ENOMEM);
        }
        result = pread(en->fd, space, end - start, start);
        if (result == end - start) {
                result = wal_replay(en, space, start, end);
        } else if (result < 0) {
                result = ERROR(-errno);
        } else {
                result = ERROR(-EIO);
        }
        mem_free(space);
        return result;
}

static void wal_recovery_done(struct wal_te  *en, lsn_t start, lsn_t end) {
        en->lsn = en->max_persistent = en->max_synced = en->max_written = end;
        en->log_pruned = en->log_start_persistent = en->log_start = start;
        en->recovered = true;
}

static int wal_recover(struct wal_te  *en) {
        void           *buf;
        struct wal_rec *rec;
        struct stat     st;
        int             result;
        int64_t         lastbuf;
        result = fstat(en->fd, &st);
        if (result != 0) {
                return ERROR(-errno);
        }
        if (st.st_size == en->buf_size) {
                wal_recovery_done(en, en->buf_size, en->buf_size);
                return 0;
        }
        rec = buf = mem_alloc(en->buf_size);
        if (UNLIKELY(buf == NULL)) {
                return ERROR(-ENOMEM);
        }
        for (lastbuf = (st.st_size - 1) / en->buf_size; lastbuf > 0; lastbuf--) {
                lsn_t off = lastbuf * en->buf_size;
                result = pread(en->fd, buf, en->buf_size, off);
                if (result >= SOF(*rec)) {
                        if (wal_buf_is_valid(en, rec, off)) {
                                result = 0;
                                break;
                        } else {
                                result = ERROR(-EIO);
                        }
                } else {
                        result = ERROR(result < 0 ? -errno : -EIO);
                }
        }
        if (result == 0) {
                if (lastbuf >= 1) {
                        result = wal_recover_log(en, rec->u.header.log_start, rec->u.header.max_synced);
                        if (result == 0) {
                                wal_recovery_done(en, rec->u.header.log_start, rec->u.header.max_synced);
                                en->recovered = true;
                                en->lsn = en->max_persistent = en->max_synced = en->max_written = rec->u.header.max_synced;
                                en->log_start = rec->u.header.log_start;
                        }
                } else {
                        return ERROR(-EIO);
                }
        }
        mem_free(buf);
        return result;
}

static struct t2_tx *wal_make(struct t2_te *te) {
        struct wal_tx *tx = mem_alloc(sizeof *tx);
        if (LIKELY(tx != NULL)) {
                return &tx->base;
        } else {
                return NULL;
        }
}

static bool wal_tx_stable(struct wal_te *en, lsn_t tx) {
        return ((en->flags & FORCE) ? en->log_start_persistent : en->max_persistent) > tx;
}

static int wal_wait(struct t2_te *engine, struct t2_tx *trax, const struct timespec *deadline, bool force) {
        struct wal_te *en = COF(engine, struct wal_te, base);
        struct wal_tx *tx = COF(trax, struct wal_tx, base);
        int            result = 0;
        ASSERT(tx->id != 0);
        mutex_lock(&en->lock);
        ASSERT(wal_invariant(en));
        if (force && en->cur != NULL && en->cur->start <= tx->id) {
                wal_buf_end(en);
        }
        while (!wal_tx_stable(en, tx->id)) {
                result = -pthread_cond_timedwait(&en->logwait, &en->lock, deadline);
                ASSERT(result == 0 || result == -ETIMEDOUT);
                if (result != 0) {
                        break;
                }
        }
        ASSERT(wal_invariant(en));
        mutex_unlock(&en->lock);
        return result;
}

static int wal_open(struct t2_te *engine, struct t2_tx *trax) {
        return 0;
}

static void wal_close(struct t2_te *engine, struct t2_tx *trax) {
}

static void wal_done(struct t2_te *te, struct t2_tx *trax) {
        mem_free(COF(trax, struct wal_tx, base));
}

static bool wal_canpage(struct t2_te *engine, struct t2_node *n) {
        struct wal_te *en = COF(engine, struct wal_te, base);
        return t2_lsnget(n) < en->max_persistent;
}

static void wal_dirty(struct t2_te *engine, lsn_t lsn) {
        struct wal_te *en = COF(engine, struct wal_te, base);
        mutex_lock(&en->lock);
        ASSERT(wal_invariant(en));
        en->log_start = lsn;
        ASSERT(wal_invariant(en));
        mutex_unlock(&en->lock);
}

static void wal_writer_chores(struct wal_te *en) {
        counters_fold();
        if (en->cur != NULL && time(NULL) - en->cur_age > WAL_AGE_LIMIT) {
                wal_buf_end(en);
                CINC(wal_cur_aged);
        }
        if (en->log_start_persistent > en->log_pruned) {
                wal_log_prune(en);
                en->log_pruned = en->log_start_persistent;
        }
}

static void *wal_writer(void *arg) {
        struct wal_te *en = arg;
        int            result;
        mutex_lock(&en->lock);
        while (true) {
                struct timeval  cur;
                struct timespec deadline;
                int writes = 0;
                ASSERT(wal_invariant(en));
                while (!cds_list_empty(&en->busy)) {
                        wal_write(en, COF(en->busy.prev, struct wal_buf, link)); /* TODO: Handle errors. */
                        wal_report(en);
                        if ((++writes & ((1 << WAL_MAX_WRITES) - 1)) == 0) {
                                wal_writer_chores(en);
                        }
                }
                wal_writer_chores(en);
                if (en->shutdown) {
                        break;
                }
                gettimeofday(&cur, NULL);
                deadline.tv_sec  = cur.tv_sec + WAL_SLEEP_SEC;
                deadline.tv_nsec = WAL_SLEEP_NSEC;
                result = pthread_cond_timedwait(&en->bufwrite, &en->lock, &deadline);
                ASSERT(result == 0 || result == ETIMEDOUT);
        }
        mutex_unlock(&en->lock);
        return NULL;
}

static int wal_init(struct t2_te *engine, struct t2 *mod) {
        struct wal_te *en = COF(engine, struct wal_te, base);
        int            result;
        en->mod = mod;
        result = pthread_create(&en->writer, NULL, &wal_writer, en);
        if (result == 0) {
                result = wal_recover(en);
                ASSERT(result == 0 ? wal_invariant(en) : true);
        }
        return result;
}

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

static int mso_read(struct t2_storage *storage, taddr_t addr, int nr, struct iovec *dst) {
        void *src = (void *)taddr_saddr(addr);
        ASSERT(taddr_ssize(addr) == REDUCE(i, nr, 0, + dst[i].iov_len));
        if (taddr_ssize(addr) <= 4096 && FORALL(i, taddr_ssize(addr) / 8, addr_is_valid((void *)taddr_saddr(addr) + 8 * i))) {
                for (int i = 0; i < nr; ++i) {
                        memcpy(dst[i].iov_base, src, dst[i].iov_len);
                        src += dst[i].iov_len;
                }
                return 0;
        } else {
                return -ESTALE;
        }
}

static int mso_write(struct t2_storage *storage, taddr_t addr, int nr, struct iovec *src) {
        void *dst = (void *)taddr_saddr(addr);
        ASSERT(taddr_ssize(addr) == REDUCE(i, nr, 0, + src[i].iov_len));
        for (int i = 0; i < nr; ++i) {
                memcpy(dst, src[i].iov_base, src[i].iov_len);
                dst += src[i].iov_len;
        }
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

static int file_read(struct t2_storage *storage, taddr_t addr, int nr, struct iovec *dst) {
        struct file_storage *fs    = COF(storage, struct file_storage, gen);
        uint64_t             off   = taddr_saddr(addr);
        int                  result;
        ASSERT(taddr_ssize(addr) == REDUCE(i, nr, 0, + dst[i].iov_len));
        if (UNLIKELY(off >= fs->free)) {
                return -ESTALE;
        }
        result = preadv(fs->fd, dst, nr, off);
        if (LIKELY(result == taddr_ssize(addr))) {
                return 0;
        } else if (result < 0) {
                return ERROR(result);
        } else {
                return -ESTALE;
        }
}

static int file_write(struct t2_storage *storage, taddr_t addr, int nr, struct iovec *src) {
        struct file_storage *fs    = COF(storage, struct file_storage, gen);
        uint64_t             off   = taddr_saddr(addr);
        int                  result;
        ASSERT(taddr_ssize(addr) == REDUCE(i, nr, 0, + src[i].iov_len));
        if (UNLIKELY(off >= fs->free)) {
                return -ESTALE;
        }
        result = pwritev(fs->fd, src, nr, off);
        if (LIKELY(result == taddr_ssize(addr))) {
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
        struct mod mod = {};
        struct sheader *sh = simple_header(s->node);
        for (int32_t i = 0; simple_free(s->node) >=
                     buf_len(key) + buf_len(val) + SOF(struct dir_element); ++i) {
                NOFAIL(simple_insert(s, &mod));
                radixmap_update(s->node);
                ASSERT(sh->nr == i + 1);
                ((char *)key->addr)[1]++;
                ((char *)val->addr)[1]++;
                s->idx = (s->idx + 7) % sh->nr;
        }
}

static void buf_init_str(struct t2_buf *b, const char *s) {
        b->len  = (int32_t)strlen(s) + 1;
        b->addr = (void *)s;
}

static bool is_sorted(struct node *n) {
        struct sheader *sh = simple_header(n);
        SLOT_DEFINE(ss, n);
        char   *keyarea = NULL;
        int32_t keysize = 0;
        for (int32_t i = 0; i < sh->nr; ++i) {
                rec_get(&ss, i);
                if (i > 0) {
                        int cmp = skeycmp(sh, i, 0, keyarea, keysize, nsize(n) - 1);
                        if (cmp <= 0) {
                                printf("Misordered at %i: ", i);
                                range_print(keyarea, keysize,
                                            keyarea, keysize);
                                printf(" %c ", cmpch(cmp));
                                range_print(n->data, nsize(n),
                                            ss.rec.key->addr,
                                            ss.rec.key->len);
                                printf("\n");
                                simple_print(n);
                                return false;
                        }
                }
                keyarea = ss.rec.key->addr;
                keysize = ss.rec.key->len;
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
        struct mod m = {};
        int result;
        buf_init_str(&key, key0);
        buf_init_str(&val, val0);
        usuite("simple-node");
        utest("make");
        simple_make(&n);
        ASSERT(sh->nr == 0);
        utest("insert");
        populate(&s, &key, &val);
        result = simple_insert(&s, &m);
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
                simple_delete(&s, &m);
                radixmap_update(&n);
                ASSERT(sh->nr == i);
        }
        s.idx = 0;
        while (nr(&n) > 0) {
                simple_delete(&s, &m);
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
                NOFAIL(simple_insert(&s, &m));
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
        struct mod m = {};
        int result;
        usuite("traverse");
        utest("t2_init");
        struct t2 *mod = t2_init(ut_storage, NULL, HT_SHIFT, CA_SHIFT);
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
                NOFAIL(simple_insert(&s, &m));
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
        struct t2 *mod = t2_init(ut_storage, NULL, HT_SHIFT, CA_SHIFT);
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
        NOFAIL(t2_insert(&t, &r, NULL));
        utest("eexist");
        result = t2_insert(&t, &r, NULL);
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
        mod = t2_init(ut_storage, NULL, HT_SHIFT, CA_SHIFT);
        ASSERT(EISOK(mod));
        ttype.mod = NULL;
        t2_tree_type_register(mod, &ttype);
        t2_node_type_register(mod, &ntype);
        t = t2_tree_create(&ttype, NULL);
        ASSERT(EISOK(t));
        buf_init_str(&key, key0);
        buf_init_str(&val, val0);
        utest("insert-1");
        NOFAIL(t2_insert(t, &r, NULL));
        utest("eexist");
        result = t2_insert(t, &r, NULL);
        ASSERT(result == -EEXIST);
        utest("5K");
        key = BUF_VAL(k64);
        val = BUF_VAL(v64);
        for (k64 = 0; k64 < 5000; ++k64) {
                NOFAIL(t2_insert(t, &r, NULL));
        }
        utest("20K");
        key = BUF_VAL(k64);
        val = BUF_VAL(v64);
        for (int i = 0; i < 20000; ++i) {
                k64 = ht_hash(i);
                v64 = ht_hash(i + 1);
                NOFAIL(t2_insert(t, &r, NULL));
        }
        utest("50K");
        for (int i = 0; i < 50000; ++i) {
                k64 = ht_hash(i);
                v64 = ht_hash(i + 1);
                result = t2_insert(t, &r, NULL);
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
        mod = t2_init(ut_storage, NULL, HT_SHIFT, CA_SHIFT);
        ASSERT(EISOK(mod));
        ttype.mod = NULL;
        t2_tree_type_register(mod, &ttype);
        t2_node_type_register(mod, &ntype);
        t = t2_tree_create(&ttype, NULL);
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
                keyb = (struct t2_buf){ .len = ksize, .addr = &key };
                valb = (struct t2_buf){ .len = vsize, .addr = &val };
                NOFAIL(t2_insert(t, &r, NULL));
                for (int j = 0; j < 10; ++j) {
                        long probe = rand();
                        *(long *)key = probe;
                        keyb = (struct t2_buf){ .len = ksize, .addr = &key };
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
                keyb = (struct t2_buf){ .len = ksize,    .addr = &key };
                valb = (struct t2_buf){ .len = SOF(val), .addr = &val };
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
                keyb = (struct t2_buf){ .len = ksize, .addr = &key };
                valb = (struct t2_buf){ .len = vsize, .addr = &val };
                result = t2_insert(t, &r, NULL);
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
        mod = t2_init(ut_storage, NULL, HT_SHIFT, CA_SHIFT);
        ASSERT(EISOK(mod));
        ttype.mod = NULL;
        t2_tree_type_register(mod, &ttype);
        t2_node_type_register(mod, &ntype);
        t = t2_tree_create(&ttype, NULL);
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
                keyb = (struct t2_buf){ .len = ksize, .addr = &key };
                valb = (struct t2_buf){ .len = vsize, .addr = &val };
                NOFAIL(t2_insert(t, &r, NULL));
        }
        for (long i = U - 1; i >= 0; --i) {
                for (long j = 0; j < U; ++j) {
                        ksize = sizeof i;
                        *(long *)key = j;
                        keyb = (struct t2_buf){ .len = ksize,    .addr = &key };
                        valb = (struct t2_buf){ .len = SOF(val), .addr = &val };
                        result = t2_lookup(t, &r);
                        ASSERT((result == 0) == (j <= i) && (result == -ENOENT) == (j > i));
                }
                ksize = sizeof i;
                vsize = rand() % maxsize;
                ASSERT(ksize < SOF(key));
                ASSERT(vsize < SOF(val));
                ASSERT(4 * (ksize + vsize) < ((int32_t)1 << ntype.shift));
                *(long *)key = i;
                keyb = (struct t2_buf){ .len = ksize, .addr = &key };
                valb = (struct t2_buf){ .len = vsize, .addr = &val };
                NOFAIL(t2_delete(t, &r, NULL));
        }
        for (long i = 0; i < U; ++i) {
                ksize = sizeof i;
                vsize = rand() % maxsize;
                *(long *)key = i;
                keyb = (struct t2_buf){ .len = ksize,    .addr = &key };
                valb = (struct t2_buf){ .len = SOF(val), .addr = &val };
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
                keyb = (struct t2_buf){ .len = ksize,    .addr = &key };
                if (rand() & 1) {
                        fill(val, vsize);
                        valb = (struct t2_buf){ .len = vsize, .addr = &val };
                        result = t2_insert(t, &r, NULL);
                        ASSERT(result == 0 || result == -EEXIST);
                        if (result == -EEXIST) {
                                exist++;
                        }
                        inserts++;
                } else {
                        result = t2_delete(t, &r, NULL);
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
        mod = t2_init(ut_storage, NULL, HT_SHIFT, CA_SHIFT);
        ASSERT(EISOK(mod));
        ttype.mod = NULL;
        t2_tree_type_register(mod, &ttype);
        t2_node_type_register(mod, &ntype);
        t = t2_tree_create(&ttype, NULL);
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
                NOFAIL(t2_insert(t, &r, NULL));
        }
        utest("smoke");
        for (long i = 0, del = 0; i < U; ++i, del += 7, del %= U) {
                unsigned long ulongmax = ~0ul;
                struct t2_buf maxkey = BUF_VAL(ulongmax);
                keyb = BUF_VAL(del);
                valb = BUF_VAL(del);
                NOFAIL(t2_delete(t, &r, NULL));
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
        mod = t2_init(ut_storage, NULL, HT_SHIFT, CA_SHIFT);
        ASSERT(EISOK(mod));
        ttype.mod = NULL;
        t2_tree_type_register(mod, &ttype);
        t2_node_type_register(mod, &ntype);
        t = t2_tree_create(&ttype, NULL);
        ASSERT(EISOK(t));
        utest("populate");
        long U = 1000000;
        for (long i = 0; i < U; ++i) {
                keyb = BUF_VAL(key);
                valb = BUF_VAL(val);
                r.key = &keyb;
                r.val = &valb;
                NOFAIL(t2_insert(t, &r, NULL));
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
                int result = t2_insert_ptr(t, kbuf, ksize, vbuf, vsize, NULL);
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
                int result = t2_delete_ptr(t, kbuf, ksize, NULL);
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
                random_buf(startkey.addr, sizeof key, &startkey.len);
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
        mod = t2_init(ut_storage, NULL, HT_SHIFT, CA_SHIFT);
        ASSERT(EISOK(mod));
        ttype.mod = NULL;
        t2_tree_type_register(mod, &ttype);
        t2_node_type_register(mod, &ntype);
        t = t2_tree_create(&ttype, NULL);
        ASSERT(EISOK(t));
        utest("populate");
        for (long i = 0; i < OPS; ++i) {
                random_buf(kbuf, sizeof kbuf, &ksize);
                random_buf(vbuf, sizeof vbuf, &vsize);
                result = t2_insert_ptr(t, kbuf, ksize, vbuf, vsize, NULL);
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
        mod = t2_init(ut_storage, NULL, HT_SHIFT, CA_SHIFT);
        ASSERT(EISOK(mod));
        ttype.mod = NULL;
        t2_tree_type_register(mod, &ttype);
        t2_node_type_register(mod, &ntype);
        t = t2_tree_create(&ttype, NULL);
        ASSERT(EISOK(t));
        for (long i = 0; i < 4*OPS; ++i) {
                random_buf(kbuf, sizeof kbuf, &ksize);
                random_buf(vbuf, sizeof vbuf, &vsize);
                result = t2_insert_ptr(t, kbuf, ksize, vbuf, vsize, NULL);
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
        mod = t2_init(ut_storage, NULL, HT_SHIFT, CA_SHIFT);
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

static struct t2_node *fake_node = (void*)&open_ut;
static int lsnset_nr;
static int apply_nr;
static void *fdata;

static void wal_ut_lsnset(struct t2_node *node, lsn_t lsn) {
        ASSERT(node == fake_node && lsn > 0);
        ++lsnset_nr;
}

static int wal_ut_apply(struct t2 *mod, struct t2_txrec *txr) {
        ASSERT(fdata != NULL);
        memcpy(fdata + txr->off, txr->part.addr, txr->part.len);
        ++apply_nr;
        return 0;
}

enum {
        NODE_SHIFT = 10,
        NODE_SIZE  = 1 << NODE_SHIFT,
        OFF        = NODE_SIZE / 7,
        SIZE       = NODE_SIZE / 3,
        NR_BUFS    = 200,
        BUF_SIZE   = 1 << 20,
        FLAGS      = 0, /* noforce-nosteal == redo only. */
        NOPS       = 10
};

static const char logname[] = "log";

static uint64_t prev_key;
static uint64_t keys;

static int wal_cnext(struct t2_cursor *c, const struct t2_rec *rec) {
        uint64_t key = *(uint64_t *)rec->key->addr;
        uint64_t val = *(uint64_t *)rec->val->addr;
        ASSERT(rec->key->len == sizeof key);
        ASSERT(rec->val->len == sizeof val);
        ASSERT(prev_key == 0 || key == prev_key + 2);
        ++keys;
        prev_key = key;
        return +1;
}

static void wal_verify(struct t2_tree *t) {
        uint64_t key;
        uint64_t start = 0;
        struct t2_buf startkey = BUF_VAL(start);
        struct t2_cursor_op cop = {
                .next = &wal_cnext
        };
        struct t2_cursor c = {
                .curkey = BUF_VAL(key),
                .tree   = t,
                .dir    = T2_MORE,
                .op     = &cop
        };
        keys = 0;
        prev_key = 0;
        t2_cursor_init(&c, &startkey);
        while (t2_cursor_next(&c) > 0) {
                        ;
        }
        ASSERT(keys == NOPS / 2);
        t2_cursor_fini(&c);
}

static void wal_ut() {
        struct t2 *mod;
        struct t2_te *engine;
        struct t2_tx *tx;
        char fake_data[NODE_SIZE];
        char copy[NODE_SIZE];
        struct t2_txrec txr = {
                .node = fake_node,
                .addr = taddr_make(0x100000, NODE_SHIFT),
                .off  = OFF,
                .part = {
                        .addr = fake_data + txr.off,
                        .len  = SIZE
                }
        };
        struct t2_tree *t;
        int result;
        memset(fake_data, '#', SOF(fake_data));
        usuite("wal");
        lsnset_nr = 0;
        ut_lsnset = &wal_ut_lsnset;
        ut_apply  = &wal_ut_apply;
        utest("init");
        engine = wal_prep(logname, NR_BUFS, BUF_SIZE, FLAGS|MAKE);
        ASSERT(EISOK(engine));
        mod = t2_init(ut_storage, engine, HT_SHIFT, CA_SHIFT);
        ASSERT(EISOK(mod));
        t2_fini(mod);
        utest("add");
        engine = wal_prep(logname, NR_BUFS, BUF_SIZE, FLAGS|MAKE);
        ASSERT(EISOK(engine));
        mod = t2_init(ut_storage, engine, HT_SHIFT, CA_SHIFT);
        ASSERT(EISOK(mod));
        tx = t2_tx_make(mod);
        ASSERT(EISOK(tx));
        result = wal_post(engine, tx, txr.part.len, 1, &txr);
        ASSERT(result == 0);
        t2_tx_done(mod, tx);
        t2_fini(mod);
        utest("add-many");
        engine = wal_prep(logname, NR_BUFS, BUF_SIZE, FLAGS|MAKE);
        ASSERT(EISOK(engine));
        mod = t2_init(ut_storage, engine, HT_SHIFT, CA_SHIFT);
        ASSERT(EISOK(mod));
        tx = t2_tx_make(mod);
        ASSERT(EISOK(tx));
        for (int i = 0; i < 100000; ++i) {
                txr.off = rand() % (NODE_SIZE - 10);
                txr.part.addr = fake_data + txr.off;
                txr.part.len  = rand() % (NODE_SIZE - txr.off - 1);
                result = wal_post(engine, tx, txr.part.len, 1, &txr);
                ASSERT(result == 0);
        }
        t2_tx_done(mod, tx);
        t2_fini(mod);
        utest("replay");
        fdata = fake_data;
        engine = wal_prep(logname, NR_BUFS, BUF_SIZE, FLAGS|MAKE|KEEP);
        ASSERT(EISOK(engine));
        mod = t2_init(ut_storage, engine, HT_SHIFT, CA_SHIFT);
        ASSERT(EISOK(mod));
        tx = t2_tx_make(mod);
        ASSERT(EISOK(tx));
        for (int i = 0; i < 100000; ++i) {
                txr.off = rand() % (NODE_SIZE - 10);
                txr.part.addr = fake_data + txr.off;
                txr.part.len  = rand() % (NODE_SIZE - txr.off - 1);
                memset(txr.part.addr, 'A' + rand() % ('Z' - 'A' + 1), txr.part.len);
                result = wal_post(engine, tx, txr.part.len, 1, &txr);
                ASSERT(result == 0);
        }
        t2_tx_done(mod, tx);
        t2_fini(mod);
        memcpy(copy, fake_data, SOF(copy));
        memset(fake_data, '#', SOF(fake_data));
        apply_nr = 0;
        engine = wal_prep(logname, NR_BUFS, BUF_SIZE, FLAGS);
        ASSERT(EISOK(engine));
        mod = t2_init(ut_storage, engine, HT_SHIFT, CA_SHIFT);
        ASSERT(EISOK(mod));
        ASSERT(memcmp(copy, fake_data, SOF(copy)) == 0);
        ASSERT(apply_nr == 100000);
        t2_fini(mod);
        ut_lsnset = NULL;
        ut_apply = NULL;
        utest("tree-create");
        engine = wal_prep(logname, NR_BUFS, BUF_SIZE, FLAGS|MAKE);
        ASSERT(EISOK(engine));
        mod = t2_init(ut_storage, engine, HT_SHIFT, CA_SHIFT);
        ASSERT(EISOK(mod));
        ttype.mod = NULL;
        t2_tree_type_register(mod, &ttype);
        t2_node_type_register(mod, &ntype);
        tx = t2_tx_make(mod);
        ASSERT(EISOK(tx));
        t = t2_tree_create(&ttype, tx);
        ASSERT(EISOK(t));
        t2_tree_close(t);
        t2_tx_done(mod, tx);
        t2_tree_type_degister(&ttype);
        t2_node_type_degister(&ntype);
        t2_fini(mod);
        utest("replay-ops");
        engine = wal_prep(logname, NR_BUFS, BUF_SIZE, FLAGS|MAKE|KEEP);
        ASSERT(EISOK(engine));
        mod = t2_init(ut_storage, engine, HT_SHIFT, CA_SHIFT);
        ASSERT(EISOK(mod));
        ttype.mod = NULL;
        t2_tree_type_register(mod, &ttype);
        t2_node_type_register(mod, &ntype);
        tx = t2_tx_make(mod);
        ASSERT(EISOK(tx));
        result = t2_tx_open(mod, tx);
        ASSERT(result == 0);
        t = t2_tree_create(&ttype, tx);
        ASSERT(EISOK(t));
        t2_tree_close(t);
        for (uint64_t k = 0; k < NOPS; ++k) {
                result = t2_tx_open(mod, tx);
                ASSERT(result == 0);
                result = t2_insert_ptr(t, &k, SOF(k), &k, SOF(k), tx);
                ASSERT(result == 0);
                t2_tx_close(mod, tx);
        }
        for (uint64_t k = 0; k < NOPS; k += 2) {
                result = t2_tx_open(mod, tx);
                ASSERT(result == 0);
                result = t2_delete_ptr(t, &k, SOF(k), tx);
                ASSERT(result == 0);
                t2_tx_close(mod, tx);
        }
        t2_tx_done(mod, tx);
        wal_verify(t);
        t2_tree_type_degister(&ttype);
        t2_node_type_degister(&ntype);
        t2_fini(mod);
        utestdone();
}

int main(int argc, char **argv) {
        argv0 = argv[0];
        setbuf(stdout, NULL);
        setbuf(stderr, NULL);
        wal_ut();
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
        wal_ut();
        counters_print();
        return 0;
}

#endif /* UT */

/*
 * To do:
 *
 * - integrate rcu: https://github.com/urcu/userspace-rcu/blob/master/include/urcu/rculist.h (rculfhash.c)
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
 * ! replace cookie with get(), benchmark (sigprocmask is expensive).
 *
 * + abstract node and tree type operations (no direct simple_* calls)
 *
 * ! multi-segment buffers
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
 *
 * - C. Mohan et al., ARIES: a transaction recovery method supporting
 *   fine-granularity locking and partial rollbacks using write-ahead logging
 *   (https://dl.acm.org/doi/10.1145/128765.128770)
 *
 * - J. Gray, A. Reuter, Transaction Processing: Concepts and Techniques
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
