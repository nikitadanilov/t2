/* -*- C -*- */

/*
 * https://github.com/urcu/userspace-rcu/blob/master/include/urcu/rculist.h
 *
 * Simple node functions should be robust in the face of concurrent modifications.
 */

#include <stdbool.h>
#include <assert.h>
#include <stdlib.h>
#include <stdarg.h>
#include <errno.h>
#include <string.h>
#include <stdio.h>
#include <ctype.h>
#include "t2.h"

enum {
        MAX_TREE_HEIGHT =   10,
        MAX_TREE_TYPE   = 1024,
        MAX_ERR_CODE    = 1024
};

struct msg_ctx {
        const char *func;
        const char *file;
        int         lineno;
        const char *fmt;
};

static void immanentise(const struct msg_ctx *ctx, ...) __attribute__((noreturn));
static void *mem_alloc(size_t size);
static void  mem_free(void *ptr);
static void llog(const struct msg_ctx *ctx, ...);

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
        struct t2_storage         *stor;
        struct ht                  ht;
};

/*
 * "Address" of a node on storage.
 *
 * Highest 8 bits (56--63) are reserved and must be 0.
 *
 * Lowest 4 bits (0--3) contains the node size, see below.
 *
 * Next 5 bits (4--8) are reserved and must be 0.
 *
 * Remaining 47 (9--55) bits contain the address on the storage.
 *
 * @verbatim
 *
 *  6      5 5                                            0 0   0 0  0
 *  3      6 5                                            9 8   4 3  0
 * +--------+----------------------------------------------+-----+----+
 * |   0    |                     ADDR                     |  0  | X  |
 * +--------+----------------------------------------------+-----+----+
 *
 * @endverbatim
 *
 * Node size is 2^(9+X) bytes (i.e., the smallest node is 512 bytes and the
 * largest node is 2^(9+15) == 16MB).
 *
 * Node address is ADDR << 9.
 *
 * This allows for 128T nodes (2^47) and total of 64PB (2^56) of meta-data per
 * segment.
 */
typedef uint64_t taddr_t;

struct t2_tree {
        struct t2_tree_type *ttype;
        taddr_t root;
};

static void link_init(struct link *l) {
        l->next = l->prev = l;
}

static void link_fini(struct link *l) {
        ASSERT(l->next == l && l->prev == l);
}

static int  ht_init(struct ht *ht, int shift);
static void ht_fini(struct ht *ht);
static struct node *ht_lookup(struct ht *ht, taddr_t addr);
static void ht_insert(struct ht *ht, struct node *n);
static void ht_delete(struct node *n);

struct t2 *t2_init(struct t2_storage *storage, int hshift) {
        int result;
        struct t2 *mod = mem_alloc(sizeof *mod);
        if (mod != NULL) {
                mod->stor = storage;
                result = storage->op->init(storage);
                if (result == 0) {
                        result = ht_init(&mod->ht, hshift);
                        if (result != 0) {
                                storage->op->fini(storage);
                        }
                }
        } else {
                result = -ENOMEM;
        }
        if (result != 0) {
                mem_free(mod);
                return EPTR(result);
        } else {
                return mod;
        }
}

void t2_fini(struct t2 *mod) {
        ht_fini(&mod->ht);
        mod->stor->op->fini(mod->stor);
        mem_free(mod);
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

static void tree_init(struct t2_tree *t, struct t2_tree_type *ttype, taddr_t root) {
        t->ttype = ttype;
        t->root = root;
}

struct t2_tree *t2_tree_create(struct t2_tree_type *ttype) {
        struct t2_tree *t = mem_alloc(sizeof *t);
        if (t != NULL) {
                int      shift;
                uint64_t addr = SCALL(ttype->mod, alloc, ttype->root_min, ttype->root_max, &shift);
                if (EISOK(addr)) {
                        tree_init(t, ttype, taddr_make(addr, shift));
                        return t;
                } else {
                        return EPTR(addr);
                }
        } else {
                return EPTR(-ENOMEM);
        }
}

enum optype {
        LOOKUP,
        DELETE,
        INSERT,
        NEXT
};

static int cookie_try(struct t2_tree *t, struct t2_rec *r, enum optype opt) {
        return -ESTALE;
}

struct node_type {
        const char *name;
        int         shift;
};

struct node {
        struct link             hash;
        uint64_t                seq;
        const struct node_type *ntype;
        taddr_t                 addr;
        void                   *data;
        int                     level;
};

enum lock_mode {
        NONE,
        READ,
        WRITE
};

enum rung_flags {
        PINNED = 1ull << 0
};

struct rung {
        struct node   *node;
        uint64_t       seq;
        uint64_t       flags;
        int            pos;
};

struct path {
        int         used;
        struct rung rung[MAX_TREE_HEIGHT];
};

static uint64_t node_seq(const struct node *n) {
        /* Barrier? */
        return n->seq;
}

static bool path_is_valid(const struct path *p) {
        return FORALL(i, p->used, node_seq(p->rung[i].node) == p->rung[i].seq);
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

static void put(struct node *n);

static void lock(struct node *n, enum lock_mode mode) {
};

static void unlock(struct node *n, enum lock_mode mode) {
};

static void path_fini(struct path *p) {
        for (int i = 0; i < p->used; ++i) {
                struct rung *r = &p->rung[i];
                uint64_t flags = r->flags;
                if ((flags >> 32) != 0) {
                        unlock(r->node, flags >> 32);
                }
                if (r->flags & PINNED) {
                        put(r->node);
                }
        }
        SET0(p);
}

static struct node *peek(struct t2 *mod, taddr_t addr) {
        return ht_lookup(&mod->ht, addr);
}

static struct node *get(struct t2 *mod, taddr_t addr) {
        struct node *n = ht_lookup(&mod->ht, addr);
        if (n == NULL) {
        }
        return NULL;
}

static void put(struct node *n) {
}

static int load(struct node *n) {
        return 0;
}

static bool is_leaf(const struct node *n) {
        return n->level == 0;
}

struct slot {
	struct node   *node;
	int            idx;
	struct t2_rec  rec;
};

static taddr_t internal_search(struct node *n, struct t2_rec *r, int *pos);
static int leaf_search(struct node *n, struct t2_rec *r, struct slot *s);

struct tree_op {
        struct t2_tree *tree;
        enum optype     opt;
        struct t2_rec  *rec;
        struct path     path;
};

static void op_init(struct tree_op *top, struct t2_tree *t, struct t2_rec *r, enum optype opt) {
        ASSERT(IS0(top));
        top->tree = t;
        top->rec  = r;
        top->opt  = opt;
}

static void op_fini(struct tree_op *top) {
        path_fini(&top->path);
}

static bool op_is_valid(const struct tree_op *top) {
        const struct path *p = &top->path;
        return p->used > 0 && is_leaf(p->rung[p->used - 1].node) &&
                top->tree->root == p->rung[0].node->addr &&
                path_is_valid(&top->path);
}

static void rcu_lock(void) {
};

static void rcu_unlock(void) {
};

static void op_lock(struct tree_op *top) {
}

static int val_copy(struct t2_rec *r, struct node *n, struct slot *s);


static int lookup_complete(struct tree_op *top, struct node *n, struct t2_rec *r) {
        struct t2_buf key;
        struct t2_buf val;
        struct slot s = { .rec = { .key = &key, .val = &val } };
        return leaf_search(n, r, &s) ?: val_copy(r, n, &s);
}

static int insert_complete(struct tree_op *top, struct node *n, struct t2_rec *r, struct slot *s, int result) {
        return 0;
}

static int delete_complete(struct tree_op *top, struct node *n, struct t2_rec *r, struct slot *s, int result) {
        return 0;
}

static int next_complete(struct tree_op *top, struct node *n, struct t2_rec *r, struct slot *s, int result) {
        return 0;
}

static int op_complete(struct tree_op *top, struct node *n, struct t2_rec *r) {
        struct t2_buf key;
        struct t2_buf val;
        struct slot s = { .rec = { .key = &key, .val = &val } };
        int result = leaf_search(n, r, &s);
        switch (top->opt) {
        case INSERT:
                result = insert_complete(top, n, r, &s, result);
                break;
        case DELETE:
                result = delete_complete(top, n, r, &s, result);
                break;
        case NEXT:
                result = next_complete(top, n, r, &s, result);
                break;
        default:
                IMMANENTISE("Wrong opt: %i", top->opt);
        }
        return result;
}

static int traverse(struct tree_op *top) {
        int      result;
        uint64_t next;
        struct path *p = &top->path;
        struct t2 *mod = top->tree->ttype->mod;
        ASSERT(p->used == 0);
        rcu_lock();
        while (true) {
                struct node *n;
                struct rung *r;
                uint64_t     flags = 0;
                if (p->used == 0) {
                        next = top->tree->root;
                }
                n = peek(mod, next);
                if (EISERR(n)) {
                        result = ERROR(ERRCODE(n));
                        break;
                } else if (n == NULL) {
                        n = get(mod, next);
                        if (EISERR(n)) {
                                if (ERRCODE(n) == -ESTALE) {
                                        op_fini(top);
                                        continue;
                                } else {
                                        result = ERROR(ERRCODE(n));
                                        break;
                                }
                        } else {
                                flags |= PINNED;
                        }
                }
                r = path_add(p, n, node_seq(n), flags);
                if (is_leaf(n)) {
                        if (top->opt == LOOKUP) {
                                result = lookup_complete(top, n, top->rec);
                                if (!op_is_valid(top)) {
                                        op_fini(top);
                                } else {
                                        break;
                                }
                        } else {
                                op_lock(top); /* Take locks as needed. */
                                if (op_is_valid(top)) {
                                        result = op_complete(top, n, top->rec);
                                        break;
                                } else {
                                        op_fini(top);
                                }
                        }
                } else {
                        int pos;
                        next = internal_search(n, top->rec, &r->pos);
                        if (EISERR(next)) {
                                result = ERROR(ERRCODE(next));
                                break;
                        }
                }
        }
        rcu_unlock();
        return result;
}

static int lookup(struct t2_tree *t, struct t2_rec *r) {
        int result = cookie_try(t, r, LOOKUP);
        if (result != -ESTALE) {
                return ERROR(result);
        } else {
                struct tree_op top = {};
                op_init(&top, t, r, LOOKUP);
                result = traverse(&top);
                op_fini(&top);
                return result;
        }
}

int t2_lookup(struct t2_tree *t, struct t2_rec *r) {
        return lookup(t, r);
}

int t2_delete(struct t2_tree *t, struct t2_rec *r) {
        return 0;
}

int t2_insert(struct t2_tree *t, struct t2_rec *r) {
        return 0;
}

__attribute__((noreturn)) static void immanentise(const struct msg_ctx *ctx, ...)
{
        va_list args;
        fprintf(stderr, "%s (%s/%i): Immanentising the eschaton: ", ctx->func, ctx->file, ctx->lineno);
        va_start(args, ctx);
        vfprintf(stderr, ctx->fmt, args);
        va_end(args);
        puts(".\n");
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

static void  mem_free(void *ptr) {
        free(ptr);
}

static void llog(const struct msg_ctx *ctx, ...) {
        va_list args;
        fprintf(stderr, "%s (%s/%i): ", ctx->func, ctx->file, ctx->lineno);
        va_start(args, ctx);
        vfprintf(stderr, ctx->fmt, args);
        va_end(args);
        puts(".\n");
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
        return -ENOMEM;
}

static void ht_fini(struct ht *ht) {
        for (int i = 0; i < (1 << ht->shift); i++) {
                link_fini(&ht->chains[i]);
        }
        mem_free(ht->chains);
}

static unsigned ht_hash(taddr_t addr) {
        return 0;
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

enum {
        NODE_MAGIX = 0x1f2e3d4c
};

struct header {
        uint32_t magix;
        uint32_t csum;
        uint16_t ntype;
        uint8_t  level;
        uint8_t  pad;
        uint64_t treeid[2];
};

struct dir_element {
        uint32_t koff; /* Start of the key. */
        uint32_t voff; /* End of the value. */
};

struct sheader { /* Simple node format. */
        struct header head;
        uint32_t      dir_off;
        uint16_t      nr;
        uint16_t      pad;
};

static void simple_print(struct node *n);

static struct dir_element *sdir(struct sheader *sh) {
        return (void *)sh + sh->dir_off;
}

static struct dir_element *sat(struct sheader *sh, int pos) {
        return sdir(sh) + pos;
}

static bool is_in(uint32_t lo, uint32_t v, uint32_t hi) {
        return lo <= v && v <= hi;
}

static bool scheck(struct sheader *sh, struct node_type *nt) {
        uint32_t size = 1ul << nt->shift;
        uint32_t dend = sh->dir_off + (sh->nr + 1) * sizeof(struct dir_element);
        return  is_in(sizeof *sh, sh->dir_off, size) &&
                is_in(sizeof *sh, dend, size) &&
                FORALL(i, sh->nr + 1,
                       is_in(sizeof *sh, sat(sh, i)->koff, sh->dir_off) &&
                       is_in(dend, sat(sh, i)->voff, size));
                FORALL(i, sh->nr,
                       sat(sh, i)->koff  < sat(sh, i + 1)->koff &&
                       sat(sh, i)->voff >= sat(sh, i + 1)->voff);
}

static uint32_t sdirsize(struct sheader *sh) {
        return (sh->nr + 1) * sizeof(struct dir_element);
}

static uint32_t sdirend(struct sheader *sh) {
        return sh->dir_off + sdirsize(sh);
}

static void *skey(struct sheader *sh, int pos, uint32_t *size) {
        ASSERT(0 <= pos && pos < sh->nr);
        struct dir_element *del = sat(sh, pos);
        *size = sat(sh, pos + 1)->koff - del->koff;
        return (void *)sh + del->koff;
}

static void *sval(struct sheader *sh, int pos, uint32_t *size) {
        ASSERT(0 <= pos && pos < sh->nr);
        struct dir_element *del = sat(sh, pos + 1);
        *size = sat(sh, pos)->voff  - del->voff;
        return (void *)sh + del->voff;
}

static char cmpch(int cmp) {
        return cmp < 0 ? '<' : cmp == 0 ? '=' : '>';
}

static void print_range(void *orig, uint32_t nsize, void *start, uint32_t nob, bool oct);

static int skeycmp(struct sheader *sh, int pos, void *key, uint32_t klen) {
        uint32_t ksize;
        void *kstart = skey(sh, pos, &ksize);
        if (pos == -1) {
                return -1;
        } else if (pos == sh->nr) {
                return +1;
        } else {
                return memcmp(kstart, key, ksize < klen ? ksize : klen) ?:
                        ksize < klen ? -1 : klen != ksize; /* sic. */
        }
}

static struct sheader *simple_header(struct node *n) {
        return n->data;
}

static bool simple_search(struct node *n, struct t2_rec *rec, struct slot *out) {
        ASSERT(rec->key->nr == 1);
        bool            found = false;
        struct sheader *sh    = simple_header(n);
        int             l     = -1;
        int             r     = sh->nr;
        struct t2_buf  *key   = out->rec.key;
        struct t2_buf  *val   = out->rec.val;
        int             cmp;
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

static taddr_t internal_search(struct node *n, struct t2_rec *r, int *pos) {
        struct t2_buf key;
        struct t2_buf val;
        struct slot s = { .rec = { .key = &key, .val = &val } };
        (void)simple_search(n, r, &s);
        ASSERT(val.nr > 0 && val.seg[0].len > sizeof(taddr_t));
        return *(taddr_t *)val.seg[0].addr;
}

static int leaf_search(struct node *n, struct t2_rec *r, struct slot *s) {
        return simple_search(n, r, s);
}

static void buf_copy(const struct t2_buf *dst, const struct t2_buf *src);
static uint32_t buf_len(const struct t2_buf *b);

static int val_copy(struct t2_rec *r, struct node *n, struct slot *s) { /* r := s */
        struct t2_buf *key    = s->rec.key;
        struct t2_buf *val    = s->rec.val;
        int            result = 0;
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

static uint32_t sfreekey(struct node *n) {
        struct sheader *sh  = simple_header(n);
        return sh->dir_off - sat(sh, sh->nr)->koff;
}

static uint32_t sfreeval(struct node *n) {
        struct sheader *sh  = simple_header(n);
        return sat(sh, sh->nr)->voff - sdirend(sh);
}

static uint32_t simple_free(struct node *n) {
        struct sheader     *sh  = simple_header(n);
        struct dir_element *end = sat(sh, sh->nr);
        return end->voff - end->koff - sdirsize(sh);
}

static uint32_t min_u32(uint32_t a, uint32_t b) {
        return a < b ? a : b;
}

static uint32_t max_u32(uint32_t a, uint32_t b) {
        return a > b ? a : b;
}

static uint32_t buf_len(const struct t2_buf *b) {
        uint32_t len = 0;
        for (int i = 0; i < b->nr; ++i) {
                len += b->seg[i].len;
        }
        return len;
}

static void buf_copy(const struct t2_buf *dst, const struct t2_buf *src) {
        int      didx = 0;
        uint32_t doff = 0;
        int      sidx = 0;
        uint32_t soff = 0;
        ASSERT(buf_len(dst) >= buf_len(src));
        while (sidx < src->nr && didx < dst->nr) {
                uint32_t nob = min_u32(src->seg[sidx].len - soff, dst->seg[didx].len - doff);
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

static void move(void *sh, uint32_t start, uint32_t end, int delta) {
        ASSERT(start <= end);
        memmove(sh + start + delta, sh + start, end - start);
}

static void sdirmove(struct sheader *sh, uint32_t nsize,
                     uint32_t knob, uint32_t vnob, uint32_t nr) {
        uint32_t dir_off = (knob * (nsize - sizeof *sh)) / (knob + vnob) -
                nr * sizeof(struct dir_element) / 2 + sizeof *sh;
        dir_off = max_u32(dir_off, knob + sizeof *sh);
        ASSERT(dir_off + nr * sizeof(struct dir_element) + vnob <= nsize);
        move(sh, sh->dir_off, sdirend(sh), dir_off - sh->dir_off);
        sh->dir_off = dir_off;
}

static int simple_insert(struct slot *s) {
        struct t2_buf       buf;
        struct sheader     *sh   = simple_header(s->node);
        struct dir_element *end  = sat(sh, sh->nr);
        struct dir_element *piv  = sat(sh, s->idx);
        uint32_t            klen = buf_len(s->rec.key);
        uint32_t            vlen = buf_len(s->rec.val);
        ASSERT(s->idx <= sh->nr);
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
        for (uint32_t i = ++sh->nr; i > s->idx; --i) {
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
        return 0;
}

static void simple_delete(struct slot *s) {
        struct sheader     *sh   = simple_header(s->node);
        struct dir_element *end  = sat(sh, sh->nr);
        struct dir_element *piv  = sat(sh, s->idx);
        struct dir_element *inn  = sat(sh, s->idx + 1);
        uint32_t            klen = inn->koff - piv->koff;
        uint32_t            vlen = piv->voff - inn->voff;
        ASSERT(s->idx < sh->nr);
        move(sh, inn->koff, end->koff, -klen);
        move(sh, end->voff, inn->voff, +vlen);
        for (uint32_t i = s->idx; i < sh->nr; ++i) {
                struct dir_element *next = sat(sh, i + 1);
                *sat(sh, i) = (struct dir_element){
                        .koff = next->koff - klen,
                        .voff = next->voff + vlen
                };
        }
        --sh->nr;
}

static void simple_get(struct slot *s) {
        struct sheader *sh = simple_header(s->node);
        ASSERT(s->idx < sh->nr);
        s->rec.key->nr = 1;
        s->rec.val->nr = 1;
        s->rec.key->seg[0].addr = skey(sh, s->idx, &s->rec.key->seg[0].len);
        s->rec.val->seg[0].addr = sval(sh, s->idx, &s->rec.val->seg[0].len);
}

static void simple_make(struct node *n) {
        uint32_t        nsize = 1ul << n->ntype->shift;
        struct sheader *sh    = simple_header(n);
        ASSERT(IS0(sh));
        sh->dir_off = sizeof *sh + (nsize - sizeof *sh) / 2;
        *sat(sh, 0) = (struct dir_element){ .koff = sizeof *sh, .voff = nsize };
}

static void print_range(void *orig, uint32_t nsize, void *start, uint32_t nob, bool oct) {
        uint32_t off = start - orig;
        printf("[%u %u ", off, off + nob);
        if (is_in(0, off, nsize) &&
            is_in(0, off + nob, nsize)) {
                for (uint32_t i = 0; i < nob; ++i) {
                        int ch = ((char *)orig)[off + i];
                        if (isprint(ch) && !oct) {
                                printf("%c", ch);
                        } else {
                                printf("\\%03o", ch & 0xff);
                        }
                }
        } else {
                printf("out of range");
        }
        printf("]");
}

static void simple_print(struct node *n) {
        uint32_t        nsize = 1ul << n->ntype->shift;
        struct sheader *sh    = simple_header(n);
        printf("nr: %u size: %u dir_off: %u dir_end: %u\n",
               sh->nr, nsize, sh->dir_off, sdirend(sh));
        for (uint32_t i = 0; i <= sh->nr; ++i) {
                struct dir_element *del = sat(sh, i);
                uint32_t            size;
                printf("        %4u %4u %4u: ", i, del->koff, del->voff);
                if (i < sh->nr) {
                        print_range(sh, nsize, skey(sh, i, &size), size, false);
                        printf(" ");
                        print_range(sh, nsize, sval(sh, i, &size), size, false);
                }
                printf("\n");
        }
}
static void usuite(const char *suite) {
        printf("        %s\n", suite);
}

static int ok;
static int failed;
static const char *test = NULL;

static void utestdone(void) {
        printf("                %c %-15s %6i %6i\n", failed == 0 ? '+' : '.', test, ok, failed);
        test = NULL;
}

static void utest(const char *t) {
        if (test != NULL) {
                utestdone();
        }
        ok = failed = 0;
        test = t;
}

static void ufail(const char *cond) {
        ++failed;
        printf("                        Failed: %s\n", cond);
}


#define UASSERT(cond) ((cond) ? ++ok : ufail(#cond))

static void populate(struct slot *s, struct t2_buf *key, struct t2_buf *val) {
        struct sheader *sh = simple_header(s->node);
        for (uint32_t i = 0; simple_free(s->node) >
                     buf_len(key) + buf_len(val) + sizeof(struct dir_element); ++i) {
                UASSERT(simple_insert(s) == 0);
                UASSERT(sh->nr == i + 1);
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

static bool is_sorted(struct node *n, int maxkey) {
        struct sheader *sh = simple_header(n);
        struct t2_buf kk;
        struct t2_buf vv;
        struct slot ss = {
                .node = n,
                .rec = { .key = &kk, .val = &vv }
        };
        char keyarea[maxkey];
        memset(keyarea, 0, sizeof keyarea);
        for (uint32_t i = 0; i < sh->nr; ++i) {
                ss.idx = i;
                simple_get(&ss);
                UASSERT(ss.rec.key->seg[0].len <= sizeof keyarea);
                if (i > 0) {
                        int cmp = memcmp(keyarea, ss.rec.key->seg[0].addr,
                                         ss.rec.key->seg[0].len);
                        if (cmp >= 0) {
                                printf("Misordered at %i: ", i);
                                print_range(keyarea, sizeof keyarea,
                                            keyarea, sizeof keyarea, true);
                                printf(" %c ", cmpch(cmp));
                                print_range(n->data, 1ul << n->ntype->shift,
                                            ss.rec.key->seg[0].addr,
                                            ss.rec.key->seg[0].len, true);
                                printf("\n");
                                simple_print(n);
                                return false;
                        }
                }
                memcpy(keyarea, ss.rec.key->seg[0].addr, ss.rec.key->seg[0].len);
        }
        return true;
}

static void simple_ut(void) {
        int result;
        struct node_type ntype = {
                .name  = "simple-ut",
                .shift = 9
        };
        char body[1ul << ntype.shift];
        struct node n = {
                .ntype = &ntype,
                .addr  = taddr_make(0x100000, ntype.shift),
                .data  = body,
                .level = 0
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
        usuite("simple node");
        utest("make");
        simple_make(&n);
        UASSERT(sh->nr == 0);
        utest("insert");
        populate(&s, &key, &val);
        UASSERT(simple_insert(&s) == -ENOSPC);
        utest("get");
        for (uint32_t i = 0; i < sh->nr; ++i) {
                s.idx = i;
                simple_get(&s);
                UASSERT(buf_len(s.rec.key) == strlen(key0) + 1);
                UASSERT(buf_len(s.rec.val) == strlen(val0) + 1);
        }
        utest("delete");
        for (int32_t i = sh->nr - 1; i >= 0; --i) {
                s.idx = (s.idx + 7) % sh->nr;
                simple_delete(&s);
                UASSERT(sh->nr == i);
        }
        utest("search");
        key0[1] = 'a';
        for (uint32_t i = 0; simple_free(&n) >
                     buf_len(&key) + buf_len(&val) + sizeof(struct dir_element); ++i) {
                UASSERT(!simple_search(&n, &s.rec, &s));
                s.idx++;
                buf_init_str(&key, key0);
                buf_init_str(&val, val0);
                UASSERT(simple_insert(&s) == 0);
                UASSERT(is_sorted(&n, sizeof key0));
                key0[1] += 251; /* Co-prime with 512. */
                val0[1]++;
        }
        utestdone();
}

int main(int argc, char **argv) {
        simple_ut();
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
