/* -*- C -*- */

/* See https://github.com/nikitadanilov/t2/blob/master/LICENCE for licencing information. */

#include <math.h>
#include <pthread.h>
#include <stdarg.h>
#include <stdio.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <unistd.h>
#include <sys/time.h>
#include "t2.h"

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

#define NOFAIL(expr)                                            \
({                                                              \
        int result = (expr);                                    \
        if (result != 0) {                                      \
                printf(#expr " failed with %i.\n", result);     \
                assert(false);                                  \
        }                                                       \
})

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

#define SET0(obj)                               \
({                                              \
        SASSERT(!IS_ARRAY(obj));                \
        memset((obj), 0, sizeof *(obj));        \
})

#define IS0(obj) FORALL(i, sizeof *(obj), ((char *)obj)[i] == 0)

#define SASSERT(cond) _Static_assert((cond), #cond)

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

struct bvar {
        uint64_t nr;
        uint64_t sum;
        uint64_t min;
        uint64_t max;
        uint64_t ssq;
};

struct bthread;

struct rthread {
        pthread_t self;
        struct bthread *parent;
        int idx;
        bool ready;
};

enum bop_type {
        BSLEEP,
        BLOOKUP,
        BINSERT,
        BDELETE,
        BNEXT,
        BREMOUNT
};

enum border {
        RND,
        EXI,
        SEQ
};

struct bspec {
        enum border ord;
        int min;
        int max;
};

struct boption {
        enum bop_type opt;
        int delay;
        int iter;
        struct bspec key;
        struct bspec val;
        struct bvar  var;
        struct bvar  prev;
};

struct bchoice {
        int percent;
        struct boption option;
};

struct bthread {
        int nr;
        struct bchoice *choice;
        struct bgroup *parent;
        struct rthread *rt;
};

struct bgroup {
        int nr;
        int ops;
        struct bthread thread;
        struct bphase *parent;
        int idx;
};

struct bphase {
        int nr;
        struct bgroup *group;
        pthread_mutex_t lock;
        pthread_cond_t cond;
        pthread_cond_t start;
        struct benchmark *parent;
        bool run;
};

struct benchmark {
        int nr;
        struct bphase *phase;
        uint64_t seed;
        struct t2 *mod;
        struct t2_tree *tree;
};

struct span {
        const char *start;
        const char *end;
};

#define SPAN(s, e) ((const struct span) { .start = (s), .end = (e) })

static const char *total;

enum {
        BRESULTS,
        BPROGRESS,
        BINFO,
        BTRACE,
        BDEBUG
};

extern struct t2_storage *bn_storage;
extern taddr_t bn_tree_root(const struct t2_tree *t);
extern uint64_t bn_file_free(struct t2_storage *storage);
extern void bn_file_free_set(struct t2_storage *storage, uint64_t free);
extern void bn_counters_print(void);

static void *mem_alloc(size_t size) {
        void *out = malloc(size);
        assert(out != NULL);
        memset(out, 0, size);
        return out;
}

static void mem_free(void *ptr) {
        free(ptr);
}

static void mutex_lock(pthread_mutex_t *lock) {
        NOFAIL(pthread_mutex_lock(lock));
}

static void mutex_unlock(pthread_mutex_t *lock) {
        NOFAIL(pthread_mutex_unlock(lock));
}

static int blog_level = BRESULTS;
static void blog(int level, const char *fmt, ...) {
        if (level <= blog_level) {
                va_list args;
                va_start(args, fmt);
                vfprintf(stdout, fmt, args);
                va_end(args);
        }
}

static void logspan(const struct span *s) {
        blog(BDEBUG, "%s\n", total);
        for (const char *c = total; c < s->start; ++c) {
                blog(BDEBUG, " ");
        }
        blog(BDEBUG, "^");
        for (const char *c = s->start + 1; c < s->end; ++c) {
                blog(BDEBUG, ".");
        }
        blog(BDEBUG, "^\n");
}

static void bskip(struct span *s) {
        while (s->start < s->end && *s->start == ' ') {
                s->start++;
        }
}

static int span_nr(const struct span *s, char delim) {
        return COUNT(i, s->end - s->start, s->start[i] == delim) + 1;
}

static struct span *span_next(const struct span *super, char delim, struct span *sub) {
        logspan(super);
        if (sub->start == NULL) {
                sub->start = sub->end = super->start;
        } else {
                sub->start = ++sub->end; /* Skip delimiter. */
        }
        if (sub->start >= super->end) {
                return NULL;
        }
        while (sub->end < super->end && *sub->end != delim) {
                sub->end++;
        }
        bskip(sub);
        return sub;
}

static int bnumber(struct span *s) {
        char *end;
        errno = 0;
        long n = strtol(s->start, &end, 0);
        logspan(s);
        bskip(s);
        assert((n != 0 || errno == 0) && end <= s->end);
        s->start = end;
        return n;
}

static bool bstarts(struct span *s, const char *prefix) {
        int len = strlen(prefix);
        logspan(s);
        bskip(s);
        if (s->start + len <= s->end && strncmp(s->start, prefix, len) == 0) {
                s->start += len;
                return true;
        } else {
                return false;
        }
}

static void bspec_parse(struct bspec *sp, struct span *s) {
        struct span sub = {};
        logspan(s);
        if (bstarts(s, "rnd")) {
                sp->ord = RND;
        } else if (bstarts(s, "exi")) {
                sp->ord = EXI;
        } else if (bstarts(s, "seq")) {
                sp->ord = SEQ;
        } else {
                puts("Cannot parse spec.");
                assert(false);
        }
        if (span_nr(s, '-') != 2) {
                puts(s->start);
        }
        sp->min = bnumber(span_next(s, '-', &sub));
        sp->max = bnumber(span_next(s, '-', &sub));
        s->start = sub.end;
}

static void boption_parse(struct boption *o, const struct span *s) {
        struct span sub = {};
        struct span rest = *s;
        logspan(s);
        if (bstarts(&rest, "sleep$")) {
                o->opt = BSLEEP;
                o->delay = bnumber(&rest);
        } else if (bstarts(&rest, "lookup$")) {
                o->opt = BLOOKUP;
                bspec_parse(&o->key, span_next(&rest, '/', &sub));
                o->val.max = bnumber(span_next(&rest, '/', &sub));
        } else if (bstarts(&rest, "insert$")) {
                o->opt = BINSERT;
                bspec_parse(&o->key, span_next(&rest, '/', &sub));
                bspec_parse(&o->val, span_next(&rest, '/', &sub));
        } else if (bstarts(&rest, "delete$")) {
                o->opt = BDELETE;
                bspec_parse(&o->key, &rest);
        } else if (bstarts(&rest, "next$")) {
                o->opt = BNEXT;
                bspec_parse(&o->key, span_next(&rest, '/', &sub));
                o->iter = bnumber(span_next(&rest, '/', &sub));
        } else if (bstarts(&rest, "remount$")) {
                o->opt = BREMOUNT;
        } else {
                puts("Unknown option.");
                assert(false);
        }
        o->var.min = ~0ull;
}

static void bchoice_parse(struct bchoice *choice, const struct span *s) {
        struct span sub = {};
        logspan(s);
        choice->percent = bnumber(span_next(s, ':', &sub));
        boption_parse(&choice->option, span_next(s, ':', &sub));
        assert(span_next(s, ':', &sub) == NULL);
}

static void bthread_parse(struct bthread *th, const struct span *s) {
        int total = 0;
        struct span sub = {};
        struct span *cur;
        logspan(s);
        th->nr = span_nr(s, '|');
        th->choice = mem_alloc(th->nr * sizeof th->choice[0]);
        for (int i = 0; (cur = span_next(s, '|', &sub)) != NULL; i++) {
                bchoice_parse(&th->choice[i], cur);
                total += th->choice[i].percent;
        }
        assert(total == 100);
}

static void bgroup_parse(struct bgroup *g, const struct span *s) {
        struct span sub = {};
        logspan(s);
        g->nr = bnumber(span_next(s, '*', &sub));
        g->ops = bnumber(span_next(s, '*', &sub));
        bthread_parse(&g->thread, span_next(s, '*', &sub));
        g->thread.parent = g;
        assert(span_next(s, '*', &sub) == NULL);
}

static void bphase_parse(struct bphase *ph, const struct span *s) {
        struct span sub = {};
        struct span *cur;
        logspan(s);
        ph->nr = span_nr(s, '+');
        ph->group = mem_alloc(ph->nr * sizeof ph->group[0]);
        for (int i = 0; (cur = span_next(s, '+', &sub)) != NULL; i++) {
                ph->group[i].parent = ph;
                bgroup_parse(&ph->group[i], cur);
        }
}

static struct benchmark *bparse(const struct span *s) {
        struct benchmark *b = mem_alloc(sizeof *b);
        struct span sub = {};
        struct span *cur;
        logspan(s);
        b->nr = span_nr(s, ';');
        b->phase = mem_alloc(b->nr * sizeof b->phase[0]);
        for (int i = 0; (cur = span_next(s, ';', &sub)) != NULL; i++) {
                b->phase[i].parent = b;
                bphase_parse(&b->phase[i], cur);
        }
        return b;
}

static uint64_t brnd(uint64_t prev) {
        return (prev * 6364136223846793005ULL + 1442695040888963407ULL) >> 11;
}

static int bn_next(struct t2_cursor *c, const struct t2_rec *rec) {
        return +1;
}

static void binc(unsigned char *key, int len) {
        int i;
        for (i = len - 1; i >= 0 && key[i] == 0xff; --i) {
                ;
        }
        if (i >= 0) {
                key[i]++;
        }
        while (++i < len) {
                key[i] = 0;
        }
}

static void bfill(char *buf, int len, uint64_t seed) {
        for (int i = 0; i < len; ++i) {
                buf[i] = (seed = brnd(seed)) & 0xff;
        }
}

static int rnd_between(int lo, int hi, uint64_t seed) {
        return lo + (hi - lo) * (brnd(seed) % (hi - lo + 1)) / (hi - lo + 1);
}

static int32_t bufgen(void *key, uint64_t seed0, int max, int *rndmax, int delta, struct bspec *sp) {
        uint64_t seed = seed0 + max + delta;
        int len;
        switch (sp->ord) {
        case EXI:
                seed = rnd_between(seed0, seed0 + *rndmax, seed) + delta;
                len = rnd_between(sp->min, sp->max, seed);
                bfill(key, len, seed);
                break;
        case RND:
                seed = seed0 + (*rndmax)++ + delta;
                len = rnd_between(sp->min, sp->max, seed);
                bfill(key, len, seed);
                break;
        case SEQ:
                len = rnd_between(sp->min, sp->max, seed);
                binc(key, len);
                break;
        }
        return len;
}

static uint64_t now(void) {
        struct timeval t;
        NOFAIL(gettimeofday(&t, NULL));
        return t.tv_sec * 1000000 + t.tv_usec;
}

static void var_fold(struct bphase *ph, struct bthread *bt, struct bvar *var) {
        mutex_lock(&ph->lock);
        for (int i = 0; i < bt->nr; ++i) {
                struct bvar *v = &bt->choice[i].option.var;
                v->nr  += var[i].nr;
                v->sum += var[i].sum;
                v->ssq += var[i].ssq;
                v->min  = MIN(v->min, var[i].min);
                v->max  = MAX(v->max, var[i].max);
                SET0(&var[i]);
        }
        mutex_unlock(&ph->lock);
        SET0(var);
}

static int ht_shift = 20;
static int counters_level = 0;
static int shift_internal = 9;
static int shift_leaf     = 9;

static struct t2_node_type *bn_ntype_internal;
static struct t2_node_type *bn_ntype_leaf;

static struct t2_node_type *bn_tree_ntype(struct t2_tree *t, int level) {
        return level == 0 ? bn_ntype_leaf : bn_ntype_internal;
}

static struct t2_tree_type bn_ttype = {
        .id       = 2,
        .name     = "tree-type-bn",
        .ntype    = &bn_tree_ntype
};

static void *bworker(void *arg) {
        struct rthread *rt = arg;
        struct bthread *bt = rt->parent;
        struct bgroup *g = bt->parent;
        struct bphase *ph = g->parent;
        struct t2_tree *t = ph->parent->tree;
        int choice[100] = {};
        int32_t maxkey = 0;
        int32_t maxval = 0;
        int rndmax = 0;
        void *key;
        void *val;
        void *cur;
        struct bvar *var;
        int i;
        int finger = 0;
        uint64_t seed0 = ph->parent->seed + g->idx * 100000 + rt->idx;
        uint64_t reported = now() - rt->idx * 10000;
        struct t2_cursor_op cop = {
                .next = &bn_next
        };
        struct t2_cursor c = {
                .tree = t,
                .op   = &cop
        };
        t2_thread_register();
        assert(rt->self == pthread_self());
        blog(BINFO, "        Thread %3i in group %2i started.\n", rt->idx, g->idx);
        var = mem_alloc(bt->nr * sizeof var[0]);
        for (i = 0; i < bt->nr; ++i) {
                maxkey = MAX(maxkey, bt->choice[i].option.key.max);
                maxval = MAX(maxval, bt->choice[i].option.val.max);
                for (int j = 0; j < bt->choice[i].percent; ++j) {
                        choice[finger++] = i;
                }
                var[i].min = ~0ull;
        }
        assert(finger == 100);
        key = mem_alloc(maxkey);
        val = mem_alloc(maxval);
        cur = mem_alloc(maxkey);
        c.curkey = (struct t2_buf){ .nr = 1, .seg = { [0] = { .addr = cur, .len = maxkey } } };
        assert(key != NULL && val != NULL);
        mutex_lock(&ph->lock);
        rt->ready = true;
        NOFAIL(pthread_cond_signal(&ph->start));
        while (!ph->run) {
                NOFAIL(pthread_cond_wait(&ph->cond, &ph->lock));
        }
        mutex_unlock(&ph->lock);
        for (i = 0; i < g->ops; ++i) {
                uint64_t seed = seed0 + (i << 3);
                int ch = choice[brnd(seed) % 100];
                struct boption *opt = &bt->choice[ch].option;
                uint64_t start;
                uint64_t end;
                if (opt->opt == BSLEEP) {
                        struct timespec sleep = {
                                .tv_nsec = (brnd(seed + 1) % opt->delay) * 1000
                        };
                        start = now();
                        NOFAIL(nanosleep(&sleep, NULL));
                        end = now();
                } else if (opt->opt == BREMOUNT) {
                        struct t2 *mod = ph->parent->mod;
                        taddr_t root = bn_tree_root(t);
                        t2_tree_close(ph->parent->tree);
                        t2_tree_type_degister(&bn_ttype);
                        t2_node_type_degister(bn_ntype_internal);
                        t2_node_type_degister(bn_ntype_leaf);
                        t2_fini(mod);
                        uint64_t free = bn_file_free(bn_storage);
                        ph->parent->mod = mod = t2_init(bn_storage, ht_shift);
                        bn_ttype.mod = NULL;
                        t2_node_type_register(mod, bn_ntype_internal);
                        t2_node_type_register(mod, bn_ntype_leaf);
                        t2_tree_type_register(mod, &bn_ttype);
                        bn_file_free_set(bn_storage, free);
                        ph->parent->tree = t = t2_tree_open(&bn_ttype, root);
                } else {
                        int32_t ksize = bufgen(key, seed0, i, &rndmax, 1, &opt->key);
                        int result;
                        if (opt->opt == BLOOKUP) {
                                start = now();
                                result = t2_lookup_ptr(t, key, ksize, val, maxval);
                                end = now();
                                assert(result == 0 || result == -ENOENT || result == -ENAMETOOLONG);
                        } else if (opt->opt == BINSERT) {
                                int32_t vsize = bufgen(val, seed0, i, &rndmax, 2, &opt->val);
                                start = now();
                                result = t2_insert_ptr(t, key, ksize, val, vsize);
                                end = now();
                                assert(result == 0 || result == -EEXIST);
                        } else if (opt->opt == BDELETE) {
                                start = now();
                                result = t2_delete_ptr(t, key, ksize);
                                end = now();
                                assert(result == 0 || result == -ENOENT);
                        } else if (opt->opt == BNEXT) {
                                struct t2_buf nextkey = {
                                        .nr = 1,
                                        .seg = { [0] = { .addr = key, .len = ksize } }
                                };
                                int it = brnd(seed + 3) % opt->iter;
                                c.dir = (brnd(seed + 4) % 2 == 0) ? T2_MORE : T2_LESS;
                                start = now();
                                t2_cursor_init(&c, &nextkey);
                                for (int i = 0; i < it && t2_cursor_next(&c) > 0; ++i) {
                                        ;
                                }
                                t2_cursor_fini(&c);
                                end = now();
                        } else {
                                assert(false);
                        }
                }
                uint64_t delta = end - start;
                var[ch].nr++;
                var[ch].sum += delta;
                var[ch].ssq += delta * delta;
                var[ch].min  = MIN(var[ch].min, delta);
                var[ch].max  = MAX(var[ch].max, delta);
                if (end - reported > 1000000) {
                        var_fold(ph, bt, var);
                        reported = end;
                }
        }
        blog(BINFO, "        Thread %3i in group %2i completed %i operations.\n", rt->idx, bt->parent->idx, i);
        var_fold(ph, bt, var);
        mem_free(cur);
        mem_free(key);
        mem_free(val);
        mem_free(var);
        t2_thread_degister();
        return NULL;
}

static void bthread_start(struct bthread *bt, int idx) {
        struct rthread *rt = &bt->rt[idx];
        struct bphase *ph = bt->parent->parent;
        assert(idx < bt->parent->nr);
        rt->idx = idx;
        rt->parent = bt;
        NOFAIL(pthread_create(&rt->self, NULL, &bworker, rt));
        mutex_lock(&ph->lock);
        while (!rt->ready) {
                NOFAIL(pthread_cond_wait(&ph->start, &ph->lock));
        }
        mutex_unlock(&ph->lock);
}

static void bphase_report(struct bphase *ph, bool final);

static int report_interval = 10;

static void *breport_thread(void *arg) {
        struct bphase *ph = arg;
        NOFAIL(pthread_setcancelstate(PTHREAD_CANCEL_ENABLE, NULL));
        NOFAIL(pthread_setcanceltype(PTHREAD_CANCEL_ASYNCHRONOUS, NULL));
        while (true) {
                sleep(report_interval);
                bphase_report(ph, false);
                if (counters_level > 1) {
                        bn_counters_print();
                }
                pthread_testcancel();
        }
}

static void bphase(struct bphase *ph, int i) {
        pthread_t reporter;
        NOFAIL(pthread_mutex_init(&ph->lock, NULL));
        NOFAIL(pthread_cond_init(&ph->cond, NULL));
        NOFAIL(pthread_cond_init(&ph->start, NULL));
        blog(BINFO, "    Starting phase %2i.\n", i);
        for (int i = 0; i < ph->nr; ++i) {
                ph->group[i].thread.rt = mem_alloc(ph->group[i].nr * sizeof(struct rthread));
                ph->group[i].idx = i;
                assert(ph->group[i].thread.rt != NULL);
                for (int j = 0; j < ph->group[i].nr; ++j) {
                        bthread_start(&ph->group[i].thread, j);
                }
        }
        blog(BINFO, "    Threads started. Run!\n");
        mutex_lock(&ph->lock);
        ph->run = true;
        NOFAIL(pthread_cond_broadcast(&ph->cond));
        mutex_unlock(&ph->lock);
        NOFAIL(pthread_create(&reporter, NULL, *breport_thread, ph));
        for (int i = 0; i < ph->nr; ++i) {
                for (int j = 0; j < ph->group[i].nr; ++j) {
                        pthread_join(ph->group[i].thread.rt[j].self, NULL);
                }
        }
        blog(BINFO, "    Phase %2i done.\n", i);
        if (counters_level > 0) {
                bn_counters_print();
        }
        NOFAIL(pthread_cancel(reporter));
        NOFAIL(pthread_cond_destroy(&ph->start));
        NOFAIL(pthread_cond_destroy(&ph->cond));
        NOFAIL(pthread_mutex_destroy(&ph->lock));
}

static void bphase_report(struct bphase *ph, bool final) {
        int lev = final ? BRESULTS : BPROGRESS;
        for (int i = 0; i < ph->nr; ++i) {
                struct bthread *bt = &ph->group[i].thread;
                blog(lev, "        Group %2i:\n", i);
                for (int k = 0; k < bt->nr; ++k) {
                        const double M = 1000000.0;
                        if (!final) {
                                mutex_lock(&ph->lock);
                        }
                        struct bvar prev = bt->choice[k].option.prev;
                        struct bvar var = bt->choice[k].option.var;
                        bt->choice[k].option.prev = var;
                        if (!final) {
                                mutex_unlock(&ph->lock);
                                var.sum -= prev.sum;
                                var.nr  -= prev.nr;
                                var.ssq -= prev.ssq;
                        }
                        if (var.nr != 0) {
                                double avg = 1.0 * var.sum / var.nr;
                                blog(lev, "            Option %2i: ops: %10llu sec: %10.4f op/sec: %9.1f usec/op: %6.2f min: %3llu max: %7llu dev: %12.4g\n",
                                     k, var.nr, var.sum / M, M * var.nr / var.sum, avg, var.min, var.max, sqrt(var.ssq / var.nr - avg * avg));
                        } else {
                                blog(lev, "            Option %2i: idle.\n", k);
                        }
                }
        }
}

static void brun(struct benchmark *b) {
        b->mod = t2_init(bn_storage, ht_shift);
        bn_ntype_internal = t2_node_type_init(2, "simple-bn-internal", shift_internal, 0);
        bn_ntype_leaf     = t2_node_type_init(1, "simple-bn-leaf",     shift_leaf,     0);
        t2_node_type_register(b->mod, bn_ntype_internal);
        t2_node_type_register(b->mod, bn_ntype_leaf);
        t2_tree_type_register(b->mod, &bn_ttype);
        b->tree = t2_tree_create(&bn_ttype);
        blog(BINFO, "Starting benchmark.\n");
        for (int i = 0; i < b->nr; ++i) {
                bphase(&b->phase[i], i);
        }
        blog(BINFO, "Benchmark done.\n");
        t2_tree_close(b->tree);
        t2_tree_type_degister(&bn_ttype);
        t2_node_type_degister(bn_ntype_internal);
        t2_node_type_degister(bn_ntype_leaf);
        t2_fini(b->mod);
        for (int i = 0; i < b->nr; ++i) {
                blog(BRESULTS, "    Phase %2i report:\n", i);
                bphase_report(&b->phase[i], true);
        }
}

int main(int argc, char **argv) {
        char ch;
        setbuf(stdout, NULL);
        setbuf(stderr, NULL);
        while ((ch = getopt(argc, argv, "vf:r:n:N:h:c")) != -1) {
                switch (ch) {
                case 'v':
                        blog_level++;
                        break;
                case 'f':
                        total = optarg;
                        break;
                case 'r':
                        report_interval = atoi(optarg);
                        break;
                case 'n':
                        shift_leaf = atoi(optarg);
                        break;
                case 'N':
                        shift_internal = atoi(optarg);
                        break;
                case 'h':
                        ht_shift = atoi(optarg);
                        break;
                case 'c':
                        counters_level++;
                        break;
                }
        }
        if (total != NULL) {
                struct benchmark *b = bparse(&SPAN(total, total + strlen(total)));
                brun(b);
                return 0;
        } else {
                puts("Huh?");
                return 1;
        }
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
