/* -*- C -*- */

/* See https://github.com/nikitadanilov/t2/blob/master/LICENCE for licencing information. */

#include "t2.h"

enum {
        OK,
        NOENT,
        EXIST,
        OTHER,
        ENR
};

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
        uint64_t rc[ENR];
        uint64_t prev_rc[ENR];
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
        long long ops;
        struct bthread thread;
        struct bphase *parent;
        int idx;
};

struct bphase {
        int nr;
        int idx;
        struct bgroup *group;
        pthread_mutex_t lock;
        pthread_cond_t cond;
        pthread_cond_t start;
        struct benchmark *parent;
        bool run;
        uint64_t begin;
        uint64_t last;
};

#if USE_ROCKSDB
#include <rocksdb/c.h>

struct rocksdb_benchmark {
        rocksdb_t *db;
        rocksdb_writeoptions_t *wo;
        rocksdb_readoptions_t *ro;
};

#else
struct rocksdb_benchmark { char x; };
#endif

#if USE_LMDB
#include <lmdb.h>

struct lmdb_benchmark {
	MDB_env *env;
	MDB_dbi dbi;
};

#else
struct lmdb_benchmark { char x; };
#endif

struct kvbenchmark {
        union {
                struct {
                        struct t2_tree *tree;
                        struct t2      *mod;
                        taddr_t         root;
                        uint64_t        free;
                        uint64_t        bolt;
                } t2;
                struct rocksdb_benchmark r;
                struct lmdb_benchmark l;
                struct {
                        void *m;
                        void *l;
                } m;
        } u;
};

struct benchmark {
        int nr;
        struct bphase *phase;
        uint64_t seed;
        struct kvbenchmark kv;
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

enum kvtype {
        T2,
        ROCKSDB,
        MAP,
        LMDB,

        KVNR
};

struct kvdata {
        struct kvbenchmark *b;
        union {
                struct {
                        struct t2_tree      *tree;
                        struct t2_cursor_op  cop;
                        struct t2_cursor     c;
                        void                *cur;
                        struct t2_tx        *tx;
                } t2;
        } u;
};

struct kv {
        void (*mount)(struct benchmark *b);
        void (*umount)(struct benchmark *b);
        void (*worker_init)(struct rthread *rt, struct kvdata *d, int maxkey, int maxval);
        void (*worker_fini)(struct rthread *rt, struct kvdata *d);
        int  (*lookup)(struct rthread *rt, struct kvdata *d, void *key, int ksize, void *val, int vsize);
        int  (*insert)(struct rthread *rt, struct kvdata *d, void *key, int ksize, void *val, int vsize);
        int  (*del)(struct rthread *rt, struct kvdata *d, void *key, int ksize);
        int  (*next)  (struct rthread *rt, struct kvdata *d, void *key, int ksize, enum t2_dir dir, int nr);
};

/*
 *  Local variables:
 *  c-indentation-style: "K&R"
 *  c-basic-offset: 8
 *  tab-width: 8
 *  scroll-step: 1
 *  indent-tabs-mode: nil
 *  End:
 */
