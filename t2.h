/* -*- C -*- */

/* Copyright 2023--2026 Nikita Danilov <danilov@gmail.com> */
/* See https://github.com/nikitadanilov/t2/blob/master/LICENCE for licencing information. */

#include <inttypes.h>
#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>

struct timespec;
struct iovec;

struct t2;
struct t2_tree;
struct t2_buf;
struct t2_rec;
struct t2_cookie;
struct t2_storage;
struct t2_storage_op;
struct t2_te;
struct t2_tx;
struct t2_txrec;
struct t2_tree_type;
struct t2_cursor;
struct t2_cursor_op;
struct t2_node;

struct t2_conf {
        struct t2_storage    *storage;
        struct t2_te         *te;
        int                   hshift;
        int                   cshift;
        int                   ishift;
        int                   min_radix_level;
        int                   cache_shepherd_shift;
        int                   cache_briard_shift;
        int                   cache_buhund_shift;
        bool                  cache_direct;
        int                   scan_run;
        int                   free_hi;
        int                   free_lo;
        int                   scan_rate_shift;
        bool                  make;
        struct t2_tree_type **ttypes;
        struct t2_node_type **ntypes;
};

struct t2_param {
        struct t2_conf conf;
        const char    *storage_type;
        const char    *file_storage_path;
        int32_t        file_storage_frag_nr;
        const char    *te_type;
        bool           no_te;
        const char    *wal_logname;
        int            wal_nr_bufs;
        int            wal_buf_size;
        int32_t        wal_flags;
        int            wal_workers;
        int            wal_log_nr;
        double         wal_log_sleep;
        double         wal_age_limit;
        double         wal_sync_age;
        int64_t        wal_sync_nob; /* Measured in buffers. */
        int64_t        wal_log_size;
        int            wal_reserve_quantum;
        int            wal_threshold_paged;
        int            wal_threshold_page;
        int            wal_threshold_log_syncd;
        int            wal_threshold_log_sync;
        int            wal_ready_lo;
        bool           wal_directio;
        bool           wal_crc;
        int            wal_compression;
        const char    *policy_leaf;
        const char    *policy_twig;
        const char    *policy_internal;
};

struct t2_tree_type {
        struct t2             *mod;
        uint32_t               id;
        const char            *name;
        struct t2_node_type *(*ntype)(struct t2_tree *t, int level);
};

struct t2_storage {
        const struct t2_storage_op *op;
};

struct t2_tx { /* Transaction. */
};

typedef int64_t lsn_t;
struct t2_te { /* Transaction engine. */
        int           (*post)    (struct t2_te *te, struct t2_tx *tx, int32_t nob, int nr, struct t2_txrec *txr);
        int           (*ante)    (struct t2_te *te, struct t2_tx *tx, int32_t nob, int nr, struct t2_txrec *txr);
        int           (*init)    (struct t2_te *te, struct t2 *mod);
        void          (*fini)    (struct t2_te *te);
        void          (*destroy) (struct t2_te *te);
        void          (*quiesce) (struct t2_te *te);
        struct t2_tx *(*make)    (struct t2_te *te);
        lsn_t         (*lsn)     (struct t2_te *te);
        int           (*open)    (struct t2_te *te, struct t2_tx *tx);
        void          (*close)   (struct t2_te *te, struct t2_tx *tx);
        int           (*wait)    (struct t2_te *te, struct t2_tx *tx, bool force);
        void          (*wait_for)(struct t2_te *te, lsn_t lsn, bool force);
        void          (*done)    (struct t2_te *te, struct t2_tx *tx);
        bool          (*pinned)  (const struct t2_te *te, struct t2_node *n);
        bool          (*check)   (const struct t2_te *te, struct t2_node *n);
        bool          (*throttle)(const struct t2_te *te, struct t2_node *n);
        bool          (*stop)    (struct t2_te *te, struct t2_node *n);
        void          (*maxpaged)(struct t2_te *te, lsn_t max);
        void          (*clean)   (struct t2_te *te, struct t2_node **nodes, int nr);
        void          (*print)   (struct t2_te *te);
        const char     *name;
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
 * This allows for 128T nodes (2^47) and total of 64PB (2^56) per storage
 * instance.
 */
typedef uint64_t taddr_t;

struct t2_buf {
        int32_t  len;
        void    *addr;
};

enum t2_txr_op {
        T2_TXR_ALLOC = INT32_MAX - 2,
        T2_TXR_DEALLOC
};

struct t2_txrec { /* Transaction log record. */
        struct t2_node *node;
        taddr_t         addr;
        int16_t         ntype;
        int32_t         off;
        struct t2_buf   part;
};

struct t2_io_ctx;
struct t2_storage_op {
        const char *name;
        int               (*init)  (struct t2_storage *storage, bool make);
        void              (*fini)  (struct t2_storage *storage);
        struct t2_io_ctx *(*create)(struct t2_storage *storage, int queue);
        void              (*done)  (struct t2_storage *storage, struct t2_io_ctx *arg);
        taddr_t           (*alloc) (struct t2_storage *storage, int shift_min, int shift_max);
        void              (*free)  (struct t2_storage *storage, taddr_t addr);
        int               (*read)  (struct t2_storage *storage, taddr_t addr, int nr, struct iovec *dst);
        int               (*write) (struct t2_storage *storage, taddr_t addr, int nr, struct iovec *src, struct t2_io_ctx *ctx, void *arg);
        void             *(*end)   (struct t2_storage *storage, struct t2_io_ctx *ctx, int32_t *nob, bool wait);
        int               (*sync)  (struct t2_storage *storage, bool barrier);
        bool              (*same)  (struct t2_storage *storage, int fd);
        int               (*replay)(struct t2_storage *storage, taddr_t addr, enum t2_txr_op op);
};

struct t2_cookie {
        uint64_t hi;
        uint64_t lo;
};

struct t2_rec {
        struct t2_buf   *val;
        void           (*vcb)(struct t2_buf *buf, void *arg);
        struct t2_buf   *key;
        void           (*kcb)(struct t2_buf *buf, void *arg);
        void            *arg;
        struct t2_buf   *scr;
        struct t2_cookie cookie;
};

enum t2_dir {
        T2_LESS = -1,
        T2_MORE = +1
};

struct t2_cursor_op {
        int (*next)(struct t2_cursor *c, const struct t2_rec *rec);
};

enum { T2_CURSOR_CACHED = 3 };

struct t2_cursor {
        enum t2_dir          dir;
        struct t2_buf        curkey;
        struct t2_buf        scr;
        struct t2_tree      *tree;
        struct t2_cursor_op *op;
        int32_t              maxlen;
        void                *cached[T2_CURSOR_CACHED];
};

enum t2_node_type_flags {
        T2_NT_VARKEY   = 1ull << 0,
        T2_NT_VARVAL   = 1ull << 1,
        T2_NT_INTERNAL = 1ull << 2,
        T2_NT_LEAF     = 1ull << 3
};

enum {
        T2_INIT_EXPLAIN = 1ull << 0,
        T2_INIT_VERBOSE = 1ull << 1
};

#define T2_INIT_WITH(flags, ...) t2_init_with((flags), &(struct t2_conf){ __VA_ARGS__ })

struct t2 *t2_init_with(uint64_t flags, struct t2_param *param);
struct t2 *t2_init(const struct t2_conf *conf);
void       t2_fini(struct t2 *mod);

void t2_thread_register(void);
void t2_thread_degister(void);

struct t2_node_type *t2_node_type_init(int16_t id, const char *name, int shift, uint64_t flags);
void                 t2_node_type_fini(struct t2_node_type *nt);

struct t2_tree *t2_tree_create(struct t2_tree_type *ttype, struct t2_tx *tx);
struct t2_tree *t2_tree_open(struct t2_tree_type *ttype, uint32_t id);
uint32_t        t2_tree_id(const struct t2_tree *t);
void            t2_tree_close(struct t2_tree *t);

int  t2_lookup(struct t2_tree *t, struct t2_rec *r);
int  t2_insert(struct t2_tree *t, struct t2_rec *r, struct t2_tx *tx);
int  t2_delete(struct t2_tree *t, struct t2_rec *r, struct t2_tx *tx);

int  t2_cursor_init(struct t2_cursor *c, struct t2_buf *key);
void t2_cursor_fini(struct t2_cursor *c);
int  t2_cursor_next(struct t2_cursor *c);

struct t2_tx *t2_tx_make (struct t2 *mod);
int           t2_tx_open (struct t2 *mod, struct t2_tx *tx);
void          t2_tx_close(struct t2 *mod, struct t2_tx *tx);
int           t2_tx_wait (struct t2 *mod, struct t2_tx *tx, bool force);
void          t2_tx_done (struct t2 *mod, struct t2_tx *tx);

void    t2_release(struct t2_node *n);
void    t2_lsnset (struct t2_node *n, lsn_t lsn);
lsn_t   t2_lsnget (const struct t2_node *n);
taddr_t t2_addr   (const struct t2_node *n);
struct t2_node *t2_apply(struct t2 *mod, const struct t2_txrec *txr);

int   t2_error(int idx, char *buf, int nob, int *err);
void  t2_error_print(void);
bool  t2_is_err (void *ptr);
int   t2_errcode(void *ptr);
void *t2_errptr (int errcode);
void  t2_conf_print(int fd);

enum t2_stats_flags {
        T2_SF_TREE       = 1ull <<  0, /* t */
        T2_SF_MAXWELL    = 1ull <<  1, /* m */
        T2_SF_SHEPHERD   = 1ull <<  2, /* s */
        T2_SF_IO         = 1ull <<  3, /* i */
        T2_SF_MALLOC     = 1ull <<  4, /* M */
        T2_SF_POOL       = 1ull <<  5, /* p */
        T2_SF_TX         = 1ull <<  6, /* x */
        T2_SF_OS         = 1ull <<  7, /* o */
        T2_SF_COUNTERS   = 1ull <<  8, /* c */
        T2_SF_HASH       = 1ull <<  9, /* h */

        T2_SF_SCAN       = T2_SF_MAXWELL | T2_SF_SHEPHERD,
        T2_SF_ALLOC      = T2_SF_MALLOC
};

void t2_stats_print(struct t2 *mod, uint64_t flags);
uint64_t t2_stats_flags_parse(const char *s);

int t2_lookup_ptr(struct t2_tree *t, void *key, void *scr, int32_t ksize, void *val, int32_t vsize);
int t2_insert_ptr(struct t2_tree *t, void *key, void *scr, int32_t ksize, void *val, int32_t vsize, struct t2_tx *tx);
int t2_delete_ptr(struct t2_tree *t, void *key, void *scr, int32_t ksize, struct t2_tx *tx);

/*
 *  Local variables:
 *  c-indentation-style: "K&R"
 *  c-basic-offset: 8
 *  tab-width: 8
 *  scroll-step: 1
 *  indent-tabs-mode: nil
 *  End:
 */
