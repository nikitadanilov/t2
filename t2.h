/* -*- C -*- */

#include <inttypes.h>
#include <stddef.h>
#include <stdbool.h>

struct t2;
struct t2_tree;
struct t2_buf;
struct t2_rec;
struct t2_cookie;
struct t2_storage;
struct t2_storage_op;
struct t2_tree_type;

struct t2_tree_type {
        struct t2  *mod;
        uint32_t    id;
        const char *name;
        int root_min;
        int root_max;
};

struct t2_storage {
        const struct t2_storage_op *op;
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

struct t2_storage_op {
        const char *name;
        int      (*init) (struct t2_storage *storage);
        void     (*fini) (struct t2_storage *storage);
        taddr_t  (*alloc)(struct t2_storage *storage, int shift_min, int shift_max);
        void     (*free) (struct t2_storage *storage, taddr_t addr);
        int      (*read) (struct t2_storage *storage, taddr_t addr, void *dst);
        int      (*write)(struct t2_storage *storage, taddr_t addr, void *src);
};

struct t2 *t2_init(struct t2_storage *storage, int hshift);
void       t2_fini(struct t2 *mod);

bool  t2_is_err (void *ptr);
int   t2_errcode(void *ptr);
void *t2_errptr (int errcode);

void t2_tree_type_register(struct t2 *mod, struct t2_tree_type *ttype);
void t2_tree_type_degister(struct t2_tree_type *ttype);

struct t2_seg {
        uint32_t  len;
        void     *addr;
};

struct t2_buf {
        uint32_t      nr;
        struct t2_seg seg[1];
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
        struct t2_cookie cookie;
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
