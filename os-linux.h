/* -*- C -*- */

/* See https://github.com/nikitadanilov/t2/blob/master/LICENCE for licencing information. */

#include <sys/syscall.h>
#include <sys/time.h>
#include <endian.h>
#include <linux/falloc.h>

extern int fallocate(int fd, int mode, off_t offset, off_t len); /* Hmm... */

/*
 *  Local variables:
 *  c-indentation-style: "K&R"
 *  c-basic-offset: 8
 *  tab-width: 8
 *  scroll-step: 1
 *  indent-tabs-mode: nil
 *  End:
 */
