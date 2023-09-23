/* -*- C -*- */

/* See https://github.com/nikitadanilov/t2/blob/master/LICENCE for licencing information. */

#if defined(__has_attribute)
#if __has_attribute(assume)
#define ASSUME(expr) __attribute__((assume(expr)))
#else
#define ASSUME(expr) ((void)sizeof(expr))
#endif
#endif

/*
 *  Local variables:
 *  c-indentation-style: "K&R"
 *  c-basic-offset: 8
 *  tab-width: 8
 *  scroll-step: 1
 *  indent-tabs-mode: nil
 *  End:
 */
