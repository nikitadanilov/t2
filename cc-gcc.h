/* -*- C -*- */

/* Copyright 2023--2024 Nikita Danilov <danilov@gmail.com> */
/* See https://github.com/nikitadanilov/t2/blob/master/LICENCE for licencing information. */

#if defined(__has_attribute)
#if __has_attribute(assume)
#define ASSUME(expr) __attribute__((assume(expr)))
#else
#define ASSUME(expr) ((void)sizeof(expr))
#endif
#endif

#if __has_attribute(no_sanitize_address)
#define NOSANITISE_ADDRESS __attribute__((no_sanitize_address))
#else
#define NOSANITISE_ADDRESS
#endif

#define ATTRIBUTE_RETAIN __attribute__((used))

/*
 *  Local variables:
 *  c-indentation-style: "K&R"
 *  c-basic-offset: 8
 *  tab-width: 8
 *  scroll-step: 1
 *  indent-tabs-mode: nil
 *  End:
 */
