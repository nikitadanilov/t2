/* -*- C -*- */

/* Copyright 2023--2024 Nikita Danilov <danilov@gmail.com> */
/* See https://github.com/nikitadanilov/t2/blob/master/LICENCE for licencing information. */

#define ASSUME(expr) __builtin_assume(expr)

#if __has_feature(address_sanitizer)
#define NOSANITISE_ADDRESS __attribute__((no_sanitize("address")))
#else
#define NOSANITISE_ADDRESS
#endif

#define ATTRIBUTE_RETAIN __attribute__((retain))
/*
 *  Local variables:
 *  c-indentation-style: "K&R"
 *  c-basic-offset: 8
 *  tab-width: 8
 *  scroll-step: 1
 *  indent-tabs-mode: nil
 *  End:
 */
