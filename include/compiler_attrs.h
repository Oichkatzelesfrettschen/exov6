/**
 * @file compiler_attrs.h
 * @brief Common compiler attribute macros for portability
 */
#ifndef _COMPILER_ATTRS_H
#define _COMPILER_ATTRS_H

/* Function never returns */
#if defined(__GNUC__) || defined(__clang__)
#define EXO_NORETURN __attribute__((noreturn))
#else
#define EXO_NORETURN
#endif

/* Variable/function may be unused */
#if defined(__GNUC__) || defined(__clang__)
#define EXO_MAYBE_UNUSED __attribute__((unused))
#else
#define EXO_MAYBE_UNUSED
#endif

/* Function should not be discarded */
#if defined(__GNUC__) || defined(__clang__)
#define EXO_NODISCARD __attribute__((warn_unused_result))
#else
#define EXO_NODISCARD
#endif

/* Inline hint */
#if defined(__GNUC__) || defined(__clang__)
#define EXO_ALWAYS_INLINE __attribute__((always_inline)) inline
#else
#define EXO_ALWAYS_INLINE inline
#endif

/* Pure function (no side effects except return value) */
#if defined(__GNUC__) || defined(__clang__)
#define EXO_PURE __attribute__((pure))
#else
#define EXO_PURE
#endif

/* Const function (result depends only on arguments) */
#if defined(__GNUC__) || defined(__clang__)
#define EXO_CONST __attribute__((const))
#else
#define EXO_CONST
#endif

/* Non-null pointer argument */
#if defined(__GNUC__) || defined(__clang__)
#define EXO_NONNULL(...) __attribute__((nonnull(__VA_ARGS__)))
#else
#define EXO_NONNULL(...)
#endif

/* Packed structure */
#if defined(__GNUC__) || defined(__clang__)
#define EXO_PACKED __attribute__((packed))
#else
#define EXO_PACKED
#endif

/* Aligned to boundary */
#if defined(__GNUC__) || defined(__clang__)
#define EXO_ALIGNED(n) __attribute__((aligned(n)))
#else
#define EXO_ALIGNED(n)
#endif

/* Section placement */
#if defined(__GNUC__) || defined(__clang__)
#define EXO_SECTION(name) __attribute__((section(name)))
#else
#define EXO_SECTION(name)
#endif

/* Weak symbol */
#if defined(__GNUC__) || defined(__clang__)
#define EXO_WEAK __attribute__((weak))
#else
#define EXO_WEAK
#endif

#endif /* _COMPILER_ATTRS_H */
