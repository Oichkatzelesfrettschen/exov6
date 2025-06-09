#pragma once

#ifndef __has_attribute
#define __has_attribute(x) 0
#endif

#ifndef __has_include
#define __has_include(x) 0
#endif

#define EXO_HAS_ATTR(x) __has_attribute(x)

/* Attribute helpers for modern C compilers */
#ifndef __has_c_attribute
#define __has_c_attribute(x) 0
#endif

#if __has_c_attribute(noreturn)
#define EXO_NORETURN [[noreturn]]
#elif EXO_HAS_ATTR(noreturn)
#define EXO_NORETURN __attribute__((noreturn))
#else
#define EXO_NORETURN
#endif

#if __has_c_attribute(nodiscard)
#define EXO_NODISCARD [[nodiscard]]
#elif EXO_HAS_ATTR(warn_unused_result)
#define EXO_NODISCARD __attribute__((warn_unused_result))
#else
#define EXO_NODISCARD
#endif

#if __has_c_attribute(maybe_unused)
#define EXO_MAYBE_UNUSED [[maybe_unused]]
#elif EXO_HAS_ATTR(unused)
#define EXO_MAYBE_UNUSED __attribute__((unused))
#else
#define EXO_MAYBE_UNUSED
#endif
