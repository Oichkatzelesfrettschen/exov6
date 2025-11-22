/**
 * @file test_framework.h
 * @brief Pure C17 test framework header
 */

#ifndef TEST_FRAMEWORK_H
#define TEST_FRAMEWORK_H

#include <stdbool.h>

/* Test suite management */
void test_suite_init(const char *suite_name);
void test_suite_summary(void);
int test_suite_exit_code(void);

/* Test execution */
void test_run(const char *name, void (*test_func)(void));

/* Assertion implementations */
void test_assert_impl(bool condition, const char *expr, 
                      const char *file, int line, const char *func);
void test_assert_eq_impl(long actual, long expected,
                         const char *actual_expr, const char *expected_expr,
                         const char *file, int line, const char *func);
void test_assert_ne_impl(long actual, long expected,
                         const char *actual_expr, const char *expected_expr,
                         const char *file, int line, const char *func);
void test_assert_str_eq_impl(const char *actual, const char *expected,
                            const char *actual_expr, const char *expected_expr,
                            const char *file, int line, const char *func);
void test_assert_null_impl(const void *ptr, const char *expr,
                          const char *file, int line, const char *func);
void test_assert_not_null_impl(const void *ptr, const char *expr,
                               const char *file, int line, const char *func);

/* Assertion macros */
#define TEST_ASSERT(expr) \
    test_assert_impl((expr), #expr, __FILE__, __LINE__, __func__)

#define TEST_ASSERT_EQ(actual, expected) \
    test_assert_eq_impl((long)(actual), (long)(expected), \
                       #actual, #expected, __FILE__, __LINE__, __func__)

#define TEST_ASSERT_NE(actual, expected) \
    test_assert_ne_impl((long)(actual), (long)(expected), \
                       #actual, #expected, __FILE__, __LINE__, __func__)

#define TEST_ASSERT_STR_EQ(actual, expected) \
    test_assert_str_eq_impl((actual), (expected), \
                           #actual, #expected, __FILE__, __LINE__, __func__)

#define TEST_ASSERT_NULL(ptr) \
    test_assert_null_impl((ptr), #ptr, __FILE__, __LINE__, __func__)

#define TEST_ASSERT_NOT_NULL(ptr) \
    test_assert_not_null_impl((ptr), #ptr, __FILE__, __LINE__, __func__)

/* Test definition macro */
#define TEST(name) static void test_##name(void)

/* Main test runner macro */
#define TEST_MAIN(suite_name, ...) \
int main(int argc, char *argv[]) { \
    (void)argc; (void)argv; \
    test_suite_init(suite_name); \
    void (*tests[])(void) = { __VA_ARGS__ }; \
    const char *names[] = { #__VA_ARGS__ }; \
    for (size_t i = 0; i < sizeof(tests)/sizeof(tests[0]); i++) { \
        test_run(names[i], tests[i]); \
    } \
    test_suite_summary(); \
    return test_suite_exit_code(); \
}

#endif /* TEST_FRAMEWORK_H */