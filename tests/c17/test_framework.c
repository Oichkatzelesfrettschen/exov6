/**
 * @file test_framework.c
 * @brief Pure C17 test framework for exov6
 * 
 * Provides common test utilities and assertions
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <time.h>
#include "test_framework.h"

static int total_tests = 0;
static int passed_tests = 0;
static int failed_tests = 0;
static clock_t suite_start_time;

void test_suite_init(const char *suite_name) {
    printf("\n");
    printf("========================================\n");
    printf("  %s Test Suite\n", suite_name);
    printf("========================================\n");
    total_tests = 0;
    passed_tests = 0;
    failed_tests = 0;
    suite_start_time = clock();
}

void test_suite_summary(void) {
    double elapsed = ((double)(clock() - suite_start_time)) / CLOCKS_PER_SEC;
    
    printf("\n");
    printf("========================================\n");
    printf("  Test Results\n");
    printf("========================================\n");
    printf("  Total:  %d\n", total_tests);
    printf("  Passed: %d\n", passed_tests);
    printf("  Failed: %d\n", failed_tests);
    printf("  Time:   %.3f seconds\n", elapsed);
    printf("========================================\n");
    
    if (failed_tests == 0) {
        printf("\n✓ All tests passed!\n");
    } else {
        printf("\n✗ %d test(s) failed\n", failed_tests);
    }
}

int test_suite_exit_code(void) {
    return failed_tests;
}

void test_assert_impl(bool condition, const char *expr, 
                      const char *file, int line, const char *func) {
    total_tests++;
    
    if (condition) {
        passed_tests++;
        printf("  ✓ %s\n", func);
    } else {
        failed_tests++;
        printf("  ✗ %s\n", func);
        printf("    ASSERTION FAILED: %s\n", expr);
        printf("    at %s:%d\n", file, line);
    }
}

void test_assert_eq_impl(long actual, long expected,
                         const char *actual_expr, const char *expected_expr,
                         const char *file, int line, const char *func) {
    total_tests++;
    
    if (actual == expected) {
        passed_tests++;
        printf("  ✓ %s\n", func);
    } else {
        failed_tests++;
        printf("  ✗ %s\n", func);
        printf("    ASSERTION FAILED: %s == %s\n", actual_expr, expected_expr);
        printf("    Expected: %ld\n", expected);
        printf("    Actual:   %ld\n", actual);
        printf("    at %s:%d\n", file, line);
    }
}

void test_assert_ne_impl(long actual, long expected,
                         const char *actual_expr, const char *expected_expr,
                         const char *file, int line, const char *func) {
    total_tests++;
    
    if (actual != expected) {
        passed_tests++;
        printf("  ✓ %s\n", func);
    } else {
        failed_tests++;
        printf("  ✗ %s\n", func);
        printf("    ASSERTION FAILED: %s != %s\n", actual_expr, expected_expr);
        printf("    Both values: %ld\n", actual);
        printf("    at %s:%d\n", file, line);
    }
}

void test_assert_str_eq_impl(const char *actual, const char *expected,
                            const char *actual_expr, const char *expected_expr,
                            const char *file, int line, const char *func) {
    total_tests++;
    
    if (actual == NULL && expected == NULL) {
        passed_tests++;
        printf("  ✓ %s\n", func);
    } else if (actual == NULL || expected == NULL) {
        failed_tests++;
        printf("  ✗ %s\n", func);
        printf("    ASSERTION FAILED: %s == %s\n", actual_expr, expected_expr);
        printf("    Expected: %s\n", expected ? expected : "(null)");
        printf("    Actual:   %s\n", actual ? actual : "(null)");
        printf("    at %s:%d\n", file, line);
    } else if (strcmp(actual, expected) == 0) {
        passed_tests++;
        printf("  ✓ %s\n", func);
    } else {
        failed_tests++;
        printf("  ✗ %s\n", func);
        printf("    ASSERTION FAILED: %s == %s\n", actual_expr, expected_expr);
        printf("    Expected: \"%s\"\n", expected);
        printf("    Actual:   \"%s\"\n", actual);
        printf("    at %s:%d\n", file, line);
    }
}

void test_assert_null_impl(const void *ptr, const char *expr,
                          const char *file, int line, const char *func) {
    total_tests++;
    
    if (ptr == NULL) {
        passed_tests++;
        printf("  ✓ %s\n", func);
    } else {
        failed_tests++;
        printf("  ✗ %s\n", func);
        printf("    ASSERTION FAILED: %s == NULL\n", expr);
        printf("    Actual: %p\n", ptr);
        printf("    at %s:%d\n", file, line);
    }
}

void test_assert_not_null_impl(const void *ptr, const char *expr,
                               const char *file, int line, const char *func) {
    total_tests++;
    
    if (ptr != NULL) {
        passed_tests++;
        printf("  ✓ %s\n", func);
    } else {
        failed_tests++;
        printf("  ✗ %s\n", func);
        printf("    ASSERTION FAILED: %s != NULL\n", expr);
        printf("    at %s:%d\n", file, line);
    }
}

void test_run(const char *name, void (*test_func)(void)) {
    printf("\nRunning: %s\n", name);
    test_func();
}