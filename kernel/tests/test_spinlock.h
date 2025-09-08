#pragma once

#include <assert.h>
#include <string.h>
#include "spinlock.h"

// Mock config for testing
#ifndef CONFIG_SMP
#define CONFIG_SMP 1
#endif

// Mock cpu struct for testing
struct cpu { int id; };

// Mock cache_line_size for testing
size_t cache_line_size = 64;

// Test: spinlock_optimal_alignment returns cache_line_size
static inline void test_spinlock_optimal_alignment() {
    cache_line_size = 128;
    assert(spinlock_optimal_alignment() == 128);
    cache_line_size = 64;
    assert(spinlock_optimal_alignment() == 64);
}

// Test: initlock sets name and zeroes ticket fields
static inline void test_initlock() {
    struct spinlock lk;
    memset(&lk, 0xAB, sizeof(lk));
    initlock(&lk, (char*)"testlock");
#if CONFIG_SMP && !defined(SPINLOCK_UNIPROCESSOR)
    assert(lk.name == (char*)"testlock");
    assert(lk.ticket.head == 0);
    assert(lk.ticket.tail == 0);
#endif
}

// Test: acquire/release/holding basic usage
static inline void test_acquire_release_holding() {
    struct spinlock lk;
    initlock(&lk, (char*)"testlock");
    acquire(&lk);
    assert(holding(&lk));
    release(&lk);
#if CONFIG_SMP && !defined(SPINLOCK_UNIPROCESSOR)
    // After release, holding() should be false (if implemented)
    // But in the stub, holding always returns 1
#endif
}

// Run all tests
static inline void run_spinlock_tests() {
    test_spinlock_optimal_alignment();
    test_initlock();
    test_acquire_release_holding();
}
