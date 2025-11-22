#pragma once
#include <stdint.h>
#include <stdbool.h>

typedef uint32_t label_t;

// Lattice operations
// Default implementation: Bitwise lattice
// A dominates B if A has all bits of B set.

static inline label_t label_join(label_t a, label_t b) {
    return a | b;
}

static inline label_t label_meet(label_t a, label_t b) {
    return a & b;
}

static inline bool label_dominates(label_t a, label_t b) {
    return (a & b) == b;
}

// Check if flow from A to B is safe (A <= B for write, B <= A for read)
static inline bool is_flow_safe(label_t src, label_t dst) {
    return label_dominates(dst, src);
}
