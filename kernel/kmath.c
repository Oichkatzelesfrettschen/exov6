/**
 * @file kmath.c
 * @brief Kernel-space math functions implementation
 * 
 * Pure C17 implementation of essential math functions for kernel use.
 * No floating-point operations, no external dependencies.
 * Optimized for integer and fixed-point arithmetic.
 */

#include <stdint.h>
#include <stdbool.h>

// Absolute value implementations
__attribute__((unused))
static inline int32_t kabs32(int32_t x) {
    return (x < 0) ? -x : x;
}

__attribute__((unused))
static inline int64_t kabs64(int64_t x) {
    return (x < 0) ? -x : x;
}

/**
 * Integer square root using Newton-Raphson method
 * Returns floor(sqrt(x))
 */
uint32_t kisqrt32(uint32_t x) {
    if (x == 0) return 0;
    if (x == 1) return 1;
    
    // Initial guess: highest bit set
    uint32_t guess = 1;
    uint32_t bits = 0;
    uint32_t tmp = x;
    
    while (tmp > 0) {
        tmp >>= 1;
        bits++;
    }
    guess = 1U << (bits / 2);
    
    // Newton-Raphson iterations
    // y = (y + x/y) / 2
    uint32_t prev;
    do {
        prev = guess;
        guess = (guess + x / guess) / 2;
    } while (guess < prev);
    
    return prev;
}

/**
 * 64-bit integer square root
 */
uint64_t kisqrt64(uint64_t x) {
    if (x == 0) return 0;
    if (x == 1) return 1;
    
    uint64_t guess = 1;
    uint64_t bits = 0;
    uint64_t tmp = x;
    
    while (tmp > 0) {
        tmp >>= 1;
        bits++;
    }
    guess = 1ULL << (bits / 2);
    
    uint64_t prev;
    do {
        prev = guess;
        guess = (guess + x / guess) / 2;
    } while (guess < prev);
    
    return prev;
}

/**
 * Fixed-point square root (16.16 format)
 * Input: fixed-point value (16 bits integer, 16 bits fraction)
 * Output: fixed-point square root
 */
uint32_t kfsqrt(uint32_t x) {
    if (x == 0) return 0;
    
    // Convert to 64-bit for intermediate calculations
    uint64_t n = (uint64_t)x << 16; // Shift to maintain precision
    uint64_t result = kisqrt64(n);
    
    return (uint32_t)result;
}

/**
 * Integer power function
 */
uint64_t kipow(uint32_t base, uint32_t exp) {
    uint64_t result = 1;
    uint64_t b = base;
    
    while (exp > 0) {
        if (exp & 1) {
            result *= b;
        }
        b *= b;
        exp >>= 1;
    }
    
    return result;
}

/**
 * Integer logarithm base 2 (floor(log2(x)))
 */
uint32_t kilog2(uint32_t x) {
    if (x == 0) return 0;
    
    uint32_t log = 0;
    while (x >>= 1) {
        log++;
    }
    
    return log;
}

/**
 * Count leading zeros
 */
uint32_t kclz32(uint32_t x) {
    if (x == 0) return 32;
    
    uint32_t count = 0;
    if (!(x & 0xFFFF0000)) { count += 16; x <<= 16; }
    if (!(x & 0xFF000000)) { count += 8;  x <<= 8; }
    if (!(x & 0xF0000000)) { count += 4;  x <<= 4; }
    if (!(x & 0xC0000000)) { count += 2;  x <<= 2; }
    if (!(x & 0x80000000)) { count += 1; }
    
    return count;
}

/**
 * Count trailing zeros
 */
uint32_t kctz32(uint32_t x) {
    if (x == 0) return 32;
    
    uint32_t count = 0;
    if (!(x & 0x0000FFFF)) { count += 16; x >>= 16; }
    if (!(x & 0x000000FF)) { count += 8;  x >>= 8; }
    if (!(x & 0x0000000F)) { count += 4;  x >>= 4; }
    if (!(x & 0x00000003)) { count += 2;  x >>= 2; }
    if (!(x & 0x00000001)) { count += 1; }
    
    return count;
}

/**
 * Population count (number of set bits)
 */
uint32_t kpopcount32(uint32_t x) {
    x = x - ((x >> 1) & 0x55555555);
    x = (x & 0x33333333) + ((x >> 2) & 0x33333333);
    x = (x + (x >> 4)) & 0x0F0F0F0F;
    x = x + (x >> 8);
    x = x + (x >> 16);
    return x & 0x3F;
}

/**
 * Greatest common divisor using Euclidean algorithm
 */
uint32_t kgcd(uint32_t a, uint32_t b) {
    while (b != 0) {
        uint32_t temp = b;
        b = a % b;
        a = temp;
    }
    return a;
}

/**
 * Least common multiple
 */
uint32_t klcm(uint32_t a, uint32_t b) {
    if (a == 0 || b == 0) return 0;
    return (a / kgcd(a, b)) * b;
}

/**
 * Min/max functions
 */
__attribute__((unused))
static inline uint32_t kmin32(uint32_t a, uint32_t b) {
    return (a < b) ? a : b;
}

__attribute__((unused))
static inline uint32_t kmax32(uint32_t a, uint32_t b) {
    return (a > b) ? a : b;
}

__attribute__((unused))
static inline int32_t kimin32(int32_t a, int32_t b) {
    return (a < b) ? a : b;
}

__attribute__((unused))
static inline int32_t kimax32(int32_t a, int32_t b) {
    return (a > b) ? a : b;
}

/**
 * Clamp value between min and max
 */
__attribute__((unused))
static inline uint32_t kclamp32(uint32_t val, uint32_t min, uint32_t max) {
    if (val < min) return min;
    if (val > max) return max;
    return val;
}

/**
 * Check if power of 2
 */
__attribute__((unused))
static inline bool kis_pow2(uint32_t x) {
    return x && !(x & (x - 1));
}

/**
 * Round up to next power of 2
 */
uint32_t kround_up_pow2(uint32_t x) {
    if (x == 0) return 1;
    
    x--;
    x |= x >> 1;
    x |= x >> 2;
    x |= x >> 4;
    x |= x >> 8;
    x |= x >> 16;
    x++;
    
    return x;
}

/**
 * Align value up to alignment boundary
 */
__attribute__((unused))
static inline uint64_t kalign_up(uint64_t val, uint64_t align) {
    return (val + align - 1) & ~(align - 1);
}

/**
 * Align value down to alignment boundary
 */
__attribute__((unused))
static inline uint64_t kalign_down(uint64_t val, uint64_t align) {
    return val & ~(align - 1);
}

/**
 * Rotate left
 */
__attribute__((unused))
static inline uint32_t krotl32(uint32_t x, uint32_t n) {
    n &= 31;
    return (x << n) | (x >> (32 - n));
}

/**
 * Rotate right
 */
__attribute__((unused))
static inline uint32_t krotr32(uint32_t x, uint32_t n) {
    n &= 31;
    return (x >> n) | (x << (32 - n));
}

/**
 * Fast approximation of sine using Taylor series
 * Input: angle in units of 2^16 = 2*pi radians
 * Output: sine value in 16.16 fixed point
 */
int32_t kfsin(int32_t angle) {
    // Normalize angle to [0, 2^16)
    angle &= 0xFFFF;
    
    // Use symmetry to reduce to first quadrant
    int32_t sign = 1;
    if (angle > 0x8000) {
        angle = 0x10000 - angle;
        sign = -1;
    }
    if (angle > 0x4000) {
        angle = 0x8000 - angle;
    }
    
    // Convert to radians in fixed point
    // angle * (2*pi / 65536) * 65536 = angle * pi / 32768
    int64_t x = ((int64_t)angle * 3141592653LL) >> 15;
    
    // Taylor series: sin(x) = x - x^3/3! + x^5/5! - ...
    // Using fixed point arithmetic
    int64_t x2 = (x * x) >> 32;
    int64_t x3 = (x2 * x) >> 32;
    int64_t x5 = (x3 * x2) >> 32;
    
    int64_t result = x - x3 / 6 + x5 / 120;
    
    return (int32_t)((result * sign) >> 16);
}

/**
 * Fast approximation of cosine
 */
int32_t kfcos(int32_t angle) {
    return kfsin(angle + 0x4000); // cos(x) = sin(x + pi/2)
}

/**
 * Integer division with rounding
 */
uint32_t kdiv_round(uint32_t dividend, uint32_t divisor) {
    return (dividend + divisor / 2) / divisor;
}

/**
 * Modular exponentiation for cryptography
 * Computes (base^exp) % mod
 */
uint64_t kmod_exp(uint64_t base, uint64_t exp, uint64_t mod) {
    uint64_t result = 1;
    base %= mod;
    
    while (exp > 0) {
        if (exp & 1) {
            result = (result * base) % mod;
        }
        base = (base * base) % mod;
        exp >>= 1;
    }
    
    return result;
}

// Export initialization function
void kmath_init(void) {
    // Any initialization if needed
}
