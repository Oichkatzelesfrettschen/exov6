#include "include/libos/crypto.h" // Path relative to repo root, or adjust as per include paths
#include <stdio.h>
#include <string.h> // For memcmp and test data, and NULL
#include <assert.h> // For basic assertions

// If crypto.h does not bring in stddef.h for size_t (it should now)
// #include <stddef.h>

void test_hmac_verify() {
    printf("Starting hmac_verify_constant_time tests...\n");

    unsigned char mac1[] = {0x01, 0x02, 0x03, 0x04, 0x05};
    unsigned char mac2[] = {0x01, 0x02, 0x03, 0x04, 0x05};
    unsigned char mac3[] = {0x01, 0x02, 0x03, 0x04, 0x06}; // Differs at the end
    unsigned char mac4[] = {0x11, 0x02, 0x03, 0x04, 0x05}; // Differs at the start
    unsigned char empty_mac1[] = {}; // Note: C standard does not allow zero-size arrays directly
    unsigned char empty_mac2[] = {}; // These will behave like arrays of size 0 in some contexts if supported, or be pointers if dynamically managed

    size_t len = sizeof(mac1);
    size_t empty_len = 0; // Standard way to represent zero length for empty_mac arrays

    // Test 1: Equal MACs
    assert(hmac_verify_constant_time(mac1, mac2, len) == 1);
    printf("Test 1 (Equal MACs): Passed\n");

    // Test 2: Unequal MACs (difference at the end)
    assert(hmac_verify_constant_time(mac1, mac3, len) == 0);
    printf("Test 2 (Unequal MACs - diff end): Passed\n");

    // Test 3: Unequal MACs (difference at the start)
    assert(hmac_verify_constant_time(mac1, mac4, len) == 0);
    printf("Test 3 (Unequal MACs - diff start): Passed\n");

    // Test 4: Zero-length MACs (comparing zero bytes)
    // For empty_mac1 and empty_mac2, if they are actual zero-sized arrays (compiler extension)
    // or more typically pointers to some base or NULL, with len=0, they should be equal.
    unsigned char dummy1[1] = {0}; // Ensure non-NULL pointers if arrays are empty
    unsigned char dummy2[1] = {0};
    assert(hmac_verify_constant_time(empty_len == 0 ? dummy1 : empty_mac1, empty_len == 0 ? dummy2 : empty_mac2, empty_len) == 1);
    printf("Test 4 (Zero-length MACs): Passed\n");

    // Test 5: One zero-length, one not (should be equal if len is 0 for comparison)
    assert(hmac_verify_constant_time(mac1, dummy1, 0) == 1); // Comparing 0 bytes
    printf("Test 5 (Comparing 0 bytes of non-empty MACs): Passed\n");

    // Test 6: Null pointers - according to impl, NULL, NULL, len should be 1 (equal)
    assert(hmac_verify_constant_time(NULL, NULL, 5) == 1);
    printf("Test 6 (NULL, NULL, len=5): Passed\n");
    assert(hmac_verify_constant_time(NULL, NULL, 0) == 1);
    printf("Test 6.1 (NULL, NULL, len=0): Passed\n");


    // Test 7: One NULL, one not - should be 0 (unequal)
    assert(hmac_verify_constant_time(mac1, NULL, len) == 0);
    printf("Test 7 (mac1, NULL, len): Passed\n");
    assert(hmac_verify_constant_time(NULL, mac1, len) == 0);
    printf("Test 7.1 (NULL, mac1, len): Passed\n");

    // Test 8: Different lengths (function strictly compares `len` bytes)
    unsigned char mac_short[] = {0x01, 0x02, 0x03};
    assert(hmac_verify_constant_time(mac1, mac_short, sizeof(mac_short)) == 1);
    printf("Test 8 (Compare prefix: mac1 vs mac_short, len=3): Passed\n");

    unsigned char mac_short_diff[] = {0x01, 0x02, 0xAA};
    assert(hmac_verify_constant_time(mac1, mac_short_diff, sizeof(mac_short_diff)) == 0);
    printf("Test 9 (Compare prefix: mac1 vs mac_short_diff, len=3): Passed\n");

    printf("All hmac_verify_constant_time tests completed.\n");
}

int main() {
    test_hmac_verify();
    return 0;
}
