#pragma once

/**
 * @file capnp_helpers.h
 * @brief Cap'n Proto integration for exokernel IPC
 * 
 * C17-compliant Cap'n Proto support for high-performance serialization.
 */

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

// Cap'n Proto pointer types
typedef enum {
    CAPNP_PTR_STRUCT = 0,
    CAPNP_PTR_LIST = 1,
    CAPNP_PTR_FAR = 2,
    CAPNP_PTR_OTHER = 3
} capnp_pointer_type_t;

// Cap'n Proto list element types
typedef enum {
    CAPNP_ELEMENT_VOID = 0,
    CAPNP_ELEMENT_BIT = 1,
    CAPNP_ELEMENT_BYTE = 2,
    CAPNP_ELEMENT_TWO_BYTES = 3,
    CAPNP_ELEMENT_FOUR_BYTES = 4,
    CAPNP_ELEMENT_EIGHT_BYTES = 5,
    CAPNP_ELEMENT_POINTER = 6,
    CAPNP_ELEMENT_COMPOSITE = 7
} capnp_list_element_type_t;

// Cap'n Proto pointer union
typedef union {
    struct {
        uint32_t type : 2;
        uint32_t offset : 30;
        uint16_t data_words;
        uint16_t ptr_words;
    } struct_ptr;
    
    struct {
        uint32_t type : 2;
        uint32_t offset : 30;
        uint32_t element_type : 3;
        uint32_t element_count : 29;
    } list_ptr;
    
    struct {
        uint32_t type : 2;
        uint32_t landing_pad : 1;
        uint32_t offset : 29;
        uint32_t segment_id;
    } far_ptr;
    
    uint64_t raw;
} capnp_pointer_t;

// Message descriptor
typedef struct {
    uint32_t size;
    uint32_t type;
} msg_desc_t;

// Function declarations
size_t msg_desc_size(const msg_desc_t* desc);
void capnp_init(void);

// Cap'n Proto pointer constructors
capnp_pointer_t capnp_make_struct_pointer(uint32_t offset, uint16_t data_words, uint16_t ptr_words);
capnp_pointer_t capnp_make_list_pointer(uint32_t offset, capnp_list_element_type_t element_type, uint32_t count);
capnp_pointer_t capnp_make_far_pointer(uint32_t segment_id, uint32_t offset, bool landing_pad);

// Static assertions for ABI compatibility
_Static_assert(sizeof(capnp_pointer_t) == 8, "Cap'n Proto pointer must be 64-bit");
_Static_assert(sizeof(msg_desc_t) == 8, "Message descriptor must be 64-bit aligned");