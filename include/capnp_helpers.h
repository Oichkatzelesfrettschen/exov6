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
    } common;

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

// Cap'n Proto error codes
typedef enum {
    CAPNP_OK = 0,
    CAPNP_ERROR_INVALID_MESSAGE = -1,
    CAPNP_ERROR_OUT_OF_MEMORY = -2,
    CAPNP_ERROR_INVALID_SEGMENT = -3,
    CAPNP_ERROR_INVALID_SCHEMA = -4
} capnp_error_t;

// Cap'n Proto schema types (minimal stubs for kernel use)
typedef struct {
    uint64_t id;
    uint16_t data_word_count;
    uint16_t pointer_count;
    uint16_t data_words;
    uint16_t ptr_words;
    const char *name;
} capnp_struct_schema_t;

typedef struct {
    uint16_t slot;
    uint8_t type;
    uint8_t is_pointer;
    uint16_t offset;
    uint64_t default_value;
    const char *name;
} capnp_field_t;

// Cap'n Proto wire format structures
typedef struct {
    uint32_t segment_count;  // Actually stored as (count - 1)
    uint32_t reserved;       // Padding for alignment
} capnp_message_header_t;

typedef struct {
    uint32_t size_words;
} capnp_segment_entry_t;

// Cap'n Proto message builder
#define CAPNP_MAX_SEGMENTS 16
typedef struct {
    uint8_t *segments[CAPNP_MAX_SEGMENTS];
    size_t segment_sizes[CAPNP_MAX_SEGMENTS];
    size_t segment_used[CAPNP_MAX_SEGMENTS];
    uint32_t segment_count;
    uint32_t current_segment;
} capnp_builder_t;

// Cap'n Proto message reader
typedef struct {
    const uint8_t *segments[CAPNP_MAX_SEGMENTS];
    size_t segment_sizes[CAPNP_MAX_SEGMENTS];
    uint32_t segment_count;
    uint64_t traversal_limit;
    uint64_t traversal_used;
} capnp_reader_t;

// Message descriptor
typedef struct {
    uint32_t size;
    uint32_t type;
} msg_desc_t;

// Function declarations
size_t capnp_msg_desc_size(const msg_desc_t* desc);  /* Renamed to avoid conflict with ipc.h */
void capnp_init(void);

// Cap'n Proto pointer constructors
capnp_pointer_t capnp_make_struct_pointer(uint32_t offset, uint16_t data_words, uint16_t ptr_words);
capnp_pointer_t capnp_make_list_pointer(uint32_t offset, capnp_list_element_type_t element_type, uint32_t count);
capnp_pointer_t capnp_make_far_pointer(uint32_t segment_id, uint32_t offset, bool landing_pad);

// Cap'n Proto builder API
capnp_error_t capnp_builder_init(capnp_builder_t *builder, uint8_t *buffer, size_t buffer_size);
void *capnp_builder_alloc(capnp_builder_t *builder, size_t bytes);
capnp_error_t capnp_builder_new_segment(capnp_builder_t *builder, size_t min_size);

// Utility functions
size_t capnp_align_to_word(size_t bytes);
size_t capnp_bytes_to_words(size_t bytes);
size_t capnp_words_to_bytes(size_t words);

// Static assertions for ABI compatibility
_Static_assert(sizeof(capnp_pointer_t) == 8, "Cap'n Proto pointer must be 64-bit");
_Static_assert(sizeof(msg_desc_t) == 8, "Message descriptor must be 64-bit aligned");