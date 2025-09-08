/**
 * @file capnp_kernel.c
 * @brief Minimal Cap'n Proto implementation for kernel space
 * 
 * Pure C17 implementation of Cap'n Proto serialization primitives
 * designed for zero-copy message passing in kernel space.
 * No dynamic allocation, no external dependencies.
 */

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <string.h>
#include "spinlock.h"
#include "defs.h"

// Cap'n Proto pointer types
typedef uint64_t capnp_ptr_t;

// Pointer type tags (2 LSBs)
#define CAPNP_PTR_TYPE_MASK     0x3
#define CAPNP_PTR_TYPE_STRUCT   0x0
#define CAPNP_PTR_TYPE_LIST     0x1
#define CAPNP_PTR_TYPE_FAR      0x2
#define CAPNP_PTR_TYPE_OTHER    0x3

// Struct pointer layout (type = 0)
#define CAPNP_STRUCT_PTR_OFFSET_SHIFT  2
#define CAPNP_STRUCT_PTR_OFFSET_MASK   0x3FFFFFFF
#define CAPNP_STRUCT_PTR_DATA_SIZE_SHIFT 32
#define CAPNP_STRUCT_PTR_DATA_SIZE_MASK  0xFFFF
#define CAPNP_STRUCT_PTR_PTR_SIZE_SHIFT  48
#define CAPNP_STRUCT_PTR_PTR_SIZE_MASK   0xFFFF

// List pointer layout (type = 1)
#define CAPNP_LIST_PTR_OFFSET_SHIFT    2
#define CAPNP_LIST_PTR_OFFSET_MASK     0x3FFFFFFF
#define CAPNP_LIST_PTR_ELEM_SIZE_SHIFT 32
#define CAPNP_LIST_PTR_ELEM_SIZE_MASK  0x7
#define CAPNP_LIST_PTR_COUNT_SHIFT     35
#define CAPNP_LIST_PTR_COUNT_MASK      0x1FFFFFFF

// List element sizes
typedef enum {
    CAPNP_LIST_ELEM_VOID = 0,
    CAPNP_LIST_ELEM_BIT = 1,
    CAPNP_LIST_ELEM_BYTE = 2,
    CAPNP_LIST_ELEM_TWO_BYTES = 3,
    CAPNP_LIST_ELEM_FOUR_BYTES = 4,
    CAPNP_LIST_ELEM_EIGHT_BYTES = 5,
    CAPNP_LIST_ELEM_POINTER = 6,
    CAPNP_LIST_ELEM_COMPOSITE = 7
} capnp_list_elem_size_t;

// Message segment
typedef struct {
    void *data;
    size_t size;
    size_t used;
} capnp_segment_t;

// Message builder
typedef struct {
    capnp_segment_t *segments;
    size_t segment_count;
    size_t current_segment;
    struct spinlock lock;
} capnp_builder_t;

// Message reader
typedef struct {
    const void **segments;
    const uint32_t *segment_sizes;
    size_t segment_count;
} capnp_reader_t;

// Error codes
typedef enum {
    CAPNP_OK = 0,
    CAPNP_ERROR_INVALID_MESSAGE = -1,
    CAPNP_ERROR_OUT_OF_MEMORY = -2,
    CAPNP_ERROR_INVALID_POINTER = -3,
    CAPNP_ERROR_OUT_OF_BOUNDS = -4
} capnp_error_t;

/**
 * Initialize a message builder with pre-allocated segments
 */
capnp_error_t capnp_builder_init(capnp_builder_t *builder, 
                                 capnp_segment_t *segments,
                                 size_t segment_count) {
    if (!builder || !segments || segment_count == 0) {
        return CAPNP_ERROR_INVALID_MESSAGE;
    }
    
    builder->segments = segments;
    builder->segment_count = segment_count;
    builder->current_segment = 0;
    builder->segments[0].used = 0;
    
    initlock(&builder->lock, "capnp_builder");
    return CAPNP_OK;
}

/**
 * Allocate space in current segment
 */
static void *capnp_builder_allocate(capnp_builder_t *builder, size_t size) {
    if (builder->current_segment >= builder->segment_count) {
        return NULL;
    }
    
    capnp_segment_t *seg = &builder->segments[builder->current_segment];
    
    // Align to 8 bytes
    size = (size + 7) & ~7;
    
    if (seg->used + size > seg->size) {
        // Try next segment
        if (builder->current_segment + 1 < builder->segment_count) {
            builder->current_segment++;
            seg = &builder->segments[builder->current_segment];
            seg->used = 0;
        } else {
            return NULL; // Out of memory
        }
    }
    
    void *ptr = (char *)seg->data + seg->used;
    seg->used += size;
    
    // Zero the allocated memory
    memset(ptr, 0, size);
    
    return ptr;
}

/**
 * Build a struct pointer
 */
capnp_ptr_t capnp_build_struct_ptr(int32_t offset, uint16_t data_size, uint16_t ptr_size) {
    capnp_ptr_t ptr = 0;
    
    ptr |= CAPNP_PTR_TYPE_STRUCT;
    ptr |= ((uint64_t)(offset & CAPNP_STRUCT_PTR_OFFSET_MASK)) << CAPNP_STRUCT_PTR_OFFSET_SHIFT;
    ptr |= ((uint64_t)(data_size & CAPNP_STRUCT_PTR_DATA_SIZE_MASK)) << CAPNP_STRUCT_PTR_DATA_SIZE_SHIFT;
    ptr |= ((uint64_t)(ptr_size & CAPNP_STRUCT_PTR_PTR_SIZE_MASK)) << CAPNP_STRUCT_PTR_PTR_SIZE_SHIFT;
    
    return ptr;
}

/**
 * Build a list pointer
 */
capnp_ptr_t capnp_build_list_ptr(int32_t offset, capnp_list_elem_size_t elem_size, uint32_t count) {
    capnp_ptr_t ptr = 0;
    
    ptr |= CAPNP_PTR_TYPE_LIST;
    ptr |= ((uint64_t)(offset & CAPNP_LIST_PTR_OFFSET_MASK)) << CAPNP_LIST_PTR_OFFSET_SHIFT;
    ptr |= ((uint64_t)(elem_size & CAPNP_LIST_PTR_ELEM_SIZE_MASK)) << CAPNP_LIST_PTR_ELEM_SIZE_SHIFT;
    ptr |= ((uint64_t)(count & CAPNP_LIST_PTR_COUNT_MASK)) << CAPNP_LIST_PTR_COUNT_SHIFT;
    
    return ptr;
}

/**
 * Extract pointer type
 */
static inline uint8_t capnp_ptr_type(capnp_ptr_t ptr) {
    return ptr & CAPNP_PTR_TYPE_MASK;
}

/**
 * Extract struct pointer fields
 */
static inline int32_t capnp_struct_ptr_offset(capnp_ptr_t ptr) {
    int32_t offset = (ptr >> CAPNP_STRUCT_PTR_OFFSET_SHIFT) & CAPNP_STRUCT_PTR_OFFSET_MASK;
    // Sign extend if negative
    if (offset & 0x20000000) {
        offset |= 0xC0000000;
    }
    return offset;
}

static inline uint16_t capnp_struct_ptr_data_size(capnp_ptr_t ptr) {
    return (ptr >> CAPNP_STRUCT_PTR_DATA_SIZE_SHIFT) & CAPNP_STRUCT_PTR_DATA_SIZE_MASK;
}

static inline uint16_t capnp_struct_ptr_ptr_size(capnp_ptr_t ptr) {
    return (ptr >> CAPNP_STRUCT_PTR_PTR_SIZE_SHIFT) & CAPNP_STRUCT_PTR_PTR_SIZE_MASK;
}

/**
 * Extract list pointer fields
 */
static inline int32_t capnp_list_ptr_offset(capnp_ptr_t ptr) {
    int32_t offset = (ptr >> CAPNP_LIST_PTR_OFFSET_SHIFT) & CAPNP_LIST_PTR_OFFSET_MASK;
    // Sign extend if negative
    if (offset & 0x20000000) {
        offset |= 0xC0000000;
    }
    return offset;
}

static inline capnp_list_elem_size_t capnp_list_ptr_elem_size(capnp_ptr_t ptr) {
    return (ptr >> CAPNP_LIST_PTR_ELEM_SIZE_SHIFT) & CAPNP_LIST_PTR_ELEM_SIZE_MASK;
}

static inline uint32_t capnp_list_ptr_count(capnp_ptr_t ptr) {
    return (ptr >> CAPNP_LIST_PTR_COUNT_SHIFT) & CAPNP_LIST_PTR_COUNT_MASK;
}

/**
 * Create a new struct in the message
 */
void *capnp_new_struct(capnp_builder_t *builder, capnp_ptr_t *out_ptr,
                      uint16_t data_words, uint16_t ptr_words) {
    size_t size = (data_words + ptr_words) * 8;
    
    acquire(&builder->lock);
    void *data = capnp_builder_allocate(builder, size);
    release(&builder->lock);
    
    if (!data) {
        return NULL;
    }
    
    // Build pointer to this struct (offset = 0 since ptr immediately precedes data)
    *out_ptr = capnp_build_struct_ptr(0, data_words, ptr_words);
    
    return data;
}

/**
 * Create a new list in the message
 */
void *capnp_new_list(capnp_builder_t *builder, capnp_ptr_t *out_ptr,
                    capnp_list_elem_size_t elem_size, uint32_t count) {
    size_t elem_bytes = 0;
    
    switch (elem_size) {
        case CAPNP_LIST_ELEM_VOID: elem_bytes = 0; break;
        case CAPNP_LIST_ELEM_BIT: elem_bytes = 1; break; // Pack 8 per byte
        case CAPNP_LIST_ELEM_BYTE: elem_bytes = 1; break;
        case CAPNP_LIST_ELEM_TWO_BYTES: elem_bytes = 2; break;
        case CAPNP_LIST_ELEM_FOUR_BYTES: elem_bytes = 4; break;
        case CAPNP_LIST_ELEM_EIGHT_BYTES: elem_bytes = 8; break;
        case CAPNP_LIST_ELEM_POINTER: elem_bytes = 8; break;
        case CAPNP_LIST_ELEM_COMPOSITE: 
            // Composite lists have a tag word followed by the elements
            elem_bytes = 8; // Will be multiplied by element count
            break;
    }
    
    size_t size = elem_bytes * count;
    if (elem_size == CAPNP_LIST_ELEM_BIT) {
        size = (count + 7) / 8; // Round up for bit packing
    }
    
    acquire(&builder->lock);
    void *data = capnp_builder_allocate(builder, size);
    release(&builder->lock);
    
    if (!data) {
        return NULL;
    }
    
    *out_ptr = capnp_build_list_ptr(0, elem_size, count);
    
    return data;
}

/**
 * Read a struct from a message
 */
const void *capnp_read_struct(const capnp_reader_t *reader, capnp_ptr_t ptr,
                             uint16_t *data_words, uint16_t *ptr_words) {
    if (capnp_ptr_type(ptr) != CAPNP_PTR_TYPE_STRUCT) {
        return NULL;
    }
    
    if (data_words) {
        *data_words = capnp_struct_ptr_data_size(ptr);
    }
    if (ptr_words) {
        *ptr_words = capnp_struct_ptr_ptr_size(ptr);
    }
    
    // For simplicity, assume pointer is in first segment
    // Real implementation would handle far pointers and multiple segments
    int32_t offset = capnp_struct_ptr_offset(ptr);
    
    // Pointer points to the word after itself, so add 1
    const uint64_t *base = (const uint64_t *)reader->segments[0];
    return base + offset + 1;
}

/**
 * Read a list from a message
 */
const void *capnp_read_list(const capnp_reader_t *reader, capnp_ptr_t ptr,
                           capnp_list_elem_size_t *elem_size, uint32_t *count) {
    if (capnp_ptr_type(ptr) != CAPNP_PTR_TYPE_LIST) {
        return NULL;
    }
    
    if (elem_size) {
        *elem_size = capnp_list_ptr_elem_size(ptr);
    }
    if (count) {
        *count = capnp_list_ptr_count(ptr);
    }
    
    int32_t offset = capnp_list_ptr_offset(ptr);
    
    const uint64_t *base = (const uint64_t *)reader->segments[0];
    return base + offset + 1;
}

/**
 * Initialize a message reader
 */
capnp_error_t capnp_reader_init(capnp_reader_t *reader,
                               const void **segments,
                               const uint32_t *segment_sizes,
                               size_t segment_count) {
    if (!reader || !segments || !segment_sizes || segment_count == 0) {
        return CAPNP_ERROR_INVALID_MESSAGE;
    }
    
    reader->segments = segments;
    reader->segment_sizes = segment_sizes;
    reader->segment_count = segment_count;
    
    return CAPNP_OK;
}

// Export symbols for kernel use
void capnp_init(void) {
    // Any global initialization if needed
}