#pragma once

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

// =============================================================================
// CORE TYPE DEFINITIONS
// =============================================================================

// Cap'n Proto message header structure
typedef struct {
  uint32_t segment_count; // Number of segments in message
  uint32_t reserved;      // Must be zero
} __attribute__((packed)) capnp_message_header_t;

// Segment table entry
typedef struct {
  uint32_t size_words; // Size of segment in 8-byte words
} __attribute__((packed)) capnp_segment_entry_t;

// Pointer types (encoded in low 2 bits)
typedef enum {
  CAPNP_PTR_STRUCT = 0,
  CAPNP_PTR_LIST = 1,
  CAPNP_PTR_FAR = 2,
  CAPNP_PTR_OTHER = 3
} capnp_pointer_type_t;

// List element types
typedef enum {
  CAPNP_LIST_VOID = 0,
  CAPNP_LIST_BIT = 1,
  CAPNP_LIST_BYTE = 2,
  CAPNP_LIST_TWO_BYTES = 3,
  CAPNP_LIST_FOUR_BYTES = 4,
  CAPNP_LIST_EIGHT_BYTES = 5,
  CAPNP_LIST_POINTER = 6,
  CAPNP_LIST_COMPOSITE = 7
} capnp_list_element_type_t;

// Generic pointer structure
typedef union {
  uint64_t raw;
  struct {
    uint64_t type : 2;
    uint64_t data : 62;
  } common;
  struct {
    uint64_t type : 2;        // CAPNP_PTR_STRUCT
    uint64_t offset : 30;     // Offset to struct in words
    uint64_t data_words : 16; // Size of data section
    uint64_t ptr_words : 16;  // Size of pointer section
  } struct_ptr;
  struct {
    uint64_t type : 2;           // CAPNP_PTR_LIST
    uint64_t offset : 30;        // Offset to list in words
    uint64_t element_type : 3;   // List element type
    uint64_t element_count : 29; // Number of elements
  } list_ptr;
  struct {
    uint64_t type : 2;        // CAPNP_PTR_FAR
    uint64_t landing_pad : 1; // Is this a landing pad?
    uint64_t offset : 29;     // Offset in target segment
    uint64_t segment_id : 32; // Target segment ID
  } far_ptr;
} __attribute__((packed)) capnp_pointer_t;

// Message builder context
typedef struct {
  uint8_t *segments[16];    // Segment pointers (max 16 segments)
  size_t segment_sizes[16]; // Segment sizes in bytes
  size_t segment_used[16];  // Used bytes in each segment
  uint32_t segment_count;   // Number of segments
  uint32_t current_segment; // Current segment for allocation
} capnp_builder_t;

// Message reader context
typedef struct {
  const uint8_t *segments[16]; // Segment pointers
  size_t segment_sizes[16];    // Segment sizes in bytes
  uint32_t segment_count;      // Number of segments
  size_t traversal_limit;      // Limit for traversal depth/size
  size_t traversal_used;       // Used traversal budget
} capnp_reader_t;

// Schema field descriptor
typedef struct {
  uint32_t offset; // Offset in struct (in bits for data, in pointers for ptrs)
  uint32_t type;   // Field type identifier
  uint64_t default_value; // Default value for primitive types
  bool is_pointer;        // True if this is a pointer field
} capnp_field_t;

// Schema structure descriptor
typedef struct {
  const char *name;            // Structure name
  uint16_t data_words;         // Size of data section in words
  uint16_t ptr_words;          // Size of pointer section in words
  uint32_t field_count;        // Number of fields
  const capnp_field_t *fields; // Field descriptors
} capnp_struct_schema_t;

// Error codes
typedef enum {
  CAPNP_OK = 0,
  CAPNP_ERROR_INVALID_MESSAGE = -1,
  CAPNP_ERROR_BUFFER_TOO_SMALL = -2,
  CAPNP_ERROR_OUT_OF_MEMORY = -3,
  CAPNP_ERROR_INVALID_POINTER = -4,
  CAPNP_ERROR_TRAVERSAL_LIMIT = -5,
  CAPNP_ERROR_INVALID_SCHEMA = -6
} capnp_error_t;

// =============================================================================
// MESSAGE BUILDING API
// =============================================================================

// Initialize a message builder
capnp_error_t capnp_builder_init(capnp_builder_t *builder, uint8_t *buffer,
                                 size_t buffer_size);

// Allocate space in current segment
void *capnp_builder_alloc(capnp_builder_t *builder, size_t bytes);

// Allocate a new segment
capnp_error_t capnp_builder_new_segment(capnp_builder_t *builder,
                                        size_t min_size);

// Build a struct with given schema
void *capnp_builder_new_struct(capnp_builder_t *builder,
                               const capnp_struct_schema_t *schema);

// Build a list
void *capnp_builder_new_list(capnp_builder_t *builder,
                             capnp_list_element_type_t element_type,
                             uint32_t count);

// Set primitive fields
capnp_error_t capnp_builder_set_uint8(void *struct_ptr,
                                      const capnp_field_t *field,
                                      uint8_t value);
capnp_error_t capnp_builder_set_uint16(void *struct_ptr,
                                       const capnp_field_t *field,
                                       uint16_t value);
capnp_error_t capnp_builder_set_uint32(void *struct_ptr,
                                       const capnp_field_t *field,
                                       uint32_t value);
capnp_error_t capnp_builder_set_uint64(void *struct_ptr,
                                       const capnp_field_t *field,
                                       uint64_t value);
capnp_error_t capnp_builder_set_float32(void *struct_ptr,
                                        const capnp_field_t *field,
                                        float value);
capnp_error_t capnp_builder_set_float64(void *struct_ptr,
                                        const capnp_field_t *field,
                                        double value);

// Set pointer fields
capnp_error_t capnp_builder_set_struct(void *struct_ptr,
                                       const capnp_field_t *field,
                                       void *target_struct);
capnp_error_t capnp_builder_set_list(void *struct_ptr,
                                     const capnp_field_t *field,
                                     void *target_list);
capnp_error_t capnp_builder_set_text(capnp_builder_t *builder, void *struct_ptr,
                                     const capnp_field_t *field,
                                     const char *text);
capnp_error_t capnp_builder_set_data(capnp_builder_t *builder, void *struct_ptr,
                                     const capnp_field_t *field,
                                     const void *data, size_t len);

// Finalize message and get serialized size
size_t capnp_builder_finalize(capnp_builder_t *builder, uint8_t *output_buffer,
                              size_t buffer_size);

// =============================================================================
// MESSAGE READING API
// =============================================================================

// Initialize a message reader
capnp_error_t capnp_reader_init(capnp_reader_t *reader, const uint8_t *buffer,
                                size_t buffer_size, size_t traversal_limit);

// Get root struct from message
void *capnp_reader_get_root(capnp_reader_t *reader,
                            const capnp_struct_schema_t *schema);

// Read primitive fields
uint8_t capnp_reader_get_uint8(const void *struct_ptr,
                               const capnp_field_t *field);
uint16_t capnp_reader_get_uint16(const void *struct_ptr,
                                 const capnp_field_t *field);
uint32_t capnp_reader_get_uint32(const void *struct_ptr,
                                 const capnp_field_t *field);
uint64_t capnp_reader_get_uint64(const void *struct_ptr,
                                 const capnp_field_t *field);
float capnp_reader_get_float32(const void *struct_ptr,
                               const capnp_field_t *field);
double capnp_reader_get_float64(const void *struct_ptr,
                                const capnp_field_t *field);

// Read pointer fields
void *capnp_reader_get_struct(capnp_reader_t *reader, const void *struct_ptr,
                              const capnp_field_t *field,
                              const capnp_struct_schema_t *schema);
void *capnp_reader_get_list(capnp_reader_t *reader, const void *struct_ptr,
                            const capnp_field_t *field);
const char *capnp_reader_get_text(capnp_reader_t *reader,
                                  const void *struct_ptr,
                                  const capnp_field_t *field);
const void *capnp_reader_get_data(capnp_reader_t *reader,
                                  const void *struct_ptr,
                                  const capnp_field_t *field, size_t *len_out);

// List iteration
uint32_t capnp_list_get_size(const void *list_ptr);
void *capnp_list_get_element(const void *list_ptr, uint32_t index);

// =============================================================================
// UTILITY FUNCTIONS
// =============================================================================

// Validate message structure
capnp_error_t capnp_validate_message(const uint8_t *buffer, size_t buffer_size);

// Calculate message size requirements
size_t capnp_calculate_message_size(const capnp_struct_schema_t *schema,
                                    size_t estimated_data_size);

// Pointer manipulation utilities
capnp_pointer_t capnp_make_struct_pointer(uint32_t offset, uint16_t data_words,
                                          uint16_t ptr_words);
capnp_pointer_t capnp_make_list_pointer(uint32_t offset,
                                        capnp_list_element_type_t element_type,
                                        uint32_t count);
capnp_pointer_t capnp_make_far_pointer(uint32_t segment_id, uint32_t offset,
                                       bool landing_pad);

// Endianness handling
uint16_t capnp_le16(uint16_t value);
uint32_t capnp_le32(uint32_t value);
uint64_t capnp_le64(uint64_t value);

// Memory alignment utilities
size_t capnp_align_to_word(size_t bytes);
size_t capnp_bytes_to_words(size_t bytes);
size_t capnp_words_to_bytes(size_t words);

// =============================================================================
// LEGACY COMPATIBILITY API
// =============================================================================

// Original function signatures for backward compatibility
size_t capnp_encode(const void *msg, size_t len, unsigned char *buf);
size_t capnp_decode(void *msg, size_t len, const unsigned char *buf);

// High-level encode/decode with schema
size_t capnp_encode_struct(const void *struct_data,
                           const capnp_struct_schema_t *schema, uint8_t *buffer,
                           size_t buffer_size);
capnp_error_t capnp_decode_struct(void *struct_data,
                                  const capnp_struct_schema_t *schema,
                                  const uint8_t *buffer, size_t buffer_size);

// =============================================================================
// SCHEMA DEFINITION MACROS
// =============================================================================

// Macro to define a field descriptor
#define CAPNP_FIELD(name, offset, type, is_ptr, default_val)                   \
  {.offset = (offset),                                                         \
   .type = (type),                                                             \
   .default_value = (default_val),                                             \
   .is_pointer = (is_ptr)}

// Macro to define a struct schema
#define CAPNP_STRUCT_SCHEMA(name, data_words, ptr_words, field_array)          \
  {.name = #name,                                                              \
   .data_words = (data_words),                                                 \
   .ptr_words = (ptr_words),                                                   \
   .field_count = sizeof(field_array) / sizeof(capnp_field_t),                 \
   .fields = (field_array)}

// Field type constants
#define CAPNP_TYPE_VOID 0
#define CAPNP_TYPE_BOOL 1
#define CAPNP_TYPE_INT8 2
#define CAPNP_TYPE_INT16 3
#define CAPNP_TYPE_INT32 4
#define CAPNP_TYPE_INT64 5
#define CAPNP_TYPE_UINT8 6
#define CAPNP_TYPE_UINT16 7
#define CAPNP_TYPE_UINT32 8
#define CAPNP_TYPE_UINT64 9
#define CAPNP_TYPE_FLOAT32 10
#define CAPNP_TYPE_FLOAT64 11
#define CAPNP_TYPE_TEXT 12
#define CAPNP_TYPE_DATA 13
#define CAPNP_TYPE_LIST 14
#define CAPNP_TYPE_ENUM 15
#define CAPNP_TYPE_STRUCT 16
#define CAPNP_TYPE_INTERFACE 17
#define CAPNP_TYPE_ANYPOINTER 18

// =============================================================================
// ADVANCED FEATURES
// =============================================================================

// Message packing for reduced size
size_t capnp_pack_message(const uint8_t *unpacked, size_t unpacked_size,
                          uint8_t *packed, size_t packed_buffer_size);
size_t capnp_unpack_message(const uint8_t *packed, size_t packed_size,
                            uint8_t *unpacked, size_t unpacked_buffer_size);

// Zero-copy string/data handling
typedef struct {
  const uint8_t *data;
  size_t length;
} capnp_data_slice_t;

capnp_data_slice_t capnp_reader_get_data_slice(capnp_reader_t *reader,
                                               const void *struct_ptr,
                                               const capnp_field_t *field);

// Message streaming support
typedef struct {
  uint8_t *buffer;
  size_t buffer_size;
  size_t position;
  size_t message_size;
} capnp_stream_t;

capnp_error_t capnp_stream_init(capnp_stream_t *stream, uint8_t *buffer,
                                size_t buffer_size);
capnp_error_t capnp_stream_write_message(capnp_stream_t *stream,
                                         const uint8_t *message,
                                         size_t message_size);
capnp_error_t capnp_stream_read_message(capnp_stream_t *stream,
                                        uint8_t *message_buffer,
                                        size_t buffer_size,
                                        size_t *message_size_out);

#ifdef __cplusplus
}
#endif
