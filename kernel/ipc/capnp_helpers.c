#include "capnp_helpers.h"
#include <string.h>
#include <stdlib.h>

// =============================================================================
// UTILITY FUNCTIONS IMPLEMENTATION
// =============================================================================

static inline uint16_t capnp_le16(uint16_t value) {
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  return value;
#else
  return ((value & 0xFF) << 8) | ((value >> 8) & 0xFF);
#endif
}

static inline uint32_t capnp_le32(uint32_t value) {
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  return value;
#else
  return ((value & 0xFF) << 24) | (((value >> 8) & 0xFF) << 16) |
         (((value >> 16) & 0xFF) << 8) | ((value >> 24) & 0xFF);
#endif
}

static inline uint64_t capnp_le64(uint64_t value) {
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
  return value;
#else
  return ((uint64_t)capnp_le32(value & 0xFFFFFFFF) << 32) |
         capnp_le32(value >> 32);
#endif
}

size_t capnp_align_to_word(size_t bytes) { return (bytes + 7) & ~7; }

size_t capnp_bytes_to_words(size_t bytes) { return (bytes + 7) / 8; }

size_t capnp_words_to_bytes(size_t words) { return words * 8; }

// =============================================================================
// POINTER UTILITIES
// =============================================================================

capnp_pointer_t capnp_make_struct_pointer(uint32_t offset, uint16_t data_words,
                                          uint16_t ptr_words) {
  capnp_pointer_t ptr = {0};
  ptr.struct_ptr.type = CAPNP_PTR_STRUCT;
  ptr.struct_ptr.offset = offset;
  ptr.struct_ptr.data_words = data_words;
  ptr.struct_ptr.ptr_words = ptr_words;
  return ptr;
}

capnp_pointer_t capnp_make_list_pointer(uint32_t offset,
                                        capnp_list_element_type_t element_type,
                                        uint32_t count) {
  capnp_pointer_t ptr = {0};
  ptr.list_ptr.type = CAPNP_PTR_LIST;
  ptr.list_ptr.offset = offset;
  ptr.list_ptr.element_type = element_type;
  ptr.list_ptr.element_count = count;
  return ptr;
}

capnp_pointer_t capnp_make_far_pointer(uint32_t segment_id, uint32_t offset,
                                       bool landing_pad) {
  capnp_pointer_t ptr = {0};
  ptr.far_ptr.type = CAPNP_PTR_FAR;
  ptr.far_ptr.segment_id = segment_id;
  ptr.far_ptr.offset = offset;
  ptr.far_ptr.landing_pad = landing_pad ? 1 : 0;
  return ptr;
}

// =============================================================================
// MESSAGE BUILDER IMPLEMENTATION
// =============================================================================

capnp_error_t capnp_builder_init(capnp_builder_t *builder, uint8_t *buffer,
                                 size_t buffer_size) {
  if (!builder || !buffer || buffer_size < 16) {
    return CAPNP_ERROR_INVALID_MESSAGE;
  }

  memset(builder, 0, sizeof(*builder));
  builder->segments[0] = buffer;
  builder->segment_sizes[0] = buffer_size;
  builder->segment_used[0] = 0;
  builder->segment_count = 1;
  builder->current_segment = 0;

  return CAPNP_OK;
}

void *capnp_builder_alloc(capnp_builder_t *builder, size_t bytes) {
  if (!builder)
    return NULL;

  size_t aligned_bytes = capnp_align_to_word(bytes);
  uint32_t seg = builder->current_segment;

  if (builder->segment_used[seg] + aligned_bytes >
      builder->segment_sizes[seg]) {
    // Try to allocate new segment
    if (capnp_builder_new_segment(builder, aligned_bytes) != CAPNP_OK) {
      return NULL;
    }
    seg = builder->current_segment;
  }

  void *ptr = builder->segments[seg] + builder->segment_used[seg];
  builder->segment_used[seg] += aligned_bytes;

  // Zero-initialize allocated memory
  memset(ptr, 0, aligned_bytes);

  return ptr;
}

capnp_error_t capnp_builder_new_segment(capnp_builder_t *builder,
                                        size_t min_size) {
  if (!builder || builder->segment_count >= 16) {
    return CAPNP_ERROR_OUT_OF_MEMORY;
  }

  // For simplicity, we don't actually allocate new segments in this
  // implementation In a real implementation, you'd allocate new memory here
  return CAPNP_ERROR_OUT_OF_MEMORY;
}

void *capnp_builder_new_struct(capnp_builder_t *builder,
                               const capnp_struct_schema_t *schema) {
  if (!builder || !schema)
    return NULL;

  size_t struct_size =
      capnp_words_to_bytes(schema->data_words + schema->ptr_words);
  return capnp_builder_alloc(builder, struct_size);
}

void *capnp_builder_new_list(capnp_builder_t *builder,
                             capnp_list_element_type_t element_type,
                             uint32_t count) {
  if (!builder)
    return NULL;

  size_t element_size = 0;
  switch (element_type) {
  case CAPNP_LIST_VOID:
    element_size = 0;
    break;
  case CAPNP_LIST_BIT:
    element_size = (count + 7) / 8;
    break;
  case CAPNP_LIST_BYTE:
    element_size = count;
    break;
  case CAPNP_LIST_TWO_BYTES:
    element_size = count * 2;
    break;
  case CAPNP_LIST_FOUR_BYTES:
    element_size = count * 4;
    break;
  case CAPNP_LIST_EIGHT_BYTES:
    element_size = count * 8;
    break;
  case CAPNP_LIST_POINTER:
    element_size = count * 8;
    break;
  case CAPNP_LIST_COMPOSITE:
    element_size = count * 8;
    break; // Simplified
  }

  return capnp_builder_alloc(builder, element_size);
}

// =============================================================================
// FIELD SETTERS
// =============================================================================

capnp_error_t capnp_builder_set_uint8(void *struct_ptr,
                                      const capnp_field_t *field,
                                      uint8_t value) {
  if (!struct_ptr || !field || field->is_pointer)
    return CAPNP_ERROR_INVALID_SCHEMA;

  uint8_t *data_ptr = (uint8_t *)struct_ptr + (field->offset / 8);
  *data_ptr = value ^ (uint8_t)field->default_value;
  return CAPNP_OK;
}

capnp_error_t capnp_builder_set_uint16(void *struct_ptr,
                                       const capnp_field_t *field,
                                       uint16_t value) {
  if (!struct_ptr || !field || field->is_pointer)
    return CAPNP_ERROR_INVALID_SCHEMA;

  uint16_t *data_ptr =
      (uint16_t *)((uint8_t *)struct_ptr + (field->offset / 8));
  *data_ptr = capnp_le16(value ^ (uint16_t)field->default_value);
  return CAPNP_OK;
}

capnp_error_t capnp_builder_set_uint32(void *struct_ptr,
                                       const capnp_field_t *field,
                                       uint32_t value) {
  if (!struct_ptr || !field || field->is_pointer)
    return CAPNP_ERROR_INVALID_SCHEMA;

  uint32_t *data_ptr =
      (uint32_t *)((uint8_t *)struct_ptr + (field->offset / 8));
  *data_ptr = capnp_le32(value ^ (uint32_t)field->default_value);
  return CAPNP_OK;
}

capnp_error_t capnp_builder_set_uint64(void *struct_ptr,
                                       const capnp_field_t *field,
                                       uint64_t value) {
  if (!struct_ptr || !field || field->is_pointer)
    return CAPNP_ERROR_INVALID_SCHEMA;

  uint64_t *data_ptr =
      (uint64_t *)((uint8_t *)struct_ptr + (field->offset / 8));
  *data_ptr = capnp_le64(value ^ field->default_value);
  return CAPNP_OK;
}

capnp_error_t capnp_builder_set_text(capnp_builder_t *builder, void *struct_ptr,
                                     const capnp_field_t *field,
                                     const char *text) {
  if (!builder || !struct_ptr || !field || !field->is_pointer || !text) {
    return CAPNP_ERROR_INVALID_SCHEMA;
  }

  size_t text_len = strlen(text);
  size_t total_size = text_len + 1; // Include null terminator

  // Allocate space for the text
  char *text_data = (char *)capnp_builder_alloc(builder, total_size);
  if (!text_data)
    return CAPNP_ERROR_OUT_OF_MEMORY;

  memcpy(text_data, text, text_len);
  text_data[text_len] = '\0';

  // Create list pointer for text (text is a list of bytes)
  capnp_pointer_t ptr =
      capnp_make_list_pointer(0, CAPNP_LIST_BYTE, text_len + 1);

  // Calculate offset from struct to text data
  uintptr_t struct_addr = (uintptr_t)struct_ptr;
  uintptr_t text_addr = (uintptr_t)text_data;
  uint32_t offset_words =
      (text_addr - struct_addr - 8) / 8; // -8 for pointer itself
  ptr.list_ptr.offset = offset_words;

  // Set the pointer in the struct
  capnp_pointer_t *ptr_field =
      (capnp_pointer_t *)((uint8_t *)struct_ptr + field->offset);
  ptr_field->raw = capnp_le64(ptr.raw);

  return CAPNP_OK;
}

// =============================================================================
// MESSAGE FINALIZATION
// =============================================================================

size_t capnp_builder_finalize(capnp_builder_t *builder, uint8_t *output_buffer,
                              size_t buffer_size) {
  if (!builder || !output_buffer)
    return 0;

  // Calculate total message size
  size_t header_size = sizeof(capnp_message_header_t);
  size_t segment_table_size =
      builder->segment_count * sizeof(capnp_segment_entry_t);
  if (builder->segment_count % 2 == 0) {
    segment_table_size += sizeof(uint32_t); // Padding
  }

  size_t total_segment_size = 0;
  for (uint32_t i = 0; i < builder->segment_count; i++) {
    total_segment_size += capnp_align_to_word(builder->segment_used[i]);
  }

  size_t total_size = header_size + segment_table_size + total_segment_size;

  if (total_size > buffer_size)
    return 0;

  // Write header
  capnp_message_header_t *header = (capnp_message_header_t *)output_buffer;
  header->segment_count =
      capnp_le32(builder->segment_count - 1); // -1 as per spec
  header->reserved = 0;

  size_t offset = header_size;

  // Write segment table
  for (uint32_t i = 0; i < builder->segment_count; i++) {
    capnp_segment_entry_t *entry =
        (capnp_segment_entry_t *)(output_buffer + offset);
    entry->size_words =
        capnp_le32(capnp_bytes_to_words(builder->segment_used[i]));
    offset += sizeof(capnp_segment_entry_t);
  }

  // Add padding if needed
  if (builder->segment_count % 2 == 0) {
    *(uint32_t *)(output_buffer + offset) = 0;
    offset += sizeof(uint32_t);
  }

  // Write segments
  for (uint32_t i = 0; i < builder->segment_count; i++) {
    size_t segment_size = builder->segment_used[i];
    memcpy(output_buffer + offset, builder->segments[i], segment_size);
    offset += capnp_align_to_word(segment_size);
  }

  return total_size;
}

// =============================================================================
// MESSAGE READER IMPLEMENTATION
// =============================================================================

capnp_error_t capnp_reader_init(capnp_reader_t *reader, const uint8_t *buffer,
                                size_t buffer_size, size_t traversal_limit) {
  if (!reader || !buffer || buffer_size < sizeof(capnp_message_header_t)) {
    return CAPNP_ERROR_INVALID_MESSAGE;
  }

  memset(reader, 0, sizeof(*reader));
  reader->traversal_limit = traversal_limit;
  reader->traversal_used = 0;

  const capnp_message_header_t *header = (const capnp_message_header_t *)buffer;
  reader->segment_count =
      capnp_le32(header->segment_count) + 1; // +1 as per spec

  if (reader->segment_count > 16) {
    return CAPNP_ERROR_INVALID_MESSAGE;
  }

  size_t offset = sizeof(capnp_message_header_t);

  // Read segment table
  for (uint32_t i = 0; i < reader->segment_count; i++) {
    if (offset + sizeof(capnp_segment_entry_t) > buffer_size) {
      return CAPNP_ERROR_INVALID_MESSAGE;
    }

    const capnp_segment_entry_t *entry =
        (const capnp_segment_entry_t *)(buffer + offset);
    reader->segment_sizes[i] =
        capnp_words_to_bytes(capnp_le32(entry->size_words));
    offset += sizeof(capnp_segment_entry_t);
  }

  // Skip padding if needed
  if (reader->segment_count % 2 == 0) {
    offset += sizeof(uint32_t);
  }

  // Set segment pointers
  for (uint32_t i = 0; i < reader->segment_count; i++) {
    if (offset + reader->segment_sizes[i] > buffer_size) {
      return CAPNP_ERROR_INVALID_MESSAGE;
    }

    reader->segments[i] = buffer + offset;
    offset += capnp_align_to_word(reader->segment_sizes[i]);
  }

  return CAPNP_OK;
}

void *capnp_reader_get_root(capnp_reader_t *reader,
                            const capnp_struct_schema_t *schema) {
  if (!reader || !schema || reader->segment_count == 0)
    return NULL;

  // Root struct is at the beginning of the first segment
  return (void *)reader->segments[0];
}

// =============================================================================
// FIELD GETTERS
// =============================================================================

uint8_t capnp_reader_get_uint8(const void *struct_ptr,
                               const capnp_field_t *field) {
  if (!struct_ptr || !field || field->is_pointer)
    return (uint8_t)field->default_value;

  const uint8_t *data_ptr = (const uint8_t *)struct_ptr + (field->offset / 8);
  return *data_ptr ^ (uint8_t)field->default_value;
}

uint16_t capnp_reader_get_uint16(const void *struct_ptr,
                                 const capnp_field_t *field) {
  if (!struct_ptr || !field || field->is_pointer)
    return (uint16_t)field->default_value;

  const uint16_t *data_ptr =
      (const uint16_t *)((const uint8_t *)struct_ptr + (field->offset / 8));
  return capnp_le16(*data_ptr) ^ (uint16_t)field->default_value;
}

uint32_t capnp_reader_get_uint32(const void *struct_ptr,
                                 const capnp_field_t *field) {
  if (!struct_ptr || !field || field->is_pointer)
    return (uint32_t)field->default_value;

  const uint32_t *data_ptr =
      (const uint32_t *)((const uint8_t *)struct_ptr + (field->offset / 8));
  return capnp_le32(*data_ptr) ^ (uint32_t)field->default_value;
}

uint64_t capnp_reader_get_uint64(const void *struct_ptr,
                                 const capnp_field_t *field) {
  if (!struct_ptr || !field || field->is_pointer)
    return field->default_value;

  const uint64_t *data_ptr =
      (const uint64_t *)((const uint8_t *)struct_ptr + (field->offset / 8));
  return capnp_le64(*data_ptr) ^ field->default_value;
}

const char *capnp_reader_get_text(capnp_reader_t *reader,
                                  const void *struct_ptr,
                                  const capnp_field_t *field) {
  if (!reader || !struct_ptr || !field || !field->is_pointer)
    return NULL;

  const capnp_pointer_t *ptr_field =
      (const capnp_pointer_t *)((const uint8_t *)struct_ptr + field->offset);
  capnp_pointer_t ptr;
  ptr.raw = capnp_le64(ptr_field->raw);

  if (ptr.common.type != CAPNP_PTR_LIST ||
      ptr.list_ptr.element_type != CAPNP_LIST_BYTE) {
    return NULL;
  }

  // Calculate address of text data
  uintptr_t struct_addr = (uintptr_t)struct_ptr;
  uintptr_t text_addr =
      struct_addr + (field->offset + 8) + (ptr.list_ptr.offset * 8);

  return (const char *)text_addr;
}

// =============================================================================
// LEGACY COMPATIBILITY
// =============================================================================

size_t capnp_encode(const void *msg, size_t len, unsigned char *buf) {
  // Simplified implementation - just copy with basic framing
  if (!msg || !buf || len == 0)
    return 0;

  capnp_message_header_t header = {0, 0};
  size_t total_size =
      sizeof(header) + sizeof(uint32_t) + capnp_align_to_word(len);

  memcpy(buf, &header, sizeof(header));
  size_t offset = sizeof(header);

  uint32_t segment_size = capnp_bytes_to_words(len);
  memcpy(buf + offset, &segment_size, sizeof(segment_size));
  offset += sizeof(segment_size);

  memcpy(buf + offset, msg, len);

  return total_size;
}

size_t capnp_decode(void *msg, size_t len, const unsigned char *buf) {
  // Simplified implementation - just copy with basic validation
  if (!msg || !buf || len == 0)
    return 0;

  size_t offset = sizeof(capnp_message_header_t) + sizeof(uint32_t);
  if (len < offset)
    return 0;

  const uint32_t *segment_size_ptr =
      (const uint32_t *)(buf + sizeof(capnp_message_header_t));
  size_t data_size = capnp_words_to_bytes(*segment_size_ptr);

  if (data_size > len)
    return 0;

  memcpy(msg, buf + offset, data_size);
  return data_size;
}
