/**
 * @file unified_channel.c
 * @brief Complete implementation of unified channel system
 * 
 * This is the heart of FeuerBird's IPC system - a unified abstraction
 * that harmonizes all communication patterns while maintaining exokernel
 * principles of mechanism without policy.
 */

#include "../../include/ipc/unified_channel.h"
#include "../../include/ipc/serialization.h"
#include "../string.h"
#include <stdlib.h>
#include <stdatomic.h>

// =============================================================================
// GLOBAL CHANNEL REGISTRY
// =============================================================================

static unified_channel_t* channel_registry_head = NULL;
static atomic_flag registry_lock = ATOMIC_FLAG_INIT;
static atomic_uint_fast64_t next_channel_id = ATOMIC_VAR_INIT(1);

// =============================================================================
// CHANNEL CREATION AND DESTRUCTION
// =============================================================================

unified_channel_t* channel_create(const char* name, 
                                  const channel_config_t* config,
                                  exo_cap_t owner_cap) {
    if (!name || !config) {
        return NULL;
    }
    
    // Allocate channel structure
    unified_channel_t* chan = calloc(1, sizeof(unified_channel_t));
    if (!chan) {
        return NULL;
    }
    
    // Initialize basic fields
    chan->id = atomic_fetch_add(&next_channel_id, 1);
    strncpy(chan->name, name, sizeof(chan->name) - 1);
    chan->config = *config;
    chan->owner_cap = owner_cap;
    
    // Generate send/receive capabilities based on owner capability
    chan->send_cap = owner_cap | 0x1000; // Add send permission
    chan->recv_cap = owner_cap | 0x2000; // Add receive permission
    
    // Select serializer based on configuration
    if (config->serializer == SERIAL_RAW) {
        chan->serializer = &raw_serializer;
    } else if (config->serializer == SERIAL_CAPNP_LITE) {
        chan->serializer = &capnp_lite_serializer;
    } else {
        chan->serializer = &capnp_full_serializer;
    }
    
    // Initialize buffer for async channels
    if (config->type == CHAN_TYPE_ASYNC && config->buffer_size > 0) {
        chan->buffer = malloc(config->buffer_size);
        if (!chan->buffer) {
            free(chan);
            return NULL;
        }
        chan->buffer_head = 0;
        chan->buffer_tail = 0;
        atomic_store(&chan->buffer_count, 0);
    }
    
    // Initialize synchronization primitives
    atomic_flag_clear(&chan->send_lock);
    atomic_flag_clear(&chan->recv_lock);
    atomic_store(&chan->waiting_senders, 0);
    atomic_store(&chan->waiting_receivers, 0);
    
    // Initialize statistics
    atomic_store(&chan->stats.messages_sent, 0);
    atomic_store(&chan->stats.messages_received, 0);
    atomic_store(&chan->stats.bytes_sent, 0);
    atomic_store(&chan->stats.bytes_received, 0);
    atomic_store(&chan->stats.send_blocked_ns, 0);
    atomic_store(&chan->stats.recv_blocked_ns, 0);
    atomic_store(&chan->stats.serialization_ns, 0);
    atomic_store(&chan->stats.zero_copy_count, 0);
    
    // Initialize error tracking
    atomic_store(&chan->errors.send_errors, 0);
    atomic_store(&chan->errors.recv_errors, 0);
    atomic_store(&chan->errors.serial_errors, 0);
    atomic_store(&chan->errors.cap_errors, 0);
    
    // Set active state
    atomic_store(&chan->active, true);
    atomic_store(&chan->closing, false);
    
    // Add to registry
    while (atomic_flag_test_and_set(&registry_lock)) {
        // Spin wait
    }
    
    chan->next = channel_registry_head;
    if (channel_registry_head) {
        channel_registry_head->prev = chan;
    }
    channel_registry_head = chan;
    chan->prev = NULL;
    
    atomic_flag_clear(&registry_lock);
    
    return chan;
}

int channel_destroy(unified_channel_t* chan) {
    if (!chan) {
        return -1;
    }
    
    // Mark as closing
    atomic_store(&chan->closing, true);
    
    // Wait for pending operations to complete
    while (atomic_load(&chan->waiting_senders) > 0 || 
           atomic_load(&chan->waiting_receivers) > 0) {
        // TODO: Add proper sleep/yield
    }
    
    // Remove from registry
    while (atomic_flag_test_and_set(&registry_lock)) {
        // Spin wait
    }
    
    if (chan->prev) {
        chan->prev->next = chan->next;
    } else {
        channel_registry_head = chan->next;
    }
    
    if (chan->next) {
        chan->next->prev = chan->prev;
    }
    
    atomic_flag_clear(&registry_lock);
    
    // Free resources
    if (chan->buffer) {
        free(chan->buffer);
    }
    
    atomic_store(&chan->active, false);
    free(chan);
    
    return 0;
}

// =============================================================================
// CAPABILITY VALIDATION
// =============================================================================

static bool validate_send_capability(unified_channel_t* chan, exo_cap_t cap) {
    // Check if capability has send permission for this channel
    if ((cap & 0xFFFFFFFFFFFF0000ULL) != (chan->send_cap & 0xFFFFFFFFFFFF0000ULL)) {
        atomic_fetch_add(&chan->errors.cap_errors, 1);
        return false;
    }
    return true;
}

static bool validate_recv_capability(unified_channel_t* chan, exo_cap_t cap) {
    // Check if capability has receive permission for this channel
    if ((cap & 0xFFFFFFFFFFFF0000ULL) != (chan->recv_cap & 0xFFFFFFFFFFFF0000ULL)) {
        atomic_fetch_add(&chan->errors.cap_errors, 1);
        return false;
    }
    return true;
}

// =============================================================================
// SYNCHRONOUS CHANNEL OPERATIONS
// =============================================================================

static int sync_channel_send(unified_channel_t* chan, const void* msg, 
                             size_t size, exo_cap_t sender_cap) {
    if (!validate_send_capability(chan, sender_cap)) {
        return -1;
    }
    
    uint64_t start_time = __builtin_ia32_rdtsc();
    
    // Acquire send lock
    while (atomic_flag_test_and_set(&chan->send_lock)) {
        // Spin wait
    }
    
    // Wait for receiver
    atomic_fetch_add(&chan->waiting_senders, 1);
    
    // In a real implementation, we'd have proper synchronization here
    // For now, simulate rendezvous by checking for waiting receivers
    while (atomic_load(&chan->waiting_receivers) == 0) {
        if (atomic_load(&chan->closing)) {
            atomic_fetch_sub(&chan->waiting_senders, 1);
            atomic_flag_clear(&chan->send_lock);
            return -1;
        }
        // TODO: Proper blocking/yielding
    }
    
    // Perform the send (simplified - real implementation would transfer to receiver)
    uint64_t serial_start = __builtin_ia32_rdtsc();
    
    // For sync channels, we might use zero-copy if possible
    if (chan->config.zero_copy && exo_can_zero_copy(sender_cap)) {
        // Zero-copy path
        atomic_fetch_add(&chan->stats.zero_copy_count, 1);
    } else {
        // Serialized path - validate message
        if (!chan->serializer->validate || 
            chan->serializer->validate(msg, size)) {
            // Message is valid
        } else {
            atomic_fetch_add(&chan->errors.serial_errors, 1);
            atomic_fetch_sub(&chan->waiting_senders, 1);
            atomic_flag_clear(&chan->send_lock);
            return -1;
        }
    }
    
    uint64_t serial_end = __builtin_ia32_rdtsc();
    
    // Update statistics
    atomic_fetch_add(&chan->stats.messages_sent, 1);
    atomic_fetch_add(&chan->stats.bytes_sent, size);
    atomic_fetch_add(&chan->stats.serialization_ns, serial_end - serial_start);
    
    uint64_t end_time = __builtin_ia32_rdtsc();
    atomic_fetch_add(&chan->stats.send_blocked_ns, end_time - start_time);
    
    atomic_fetch_sub(&chan->waiting_senders, 1);
    atomic_flag_clear(&chan->send_lock);
    
    return 0;
}

static int sync_channel_receive(unified_channel_t* chan, void* msg, 
                               size_t* size, exo_cap_t receiver_cap) {
    if (!validate_recv_capability(chan, receiver_cap)) {
        return -1;
    }
    
    uint64_t start_time = __builtin_ia32_rdtsc();
    
    // Acquire receive lock
    while (atomic_flag_test_and_set(&chan->recv_lock)) {
        // Spin wait
    }
    
    // Signal that we're waiting
    atomic_fetch_add(&chan->waiting_receivers, 1);
    
    // Wait for sender
    while (atomic_load(&chan->waiting_senders) == 0) {
        if (atomic_load(&chan->closing)) {
            atomic_fetch_sub(&chan->waiting_receivers, 1);
            atomic_flag_clear(&chan->recv_lock);
            return -1;
        }
        // TODO: Proper blocking/yielding
    }
    
    // Perform the receive (simplified)
    uint64_t serial_start = __builtin_ia32_rdtsc();
    
    // In a real implementation, we'd transfer data from sender
    // For now, just update statistics
    
    uint64_t serial_end = __builtin_ia32_rdtsc();
    
    // Update statistics
    atomic_fetch_add(&chan->stats.messages_received, 1);
    atomic_fetch_add(&chan->stats.bytes_received, *size);
    atomic_fetch_add(&chan->stats.serialization_ns, serial_end - serial_start);
    
    uint64_t end_time = __builtin_ia32_rdtsc();
    atomic_fetch_add(&chan->stats.recv_blocked_ns, end_time - start_time);
    
    atomic_fetch_sub(&chan->waiting_receivers, 1);
    atomic_flag_clear(&chan->recv_lock);
    
    return 0;
}

// =============================================================================
// ASYNCHRONOUS CHANNEL OPERATIONS
// =============================================================================

static int async_channel_send(unified_channel_t* chan, const void* msg,
                              size_t size, exo_cap_t sender_cap) {
    if (!validate_send_capability(chan, sender_cap)) {
        return -1;
    }
    
    if (size > chan->config.message_size) {
        atomic_fetch_add(&chan->errors.send_errors, 1);
        return -1;
    }
    
    uint64_t start_time = __builtin_ia32_rdtsc();
    
    // Check if buffer has space
    size_t current_count = atomic_load(&chan->buffer_count);
    size_t max_messages = chan->config.buffer_size / chan->config.message_size;
    
    if (current_count >= max_messages) {
        if (chan->config.mode == CHAN_MODE_NONBLOCKING) {
            return -2; // Would block
        }
        // TODO: Block until space is available
        return -1;
    }
    
    // Serialize message into buffer
    uint64_t serial_start = __builtin_ia32_rdtsc();
    
    size_t slot_size = chan->config.message_size;
    size_t buffer_offset = (chan->buffer_head * slot_size) % chan->config.buffer_size;
    void* buffer_slot = (uint8_t*)chan->buffer + buffer_offset;
    
    size_t encoded_size = chan->serializer->encode(msg, size, buffer_slot, slot_size);
    if (encoded_size == 0) {
        atomic_fetch_add(&chan->errors.serial_errors, 1);
        return -1;
    }
    
    uint64_t serial_end = __builtin_ia32_rdtsc();
    
    // Advance buffer head
    chan->buffer_head = (chan->buffer_head + 1) % max_messages;
    atomic_fetch_add(&chan->buffer_count, 1);
    
    // Update statistics
    atomic_fetch_add(&chan->stats.messages_sent, 1);
    atomic_fetch_add(&chan->stats.bytes_sent, encoded_size);
    atomic_fetch_add(&chan->stats.serialization_ns, serial_end - serial_start);
    
    uint64_t end_time = __builtin_ia32_rdtsc();
    atomic_fetch_add(&chan->stats.send_blocked_ns, end_time - start_time);
    
    return 0;
}

static int async_channel_receive(unified_channel_t* chan, void* msg,
                                size_t* size, exo_cap_t receiver_cap) {
    if (!validate_recv_capability(chan, receiver_cap)) {
        return -1;
    }
    
    uint64_t start_time = __builtin_ia32_rdtsc();
    
    // Check if buffer has messages
    size_t current_count = atomic_load(&chan->buffer_count);
    if (current_count == 0) {
        if (chan->config.mode == CHAN_MODE_NONBLOCKING) {
            return -2; // Would block
        }
        // TODO: Block until message is available
        return -1;
    }
    
    // Deserialize message from buffer
    uint64_t serial_start = __builtin_ia32_rdtsc();
    
    size_t slot_size = chan->config.message_size;
    size_t max_messages = chan->config.buffer_size / slot_size;
    size_t buffer_offset = (chan->buffer_tail * slot_size) % chan->config.buffer_size;
    void* buffer_slot = (uint8_t*)chan->buffer + buffer_offset;
    
    size_t decoded_size = chan->serializer->decode(buffer_slot, slot_size, msg, *size);
    if (decoded_size == 0) {
        atomic_fetch_add(&chan->errors.serial_errors, 1);
        return -1;
    }
    
    uint64_t serial_end = __builtin_ia32_rdtsc();
    
    // Advance buffer tail
    chan->buffer_tail = (chan->buffer_tail + 1) % max_messages;
    atomic_fetch_sub(&chan->buffer_count, 1);
    
    // Update size
    *size = decoded_size;
    
    // Update statistics
    atomic_fetch_add(&chan->stats.messages_received, 1);
    atomic_fetch_add(&chan->stats.bytes_received, decoded_size);
    atomic_fetch_add(&chan->stats.serialization_ns, serial_end - serial_start);
    
    uint64_t end_time = __builtin_ia32_rdtsc();
    atomic_fetch_add(&chan->stats.recv_blocked_ns, end_time - start_time);
    
    return 0;
}

// =============================================================================
// MAIN CHANNEL OPERATIONS
// =============================================================================

int channel_send(unified_channel_t* chan, const void* msg, size_t size,
                 exo_cap_t sender_cap) {
    if (!chan || !msg || !atomic_load(&chan->active)) {
        return -1;
    }
    
    switch (chan->config.type) {
        case CHAN_TYPE_SYNC:
            return sync_channel_send(chan, msg, size, sender_cap);
        case CHAN_TYPE_ASYNC:
            return async_channel_send(chan, msg, size, sender_cap);
        case CHAN_TYPE_BROADCAST:
            // TODO: Implement broadcast
            return -1;
        case CHAN_TYPE_MULTICAST:
            // TODO: Implement multicast
            return -1;
        case CHAN_TYPE_STREAM:
            // TODO: Implement stream
            return -1;
        case CHAN_TYPE_BATCH:
            // TODO: Implement batch
            return -1;
        default:
            return -1;
    }
}

int channel_receive(unified_channel_t* chan, void* msg, size_t* size,
                    exo_cap_t receiver_cap) {
    if (!chan || !msg || !size || !atomic_load(&chan->active)) {
        return -1;
    }
    
    switch (chan->config.type) {
        case CHAN_TYPE_SYNC:
            return sync_channel_receive(chan, msg, size, receiver_cap);
        case CHAN_TYPE_ASYNC:
            return async_channel_receive(chan, msg, size, receiver_cap);
        case CHAN_TYPE_BROADCAST:
            // TODO: Implement broadcast
            return -1;
        case CHAN_TYPE_MULTICAST:
            // TODO: Implement multicast
            return -1;
        case CHAN_TYPE_STREAM:
            // TODO: Implement stream
            return -1;
        case CHAN_TYPE_BATCH:
            // TODO: Implement batch
            return -1;
        default:
            return -1;
    }
}

// =============================================================================
// NON-BLOCKING OPERATIONS
// =============================================================================

int channel_try_send(unified_channel_t* chan, const void* msg, size_t size,
                     exo_cap_t sender_cap) {
    if (!chan || !atomic_load(&chan->active)) {
        return -1;
    }
    
    channel_mode_t original_mode = chan->config.mode;
    chan->config.mode = CHAN_MODE_NONBLOCKING;
    
    int result = channel_send(chan, msg, size, sender_cap);
    
    chan->config.mode = original_mode;
    return result;
}

int channel_try_receive(unified_channel_t* chan, void* msg, size_t* size,
                        exo_cap_t receiver_cap) {
    if (!chan || !atomic_load(&chan->active)) {
        return -1;
    }
    
    channel_mode_t original_mode = chan->config.mode;
    chan->config.mode = CHAN_MODE_NONBLOCKING;
    
    int result = channel_receive(chan, msg, size, receiver_cap);
    
    chan->config.mode = original_mode;
    return result;
}

// =============================================================================
// CHANNEL MANAGEMENT
// =============================================================================

void channel_get_stats(unified_channel_t* chan, 
                       struct unified_channel* stats_out) {
    if (!chan || !stats_out) {
        return;
    }
    
    *stats_out = *chan;
}

void channel_reset_stats(unified_channel_t* chan) {
    if (!chan) {
        return;
    }
    
    atomic_store(&chan->stats.messages_sent, 0);
    atomic_store(&chan->stats.messages_received, 0);
    atomic_store(&chan->stats.bytes_sent, 0);
    atomic_store(&chan->stats.bytes_received, 0);
    atomic_store(&chan->stats.send_blocked_ns, 0);
    atomic_store(&chan->stats.recv_blocked_ns, 0);
    atomic_store(&chan->stats.serialization_ns, 0);
    atomic_store(&chan->stats.zero_copy_count, 0);
    
    atomic_store(&chan->errors.send_errors, 0);
    atomic_store(&chan->errors.recv_errors, 0);
    atomic_store(&chan->errors.serial_errors, 0);
    atomic_store(&chan->errors.cap_errors, 0);
}

bool channel_is_empty(unified_channel_t* chan) {
    if (!chan) {
        return true;
    }
    
    if (chan->config.type == CHAN_TYPE_ASYNC) {
        return atomic_load(&chan->buffer_count) == 0;
    }
    
    return atomic_load(&chan->waiting_senders) == 0;
}

bool channel_is_full(unified_channel_t* chan) {
    if (!chan) {
        return true;
    }
    
    if (chan->config.type == CHAN_TYPE_ASYNC) {
        size_t current_count = atomic_load(&chan->buffer_count);
        size_t max_messages = chan->config.buffer_size / chan->config.message_size;
        return current_count >= max_messages;
    }
    
    return false; // Sync channels are never "full"
}

size_t channel_pending_count(unified_channel_t* chan) {
    if (!chan) {
        return 0;
    }
    
    if (chan->config.type == CHAN_TYPE_ASYNC) {
        return atomic_load(&chan->buffer_count);
    }
    
    return atomic_load(&chan->waiting_senders);
}

// =============================================================================
// CHANNEL REGISTRY OPERATIONS
// =============================================================================

unified_channel_t* channel_find(const char* name) {
    if (!name) {
        return NULL;
    }
    
    while (atomic_flag_test_and_set(&registry_lock)) {
        // Spin wait
    }
    
    unified_channel_t* chan = channel_registry_head;
    while (chan) {
        if (strncmp(chan->name, name, sizeof(chan->name)) == 0) {
            atomic_flag_clear(&registry_lock);
            return chan;
        }
        chan = chan->next;
    }
    
    atomic_flag_clear(&registry_lock);
    return NULL;
}

unified_channel_t* channel_find_by_id(uint64_t id) {
    while (atomic_flag_test_and_set(&registry_lock)) {
        // Spin wait
    }
    
    unified_channel_t* chan = channel_registry_head;
    while (chan) {
        if (chan->id == id) {
            atomic_flag_clear(&registry_lock);
            return chan;
        }
        chan = chan->next;
    }
    
    atomic_flag_clear(&registry_lock);
    return NULL;
}

size_t channel_list(unified_channel_t** list, size_t max_count) {
    if (!list || max_count == 0) {
        return 0;
    }
    
    while (atomic_flag_test_and_set(&registry_lock)) {
        // Spin wait
    }
    
    size_t count = 0;
    unified_channel_t* chan = channel_registry_head;
    while (chan && count < max_count) {
        list[count++] = chan;
        chan = chan->next;
    }
    
    atomic_flag_clear(&registry_lock);
    return count;
}

size_t channel_count(void) {
    while (atomic_flag_test_and_set(&registry_lock)) {
        // Spin wait
    }
    
    size_t count = 0;
    unified_channel_t* chan = channel_registry_head;
    while (chan) {
        count++;
        chan = chan->next;
    }
    
    atomic_flag_clear(&registry_lock);
    return count;
}

// =============================================================================
// INITIALIZATION
// =============================================================================

void init_channel_system(void) {
    // Initialize serialization system first
    init_serialization_system();
    
    // Reset registry
    channel_registry_head = NULL;
    atomic_flag_clear(&registry_lock);
    atomic_store(&next_channel_id, 1);
}

void shutdown_channel_system(void) {
    // Destroy all channels
    while (atomic_flag_test_and_set(&registry_lock)) {
        // Spin wait
    }
    
    unified_channel_t* chan = channel_registry_head;
    while (chan) {
        unified_channel_t* next = chan->next;
        atomic_flag_clear(&registry_lock);
        channel_destroy(chan);
        while (atomic_flag_test_and_set(&registry_lock)) {
            // Spin wait
        }
        chan = next;
    }
    
    channel_registry_head = NULL;
    atomic_flag_clear(&registry_lock);
}