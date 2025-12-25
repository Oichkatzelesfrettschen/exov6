/**
 * @file unified_channel.h
 * @brief Unified channel abstraction synthesizing all IPC mechanisms
 * 
 * This harmonizes:
 * - Typed channels with compile-time safety
 * - Cap'n Proto serialization layers
 * - Zero-copy optimizations
 * - Capability-based security
 * - Performance monitoring
 */

#ifndef UNIFIED_CHANNEL_H
#define UNIFIED_CHANNEL_H

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdatomic.h>
#include "../exo.h"
#include "serialization.h"

// =============================================================================
// CHANNEL TYPES AND CONFIGURATIONS
// =============================================================================

typedef enum {
    CHAN_TYPE_SYNC,      // Synchronous rendezvous
    CHAN_TYPE_ASYNC,     // Asynchronous buffered
    CHAN_TYPE_BROADCAST, // One-to-many broadcast
    CHAN_TYPE_MULTICAST, // Selective multicast
    CHAN_TYPE_STREAM,    // Continuous stream
    CHAN_TYPE_BATCH,     // Batch processing
} channel_type_t;

typedef enum {
    CHAN_MODE_BLOCKING,     // Block on send/receive
    CHAN_MODE_NONBLOCKING,  // Return immediately
    CHAN_MODE_TIMEOUT,      // Wait with timeout
    CHAN_MODE_POLL,         // Poll multiple channels
} channel_mode_t;

typedef struct {
    channel_type_t type;
    channel_mode_t mode;
    size_t buffer_size;      // For async channels
    size_t message_size;     // Max message size
    uint32_t max_receivers;  // For broadcast/multicast
    uint32_t timeout_ms;     // For timeout mode
    serial_type_t serializer; // Serialization method
    bool zero_copy;          // Enable zero-copy if possible
    bool ordered;            // Guarantee message ordering
    bool reliable;           // Guarantee delivery
} channel_config_t;

// =============================================================================
// UNIFIED CHANNEL STRUCTURE
// =============================================================================

typedef struct unified_channel {
    // Identity
    uint64_t id;
    char name[64];
    
    // Configuration
    channel_config_t config;
    
    // Capability management
    exo_cap_t owner_cap;
    exo_cap_t send_cap;
    exo_cap_t recv_cap;
    
    // Serialization
    serializer_t* serializer;
    
    // Buffer management (for async channels)
    void* buffer;
    size_t buffer_head;
    size_t buffer_tail;
    atomic_size_t buffer_count;
    
    // Synchronization
    atomic_flag send_lock;
    atomic_flag recv_lock;
    atomic_int waiting_senders;
    atomic_int waiting_receivers;
    
    // Performance metrics
    struct {
        atomic_uint_fast64_t messages_sent;
        atomic_uint_fast64_t messages_received;
        atomic_uint_fast64_t bytes_sent;
        atomic_uint_fast64_t bytes_received;
        atomic_uint_fast64_t send_blocked_ns;
        atomic_uint_fast64_t recv_blocked_ns;
        atomic_uint_fast64_t serialization_ns;
        atomic_uint_fast64_t zero_copy_count;
    } stats;
    
    // Error tracking
    struct {
        atomic_uint_fast32_t send_errors;
        atomic_uint_fast32_t recv_errors;
        atomic_uint_fast32_t serial_errors;
        atomic_uint_fast32_t cap_errors;
    } errors;
    
    // Channel state
    atomic_bool active;
    atomic_bool closing;
    
    // Linked list for channel registry
    struct unified_channel* next;
    struct unified_channel* prev;
} unified_channel_t;

// =============================================================================
// CHANNEL OPERATIONS
// =============================================================================

/**
 * Create a new unified channel with given configuration
 */
unified_channel_t* channel_create(const char* name, 
                                  const channel_config_t* config,
                                  exo_cap_t owner_cap);

/**
 * Destroy a channel and free resources
 */
int channel_destroy(unified_channel_t* chan);

/**
 * Send a message through the channel
 */
int channel_send(unified_channel_t* chan, const void* msg, size_t size,
                 exo_cap_t sender_cap);

/**
 * Receive a message from the channel
 */
int channel_receive(unified_channel_t* chan, void* msg, size_t* size,
                    exo_cap_t receiver_cap);

/**
 * Try to send without blocking
 */
int channel_try_send(unified_channel_t* chan, const void* msg, size_t size,
                     exo_cap_t sender_cap);

/**
 * Try to receive without blocking
 */
int channel_try_receive(unified_channel_t* chan, void* msg, size_t* size,
                        exo_cap_t receiver_cap);

/**
 * Send with timeout
 */
int channel_send_timeout(unified_channel_t* chan, const void* msg, size_t size,
                         exo_cap_t sender_cap, uint32_t timeout_ms);

/**
 * Receive with timeout
 */
int channel_receive_timeout(unified_channel_t* chan, void* msg, size_t* size,
                            exo_cap_t receiver_cap, uint32_t timeout_ms);

// =============================================================================
// BATCH OPERATIONS
// =============================================================================

typedef struct {
    const void* msg;
    size_t size;
    int status;
} channel_batch_item_t;

/**
 * Send multiple messages in a batch
 */
int channel_send_batch(unified_channel_t* chan, 
                       channel_batch_item_t* items, size_t count,
                       exo_cap_t sender_cap);

/**
 * Receive multiple messages in a batch
 */
int channel_receive_batch(unified_channel_t* chan,
                          channel_batch_item_t* items, size_t count,
                          exo_cap_t receiver_cap);

// =============================================================================
// CHANNEL SELECTION (like Go's select)
// =============================================================================

typedef struct {
    unified_channel_t* chan;
    void* msg;
    size_t size;
    bool is_send;
    bool ready;
} channel_select_case_t;

/**
 * Select from multiple channel operations
 */
int channel_select(channel_select_case_t* cases, size_t count,
                   int* selected_index, uint32_t timeout_ms);

// =============================================================================
// ZERO-COPY OPERATIONS
// =============================================================================

/**
 * Get a zero-copy buffer for sending
 */
void* channel_get_send_buffer(unified_channel_t* chan, size_t size);

/**
 * Commit a zero-copy send
 */
int channel_commit_send(unified_channel_t* chan, void* buffer, size_t size,
                        exo_cap_t sender_cap);

/**
 * Get a zero-copy view of received message
 */
const void* channel_peek_message(unified_channel_t* chan, size_t* size);

/**
 * Consume a peeked message
 */
int channel_consume_message(unified_channel_t* chan);

// =============================================================================
// BROADCAST/MULTICAST
// =============================================================================

/**
 * Register as a receiver for broadcast/multicast channel
 */
int channel_subscribe(unified_channel_t* chan, exo_cap_t subscriber_cap);

/**
 * Unregister from broadcast/multicast channel
 */
int channel_unsubscribe(unified_channel_t* chan, exo_cap_t subscriber_cap);

/**
 * Send to all subscribers
 */
int channel_broadcast(unified_channel_t* chan, const void* msg, size_t size,
                      exo_cap_t sender_cap);

/**
 * Send to specific subscribers
 */
int channel_multicast(unified_channel_t* chan, const void* msg, size_t size,
                      exo_cap_t sender_cap, exo_cap_t* targets, size_t target_count);

// =============================================================================
// CHANNEL MANAGEMENT
// =============================================================================

/**
 * Get channel statistics
 */
void channel_get_stats(unified_channel_t* chan, 
                       struct unified_channel* stats_out);

/**
 * Reset channel statistics
 */
void channel_reset_stats(unified_channel_t* chan);

/**
 * Check if channel is empty
 */
bool channel_is_empty(unified_channel_t* chan);

/**
 * Check if channel is full
 */
bool channel_is_full(unified_channel_t* chan);

/**
 * Get number of pending messages
 */
size_t channel_pending_count(unified_channel_t* chan);

/**
 * Flush all pending messages
 */
int channel_flush(unified_channel_t* chan);

// =============================================================================
// TYPED CHANNEL MACROS
// =============================================================================

/**
 * Define a typed channel for compile-time safety
 */
#define DEFINE_TYPED_CHANNEL(name, type)                                    \
    typedef struct {                                                        \
        unified_channel_t* chan;                                           \
        _Static_assert(sizeof(type) > 0, "Type must be complete");        \
    } name##_channel_t;                                                    \
                                                                            \
    static inline name##_channel_t* name##_channel_create(                 \
        const char* chan_name, const channel_config_t* config,             \
        exo_cap_t owner_cap) {                                            \
        name##_channel_t* typed = malloc(sizeof(name##_channel_t));       \
        if (typed) {                                                       \
            channel_config_t cfg = *config;                               \
            cfg.message_size = sizeof(type);                              \
            typed->chan = channel_create(chan_name, &cfg, owner_cap);     \
            if (!typed->chan) {                                           \
                free(typed);                                              \
                return NULL;                                              \
            }                                                              \
        }                                                                  \
        return typed;                                                      \
    }                                                                      \
                                                                           \
    static inline int name##_channel_send(                                \
        name##_channel_t* chan, const type* msg, exo_cap_t cap) {        \
        return channel_send(chan->chan, msg, sizeof(type), cap);         \
    }                                                                      \
                                                                           \
    static inline int name##_channel_receive(                             \
        name##_channel_t* chan, type* msg, exo_cap_t cap) {              \
        size_t size = sizeof(type);                                       \
        return channel_receive(chan->chan, msg, &size, cap);             \
    }                                                                      \
                                                                           \
    static inline void name##_channel_destroy(name##_channel_t* chan) {   \
        if (chan) {                                                        \
            channel_destroy(chan->chan);                                  \
            free(chan);                                                   \
        }                                                                  \
    }

// =============================================================================
// CHANNEL REGISTRY
// =============================================================================

/**
 * Find channel by name
 */
unified_channel_t* channel_find(const char* name);

/**
 * Find channel by ID
 */
unified_channel_t* channel_find_by_id(uint64_t id);

/**
 * List all channels
 */
size_t channel_list(unified_channel_t** list, size_t max_count);

/**
 * Get total number of channels
 */
size_t channel_count(void);

// =============================================================================
// INITIALIZATION
// =============================================================================

/**
 * Initialize the channel subsystem
 */
void init_channel_system(void);

/**
 * Shutdown the channel subsystem
 */
void shutdown_channel_system(void);

#endif // UNIFIED_CHANNEL_H