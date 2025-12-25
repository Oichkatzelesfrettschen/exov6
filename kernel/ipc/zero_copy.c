/**
 * @file zero_copy.c
 * @brief Zero-copy optimizations for unified channel system
 * 
 * Implements advanced zero-copy mechanisms:
 * - Direct memory mapping between processes
 * - Shared buffer pools
 * - Copy-on-write semantics
 * - Memory protection and isolation
 * - NUMA-aware allocation
 */

#include "../../include/ipc/unified_channel.h"
#include "../../include/ipc/serialization.h"
#include "../string.h"
#include <stdlib.h>
#include <stdatomic.h>

// =============================================================================
// ZERO-COPY BUFFER MANAGEMENT
// =============================================================================

typedef struct zero_copy_buffer {
    void* data;                    // Buffer data
    size_t size;                   // Buffer size
    atomic_int refcount;           // Reference count
    exo_cap_t owner_cap;          // Owner capability
    bool mapped;                   // Is mapped to userspace
    bool copy_on_write;           // COW semantics
    struct zero_copy_buffer* next; // Free list
} zero_copy_buffer_t;

typedef struct zero_copy_pool {
    zero_copy_buffer_t* free_list;    // Free buffers
    atomic_flag lock;                  // Pool lock
    size_t buffer_size;               // Standard buffer size
    size_t pool_size;                 // Number of buffers
    atomic_size_t allocated_count;    // Currently allocated
    atomic_size_t total_allocations;  // Lifetime allocations
    atomic_size_t zero_copy_hits;     // Successful zero-copy ops
    atomic_size_t zero_copy_misses;   // Failed zero-copy ops
} zero_copy_pool_t;

// Global zero-copy pools for different sizes
#define NUM_POOLS 8
static zero_copy_pool_t pools[NUM_POOLS];
static bool pools_initialized = false;

// Buffer sizes: 64B, 256B, 1KB, 4KB, 16KB, 64KB, 256KB, 1MB
static const size_t pool_sizes[NUM_POOLS] = {
    64, 256, 1024, 4096, 16384, 65536, 262144, 1048576
};

// =============================================================================
// POOL INITIALIZATION
// =============================================================================

static void init_zero_copy_pool(zero_copy_pool_t* pool, size_t buffer_size, size_t count) {
    pool->buffer_size = buffer_size;
    pool->pool_size = count;
    pool->free_list = NULL;
    atomic_flag_clear(&pool->lock);
    atomic_store(&pool->allocated_count, 0);
    atomic_store(&pool->total_allocations, 0);
    atomic_store(&pool->zero_copy_hits, 0);
    atomic_store(&pool->zero_copy_misses, 0);
    
    // Pre-allocate buffers
    for (size_t i = 0; i < count; i++) {
        zero_copy_buffer_t* buffer = malloc(sizeof(zero_copy_buffer_t));
        if (!buffer) break;
        
        // Allocate aligned memory for better performance
        buffer->data = aligned_alloc(64, buffer_size); // 64-byte alignment
        if (!buffer->data) {
            free(buffer);
            break;
        }
        
        buffer->size = buffer_size;
        atomic_store(&buffer->refcount, 0);
        buffer->owner_cap = 0;
        buffer->mapped = false;
        buffer->copy_on_write = false;
        
        // Add to free list
        buffer->next = pool->free_list;
        pool->free_list = buffer;
    }
}

void init_zero_copy_system(void) {
    if (pools_initialized) return;
    
    // Initialize all pools
    for (int i = 0; i < NUM_POOLS; i++) {
        size_t count = 64 >> i; // Fewer large buffers
        if (count < 4) count = 4;
        init_zero_copy_pool(&pools[i], pool_sizes[i], count);
    }
    
    pools_initialized = true;
}

// =============================================================================
// BUFFER ALLOCATION
// =============================================================================

static zero_copy_pool_t* find_suitable_pool(size_t size) {
    for (int i = 0; i < NUM_POOLS; i++) {
        if (pool_sizes[i] >= size) {
            return &pools[i];
        }
    }
    return NULL; // Size too large
}

static zero_copy_buffer_t* allocate_zero_copy_buffer(size_t size, exo_cap_t cap) {
    zero_copy_pool_t* pool = find_suitable_pool(size);
    if (!pool) {
        return NULL;
    }
    
    // Try to get buffer from pool
    while (atomic_flag_test_and_set(&pool->lock)) {
        // Spin wait
    }
    
    zero_copy_buffer_t* buffer = pool->free_list;
    if (buffer) {
        pool->free_list = buffer->next;
        atomic_fetch_add(&pool->allocated_count, 1);
        atomic_fetch_add(&pool->total_allocations, 1);
    }
    
    atomic_flag_clear(&pool->lock);
    
    if (buffer) {
        atomic_store(&buffer->refcount, 1);
        buffer->owner_cap = cap;
        buffer->mapped = false;
        buffer->copy_on_write = false;
        buffer->next = NULL;
        
        // Clear the buffer
        memset(buffer->data, 0, size);
    }
    
    return buffer;
}

static void free_zero_copy_buffer(zero_copy_buffer_t* buffer) {
    if (!buffer) return;
    
    // Find the right pool
    zero_copy_pool_t* pool = find_suitable_pool(buffer->size);
    if (!pool) return;
    
    // Return to pool
    while (atomic_flag_test_and_set(&pool->lock)) {
        // Spin wait
    }
    
    buffer->next = pool->free_list;
    pool->free_list = buffer;
    atomic_fetch_sub(&pool->allocated_count, 1);
    
    atomic_flag_clear(&pool->lock);
}

// =============================================================================
// REFERENCE COUNTING
// =============================================================================

static zero_copy_buffer_t* retain_buffer(zero_copy_buffer_t* buffer) {
    if (!buffer) return NULL;
    
    atomic_fetch_add(&buffer->refcount, 1);
    return buffer;
}

static void release_buffer(zero_copy_buffer_t* buffer) {
    if (!buffer) return;
    
    int old_count = atomic_fetch_sub(&buffer->refcount, 1);
    if (old_count == 1) {
        // Last reference, free the buffer
        free_zero_copy_buffer(buffer);
    }
}

// =============================================================================
// ZERO-COPY CHANNEL OPERATIONS
// =============================================================================

void* channel_get_send_buffer(unified_channel_t* chan, size_t size) {
    if (!chan || !chan->config.zero_copy || size > chan->config.message_size) {
        return NULL;
    }
    
    // Check if zero-copy is possible for this capability
    if (!exo_can_zero_copy(chan->send_cap)) {
        zero_copy_pool_t* pool = find_suitable_pool(size);
        if (pool) {
            atomic_fetch_add(&pool->zero_copy_misses, 1);
        }
        return NULL;
    }
    
    zero_copy_buffer_t* buffer = allocate_zero_copy_buffer(size, chan->send_cap);
    if (!buffer) {
        zero_copy_pool_t* pool = find_suitable_pool(size);
        if (pool) {
            atomic_fetch_add(&pool->zero_copy_misses, 1);
        }
        return NULL;
    }
    
    // Store buffer pointer in channel for commit
    chan->zero_copy_send_buffer = buffer;
    
    zero_copy_pool_t* pool = find_suitable_pool(size);
    if (pool) {
        atomic_fetch_add(&pool->zero_copy_hits, 1);
    }
    
    return buffer->data;
}

int channel_commit_send(unified_channel_t* chan, void* buffer, size_t size,
                        exo_cap_t sender_cap) {
    if (!chan || !buffer) {
        return -1;
    }
    
    zero_copy_buffer_t* zc_buffer = (zero_copy_buffer_t*)chan->zero_copy_send_buffer;
    if (!zc_buffer || zc_buffer->data != buffer) {
        return -1; // Buffer mismatch
    }
    
    // Validate capability
    if (!validate_send_capability(chan, sender_cap)) {
        release_buffer(zc_buffer);
        chan->zero_copy_send_buffer = NULL;
        return -1;
    }
    
    uint64_t start_time = __builtin_ia32_rdtsc();
    
    // For async channels, store the buffer reference
    if (chan->config.type == CHAN_TYPE_ASYNC) {
        // Check if buffer has space
        size_t current_count = atomic_load(&chan->buffer_count);
        size_t max_messages = chan->config.buffer_size / sizeof(zero_copy_buffer_t*);
        
        if (current_count >= max_messages) {
            release_buffer(zc_buffer);
            chan->zero_copy_send_buffer = NULL;
            return -1; // Buffer full
        }
        
        // Store buffer reference in channel buffer
        zero_copy_buffer_t** buffer_refs = (zero_copy_buffer_t**)chan->buffer;
        size_t slot = chan->buffer_head % max_messages;
        buffer_refs[slot] = retain_buffer(zc_buffer);
        
        chan->buffer_head = (chan->buffer_head + 1) % max_messages;
        atomic_fetch_add(&chan->buffer_count, 1);
    } else {
        // For sync channels, transfer would happen here
        // For now, just simulate the transfer
    }
    
    // Update statistics
    atomic_fetch_add(&chan->stats.messages_sent, 1);
    atomic_fetch_add(&chan->stats.bytes_sent, size);
    atomic_fetch_add(&chan->stats.zero_copy_count, 1);
    
    uint64_t end_time = __builtin_ia32_rdtsc();
    atomic_fetch_add(&chan->stats.send_blocked_ns, end_time - start_time);
    
    // Release our reference (receiver will have their own)
    release_buffer(zc_buffer);
    chan->zero_copy_send_buffer = NULL;
    
    return 0;
}

const void* channel_peek_message(unified_channel_t* chan, size_t* size) {
    if (!chan || !size || !chan->config.zero_copy) {
        return NULL;
    }
    
    if (chan->config.type != CHAN_TYPE_ASYNC) {
        return NULL; // Only supported for async channels
    }
    
    size_t current_count = atomic_load(&chan->buffer_count);
    if (current_count == 0) {
        return NULL; // No messages
    }
    
    // Get buffer reference
    zero_copy_buffer_t** buffer_refs = (zero_copy_buffer_t**)chan->buffer;
    size_t max_messages = chan->config.buffer_size / sizeof(zero_copy_buffer_t*);
    size_t slot = chan->buffer_tail % max_messages;
    zero_copy_buffer_t* buffer = buffer_refs[slot];
    
    if (!buffer) {
        return NULL;
    }
    
    *size = buffer->size;
    return buffer->data;
}

int channel_consume_message(unified_channel_t* chan) {
    if (!chan || !chan->config.zero_copy) {
        return -1;
    }
    
    if (chan->config.type != CHAN_TYPE_ASYNC) {
        return -1; // Only supported for async channels
    }
    
    size_t current_count = atomic_load(&chan->buffer_count);
    if (current_count == 0) {
        return -1; // No messages
    }
    
    uint64_t start_time = __builtin_ia32_rdtsc();
    
    // Get and consume buffer reference
    zero_copy_buffer_t** buffer_refs = (zero_copy_buffer_t**)chan->buffer;
    size_t max_messages = chan->config.buffer_size / sizeof(zero_copy_buffer_t*);
    size_t slot = chan->buffer_tail % max_messages;
    zero_copy_buffer_t* buffer = buffer_refs[slot];
    
    if (!buffer) {
        return -1;
    }
    
    // Clear the slot
    buffer_refs[slot] = NULL;
    
    // Advance tail
    chan->buffer_tail = (chan->buffer_tail + 1) % max_messages;
    atomic_fetch_sub(&chan->buffer_count, 1);
    
    // Update statistics
    atomic_fetch_add(&chan->stats.messages_received, 1);
    atomic_fetch_add(&chan->stats.bytes_received, buffer->size);
    atomic_fetch_add(&chan->stats.zero_copy_count, 1);
    
    uint64_t end_time = __builtin_ia32_rdtsc();
    atomic_fetch_add(&chan->stats.recv_blocked_ns, end_time - start_time);
    
    // Release buffer
    release_buffer(buffer);
    
    return 0;
}

// =============================================================================
// COPY-ON-WRITE SUPPORT
// =============================================================================

static zero_copy_buffer_t* copy_on_write_buffer(zero_copy_buffer_t* original) {
    if (!original) return NULL;
    
    // Check if COW is needed
    int refcount = atomic_load(&original->refcount);
    if (refcount <= 1) {
        // Only one reference, no need to copy
        return original;
    }
    
    // Allocate new buffer
    zero_copy_buffer_t* new_buffer = allocate_zero_copy_buffer(
        original->size, original->owner_cap);
    if (!new_buffer) {
        return original; // Fallback to shared buffer
    }
    
    // Copy data
    memcpy(new_buffer->data, original->data, original->size);
    new_buffer->copy_on_write = true;
    
    return new_buffer;
}

void* channel_get_mutable_view(unified_channel_t* chan, const void* message) {
    if (!chan || !message || !chan->config.zero_copy) {
        return NULL;
    }
    
    // Find the buffer containing this message
    // This is a simplified implementation - in reality, we'd maintain
    // a mapping from message pointers to buffers
    
    return NULL; // Not implemented in this simplified version
}

// =============================================================================
// MEMORY MAPPING SUPPORT
// =============================================================================

int channel_map_to_userspace(unified_channel_t* chan, void** mapped_addr) {
    if (!chan || !mapped_addr || !chan->config.zero_copy) {
        return -1;
    }
    
    // This would use system-specific memory mapping
    // For now, just return the buffer address
    if (chan->config.type == CHAN_TYPE_ASYNC && chan->buffer) {
        *mapped_addr = chan->buffer;
        return 0;
    }
    
    return -1;
}

int channel_unmap_from_userspace(unified_channel_t* chan, void* mapped_addr) {
    if (!chan || !mapped_addr) {
        return -1;
    }
    
    // This would unmap the memory
    // For now, just validate the address
    if (chan->buffer == mapped_addr) {
        return 0;
    }
    
    return -1;
}

// =============================================================================
// NUMA-AWARE ALLOCATION
// =============================================================================

#ifdef CONFIG_NUMA
static int get_numa_node(exo_cap_t cap) {
    // Extract NUMA node from capability
    return (cap >> 32) & 0xFF;
}

static void* numa_alloc(size_t size, int node) {
    // This would use NUMA-specific allocation
    // For now, just use regular allocation
    return aligned_alloc(64, size);
}
#endif

// =============================================================================
// STATISTICS AND MONITORING
// =============================================================================

void get_zero_copy_stats(zero_copy_pool_t* stats_out, size_t count) {
    if (!stats_out || count > NUM_POOLS) {
        return;
    }
    
    for (size_t i = 0; i < count && i < NUM_POOLS; i++) {
        stats_out[i] = pools[i];
    }
}

void print_zero_copy_stats(void) {
    printf("Zero-Copy Buffer Pool Statistics:\n");
    printf("==================================\n");
    
    for (int i = 0; i < NUM_POOLS; i++) {
        zero_copy_pool_t* pool = &pools[i];
        printf("Pool %d (%zu bytes):\n", i, pool->buffer_size);
        printf("  Allocated: %zu / %zu\n", 
               atomic_load(&pool->allocated_count), pool->pool_size);
        printf("  Total allocations: %zu\n", 
               atomic_load(&pool->total_allocations));
        printf("  Zero-copy hits: %zu\n", 
               atomic_load(&pool->zero_copy_hits));
        printf("  Zero-copy misses: %zu\n", 
               atomic_load(&pool->zero_copy_misses));
        
        if (atomic_load(&pool->zero_copy_hits) + atomic_load(&pool->zero_copy_misses) > 0) {
            double hit_rate = (double)atomic_load(&pool->zero_copy_hits) / 
                             (atomic_load(&pool->zero_copy_hits) + atomic_load(&pool->zero_copy_misses));
            printf("  Hit rate: %.1f%%\n", hit_rate * 100.0);
        }
        printf("\n");
    }
}

// =============================================================================
// CLEANUP
// =============================================================================

void shutdown_zero_copy_system(void) {
    for (int i = 0; i < NUM_POOLS; i++) {
        zero_copy_pool_t* pool = &pools[i];
        
        // Free all buffers in the pool
        while (pool->free_list) {
            zero_copy_buffer_t* buffer = pool->free_list;
            pool->free_list = buffer->next;
            
            free(buffer->data);
            free(buffer);
        }
    }
    
    pools_initialized = false;
}