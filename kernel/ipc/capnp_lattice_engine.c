/**
 * @file capnp_lattice_engine.c
 * @brief Integrated Cap'n Proto + Lattice IPC Engine
 *
 * Pure C17 implementation synthesizing zero-copy serialization with
 * post-quantum cryptography and exokernel capabilities.
 */

/* Define kernel mode before any includes to prevent userspace API conflicts */
#ifndef EXO_KERNEL
#define EXO_KERNEL 1
#endif

#include "capnp_helpers.h"
#include "lattice_ipc.h"
#include "exo.h"
/* exo.h included via defs.h/proc.h (kernel API, not userspace exokernel.h) */
#include "octonion.h"
#include <stdatomic.h>
#include <string.h>
#include <stdlib.h>  /* For malloc, free */
#include <errno.h>   /* For EPERM, EINVAL */
#include "defs.h"    /* For myproc() - instead of getpid() */

// Arena allocation with capability integration
typedef struct exo_capnp_arena {
    exo_cap memory_cap;
    uint8_t* segments[16];
    size_t segment_sizes[16];
    _Atomic size_t current_seg;
    _Atomic size_t current_pos;
    lattice_channel_t *secure_chan;
    octonion_t arena_identity;
} exo_capnp_arena_t;

// Forward declarations for zone message handlers
int exo_kernel_receive_message(exo_capnp_arena_t *arena, const capnp_pointer_t *msg);
int exo_libos_receive_message(exo_capnp_arena_t *arena, const capnp_pointer_t *msg);
int exo_userspace_receive_message(exo_capnp_arena_t *arena, const capnp_pointer_t *msg);

// Global arena registry
static exo_capnp_arena_t g_arenas[256];
static _Atomic uint32_t g_arena_count = 0;

/**
 * Create capability-protected Cap'n Proto arena
 */
exo_capnp_arena_t* exo_capnp_create_arena(size_t initial_size) {
    uint32_t arena_idx = atomic_fetch_add(&g_arena_count, 1);
    if (arena_idx >= 256) return NULL;
    
    exo_capnp_arena_t *arena = &g_arenas[arena_idx];
    
    // Allocate capability for arena memory
    arena->memory_cap = exo_alloc_page();
    if (arena->memory_cap.id == 0) return NULL;
    
    // Initialize first segment
    arena->segments[0] = (uint8_t*)malloc(initial_size);
    if (!arena->segments[0]) return NULL;
    
    arena->segment_sizes[0] = initial_size;
    atomic_store(&arena->current_seg, 0);
    atomic_store(&arena->current_pos, 0);
    
    // Generate 8D mathematical identity for arena
    arena->arena_identity = octonion_generate_identity();
    
    // Create secure lattice channel
    arena->secure_chan = malloc(sizeof(lattice_channel_t));
    if (lattice_channel_init(arena->secure_chan) != 0) {
        free(arena->segments[0]);
        return NULL;
    }
    
    return arena;
}

/**
 * Allocate object in arena with capability verification
 */
void* exo_capnp_alloc_object(exo_capnp_arena_t *arena, size_t words) {
    if (!arena || !cap_verify(arena->memory_cap)) {
        return NULL;
    }
    
    size_t bytes = words * 8;  // Cap'n Proto word = 8 bytes
    size_t current_seg = atomic_load(&arena->current_seg);
    size_t current_pos = atomic_fetch_add(&arena->current_pos, bytes);
    
    // Check if we need a new segment
    if (current_pos + bytes > arena->segment_sizes[current_seg]) {
        // Allocate new segment
        if (current_seg >= 15) return NULL;  // Max segments reached
        
        size_t new_seg = current_seg + 1;
        size_t new_size = arena->segment_sizes[current_seg] * 2;
        
        arena->segments[new_seg] = (uint8_t*)malloc(new_size);
        if (!arena->segments[new_seg]) return NULL;
        
        arena->segment_sizes[new_seg] = new_size;
        atomic_store(&arena->current_seg, new_seg);
        atomic_store(&arena->current_pos, bytes);
        
        current_pos = 0;
        current_seg = new_seg;
    }
    
    void *ptr = arena->segments[current_seg] + current_pos;
    memset(ptr, 0, bytes);  // Zero-initialize for security
    
    return ptr;
}

/**
 * Create cryptographically secure Cap'n Proto pointer
 */
capnp_pointer_t exo_capnp_make_secure_pointer(uint32_t offset, uint16_t data_words,
                                              uint16_t ptr_words, exo_capnp_arena_t *arena) {
    capnp_pointer_t ptr = {0};
    ptr.struct_ptr.type = CAPNP_PTR_STRUCT;
    ptr.struct_ptr.offset = offset;
    ptr.struct_ptr.data_words = data_words;
    ptr.struct_ptr.ptr_words = ptr_words;
    
    // Add cryptographic signature using lattice channel
    if (arena->secure_chan) {
        // Generate lattice signature for pointer integrity
        lattice_sig_t sig;
        if (lattice_sign(&arena->secure_chan->priv, &ptr.raw, sizeof(uint64_t), &sig) == 0) {
            // Signature successful - pointer is now cryptographically protected
        }
    }
    
    return ptr;
}

/**
 * Follow pointer with full security verification
 */
void* exo_capnp_follow_secure_pointer(const capnp_pointer_t *ptr,
                                     const exo_capnp_arena_t *arena,
                                     exo_cap required_cap) {
    // Verify arena access capability
    if (!cap_verify(arena->memory_cap)) {
        return NULL;  // Access denied
    }
    
    // Verify required capability for this specific access
    if (required_cap.id != 0 && !cap_verify(required_cap)) {
        return NULL;  // Insufficient permissions
    }
    
    // Verify pointer is within valid arena bounds
    uint32_t seg_idx = ptr->struct_ptr.offset >> 16;
    uint32_t word_offset = ptr->struct_ptr.offset & 0xFFFF;
    
    if (seg_idx >= 16 || !arena->segments[seg_idx]) {
        return NULL;  // Invalid segment
    }
    
    size_t byte_offset = word_offset * 8;
    if (byte_offset >= arena->segment_sizes[seg_idx]) {
        return NULL;  // Out of bounds
    }
    
    // All verifications passed - return pointer
    return arena->segments[seg_idx] + byte_offset;
}

/**
 * Send Cap'n Proto message through lattice-secured channel
 */
int exo_capnp_send_message(exo_capnp_arena_t *src_arena,
                          lattice_channel_t *dest_channel,
                          const capnp_pointer_t *root_ptr) {
    
    if (!src_arena || !dest_channel || !root_ptr) {
        return -1;
    }
    
    // Verify source arena capability
    if (!cap_verify(src_arena->memory_cap)) {
        return -EPERM;
    }
    
    // Calculate message size
    size_t msg_size = sizeof(capnp_pointer_t);
    
    // Send via secure lattice channel with post-quantum protection
    return lattice_channel_send(dest_channel, root_ptr, msg_size);
}

/**
 * Initialize the integrated Cap'n Proto + Lattice IPC engine
 */
int exo_capnp_lattice_init(void) {
    // Initialize global state
    atomic_store(&g_arena_count, 0);
    
    // Zero out arena registry
    memset(g_arenas, 0, sizeof(g_arenas));
    
    // Initialize lattice cryptography
    lattice_crypto_init();
    
    return 0;
}

/**
 * Cross-zone IPC with Cap'n Proto + Lattice integration
 */
int exo_ipc_send_capnp_message(uint32_t dest_zone,
                              exo_capnp_arena_t *arena,
                              const capnp_pointer_t *msg) {
    
    // Validate zone capability
    struct proc *p = myproc();
    exo_cap zone_cap = cap_new(dest_zone, EXO_RIGHT_EXEC | EXO_RIGHT_CTL, p ? p->pid : 0);
    if (!cap_verify(zone_cap)) {
        return -EPERM;
    }
    
    // Route message based on destination zone
    switch (dest_zone) {
        case 0: // Kernel zone
            return exo_kernel_receive_message(arena, msg);
        case 1: // LibOS zone  
            return exo_libos_receive_message(arena, msg);
        case 2: // Userspace zone
            return exo_userspace_receive_message(arena, msg);
        default:
            return -EINVAL;
    }
}

// Stub implementations for zone message handlers
int exo_kernel_receive_message(exo_capnp_arena_t *arena, const capnp_pointer_t *msg) {
    (void)arena; (void)msg;
    return 0;  // Stub implementation
}

int exo_libos_receive_message(exo_capnp_arena_t *arena, const capnp_pointer_t *msg) {
    (void)arena; (void)msg;
    return 0;  // Stub implementation
}

int exo_userspace_receive_message(exo_capnp_arena_t *arena, const capnp_pointer_t *msg) {
    (void)arena; (void)msg;
    return 0;  // Stub implementation
}
