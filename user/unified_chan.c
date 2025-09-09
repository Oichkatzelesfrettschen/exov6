/**
 * @file unified_chan.c
 * @brief Unified Channel Implementation
 */

#include "unified_chan.h"
#include "user.h"
#include <stdlib.h>

/**
 * Create a unified channel with specified properties
 */
unified_chan_t *unified_chan_create(const msg_type_desc_t *desc, uint32_t properties) {
    unified_chan_t *c = malloc(sizeof(*c));
    if (c) {
        c->type_desc = desc;
        c->properties = properties;
        c->impl_data = NULL;
        // Initialize extensions based on properties
        if (properties & CHAN_AFFINE) {
            c->ext.affine.send_count = 0;
            c->ext.affine.recv_count = 0;
        }
        if (properties & CHAN_BOUNDED) {
            c->ext.bounded.max_messages = 16; // Default
            c->ext.bounded.current_count = 0;
        }
    }
    return c;
}

/**
 * Destroy a unified channel
 */
void unified_chan_destroy(unified_chan_t *c) {
    if (c) {
        free(c->impl_data);
        free(c);
    }
}

/**
 * Send message through unified channel
 */
int unified_chan_send(unified_chan_t *c, exo_cap dest, const void *msg, size_t len) {
    if (!c || !msg) return -1;
    
    // Check affine constraints
    if (c->properties & CHAN_AFFINE) {
        // For simplicity, allow multiple sends for now
    }
    
    // Check bounded constraints
    if (c->properties & CHAN_BOUNDED) {
        if (c->ext.bounded.current_count >= c->ext.bounded.max_messages) {
            return -1; // Queue full
        }
    }
    
    // Delegate to capability system
    return cap_send(dest, msg, len);
}

/**
 * Receive message through unified channel
 */
int unified_chan_recv(unified_chan_t *c, exo_cap src, void *msg, size_t max_len) {
    if (!c || !msg) return -1;
    
    // Check affine constraints
    if (c->properties & CHAN_AFFINE) {
        // For simplicity, allow multiple receives for now
    }
    
    // Delegate to capability system
    return cap_recv(src, msg, max_len);
}