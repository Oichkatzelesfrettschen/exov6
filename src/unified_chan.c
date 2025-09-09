/**
 * @file unified_chan.c
 * @brief Implementation of Unified Channel Trait System
 * 
 * Provides concrete implementation of the unified channel architecture
 * that eliminates the redundancy between CHAN_DECLARE, AFFINE_CHAN_DECLARE,
 * and CHAN_DECLARE_VAR by using composable properties.
 */

#include "unified_chan.h"
#include "string.h"
#include "spinlock.h"
#include "errno.h"

/* Internal channel implementation data */
typedef struct chan_impl {
    struct spinlock lock;
    void *message_queue;       /* Message storage */
    size_t queue_capacity;     /* Maximum messages in queue */
    size_t queue_size;         /* Current messages in queue */
    uint32_t flags;            /* Internal flags */
} chan_impl_t;

/* Global channel allocator (simplified) */
static unified_chan_t channel_pool[256];
static bool channel_used[256];
static struct spinlock channel_allocator_lock = { .locked = 0, .name = "chan_alloc" };

static unified_chan_t *alloc_channel(void) {
    acquire(&channel_allocator_lock);
    
    for (int i = 0; i < 256; i++) {
        if (!channel_used[i]) {
            channel_used[i] = true;
            release(&channel_allocator_lock);
            return &channel_pool[i];
        }
    }
    
    release(&channel_allocator_lock);
    return NULL;  /* Out of channels */
}

static void free_channel(unified_chan_t *c) {
    acquire(&channel_allocator_lock);
    
    int index = c - channel_pool;
    if (index >= 0 && index < 256) {
        channel_used[index] = false;
    }
    
    release(&channel_allocator_lock);
}

/* Core channel operations */
unified_chan_t *unified_chan_create(const msg_type_desc_t *desc, uint32_t properties) {
    if (!desc) return NULL;
    
    unified_chan_t *c = alloc_channel();
    if (!c) return NULL;
    
    /* Initialize base structure */
    c->type_desc = desc;
    c->properties = properties;
    
    /* Allocate implementation data */
    chan_impl_t *impl = (chan_impl_t *)kmalloc(sizeof(chan_impl_t));
    if (!impl) {
        free_channel(c);
        return NULL;
    }
    
    initlock(&impl->lock, "unified_chan");
    impl->message_queue = NULL;
    impl->queue_capacity = 1;  /* Default single message */
    impl->queue_size = 0;
    impl->flags = 0;
    
    c->impl_data = impl;
    
    /* Initialize property-specific data */
    if (properties & CHAN_AFFINE) {
        c->ext.affine.send_count = 1;    /* Default: one send */
        c->ext.affine.recv_count = 1;    /* Default: one receive */
    }
    
    if (properties & CHAN_BOUNDED) {
        c->ext.bounded.max_messages = 16;  /* Default queue size */
        c->ext.bounded.current_count = 0;
    }
    
    if (properties & CHAN_SECURED) {
        c->ext.secured.required_caps = 0;
        c->ext.secured.owner_cap = (exo_cap){0};
    }
    
    return c;
}

void unified_chan_destroy(unified_chan_t *c) {
    if (!c) return;
    
    chan_impl_t *impl = (chan_impl_t *)c->impl_data;
    if (impl) {
        acquire(&impl->lock);
        
        /* Free message queue if allocated */
        if (impl->message_queue) {
            kfree(impl->message_queue);
        }
        
        release(&impl->lock);
        kfree(impl);
    }
    
    free_channel(c);
}

int unified_chan_send(unified_chan_t *c, exo_cap dest, const void *msg, size_t len) {
    if (!c || !msg || !c->impl_data) return -EINVAL;
    
    chan_impl_t *impl = (chan_impl_t *)c->impl_data;
    acquire(&impl->lock);
    
    /* Check affine constraints */
    if (c->properties & CHAN_AFFINE) {
        if (c->ext.affine.send_count <= 0) {
            release(&impl->lock);
            return -EPERM;  /* No sends remaining */
        }
        c->ext.affine.send_count--;
    }
    
    /* Check bounded constraints */
    if (c->properties & CHAN_BOUNDED) {
        if (c->ext.bounded.current_count >= c->ext.bounded.max_messages) {
            release(&impl->lock);
            return -ENOSPC;  /* Queue full */
        }
    }
    
    /* Validate message size */
    if (len > c->type_desc->msg_size) {
        release(&impl->lock);
        return -EMSGSIZE;
    }
    
    if ((c->properties & CHAN_VAR) == 0 && len != c->type_desc->msg_size) {
        release(&impl->lock);
        return -EMSGSIZE;  /* Fixed-size channels require exact size */
    }
    
    /* Encode message */
    unsigned char *buffer = kmalloc(c->type_desc->msg_size);
    if (!buffer) {
        release(&impl->lock);
        return -ENOMEM;
    }
    
    size_t encoded_len = len;
    if (c->type_desc->encode_fn) {
        encoded_len = c->type_desc->encode_fn(msg, buffer);
    } else {
        /* Direct copy for simple types */
        memcpy(buffer, msg, len);
    }
    
    /* Simulate sending through exo capability endpoint */
    /* In real implementation, this would use the exokernel IPC */
    int result = exo_send(dest, buffer, encoded_len);
    
    if (result == 0 && (c->properties & CHAN_BOUNDED)) {
        c->ext.bounded.current_count++;
    }
    
    kfree(buffer);
    release(&impl->lock);
    
    return result;
}

int unified_chan_recv(unified_chan_t *c, exo_cap src, void *msg, size_t max_len) {
    if (!c || !msg || !c->impl_data) return -EINVAL;
    
    chan_impl_t *impl = (chan_impl_t *)c->impl_data;
    acquire(&impl->lock);
    
    /* Check affine constraints */
    if (c->properties & CHAN_AFFINE) {
        if (c->ext.affine.recv_count <= 0) {
            release(&impl->lock);
            return -EPERM;  /* No receives remaining */
        }
        c->ext.affine.recv_count--;
    }
    
    /* Allocate receive buffer */
    unsigned char *buffer = kmalloc(c->type_desc->msg_size);
    if (!buffer) {
        release(&impl->lock);
        return -ENOMEM;
    }
    
    /* Simulate receiving through exo capability endpoint */
    int result = exo_recv(src, buffer, c->type_desc->msg_size);
    
    if (result >= 0) {
        /* Decode message */
        size_t decoded_len = max_len;
        if (c->type_desc->decode_fn) {
            decoded_len = c->type_desc->decode_fn(msg, buffer);
        } else {
            /* Direct copy for simple types */
            size_t copy_len = (result < max_len) ? result : max_len;
            memcpy(msg, buffer, copy_len);
            decoded_len = copy_len;
        }
        
        if ((c->properties & CHAN_BOUNDED) && c->ext.bounded.current_count > 0) {
            c->ext.bounded.current_count--;
        }
        
        result = decoded_len;
    }
    
    kfree(buffer);
    release(&impl->lock);
    
    return result;
}

/* Property configuration functions */
int unified_chan_configure_affine(unified_chan_t *c, int max_sends, int max_recvs) {
    if (!c || !(c->properties & CHAN_AFFINE)) return -EINVAL;
    
    chan_impl_t *impl = (chan_impl_t *)c->impl_data;
    acquire(&impl->lock);
    
    c->ext.affine.send_count = max_sends;
    c->ext.affine.recv_count = max_recvs;
    
    release(&impl->lock);
    return 0;
}

int unified_chan_configure_bounded(unified_chan_t *c, size_t max_messages) {
    if (!c || !(c->properties & CHAN_BOUNDED)) return -EINVAL;
    
    chan_impl_t *impl = (chan_impl_t *)c->impl_data;
    acquire(&impl->lock);
    
    c->ext.bounded.max_messages = max_messages;
    
    release(&impl->lock);
    return 0;
}

int unified_chan_configure_secured(unified_chan_t *c, uint32_t required_caps, exo_cap owner) {
    if (!c || !(c->properties & CHAN_SECURED)) return -EINVAL;
    
    chan_impl_t *impl = (chan_impl_t *)c->impl_data;
    acquire(&impl->lock);
    
    c->ext.secured.required_caps = required_caps;
    c->ext.secured.owner_cap = owner;
    
    release(&impl->lock);
    return 0;
}

/* Compatibility functions for existing code */
void *kmalloc(size_t size) {
    /* Temporary stub - in real implementation would use kernel allocator */
    static char memory_pool[65536];
    static size_t pool_offset = 0;
    
    if (pool_offset + size > sizeof(memory_pool)) {
        return NULL;
    }
    
    void *ptr = &memory_pool[pool_offset];
    pool_offset += size;
    return ptr;
}

void kfree(void *ptr) {
    /* Temporary stub - in real implementation would free memory */
    (void)ptr;
}