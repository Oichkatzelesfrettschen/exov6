/*
 * unified_ipc.c - Unified Zero-Copy IPC Architecture
 * 
 * Pure C17 implementation harmonizing all IPC mechanisms:
 * - FastIPC for ultra-low latency
 * - Channels for structured communication  
 * - STREAMS for modular I/O
 * - BSD sockets compatibility
 * - Cap'n Proto for serialization
 * - Capability-secured endpoints
 * 
 * Performance targets:
 * - < 1000 cycle latency
 * - Zero-copy data transfer
 * - Lock-free operations
 * - Cache-optimized structures
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdatomic.h>
#include <string.h>
#include <stdalign.h>
#include <errno.h>

#include "types.h"
#include "cap.h"  /* Capability system */
#include "ipc.h"
#include "hal/hal.h"

/* Type definitions for POSIX compatibility */
#ifndef _SSIZE_T_DEFINED
#define _SSIZE_T_DEFINED
typedef long ssize_t;
#endif

#ifndef _SOCKLEN_T_DEFINED
#define _SOCKLEN_T_DEFINED
typedef uint32_t socklen_t;
#endif

/* Fallback errno definitions if not in errno.h */
#ifndef EINVAL
#define EINVAL 22
#endif
#ifndef EPERM
#define EPERM 1
#endif
#ifndef ETIMEDOUT
#define ETIMEDOUT 110
#endif
#ifndef ENOMEM
#define ENOMEM 12
#endif
#ifndef ENOTCONN
#define ENOTCONN 107
#endif
#ifndef ENOBUFS
#define ENOBUFS 105
#endif
#ifndef ENOSPC
#define ENOSPC 28
#endif
#ifndef ENOTSOCK
#define ENOTSOCK 88
#endif
#ifndef ENOTSUP
#define ENOTSUP 95
#endif

/* Socket constants */
#ifndef SOCK_STREAM
#define SOCK_STREAM 1
#endif
#ifndef SOCK_DGRAM
#define SOCK_DGRAM 2
#endif

/* Forward declarations for STREAMS */
struct strbuf {
    char *buf;
    int maxlen;
    int len;
};

/* Capability rights for IPC */
#ifndef CAP_RIGHT_INVOKE
#define CAP_RIGHT_INVOKE 0x10
#endif
#ifndef CAP_RIGHT_IPC
#define CAP_RIGHT_IPC 0x20
#endif
#ifndef CAP_RIGHT_NET
#define CAP_RIGHT_NET 0x40
#endif
#ifndef CAP_RIGHT_READ
#define CAP_RIGHT_READ 0x01
#endif
#ifndef CAP_RIGHT_WRITE
#define CAP_RIGHT_WRITE 0x02
#endif

/* ============================================================================
 * IPC Constants and Configuration
 * ============================================================================ */

#define IPC_MAX_ENDPOINTS      4096    /* Maximum endpoints */
#define IPC_MAX_CHANNELS       2048    /* Maximum channels */
#define IPC_MAX_STREAMS        1024    /* Maximum STREAMS */
#define IPC_MAX_SOCKETS        1024    /* Maximum BSD sockets */
#define IPC_BUFFER_SIZE        65536   /* Default buffer size */
#define IPC_CACHE_LINE_SIZE    64      /* Cache line size */
#define IPC_MAX_MESSAGE_SIZE   (1 << 20)  /* 1MB max message */

/* IPC types unified */
typedef enum {
    IPC_TYPE_INVALID = 0,
    IPC_TYPE_FASTIPC = 1,      /* Ultra-fast register-based */
    IPC_TYPE_CHANNEL = 2,      /* Bidirectional channels */
    IPC_TYPE_STREAM = 3,       /* UNIX V8 STREAMS */
    IPC_TYPE_SOCKET = 4,       /* BSD sockets */
    IPC_TYPE_PIPE = 5,         /* Traditional pipes */
    IPC_TYPE_QUEUE = 6,        /* Message queues */
    IPC_TYPE_SHMEM = 7,        /* Shared memory */
    IPC_TYPE_SIGNAL = 8,       /* Signals */
    IPC_TYPE_EVENTFD = 9,      /* Event notification */
    IPC_TYPE_CAPNP = 10        /* Cap'n Proto RPC */
} ipc_type_t;

/* IPC flags */
typedef enum {
    IPC_FLAG_NONBLOCK   = (1 << 0),
    IPC_FLAG_ZEROCOPY   = (1 << 1),
    IPC_FLAG_BROADCAST  = (1 << 2),
    IPC_FLAG_MULTICAST  = (1 << 3),
    IPC_FLAG_RELIABLE   = (1 << 4),
    IPC_FLAG_ORDERED    = (1 << 5),
    IPC_FLAG_ENCRYPTED  = (1 << 6),
    IPC_FLAG_COMPRESSED = (1 << 7),
    IPC_FLAG_PRIORITY   = (1 << 8),
    IPC_FLAG_REALTIME   = (1 << 9)
} ipc_flags_t;

/* ============================================================================
 * Zero-Copy Buffer Management
 * ============================================================================ */

typedef struct ipc_buffer {
    _Alignas(64) struct {
        _Atomic(uint64_t) head;         /* Producer position */
        _Atomic(uint64_t) tail;         /* Consumer position */
        _Atomic(uint64_t) size;         /* Buffer size */
        _Atomic(uint32_t) flags;        /* Buffer flags */
        _Atomic(uint32_t) ref_count;    /* Reference count */
        
        /* Physical pages for zero-copy */
        uint64_t *pages;                /* Page frame numbers */
        uint32_t page_count;            /* Number of pages */
        
        /* Memory mapping info */
        void *vaddr;                    /* Virtual address */
        uint64_t paddr;                 /* Physical address */
        
        /* Statistics */
        _Atomic(uint64_t) bytes_written;
        _Atomic(uint64_t) bytes_read;
        _Atomic(uint64_t) messages_sent;
        _Atomic(uint64_t) messages_received;
    } data;
    
    /* Actual buffer (cache-aligned) */
    _Alignas(4096) uint8_t buffer[IPC_BUFFER_SIZE];
} ipc_buffer_t;

/* ============================================================================
 * Unified IPC Endpoint
 * ============================================================================ */

typedef struct ipc_endpoint {
    _Alignas(64) struct {
        /* Identity */
        _Atomic(uint64_t) id;           /* Endpoint ID */
        _Atomic(ipc_type_t) type;       /* IPC type */
        _Atomic(uint32_t) flags;        /* Endpoint flags */
        _Atomic(uint32_t) state;        /* Endpoint state */
        
        /* Capability security */
        uint64_t cap_id;                /* Associated capability */
        uint32_t domain;                /* Security domain */
        
        /* Connections */
        _Atomic(struct ipc_endpoint*) peer;     /* Connected peer */
        _Atomic(struct ipc_endpoint*) next;     /* Next in chain */
        
        /* Buffers for zero-copy */
        ipc_buffer_t *send_buffer;
        ipc_buffer_t *recv_buffer;
        
        /* Protocol-specific data */
        union {
            struct {  /* FastIPC */
                _Atomic(uint64_t) registers[8];
                _Atomic(uint32_t) ready;
            } fastipc;
            
            struct {  /* Channel */
                _Atomic(uint64_t) sequence;
                _Atomic(uint32_t) window;
            } channel;
            
            struct {  /* STREAMS */
                void *stream_head;
                void *stream_modules[8];
                uint32_t module_count;
            } stream;
            
            struct {  /* Socket */
                uint32_t family;
                uint32_t type;
                uint32_t protocol;
                uint16_t local_port;
                uint16_t remote_port;
            } socket;
        } proto;
        
        /* Wait queue */
        _Atomic(void*) wait_queue;
        
        /* Statistics */
        _Atomic(uint64_t) operations;
        _Atomic(uint64_t) errors;
    } data;
} ipc_endpoint_t;

/* Static assertions */
_Static_assert(sizeof(ipc_endpoint_t) <= 256, "endpoint must fit in 4 cache lines");
_Static_assert(alignof(ipc_endpoint_t) == 64, "endpoint must be cache-aligned");

/* ============================================================================
 * IPC Message Structure
 * ============================================================================ */

typedef struct ipc_message {
    _Alignas(64) struct {
        /* Header */
        uint64_t id;                    /* Message ID */
        uint64_t timestamp;             /* Time stamp */
        uint32_t type;                  /* Message type */
        uint32_t flags;                 /* Message flags */
        uint32_t length;                /* Data length */
        uint32_t priority;              /* Priority level */
        
        /* Routing */
        uint64_t src_endpoint;          /* Source endpoint */
        uint64_t dst_endpoint;          /* Destination endpoint */
        
        /* Capability */
        uint64_t cap_id;                /* Capability for access */
        
        /* Zero-copy data */
        union {
            uint8_t inline_data[64];    /* Small inline data */
            struct {
                uint64_t paddr;         /* Physical address */
                uint64_t vaddr;         /* Virtual address */
                uint32_t page_count;    /* Number of pages */
            } zerocopy;
        } data;
        
        /* Checksum/HMAC */
        uint32_t checksum;
        uint8_t hmac[32];
    } header;
    
    /* Variable-length data follows */
    uint8_t payload[];
} ipc_message_t;

/* ============================================================================
 * Global IPC Tables
 * ============================================================================ */

static _Alignas(4096) ipc_endpoint_t endpoint_table[IPC_MAX_ENDPOINTS];
static _Atomic(uint64_t) next_endpoint_id = 1;

/* Hash table for fast endpoint lookup */
static _Atomic(ipc_endpoint_t*) endpoint_hash[1024];

/* ============================================================================
 * Helper Functions (Stubs for now)
 * ============================================================================ */

static inline ipc_endpoint_t* ipc_endpoint_lookup(uint64_t id) {
    if (id == 0 || id >= IPC_MAX_ENDPOINTS) return NULL;
    return &endpoint_table[id];
}

static inline ipc_endpoint_t* ipc_endpoint_alloc(ipc_type_t type) {
    uint64_t id = atomic_fetch_add(&next_endpoint_id, 1);
    if (id >= IPC_MAX_ENDPOINTS) return NULL;
    ipc_endpoint_t *ep = &endpoint_table[id];
    atomic_store(&ep->data.id, id);
    atomic_store(&ep->data.type, type);
    return ep;
}

static inline void ipc_endpoint_free(ipc_endpoint_t *ep) {
    if (ep) {
        atomic_store(&ep->data.state, 0);
    }
}

static inline ipc_buffer_t* ipc_buffer_alloc(size_t size) {
    (void)size;
    return NULL;  /* Stub - buffer management not implemented yet */
}

static inline int capability_check(uint64_t cap_id, uint32_t required_rights) {
    (void)cap_id;
    (void)required_rights;
    return 1;  /* Stub - always allow for now */
}

static inline int channel_send_zerocopy(ipc_endpoint_t *ep, const void *data, size_t len) {
    (void)ep; (void)data; (void)len;
    return 0;  /* Stub */
}

static inline size_t ipc_buffer_space(ipc_buffer_t *buf) {
    (void)buf;
    return 4096;  /* Stub */
}

static inline ssize_t ipc_buffer_write(ipc_buffer_t *buf, const void *data, size_t len) {
    (void)buf; (void)data; (void)len;
    return len;  /* Stub */
}

static inline void ipc_wakeup(ipc_endpoint_t *ep) {
    (void)ep;  /* Stub */
}

static inline ssize_t socket_send(ipc_endpoint_t *ep, const void *data, size_t len, int flags) {
    (void)ep; (void)data; (void)len; (void)flags;
    return len;  /* Stub */
}

static inline ssize_t socket_receive(ipc_endpoint_t *ep, void *buf, size_t len, int flags) {
    (void)ep; (void)buf; (void)len; (void)flags;
    return 0;  /* Stub */
}

static inline ssize_t fastipc_send_message(ipc_endpoint_t *ep, const uint64_t *regs) {
    (void)ep; (void)regs;
    return 0;  /* Stub */
}

static inline ssize_t fastipc_receive_message(ipc_endpoint_t *ep, uint64_t *regs) {
    (void)ep; (void)regs;
    return 0;  /* Stub */
}

static inline ssize_t channel_receive(ipc_endpoint_t *ep, void *buf, size_t len) {
    (void)ep; (void)buf; (void)len;
    return 0;  /* Stub */
}

static inline ssize_t streams_read(ipc_endpoint_t *ep, struct strbuf *data, int *flags) {
    (void)ep; (void)data; (void)flags;
    return 0;  /* Stub */
}

static inline void lattice_init(void) {
    /* Stub */
}

static inline void ipc_register_syscalls(void) {
    /* Stub */
}

static inline void printk(const char *fmt, ...) {
    (void)fmt;  /* Stub */
}

/* ============================================================================
 * FastIPC Implementation (Register-based)
 * ============================================================================ */

/**
 * fastipc_call - Ultra-fast synchronous IPC call
 * @endpoint_id: Target endpoint
 * @regs: Register values to pass
 * @result: Register values returned
 * 
 * Returns: 0 on success, error code on failure
 * 
 * Performance: < 500 cycles for local calls
 */
int fastipc_call(uint64_t endpoint_id, uint64_t regs[8], uint64_t result[8]) {
    ipc_endpoint_t *ep = ipc_endpoint_lookup(endpoint_id);
    if (!ep || ep->data.type != IPC_TYPE_FASTIPC) {
        return -EINVAL;
    }
    
    /* Check capability */
    if (!capability_check(ep->data.cap_id, CAP_RIGHT_INVOKE)) {
        return -EPERM;
    }
    
    /* Copy registers atomically */
    for (int i = 0; i < 8; i++) {
        atomic_store_explicit(&ep->data.proto.fastipc.registers[i], 
                             regs[i], memory_order_release);
    }
    
    /* Signal ready */
    atomic_store_explicit(&ep->data.proto.fastipc.ready, 1, 
                         memory_order_release);
    
    /* Spin wait for response (with timeout) */
    uint64_t start = hal_read_timestamp();
    uint64_t timeout = start + 1000000;  /* 1ms timeout */
    
    while (atomic_load_explicit(&ep->data.proto.fastipc.ready, 
                                memory_order_acquire) != 2) {
        hal_cpu_pause();
        
        if (hal_read_timestamp() > timeout) {
            return -ETIMEDOUT;
        }
    }
    
    /* Copy result registers */
    for (int i = 0; i < 8; i++) {
        result[i] = atomic_load_explicit(&ep->data.proto.fastipc.registers[i], 
                                        memory_order_acquire);
    }
    
    /* Clear ready flag */
    atomic_store_explicit(&ep->data.proto.fastipc.ready, 0, 
                         memory_order_relaxed);
    
    /* Update statistics */
    atomic_fetch_add_explicit(&ep->data.operations, 1, memory_order_relaxed);
    
    return 0;
}

/* ============================================================================
 * Channel Implementation (Bidirectional)
 * ============================================================================ */

/**
 * channel_create - Create a bidirectional channel
 * @ep1: First endpoint ID (output)
 * @ep2: Second endpoint ID (output)
 * @cap_id: Capability for channel
 * 
 * Returns: 0 on success, error code on failure
 */
int channel_create(uint64_t *ep1, uint64_t *ep2, uint64_t cap_id) {
    /* Check capability */
    if (!capability_check(cap_id, CAP_RIGHT_IPC)) {
        return -EPERM;
    }
    
    /* Allocate two endpoints */
    ipc_endpoint_t *endpoint1 = ipc_endpoint_alloc(IPC_TYPE_CHANNEL);
    ipc_endpoint_t *endpoint2 = ipc_endpoint_alloc(IPC_TYPE_CHANNEL);
    
    if (!endpoint1 || !endpoint2) {
        if (endpoint1) ipc_endpoint_free(endpoint1);
        if (endpoint2) ipc_endpoint_free(endpoint2);
        return -ENOMEM;
    }
    
    /* Link endpoints */
    atomic_store_explicit(&endpoint1->data.peer, endpoint2, 
                         memory_order_release);
    atomic_store_explicit(&endpoint2->data.peer, endpoint1, 
                         memory_order_release);
    
    /* Set capability */
    endpoint1->data.cap_id = cap_id;
    endpoint2->data.cap_id = cap_id;
    
    /* Initialize channel state */
    atomic_init(&endpoint1->data.proto.channel.sequence, 0);
    atomic_init(&endpoint1->data.proto.channel.window, 64);
    atomic_init(&endpoint2->data.proto.channel.sequence, 0);
    atomic_init(&endpoint2->data.proto.channel.window, 64);
    
    /* Allocate buffers */
    endpoint1->data.send_buffer = ipc_buffer_alloc(IPC_BUFFER_SIZE);
    endpoint1->data.recv_buffer = ipc_buffer_alloc(IPC_BUFFER_SIZE);
    endpoint2->data.send_buffer = ipc_buffer_alloc(IPC_BUFFER_SIZE);
    endpoint2->data.recv_buffer = ipc_buffer_alloc(IPC_BUFFER_SIZE);
    
    *ep1 = atomic_load_explicit(&endpoint1->data.id, memory_order_relaxed);
    *ep2 = atomic_load_explicit(&endpoint2->data.id, memory_order_relaxed);
    
    return 0;
}

/**
 * channel_send - Send message through channel (zero-copy)
 * @endpoint_id: Source endpoint
 * @data: Data to send
 * @length: Data length
 * @flags: Send flags
 * 
 * Returns: Bytes sent or negative error
 */
ssize_t channel_send(uint64_t endpoint_id, const void *data, 
                    size_t length, uint32_t flags) {
    ipc_endpoint_t *ep = ipc_endpoint_lookup(endpoint_id);
    if (!ep || ep->data.type != IPC_TYPE_CHANNEL) {
        return -EINVAL;
    }
    
    ipc_endpoint_t *peer = atomic_load_explicit(&ep->data.peer, 
                                                memory_order_acquire);
    if (!peer) {
        return -ENOTCONN;
    }
    
    /* Zero-copy if possible */
    if (flags & IPC_FLAG_ZEROCOPY && length > 4096) {
        /* Map pages directly */
        return channel_send_zerocopy(ep, data, length);
    }
    
    /* Regular buffered send */
    ipc_buffer_t *buffer = peer->data.recv_buffer;
    if (!buffer) {
        return -ENOBUFS;
    }
    
    /* Wait for space if needed */
    if (!(flags & IPC_FLAG_NONBLOCK)) {
        while (ipc_buffer_space(buffer) < length) {
            hal_cpu_pause();
        }
    }
    
    /* Copy data to buffer */
    size_t written = ipc_buffer_write(buffer, data, length);
    
    /* Update statistics */
    atomic_fetch_add_explicit(&buffer->data.messages_sent, 1, 
                             memory_order_relaxed);
    
    /* Wake waiting receivers */
    ipc_wakeup(peer->data.wait_queue);
    
    return written;
}

/* ============================================================================
 * STREAMS Implementation (UNIX V8-V10)
 * ============================================================================ */

/**
 * streams_create - Create a STREAMS endpoint
 * @endpoint_id: Endpoint ID (output)
 * @cap_id: Capability
 * 
 * Returns: 0 on success, error code on failure
 */
int streams_create(uint64_t *endpoint_id, uint64_t cap_id) {
    if (!capability_check(cap_id, CAP_RIGHT_IPC)) {
        return -EPERM;
    }
    
    ipc_endpoint_t *ep = ipc_endpoint_alloc(IPC_TYPE_STREAM);
    if (!ep) {
        return -ENOMEM;
    }
    
    ep->data.cap_id = cap_id;
    ep->data.proto.stream.stream_head = NULL;
    ep->data.proto.stream.module_count = 0;
    
    *endpoint_id = atomic_load_explicit(&ep->data.id, memory_order_relaxed);
    
    return 0;
}

/**
 * streams_push_module - Push a module onto STREAM
 * @endpoint_id: STREAM endpoint
 * @module: Module to push
 * 
 * Returns: 0 on success, error code on failure
 */
int streams_push_module(uint64_t endpoint_id, void *module) {
    ipc_endpoint_t *ep = ipc_endpoint_lookup(endpoint_id);
    if (!ep || ep->data.type != IPC_TYPE_STREAM) {
        return -EINVAL;
    }
    
    if (ep->data.proto.stream.module_count >= 8) {
        return -ENOSPC;
    }
    
    /* Push module onto stack */
    ep->data.proto.stream.stream_modules[ep->data.proto.stream.module_count++] = module;
    
    return 0;
}

/**
 * streams_write - Write to STREAM
 * @endpoint_id: STREAM endpoint
 * @ctrl: Control message
 * @data: Data message
 * @flags: Write flags
 * 
 * Returns: 0 on success, error code on failure
 */
int streams_write(uint64_t endpoint_id, struct strbuf *ctrl, 
                 struct strbuf *data, int flags) {
    ipc_endpoint_t *ep = ipc_endpoint_lookup(endpoint_id);
    if (!ep || ep->data.type != IPC_TYPE_STREAM) {
        return -EINVAL;
    }
    
    /* Process through module stack */
    for (int i = ep->data.proto.stream.module_count - 1; i >= 0; i--) {
        void *module = ep->data.proto.stream.stream_modules[i];
        /* Module processing would go here */
    }
    
    /* Write to stream head */
    if (ep->data.send_buffer) {
        if (ctrl && ctrl->len > 0) {
            ipc_buffer_write(ep->data.send_buffer, ctrl->buf, ctrl->len);
        }
        if (data && data->len > 0) {
            ipc_buffer_write(ep->data.send_buffer, data->buf, data->len);
        }
    }
    
    return 0;
}

/* ============================================================================
 * BSD Socket Compatibility Layer
 * ============================================================================ */

/**
 * socket_create - Create BSD-compatible socket
 * @domain: Address family (AF_INET, AF_UNIX, etc.)
 * @type: Socket type (SOCK_STREAM, SOCK_DGRAM, etc.)
 * @protocol: Protocol number
 * @cap_id: Capability
 * 
 * Returns: Socket endpoint ID or negative error
 */
int socket_create(int domain, int type, int protocol, uint64_t cap_id) {
    if (!capability_check(cap_id, CAP_RIGHT_NET)) {
        return -EPERM;
    }
    
    ipc_endpoint_t *ep = ipc_endpoint_alloc(IPC_TYPE_SOCKET);
    if (!ep) {
        return -ENOMEM;
    }
    
    ep->data.cap_id = cap_id;
    ep->data.proto.socket.family = domain;
    ep->data.proto.socket.type = type;
    ep->data.proto.socket.protocol = protocol;
    
    /* Allocate buffers based on socket type */
    if (type == SOCK_STREAM) {
        ep->data.send_buffer = ipc_buffer_alloc(65536);  /* 64KB */
        ep->data.recv_buffer = ipc_buffer_alloc(65536);
    } else if (type == SOCK_DGRAM) {
        ep->data.send_buffer = ipc_buffer_alloc(8192);   /* 8KB */
        ep->data.recv_buffer = ipc_buffer_alloc(8192);
    }
    
    return atomic_load_explicit(&ep->data.id, memory_order_relaxed);
}

/**
 * socket_connect - Connect socket to remote endpoint
 * @socket_id: Socket endpoint ID
 * @addr: Address to connect to
 * @addrlen: Address length
 * 
 * Returns: 0 on success, error code on failure
 */
int socket_connect(uint64_t socket_id, const struct sockaddr *addr, 
                  socklen_t addrlen) {
    ipc_endpoint_t *ep = ipc_endpoint_lookup(socket_id);
    if (!ep || ep->data.type != IPC_TYPE_SOCKET) {
        return -ENOTSOCK;
    }
    
    /* Find or create remote endpoint */
    /* This would involve network stack integration */
    
    return 0;
}

/* ============================================================================
 * Zero-Copy Transfer Implementation
 * ============================================================================ */

/**
 * ipc_zerocopy_map - Map pages for zero-copy transfer
 * @src_ep: Source endpoint
 * @dst_ep: Destination endpoint
 * @pages: Page frame numbers
 * @count: Number of pages
 * 
 * Returns: Virtual address in destination or NULL
 */
void* ipc_zerocopy_map(ipc_endpoint_t *src_ep, ipc_endpoint_t *dst_ep,
                      uint64_t *pages, uint32_t count) {
    /* Check capabilities */
    if (!capability_check(src_ep->data.cap_id, CAP_RIGHT_READ) ||
        !capability_check(dst_ep->data.cap_id, CAP_RIGHT_WRITE)) {
        return NULL;
    }
    
    /* Map pages into destination address space */
    void *vaddr = NULL;
    for (uint32_t i = 0; i < count; i++) {
        uint64_t paddr = pages[i] << 12;  /* Convert to physical address */
        
        /* Use HAL to map page */
        if (hal_current && hal_current->memory) {
            hal_current->memory->page_map(NULL, (uint64_t)vaddr + (i << 12),
                                         paddr, 4096, HAL_PAGE_PRESENT | 
                                         HAL_PAGE_WRITABLE | HAL_PAGE_USER);
        }
    }
    
    return vaddr;
}

/**
 * ipc_zerocopy_unmap - Unmap zero-copy pages
 * @vaddr: Virtual address
 * @count: Number of pages
 */
void ipc_zerocopy_unmap(void *vaddr, uint32_t count) {
    if (hal_current && hal_current->memory) {
        hal_current->memory->page_unmap(NULL, (uint64_t)vaddr, count * 4096);
    }
}

/* ============================================================================
 * Unified IPC Interface
 * ============================================================================ */

/**
 * ipc_send - Unified send interface
 * @endpoint_id: Source endpoint
 * @msg: Message to send
 * @flags: Send flags
 * 
 * Returns: 0 on success, error code on failure
 */
int ipc_send(uint64_t endpoint_id, ipc_message_t *msg, uint32_t flags) {
    ipc_endpoint_t *ep = ipc_endpoint_lookup(endpoint_id);
    if (!ep) {
        return -EINVAL;
    }
    
    /* Route based on IPC type */
    switch (ep->data.type) {
    case IPC_TYPE_FASTIPC:
        return fastipc_send_message(ep, msg);
        
    case IPC_TYPE_CHANNEL:
        return channel_send(endpoint_id, msg->payload, 
                          msg->header.length, flags);
        
    case IPC_TYPE_STREAM:
        {
            struct strbuf data = {
                .buf = (char*)msg->payload,
                .len = msg->header.length,
                .maxlen = msg->header.length
            };
            return streams_write(endpoint_id, NULL, &data, flags);
        }
        
    case IPC_TYPE_SOCKET:
        return socket_send(ep, msg->payload,
                          msg->header.length, flags);
        
    default:
        return -ENOTSUP;
    }
}

/**
 * ipc_receive - Unified receive interface
 * @endpoint_id: Destination endpoint
 * @msg: Message buffer
 * @flags: Receive flags
 * 
 * Returns: Message length or negative error
 */
ssize_t ipc_receive(uint64_t endpoint_id, ipc_message_t *msg, uint32_t flags) {
    ipc_endpoint_t *ep = ipc_endpoint_lookup(endpoint_id);
    if (!ep) {
        return -EINVAL;
    }
    
    /* Route based on IPC type */
    switch (ep->data.type) {
    case IPC_TYPE_FASTIPC:
        return fastipc_receive_message(ep, msg);
        
    case IPC_TYPE_CHANNEL:
        return channel_receive(ep, msg->payload,
                              IPC_MAX_MESSAGE_SIZE);
        
    case IPC_TYPE_STREAM:
        {
            struct strbuf data = {
                .buf = (char*)msg->payload,
                .maxlen = IPC_MAX_MESSAGE_SIZE
            };
            int ret = streams_read(ep, &data, (int*)&flags);
            msg->header.length = data.len;
            return ret < 0 ? ret : data.len;
        }
        
    case IPC_TYPE_SOCKET:
        return socket_receive(ep, msg->payload,
                             IPC_MAX_MESSAGE_SIZE, flags);
        
    default:
        return -ENOTSUP;
    }
}

/* ============================================================================
 * IPC System Initialization
 * ============================================================================ */

/**
 * ipc_init - Initialize unified IPC system
 */
void ipc_init(void) {
    /* Initialize endpoint table */
    for (int i = 0; i < IPC_MAX_ENDPOINTS; i++) {
        atomic_init(&endpoint_table[i].data.id, 0);
        atomic_init(&endpoint_table[i].data.type, IPC_TYPE_INVALID);
    }
    
    /* Initialize hash table */
    for (int i = 0; i < 1024; i++) {
        atomic_init(&endpoint_hash[i], NULL);
    }
    
    /* Initialize capability system if needed */
    lattice_init();
    
    /* Register IPC syscalls */
    ipc_register_syscalls();
    
    printk("Unified IPC system initialized: FastIPC, Channels, STREAMS, Sockets\n");
}