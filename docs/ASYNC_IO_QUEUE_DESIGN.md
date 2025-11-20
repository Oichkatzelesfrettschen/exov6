# Async I/O Queue Design

**Status:** Design Document (Future Implementation)
**Date:** 2025-11-20
**Phase:** 5.4

## Overview

The buffer cache currently performs synchronous I/O through `bcache_io_read()` and `bcache_io_write()`. While functional, this blocks the calling thread during disk operations. For optimal performance, we need asynchronous I/O with:

1. **Non-blocking submission** - Queue I/O requests without waiting
2. **Interrupt-driven completion** - IDE interrupts signal completion
3. **Read-ahead batching** - Group multiple prefetch requests
4. **Write-back coalescing** - Merge adjacent dirty blocks

## Current State

**What Works:**
- ✅ Synchronous read via `bcache_io_read()`
- ✅ Synchronous write via `bcache_io_write()`
- ✅ IDE driver with interrupt-driven queue (`ide.c`)
- ✅ Read-ahead stub calls `bcache_io_read_async()`

**What's Stubbed:**
- `bcache_io_read_async()` - Currently calls synchronous `bcache_io_read()`
- No background write-back daemon
- No I/O request batching

## Architecture

### Option 1: Leverage Existing IDE Queue (Simple)

The IDE driver (`kernel/fs/ide.c`) already has an interrupt-driven queue:

```c
static struct buf *idequeue;  // Request queue
void idestart(struct buf *b); // Start I/O
void ideintr(void);           // Interrupt handler
```

**Approach:**
1. Create wrapper that converts `bcache_entry_t` → `struct buf`
2. Queue request to IDE driver
3. IDE interrupt completes I/O
4. Callback marks cache entry as VALID

**Pros:**
- Minimal code changes
- Reuses proven IDE queueing
- Interrupt-driven already

**Cons:**
- One request at a time (no batching)
- Tightly coupled to IDE driver

### Option 2: Dedicated Async I/O Layer (Complex)

Create a separate async I/O subsystem:

```c
typedef struct {
    bcache_entry_t *entry;        // Cache entry
    void (*callback)(void*);      // Completion callback
    bool is_write;                // Read or write?
} async_io_request_t;

typedef struct {
    async_io_request_t *queue;    // Request queue
    uint32_t head, tail;          // Queue pointers
    struct qspinlock lock;        // Queue lock
} async_io_queue_t;
```

**Approach:**
1. Caller submits request to async queue
2. Background worker dequeues and submits to IDE
3. IDE interrupt signals completion
4. Worker invokes callback, marks entry VALID

**Pros:**
- Can batch multiple requests
- Can prioritize (read > write)
- Can coalesce adjacent writes
- Decoupled from IDE driver

**Cons:**
- More complex
- Requires kernel threads or periodic polling
- More synchronization overhead

## Recommended Approach

**Phase 5.4a: Simple Async (Short-term)**
- Use Option 1 (leverage IDE queue)
- Non-blocking submission for read-ahead
- Maintain synchronous path for demand reads
- ~200 lines of code

**Phase 5.4b: Full Async (Long-term)**
- Implement Option 2 (dedicated queue)
- Background write-back daemon
- I/O request batching and coalescing
- Integration with io_uring-style zero-copy
- ~800 lines of code

## Implementation Plan (Phase 5.4a)

### 1. Create Async Request Structure

```c
typedef struct async_buf_request {
    struct buf buf;                    // IDE buffer
    bcache_entry_t *cache_entry;       // Associated cache entry
    struct async_buf_request *next;    // Queue linkage
} async_buf_request_t;
```

### 2. Modify `bcache_io_read_async()`

```c
int bcache_io_read_async(buffer_cache_t *cache, bcache_entry_t *entry)
{
    /* Allocate async request */
    async_buf_request_t *req = malloc(sizeof(*req));

    /* Setup IDE buffer */
    req->buf.dev = entry->dev;
    req->buf.blockno = entry->blockno;
    req->buf.flags = 0;
    req->cache_entry = entry;

    /* Submit to IDE queue (non-blocking) */
    ide_submit_async(&req->buf);

    /* Return immediately - completion via interrupt */
    return 0;
}
```

### 3. Modify IDE Interrupt Handler

```c
void ideintr(void)
{
    struct buf *b = idequeue;

    /* ... existing IDE completion ... */

    /* Check if this is an async buffer cache request */
    async_buf_request_t *req = container_of(b, async_buf_request_t, buf);

    if (req->cache_entry) {
        /* Copy data to cache entry */
        memcpy(req->cache_entry->data, b->data, BSIZE);

        /* Mark entry as VALID */
        atomic_fetch_or(&req->cache_entry->flags, BCACHE_VALID);

        /* Free async request */
        free(req);
    }
}
```

## Performance Impact

**Expected Improvements:**
- **Sequential reads:** 2-4x faster (overlapped I/O)
- **Read-ahead:** Non-blocking prefetch
- **Write-back:** Delayed, coalesced writes
- **CPU utilization:** Reduced idle time during I/O

**Benchmarks (Projected):**
- **Synchronous:** 1 read at a time, ~10ms each = 100 reads/sec
- **Async (4 outstanding):** 4 overlapped reads = 400 reads/sec
- **Async + batching:** 8-16 reads/batch = 800+ reads/sec

## Integration Points

### Buffer Cache Integration
- `bcache_prefetch_async()` - Already calls `bcache_io_read_async()`
- `bcache_read_with_prefetch()` - Triggers read-ahead
- `bcache_adaptive_tune()` - Could trigger write-back

### VFS Integration (Phase 6)
- `vfs_read()` - Demand reads (synchronous)
- `vfs_readahead()` - Opportunistic prefetch (async)
- `vfs_sync()` - Flush dirty blocks (async writes)

### SIMD Integration (Phase 3)
- Checksum computation while waiting for I/O
- SIMD block copy in completion handler
- Parallel checksums for batched reads

## Future Enhancements

### Linux-style Pluggable I/O Schedulers
- **Noop:** Simple FIFO (current)
- **Deadline:** Deadline-based prioritization
- **CFQ:** Completely Fair Queuing
- **BFQ:** Budget Fair Queuing

### io_uring Integration (Long-term)
- Pre-registered buffer rings
- Zero-copy capability-tagged buffers
- Batched submission and completion
- Polling mode for low-latency

## Testing Strategy

### Unit Tests
1. Single async read completes correctly
2. Multiple async reads don't interfere
3. Async read + synchronous read mix
4. Error handling (device failure)

### Integration Tests
1. Read-ahead with sequential access
2. Write-back with delayed writes
3. Cache eviction of in-flight I/O
4. System shutdown with pending I/O

### Performance Tests
1. Sequential read throughput
2. Random read IOPS
3. Write-back coalescing effectiveness
4. CPU utilization during I/O

## Current Status

**Phase 5.4a:** ⏸️ **DEFERRED**
- `bcache_io_read_async()` implemented as synchronous fallback
- Functional but not performance-optimal
- Placeholder for future async implementation

**Rationale:**
- Current synchronous I/O is sufficient for Phase 6 VFS integration
- Async I/O can be optimized after basic functionality works
- Allows us to proceed with SIMD (Phase 3) and testing (Phase 6)

**Next Steps:**
1. ✅ Complete Phase 5 basic I/O
2. → Proceed to Phase 6 (VFS integration)
3. → Implement Phase 3 (SIMD)
4. → Return to Phase 5.4a (async I/O optimization)

---

**References:**
- Linux kernel block layer: `block/blk-core.c`
- io_uring design: Jens Axboe, "Efficient IO with io_uring" (2024)
- IDE driver: `kernel/fs/ide.c` (xv6 base)
