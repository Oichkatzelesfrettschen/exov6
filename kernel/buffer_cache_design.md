# PDAC-Aware Buffer Cache Design & VFS Integration

## 1. Cache Architecture Clarification

### Buffer Cache vs. Page Cache
The current implementation utilizes a **Block-based Buffer Cache**, not a Page Cache.
- **Unit of Operation**: The cache operates on fixed-size blocks defined by `BSIZE` (512 bytes).
- **Physical Awareness**: The cache is aware of device IDs and block numbers, mapping `(device, block_number)` to a cache entry (`bcache_entry_t`).
- **Memory Layout**: It does not manage variable-size buffers. Each entry contains a pointer to a `BSIZE` memory region.

### PDAC (Probabilistic DAG Algebra with Capabilities) Logic Insertion
The PDAC logic is inserted directly into the buffer cache entry lookup and validation process:
1.  **Storage**: Each `bcache_entry_t` stores a `vfs_capability_t` structure, which includes access rights, expiry, owner UID, and a cryptographic signature.
2.  **Enforcement**:
    -   When requesting a block via `bcache_get()` or `bcache_get_or_read()`, the caller must provide a `required_cap`.
    -   The cache verifies that the cached entry's capability matches or exceeds the `required_cap` rights and has not expired/tampered with.
    -   This effectively maps physical frames (blocks) to security domains defined by the capabilities.

## 2. VFS Layering & Caching

### Layering Model
The VFS integration follows this path:
1.  **System Call**: User invokes `read()`, `write()`, etc.
2.  **VFS Layer**: `kernel/vfs/vfs_file.c` handles the `struct vfs_file` and calls the filesystem-specific operation (`file->f_op->read`).
3.  **Filesystem Layer**: `kernel/fs/minix3.c` (e.g., `minix3_file_read`) translates the file offset to a logical block number.
4.  **Block Mapping**: `minix3_bmap` maps the logical block to a physical disk block.
5.  **Buffer Cache**: The filesystem requests the physical block from the `buffer_cache`.
    -   **Capability Propagation**: The `vfs_file` structure contains the active capability (`file->capability`). This capability is passed down to the buffer cache to authorize access to the block.
6.  **I/O Layer**: If a cache miss occurs, `kernel/bcache_io.c` performs the actual device I/O.

### Invariants
1.  **Single Source of Truth**: For any given `(device, block)`, there is at most one active `bcache_entry_t` in the system (ensured by hash chain locking or similar mechanisms - currently relying on global lock or atomic handling in `bcache_alloc`).
2.  **Capability Persistence**: A capability associated with a file at `open()` time propagates to all accessed pages/blocks. The block cache entry retains the capability used to load it (or the first valid one).
3.  **No Aliasing of Dirty Pages**: Since the cache is physically indexed by `(dev, block)`, aliasing of the same file offset is impossible unless the filesystem creates multiple references to the same block (hard links), which is handled correctly as they resolve to the same physical block.
4.  **Security Domain Isolation**: A process cannot access a cached block unless it presents a valid capability that intersects with the block's required security domain (in this model, the capability presented must match the rights check).

## 3. Plan for Completion

1.  **Complete MINIX v3 Implementation**:
    -   Implement superblock reading/writing.
    -   Implement inode reading/writing.
    -   Implement full block mapping (indirect blocks).
    -   Implement directory operations (add/remove entries).
2.  **Unify Capabilities**:
    -   Ensure `minix3.c` passes `file->capability` to the buffer cache.
3.  **Stress Testing**:
    -   Directory explosion (creating many files).
    -   Large file read/write (triggering indirect blocks).
    -   Crash consistency (simulated via strict ordering and flush checks).
