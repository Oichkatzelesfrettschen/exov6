/**
 * @file fs_protocol.h
 * @brief File Server IPC Protocol (Phase 9.5)
 *
 * This header defines the message format for client-server
 * file system communication. Clients send requests via IPC,
 * the file server processes them and replies.
 *
 * Message Format:
 *   w0: Request type (FS_REQ_*)
 *   w1: Request-specific data (file descriptor, offset, etc.)
 *   w2: Request-specific data (size, flags, etc.)
 *
 * Response Format:
 *   w0: Result code (0 = success, negative = error)
 *   w1: Response-specific data
 *   w2: Response-specific data
 */

#ifndef FS_PROTOCOL_H
#define FS_PROTOCOL_H

#include <stdint.h>

// ═══════════════════════════════════════════════════════════════════════════
// File Server PID (Well-Known Service)
// ═══════════════════════════════════════════════════════════════════════════

#define FS_SERVER_PID   2   // File server is always PID 2

// ═══════════════════════════════════════════════════════════════════════════
// Request Types
// ═══════════════════════════════════════════════════════════════════════════

#define FS_REQ_OPEN     1   // Open a file
#define FS_REQ_CLOSE    2   // Close a file
#define FS_REQ_READ     3   // Read from file
#define FS_REQ_WRITE    4   // Write to file
#define FS_REQ_STAT     5   // Get file status
#define FS_REQ_READDIR  6   // Read directory entry
#define FS_REQ_MKDIR    7   // Create directory
#define FS_REQ_UNLINK   8   // Remove file
#define FS_REQ_PING     99  // Test connectivity

// ═══════════════════════════════════════════════════════════════════════════
// Response Codes
// ═══════════════════════════════════════════════════════════════════════════

#define FS_OK           0   // Success
#define FS_ERR_NOTFOUND -1  // File not found
#define FS_ERR_PERM     -2  // Permission denied
#define FS_ERR_ISDIR    -3  // Is a directory
#define FS_ERR_NOTDIR   -4  // Not a directory
#define FS_ERR_NOSPC    -5  // No space left
#define FS_ERR_IO       -6  // I/O error
#define FS_ERR_INVAL    -7  // Invalid argument
#define FS_ERR_NFILE    -8  // Too many open files

// ═══════════════════════════════════════════════════════════════════════════
// Open Flags
// ═══════════════════════════════════════════════════════════════════════════

#define FS_O_RDONLY     0x0001
#define FS_O_WRONLY     0x0002
#define FS_O_RDWR       0x0003
#define FS_O_CREATE     0x0100
#define FS_O_TRUNC      0x0200

// ═══════════════════════════════════════════════════════════════════════════
// Message Structures (packed for IPC transfer)
// ═══════════════════════════════════════════════════════════════════════════

/**
 * FS_REQ_OPEN request
 * w0: FS_REQ_OPEN
 * w1: Pointer to path string (in shared memory)
 * w2: Open flags (FS_O_*)
 *
 * Response:
 * w0: File descriptor (>= 0) or error (< 0)
 */

/**
 * FS_REQ_READ request
 * w0: FS_REQ_READ
 * w1: File descriptor
 * w2: (size << 32) | offset
 *
 * Response:
 * w0: Bytes read (>= 0) or error (< 0)
 * w1: Pointer to data (in shared buffer)
 */

/**
 * FS_REQ_READDIR request
 * w0: FS_REQ_READDIR
 * w1: Directory file descriptor
 * w2: Entry index
 *
 * Response:
 * w0: 1 if entry valid, 0 if end, < 0 on error
 * w1: Inode number
 * w2: Pointer to name (in shared buffer)
 */

/**
 * FS_REQ_STAT request
 * w0: FS_REQ_STAT
 * w1: File descriptor
 * w2: 0
 *
 * Response:
 * w0: 0 on success, < 0 on error
 * w1: File type (1=dir, 2=file, 3=dev)
 * w2: File size
 */

// ═══════════════════════════════════════════════════════════════════════════
// Shared Buffer Protocol
// ═══════════════════════════════════════════════════════════════════════════

/**
 * For bulk data transfer (file content, paths), clients allocate
 * a shared page and map it into both client and server address space.
 *
 * Simple approach for Phase 9:
 *   - Client allocates page at known VA (e.g., 0x50000000)
 *   - Client grants page to server via sys_page_map()
 *   - Server reads/writes data at that address
 *   - Path strings placed at start of buffer
 *   - Read data returned in same buffer
 */

#define FS_SHARED_BUF_VA    0x50000000ULL
#define FS_SHARED_BUF_SIZE  4096

// ═══════════════════════════════════════════════════════════════════════════
// Helper Macros
// ═══════════════════════════════════════════════════════════════════════════

// Pack size and offset into w2
#define FS_PACK_SIZE_OFF(size, off) (((uint64_t)(size) << 32) | (uint64_t)(off))
#define FS_UNPACK_SIZE(w2) ((uint32_t)((w2) >> 32))
#define FS_UNPACK_OFF(w2)  ((uint32_t)((w2) & 0xFFFFFFFF))

#endif // FS_PROTOCOL_H
