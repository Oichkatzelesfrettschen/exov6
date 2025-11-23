/**
 * @file pipe.h
 * @brief ExoV6 Pipe API (Phase 11.3)
 *
 * User-space pipes using shared memory ring buffers.
 */

#ifndef PIPE_H
#define PIPE_H

#include <stdint.h>

/**
 * Create a new pipe
 * @return Pipe ID (>= 0) or -1 on error
 */
int pipe_create(void);

/**
 * Read from pipe
 * @param pipe_id Pipe identifier
 * @param buf Buffer to read into
 * @param n Maximum bytes to read
 * @return Bytes read, 0 on EOF, -1 on error
 */
int pipe_read(int pipe_id, void *buf, int n);

/**
 * Write to pipe
 * @param pipe_id Pipe identifier
 * @param buf Data to write
 * @param n Bytes to write
 * @return Bytes written, -1 on broken pipe
 */
int pipe_write(int pipe_id, const void *buf, int n);

/**
 * Close read end of pipe
 * Signals broken pipe to writer.
 */
void pipe_close_read(int pipe_id);

/**
 * Close write end of pipe
 * Signals EOF to reader.
 */
void pipe_close_write(int pipe_id);

/**
 * Get physical address of pipe buffer
 * Used by spawn() to map into child process.
 */
uint64_t pipe_get_phys(int pipe_id);

#endif /* PIPE_H */
