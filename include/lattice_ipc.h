#pragma once
#include "exo_ipc.h"
#include "lattice_types.h"
#include "../kernel/quaternion_spinlock.h"
#include <stddef.h>
#include <stdint.h>

/**
 * @brief Lattice-based IPC channel descriptor.
 *
 * Access to mutable fields is serialized using a quaternion spinlock.
 * The sequence counter is incremented atomically on successful
 * send and receive operations.
 */
typedef struct lattice_channel {
  quaternion_spinlock_t lock; /**< Protects channel state. */
  exo_cap cap;                /**< Capability handle for peer communication. */
  _Atomic uint64_t seq;       /**< Sequence number for messages. */
  octonion_t key;             /**< Authentication token. */
} lattice_channel_t;

/**
 * @brief Establish a connection to a remote capability.
 *
 * @param chan Channel structure to initialize.
 * @param dest Capability of the remote endpoint.
 * @return 0 on success, negative value on failure.
 */
[[nodiscard]] int lattice_connect(lattice_channel_t *chan, exo_cap dest);

/**
 * @brief Send a message over the channel.
 *
 * @param chan Channel previously initialized with lattice_connect.
 * @param buf  Data buffer to transmit.
 * @param len  Number of bytes to send.
 * @return 0 on success, negative value on failure.
 *
 * The sequence counter is updated atomically while the quaternion
 * lock guards the channel state.
 */
[[nodiscard]] int lattice_send(lattice_channel_t *chan, const void *buf,
                               size_t len);

/**
 * @brief Receive a message from the channel.
 *
 * @param chan Channel previously initialized with lattice_connect.
 * @param buf  Buffer to store received data.
 * @param len  Maximum number of bytes to read.
 * @return Number of bytes received on success, negative value on failure.
 *
 * The call acquires the quaternion lock and increments the sequence
 * counter atomically on success.
 */
[[nodiscard]] int lattice_recv(lattice_channel_t *chan, void *buf, size_t len);

/**
 * @brief Close a previously opened channel.
 *
 * @param chan Channel to close.
 *
 * The operation resets the sequence counter and authentication token
 * under the channel lock.
 */
void lattice_close(lattice_channel_t *chan);

/**
 * @brief Yield the CPU to the remote endpoint if possible.
 *
 * @param chan Channel describing the destination.
 * @return 0 on success, negative value on failure.
 */
[[nodiscard]] int lattice_yield_to(const lattice_channel_t *chan);
