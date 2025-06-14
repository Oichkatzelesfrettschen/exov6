#pragma once
#include "exo_ipc.h"
#include "lattice_types.h"
#include <stddef.h>
#include <stdint.h>

/**
 * @brief Lattice-based IPC channel descriptor.
 */
typedef struct lattice_channel {
    exo_cap        cap; /**< Capability handle for peer communication. */
    uint64_t       seq; /**< Sequence number for messages. */
    lattice_sig_t  key; /**< Authentication token. */
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
 */
[[nodiscard]] int lattice_send(lattice_channel_t *chan, const void *buf, size_t len);

/**
 * @brief Receive a message from the channel.
 *
 * @param chan Channel previously initialized with lattice_connect.
 * @param buf  Buffer to store received data.
 * @param len  Maximum number of bytes to read.
 * @return Number of bytes received on success, negative value on failure.
 */
[[nodiscard]] int lattice_recv(lattice_channel_t *chan, void *buf, size_t len);

/**
 * @brief Close a previously opened channel.
 *
 * @param chan Channel to close.
 */
void lattice_close(lattice_channel_t *chan);

/**
 * @brief Yield the CPU to the remote endpoint if possible.
 *
 * @param chan Channel describing the destination.
 * @return 0 on success, negative value on failure.
 */
[[nodiscard]] int lattice_yield_to(const lattice_channel_t *chan);


