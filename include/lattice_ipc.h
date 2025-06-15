#pragma once

#include <stddef.h>
#include <stdint.h>

#include "exo_ipc.h"
#include "lattice_types.h"
#include "../kernel/quaternion_spinlock.h"
#include "octonion.h"
#include "dag.h"

/**
 * @brief Lattice IPC channel descriptor.
 *
 * Encapsulates an authenticated, encrypted channel with
 * post-quantum secrecy, octonion session tagging, and
 * DAG-driven scheduling.  All mutable state is protected
 * by a quaternion spinlock, and sequence counters use
 * relaxed _Atomic updates.
 */
typedef struct lattice_channel {
    quaternion_spinlock_t lock; /**< Guards all mutable channel state. */
    exo_cap               cap;  /**< Capability handle for peer comm. */
    _Atomic uint64_t      seq;  /**< Sequence counter for messages. */
    lattice_sig_t         key;  /**< HMAC authentication token. */
    octonion_t            token;/**< Octonion session token. */
    struct dag_node       dag;  /**< Embedded DAG node for deps. */
} lattice_channel_t;

/**
 * @brief Establish a secure channel over a capability.
 *
 * Performs post-quantum key exchange (Kyber stub), resets
 * sequence/auth state, derives the octonion token, and
 * initializes the DAG node.
 *
 * @param chan  Pointer to a channel struct (non-NULL).
 * @param dest  Remote endpoint capability.
 * @return      0 on success, negative on failure.
 */
[[nodiscard]] int
lattice_connect(lattice_channel_t *chan,
                exo_cap dest);

/**
 * @brief Send an encrypted, authenticated message.
 *
 * Under lock, increments the sequence counter (relaxed),
 * recomputes HMAC, encrypts via XOR-stream, and transmits.
 *
 * @param chan  Initialized channel (lattice_connect done).
 * @param buf   Pointer to data to send.
 * @param len   Data length in bytes.
 * @return      Bytes sent on success, negative on error.
 */
[[nodiscard]] int
lattice_send(lattice_channel_t *chan,
             const void *buf,
             size_t len);

/**
 * @brief Receive and decrypt an authenticated message.
 *
 * Under lock, retrieves the next message, verifies HMAC,
 * XOR-decrypts, increments sequence, and copies into buf.
 *
 * @param chan     Initialized channel.
 * @param buf      Buffer to receive into.
 * @param len      Maximum buffer size.
 * @return         Bytes received on success,
 *                 negative or E_NO_MESSAGE otherwise.
 */
[[nodiscard]] int
lattice_recv(lattice_channel_t *chan,
             void *buf,
             size_t len);

/**
 * @brief Close and reset a channel.
 *
 * Zeros sequence, auth token, octonion token,
 * and resets the DAG node under lock.
 *
 * @param chan  Channel to close (non-NULL).
 */
void
lattice_close(lattice_channel_t *chan);

/**
 * @brief Yield execution to the channel’s peer.
 *
 * Uses the stored capability to transfer control.
 *
 * @param chan  Channel describing destination.
 * @return      0 on success, negative on error.
 */
[[nodiscard]] int
lattice_yield_to(const lattice_channel_t *chan);

/**
 * @brief Add a DAG dependency between two channels.
 *
 * Prevents cycles: returns an error if adding
 * the edge would introduce a cycle.
 *
 * @param parent  Channel that must complete first.
 * @param child   Channel that depends on parent.
 * @return        0 on success, negative on cycle or error.
 */
[[nodiscard]] int
lattice_channel_add_dep(lattice_channel_t *parent,
                        lattice_channel_t *child);

/**
 * @brief Submit a channel’s DAG node to the scheduler.
 *
 * Marks the channel as ready; the scheduler will
 * invoke lattice_yield_to() when running its node.
 *
 * @param chan  Channel to submit (non-NULL).
 * @return      0 on success, negative on error.
 */
[[nodiscard]] int
lattice_channel_submit(lattice_channel_t *chan);
