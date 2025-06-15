#pragma once
#include "ipc.h"
#include "caplib.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief Lightweight abstraction representing a synchronous door.
 *
 * A door is either local, in which case @c handler is invoked directly,
 * or remote and messages are forwarded through @c dest.
 */
typedef struct door {
  exo_cap dest;                     /**< Capability for remote invocation. */
  void (*handler)(zipc_msg_t *msg); /**< Local handler for incoming calls. */
  int is_local;                     /**< Non-zero if the door is local. */
} door_t;

/**
 * @brief Create a door that dispatches to a local handler.
 *
 * @param handler Function invoked when @ref door_call is used on this door.
 * @return Initialized door descriptor.
 */
door_t door_create_local(void (*handler)(zipc_msg_t *msg));

/**
 * @brief Create a door that forwards calls to a remote endpoint.
 *
 * @param dest Capability designating the remote endpoint.
 * @return Initialized door descriptor.
 */
door_t door_create_remote(exo_cap dest);

/**
 * @brief Invoke the door using the provided message.
 *
 * For local doors the handler is executed directly. For remote doors the
 * message is sent and a reply is awaited.
 *
 * @param d Door to invoke.
 * @param msg Message passed to the handler or remote endpoint.
 * @return 0 on success, -1 on failure.
 */
EXO_NODISCARD int door_call(door_t *d, zipc_msg_t *msg);

/**
 * @brief Service incoming requests on a remote door.
 *
 * This function blocks and repeatedly receives messages on @c d->dest,
 * dispatches them to @c d->handler and sends the response back.
 *
 * @param d Door descriptor with a valid handler.
 */
void door_server_loop(door_t *d);

/**
 * @brief Send a message without waiting for the reply.
 *
 * This is useful when issuing an asynchronous request to a remote
 * door.  The response can later be obtained with @ref door_recv.
 *
 * @param d   Door descriptor.
 * @param msg Message to transmit.
 * @return 0 on success, -1 on failure.
 */
EXO_NODISCARD int door_call_async(door_t *d, const zipc_msg_t *msg);

/**
 * @brief Receive a message or reply on a door.
 *
 * @param d   Door descriptor.
 * @param msg Output buffer for the received message.
 * @return 0 on success, -1 on failure.
 */
EXO_NODISCARD int door_recv(door_t *d, zipc_msg_t *msg);

/**
 * @brief Send a reply for a previously received request.
 *
 * Typically used by custom service loops in place of
 * @ref door_server_loop.
 *
 * @param d   Door descriptor.
 * @param msg Message to transmit.
 * @return 0 on success, -1 on failure.
 */
EXO_NODISCARD int door_reply(door_t *d, const zipc_msg_t *msg);

#ifdef __cplusplus
}
#endif
