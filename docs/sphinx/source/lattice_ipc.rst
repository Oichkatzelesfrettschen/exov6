Lattice IPC
===========

.. contents::
   :local:

Overview
--------

The **Lattice IPC** layer provides an authenticated, encrypted,
capability-based interface for secure message passing.  Clients and
servers simply:

#.  Open a channel with ``:c:func:`lattice_connect````
#.  Exchange messages with ``:c:func:`lattice_send``` and
    ``:c:func:`lattice_recv```
#.  Close the channel with ``:c:func:`lattice_close```

Under the hood, each channel implements:

- **Post-quantum Kyber key exchange** on connect, deriving a shared secret
  stored in ``lattice_channel_t.key``.
- **Transparent XOR-stream encryption/decryption** of every payload.
- **Per-channel sequence counters** with HMAC-based authentication tokens,
  bumped atomically (``memory_order_relaxed``) on each send/receive.
- **Quaternion spinlock** protection of all mutable channel state,
  permitting safe recursive locking across threads.
- **Octonion session tokens** derived from the shared secret, stored in
  ``lattice_channel_t.token`` for application-level tagging.
- **DAG-based channel dependencies**, managed via
  ``lattice_channel_add_dep`` and ``lattice_channel_submit``, to prevent
  cyclic wait-for graphs in event-driven or cooperative systems.

Applications retain the same simple API but gain strong,
quantum-resistant confidentiality and integrity guarantees.

Basic Usage
-----------

.. code-block:: c

   #include "lattice_ipc.h"
   #include <stdio.h>
   #include <string.h>

   int
   main(void)
   {
       lattice_channel_t ch;
       int rc = lattice_connect(&ch, server_capability);
       if (rc != 0) {
           fprintf(stderr, "connect failed: %d\n", rc);
           return rc;
       }

       /* Send an encrypted message */
       const char *msg = "hello";
       rc = lattice_send(&ch, msg, strlen(msg));
       if (rc != (int)strlen(msg)) {
           fprintf(stderr, "send failed: %d\n", rc);
           lattice_close(&ch);
           return rc;
       }

       /* Receive and decrypt */
       char buf[64];
       size_t out_len = sizeof buf;
       rc = lattice_recv(&ch, buf, &out_len);
       if (rc == 0) {
           buf[out_len] = '\0';
           printf("Received: %s\n", buf);
       } else {
           fprintf(stderr, "recv failed or no message: %d\n", rc);
       }

       lattice_close(&ch);
       return 0;
   }

API Reference
-------------

.. c:function:: int lattice_connect(lattice_channel_t *chan, exo_cap cap)

   - Generates two ephemeral Kyber key-pairs, exchanges public keys
     via the capability channel.
   - Derives ``chan->key`` via KDF over the shared contributions.
   - Initializes ``chan->seq = 0``, ``chan->auth_token = HMAC(chan->key, 0)``.
   - Derives ``chan->token`` (octonion session marker) from ``chan->key``.
   - Initializes associated DAG node via ``dag_node_init(&chan->node)``.

.. c:function:: int lattice_send(lattice_channel_t *chan,
                                 const void *data,
                                 size_t len)

   - Locks ``chan->lock`` (quaternion spinlock).
   - Increments ``chan->seq`` (``memory_order_relaxed``), recomputes
     ``chan->auth_token``.
   - Derives an XOR keystream from ``chan->key || chan->seq``.
   - Encrypts payload in-place by XORing.
   - Appends ``chan->auth_token`` to ciphertext.
   - Queues or transmits the message.
   - Unlocks ``chan->lock``.
   - Returns number of bytes sent, or negative on error.

.. c:function:: int lattice_recv(lattice_channel_t *chan,
                                 void *buf,
                                 size_t *len_out)

   - Locks ``chan->lock``.
   - Retrieves next message from queue or network transport.
   - Verifies appended ``auth_token`` matches HMAC.
   - Derives XOR keystream from ``chan->key || message.seq``.
   - Decrypts payload by XORing, copies into ``buf``, sets ``*len_out``.
   - Increments ``chan->seq`` and updates ``chan->auth_token``.
   - Unlocks ``chan->lock``.
   - Returns 0 on success, negative or ``E_NO_MESSAGE`` if none.

.. c:function:: void lattice_close(lattice_channel_t *chan)

   - Closes the channel, zeroing ``chan->cap``, ``chan->seq``,
     ``chan->auth_token``, ``chan->token``.
   - Resets DAG node via ``dag_node_reset(&chan->node)``.

.. c:function:: int lattice_yield_to(const lattice_channel_t *chan)

   - Yields execution to the peer endpoint’s capability.
   - Invoked internally by the DAG scheduler when a node becomes runnable.

.. c:function:: int lattice_channel_add_dep(lattice_channel_t *parent,
                                            lattice_channel_t *child)

   - Adds a dependency edge in the channel DAG.
   - Returns 0 on success, -1 if adding would create a cycle.

.. c:function:: int lattice_channel_submit(lattice_channel_t *chan)

   - Marks ``chan`` as ready by submitting its DAG node to the scheduler.
   - Returns 0 on success.

Under the Hood
--------------

1. **lattice_connect()**  
   - Ephemeral keypairs for client/server.  
   - Capability-based public-key exchange.  
   - KDF to derive shared secret into ``chan->key``.  
   - Reset sequence counter and compute initial HMAC.  
   - Generate octonion session token from secret.  
   - Initialize DAG node for this channel.

2. **lattice_send() / lattice_recv()**  
   - Acquire quaternion spinlock via ``WITH_QLOCK(chan->lock)``.  
   - Bump ``chan->seq`` with ``memory_order_relaxed``.  
   - Derive per-message keystream from ``chan->key`` and the new sequence.  
   - XOR-encrypt or decrypt payload bytes.  
   - Verify or append HMAC authentication token.  
   - Enqueue or dequeues the message from the local graph.  
   - Release spinlock.

DAG Scheduler Integration
-------------------------

Lattice channels integrate with the DAG scheduler via each
``lattice_channel_t``’s embedded ``dag_node``.  Dependencies prevent
deadlock by guaranteeing acyclic wait-for graphs:

.. code-block:: c

   #include "lattice_ipc.h"
   #include "dag_sched.h"

   int
   main(void)
   {
       lattice_channel_t ch_send, ch_recv;
       dag_node_init(&ch_send.node);
       dag_node_init(&ch_recv.node);

       lattice_connect(&ch_send, peer_cap);
       lattice_connect(&ch_recv, peer_cap);

       lattice_channel_add_dep(&ch_send, &ch_recv);
       lattice_channel_submit(&ch_send);
       lattice_channel_submit(&ch_recv);

       dag_sched_run();
       return 0;
   }

When the scheduler runs, each node yields via
``lattice_yield_to(&node->chan)``, transmitting control across
the octonion-protected channel.

Concurrency
-----------

All operations on ``lattice_channel_t`` mutate shared state.  A
quaternion spinlock (``WITH_QLOCK(ch.lock)``) guards each critical
section.  Sequence counters use ``memory_order_relaxed``, relying on
the spinlock for necessary happens-before ordering.  DAG dependencies
are enforced at submission time, rejecting cycles to guarantee progress.
