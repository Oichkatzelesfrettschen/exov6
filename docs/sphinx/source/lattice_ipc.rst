Lattice IPC
===========

.. contents::
   :local:

Overview
--------

The **Lattice IPC** layer provides an authenticated, encrypted,
capability‐based interface for secure message passing.  Applications
follow a simple three‐step workflow:

#.  Open a channel with ``:c:func:`lattice_connect````
#.  Exchange messages with ``:c:func:`lattice_send``` and
    ``:c:func:`lattice_recv```
#.  Close the channel with ``:c:func:`lattice_close```

Under the hood, each channel implements:

- **Post-quantum Kyber key exchange** on connect, deriving a shared secret
  and storing it in ``lattice_channel_t.key``.
- **Transparent XOR-stream encryption/decryption** of every payload.
- **Per-channel sequence counters** and authentication tokens,
  incremented atomically (relaxed) on each send/receive.
- **Quaternion spinlock** protection of all mutable channel state,
  permitting safe recursive locking across threads.

Applications retain the same API but gain quantum‐resistant
confidentiality and integrity guarantees.

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

       /* Channel.key now holds the shared Kyber-derived secret */
       const char *msg = "hello";
       rc = lattice_send(&ch, msg, strlen(msg));
       if (rc != (int)strlen(msg)) {
           fprintf(stderr, "send failed: %d\n", rc);
           lattice_close(&ch);
           return rc;
       }

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

   - Generates two Kyber key‐pairs, exchanges public keys with the peer.
   - Derives ``chan->key`` via ``establish_secret``.
   - Initializes ``chan->seq = 0`` and computes initial
     ``chan->auth_token = HMAC(chan->key, chan->seq)``.

.. c:function:: int lattice_send(lattice_channel_t *chan,
                                 const void *data,
                                 size_t len)

   - Locks ``chan->lock`` (quaternion spinlock).
   - Increments ``chan->seq`` (relaxed atomic) and recomputes
     ``chan->auth_token``.
   - Derives an XOR keystream from ``chan->key || chan->seq``.
   - Encrypts payload in-place by XORing with the keystream.
   - Appends ``chan->auth_token`` and queues or transmits.
   - Unlocks ``chan->lock``.

.. c:function:: int lattice_recv(lattice_channel_t *chan,
                                 void *buf,
                                 size_t *len_out)

   - Locks ``chan->lock``.
   - Retrieves next message from queue or network transport.
   - Verifies appended ``auth_token``.
   - Derives XOR keystream from ``chan->key || message.seq``.
   - Decrypts payload in-place by XORing.
   - Copies plaintext into ``buf``, sets ``*len_out``.
   - Increments ``chan->seq`` and updates ``chan->auth_token``.
   - Unlocks ``chan->lock``.

.. c:function:: void lattice_close(lattice_channel_t *chan)

   - Closes the channel, zeroing out ``chan->cap``, ``chan->seq`` and
     wiping ``chan->key``.

.. c:function:: int lattice_yield_to(const lattice_channel_t *chan)

   - Yields execution to the peer endpoint associated with ``chan``.
   - Internally invoked by the DAG scheduler (see below).

Under the Hood
--------------

1. **lattice_connect()**  
   - Generates ephemeral keypairs on both ends.  
   - Exchanges public keys over the capability channel.  
   - Derives the shared secret via KDF into ``chan->key``.  
   - Resets ``chan->seq = 0`` and computes initial HMAC.

2. **lattice_send() / lattice_recv()**  
   - Acquire quaternion spinlock via ``WITH_QLOCK(chan->lock)``.  
   - Bump sequence counter with ``memory_order_relaxed``.  
   - Derive a per-message keystream from ``chan->key || seq``.  
   - XOR‐encrypt or decrypt payload bytes.  
   - Verify or append authentication token.  
   - Enqueue or dequeue the message.  
   - Release spinlock.

DAG Scheduler Integration
-------------------------

The Lattice IPC layer integrates seamlessly with the DAG scheduler.
Tasks are represented by ``dag_node`` structures; each can be bound
to a channel.  When the scheduler activates a node, it calls
``lattice_yield_to()`` for that node’s channel.

Example:

.. code-block:: c

   #include "lattice_ipc.h"
   #include "dag_sched.h"

   int
   main(void)
   {
       lattice_channel_t ch;
       struct dag_node send_node, recv_node;

       lattice_connect(&ch, peer_cap);
       dag_node_init(&send_node);
       dag_node_init(&recv_node);

       dag_node_set_channel(&send_node, &ch);
       dag_node_set_channel(&recv_node, &ch);
       dag_node_add_dep(&send_node, &recv_node);

       dag_sched_submit(&send_node);
       dag_sched_submit(&recv_node);

       dag_sched_run();
       return 0;
   }

When the DAG scheduler runs, ``send_node`` and ``recv_node`` execute
in dependency order, yielding control via the octonion‐backed channel.

Concurrency
-----------

All operations on ``lattice_channel_t`` mutate shared state.  A
quaternion spinlock, via the macro ``WITH_QLOCK(ch.lock)``, guards
each critical section.  Sequence counters use
``memory_order_relaxed``, relying on the spinlock for the necessary
happens‐before ordering without extra barriers.
