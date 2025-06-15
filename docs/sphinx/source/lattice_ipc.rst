Lattice IPC
===========

The **Lattice IPC** layer provides an authenticated, encrypted,
capability‐based interface for secure message passing.  Applications
follow a simple three‐step workflow:

#.  Open a channel with ``:c:func:`lattice_connect````
#.  Exchange messages with ``:c:func:`lattice_send``` and
    ``:c:func:`lattice_recv```
#.  Close the channel with ``:c:func:`lattice_close```

Under the hood, each channel performs:

- **Post-quantum Kyber key exchange** on connect, storing the negotiated
  secret in ``lattice_channel_t.key``.
- **Transparent XOR-stream encryption/decryption** of every payload.
- **Per-channel sequence counters** and authentication tokens, incremented
  atomically (relaxed) on each send/receive.
- **Quaternion spinlock** protection of all mutable channel state, allowing
  safe recursive locking across threads.
- **Octonion session tokens** derived from the negotiated secret, stored in
  ``lattice_channel_t.token``.
- **DAG-based channel management** through ``lattice_channel_add_dep`` and
  ``lattice_channel_submit`` which prevent cyclic wait-for graphs.

Applications continue to use the same simple API but gain strong,
quantum-resistant confidentiality and integrity guarantees.

Basic Usage Example
-------------------

.. code-block:: c

   #include "lattice_ipc.h"
   #include <stdio.h>
   #include <string.h>

   int main(void) {
       lattice_channel_t ch;
       int rc = lattice_connect(&ch, server_capability);
       if (rc != 0) {
           fprintf(stderr, "connect failed: %d\n", rc);
           return rc;
       }

       /* Channel.key now holds the shared Kyber-derived secret */
       const char *msg = "hello";
       rc = lattice_send(&ch, msg, strlen(msg));
       if (rc != 0) {
           fprintf(stderr, "send failed: %d\n", rc);
           lattice_close(&ch);
           return rc;
       }

       char buf[64];
       size_t out_len = sizeof(buf);
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

API Details
-----------

``lattice_connect(&ch, cap)``
  - Generates two Kyber key‐pairs, exchanges public keys with the peer.
  - Derives ``ch.key`` via ``establish_secret(ch.key, peer_pub)``.
  - Initializes ``ch.seq = 0`` and computes initial
    ``ch.auth_token = HMAC(ch.key, ch.seq)``.
  - Derives ``ch.token`` from ``ch.key`` as an octonion session marker.
  - Initializes ``ch.dag`` for DAG scheduling with ``dag_node_init``.

``lattice_send(&ch, data, len)``
  - Locks ``ch.lock`` (quaternion spinlock).
  - Increments ``ch.seq`` (relaxed atomic) and recomputes
    ``ch.auth_token``.
  - Derives an XOR keystream from ``ch.key || ch.seq``.
  - Encrypts payload in-place by XORing with the keystream.
  - Appends ``ch.auth_token`` to the ciphertext.
  - Queues or transmits the message.
  - Unlocks ``ch.lock``.

``lattice_recv(&ch, buf, &buflen)``
  - Locks ``ch.lock``.
  - Retrieves next message from queue or network transport.
  - Verifies appended ``auth_token``.
  - Derives XOR keystream from ``ch.key || message.seq``.
  - Decrypts payload in-place by XORing.
  - Copies plaintext into ``buf`` and sets ``*buflen``.
  - Increments ``ch.seq`` and updates ``ch.auth_token``.
  - Unlocks ``ch.lock``.

``lattice_channel_add_dep(parent, child)``
  - Adds a dependency edge in the wait-for DAG.
  - Fails with ``-1`` if the edge would create a cycle.

``lattice_channel_submit(chan)``
  - Marks ``chan`` as ready by submitting its DAG node.

Concurrency
-----------

All operations on ``lattice_channel_t`` mutate shared state.  The
quaternion spinlock, used via the macro ``WITH_QLOCK(ch.lock)``, guards
every critical section.  Sequence counters use ``memory_order_relaxed``
since the spinlock provides the necessary happens-before ordering
without extra barriers.
Channel dependencies are expressed using a DAG; submissions that would
introduce cycles are rejected to guarantee progress.
