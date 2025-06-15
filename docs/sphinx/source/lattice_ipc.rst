Lattice IPC
===========

The **Lattice IPC** layer provides a simple, capability-based interface for authenticated, encrypted message passing. Applications open a channel with `lattice_connect()`, then exchange messages with `lattice_send()` and `lattice_recv()`, and finally close it with `lattice_close()`.  

Under the hood, each channel now performs:

#. **Post‑quantum Kyber-style key exchange** on connect, placing the negotiated
   secret into ``lattice_channel_t.key``.
#. **Transparent XOR-stream encryption and decryption** of every payload.
#. **Per-channel sequence counters** with authentication tokens, bumped
   atomically on each send/receive.
#. **Quaternion spinlock** protection of all mutable channel state, permitting
   safe recursive locking across threads.

Applications continue to use the same simple API but gain strong, quantum-resistant confidentiality and integrity guarantees.

Basic usage example::

```c
lattice_channel_t ch;
if (lattice_connect(&ch, server_cap) == 0) {
    // Channel.key now holds the shared Kyber-derived secret
    lattice_send(&ch, "hello", 5);          // encrypts + updates sequence counter
    char buf[16];
    lattice_recv(&ch, buf, sizeof(buf));    // decrypts + updates sequence counter
    lattice_close(&ch);
}
The helpers work as follows:

``lattice_connect``
  Generates a random key pair, exchanges the public key with the peer and
  derives ``ch.key`` from both contributions using ``libos_kdf_derive``.  The
  sequence counter is then reset to zero.

``lattice_send``/``lattice_recv``
  Lock the channel, XOR-encrypt or decrypt the payload with a stream derived
  from ``ch.key`` and the current sequence value, update the sequence counter and
  release the lock.
