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

   .. code-block:: c

      lattice_channel_t ch;
      if (lattice_connect(&ch, server_cap) == 0) {
          /* Channel.key now holds the shared Kyber-derived secret */
          lattice_send(&ch, "hello", 5);          /* encrypt + update sequence counter */
          char buf[16];
          lattice_recv(&ch, buf, sizeof(buf));    /* decrypt + update sequence counter */
          lattice_close(&ch);
      }

Below is the underlying process:

lattice_connect(&ch, cap)
- generates two Kyber key-pairs, exchanges public keys, derives ch.key via establish_secret(…)
- initializes ch.seq = 0, ch.auth_token = HMAC(ch.key, seq)

lattice_send(&ch, data, len)
- locks ch.lock (quaternion spinlock), increments ch.seq, recomputes ch.auth_token
- XOR-encrypts data with a keystream derived from ch.key || ch.seq, appends ch.auth_token, and queues or transmits
- unlocks ch.lock

lattice_recv(&ch, buf, buflen)
- locks ch.lock, checks and decrypts incoming payload, verifies auth_token, increments ch.seq
- copies plaintext into buf, unlocks ch.lock

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
