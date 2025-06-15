Lattice IPC
===========

The **Lattice IPC** layer provides a simple, capability-based interface for authenticated, encrypted message passing. Applications open a channel with `lattice_connect()`, then exchange messages with `lattice_send()` and `lattice_recv()`, and finally close it with `lattice_close()`.  

Under the hood, each channel now performs:
1. **Post-quantum Kyber key exchange** on connect, storing the negotiated secret in `lattice_channel_t.key`.  
2. **Transparent XOR-stream encryption/decryption** of every payload.  
3. **Per-channel sequence counters** and authentication tokens, incremented atomically with relaxed semantics on each send/receive.
4. **Quaternion spinlock** protection of all mutable channel state, allowing safe recursive locking across threads.

Applications continue to use the same simple API but gain strong, quantum-resistant confidentiality and integrity guarantees.

Basic usage example::

```c
lattice_channel_t ch;
if (lattice_connect(&ch, server_cap) == 0) {
  // Channel.key now holds the shared Kyber-derived secret
  lattice_send(&ch, "hello", 5); // encrypts + updates sequence counter
  char buf[16];
  lattice_recv(&ch, buf, sizeof(buf)); // decrypts + updates sequence counter
  lattice_close(&ch);
}
— underneath :

    lattice_connect(&ch, cap)
• generates two Kyber key
    -
    pairs,
    exchanges public keys,
    derives ch.key via establish_secret(…).
• initializes ch.seq = 0,
               ch.auth_token = HMAC(ch.key, seq)
                                   .

                               lattice_send(&ch, data, len)
• locks ch.lock(quaternion spinlock),
               increments ch.seq with relaxed atomics, recomputes ch.auth_token.
• XOR - encrypts data with a keystream derived from ch.key || ch.seq,
               appends ch.auth_token,
               and queues or transmits.
• unlocks ch.lock.

                             lattice_recv(&ch, buf, buflen)
• locks ch.lock,
               checks and decrypts incoming payload, verifies auth_token,
               increments ch.seq with relaxed atomics.
• copies plaintext into buf, unlocks ch.lock.