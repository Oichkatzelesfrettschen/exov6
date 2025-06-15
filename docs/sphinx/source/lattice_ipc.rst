Lattice IPC
===========

The lattice IPC layer provides a simple capability-based interface for
message passing. Applications open a channel using ``lattice_connect``
and then exchange messages with ``lattice_send`` and ``lattice_recv``.
The following snippet illustrates a basic workflow::

    lattice_channel_t ch;
    if (lattice_connect(&ch, server_cap) == 0) {
        lattice_send(&ch, "hello", 5);
        char buf[16];
        lattice_recv(&ch, buf, sizeof(buf));
        lattice_close(&ch);
    }

On connection, ``lattice_connect`` now performs a lightweight
post-quantum key exchange based on a Kyber-style exchange.  The
negotiated secret is stored in ``lattice_channel_t.key`` and
is transparently used by ``lattice_send`` and ``lattice_recv`` to
encrypt and decrypt payloads via a simple XOR stream.

Applications continue to call the API as before but now benefit from
authenticated encrypted transport.
