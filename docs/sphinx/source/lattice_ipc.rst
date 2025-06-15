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

Each channel maintains a sequence counter and authentication token.
Mutable channel state is protected by a *quaternion spinlock* allowing
recursive locking. The sequence counter increments atomically with
each successful send or receive.
