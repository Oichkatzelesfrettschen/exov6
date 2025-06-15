Door IPC
========

The door IPC API provides a thin wrapper around simple call/return
semantics. A door is either local, invoking a handler directly, or
remote, forwarding messages through a capability endpoint.

Each door is represented by :c:type:`door_t` defined in ``door.h``.
Local doors call a user supplied handler while remote doors send the
message over an IPC capability and await the reply.

Typical usage::

    static void handler(zipc_msg_t *m) {
        m->w0++;
    }

    door_t d = door_create_local(handler);
    zipc_msg_t msg = {0};
    door_call(&d, &msg);

The ``door_server_loop`` function can be used to service incoming
requests for remote doors.

Asynchronous calls are also supported. A client can issue a message
without blocking and later collect the reply::

    door_call_async(&remote_door, &msg);
    door_recv(&remote_door, &msg);

Servers that implement custom dispatch logic may use ``door_recv`` and
``door_reply`` directly instead of ``door_server_loop``.

See the generated API documentation for details on each function.
