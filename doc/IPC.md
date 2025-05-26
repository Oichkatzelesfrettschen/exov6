# Inter-Process Communication

Phoenix implements asynchronous message passing using per-process mailboxes. Each process owns a mailbox that queues incoming `zipc_msg_t` structures. Senders append to the destination mailbox while receivers dequeue from their own queue.

## Send and Receive

`exo_send(dest, buf, len)` copies a serialized message into the target mailbox. The call fails with `IPC_STATUS_AGAIN` when the mailbox is full. `exo_recv(src, buf, len)` blocks until a message arrives or the timeout expires. A timeout value of zero waits indefinitely.

## Timeouts

Timeouts are encoded as a `timeout_t` value passed to `sys_ipc`. When the wait period elapses without a message, the call returns `IPC_STATUS_TIMEOUT` and no data is copied.

## Status Codes

All IPC helpers return an `exo_ipc_status` value defined in
`engine/include/exo_ipc.h`.  The enumeration documents the possible
outcomes:

- `IPC_STATUS_SUCCESS` – operation completed normally.
- `IPC_STATUS_TIMEOUT` – receiver waited past the specified timeout.
- `IPC_STATUS_AGAIN`   – destination mailbox was full.
- `IPC_STATUS_BADDEST` – the destination thread or process id was invalid.

## Typed Channels and Capabilities

Typed channels declared with `CHAN_DECLARE` automatically encode and decode Cap'n Proto messages. Each typed channel stores a `msg_type_desc` describing the serialized size and relies on `chan_endpoint_send`/`chan_endpoint_recv` to enforce it. These helpers ultimately call `exo_send` and `exo_recv` using capabilities that reference endpoint mailboxes. Capabilities carry badges identifying the sender so higher level services can implement their own security policies.

## Debug Logging

Setting the `IPC_DEBUG` compile flag enables verbose mailbox tracing. The
`IPC_LOG()` macro prints details about each send and receive attempt along
with wait conditions and failures. Meson enables this with `-Dipc_debug=true`
while CMake uses `-DIPC_DEBUG=ON`. When the flag is unset the macros expand
to nothing.
