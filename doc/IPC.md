# IPC API

The Phoenix IPC subsystem exposes two primary calls:

```c
enum exo_ipc_status exo_send(exo_cap dest, const void *buf, uint64_t len);
enum exo_ipc_status exo_recv(exo_cap src, void *buf, uint64_t len);
```

The return type `exo_ipc_status` indicates success or the reason for
failure:

```c
enum exo_ipc_status {
    EXO_IPC_OK = 0,
    EXO_IPC_TIMEOUT = -1,
    EXO_IPC_INVALID = -2,
    EXO_IPC_OVERFLOW = -3,
};
```

`EXO_IPC_OK` means the operation completed successfully. All other
values represent error conditions.
