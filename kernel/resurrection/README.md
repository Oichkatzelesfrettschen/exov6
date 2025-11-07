# ExoV6 Resurrection Server

## Overview

The Resurrection Server (RS) is a cleanroom implementation of MINIX3-style process resurrection, redesigned for exokernel architecture with capability-based resource management.

## Design Philosophy

Unlike MINIX3's monolithic Reincarnation Server, ExoV6's implementation integrates directly with the exokernel capability system:

- **Capability-Based**: All resource tracking uses exokernel capabilities
- **Zero-Copy State**: Direct memory mapping for state preservation
- **LibOS Integration**: Policy decisions delegated to library operating systems
- **Fault Isolation**: Crashed services don't affect the resurrection infrastructure

## Key Features

### Automatic Process Resurrection
- Configurable restart policies (never, once, always, on-failure)
- Rate limiting to prevent restart storms
- Dependency-aware resurrection ordering

### State Preservation
- Capability snapshot and restoration
- Resource limit enforcement
- Environment preservation

### Service Dependencies
- Topological dependency resolution
- Automatic dependency startup
- Circular dependency detection

## Usage

### Registering a Service

```c
uint32_t service_id;
int result = rs_register_service(
    "file_server",              // Service name
    "/usr/sbin/file_server",    // Executable path
    RS_POLICY_ALWAYS,           // Always restart on crash
    &service_id                 // Output: assigned ID
);
```

### Starting a Service

```c
rs_start_service(service_id);
```

### Handling Crashes

The kernel's exception handler calls:

```c
rs_notify_crash(pid, exit_status);
```

The resurrection server then:
1. Checks the restart policy
2. Verifies rate limits
3. Starts dependencies if needed
4. Restores capability state
5. Re-executes the service

## Statistics

Query resurrection statistics:

```c
rs_service_t info;
rs_get_service_info(service_id, &info);

printf("Service: %s\n", info.name);
printf("State: %d\n", info.state);
printf("Restarts: %d\n", info.restart_count);
printf("Last crash: %llu ms ago\n", 
       rs_get_time_ms() - info.crash_time);
```

## Configuration

Resurrection parameters (in `reincarnation_server.h`):

- `RS_MAX_SERVICES`: Maximum supervised services (default: 64)
- `RS_MAX_RESTARTS`: Maximum restarts in time window (default: 5)
- `RS_RESTART_WINDOW`: Time window for rate limiting (default: 60000ms)
- `RS_MAX_DEPS`: Maximum dependencies per service (default: 16)

## Integration with ExoV6

### Capability System
The RS preserves and restores:
- Memory capabilities
- Device capabilities
- IPC endpoint capabilities
- Page table capabilities

### Process Model
Services are standard ExoV6 processes with:
- Standard capability environment
- LibOS integration
- Resource accounting

### Recovery Strategy
1. **Detection**: Exception handler or watchdog
2. **Notification**: Call `rs_notify_crash()`
3. **Policy Check**: Evaluate restart policy and limits
4. **Dependency Start**: Ensure dependencies are running
5. **State Restore**: Restore capability snapshot
6. **Execution**: Re-run the executable
7. **Monitoring**: Track for subsequent crashes

## Comparison with MINIX3

| Feature | MINIX3 RS | ExoV6 RS |
|---------|-----------|----------|
| Architecture | Monolithic server | Exokernel-integrated |
| State Mgmt | Message-based | Capability-based |
| Resource Track | Table-driven | Capability-driven |
| Isolation | Process boundaries | Capability domains |
| Performance | IPC overhead | Zero-copy capabilities |

## Future Enhancements

- [ ] Checkpoint/restore integration
- [ ] Live update support (update without restart)
- [ ] Predictive resurrection (restart before crash)
- [ ] Distributed resurrection (multi-node)
- [ ] Resource quota enforcement
- [ ] Forensic logging and analysis

## References

- MINIX3 Reincarnation Server design
- Exokernel architecture (MIT Exokernel papers)
- Capability-based operating systems
- Fault-tolerant system design
