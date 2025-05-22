# rcrs Configuration

The `rcrs` supervisor reads `drivers.conf` to determine which user space
drivers to launch. Each non-empty line describes one driver and its
arguments. Lines beginning with `#` are treated as comments and ignored.

Optional flags can follow the command. The current flags are:

* `--timeout=<ticks>` – number of clock ticks to wait for a driver to
  respond to a ping before restarting it. If omitted, a default timeout
  twice the ping interval is used.

Example `drivers.conf`:

```
# launch the keyboard service
kbdserv

# network driver with a custom timeout
pingdriver --timeout=60
```

The supervisor periodically prints a status report showing each driver's
process ID and how many times it has been restarted.
