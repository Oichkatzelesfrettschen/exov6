# STREAMS Flow Control

The STREAMS prototype uses a PID controller to throttle message flow.
The tuning constants are exposed via procfs files under `/proc/streams/fc/`:

* `/proc/streams/fc/Kp`
* `/proc/streams/fc/Ki`
* `/proc/streams/fc/Kd`

Each file holds a floating point value. The kernel reads these values at
start-up and applies changes whenever a new value is written.  The
helpers in `flow_pid.py` wrap this interface and honour the `FLOW_PID_DIR`
environment variable, making it easy to experiment with different
parameters during testing.
