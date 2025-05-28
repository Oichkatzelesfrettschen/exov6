# STREAMS Flow Control

Phoenix uses a simple PID controller to regulate message flow through the STREAMS pipeline. The three constants **Kp**, **Ki** and **Kd** tune the controller and can be adjusted at runtime via procfs entries.

## /proc/streams/fc/Kp
The proportional constant. Larger values cause the controller to react more strongly to differences between the desired and observed throughput.

## /proc/streams/fc/Ki
The integral constant accumulates past errors to eliminate steady state drift. A higher value speeds up convergence but may introduce overshoot.

## /proc/streams/fc/Kd
The derivative constant dampens oscillations by responding to the rate of change. Increasing **Kd** smooths out sudden spikes at the cost of slower response.

Missing or malformed procfs files fall back to built-in defaults. Writing a new value immediately updates the live constant. The helpers in `flow_pid.py` wrap these files:

```python
import flow_pid

flow_pid.flow_pid_init()
flow_pid.set_kp(1.2)
flow_pid.set_ki(0.05)
flow_pid.set_kd(0.01)
```

### Example Program
`examples/demos/fc_tuning_demo.py` demonstrates dynamic tuning. When run it prints the initial constants and then updates them:

```sh
$ python3 examples/demos/fc_tuning_demo.py
Initial constants: {'Kp': 1.0, 'Ki': 0.0, 'Kd': 0.0}
Updated constants: {'Kp': 1.5, 'Ki': 0.1, 'Kd': 0.05}
```

Set the `FLOW_PID_DIR` environment variable to a temporary directory when testing without a real `/proc` entry.
