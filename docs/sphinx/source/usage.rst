Usage
=====

This project consists primarily of C sources. Refer to the API
documentation generated from the code for usage details.

The :c:func:`dag_sched_submit` function rejects submissions forming
cyclic dependencies. When a cycle is detected it returns ``-1`` and the
node is not scheduled.
