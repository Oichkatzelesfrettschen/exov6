
# Phoenix Hybrid Track

The hybrid track links the philosophy and the concrete APIs.  By
following the charter's principles of minimalism and openness, Phoenix
exposes low level capabilities together with helper libraries.  User
space composes these pieces into higher abstractions as needed.

This approach allows researchers to replace parts of the system without
altering the kernel.  Examples include typed channels built on the basic
IPC calls and the supervisor managing drivers via capabilities.
