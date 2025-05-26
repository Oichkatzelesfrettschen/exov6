# Hypervisor Stub

This directory introduces a minimal hypervisor interface. The kernel now
exports a `HypervisorCap` capability which allows a user program to request
the launch of another Phoenix kernel as a guest. The current implementation
is only a stub: `hv_launch_guest()` merely prints a message and does not
perform any real virtualisation.

The goal is to experiment with exposing hardware virtualisation features
through the capability system. Future work will explore mapping guest
memory, forwarding interrupts and providing basic device emulation. Until
then the interface is useful for testing the capability plumbing and for
discussion around the design.
