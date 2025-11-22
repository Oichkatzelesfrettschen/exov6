# Security Tests

This directory contains security-focused unit tests for the Phoenix Exokernel.

## Capability System Tests

`test_cap_security.c` tests the capability system logic (creation, delegation, revocation, stale capabilities) in isolation.

### Running the test

To compile and run the test:

```bash
gcc -I mocks -o test_cap_security test_cap_security.c
./test_cap_security
```

### Files

*   `test_cap_security.c`: The main test runner.
*   `test_wrapper_capability_v2.c`: A copy of `kernel/capability_v2.c` used for testing (allows mocking kernel headers).
*   `mocks/`: Mock headers to allow compiling kernel code in user-space.
