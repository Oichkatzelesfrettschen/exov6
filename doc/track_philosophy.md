# Philosophy Track

This short note captures the guiding ideas behind Phoenix without diving into internal details. It complements the [Phoenix kernel charter](phoenixkernel.md).

Phoenix embraces the exokernel philosophy of exposing hardware resources directly to user programs. Instead of enforcing a single view of files and processes, the kernel focuses on protection and delegation. User space libraries and supervisors are free to experiment with new abstractions or compatibility layers.

By keeping the kernel small, research into scheduling policies, message passing schemes and driver models happens largely in user space. The charter describes these goals in depth, while this track emphasises why the approach matters: flexibility, replaceability and minimal trusted computing base.

# Phoenix Philosophy Track

The charter states that Phoenix should remain a small, transparent
research kernel.  Only minimal mechanisms live in the privileged core
while all policies reside in user space.

Key ideas include:

- Keep the kernel tiny and auditable.
- Build subsystems as separate libraries and drivers.
- Encourage experimentation by exposing raw capabilities.
- Document changes openly so others can reuse the work.

The philosophy drives the technical direction documented in the other
tracks.
