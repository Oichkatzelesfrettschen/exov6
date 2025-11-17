# Context switch
#
#   void swtch(struct context **old, struct context *new);
#
# Save the current registers on the stack, creating
# a struct context, and save its address in *old.
# Switch stacks to new and pop previously-saved registers.
# Scheduler lock state is preserved across context switches.

.globl swtch
swtch:
#if defined(__x86_64__) || defined(__amd64__)
  # x86_64 version - use 64-bit registers and calling convention
  # Arguments in rdi (old) and rsi (new)

  # Save old callee-saved registers
  pushq %rbp
  pushq %rbx
  pushq %r12
  pushq %r13
  pushq %r14
  pushq %r15

  # Switch stacks
  movq %rsp, (%rdi)
  movq %rsi, %rsp

  # Load new callee-saved registers
  popq %r15
  popq %r14
  popq %r13
  popq %r12
  popq %rbx
  popq %rbp
  ret
#else
  # i386 version - use 32-bit registers and calling convention
  # Arguments on stack
  movl 4(%esp), %eax
  movl 8(%esp), %edx

  # Save old callee-saved registers
  pushl %ebp
  pushl %ebx
  pushl %esi
  pushl %edi

  # Switch stacks
  movl %esp, (%eax)
  movl %edx, %esp

  # Load new callee-saved registers
  popl %edi
  popl %esi
  popl %ebx
  popl %ebp
  ret
#endif
