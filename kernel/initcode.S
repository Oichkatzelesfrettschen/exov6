# Initial process execs /init.
# This code runs in user space.

#include "syscall.h"
#include "traps.h"


<<<<<<< HEAD
# Prepare arguments and invoke the SYS_exec system call to execute the /init program.
# The arguments pushed onto the stack are:
# 1. argv: A pointer to the argument array containing the program name and a null terminator.
# 2. init: A pointer to the string "/init".
# 3. 0: A placeholder for the caller's program counter (not used here).
  pushl $0x0  # where caller pc would be
start:
  pushl $argv
  pushl $init
  pushl $0  # where caller pc would be
=======
# exec(init, argv)
.globl start
start:
  pushl $argv
  pushl $init
  pushl $0  // where caller pc would be
>>>>>>> origin/feature/epoch-cache-design-progress
  movl $SYS_exec, %eax
  int $T_SYSCALL

# for(;;) exit();
exit:
  movl $SYS_exit, %eax
  int $T_SYSCALL
<<<<<<< HEAD
  hlt  # halt the CPU execution

# char init[] = "/init\0";
init:
  .string "/init\0"  # Explicitly include the null terminator

# char *argv[] = { init, 0 };
# Align argv to a 4-byte boundary to ensure proper memory access
# and compatibility with system requirements.
.p2align 2
argv:
  .long init
  .long 0  # Null pointer to terminate the argv array
  .quad init
  .quad 0
  .long init
=======
  jmp exit

# char init[] = "/init\0";
init:
  .string "/init\0"

# char *argv[] = { init, 0 };
.p2align 2
argv:
  .long init
>>>>>>> origin/feature/epoch-cache-design-progress
  .long 0
