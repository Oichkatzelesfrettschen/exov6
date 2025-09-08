
# Consider dependencies only in project.
set(CMAKE_DEPENDS_IN_PROJECT_ONLY OFF)

# The set of languages for which implicit dependencies are needed:
set(CMAKE_DEPENDS_LANGUAGES
  "ASM"
  )
# The set of files for implicit dependencies of each language:
set(CMAKE_DEPENDS_CHECK_ASM
  "/Users/eirikr/Documents/GitHub/exov6/kernel/boot/bootasm.S" "/Users/eirikr/Documents/GitHub/exov6/build_test/CMakeFiles/kernel.elf.dir/kernel/boot/bootasm.S.o"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/boot/entry.S" "/Users/eirikr/Documents/GitHub/exov6/build_test/CMakeFiles/kernel.elf.dir/kernel/boot/entry.S.o"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/entryother.S" "/Users/eirikr/Documents/GitHub/exov6/build_test/CMakeFiles/kernel.elf.dir/kernel/entryother.S.o"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/initcode.S" "/Users/eirikr/Documents/GitHub/exov6/build_test/CMakeFiles/kernel.elf.dir/kernel/initcode.S.o"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/swtch.S" "/Users/eirikr/Documents/GitHub/exov6/build_test/CMakeFiles/kernel.elf.dir/kernel/swtch.S.o"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/swtch64.S" "/Users/eirikr/Documents/GitHub/exov6/build_test/CMakeFiles/kernel.elf.dir/kernel/swtch64.S.o"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/sys/trapasm.S" "/Users/eirikr/Documents/GitHub/exov6/build_test/CMakeFiles/kernel.elf.dir/kernel/sys/trapasm.S.o"
  )
set(CMAKE_ASM_COMPILER_ID "AppleClang")

# Preprocessor definitions for this target.
set(CMAKE_TARGET_DEFINITIONS_ASM
  "LEGACY_TYPES_COMPATIBILITY"
  "__LP64__"
  "__x86_64__"
  )

# The include file search paths:
set(CMAKE_ASM_TARGET_INCLUDE_PATH
  "/Users/eirikr/Documents/GitHub/exov6/include"
  "/Users/eirikr/Documents/GitHub/exov6/kernel"
  )

# The set of dependency files which are needed:
set(CMAKE_DEPENDS_DEPENDENCY_FILES
  "/Users/eirikr/Documents/GitHub/exov6/kernel/arbitrate.c" "CMakeFiles/kernel.elf.dir/kernel/arbitrate.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/arbitrate.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/boot/bootmain.c" "CMakeFiles/kernel.elf.dir/kernel/boot/bootmain.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/boot/bootmain.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/boot/main.c" "CMakeFiles/kernel.elf.dir/kernel/boot/main.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/boot/main.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/boot/main64.c" "CMakeFiles/kernel.elf.dir/kernel/boot/main64.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/boot/main64.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/crypto.c" "CMakeFiles/kernel.elf.dir/kernel/crypto.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/crypto.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/drivers/console.c" "CMakeFiles/kernel.elf.dir/kernel/drivers/console.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/drivers/console.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/drivers/ddekit.c" "CMakeFiles/kernel.elf.dir/kernel/drivers/ddekit.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/drivers/ddekit.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/drivers/driver.c" "CMakeFiles/kernel.elf.dir/kernel/drivers/driver.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/drivers/driver.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/drivers/ioapic.c" "CMakeFiles/kernel.elf.dir/kernel/drivers/ioapic.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/drivers/ioapic.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/drivers/iommu.c" "CMakeFiles/kernel.elf.dir/kernel/drivers/iommu.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/drivers/iommu.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/drivers/kbd.c" "CMakeFiles/kernel.elf.dir/kernel/drivers/kbd.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/drivers/kbd.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/drivers/lapic.c" "CMakeFiles/kernel.elf.dir/kernel/drivers/lapic.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/drivers/lapic.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/drivers/memide.c" "CMakeFiles/kernel.elf.dir/kernel/drivers/memide.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/drivers/memide.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/drivers/mp.c" "CMakeFiles/kernel.elf.dir/kernel/drivers/mp.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/drivers/mp.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/drivers/picirq.c" "CMakeFiles/kernel.elf.dir/kernel/drivers/picirq.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/drivers/picirq.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/drivers/uart.c" "CMakeFiles/kernel.elf.dir/kernel/drivers/uart.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/drivers/uart.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/env.c" "CMakeFiles/kernel.elf.dir/kernel/env.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/env.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/fs/bio.c" "CMakeFiles/kernel.elf.dir/kernel/fs/bio.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/fs/bio.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/fs/fs.c" "CMakeFiles/kernel.elf.dir/kernel/fs/fs.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/fs/fs.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/fs/ide.c" "CMakeFiles/kernel.elf.dir/kernel/fs/ide.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/fs/ide.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/fs/log.c" "CMakeFiles/kernel.elf.dir/kernel/fs/log.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/fs/log.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/hypervisor/hypervisor.c" "CMakeFiles/kernel.elf.dir/kernel/hypervisor/hypervisor.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/hypervisor/hypervisor.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/ipc/cap.c" "CMakeFiles/kernel.elf.dir/kernel/ipc/cap.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/ipc/cap.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/ipc/cap_mem.c" "CMakeFiles/kernel.elf.dir/kernel/ipc/cap_mem.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/ipc/cap_mem.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/ipc/cap_table.c" "CMakeFiles/kernel.elf.dir/kernel/ipc/cap_table.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/ipc/cap_table.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/ipc/capnp_helpers.c" "CMakeFiles/kernel.elf.dir/kernel/ipc/capnp_helpers.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/ipc/capnp_helpers.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/ipc/capwrap.c" "CMakeFiles/kernel.elf.dir/kernel/ipc/capwrap.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/ipc/capwrap.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/ipc/chan.c" "CMakeFiles/kernel.elf.dir/kernel/ipc/chan.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/ipc/chan.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/ipc/endpoint.c" "CMakeFiles/kernel.elf.dir/kernel/ipc/endpoint.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/ipc/endpoint.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/ipc/exo.c" "CMakeFiles/kernel.elf.dir/kernel/ipc/exo.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/ipc/exo.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/ipc/exo_cpu.c" "CMakeFiles/kernel.elf.dir/kernel/ipc/exo_cpu.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/ipc/exo_cpu.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/ipc/exo_disk.c" "CMakeFiles/kernel.elf.dir/kernel/ipc/exo_disk.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/ipc/exo_disk.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/ipc/exo_ipc.c" "CMakeFiles/kernel.elf.dir/kernel/ipc/exo_ipc.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/ipc/exo_ipc.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/ipc/exo_ipc_queue.c" "CMakeFiles/kernel.elf.dir/kernel/ipc/exo_ipc_queue.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/ipc/exo_ipc_queue.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/ipc/exo_stream.c" "CMakeFiles/kernel.elf.dir/kernel/ipc/exo_stream.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/ipc/exo_stream.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/ipc/fastipc.c" "CMakeFiles/kernel.elf.dir/kernel/ipc/fastipc.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/ipc/fastipc.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/ipc/lattice_ipc.c" "CMakeFiles/kernel.elf.dir/kernel/ipc/lattice_ipc.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/ipc/lattice_ipc.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/ipc/sys_ipc.c" "CMakeFiles/kernel.elf.dir/kernel/ipc/sys_ipc.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/ipc/sys_ipc.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/irq.c" "CMakeFiles/kernel.elf.dir/kernel/irq.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/irq.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/lambda_cap.c" "CMakeFiles/kernel.elf.dir/kernel/lambda_cap.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/lambda_cap.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/lib9p.c" "CMakeFiles/kernel.elf.dir/kernel/lib9p.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/lib9p.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/mem/kalloc.c" "CMakeFiles/kernel.elf.dir/kernel/mem/kalloc.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/mem/kalloc.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/mem/libbaremetal.c" "CMakeFiles/kernel.elf.dir/kernel/mem/libbaremetal.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/mem/libbaremetal.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/mem/mmu64.c" "CMakeFiles/kernel.elf.dir/kernel/mem/mmu64.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/mem/mmu64.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/mem/vm.c" "CMakeFiles/kernel.elf.dir/kernel/mem/vm.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/mem/vm.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/memutil.c" "CMakeFiles/kernel.elf.dir/kernel/memutil.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/memutil.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/msg_router.c" "CMakeFiles/kernel.elf.dir/kernel/msg_router.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/msg_router.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/octonion.c" "CMakeFiles/kernel.elf.dir/kernel/octonion.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/octonion.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/picokernel.c" "CMakeFiles/kernel.elf.dir/kernel/picokernel.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/picokernel.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/registration.c" "CMakeFiles/kernel.elf.dir/kernel/registration.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/registration.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/resource_account.c" "CMakeFiles/kernel.elf.dir/kernel/resource_account.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/resource_account.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/sched/beatty_dag_stream.c" "CMakeFiles/kernel.elf.dir/kernel/sched/beatty_dag_stream.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/sched/beatty_dag_stream.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/sched/beatty_sched.c" "CMakeFiles/kernel.elf.dir/kernel/sched/beatty_sched.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/sched/beatty_sched.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/sched/dag_sched.c" "CMakeFiles/kernel.elf.dir/kernel/sched/dag_sched.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/sched/dag_sched.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/sched/proc.c" "CMakeFiles/kernel.elf.dir/kernel/sched/proc.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/sched/proc.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/service.c" "CMakeFiles/kernel.elf.dir/kernel/service.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/service.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/streams.c" "CMakeFiles/kernel.elf.dir/kernel/streams.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/streams.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/sync/modern_locks.c" "CMakeFiles/kernel.elf.dir/kernel/sync/modern_locks.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/sync/modern_locks.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/sync/rcu.c" "CMakeFiles/kernel.elf.dir/kernel/sync/rcu.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/sync/rcu.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/sync/sleeplock.c" "CMakeFiles/kernel.elf.dir/kernel/sync/sleeplock.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/sync/sleeplock.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/sync/spinlock.c" "CMakeFiles/kernel.elf.dir/kernel/sync/spinlock.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/sync/spinlock.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/sys/exec.c" "CMakeFiles/kernel.elf.dir/kernel/sys/exec.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/sys/exec.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/sys/pipe.c" "CMakeFiles/kernel.elf.dir/kernel/sys/pipe.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/sys/pipe.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/sys/string.c" "CMakeFiles/kernel.elf.dir/kernel/sys/string.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/sys/string.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/sys/syscall.c" "CMakeFiles/kernel.elf.dir/kernel/sys/syscall.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/sys/syscall.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/sys/sysfile.c" "CMakeFiles/kernel.elf.dir/kernel/sys/sysfile.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/sys/sysfile.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/sys/sysproc.c" "CMakeFiles/kernel.elf.dir/kernel/sys/sysproc.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/sys/sysproc.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/sys/trap.c" "CMakeFiles/kernel.elf.dir/kernel/sys/trap.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/sys/trap.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/tty.c" "CMakeFiles/kernel.elf.dir/kernel/tty.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/tty.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/zone.c" "CMakeFiles/kernel.elf.dir/kernel/zone.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/zone.c.o.d"
  "/Users/eirikr/Documents/GitHub/exov6/kernel/zone_isolation.c" "CMakeFiles/kernel.elf.dir/kernel/zone_isolation.c.o" "gcc" "CMakeFiles/kernel.elf.dir/kernel/zone_isolation.c.o.d"
  )

# Targets to which this target links which contain Fortran sources.
set(CMAKE_Fortran_TARGET_LINKED_INFO_FILES
  )

# Targets to which this target links which contain Fortran sources.
set(CMAKE_Fortran_TARGET_FORWARD_LINKED_INFO_FILES
  )

# Fortran module output directory.
set(CMAKE_Fortran_TARGET_MODULE_DIR "")
