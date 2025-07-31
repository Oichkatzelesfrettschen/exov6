# Top-level Makefile for xv6 x86-64 port

KERNEL_DIR := kernel
ULAND_DIR  := user
LIBOS_DIR  := libos
ARCH_DIR   := src/arch

OBJS = \
    $(KERNEL_DIR)/bio.o \
    $(KERNEL_DIR)/console.o \
    $(KERNEL_DIR)/exec.o \
    $(KERNEL_DIR)/fs.o \
    $(KERNEL_DIR)/ide.o \
    $(KERNEL_DIR)/ioapic.o \
    $(KERNEL_DIR)/kalloc.o \
    $(KERNEL_DIR)/kbd.o \
    $(KERNEL_DIR)/lapic.o \
    $(KERNEL_DIR)/log.o \
    $(KERNEL_DIR)/main.o \
    $(KERNEL_DIR)/mp.o \
    $(KERNEL_DIR)/picirq.o \
    $(KERNEL_DIR)/pipe.o \
    $(KERNEL_DIR)/proc.o \
    $(KERNEL_DIR)/sleeplock.o \
    $(KERNEL_DIR)/spinlock.o \
    $(KERNEL_DIR)/qspinlock.o \
    $(KERNEL_DIR)/rspinlock.o \
    $(KERNEL_DIR)/rcu.o \
    $(KERNEL_DIR)/rcu_fastpath.o \
    $(KERNEL_DIR)/string.o \
    $(KERNEL_DIR)/syscall.o \
    $(KERNEL_DIR)/sysfile.o \
    $(KERNEL_DIR)/sysproc.o \
    $(KERNEL_DIR)/trapasm.o \
    $(KERNEL_DIR)/trap.o \
    $(KERNEL_DIR)/uart.o \
    $(KERNEL_DIR)/vm.o \
    $(KERNEL_DIR)/exo.o \
    $(KERNEL_DIR)/exo_cpu.o \
    $(KERNEL_DIR)/exo_disk.o \
    $(KERNEL_DIR)/exo_ipc.o \
    $(KERNEL_DIR)/exo_ipc_queue.o \
    $(KERNEL_DIR)/exo_stream.o \
    $(KERNEL_DIR)/cap.o \
    $(KERNEL_DIR)/cap_table.o \
    $(KERNEL_DIR)/fastipc.o \
    $(KERNEL_DIR)/endpoint.o \
    $(KERNEL_DIR)/dag_sched.o \
    $(KERNEL_DIR)/beatty_sched.o \
    $(KERNEL_DIR)/beatty_dag_stream.o

ifeq ($(ARCH),x86_64)
OBJS += $(KERNEL_DIR)/mmu64.o
endif

# Cross-compiling tool prefix inference
ifndef TOOLPREFIX
TOOLPREFIX := $(shell \
  if i386-jos-elf-objdump -i 2>&1 | grep -q '^elf32-i386$$'; then \
    echo 'i386-jos-elf-'; \
  elif objdump -i 2>&1 | grep -q 'elf32-i386'; then \
    echo ''; \
  else \
    echo "*** Error: Couldn't find an i386-*-elf toolchain." 1>&2; exit 1; \
  fi)
endif

# QEMU detection
ifndef QEMU
QEMU := $(shell \
  which qemu-system-aarch64 2>/dev/null || \
  which qemu-system-arm    2>/dev/null || \
  which qemu-system-ppc64  2>/dev/null || \
  which qemu-system-ppc    2>/dev/null || \
  which qemu-system-x86_64 2>/dev/null || \
  which qemu-system-i386   2>/dev/null || \
  which qemu)
endif

ARCH ?= x86_64
CSTD ?= c17
CLANG_TIDY ?= clang-tidy
TIDY_SRCS := $(wildcard $(KERNEL_DIR)/*.c $(ULAND_DIR)/*.c $(LIBOS_DIR)/*.c)

ifeq ($(ARCH),x86_64)
OBJS += $(KERNEL_DIR)/main64.o $(KERNEL_DIR)/swtch64.o \
        $(KERNEL_DIR)/vectors.o \
        $(ARCH_DIR)/x64/trapasm64.o
OBJS := $(filter-out $(KERNEL_DIR)/trapasm.o,$(OBJS))
BOOTASM  := $(ARCH_DIR)/x64/bootasm64.S
ENTRYASM := $(ARCH_DIR)/x64/entry64.S
else ifeq ($(ARCH),aarch64)
OBJS += $(KERNEL_DIR)/main64.o \
        $(ARCH_DIR)/aarch64/swtch.o \
        $(ARCH_DIR)/aarch64/vectors.o
BOOTASM  := $(ARCH_DIR)/aarch64/boot.S
ENTRYASM := $(ARCH_DIR)/aarch64/entry.S
else ifeq ($(ARCH),armv7)
OBJS += $(ARCH_DIR)/armv7/swtch.o \
        $(ARCH_DIR)/armv7/vectors.o
BOOTASM  := $(ARCH_DIR)/armv7/boot.S
ENTRYASM := $(ARCH_DIR)/armv7/entry.S
else ifeq ($(ARCH),powerpc)
OBJS += $(ARCH_DIR)/ppc/swtch.o \
        $(ARCH_DIR)/ppc/vectors.o
BOOTASM  := $(ARCH_DIR)/ppc/boot.S
ENTRYASM := $(ARCH_DIR)/ppc/entry.S
else ifeq ($(ARCH),powerpc64)
OBJS += $(KERNEL_DIR)/main64.o \
        $(ARCH_DIR)/ppc64/swtch.o \
        $(ARCH_DIR)/ppc64/vectors.o
BOOTASM  := $(ARCH_DIR)/ppc64/boot.S
ENTRYASM := $(ARCH_DIR)/ppc64/entry.S
else ifeq ($(ARCH),powerpc64le)
OBJS += $(KERNEL_DIR)/main64.o \
        $(ARCH_DIR)/ppc64le/swtch.o \
        $(ARCH_DIR)/ppc64le/vectors.o
BOOTASM  := $(ARCH_DIR)/ppc64le/boot.S
ENTRYASM := $(ARCH_DIR)/ppc64le/entry.S
else
OBJS += $(KERNEL_DIR)/swtch.o \
        $(KERNEL_DIR)/vectors.o
BOOTASM  := $(KERNEL_DIR)/bootasm.S
ENTRYASM := $(KERNEL_DIR)/entry.S
endif

CC      = $(TOOLPREFIX)gcc
AS      = $(TOOLPREFIX)as
LD      = $(TOOLPREFIX)ld
OBJCOPY = $(TOOLPREFIX)objcopy
OBJDUMP = $(TOOLPREFIX)objdump
AR      = $(TOOLPREFIX)ar

ifeq ($(ARCH),x86_64)
ARCHFLAG          := -m64
LDFLAGS          += -m elf_x86_64
KERNEL_FILE       := kernel64
KERNELMEMFS_FILE  := kernelmemfs64
FS_IMG            := fs64.img
XV6_IMG           := xv6-64.img
XV6_MEMFS_IMG     := xv6memfs-64.img
SIGNBOOT          := 0
else
ARCHFLAG          := -m32
LDFLAGS          += -m elf_i386
KERNEL_FILE       := kernel.bin
KERNELMEMFS_FILE  := kernelmemfs.bin
FS_IMG            := fs.img
XV6_IMG           := xv6.img
XV6_MEMFS_IMG     := xv6memfs.img
SIGNBOOT          := 1
endif

CFLAGS = -fno-pic -static -fno-builtin -fno-strict-aliasing \
         -O2 -Wall -MD -ggdb $(ARCHFLAG) -Werror \
         -fno-omit-frame-pointer -std=$(CSTD) \
         -nostdinc -I. -Iinclude -I$(KERNEL_DIR) \
         -I$(ULAND_DIR) -I$(LIBOS_DIR) -Iproto
CFLAGS += $(shell $(CC) -fno-stack-protector -E -x c /dev/null >/dev/null 2>&1 \
            && echo -fno-stack-protector)
CFLAGS += $(CPUFLAGS)

ASFLAGS = $(ARCHFLAG) -gdwarf-2 -Wa,-divide \
          -I. -Iinclude -I$(KERNEL_DIR) \
          -I$(ULAND_DIR) -Iproto $(CPUFLAGS)

# Disable PIE if supported
ifneq ($(shell $(CC) -dumpspecs | grep -q 'no-pie'; echo $$?),0)
  CFLAGS += -fno-pie -no-pie
endif

# Build disk image
$(XV6_IMG): bootblock exo-kernel
	dd if=/dev/zero of=$(XV6_IMG) count=10000
	dd if=bootblock of=$(XV6_IMG) conv=notrunc
	dd if=$(KERNEL_FILE) of=$(XV6_IMG) seek=1 conv=notrunc

$(XV6_MEMFS_IMG): bootblock kernelmemfs
	dd if=/dev/zero of=$(XV6_MEMFS_IMG) count=10000
	dd if=bootblock of=$(XV6_MEMFS_IMG) conv=notrunc
	dd if=$(KERNELMEMFS_FILE) of=$(XV6_MEMFS_IMG) seek=1 conv=notrunc

bootblock: $(BOOTASM) $(KERNEL_DIR)/bootmain.c
	$(CC) $(CFLAGS) -c $(KERNEL_DIR)/bootmain.c
	$(CC) $(CFLAGS) -c $(BOOTASM) -o bootasm.o
	$(LD) $(LDFLAGS) -N -e start -Ttext 0x7C00 \
	     -o bootblock.o bootasm.o bootmain.o
	$(OBJDUMP) -S bootblock.o > bootblock.asm
	$(OBJCOPY) -S -O binary -j .text bootblock.o bootblock
ifneq ($(SIGNBOOT),0)
	./sign.pl bootblock
endif

entry.o: $(ENTRYASM)
	$(CC) $(CFLAGS) -c $(ENTRYASM) -o entry.o

ENTRYOTHERASM := $(KERNEL_DIR)/entryother.S
ENTRYOTHERBIN := entryother

$(ENTRYOTHERBIN): $(ENTRYOTHERASM)
	$(CC) $(CFLAGS) -c $(ENTRYOTHERASM) -o entryother.o
	$(LD) $(LDFLAGS) -N -e start -Ttext 0x7000 -o bootblockother.o entryother.o
	$(OBJCOPY) -S -O binary -j .text bootblockother.o $(ENTRYOTHERBIN)
	$(OBJDUMP) -S bootblockother.o > $(ENTRYOTHERBIN).asm

initcode: $(KERNEL_DIR)/initcode.S
	$(CC) $(CFLAGS) -c $(KERNEL_DIR)/initcode.S
	$(LD) $(LDFLAGS) -N -e start -Ttext 0 -o initcode.out initcode.o
	$(OBJCOPY) -S -O binary initcode.out initcode
	$(OBJDUMP) -S initcode.o > initcode.asm

exo-kernel: $(OBJS) entry.o $(ENTRYOTHERBIN) initcode $(KERNEL_DIR)/kernel.ld
	$(LD) $(LDFLAGS) -T $(KERNEL_DIR)/kernel.ld \
	     -o $(KERNEL_FILE) entry.o $(OBJS) \
	     -b binary initcode $(ENTRYOTHERBIN)
	$(OBJDUMP) -S $(KERNEL_FILE) > kernel.asm
	$(OBJDUMP) -t $(KERNEL_FILE) | sed '1,/SYMBOL TABLE/d; s/ .* / /; /^$$/d' \
	     > kernel.sym

kernel: exo-kernel

MEMFSOBJS = $(filter-out ide.o,$(OBJS)) memide.o
kernelmemfs: $(MEMFSOBJS) entry.o $(ENTRYOTHERBIN) initcode $(KERNEL_DIR)/kernel.ld $(FS_IMG)
	$(LD) $(LDFLAGS) -T $(KERNEL_DIR)/kernel.ld \
	     -o $(KERNELMEMFS_FILE) entry.o $(MEMFSOBJS) \
	     -b binary initcode $(ENTRYOTHERBIN) $(FS_IMG)
	$(OBJDUMP) -S $(KERNELMEMFS_FILE) > kernelmemfs.asm
	$(OBJDUMP) -t $(KERNELMEMFS_FILE) | sed '1,/SYMBOL TABLE/d; s/ .* / /; /^$$/d' \
	     > kernelmemfs.sym

tags: $(OBJS) $(ENTRYOTHERASM) initcode
	etags *.S *.c

$(KERNEL_DIR)/vectors.S: vectors.pl
	./vectors.pl $(ARCH) > $@

# libos build
LIBOS_OBJS = \
    $(ULAND_DIR)/ulib.o \
    usys.o \
    $(ULAND_DIR)/printf.o \
    $(ULAND_DIR)/umalloc.o \
    $(ULAND_DIR)/swtch.o \
    $(ULAND_DIR)/caplib.o \
    $(ULAND_DIR)/chan.o \
    proto/driver.capnp.o \
    $(ULAND_DIR)/math_core.o \
    $(LIBOS_DIR)/sched.o \
    $(LIBOS_DIR)/fs.o \
    $(LIBOS_DIR)/file.o \
    $(LIBOS_DIR)/driver.o \
    $(LIBOS_DIR)/affine_runtime.o \
    $(LIBOS_DIR)/posix.o

libos: libos.a

libos.a: $(LIBOS_OBJS)
	$(AR) rcs $@ $^

_%: $(ULAND_DIR)/%.o libos.a
	$(LD) $(LDFLAGS) -N -e main -Ttext 0 \
	     -o $@ $< libos.a
	$(OBJDUMP) -S $@ > $*.asm
	$(OBJDUMP) -t $@ | sed '1,/SYMBOL TABLE/d; s/ .* / /; /^$$/d' \
	     > $*.sym

# mkfs and filesystem image
mkfs: mkfs.c fs.h
	$(CC) -Werror -Wall -o mkfs mkfs.c

$(FS_IMG): mkfs README _cat _echo _forktest _grep _init _kill _ln _ls _mkdir \
            _rm _sh _stressfs _usertests _wc _zombie _phi \
            _exo_stream_demo _dag_demo _beatty_demo _beatty_dag_demo \
            _ipc_test _nbtest _fileserver _rcrs
	./mkfs $(FS_IMG) README _cat _echo _forktest _grep _init _kill _ln _ls \
	        _mkdir _rm _sh _stressfs _usertests _wc _zombie _phi \
	        _exo_stream_demo _dag_demo _beatty_demo _beatty_dag_demo \
	        _ipc_test _nbtest _fileserver _rcrs

# User crevated demos and routines
%_demo.o: $(ULAND_DIR)/%_demo.c
	$(CC) $(CFLAGS) -c -o $@ $<

# Cap’n Proto codegen
proto/%.capnp.c proto/%.capnp.h: proto/%.capnp
	./scripts/mock_capnpc.sh $<

proto/%.capnp.o: proto/%.capnp.c proto/%.capnp.h
	$(CC) $(CFLAGS) -c -o $@ $<

.PRECIOUS: %.o

UPROGS = \
    _cat _echo _forktest _grep _init _kill _ln _ls _mkdir _rm _sh _stressfs \
    _usertests _wc _zombie _phi _exo_stream_demo _dag_demo _beatty_demo \
    _beatty_dag_demo _ipc_test _nbtest _fileserver _rcrs

ifeq ($(ARCH),x86_64)
UPROGS := $(filter-out _usertests,$(UPROGS))
endif

# QEMU options
CPUS ?= 2
QEMUEXTRA ?=
QEMUOPTS = -drive file=$(FS_IMG),index=1,media=disk,format=raw \
           -drive file=$(XV6_IMG),index=0,media=disk,format=raw \
           -smp $(CPUS) -m 512 $(QEMUEXTRA)

qemu: $(FS_IMG) $(XV6_IMG)
	if [ -z "$(QEMU)" ]; then \
	  echo "QEMU not found. Kernel built but not executed."; \
	else \
	  $(QEMU) -serial mon:stdio $(QEMUOPTS); \
	fi

qemu-memfs: $(XV6_MEMFS_IMG)
	if [ -z "$(QEMU)" ]; then \
	  echo "QEMU not found. Kernel built but not executed."; \
	else \
	  $(QEMU) -drive file=$(XV6_MEMFS_IMG),index=0,media=disk,format=raw \
	           -smp $(CPUS) -m 256; \
	fi

proof:
	$(MAKE) -C formal/coq all

formal:
	@if command -v coqc >/dev/null 2>&1; then \
	  $(MAKE) -C formal/coq all; \
	else \
	  echo "coqc not found; skipping Coq build"; \
	fi
	@if command -v tlc >/dev/null 2>&1; then \
	  tlc formal/specs/tla/ExoCap.tla >/dev/null; \
	else \
	  echo "tlc not found; skipping TLA+ check"; \
	fi

# GDB stub integration
GDBPORT = $(shell expr `id -u` % 5000 + 25000)
QEMUGDB = $(shell \
  if $(QEMU) -help | grep -q '^-gdb'; then \
    echo "-gdb tcp::$(GDBPORT)"; \
  else \
    echo "-s -p $(GDBPORT)"; \
  fi)

.gdbinit: .gdbinit.tmpl
	sed "s/localhost:1234/localhost:$(GDBPORT)/" < $^ > $@

qemu-gdb: $(FS_IMG) $(XV6_IMG) .gdbinit
	@echo "*** Now run 'gdb'." 1>&2
	if [ -z "$(QEMU)" ]; then \
	  echo "QEMU not found. GDB stub unavailable."; \
	else \
	  $(QEMU) -serial mon:stdio $(QEMUOPTS) -S $(QEMUGDB); \
	fi

qemu-nox: $(FS_IMG) $(XV6_IMG)
	if [ -z "$(QEMU)" ]; then \
	  echo "QEMU not found. Kernel built but not executed."; \
	else \
	  $(QEMU) -nographic $(QEMUOPTS); \
	fi

qemu-nox-gdb: $(FS_IMG) $(XV6_IMG) .gdbinit
	@echo "*** Now run 'gdb'." 1>&2
	if [ -z "$(QEMU)" ]; then \
	  echo "QEMU not found. GDB stub unavailable."; \
	else \
	  $(QEMU) -nographic $(QEMUOPTS) -S $(QEMUGDB); \
	fi

clean:
	find . -name '*.o' -o -name '*.d' -o -name '*.asm' -o -name '*.sym' -delete
	rm -f bootblock entry.o entryother initcode \
	      $(KERNEL_FILE) $(KERNELMEMFS_FILE) xv6.img xv6-64.img \
	      fs.img fs64.img kernelmemfs.img xv6memfs-64.img mkfs libos.a .gdbinit

clang-tidy:
	@for f in $(TIDY_SRCS); do \
	  $(CLANG_TIDY) $$f -- $(CFLAGS); \
	done

-include *.d