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

#Cross - compiling(e.g., on Mac OS X)
#TOOLPREFIX = i386-jos-elf

#Using native tools(e.g., on X86 Linux)
#TOOLPREFIX =

#Try to infer the correct TOOLPREFIX if not set
ifndef TOOLPREFIX
TOOLPREFIX := $(shell if i386-jos-elf-objdump -i 2>&1 | grep '^elf32-i386$$' >/dev/null 2>&1; \
    then echo 'i386-jos-elf-'; \
    elif objdump -i 2>&1 | grep 'elf32-i386' >/dev/null 2>&1; \
    then echo ''; else echo "***" 1>&2; \
    echo "*** Error: Couldn't find an i386-*-elf version of GCC/binutils." 1>&2; \
    echo "*** Is the directory with i386-jos-elf-gcc in your PATH?" 1>&2; \
    echo "*** If your i386-*-elf toolchain is installed with a command" 1>&2; \
    echo "*** prefix other than 'i386-jos-elf-', set your TOOLPREFIX" 1>&2; \
    echo "*** environment variable to that prefix and run 'make' again." 1>&2; \
    echo "*** To turn off this error, run 'gmake TOOLPREFIX= ...'." 1>&2; \
    echo "***" 1>&2; exit 1; fi)
endif

#If the makefile can't find QEMU, specify its path here
#QEMU = qemu-system-i386

#Try to infer the correct QEMU if not provided.Leave empty when none found.
ifndef QEMU
QEMU := $(shell which qemu-system-aarch64 2>/dev/null || \
    which qemu-system-arm 2>/dev/null || \
    which qemu-system-ppc64 2>/dev/null || \
    which qemu-system-ppc 2>/dev/null || \
    which qemu-system-x86_64 2>/dev/null || \
    which qemu-system-i386 2>/dev/null || \
    which qemu 2>/dev/null)
endif

ARCH ?= x86_64
CSTD ?= gnu2x
CLANG_TIDY ?= clang-tidy
TIDY_SRCS := $(wildcard $(KERNEL_DIR)/*.c $(ULAND_DIR)/*.c $(LIBOS_DIR)/*.c)


ifeq ($(ARCH),x86_64)
OBJS += $(KERNEL_DIR)/main64.o $(KERNEL_DIR)/swtch64.o \
       $(KERNEL_DIR)/vectors.o \
       $(ARCH_DIR)/x64/trapasm64.o
OBJS := $(filter-out $(KERNEL_DIR)/trapasm.o,$(OBJS))
BOOTASM := $(ARCH_DIR)/x64/bootasm64.S
ENTRYASM := $(ARCH_DIR)/x64/entry64.S
else ifeq ($(ARCH),aarch64)
OBJS += $(KERNEL_DIR)/main64.o \
       $(ARCH_DIR)/aarch64/swtch.o \
       $(ARCH_DIR)/aarch64/vectors.o
BOOTASM := $(ARCH_DIR)/aarch64/boot.S
ENTRYASM := $(ARCH_DIR)/aarch64/entry.S
else ifeq ($(ARCH),armv7)
OBJS += $(ARCH_DIR)/armv7/swtch.o \
       $(ARCH_DIR)/armv7/vectors.o
BOOTASM := $(ARCH_DIR)/armv7/boot.S
ENTRYASM := $(ARCH_DIR)/armv7/entry.S
else ifeq ($(ARCH),powerpc)
OBJS += $(ARCH_DIR)/ppc/swtch.o \
       $(ARCH_DIR)/ppc/vectors.o
BOOTASM := $(ARCH_DIR)/ppc/boot.S
ENTRYASM := $(ARCH_DIR)/ppc/entry.S
else ifeq ($(ARCH),powerpc64)
OBJS += $(KERNEL_DIR)/main64.o \
       $(ARCH_DIR)/ppc64/swtch.o \
       $(ARCH_DIR)/ppc64/vectors.o
BOOTASM := $(ARCH_DIR)/ppc64/boot.S
ENTRYASM := $(ARCH_DIR)/ppc64/entry.S
else ifeq ($(ARCH),powerpc64le)
OBJS += $(KERNEL_DIR)/main64.o \
       $(ARCH_DIR)/ppc64le/swtch.o \
       $(ARCH_DIR)/ppc64le/vectors.o
BOOTASM := $(ARCH_DIR)/ppc64le/boot.S
ENTRYASM := $(ARCH_DIR)/ppc64le/entry.S
else
OBJS += $(KERNEL_DIR)/swtch.o \
       $(KERNEL_DIR)/vectors.o

BOOTASM := $(KERNEL_DIR)/bootasm.S
ENTRYASM := $(KERNEL_DIR)/entry.S
endif

CC = $(TOOLPREFIX)gcc
AS = $(TOOLPREFIX)gas
LD = $(TOOLPREFIX)ld
OBJCOPY = $(TOOLPREFIX)objcopy
OBJDUMP = $(TOOLPREFIX)objdump
AR = $(TOOLPREFIX)ar

	#Output file names depend on the target architecture
ifeq ($(ARCH),x86_64)
ARCHFLAG := -m64
LDFLAGS += -m elf_x86_64
KERNEL_FILE := kernel64
KERNELMEMFS_FILE := kernelmemfs64
FS_IMG := fs64.img
XV6_IMG := xv6-64.img
XV6_MEMFS_IMG := xv6memfs-64.img
else ifeq ($(ARCH),aarch64)
ARCHFLAG := -march=armv8-a
LDFLAGS += -m elf64-littleaarch64
KERNEL_FILE := kernel-aarch64
KERNELMEMFS_FILE := kernelmemfs-aarch64
FS_IMG := fs-aarch64.img
XV6_IMG := xv6-aarch64.img
XV6_MEMFS_IMG := xv6memfs-aarch64.img
else ifeq ($(ARCH),armv7)
ARCHFLAG := -march=armv7-a
LDFLAGS += -m elf32-littlearm
KERNEL_FILE := kernel-armv7
KERNELMEMFS_FILE := kernelmemfs-armv7
FS_IMG := fs-armv7.img
XV6_IMG := xv6-armv7.img
XV6_MEMFS_IMG := xv6memfs-armv7.img
else ifeq ($(ARCH),powerpc)
ARCHFLAG := -m32
LDFLAGS += -m elf32ppc
KERNEL_FILE := kernel-powerpc
KERNELMEMFS_FILE := kernelmemfs-powerpc
FS_IMG := fs-powerpc.img
XV6_IMG := xv6-powerpc.img
XV6_MEMFS_IMG := xv6memfs-powerpc.img
else ifeq ($(ARCH),powerpc64)
ARCHFLAG := -m64
LDFLAGS += -m elf64ppc
KERNEL_FILE := kernel-powerpc64
KERNELMEMFS_FILE := kernelmemfs-powerpc64
FS_IMG := fs-powerpc64.img
XV6_IMG := xv6-powerpc64.img
XV6_MEMFS_IMG := xv6memfs-powerpc64.img
else ifeq ($(ARCH),powerpc64le)
ARCHFLAG := -m64
LDFLAGS += -m elf64lppc
KERNEL_FILE := kernel-powerpc64le
KERNELMEMFS_FILE := kernelmemfs-powerpc64le
FS_IMG := fs-powerpc64le.img
XV6_IMG := xv6-powerpc64le.img
XV6_MEMFS_IMG := xv6memfs-powerpc64le.img
else
ARCHFLAG := -m32
LDFLAGS += -m elf_i386
KERNEL_FILE := kernel.bin
KERNELMEMFS_FILE := kernelmemfs.bin
FS_IMG := fs.img
XV6_IMG := xv6.img
XV6_MEMFS_IMG := xv6memfs.img
endif

	#Only sign the bootblock for 32-bit builds. The 64-bit
	#bootloader exceeds the legacy 512-byte limit.
SIGNBOOT := 1
ifeq ($(ARCH),x86_64)
SIGNBOOT := 0
endif
ifeq ($(ARCH),aarch64)
SIGNBOOT := 0
endif
ifeq ($(ARCH),armv7)
SIGNBOOT := 0
endif
ifeq ($(ARCH),powerpc)
SIGNBOOT := 0
endif
ifeq ($(ARCH),powerpc64)
SIGNBOOT := 0
endif
ifeq ($(ARCH),powerpc64le)
SIGNBOOT := 0
endif


CFLAGS = -fno-pic -static -fno-builtin -fno-strict-aliasing -O2 -Wall -MD -ggdb $(ARCHFLAG) -Werror -fno-omit-frame-pointer -std=$(CSTD) -nostdinc -I. -Iinclude -I$(KERNEL_DIR) -I$(ULAND_DIR) -I$(LIBOS_DIR) -Iproto
CFLAGS += $(shell $(CC) -fno-stack-protector -E -x c /dev/null >/dev/null 2>&1 && echo -fno-stack-protector)
# Optional CPU optimization flags
CFLAGS += $(CPUFLAGS)
ASFLAGS = $(ARCHFLAG) -gdwarf-2 -Wa,-divide -I. -Iinclude -I$(KERNEL_DIR) -I$(ULAND_DIR) -Iproto $(CPUFLAGS)

	#Disable PIE when possible (for Ubuntu 16.10 toolchain)
ifneq ($(shell $(CC) -dumpspecs 2>/dev/null | grep -e '[^f]no-pie'),)
CFLAGS += -fno-pie -no-pie
endif
ifneq ($(shell $(CC) -dumpspecs 2>/dev/null | grep -e '[^f]nopie'),)
CFLAGS += -fno-pie -nopie
endif

$(XV6_IMG): bootblock exo-kernel
	dd if=/dev/zero of=$(XV6_IMG) count=10000
	dd if=bootblock of=$(XV6_IMG) conv=notrunc
	dd if=$(KERNEL_FILE) of=$(XV6_IMG) seek=1 conv=notrunc

$(XV6_MEMFS_IMG): bootblock kernelmemfs
	dd if=/dev/zero of=$(XV6_MEMFS_IMG) count=10000
	dd if=bootblock of=$(XV6_MEMFS_IMG) conv=notrunc
	dd if=$(KERNELMEMFS_FILE) of=$(XV6_MEMFS_IMG) seek=1 conv=notrunc

bootblock: $(BOOTASM) $(KERNEL_DIR)/bootmain.c
	$(CC) $(CFLAGS) -fno-pic -O -nostdinc -I. -c $(KERNEL_DIR)/bootmain.c
	$(CC) $(CFLAGS) -fno-pic -nostdinc -I. -c $(BOOTASM) -o bootasm.o
	$(LD) $(LDFLAGS) -N -e start -Ttext 0x7C00 -o bootblock.o bootasm.o bootmain.o
	$(OBJDUMP) -S bootblock.o > bootblock.asm
	$(OBJCOPY) -S -O binary -j .text bootblock.o bootblock
ifneq ($(SIGNBOOT),0)
	./sign.pl bootblock
endif
entry.o: $(ENTRYASM)
	$(CC) $(CFLAGS) -fno-pic -nostdinc -I. -c $(ENTRYASM) -o entry.o


ENTRYOTHERASM := $(KERNEL_DIR)/entryother.S
ENTRYOTHERBIN := entryother

$(ENTRYOTHERBIN): $(ENTRYOTHERASM)
	$(CC) $(CFLAGS) -fno-pic -nostdinc -I. -c $(ENTRYOTHERASM) -o entryother.o
	$(LD) $(LDFLAGS) -N -e start -Ttext 0x7000 -o bootblockother.o entryother.o
	$(OBJCOPY) -S -O binary -j .text bootblockother.o $(ENTRYOTHERBIN)
	$(OBJDUMP) -S bootblockother.o > $(ENTRYOTHERBIN).asm

initcode: $(KERNEL_DIR)/initcode.S
	$(CC) $(CFLAGS) -nostdinc -I. -c $(KERNEL_DIR)/initcode.S
	$(LD) $(LDFLAGS) -N -e start -Ttext 0 -o initcode.out initcode.o
	$(OBJCOPY) -S -O binary initcode.out initcode
	$(OBJDUMP) -S initcode.o > initcode.asm

exo-kernel: $(OBJS) entry.o $(ENTRYOTHERBIN) initcode kernel.ld
	$(LD) $(LDFLAGS) -T kernel.ld -o $(KERNEL_FILE) entry.o $(OBJS) -b binary initcode $(ENTRYOTHERBIN)
	$(OBJDUMP) -S $(KERNEL_FILE) > kernel.asm
	$(OBJDUMP) -t $(KERNEL_FILE) | sed '1,/SYMBOL TABLE/d; s/ .* / /; /^$$/d' > kernel.sym

kernel: exo-kernel

	#kernelmemfs is a copy of kernel that maintains the
	#disk image in memory instead of writing to a disk.
	#This is not so useful for testing persistent storage or
	#exploring disk buffering implementations, but it is
	# great for testing the kernel on real hardware without
	#needing a scratch disk.
MEMFSOBJS = $(filter-out ide.o,$(OBJS)) memide.o
kernelmemfs: $(MEMFSOBJS) entry.o $(ENTRYOTHERBIN) initcode kernel.ld $(FS_IMG)
	$(LD) $(LDFLAGS) -T kernel.ld -o $(KERNELMEMFS_FILE) entry.o  $(MEMFSOBJS) -b binary initcode $(ENTRYOTHERBIN) $(FS_IMG)
	$(OBJDUMP) -S $(KERNELMEMFS_FILE) > kernelmemfs.asm
	$(OBJDUMP) -t $(KERNELMEMFS_FILE) | sed '1,/SYMBOL TABLE/d; s/ .* / /; /^$$/d' > kernelmemfs.sym

tags: $(OBJS) $(ENTRYOTHERASM) _init
		etags *.S *.c
$(KERNEL_DIR)/vectors.S: vectors.pl
	./vectors.pl $(ARCH) > $@

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
       $(ULAND_DIR)/libos/sched.o \
        $(LIBOS_DIR)/fs.o \
       $(LIBOS_DIR)/file.o \
       $(LIBOS_DIR)/driver.o \
        $(LIBOS_DIR)/affine_runtime.o \
       $(LIBOS_DIR)/posix.o


libos: libos.a

libos.a: $(LIBOS_OBJS)
	$(AR) rcs $@ $^
	
_%: $(ULAND_DIR)/%.o libos.a
	$(LD) $(LDFLAGS) -N -e main -Ttext 0 -o $@ $< libos.a
	$(OBJDUMP) -S $@ > $*.asm
	$(OBJDUMP) -t $@ | sed '1,/SYMBOL TABLE/d; s/ .* / /; /^$$/d' > $*.sym

_forktest: $(ULAND_DIR)/forktest.o $(ULAND_DIR)/ulib.o usys.o
	#forktest has less library code linked in - needs to be small
	#in order to be able to max out the proc table.

	$(LD) $(LDFLAGS) -N -e main -Ttext 0 -o _forktest $(ULAND_DIR)/forktest.o $(ULAND_DIR)/ulib.o usys.o
	$(OBJDUMP) -S _forktest > forktest.asm

mkfs: mkfs.c fs.h
	gcc -Werror -Wall -o mkfs mkfs.c

exo_stream_demo.o: $(ULAND_DIR)/exo_stream_demo.c
	$(CC) $(CFLAGS) -c -o $@ $<


$(ULAND_DIR)/exo_stream_demo.o: $(ULAND_DIR)/exo_stream_demo.c
	$(CC) $(CFLAGS) -c -o $@ $<
$(ULAND_DIR)/dag_demo.o: $(ULAND_DIR)/dag_demo.c
	$(CC) $(CFLAGS) -c -o $@ $<
$(ULAND_DIR)/typed_chan_demo.o: $(ULAND_DIR)/typed_chan_demo.c
	$(CC) $(CFLAGS) -c -o $@ $<
$(ULAND_DIR)/typed_chan_send.o: $(ULAND_DIR)/typed_chan_send.c
	$(CC) $(CFLAGS) -c -o $@ $<

$(ULAND_DIR)/beatty_demo.o: $(ULAND_DIR)/beatty_demo.c
	$(CC) $(CFLAGS) -c -o $@ $<

$(ULAND_DIR)/beatty_dag_demo.o: $(ULAND_DIR)/beatty_dag_demo.c
	$(CC) $(CFLAGS) -c -o $@ $<

$(ULAND_DIR)/typed_chan_recv.o: $(ULAND_DIR)/typed_chan_recv.c
	$(CC) $(CFLAGS) -c -o $@ $<
$(ULAND_DIR)/chan_dag_supervisor_demo.o: $(ULAND_DIR)/chan_dag_supervisor_demo.c
	$(CC) $(CFLAGS) -c -o $@ $<
$(ULAND_DIR)/chan_beatty_rcrs_demo.o: $(ULAND_DIR)/chan_beatty_rcrs_demo.c
	$(CC) $(CFLAGS) -c -o $@ $<

	# Generate simple C bindings from Cap'n Proto schemas
proto/%.capnp.c: proto/%.capnp
	./scripts/mock_capnpc.sh $<
proto/%.capnp.h: proto/%.capnp
	./scripts/mock_capnpc.sh $<

proto/%.capnp.o: proto/%.capnp.c proto/%.capnp.h
	$(CC) $(CFLAGS) -c -o $@ $<


	#Prevent deletion of intermediate files, e.g. cat.o, after first build, so
	#that disk image changes after first build are persistent until clean.  More
	#details:
	#http://www.gnu.org/software/make/manual/html_node/Chained-Rules.html
.PRECIOUS: %.o

UPROGS=\
	_cat\
	_echo\
	_forktest\
	_grep\
	_init\
	_kill\
	_ln\
	_ls\
	_mkdir\
	_rm\
	_sh\
	_stressfs\
	_usertests\
_wc\
	_zombie\
	_phi\
	_exo_stream_demo\
	_dag_demo\
	_beatty_demo\
	_beatty_dag_demo\
	_ipc_test\
	_nbtest\
        _rcrs\
        _pingdriver\
        _typed_chan_demo\
        _typed_chan_send\
        _typed_chan_recv\
        _chan_dag_supervisor_demo\
        _chan_beatty_rcrs_demo\
        _libos_posix_test\
        _libos_posix_extra_test\
        _qspin_demo\


ifeq ($(ARCH),x86_64)
UPROGS := $(filter-out _usertests,$(UPROGS))
endif

$(FS_IMG): mkfs README $(UPROGS)
	./mkfs $(FS_IMG) README $(UPROGS)

-include *.d

clean:
	find . -name '*.o' -o -name '*.d' -o -name '*.asm' -o -name '*.sym' -delete
	rm -f *.tex *.dvi *.idx *.aux *.log *.ind *.ilg \
	  $(KERNEL_DIR)/vectors.S bootblock entryother entryother64 \
	  initcode initcode.out kernel.bin kernel64 xv6.img xv6-64.img \
	  fs.img fs64.img kernelmemfs.bin kernelmemfs64 xv6memfs.img \
	  xv6memfs-64.img mkfs .gdbinit libos.a \
	  $(UPROGS)

	#make a printout
FILES = $(shell grep -v '^\#' runoff.list)
PRINT = runoff.list runoff.spec README toc.hdr toc.ftr $(FILES)

xv6.pdf: $(PRINT)
	./runoff
	ls -l xv6.pdf

print: xv6.pdf

	#run in emulators

bochs : $(FS_IMG) $(XV6_IMG)
	if [ ! -e .bochsrc ]; then ln -s dot-bochsrc .bochsrc; fi
	bochs -q

	#try to generate a unique GDB port
GDBPORT = $(shell expr `id -u` % 5000 + 25000)
	#QEMU's gdb stub command line changed in 0.11
QEMUGDB = $(shell if $(QEMU) -help | grep -q '^-gdb'; \
	then echo "-gdb tcp::$(GDBPORT)"; \
	else echo "-s -p $(GDBPORT)"; fi)
ifndef CPUS
CPUS := 2
endif
QEMUOPTS = -drive file=$(FS_IMG),index=1,media=disk,format=raw -drive file=$(XV6_IMG),index=0,media=disk,format=raw -smp $(CPUS) -m 512 $(QEMUEXTRA)

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
	        $(QEMU) -drive file=$(XV6_MEMFS_IMG),index=0,media=disk,format=raw -smp $(CPUS) -m 256; \
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

qemu-nox: $(FS_IMG) $(XV6_IMG)
	if [ -z "$(QEMU)" ]; then \
	        echo "QEMU not found. Kernel built but not executed."; \
	else \
	        $(QEMU) -nographic $(QEMUOPTS); \
	fi

.gdbinit: .gdbinit.tmpl
	sed "s/localhost:1234/localhost:$(GDBPORT)/" < $^ > $@

qemu-gdb: $(FS_IMG) $(XV6_IMG) .gdbinit
	@echo "*** Now run 'gdb'." 1>&2
	if [ -z "$(QEMU)" ]; then \
	        echo "QEMU not found. GDB stub unavailable."; \
	else \
	        $(QEMU) -serial mon:stdio $(QEMUOPTS) -S $(QEMUGDB); \
	fi

qemu-nox-gdb: $(FS_IMG) $(XV6_IMG) .gdbinit
	@echo "*** Now run 'gdb'." 1>&2
	if [ -z "$(QEMU)" ]; then \
	        echo "QEMU not found. GDB stub unavailable."; \
	else \
	        $(QEMU) -nographic $(QEMUOPTS) -S $(QEMUGDB); \
	fi

	#CUT HERE
	#prepare dist for students
	#after running make dist, probably want to
	#rename it to rev0 or rev1 or so on and then
	#check in that version.

EXTRA=\
        mkfs.c $(ULAND_DIR)/ulib.c user.h \
        $(ULAND_DIR)/cat.c $(ULAND_DIR)/echo.c $(ULAND_DIR)/forktest.c \
        $(ULAND_DIR)/grep.c $(ULAND_DIR)/kill.c \
        $(ULAND_DIR)/ln.c $(ULAND_DIR)/ls.c $(ULAND_DIR)/mkdir.c \
        $(ULAND_DIR)/rm.c $(ULAND_DIR)/stressfs.c $(ULAND_DIR)/usertests.c \
        $(ULAND_DIR)/wc.c $(ULAND_DIR)/zombie.c \
        $(ULAND_DIR)/phi.c \
        $(ULAND_DIR)/exo_stream_demo.c \
        $(ULAND_DIR)/dag_demo.c \
        $(ULAND_DIR)/beatty_dag_demo.c \
        $(ULAND_DIR)/printf.c $(ULAND_DIR)/umalloc.c\
	README dot-bochsrc *.pl toc.* runoff runoff1 runoff.list\
	.gdbinit.tmpl gdbutil\

dist:
	rm -rf dist
	mkdir dist
	for i in $(FILES); \
	do \
		grep -v PAGEBREAK $$i >dist/$$i; \
	done
	sed '/CUT HERE/,$$d' Makefile >dist/Makefile
	echo >dist/runoff.spec
	cp $(EXTRA) dist

dist-test:
	rm -rf dist
	make dist
	rm -rf dist-test
	mkdir dist-test
	cp dist/* dist-test
	cd dist-test; $(MAKE) print
	cd dist-test; $(MAKE) bochs || true
	cd dist-test; $(MAKE) qemu

	#update this rule (change rev#) when it is time to
	#make a new revision.
tar:
	rm -rf /tmp/xv6
	mkdir -p /tmp/xv6
	cp dist/* dist/.gdbinit.tmpl /tmp/xv6
	(cd /tmp; tar cf - xv6) | gzip >xv6-rev10.tar.gz  # the next one will be 10 (9/17)

.PHONY: dist-test dist check

HOSTCC ?= gcc
HOSTCFLAGS ?= -Wall -Werror -std=c99

tools/ncc: tools/ncc.c tools/compiler_utils.c tools/compiler_utils.h
	$(HOSTCC) $(HOSTCFLAGS) -o $@ tools/ncc.c tools/compiler_utils.c

src-uland/exo_unit_test: src-uland/exo_unit_test.c
	$(HOSTCC) $(HOSTCFLAGS) -o $@ $<

check: src-uland/exo_unit_test
	./src-uland/exo_unit_test
	pytest -q

clang-tidy:
	@for f in $(TIDY_SRCS); do \
	$(CLANG_TIDY) $$f -- $(CFLAGS); \
	done
