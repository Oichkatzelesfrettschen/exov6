OBJS = \
	bio.o\
	console.o\
	exec.o\
	file.o\
	fs.o\
	ide.o\
	ioapic.o\
	kalloc.o\
	kbd.o\
	lapic.o\
	log.o\
	main.o\
	mp.o\
	picirq.o\
	pipe.o\
	proc.o\
	sleeplock.o\
	spinlock.o\
	string.o\
	syscall.o\
	sysfile.o\
	sysproc.o\
	trapasm.o\
	trap.o\
	uart.o\
	vectors.o\
        vm.o\
        exo.o\
        exo/exo_cpu.o\
        exo/exo_disk.o\
        exo/exo_ipc.o\
        exo_stream.o\
        kernel/exo_cpu.o\
        kernel/exo_disk.o\
        kernel/exo_ipc.o\

ifeq ($(ARCH),x86_64)
OBJS += mmu64.o
endif

# Cross-compiling (e.g., on Mac OS X)
# TOOLPREFIX = i386-jos-elf

# Using native tools (e.g., on X86 Linux)
#TOOLPREFIX = 

# Try to infer the correct TOOLPREFIX if not set
ifndef TOOLPREFIX
TOOLPREFIX := $(shell if i386-jos-elf-objdump -i 2>&1 | grep '^elf32-i386$$' >/dev/null 2>&1; \
	then echo 'i386-jos-elf-'; \
	elif objdump -i 2>&1 | grep 'elf32-i386' >/dev/null 2>&1; \
	then echo ''; \
	else echo "***" 1>&2; \
	echo "*** Error: Couldn't find an i386-*-elf version of GCC/binutils." 1>&2; \
	echo "*** Is the directory with i386-jos-elf-gcc in your PATH?" 1>&2; \
	echo "*** If your i386-*-elf toolchain is installed with a command" 1>&2; \
	echo "*** prefix other than 'i386-jos-elf-', set your TOOLPREFIX" 1>&2; \
	echo "*** environment variable to that prefix and run 'make' again." 1>&2; \
	echo "*** To turn off this error, run 'gmake TOOLPREFIX= ...'." 1>&2; \
	echo "***" 1>&2; exit 1; fi)
endif

# If the makefile can't find QEMU, specify its path here
# QEMU = qemu-system-i386

# Try to infer the correct QEMU if not provided. Leave empty when none found.
ifndef QEMU
QEMU := $(shell which qemu-system-i386 2>/dev/null || \
       which qemu-system-x86_64 2>/dev/null || \
       which qemu 2>/dev/null)
endif

ARCH ?= i686
CSTD ?= gnu2x



ifeq ($(ARCH),x86_64)
OBJS += main64.o swtch64.o
BOOTASM := arch/x64/bootasm64.S
ENTRYASM := arch/x64/entry64.S
else
OBJS += swtch.o

BOOTASM := bootasm.S
ENTRYASM := entry.S
endif

CC = $(TOOLPREFIX)gcc
AS = $(TOOLPREFIX)gas
LD = $(TOOLPREFIX)ld
OBJCOPY = $(TOOLPREFIX)objcopy
OBJDUMP = $(TOOLPREFIX)objdump

# Output file names depend on the target architecture
KERNEL_FILE := kernel.bin
KERNELMEMFS_FILE := kernelmemfs.bin
FS_IMG := fs.img
XV6_IMG := xv6.img
XV6_MEMFS_IMG := xv6memfs.img



ARCHFLAG := -m32
LDFLAGS += -m $(shell $(LD) -V | grep elf_i386 2>/dev/null | head -n 1)

CFLAGS = -fno-pic -static -fno-builtin -fno-strict-aliasing -O2 -Wall -MD -ggdb $(ARCHFLAG) -Werror -fno-omit-frame-pointer -std=$(CSTD) -nostdinc -I.
CFLAGS += $(shell $(CC) -fno-stack-protector -E -x c /dev/null >/dev/null 2>&1 && echo -fno-stack-protector)
ASFLAGS = $(ARCHFLAG) -gdwarf-2 -Wa,-divide

# Disable PIE when possible (for Ubuntu 16.10 toolchain)
ifneq ($(shell $(CC) -dumpspecs 2>/dev/null | grep -e '[^f]no-pie'),)
CFLAGS += -fno-pie -no-pie
endif
ifneq ($(shell $(CC) -dumpspecs 2>/dev/null | grep -e '[^f]nopie'),)
CFLAGS += -fno-pie -nopie
endif

$(XV6_IMG): bootblock kernel
	dd if=/dev/zero of=$(XV6_IMG) count=10000
	dd if=bootblock of=$(XV6_IMG) conv=notrunc
	dd if=$(KERNEL_FILE) of=$(XV6_IMG) seek=1 conv=notrunc

$(XV6_MEMFS_IMG): bootblock kernelmemfs
	dd if=/dev/zero of=$(XV6_MEMFS_IMG) count=10000
	dd if=bootblock of=$(XV6_MEMFS_IMG) conv=notrunc
	dd if=$(KERNELMEMFS_FILE) of=$(XV6_MEMFS_IMG) seek=1 conv=notrunc

bootblock: $(BOOTASM) bootmain.c
	$(CC) $(CFLAGS) -fno-pic -O -nostdinc -I. -c bootmain.c
	$(CC) $(CFLAGS) -fno-pic -nostdinc -I. -c $(BOOTASM) -o bootasm.o
	$(LD) $(LDFLAGS) -N -e start -Ttext 0x7C00 -o bootblock.o bootasm.o bootmain.o
	$(OBJDUMP) -S bootblock.o > bootblock.asm
	$(OBJCOPY) -S -O binary -j .text bootblock.o bootblock
	./sign.pl bootblock
entry.o: $(ENTRYASM)
	$(CC) $(CFLAGS) -fno-pic -nostdinc -I. -c $(ENTRYASM) -o entry.o


ENTRYOTHERASM := entryother.S
ENTRYOTHERBIN := entryother

$(ENTRYOTHERBIN): $(ENTRYOTHERASM)
	$(CC) $(CFLAGS) -fno-pic -nostdinc -I. -c $(ENTRYOTHERASM) -o entryother.o
	$(LD) $(LDFLAGS) -N -e start -Ttext 0x7000 -o bootblockother.o entryother.o
	$(OBJCOPY) -S -O binary -j .text bootblockother.o $(ENTRYOTHERBIN)
	$(OBJDUMP) -S bootblockother.o > $(ENTRYOTHERBIN).asm

initcode: initcode.S
	$(CC) $(CFLAGS) -nostdinc -I. -c initcode.S
	$(LD) $(LDFLAGS) -N -e start -Ttext 0 -o initcode.out initcode.o
	$(OBJCOPY) -S -O binary initcode.out initcode
	$(OBJDUMP) -S initcode.o > initcode.asm

kernel: $(OBJS) entry.o $(ENTRYOTHERBIN) initcode kernel.ld
	$(LD) $(LDFLAGS) -T kernel.ld -o $(KERNEL_FILE) entry.o $(OBJS) -b binary initcode $(ENTRYOTHERBIN)
		$(OBJDUMP) -S $(KERNEL_FILE) > kernel.asm
	$(OBJDUMP) -t $(KERNEL_FILE) | sed '1,/SYMBOL TABLE/d; s/ .* / /; /^$$/d' > kernel.sym

# kernelmemfs is a copy of kernel that maintains the
# disk image in memory instead of writing to a disk.
# This is not so useful for testing persistent storage or
# exploring disk buffering implementations, but it is
	# great for testing the kernel on real hardware without
# needing a scratch disk.
MEMFSOBJS = $(filter-out ide.o,$(OBJS)) memide.o
kernelmemfs: $(MEMFSOBJS) entry.o $(ENTRYOTHERBIN) initcode kernel.ld $(FS_IMG)
	$(LD) $(LDFLAGS) -T kernel.ld -o $(KERNELMEMFS_FILE) entry.o  $(MEMFSOBJS) -b binary initcode $(ENTRYOTHERBIN) $(FS_IMG)
	$(OBJDUMP) -S $(KERNELMEMFS_FILE) > kernelmemfs.asm
	$(OBJDUMP) -t $(KERNELMEMFS_FILE) | sed '1,/SYMBOL TABLE/d; s/ .* / /; /^$$/d' > kernelmemfs.sym

tags: $(OBJS) $(ENTRYOTHERASM) _init
		etags *.S *.c

vectors.S: vectors.pl
	./vectors.pl > vectors.S

ULIB = ulib.o usys.o printf.o umalloc.o swtch.o caplib.o math_core.o

_%: %.o $(ULIB)
	$(LD) $(LDFLAGS) -N -e main -Ttext 0 -o $@ $^
	$(OBJDUMP) -S $@ > $*.asm
	$(OBJDUMP) -t $@ | sed '1,/SYMBOL TABLE/d; s/ .* / /; /^$$/d' > $*.sym

_forktest: forktest.o $(ULIB)
	# forktest has less library code linked in - needs to be small
	# in order to be able to max out the proc table.
	$(LD) $(LDFLAGS) -N -e main -Ttext 0 -o _forktest forktest.o ulib.o usys.o
	$(OBJDUMP) -S _forktest > forktest.asm

mkfs: mkfs.c fs.h
	gcc -Werror -Wall -o mkfs mkfs.c

exo_stream_demo.o: user/exo_stream_demo.c
	$(CC) $(CFLAGS) -c -o $@ $<


# Prevent deletion of intermediate files, e.g. cat.o, after first build, so
# that disk image changes after first build are persistent until clean.  More
# details:
# http://www.gnu.org/software/make/manual/html_node/Chained-Rules.html
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
        _ipc_test\

ifeq ($(ARCH),x86_64)
UPROGS := $(filter-out _usertests,$(UPROGS))
endif

$(FS_IMG): mkfs README $(UPROGS)
	./mkfs $(FS_IMG) README $(UPROGS)

-include *.d

clean:
	rm -f *.tex *.dvi *.idx *.aux *.log *.ind *.ilg \
	*.o *.d *.asm *.sym vectors.S bootblock entryother entryother64 \
       initcode initcode.out kernel.bin kernel64 xv6.img xv6-64.img \
       fs.img fs64.img kernelmemfs.bin kernelmemfs64 xv6memfs.img \
	xv6memfs-64.img mkfs .gdbinit \
	$(UPROGS)

# make a printout
FILES = $(shell grep -v '^\#' runoff.list)
PRINT = runoff.list runoff.spec README toc.hdr toc.ftr $(FILES)

xv6.pdf: $(PRINT)
	./runoff
	ls -l xv6.pdf

print: xv6.pdf

# run in emulators

bochs : $(FS_IMG) $(XV6_IMG)
	if [ ! -e .bochsrc ]; then ln -s dot-bochsrc .bochsrc; fi
	bochs -q

# try to generate a unique GDB port
GDBPORT = $(shell expr `id -u` % 5000 + 25000)
# QEMU's gdb stub command line changed in 0.11
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

# CUT HERE
# prepare dist for students
# after running make dist, probably want to
# rename it to rev0 or rev1 or so on and then
# check in that version.

EXTRA=\
	mkfs.c ulib.c user.h cat.c echo.c forktest.c grep.c kill.c\
        ln.c ls.c mkdir.c rm.c stressfs.c usertests.c wc.c zombie.c\
        phi.c\
        user/exo_stream_demo.c\
        printf.c umalloc.c\
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

# update this rule (change rev#) when it is time to
# make a new revision.
tar:
	rm -rf /tmp/xv6
	mkdir -p /tmp/xv6
	cp dist/* dist/.gdbinit.tmpl /tmp/xv6
	(cd /tmp; tar cf - xv6) | gzip >xv6-rev10.tar.gz  # the next one will be 10 (9/17)

.PHONY: dist-test dist
