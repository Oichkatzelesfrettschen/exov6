HOSTCC ?= clang
HOSTCFLAGS ?= -Wall -O2 -std=c2x -I../../src/engine/libos/include -I../../src/engine/include

PROGS := cap_verify_bench exo_yield_to_bench proc_cap_test

all: $(PROGS)

cap_verify_bench: cap_verify_bench.c
	$(HOSTCC) $(HOSTCFLAGS) -o $@ $<

exo_yield_to_bench: exo_yield_to_bench.c
        $(HOSTCC) $(HOSTCFLAGS) -o $@ $<

proc_cap_test: proc_cap_test.c
        $(HOSTCC) $(HOSTCFLAGS) -o $@ $<

clean:
	rm -f $(PROGS)

run: all
        ./cap_verify_bench
        ./exo_yield_to_bench
        ./proc_cap_test
