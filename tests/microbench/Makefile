HOSTCC ?= clang
HOSTCFLAGS ?= -Wall -O2 -std=c2x -I../../include -I../..

PROGS := cap_verify_bench exo_yield_to_bench proc_cap_test lattice_pipe_bench

all: $(PROGS)

cap_verify_bench: cap_verify_bench.c
	$(HOSTCC) $(HOSTCFLAGS) -o $@ $<

exo_yield_to_bench: exo_yield_to_bench.c
	$(HOSTCC) $(HOSTCFLAGS) -o $@ $<

proc_cap_test: proc_cap_test.c
	$(HOSTCC) $(HOSTCFLAGS) -o $@ $<

lattice_pipe_bench: lattice_pipe_bench.c
	$(HOSTCC) $(HOSTCFLAGS) -o $@ $<

clean:
	rm -f $(PROGS)

run: all
	./cap_verify_bench
	./exo_yield_to_bench
	./proc_cap_test
	./lattice_pipe_bench
