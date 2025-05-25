HOSTCC ?= gcc
HOSTCFLAGS ?= -Wall -O2 -std=c99

PROGS := cap_verify_bench exo_yield_to_bench

all: $(PROGS)

cap_verify_bench: cap_verify_bench.c
	$(HOSTCC) $(HOSTCFLAGS) -o $@ $<

exo_yield_to_bench: exo_yield_to_bench.c
	$(HOSTCC) $(HOSTCFLAGS) -o $@ $<

clean:
	rm -f $(PROGS)

run: all
	./cap_verify_bench
	./exo_yield_to_bench
