# Makefile for QSpinlock Tests and Benchmarks
# ExoV6 Lock Subsystem Testing

CC = clang
CFLAGS = -std=c17 -Wall -Wextra -O2 -pthread -march=native
CFLAGS += -I../../include
CFLAGS += -D_GNU_SOURCE

# Targets
TEST_BIN = test_qspinlock
BENCH_BIN = bench_qspinlock

.PHONY: all test bench clean help

all: $(TEST_BIN) $(BENCH_BIN)

$(TEST_BIN): test_qspinlock.c
	@echo "Building unit tests..."
	$(CC) $(CFLAGS) -o $@ $<
	@echo "✓ Unit tests built: ./$@"

$(BENCH_BIN): bench_qspinlock.c
	@echo "Building benchmarks..."
	$(CC) $(CFLAGS) -o $@ $<
	@echo "✓ Benchmarks built: ./$@"

test: $(TEST_BIN)
	@echo ""
	@echo "Running QSpinlock unit tests..."
	@./$(TEST_BIN)

bench: $(BENCH_BIN)
	@echo ""
	@echo "Running QSpinlock benchmarks..."
	@./$(BENCH_BIN)

clean:
	@echo "Cleaning build artifacts..."
	rm -f $(TEST_BIN) $(BENCH_BIN)
	@echo "✓ Clean complete"

help:
	@echo "ExoV6 QSpinlock Test Suite"
	@echo ""
	@echo "Targets:"
	@echo "  make all    - Build tests and benchmarks"
	@echo "  make test   - Build and run unit tests"
	@echo "  make bench  - Build and run benchmarks"
	@echo "  make clean  - Remove build artifacts"
	@echo "  make help   - Show this help"
	@echo ""
	@echo "Requirements:"
	@echo "  - clang with C17 support"
	@echo "  - pthread library"
	@echo "  - x86_64 CPU with TSC/RDTSC support"
