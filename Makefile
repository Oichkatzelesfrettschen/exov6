# ═══════════════════════════════════════════════════════════════════════════════
# DEPRECATED MAKEFILE - LEGACY BUILD SYSTEM
# ═══════════════════════════════════════════════════════════════════════════════
#
# ⚠️  WARNING: This Makefile is DEPRECATED and will be removed in a future release.
#
# Please migrate to the modern CMake build system:
#
#   Quick Start:
#     cmake --preset=default    # Configure
#     cmake --build build       # Build
#     ctest --preset=default    # Test
#
#   Available presets:
#     - default : Standard debug build
#     - release : Optimized release build  
#     - debug   : Debug with sanitizers
#     - dev     : Quick development iteration
#     - ci      : CI with all checks
#
#   See CMakePresets.json for all configurations.
#   See README.md for full migration guide.
#
# ═══════════════════════════════════════════════════════════════════════════════

.PHONY: help migrate-info
.DEFAULT_GOAL := help

help:
	@echo "╔════════════════════════════════════════════════════════════════╗"
	@echo "║  DEPRECATED BUILD SYSTEM - Please use CMake                    ║"
	@echo "╚════════════════════════════════════════════════════════════════╝"
	@echo ""
	@echo "This Makefile is deprecated. Use CMake instead:"
	@echo ""
	@echo "  Configure:  cmake --preset=default"
	@echo "  Build:      cmake --build build"
	@echo "  Test:       ctest --preset=default"
	@echo ""
	@echo "Run 'make migrate-info' for detailed migration instructions."
	@echo ""

migrate-info:
	@echo "╔════════════════════════════════════════════════════════════════╗"
	@echo "║  MAKEFILE → CMAKE MIGRATION GUIDE                              ║"
	@echo "╚════════════════════════════════════════════════════════════════╝"
	@echo ""
	@echo "OLD (Makefile)              →  NEW (CMake)"
	@echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
	@echo "make                        →  cmake --build build"
	@echo "make clean                  →  cmake --build build --target clean"
	@echo "make test                   →  ctest --preset=default"
	@echo "make all                    →  cmake --build build --parallel"
	@echo "make lockfree               →  cmake --build build --target lockfree"
	@echo ""
	@echo "Configuration options:"
	@echo "  CC=clang make             →  cmake --preset=default (uses Clang by default)"
	@echo "  CFLAGS=-O3 make           →  cmake --preset=release"
	@echo "  make DEBUG=1              →  cmake --preset=debug"
	@echo ""
	@echo "Benefits of CMake:"
	@echo "  ✓ Modern dependency management"
	@echo "  ✓ Better IDE integration"
	@echo "  ✓ Cross-platform support"
	@echo "  ✓ Configuration presets"
	@echo "  ✓ Parallel builds by default"
	@echo "  ✓ Better error messages"
	@echo ""
	@echo "For full documentation, see:"
	@echo "  • README.md - Build instructions"
	@echo "  • CMakePresets.json - Available configurations"
	@echo "  • docs/BUILD.md - Detailed build guide"
	@echo ""

# Legacy targets that redirect to help
.PHONY: all clean test lockfree
all clean test lockfree:
	@$(MAKE) help
	@exit 1

# ═══════════════════════════════════════════════════════════════════════════════
# LEGACY MAKEFILE CONTENT (KEPT FOR REFERENCE, NOT EXECUTED)
# ═══════════════════════════════════════════════════════════════════════════════
#
# The original Makefile content has been archived below for reference.
# These targets are NO LONGER FUNCTIONAL.
#
# ─────────────────────────────────────────────────────────────────────────────── 
#
# Makefile for PDAC (Probabilistic DAG Algebra with Capabilities)
# Phase 5: Lock-Free Revolution

CC := gcc
CFLAGS := -Wall -Wextra -std=c2x -O2 -pthread -I./include -g
LDFLAGS := -pthread -lm

# Directories
KERNEL_DIR := kernel
INCLUDE_DIR := include
BUILD_DIR := build

# Create build directory
$(shell mkdir -p $(BUILD_DIR))

# PDAC Core Objects
CORE_OBJS := \
	$(BUILD_DIR)/q16_fixed.o \
	$(BUILD_DIR)/q16_octonion.o \
	$(BUILD_DIR)/resource_vector.o \
	$(BUILD_DIR)/capability_v2.o \
	$(BUILD_DIR)/dag_pdac.o \
	$(BUILD_DIR)/lcg.o \
	$(BUILD_DIR)/sched_lottery.o \
	$(BUILD_DIR)/sched_beatty.o \
	$(BUILD_DIR)/sched_hybrid.o \
	$(BUILD_DIR)/sched_admission.o \
	$(BUILD_DIR)/task_exec.o \
	$(BUILD_DIR)/percpu_sched.o \
	$(BUILD_DIR)/sched_telemetry.o \
	$(BUILD_DIR)/dag_executor.o

# Phase 5: Lock-Free Objects
LOCKFREE_OBJS := \
	$(BUILD_DIR)/lockfree.o \
	$(BUILD_DIR)/rcu_pdac.o \
	$(BUILD_DIR)/work_stealing.o

# All objects
ALL_OBJS := $(CORE_OBJS) $(LOCKFREE_OBJS)

# Test executables
TESTS := \
	$(BUILD_DIR)/test_qmath \
	$(BUILD_DIR)/test_octonion \
	$(BUILD_DIR)/test_capability_v2 \
	$(BUILD_DIR)/test_dag_pdac \
	$(BUILD_DIR)/test_scheduler \
	$(BUILD_DIR)/test_executor \
	$(BUILD_DIR)/test_lockfree \
	$(BUILD_DIR)/test_rcu \
	$(BUILD_DIR)/test_work_stealing \
	$(BUILD_DIR)/test_integration_phase5

# Examples
EXAMPLES := \
	$(BUILD_DIR)/example_phase3 \
	$(BUILD_DIR)/example_phase4 \
	$(BUILD_DIR)/example_phase5_advanced

# Default target
.PHONY: all
all: $(ALL_OBJS) $(TESTS) $(EXAMPLES)

# Phase 5: Lock-free build targets
.PHONY: lockfree
lockfree: $(LOCKFREE_OBJS) $(BUILD_DIR)/test_lockfree
	@echo "Lock-free components built successfully"

# Build rules
$(BUILD_DIR)/%.o: $(KERNEL_DIR)/%.c
	@echo "CC $<"
	@$(CC) $(CFLAGS) -c $< -o $@

# Test build rules
$(BUILD_DIR)/test_qmath: $(KERNEL_DIR)/test_qmath.c $(BUILD_DIR)/q16_fixed.o
	@echo "LINK $@"
	@$(CC) $(CFLAGS) $^ -o $@ $(LDFLAGS)

$(BUILD_DIR)/test_octonion: $(KERNEL_DIR)/test_octonion.c $(BUILD_DIR)/q16_octonion.o $(BUILD_DIR)/q16_fixed.o
	@echo "LINK $@"
	@$(CC) $(CFLAGS) $^ -o $@ $(LDFLAGS)

$(BUILD_DIR)/test_capability_v2: $(KERNEL_DIR)/test_capability_v2.c $(BUILD_DIR)/capability_v2.o $(BUILD_DIR)/q16_octonion.o $(BUILD_DIR)/q16_fixed.o $(BUILD_DIR)/resource_vector.o
	@echo "LINK $@"
	@$(CC) $(CFLAGS) $^ -o $@ $(LDFLAGS)

$(BUILD_DIR)/test_dag_pdac: $(KERNEL_DIR)/test_dag_pdac.c $(BUILD_DIR)/dag_pdac.o $(BUILD_DIR)/capability_v2.o $(BUILD_DIR)/resource_vector.o $(BUILD_DIR)/q16_octonion.o $(BUILD_DIR)/q16_fixed.o
	@echo "LINK $@"
	@$(CC) $(CFLAGS) $^ -o $@ $(LDFLAGS)

$(BUILD_DIR)/test_scheduler: $(KERNEL_DIR)/test_scheduler.c $(BUILD_DIR)/sched_lottery.o $(BUILD_DIR)/sched_beatty.o $(BUILD_DIR)/sched_hybrid.o $(BUILD_DIR)/sched_admission.o $(BUILD_DIR)/lcg.o $(BUILD_DIR)/dag_pdac.o $(BUILD_DIR)/capability_v2.o $(BUILD_DIR)/resource_vector.o $(BUILD_DIR)/q16_octonion.o $(BUILD_DIR)/q16_fixed.o
	@echo "LINK $@"
	@$(CC) $(CFLAGS) $^ -o $@ $(LDFLAGS)

$(BUILD_DIR)/test_executor: $(KERNEL_DIR)/test_executor.c $(CORE_OBJS)
	@echo "LINK $@"
	@$(CC) $(CFLAGS) $^ -o $@ $(LDFLAGS)

$(BUILD_DIR)/test_lockfree: $(KERNEL_DIR)/test_lockfree.c $(BUILD_DIR)/lockfree.o
	@echo "LINK $@"
	@$(CC) $(CFLAGS) $^ -o $@ $(LDFLAGS)

$(BUILD_DIR)/test_rcu: $(KERNEL_DIR)/test_rcu.c $(BUILD_DIR)/rcu_pdac.o $(BUILD_DIR)/lockfree.o
	@echo "LINK $@"
	@$(CC) $(CFLAGS) $^ -o $@ $(LDFLAGS)

$(BUILD_DIR)/test_work_stealing: $(KERNEL_DIR)/test_work_stealing.c $(BUILD_DIR)/work_stealing.o $(BUILD_DIR)/rcu_pdac.o $(BUILD_DIR)/lockfree.o
	@echo "LINK $@"
	@$(CC) $(CFLAGS) $^ -o $@ $(LDFLAGS)

$(BUILD_DIR)/test_integration_phase5: $(KERNEL_DIR)/test_integration_phase5.c $(BUILD_DIR)/work_stealing.o $(BUILD_DIR)/rcu_pdac.o $(BUILD_DIR)/lockfree.o
	@echo "LINK $@"
	@$(CC) $(CFLAGS) $^ -o $@ $(LDFLAGS)

# Example build rules
$(BUILD_DIR)/example_phase3: $(KERNEL_DIR)/example_phase3.c $(CORE_OBJS)
	@echo "LINK $@"
	@$(CC) $(CFLAGS) $^ -o $@ $(LDFLAGS)

$(BUILD_DIR)/example_phase4: $(KERNEL_DIR)/example_phase4.c $(CORE_OBJS)
	@echo "LINK $@"
	@$(CC) $(CFLAGS) $^ -o $@ $(LDFLAGS)

$(BUILD_DIR)/example_phase5_advanced: $(KERNEL_DIR)/example_phase5_advanced.c $(LOCKFREE_OBJS)
	@echo "LINK $@"
	@$(CC) $(CFLAGS) $^ -o $@ $(LDFLAGS)

# Test targets
.PHONY: test
test: $(TESTS)
	@echo "========================================="
	@echo "Running PDAC Test Suite"
	@echo "========================================="
	@for test in $(TESTS); do \
		echo ""; \
		echo "Running $$test..."; \
		./$$test || exit 1; \
	done
	@echo ""
	@echo "========================================="
	@echo "All tests passed!"
	@echo "========================================="

.PHONY: test-lockfree
test-lockfree: $(BUILD_DIR)/test_lockfree
	@echo "========================================="
	@echo "Running Lock-Free Tests"
	@echo "========================================="
	@./$(BUILD_DIR)/test_lockfree

.PHONY: test-phase3
test-phase3: $(BUILD_DIR)/test_scheduler
	@./$(BUILD_DIR)/test_scheduler

.PHONY: test-phase4
test-phase4: $(BUILD_DIR)/test_executor
	@./$(BUILD_DIR)/test_executor

.PHONY: test-rcu
test-rcu: $(BUILD_DIR)/test_rcu
	@echo "========================================="
	@echo "Running RCU Tests"
	@echo "========================================="
	@./$(BUILD_DIR)/test_rcu

.PHONY: test-work-stealing
test-work-stealing: $(BUILD_DIR)/test_work_stealing
	@echo "========================================="
	@echo "Running Work-Stealing Tests"
	@echo "========================================="
	@./$(BUILD_DIR)/test_work_stealing

.PHONY: test-integration
test-integration: $(BUILD_DIR)/test_integration_phase5
	@echo "========================================="
	@echo "Running Phase 5 Integration Tests"
	@echo "========================================="
	@./$(BUILD_DIR)/test_integration_phase5

.PHONY: test-phase5
test-phase5: test-lockfree test-rcu test-work-stealing test-integration

# Run examples
.PHONY: examples
examples: $(EXAMPLES)
	@echo "Running Phase 3 examples..."
	@./$(BUILD_DIR)/example_phase3
	@echo ""
	@echo "Running Phase 4 examples..."
	@./$(BUILD_DIR)/example_phase4
	@echo ""
	@echo "Running Phase 5 advanced examples..."
	@./$(BUILD_DIR)/example_phase5_advanced

# Clean
.PHONY: clean
clean:
	@echo "Cleaning build artifacts..."
	@rm -rf $(BUILD_DIR)
	@echo "Clean complete"

# Rebuild
.PHONY: rebuild
rebuild: clean all

# Help
.PHONY: help
help:
	@echo "PDAC Build System"
	@echo "================="
	@echo ""
	@echo "Targets:"
	@echo "  all             - Build all components (default)"
	@echo "  lockfree        - Build Phase 5 lock-free components"
	@echo "  test            - Run all tests"
	@echo "  test-lockfree   - Run lock-free tests only"
	@echo "  test-phase3     - Run Phase 3 scheduler tests"
	@echo "  test-phase4     - Run Phase 4 executor tests"
	@echo "  test-phase5     - Run Phase 5 lock-free tests"
	@echo "  examples        - Run all examples"
	@echo "  clean           - Remove build artifacts"
	@echo "  rebuild         - Clean and build all"
	@echo "  help            - Show this help message"
	@echo ""
	@echo "Components:"
	@echo "  Phase 1-2: Fixed-point math, octonions, capabilities"
	@echo "  Phase 3:   Lottery/Beatty/Hybrid schedulers"
	@echo "  Phase 4:   DAG executor, telemetry"
	@echo "  Phase 5:   Lock-free data structures (IN PROGRESS)"

.PHONY: info
info:
	@echo "PDAC Project Information"
	@echo "========================"
	@echo "Compiler:  $(CC)"
	@echo "CFLAGS:    $(CFLAGS)"
	@echo "LDFLAGS:   $(LDFLAGS)"
	@echo "Objects:   $(words $(ALL_OBJS)) total"
	@echo "Tests:     $(words $(TESTS)) test suites"
	@echo "Examples:  $(words $(EXAMPLES)) examples"
