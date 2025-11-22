# Topic Overlaps & Shared Sections

Sections detected with identical normalized content across multiple sources.

_Top 50 clusters shown._

## Table Structure

> ```c

**Occurrences:**
- `docs/CAPABILITY_MODEL.md` · Capability Security Model (Architecture & Implementation)
- `docs/OPTIMIZATION_GUIDE.md` · EXOV6 Optimization Guide (General & Misc)
- `docs/PHASE3_COMPLETION_REPORT.md` · Phase 3 Completion Report: LWKT Token Implementation (Analyses & Audits)
- `doc/phoenixkernel.md` · FeuerBird Kernel Overview (Architecture & Implementation)
- `doc/profiling_metrics.md` · Profiling Metrics (General & Misc)
- `doc/arbitration.md` · Arbitration Table (General & Misc)
- `archive/documentation_consolidated/UNIFIED_ARCHITECTURE_SYNTHESIS.md` · ExoV6 Unified Architecture Synthesis (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_doc_phoenixkernel.md` · Analysis Report: `read_file` for `doc/phoenixkernel.md` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/kernel_memory_management/read_file_kernel_vm_c.md` · Analysis Report: `read_file` for `kernel/vm.c` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/kernel_memory_management/read_file_kernel_mmu64_c.md` · Analysis Report: `read_file` for `kernel/mmu64.c` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/kernel_memory_management/read_file_kernel_mmu_h.md` · Analysis Report: `read_file` for `kernel/mmu.h` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/kernel_memory_management/read_file_include_memlayout_h.md` · Analysis Report: `read_file` for `include/memlayout.h` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/kernel_boot_and_core_headers/read_file_include_exokernel.md` · Analysis Report: `read_file` for `include/exokernel.h` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/kernel_boot_and_core_headers/read_file_include_defs.md` · Analysis Report: `read_file` for `include/defs.h` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/kernel_boot_and_core_headers/read_file_kernel_main64.md` · Analysis Report: `read_file` for `kernel/main64.c` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/kernel_boot_and_core_headers/read_file_kernel_main.md` · Analysis Report: `read_file` for `kernel/main.c` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/exokernel_analysis/read_file_include_exo_mem_h.md` · Analysis Report: `read_file` for `include/exo_mem.h` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/exokernel_analysis/read_file_include_capwrap_h.md` · Analysis Report: `read_file` for `include/capwrap.h` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/exokernel_analysis/read_file_kernel_exo_ipc_c.md` · Analysis Report: `read_file` for `kernel/exo_ipc.c` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/exokernel_analysis/read_file_kernel_zone_c.md` · Analysis Report: `read_file` for `kernel/zone.c` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/exokernel_analysis/read_file_include_exo_stream_h.md` · Analysis Report: `read_file` for `include/exo_stream.h` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/exokernel_analysis/read_file_kernel_irq_c.md` · Analysis Report: `read_file` for `kernel/irq.c` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/exokernel_analysis/read_file_kernel_zone_h.md` · Analysis Report: `read_file` for `kernel/zone.h` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/exokernel_analysis/read_file_kernel_hypervisor_hypervisor_h.md` · Analysis Report: `read_file` for `kernel/hypervisor/hypervisor.h` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/exokernel_analysis/read_file_kernel_exo_disk_c.md` · Analysis Report: `read_file` for `kernel/exo_disk.c` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/exokernel_analysis/read_file_kernel_msg_router_c.md` · Analysis Report: `read_file` for `kernel/msg_router.c` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/exokernel_analysis/read_file_include_caplib_h.md` · Analysis Report: `read_file` for `include/caplib.h` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/exokernel_analysis/read_file_kernel_exo_ipc_queue_c.md` · Analysis Report: `read_file` for `kernel/exo_ipc_queue.c` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/exokernel_analysis/read_file_kernel_exo_stream_c.md` · Analysis Report: `read_file` for `kernel/exo_stream.c` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/exokernel_analysis/read_file_kernel_beatty_sched_c.md` · Analysis Report: `read_file` for `kernel/beatty_sched.c` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/exokernel_analysis/read_file_kernel_proc_c.md` · Analysis Report: `read_file` for `kernel/proc.c` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/exokernel_analysis/read_file_include_chan_h.md` · Analysis Report: `read_file` for `include/chan.h` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/exokernel_analysis/read_file_kernel_exo_cpu_c.md` · Analysis Report: `read_file` for `kernel/exo_cpu.c` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/exokernel_analysis/read_file_include_exokernel_h_exokernel_focus.md` · Analysis Report: `read_file` for `include/exokernel.h` (Exokernel Focus) (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/exokernel_analysis/read_file_kernel_lambda_cap_c.md` · Analysis Report: `read_file` for `kernel/lambda_cap.c` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/exokernel_analysis/read_file_include_cap_h.md` · Analysis Report: `read_file` for `include/cap.h` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/exokernel_analysis/read_file_include_sched_h.md` · Analysis Report: `read_file` for `include/sched.h` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/exokernel_analysis/read_file_kernel_cap_c.md` · Analysis Report: `read_file` for `kernel/cap.c` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/exokernel_analysis/read_file_kernel_exo_c.md` · Analysis Report: `read_file` for `kernel/exo.c` (Architecture & Implementation)

## Quick Start

> ```bash

**Occurrences:**
- `README.md` · ExoV6: The POSIX 2024 Exokernel Renaissance (Standards & Compliance)
- `docs/PHASE8_VALIDATION_PLAN.md` · Phase 8: Real-World Validation and Testing (Roadmaps & Plans)
- `docs/C17_POSIX2024_ROADMAP.md` · C17/POSIX-2024 Native Implementation Roadmap (Roadmaps & Plans)
- `docs/MODERNIZATION_ROADMAP.md` · ExoV6 Modernization Roadmap: Building a Modern Exokernel for i386/x86_64 QEMU (Roadmaps & Plans)
- `docs/PHASE8_IMMEDIATE_NEXT_STEPS.md` · Phase 8: Immediate Next Steps - Tactical Execution Plan (Roadmaps & Plans)
- `docs/LOCK_MODERNIZATION_SUMMARY.md` · ExoV6 Lock Modernization - Session Summary (Temporal Sessions)
- `docs/OPTIMIZATION_GUIDE.md` · EXOV6 Optimization Guide (General & Misc)
- `docs/modern_build_system.md` · Modern LLVM Build System Guide (General & Misc)
- `docs/POSIX_IMPLEMENTATION_ROADMAP.md` · POSIX-2024 Complete Implementation Roadmap (Roadmaps & Plans)
- `docs/PDAC_PROJECT_SUMMARY.md` · PDAC Project: Complete Summary (General & Misc)
- `docs/DOCUMENTATION.md` · ExoV6 Operating System - Complete Documentation (General & Misc)
- `docs/EXOV6_MODERN_OS_SYNTHESIS.md` · ExoV6 (FeuerBirdOS) - Modern Operating System Synthesis (General & Misc)
- `docs/LOCK_MODERNIZATION_DESIGN.md` · ExoV6 Lock Modernization: Novel Synthesis Design (Architecture & Implementation)
- `docs/PHASE5.2_PROC_VALIDATION.md` · Phase 5.2: Process Structure Integration Validation (General & Misc)
- `doc/QEMU_DOCKER_I386.md` · i386 QEMU-in-Docker Integration Guide (General & Misc)
- `doc/QEMU_INTEGRATION.md` · QEMU Integration Guide for ExoV6 (General & Misc)
- `archive/docs_old/BUILD_PROGRESS_SESSION3.md` · ExoV6 x86_64 Build Progress - Session 3 (Temporal Sessions)
- `archive/docs_old/README_old_backup.md` · ExoV6: The Unix Renaissance (Legacy Archive)
- `archive/documentation_consolidated/setup.md` · FeuerBird Development Environment Setup Guide (Legacy Archive)
- `archive/documentation_consolidated/EXOKERNEL_SYNTHESIS_2024.md` · 🚀 ExoV6 Kernel: Complete Architectural Synthesis 2024 (Architecture & Implementation)
- `archive/documentation_consolidated/PROJECT_SYNTHESIS_MASTER_PLAN.md` · 🎯 ExoV6 Project Synthesis: Master Implementation Plan (Roadmaps & Plans)
- `archive/documentation_consolidated/CODEX.md` · OpenAI Codex Instructions (Legacy Archive)
- `archive/documentation_consolidated/CONTRIBUTING.md` · Contributing to FeuerBird Exokernel (Architecture & Implementation)
- `archive/documentation_consolidated/README_old.md` · FeuerBird Exokernel Operating System (Architecture & Implementation)
- `archive/documentation_consolidated/HEADER_REORGANIZATION_PLAN.md` · ExoV6 Header Reorganization Master Plan (Roadmaps & Plans)
- `archive/documentation_consolidated/CLAUDE.md` · Claude Code Instructions (Legacy Archive)
- `archive/legacy_documentation/GRANULAR_IMPLEMENTATION_ROADMAP.md` · GRANULAR IMPLEMENTATION ROADMAP - ExoKernel v6 (Roadmaps & Plans)
- `archive/legacy_documentation/ARCHITECTURE.md` · FeuerBird Exokernel Architecture (Architecture & Implementation)
- `archive/legacy_documentation/REORGANIZATION_PLAN.md` · Repository Reorganization Plan (Roadmaps & Plans)
- `archive/legacy_documentation/setup.md` · FeuerBird Development Environment Setup Guide (Legacy Archive)
- `archive/legacy_documentation/BUILD_DIRECTORY_BEST_PRACTICES.md` · Build Directory Best Practices for ExoKernel OS (Architecture & Implementation)
- `archive/legacy_documentation/CPP23_CONVERSION_GUIDE.md` · C++23 Conversion Guidelines for FeuerBird (Legacy Archive)
- `archive/legacy_documentation/BUILD_INTEGRATION.md` · Build System Integration for C++23 Migration (Legacy Archive)
- `archive/legacy_documentation/BUILD_ANALYSIS.md` · Build System Analysis and Modernization Strategy (Analyses & Audits)
- `archive/legacy_documentation/PHASE_1_3_DETAILED_ROADMAP.md` · PHASES 1-3 DETAILED IMPLEMENTATION ROADMAP (Roadmaps & Plans)

## In another terminal: gdb kernel.elf -ex "target remote :1234"

> ```

**Occurrences:**
- `README.md` · ExoV6: The POSIX 2024 Exokernel Renaissance (Standards & Compliance)
- `user/README.md` · ExoV6 Userland - Modern Organization (General & Misc)
- `docs/PHASE8_VALIDATION_PLAN.md` · Phase 8: Real-World Validation and Testing (Roadmaps & Plans)
- `docs/LOCK_IMPLEMENTATION_ROADMAP.md` · ExoV6 Lock Implementation Roadmap - Option A (Roadmaps & Plans)
- `docs/ZONE_BOUNDARIES.md` · Zone Boundary Documentation (General & Misc)
- `docs/C17_POSIX2024_ROADMAP.md` · C17/POSIX-2024 Native Implementation Roadmap (Roadmaps & Plans)
- `docs/MODERNIZATION_ROADMAP.md` · ExoV6 Modernization Roadmap: Building a Modern Exokernel for i386/x86_64 QEMU (Roadmaps & Plans)
- `docs/PHASE8_IMMEDIATE_NEXT_STEPS.md` · Phase 8: Immediate Next Steps - Tactical Execution Plan (Roadmaps & Plans)
- `docs/PHASE1_EXECUTION_PLAN.md` · Phase 1 Execution Plan: NUMA-Aware QSpinlock (Roadmaps & Plans)
- `docs/PHASE4_COMPLETION_REPORT.md` · Phase 4 Completion Report: DAG Lock Ordering (Architecture & Implementation)
- `docs/OPTIMIZATION_GUIDE.md` · EXOV6 Optimization Guide (General & Misc)
- `docs/PHASE6-9_EXECUTION_PLAN.md` · Phases 6-9 Execution Plan (Roadmaps & Plans)
- `doc/QEMU_DOCKER_I386.md` · i386 QEMU-in-Docker Integration Guide (General & Misc)
- `archive/docs_old/SESSION_SUCCESS_SUMMARY.md` · ExoV6 Build Session - Complete Success Summary (Temporal Sessions)
- `archive/docs_old/BUILD_PROGRESS_SESSION3.md` · ExoV6 x86_64 Build Progress - Session 3 (Temporal Sessions)
- `archive/docs_old/README_old_backup.md` · ExoV6: The Unix Renaissance (Legacy Archive)
- `archive/documentation_consolidated/C17_POSIX2024_UNIFIED_PLAN.md` · C17 + POSIX-2024 Unified Implementation Plan (Roadmaps & Plans)
- `archive/documentation_consolidated/setup.md` · FeuerBird Development Environment Setup Guide (Legacy Archive)
- `archive/documentation_consolidated/EXOKERNEL_SYNTHESIS_2024.md` · 🚀 ExoV6 Kernel: Complete Architectural Synthesis 2024 (Architecture & Implementation)
- `archive/documentation_consolidated/UNIFIED_ARCHITECTURE_SYNTHESIS.md` · ExoV6 Unified Architecture Synthesis (Architecture & Implementation)
- `archive/legacy_documentation/setup.md` · FeuerBird Development Environment Setup Guide (Legacy Archive)
- `archive/legacy_documentation/BUILD_ANALYSIS.md` · Build System Analysis and Modernization Strategy (Analyses & Audits)
- `archive/legacy_documentation/analysis_reports/kernel_memory_management/read_file_kernel_mmu64_c.md` · Analysis Report: `read_file` for `kernel/mmu64.c` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/kernel_memory_management/read_file_kernel_mmu_h.md` · Analysis Report: `read_file` for `kernel/mmu.h` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/kernel_memory_management/read_file_include_memlayout_h.md` · Analysis Report: `read_file` for `include/memlayout.h` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/kernel_boot_and_core_headers/read_file_include_defs.md` · Analysis Report: `read_file` for `include/defs.h` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/exokernel_analysis/read_file_kernel_zone_h.md` · Analysis Report: `read_file` for `kernel/zone.h` (Architecture & Implementation)

## Output:

> ```markdown

**Occurrences:**
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_doc_IPC.md` · Analysis Report: `read_file` for `doc/IPC.md` (Analyses & Audits)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_docs_architecture_design_implementation.md` · Analysis Report: `read_file` for `docs/architecture_design_implementation.md` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_doc_roadmap.md` · Analysis Report: `read_file` for `doc/roadmap.md` (Roadmaps & Plans)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_doc_multi_architecture.md` · Analysis Report: `read_file` for `doc/multi_architecture.md` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_doc_hypervisor.md` · Analysis Report: `read_file` for `doc/hypervisor.md` (Analyses & Audits)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_doc_charter.md` · Analysis Report: `read_file` for `doc/charter.md` (Analyses & Audits)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_doc_rcrs.md` · Analysis Report: `read_file` for `doc/rcrs.md` (Analyses & Audits)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_doc_formal_models.md` · Analysis Report: `read_file` for `doc/formal_models.md` (Analyses & Audits)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_docs_analytical_performance_bounds.md` · Analysis Report: `read_file` for `docs/analytical_performance_bounds.md` (Analyses & Audits)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_doc_developer_guides.md` · Analysis Report: `read_file` for `doc/developer_guides.md` (Analyses & Audits)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_doc_minix3_concepts.md` · Analysis Report: `read_file` for `doc/minix3_concepts.md` (Analyses & Audits)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_doc_phoenixkernel.md` · Analysis Report: `read_file` for `doc/phoenixkernel.md` (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_doc_posix_compat.md` · Analysis Report: `read_file` for `doc/posix_compat.md` (Standards & Compliance)

## 4.1 CMake Configuration (kernel/CMakeLists.txt:229-244)

> ```cmake

**Occurrences:**
- `docs/DAG_DESIGN.md` · DAG Lock Ordering: A Line-by-Line Commentary (Architecture & Implementation)
- `archive/documentation_consolidated/ULTIMATE_LOCK_SYNTHESIS_COMPLETE.md` · Ultimate Lock Synthesis - Complete Implementation Report (Architecture & Implementation)
- `archive/documentation_consolidated/C17_POSIX2024_UNIFIED_PLAN.md` · C17 + POSIX-2024 Unified Implementation Plan (Roadmaps & Plans)
- `archive/documentation_consolidated/COMPLETE_UNIX_POSIX_IMPLEMENTATION_PLAN.md` · Complete UNIX/POSIX Implementation Plan (Roadmaps & Plans)
- `archive/documentation_consolidated/EXOKERNEL_SYNTHESIS_2024.md` · 🚀 ExoV6 Kernel: Complete Architectural Synthesis 2024 (Architecture & Implementation)
- `archive/documentation_consolidated/HEADER_REORGANIZATION_PLAN.md` · ExoV6 Header Reorganization Master Plan (Roadmaps & Plans)
- `archive/documentation_consolidated/UNIFIED_ARCHITECTURE_SYNTHESIS.md` · ExoV6 Unified Architecture Synthesis (Architecture & Implementation)
- `archive/legacy_documentation/UNIFIED_ARCHITECTURE_VISION.md` · FeuerBird ExoKernel v6: Unified Architecture Vision (Architecture & Implementation)
- `archive/legacy_documentation/BUILD_DIRECTORY_BEST_PRACTICES.md` · Build Directory Best Practices for ExoKernel OS (Architecture & Implementation)
- `archive/legacy_documentation/BUILD_ANALYSIS.md` · Build System Analysis and Modernization Strategy (Analyses & Audits)

## Phases A, B, C Complete

> ---

**Occurrences:**
- `docs/SESSION_SUMMARY_PHASE_ABC_2025-11-19.md` · Session Summary: Task 5.5.3 Optimization Implementation (Temporal Sessions)
- `docs/PHASE1_EXECUTION_PLAN.md` · Phase 1 Execution Plan: NUMA-Aware QSpinlock (Roadmaps & Plans)
- `docs/LONG_TERM_ROADMAP.md` · ExoV6 Kernel Modernization: Long-Term Roadmap (Roadmaps & Plans)
- `docs/MASTER_TODO_2025.md` · Master TODO List: FeuerBird LibOS 2025 (Architecture & Implementation)
- `archive/docs_old/BUILD_PROGRESS_SESSION3.md` · ExoV6 x86_64 Build Progress - Session 3 (Temporal Sessions)

## endif

> ``` ---

**Occurrences:**
- `docs/PHASE4_EXECUTION_PLAN.md` · Phase 4 Execution Plan: DAG Integration for Deadlock Prevention (Roadmaps & Plans)
- `docs/PHASE1_EXECUTION_PLAN.md` · Phase 1 Execution Plan: NUMA-Aware QSpinlock (Roadmaps & Plans)
- `docs/EXOV6_C17_QUALITY_IMPROVEMENTS.md` · ExoV6 C17 Code Quality Improvements (General & Misc)
- `docs/OPTIMIZATION_GUIDE.md` · EXOV6 Optimization Guide (General & Misc)
- `docs/PHASE3_EXECUTION_PLAN.md` · Phase 3 Execution Plan: LWKT Token Implementation (Roadmaps & Plans)

## Run workload

> make qemu

**Occurrences:**
- `docs/DOCUMENTATION.md` · ExoV6 Operating System - Complete Documentation (General & Misc)
- `doc/QEMU_INTEGRATION.md` · QEMU Integration Guide for ExoV6 (General & Misc)
- `archive/docs_old/README_old_backup.md` · ExoV6: The Unix Renaissance (Legacy Archive)
- `archive/documentation_consolidated/EXOKERNEL_SYNTHESIS_2024.md` · 🚀 ExoV6 Kernel: Complete Architectural Synthesis 2024 (Architecture & Implementation)
- `archive/legacy_documentation/REORGANIZATION_PLAN.md` · Repository Reorganization Plan (Roadmaps & Plans)

## Run in QEMU

> cmake --build . --target qemu

**Occurrences:**
- `archive/documentation_consolidated/CODEX.md` · OpenAI Codex Instructions (Legacy Archive)
- `archive/documentation_consolidated/CONTRIBUTING.md` · Contributing to FeuerBird Exokernel (Architecture & Implementation)
- `archive/documentation_consolidated/GEMINI.md` · Gemini AI Instructions (Legacy Archive)
- `archive/documentation_consolidated/README_old.md` · FeuerBird Exokernel Operating System (Architecture & Implementation)
- `archive/documentation_consolidated/CLAUDE.md` · Claude Code Instructions (Legacy Archive)

## Test with QEMU multi-socket

> qemu-system-x86_64 -smp 16,sockets=2,cores=4,threads=2 \ -numa node,mem=2G,cpus=0-7 \ -numa node,mem=2G,cpus=8-15

**Occurrences:**
- `docs/LOCK_IMPLEMENTATION_ROADMAP.md` · ExoV6 Lock Implementation Roadmap - Option A (Roadmaps & Plans)
- `docs/PHASE1_EXECUTION_PLAN.md` · Phase 1 Execution Plan: NUMA-Aware QSpinlock (Roadmaps & Plans)
- `docs/LOCK_MODERNIZATION_SUMMARY.md` · ExoV6 Lock Modernization - Session Summary (Temporal Sessions)
- `docs/LOCK_MODERNIZATION_DESIGN.md` · ExoV6 Lock Modernization: Novel Synthesis Design (Architecture & Implementation)

## Complete test suite

> ctest -V

**Occurrences:**
- `archive/documentation_consolidated/CONTRIBUTING.md` · Contributing to FeuerBird Exokernel (Architecture & Implementation)
- `archive/documentation_consolidated/README_old.md` · FeuerBird Exokernel Operating System (Architecture & Implementation)
- `archive/documentation_consolidated/CLAUDE.md` · Claude Code Instructions (Legacy Archive)
- `archive/legacy_documentation/REORGANIZATION_PLAN.md` · Repository Reorganization Plan (Roadmaps & Plans)

## Clone repository

> git clone https://github.com/Oichkatzelesfrettschen/exov6.git cd exov6

**Occurrences:**
- `README.md` · ExoV6: The POSIX 2024 Exokernel Renaissance (Standards & Compliance)
- `docs/EXOV6_MODERN_OS_SYNTHESIS.md` · ExoV6 (FeuerBirdOS) - Modern Operating System Synthesis (General & Misc)
- `doc/QEMU_DOCKER_I386.md` · i386 QEMU-in-Docker Integration Guide (General & Misc)

## Run in QEMU

> ninja qemu-nox

**Occurrences:**
- `README.md` · ExoV6: The POSIX 2024 Exokernel Renaissance (Standards & Compliance)
- `docs/MODERNIZATION_ROADMAP.md` · ExoV6 Modernization Roadmap: Building a Modern Exokernel for i386/x86_64 QEMU (Roadmaps & Plans)
- `docs/EXOV6_MODERN_OS_SYNTHESIS.md` · ExoV6 (FeuerBirdOS) - Modern Operating System Synthesis (General & Misc)

## Debug with GDB

> ninja qemu-debug

**Occurrences:**
- `README.md` · ExoV6: The POSIX 2024 Exokernel Renaissance (Standards & Compliance)
- `docs/MODERNIZATION_ROADMAP.md` · ExoV6 Modernization Roadmap: Building a Modern Exokernel for i386/x86_64 QEMU (Roadmaps & Plans)
- `docs/EXOV6_MODERN_OS_SYNTHESIS.md` · ExoV6 (FeuerBirdOS) - Modern Operating System Synthesis (General & Misc)

## ifdef USE_DAG_CHECKING

> dag_lock_acquired(lock, lock->name, lock->dag_level, LOCK_TYPE_QSPIN, __FILE__, __LINE__);

**Occurrences:**
- `docs/PHASE4_EXECUTION_PLAN.md` · Phase 4 Execution Plan: DAG Integration for Deadlock Prevention (Roadmaps & Plans)
- `docs/PHASE4_COMPLETION_REPORT.md` · Phase 4 Completion Report: DAG Lock Ordering (Architecture & Implementation)
- `docs/DAG_DESIGN.md` · DAG Lock Ordering: A Line-by-Line Commentary (Architecture & Implementation)

## Build

> cmake --build . -j$(nproc)

**Occurrences:**
- `docs/DOCUMENTATION.md` · ExoV6 Operating System - Complete Documentation (General & Misc)
- `archive/documentation_consolidated/README_old.md` · FeuerBird Exokernel Operating System (Architecture & Implementation)
- `archive/legacy_documentation/BUILD_DIRECTORY_BEST_PRACTICES.md` · Build Directory Best Practices for ExoKernel OS (Architecture & Implementation)

## Run under GDB

> make qemu-gdb

**Occurrences:**
- `docs/DOCUMENTATION.md` · ExoV6 Operating System - Complete Documentation (General & Misc)
- `doc/QEMU_INTEGRATION.md` · QEMU Integration Guide for ExoV6 (General & Misc)
- `archive/docs_old/README_old_backup.md` · ExoV6: The Unix Renaissance (Legacy Archive)

## Executive Vision

> ExoV6 represents the ultimate synthesis of Unix philosophy with cutting-edge computer science, creating a **POSIX 2024 (IEEE Std 1003.1-2024/SUSv5)** compliant exokernel that transcends traditional OS

**Occurrences:**
- `README.md` · ExoV6: The POSIX 2024 Exokernel Renaissance (Standards & Compliance)
- `archive/docs_old/README_old_backup.md` · ExoV6: The Unix Renaissance (Legacy Archive)

## Test token behavior

> ./kernel/sync/test_lwkt_token

**Occurrences:**
- `docs/PHASE8_VALIDATION_PLAN.md` · Phase 8: Real-World Validation and Testing (Roadmaps & Plans)
- `docs/PHASE8_IMMEDIATE_NEXT_STEPS.md` · Phase 8: Immediate Next Steps - Tactical Execution Plan (Roadmaps & Plans)

## Build kernel with DAG checking enabled

> cd /home/user/exov6/build cmake .. -DUSE_DAG_CHECKING=ON -DDAG_PANIC_ON_VIOLATION=ON ninja kernel

**Occurrences:**
- `docs/PHASE8_VALIDATION_PLAN.md` · Phase 8: Real-World Validation and Testing (Roadmaps & Plans)
- `docs/PHASE8_IMMEDIATE_NEXT_STEPS.md` · Phase 8: Immediate Next Steps - Tactical Execution Plan (Roadmaps & Plans)

## 1. Compiler Optimizations

> ```makefile

**Occurrences:**
- `docs/C17_POSIX2024_ROADMAP.md` · C17/POSIX-2024 Native Implementation Roadmap (Roadmaps & Plans)
- `archive/legacy_documentation/BUILD_INTEGRATION.md` · Build System Integration for C++23 Migration (Legacy Archive)

## ifdef USE_DAG_CHECKING

> dag_lock_released(lk); // Track release

**Occurrences:**
- `docs/LOCK_SUBSYSTEM_ROADMAP.md` · ExoV6 Modern Lock Subsystem: Strategic Roadmap (Phases 5-9) (Roadmaps & Plans)
- `docs/PHASE6-9_EXECUTION_PLAN.md` · Phases 6-9 Execution Plan (Roadmaps & Plans)

## Build kernel

> ninja kernel

**Occurrences:**
- `docs/MODERNIZATION_ROADMAP.md` · ExoV6 Modernization Roadmap: Building a Modern Exokernel for i386/x86_64 QEMU (Roadmaps & Plans)
- `docs/EXOV6_MODERN_OS_SYNTHESIS.md` · ExoV6 (FeuerBirdOS) - Modern Operating System Synthesis (General & Misc)

## ifdef USE_DAG_CHECKING

> dag_lock_released(lock);

**Occurrences:**
- `docs/PHASE4_EXECUTION_PLAN.md` · Phase 4 Execution Plan: DAG Integration for Deadlock Prevention (Roadmaps & Plans)
- `docs/PHASE4_COMPLETION_REPORT.md` · Phase 4 Completion Report: DAG Lock Ordering (Architecture & Implementation)

## ifdef USE_DAG_CHECKING

> struct proc *p = myproc(); if (p) { return &p->lock_tracker; }

**Occurrences:**
- `docs/PHASE4_EXECUTION_PLAN.md` · Phase 4 Execution Plan: DAG Integration for Deadlock Prevention (Roadmaps & Plans)
- `docs/DAG_DESIGN.md` · DAG Lock Ordering: A Line-by-Line Commentary (Architecture & Implementation)

## ifdef ENABLE_EXOLOCK_FS

> struct exo_lock fs_lock;

**Occurrences:**
- `docs/PHASE1_COMPLETION_REPORT.md` · ExoV6 Lock Modernization - Phase 1 Completion Report (Architecture & Implementation)
- `docs/LOCK_MODERNIZATION_SUMMARY.md` · ExoV6 Lock Modernization - Session Summary (Temporal Sessions)

## else

> struct spinlock fs_lock;

**Occurrences:**
- `docs/PHASE1_COMPLETION_REPORT.md` · ExoV6 Lock Modernization - Phase 1 Completion Report (Architecture & Implementation)
- `docs/LOCK_MODERNIZATION_SUMMARY.md` · ExoV6 Lock Modernization - Session Summary (Temporal Sessions)

## 1. Architectural Overview

> FeuerBird follows the exokernel philosophy: the kernel multiplexes hardware resources while a flexible libOS exposes POSIX, BSD, and SVR4 personalities. Capabilities are the fundamental access tokens.

**Occurrences:**
- `docs/architecture_design_implementation.md` · FeuerBird Architecture, Design, and Implementation (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_docs_architecture_design_implementation.md` · Analysis Report: `read_file` for `docs/architecture_design_implementation.md` (Architecture & Implementation)

## 1.1 Kernel Subsystems

> - **Capability System** – manages capability tables and badge tracking. The design is outlined in `doc/formal_delegation_algebra_specification.md` and implemented in `kernel/cap*.c`. - **Typed IPC Cha

**Occurrences:**
- `docs/architecture_design_implementation.md` · FeuerBird Architecture, Design, and Implementation (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_docs_architecture_design_implementation.md` · Analysis Report: `read_file` for `docs/architecture_design_implementation.md` (Architecture & Implementation)

## 1.2 User Space

> User programs link against `libos` which provides the POSIX compatibility layer tracked in `doc/posix_roadmap.md`. Example drivers live in `engine/` and `examples/`.

**Occurrences:**
- `docs/architecture_design_implementation.md` · FeuerBird Architecture, Design, and Implementation (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_docs_architecture_design_implementation.md` · Analysis Report: `read_file` for `docs/architecture_design_implementation.md` (Architecture & Implementation)

## 2. Codebase Metrics

> Recent automated analysis gives a sense of scale: - `cloc` reports **526k** lines of code across **2631** files with **115k** blank lines and **11k** comment lines. - `lizard` scanned **1411** functio

**Occurrences:**
- `docs/architecture_design_implementation.md` · FeuerBird Architecture, Design, and Implementation (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_docs_architecture_design_implementation.md` · Analysis Report: `read_file` for `docs/architecture_design_implementation.md` (Architecture & Implementation)

## 1. Unit Testing

> ```python

**Occurrences:**
- `docs/LIBOS_2025_ARCHITECTURE.md` · LibOS 2025: Next-Generation Library Operating System Architecture (Architecture & Implementation)
- `docs/POSIX_IMPLEMENTATION_ROADMAP.md` · POSIX-2024 Complete Implementation Roadmap (Roadmaps & Plans)

## Purpose

> This document provides an initial analytical performance model, primarily using Big O notation, for key operations within FeuerBird's formally specified domain security lattice, capability delegation 

**Occurrences:**
- `docs/analytical_performance_bounds.md` · Outline of Analytical Performance Bounds for FeuerBird (General & Misc)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_docs_analytical_performance_bounds.md` · Analysis Report: `read_file` for `docs/analytical_performance_bounds.md` (Analyses & Audits)

## Goal

> These preliminary performance bounds serve multiple purposes: - Act as design constraints during the implementation phase. - Aid in reasoning about the scalability and efficiency of the system as the 

**Occurrences:**
- `docs/analytical_performance_bounds.md` · Outline of Analytical Performance Bounds for FeuerBird (General & Misc)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_docs_analytical_performance_bounds.md` · Analysis Report: `read_file` for `docs/analytical_performance_bounds.md` (Analyses & Audits)

## 2. Notation and Assumptions

> The following notation and assumptions are used throughout this analysis: - **`N_caps`**: Total number of capability slots in the system (e.g., `CAP_MAX` from `include/cap.h`). This represents the max

**Occurrences:**
- `docs/analytical_performance_bounds.md` · Outline of Analytical Performance Bounds for FeuerBird (General & Misc)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_docs_analytical_performance_bounds.md` · Analysis Report: `read_file` for `docs/analytical_performance_bounds.md` (Analyses & Audits)

## 3.1. Domain Lattice Operations

> These operations involve comparing or combining the security levels `L(d) = (cls, cats)` of domains. - **`LatticeLeq(d1, d2)`** (Compare security levels of two domains `d1` and `d2`): - Classification

**Occurrences:**
- `docs/analytical_performance_bounds.md` · Outline of Analytical Performance Bounds for FeuerBird (General & Misc)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_docs_analytical_performance_bounds.md` · Analysis Report: `read_file` for `docs/analytical_performance_bounds.md` (Analyses & Audits)

## 3.2. Delegation Algebra Operations

> These operations relate to the creation and validation of capability delegations. - **`DelegateCapability(c_parent, d_target, r_mask)`**: This involves several sub-operations: 1. **Rights Check on `c_

**Occurrences:**
- `docs/analytical_performance_bounds.md` · Outline of Analytical Performance Bounds for FeuerBird (General & Misc)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_docs_analytical_performance_bounds.md` · Analysis Report: `read_file` for `docs/analytical_performance_bounds.md` (Analyses & Audits)

## 3.3. Vector Timestamp (VT) Operations

> These operations assume that domain identifiers can be mapped to vector clock indices in O(1) time (e.g., if domains are numbered `0` to `N_dom-1`). - **`VTLocalEvent(vt_i, domainIndex_i)`** (Domain `

**Occurrences:**
- `docs/analytical_performance_bounds.md` · Outline of Analytical Performance Bounds for FeuerBird (General & Misc)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_docs_analytical_performance_bounds.md` · Analysis Report: `read_file` for `docs/analytical_performance_bounds.md` (Analyses & Audits)

## 3.4. Epoch Synchronization (Conceptual)

> This considers the propagation of epoch updates using the VT protocol. - **Single Epoch Update Propagation (`dSource` informs `dTarget`)**: - `dSource` performs a local event (epoch update, `VTSLocalE

**Occurrences:**
- `docs/analytical_performance_bounds.md` · Outline of Analytical Performance Bounds for FeuerBird (General & Misc)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_docs_analytical_performance_bounds.md` · Analysis Report: `read_file` for `docs/analytical_performance_bounds.md` (Analyses & Audits)

## 3.5. Core Capability Table Operations (from `kernel/cap_table.c`)

> These are based on the current implementation as reviewed. - **`cap_table_alloc()`**: - Current implementation: Linear scan for a free slot. - **Overall Complexity: O(N_caps)**. - Target/Desirable: O(

**Occurrences:**
- `docs/analytical_performance_bounds.md` · Outline of Analytical Performance Bounds for FeuerBird (General & Misc)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_docs_analytical_performance_bounds.md` · Analysis Report: `read_file` for `docs/analytical_performance_bounds.md` (Analyses & Audits)

## 4. Summary Table of Key Operations and Bounds

> | Operation | Current/Estimated Bound | Target/Board Expectation | Notes | |--------------------------------------------|------------------------------|-------------------------------|----------------

**Occurrences:**
- `docs/analytical_performance_bounds.md` · Outline of Analytical Performance Bounds for FeuerBird (General & Misc)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_docs_analytical_performance_bounds.md` · Analysis Report: `read_file` for `docs/analytical_performance_bounds.md` (Analyses & Audits)

## 5. Pedagogical Implications and Design Constraints

> - **Scalability Concerns**: Operations with complexity O(N_dom) (Vector Timestamp operations, Epoch Synchronization) or O(N_caps) (current `cap_table_alloc`) are critical bottlenecks as the number of 

**Occurrences:**
- `docs/analytical_performance_bounds.md` · Outline of Analytical Performance Bounds for FeuerBird (General & Misc)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_docs_analytical_performance_bounds.md` · Analysis Report: `read_file` for `docs/analytical_performance_bounds.md` (Analyses & Audits)

## Developer Guides

> This repository contains assorted tools to help hacking on the code base. One of these tools can generate a visualization of header file dependencies.

**Occurrences:**
- `doc/developer_guides.md` · Developer Guides (General & Misc)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_doc_developer_guides.md` · Analysis Report: `read_file` for `doc/developer_guides.md` (Analyses & Audits)

## FeuerBird Kernel Overview

> The FeuerBird kernel implements an exokernel research platform built on top of the FeuerBird code base.Its goal is to expose low - level hardware resources directly to user space while keeping the in 

**Occurrences:**
- `doc/phoenixkernel.md` · FeuerBird Kernel Overview (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_doc_phoenixkernel.md` · Analysis Report: `read_file` for `doc/phoenixkernel.md` (Architecture & Implementation)

## Capability System

> All privileged operations require an explicit capability token. Capabilities are unforgeable references that encode the rights a holder has over a particular object. They are used to control access to

**Occurrences:**
- `doc/phoenixkernel.md` · FeuerBird Kernel Overview (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_doc_phoenixkernel.md` · Analysis Report: `read_file` for `doc/phoenixkernel.md` (Architecture & Implementation)

## Directory Layout

> A suggested layout for projects building on FeuerBird is: - `kernel/` – core kernel source files - `user/` – user-space programs and the basic C library - `libos/` – the FeuerBird libOS implementing P

**Occurrences:**
- `doc/phoenixkernel.md` · FeuerBird Kernel Overview (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_doc_phoenixkernel.md` · Analysis Report: `read_file` for `doc/phoenixkernel.md` (Architecture & Implementation)

## Building

> Meson and Ninja are the primary tools for building FeuerBird. Configure a build directory and compile the entire system with: ``` meson setup build && ninja -C build ``` This command builds the kernel

**Occurrences:**
- `doc/phoenixkernel.md` · FeuerBird Kernel Overview (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_doc_phoenixkernel.md` · Analysis Report: `read_file` for `doc/phoenixkernel.md` (Architecture & Implementation)

## POSIX Compatibility in User Space

> FeuerBird itself does not provide a POSIX interface. Instead the libOS layers POSIX system calls on top of the capability primitives. Files, processes and IPC endpoints are implemented in user space, 

**Occurrences:**
- `doc/phoenixkernel.md` · FeuerBird Kernel Overview (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_doc_phoenixkernel.md` · Analysis Report: `read_file` for `doc/phoenixkernel.md` (Architecture & Implementation)

## BSD and SVR4 Compatibility Goals

> While the current focus is POSIX emulation, the project also aims to support BSD and System&nbsp; V Release &nbsp;4 personalities entirely in user space. Additional modules under `libos/` will transla

**Occurrences:**
- `doc/phoenixkernel.md` · FeuerBird Kernel Overview (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_doc_phoenixkernel.md` · Analysis Report: `read_file` for `doc/phoenixkernel.md` (Architecture & Implementation)

## Capability Primitives

> The kernel surface is intentionally small. Applications manipulate raw hardware resources via capability objects and a handful of system calls. Each call takes or returns an `exo_cap` structure define

**Occurrences:**
- `doc/phoenixkernel.md` · FeuerBird Kernel Overview (Architecture & Implementation)
- `archive/legacy_documentation/analysis_reports/documentation_analysis/read_file_doc_phoenixkernel.md` · Analysis Report: `read_file` for `doc/phoenixkernel.md` (Architecture & Implementation)
