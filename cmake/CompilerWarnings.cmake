# CompilerWarnings.cmake - Centralized compiler warning configuration
#
# WHY: Compiler warnings can accumulate technical debt and mask real issues.
# This file defines which warnings to enable/disable globally.
#
# WHAT: Manage warning flags, suppress known-benign warnings, enforce -Werror
#
# MANAGED WARNINGS:
# - GNU extensions: #include_next (used in header delegation)
# - C23 attributes: [[nodiscard]], [[maybe_unused]], [[noreturn]]
# - Other warnings: Standard -Wall -Wextra -Wpedantic

include(CheckCCompilerFlag)
include(CheckCXXCompilerFlag)

# Function to check and add compiler flags
function(add_compiler_flag_if_supported flag lang)
    if(lang STREQUAL "C")
        check_c_compiler_flag("${flag}" SUPPORTED_${flag})
        if(SUPPORTED_${flag})
            add_compile_options("${flag}")
        endif()
    elseif(lang STREQUAL "CXX")
        check_cxx_compiler_flag("${flag}" SUPPORTED_${flag})
        if(SUPPORTED_${flag})
            add_compile_options("${flag}")
        endif()
    endif()
endfunction()

# ============================================================================
# PHASE 4B-PRE: Warning Suppression (Temporary Workarounds)
# ============================================================================
#
# These suppressions are SHORT-TERM workarounds for Phase 4B-Pre.
# Long-term solutions tracked in GitHub issues for Phase 5 refactoring.

# Suppress GNU extension warnings
# REASON: Headers use #include_next for delegation to system headers
# PHASE 5 FIX: Refactor header strategy to avoid GNU extensions
# TRACKING: GitHub issue (to be created in Task 5)
if(CMAKE_C_COMPILER_ID MATCHES "Clang")
    add_compiler_flag_if_supported("-Wno-gnu-include-next" C)
    message(STATUS "Warning suppression: -Wno-gnu-include-next (Phase 5 refactoring required)")
endif()

# Suppress C23 attribute warnings
# REASON: Using C23-standard attributes ([[nodiscard]], [[maybe_unused]], etc.)
# PHASE 5 FIX: Option 1 - enable C23 mode; Option 2 - convert to __attribute__
# TRACKING: GitHub issue (to be created in Task 5)
# FILES AFFECTED: compiler_attrs.h, cap_security.h, defs.h, lattice_ipc.h (7),
#                 driver.h (12), boundary_check.h, exo.h, user.h
if(CMAKE_C_COMPILER_ID MATCHES "Clang")
    add_compiler_flag_if_supported("-Wno-c23-extensions" C)
    message(STATUS "Warning suppression: -Wno-c23-extensions (Phase 5 refactoring required)")
endif()

# ============================================================================
# STANDARD WARNING FLAGS (ALL COMPILERS)
# ============================================================================

# Enable common warnings
add_compiler_flag_if_supported("-Wall" C)
add_compiler_flag_if_supported("-Wextra" C)
add_compiler_flag_if_supported("-Wpedantic" C)

# Treat warnings as errors (uncomment to enforce)
# Note: Currently disabled to see full warning scope during Phase 4B-Pre
# Once warnings are resolved, uncomment and enforce in CI
# add_compiler_flag_if_supported("-Werror" C)

message(STATUS "Compiler warnings configured:")
message(STATUS "  - Base warnings: -Wall -Wextra -Wpedantic")
message(STATUS "  - GNU extensions suppressed: -Wno-gnu-include-next")
message(STATUS "  - C23 attributes suppressed: -Wno-c23-extensions")
message(STATUS "  - Treat as errors: DISABLED (Phase 4B-Pre diagnostic mode)")
