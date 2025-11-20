# Strict Warning Configuration for ExoV6
# Rust-level strictness for C17

# Base warning flags (enabled for all builds)
set(EXOV6_BASE_WARNINGS
    -Wall                    # Enable all standard warnings
    -Wextra                  # Enable extra warnings
    -Wpedantic               # ISO C compliance warnings
    -Wshadow                 # Warn about variable shadowing
    -Wcast-align             # Warn about pointer cast alignment
    -Wcast-qual              # Warn about discarded qualifiers
    -Wconversion             # Warn about implicit conversions
    -Wsign-conversion        # Warn about sign conversions
    -Wdouble-promotion       # Warn about float to double promotion
    -Wformat=2               # Extra format string checking
    -Wnull-dereference       # Warn about null pointer dereference
    -Wunused                 # Warn about unused entities
    -Wundef                  # Warn about undefined macros
    -Wwrite-strings          # Warn about string literal modifications
)

# Strict mode: treat warnings as errors
set(EXOV6_STRICT_FLAGS
    -Werror                  # Treat ALL warnings as errors
)

# Flags to disable (too noisy or false positives for kernel code)
set(EXOV6_DISABLED_WARNINGS
    -Wno-unused-parameter    # Many kernel APIs have unused params
    -Wno-sign-conversion     # Too noisy for kernel pointer arithmetic
    -Wno-conversion          # Too noisy for kernel code
)
