# FeuerBird Exokernel - Tool Integration Quick Reference

## Quick Command Reference

### Static Analysis
```bash
# Basic static analysis
ninja -C build static-analysis

# Advanced static analysis (20+ tools)
cmake -B build -DENABLE_ADVANCED_ANALYSIS=ON
ninja -C build advanced-analysis

# Individual tools
ninja -C build clang-tidy
ninja -C build cppcheck
ninja -C build scan-build
ninja -C build infer
ninja -C build flawfinder
ninja -C build semgrep
ninja -C build lizard
```

### Dynamic Analysis
```bash
# Enable Valgrind
cmake -B build -DENABLE_VALGRIND=ON

# Memory leak detection
ninja -C build valgrind

# All Valgrind tools
ninja -C build valgrind-memcheck    # Memory errors
ninja -C build valgrind-cachegrind  # Cache profiling
ninja -C build valgrind-callgrind   # Call graph
ninja -C build valgrind-massif      # Heap profiling
ninja -C build valgrind-helgrind    # Thread analysis
ninja -C build valgrind-drd         # Data races
```

### Performance Profiling
```bash
# Enable profiling
cmake -B build -DENABLE_PROFILING=ON

# CPU profiling
ninja -C build perf-record
ninja -C build perf-report

# Flame graph generation
ninja -C build flamegraph
# View at: build/flamegraph.svg
```

### Formal Verification
```bash
# Enable formal verification
cmake -B build -DENABLE_FORMAL_VERIFICATION=ON

# TLA+ model checking
ninja -C build tla-check

# Z3 SMT verification
ninja -C build z3-check

# Coq proof checking
ninja -C build coq-check

# Frama-C weakest precondition
ninja -C build frama-c-check

# CBMC bounded model checking
ninja -C build cbmc-check

# All formal verification
ninja -C build formal-verification
```

### Code Coverage
```bash
# Enable coverage
cmake -B build -DENABLE_COVERAGE=ON
ninja -C build test
ninja -C build coverage
# View at: build/coverage/html/index.html
```

### Combined Analysis
```bash
# Full analysis (all tools)
cmake -B build -G Ninja \
  -DCMAKE_BUILD_TYPE=Debug \
  -DENABLE_STATIC_ANALYSIS=ON \
  -DENABLE_ADVANCED_ANALYSIS=ON \
  -DENABLE_VALGRIND=ON \
  -DENABLE_PROFILING=ON \
  -DENABLE_FORMAL_VERIFICATION=ON \
  -DENABLE_COVERAGE=ON

ninja -C build
ninja -C build test
ninja -C build static-analysis
ninja -C build advanced-analysis
ninja -C build valgrind
ninja -C build formal-verification
ninja -C build coverage
```

## Tool Summaries

### View Tool Availability
```bash
ninja -C build analysis-summary              # Static analysis tools
ninja -C build advanced-analysis-summary     # Advanced analyzers
ninja -C build dynamic-analysis-summary      # Valgrind, perf, etc.
ninja -C build formal-verification-summary   # TLA+, Z3, Coq, etc.
ninja -C build ccache-info                   # Build cache
```

## Report Locations

### Static Analysis
- `build/cppcheck-report.xml` - cppcheck XML report
- `build/cppcheck-report.txt` - cppcheck text report
- `build/scan-build-results/` - scan-build HTML
- `build/infer-results/` - Infer analysis
- `build/flawfinder-report.html` - Flawfinder HTML
- `build/rats-report.html` - RATS HTML
- `build/lizard-report.html` - Complexity analysis
- `build/semgrep-report.json` - Semgrep JSON

### Dynamic Analysis
- `build/valgrind-memcheck.log` - Memory errors
- `build/valgrind-helgrind.log` - Thread analysis
- `build/valgrind-drd.log` - Data races
- `build/cachegrind.out` - Cache profile
- `build/callgrind.out` - Call graph
- `build/massif.out` - Heap profile
- `build/perf.data` - Performance data
- `build/flamegraph.svg` - Flame graph

### Code Coverage
- `build/coverage/html/index.html` - HTML report
- `build/coverage/coverage.info` - LCOV info
- `build/coverage/merged.profdata` - LLVM profile

## Tool Matrix

| Category | Tools | Count |
|----------|-------|-------|
| **Static Analysis** | clang-tidy, cppcheck, IWYU | 3 |
| **Advanced Static** | scan-build, Infer, Splint, Sparse, Flawfinder, RATS, Lizard, Semgrep | 8 |
| **Dynamic Memory** | Valgrind (memcheck, helgrind, drd, cachegrind, callgrind, massif) | 6 |
| **Sanitizers** | ASAN, UBSAN, TSAN, MSAN | 4 |
| **Profiling** | perf, gprof, FlameGraph | 3 |
| **Coverage** | llvm-cov, gcov, lcov, gcovr | 4 |
| **Formal** | TLA+, Coq, Z3, CVC5, Frama-C, CBMC | 6 |
| **Build** | CMake, Ninja, ccache | 3 |
| **Format** | clang-format, black | 2 |
| **Total** | | **39 tools** |

## Installation

### Dev Container (Recommended)
All tools pre-installed in `.devcontainer/`
```bash
# Open in VS Code
# F1 → "Dev Containers: Reopen in Container"
```

### Manual Installation (Ubuntu/Debian)
```bash
# Core tools
sudo apt-get install \
  clang-18 lld-18 llvm-18-dev \
  clang-tidy cppcheck include-what-you-use \
  valgrind linux-tools-generic \
  sparse splint flawfinder rats \
  coq

# Python tools
pip3 install semgrep lizard

# Z3 (manual)
wget https://github.com/Z3Prover/z3/releases/download/z3-4.12.2/z3-4.12.2-x64-glibc-2.35.zip
unzip z3-*.zip && sudo cp z3-*/bin/z3 /usr/local/bin/

# TLA+ (manual)
wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar -O /usr/local/bin/tla2tools.jar
echo '#!/bin/bash\njava -jar /usr/local/bin/tla2tools.jar "$@"' | sudo tee /usr/local/bin/tlc
sudo chmod +x /usr/local/bin/tlc

# FlameGraph (manual)
git clone https://github.com/brendangregg/FlameGraph
sudo ln -s $(pwd)/FlameGraph/*.pl /usr/local/bin/

# Infer (manual)
wget https://github.com/facebook/infer/releases/download/v1.1.0/infer-linux64-v1.1.0.tar.xz
tar -xJf infer-linux64-v1.1.0.tar.xz
sudo mv infer-linux64-v1.1.0 /opt/infer
sudo ln -s /opt/infer/bin/infer /usr/local/bin/
```

## CI/CD Integration

### GitHub Actions Example
```yaml
- name: Advanced Analysis
  run: |
    cmake -B build -DENABLE_ADVANCED_ANALYSIS=ON
    ninja -C build advanced-analysis

- name: Formal Verification
  run: |
    cmake -B build -DENABLE_FORMAL_VERIFICATION=ON
    ninja -C build formal-verification

- name: Code Coverage
  run: |
    cmake -B build -DENABLE_COVERAGE=ON
    ninja -C build test coverage
    
- name: Upload Coverage
  uses: codecov/codecov-action@v3
  with:
    files: build/coverage/coverage.info
```

## Troubleshooting

### Tool Not Found
```bash
# Check tool availability
ninja -C build advanced-analysis-summary

# Install missing tools
sudo apt-get install [tool-name]
```

### Valgrind Issues
```bash
# Add suppressions
echo "suppression_pattern" >> .valgrind.supp

# Use suppressions
ninja -C build valgrind  # Automatically uses .valgrind.supp
```

### Performance Too Slow
```bash
# Disable expensive tools
cmake -B build -DENABLE_ADVANCED_ANALYSIS=OFF

# Or run selectively
ninja -C build clang-tidy  # Fast
ninja -C build scan-build  # Slower but thorough
```

## Best Practices

1. **Daily Development**
   - Use clang-tidy during build: `-DENABLE_CLANG_TIDY=ON`
   - Run basic static analysis: `ninja static-analysis`
   
2. **Pre-commit**
   - Run pre-commit hooks: `pre-commit run --all-files`
   - Quick coverage check: `ninja coverage-report`

3. **Weekly**
   - Run advanced analysis: `ninja advanced-analysis`
   - Check formal specs: `ninja tla-check`
   - Memory profiling: `ninja valgrind`

4. **Pre-release**
   - Full analysis: All targets
   - Formal verification: `ninja formal-verification`
   - Performance profiling: `ninja flamegraph`
   - 100% tool coverage

## Documentation

- **BUILD_SYSTEM_GUIDE.md** - Comprehensive build guide
- **TOOLING_REFERENCE.md** - Complete tool catalog
- **DEEP_ANALYSIS_TOOLING.md** - In-depth analysis and verification
- **TECHNICAL_DEBT_ANALYSIS.md** - Gap analysis and metrics
- **QUICKSTART_BUILD.md** - Quick start guide

## Support

- GitHub Issues: https://github.com/Oichkatzelesfrettschen/feuerbird_exokernel/issues
- Documentation: `docs/` directory
- Dev Container: `.devcontainer/`

---

**Last Updated:** 2026-01-03  
**Tools Integrated:** 39+  
**Targets Available:** 50+
