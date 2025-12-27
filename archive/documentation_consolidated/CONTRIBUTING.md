# Contributing to FeuerBird Exokernel

**Welcome to the FeuerBird Exokernel project!** We welcome contributions from the community and appreciate your interest in advancing exokernel research and development.

## 📖 Essential Reading

**Before contributing, please read [README.md](README.md) - the canonical project documentation containing:**
- Complete architecture overview and design principles
- Development workflow and build instructions
- Coding standards and performance requirements
- Repository structure and organization
- Testing procedures and quality assurance

## 🎯 Development Standards

### Code Requirements (MUST FOLLOW)
- **Pure C17**: All code must comply with ISO C17 standard
- **POSIX-2024**: Strict adherence to SUSv5 specification  
- **Security First**: Maintain capability-based security model
- **Performance Focused**: No degradation of target metrics
- **Multi-Architecture**: Platform-agnostic design with HAL abstraction
- **Well Tested**: Comprehensive test coverage required
- **Well Documented**: Doxygen-style documentation for all functions

### Performance Targets
Maintain these critical metrics (detailed in README.md):
- **IPC Latency**: < 1,000 cycles
- **Context Switch**: < 2,000 cycles  
- **Capability Validation**: < 100 cycles
- **Boot Time**: < 1 second

## 🛠️ Development Setup

### Prerequisites
- **CMake 3.20+** (Primary build system)
- **C17 Compiler**: GCC 8+ or Clang 10+
- **QEMU 4.0+** for emulation testing  
- **Python 3.8+** with pytest for testing
- **Git** with LFS for large binary assets

### Initial Setup
```bash
# Clone repository
git clone https://github.com/FeuerBird/feuerbird_exokernel.git
cd feuerbird_exokernel

# Install pre-commit hooks
pip install pre-commit
pre-commit install

# Configure build
mkdir build && cd build
cmake .. -DCMAKE_BUILD_TYPE=Debug

# Build and test
cmake --build . -j$(nproc)
ctest -V
```

## 🔧 Development Workflow

### 1. Build and Test
```bash
# Development build with debugging
cmake .. -DCMAKE_BUILD_TYPE=Debug -DIPC_DEBUG=ON
cmake --build . -j$(nproc)

# Run comprehensive test suite
ctest -V                                    # All tests
cmake --build . --target posix-test        # POSIX compliance
cmake --build . --target stress-tests      # Performance tests
```

### 2. Code Quality
```bash
# Automatic formatting and linting
cmake --build . --target format lint analyze

# Pre-commit hooks (automatic on commit)
pre-commit run --all-files

# Memory safety checks
cmake .. -DCMAKE_C_FLAGS="-fsanitize=address"
cmake --build . --target unit-tests
```

### 3. Emulation and Debugging
```bash
# Run in QEMU
cmake --build . --target qemu

# Debug with GDB
cmake --build . --target qemu-gdb          # Terminal 1
gdb kernel.elf -ex "target remote :26000"  # Terminal 2
```

## 🧪 Testing Requirements

### Test Suite Structure
```
tests/
├── unit/                   # Unit tests for individual components
├── integration/            # Integration tests for system interactions  
├── performance/            # Performance benchmarks and regression tests
└── posix/                  # POSIX compliance verification
```

### Running Tests
```bash
# Complete test suite
ctest -V

# Category-specific testing
cmake --build . --target pytest_suite    # Python integration tests
cmake --build . --target posix-test      # POSIX compliance tests
cmake --build . --target unit-tests      # C unit tests

# Specific test execution
./build/tests/unit/test_capabilities     # Capability system tests
./build/tests/performance/ipc_benchmark  # IPC performance tests
```

### Test Requirements for Contributions
- **Unit tests** for all new functionality
- **Integration tests** for cross-component interactions
- **Performance tests** to verify no regression
- **POSIX compliance** verification for utility changes

## 📋 Contribution Process

### 1. Preparation
1. **Read [README.md](README.md)** for complete project understanding
2. **Fork** the repository and create feature branch
3. **Set up development environment** with all prerequisites
4. **Run existing tests** to ensure clean baseline

### 2. Development
1. **Follow coding standards** as defined in README.md
2. **Maintain architecture boundaries** between zones
3. **Use modern C17 features** and safety practices
4. **Preserve performance metrics** and security model
5. **Add comprehensive tests** for new functionality

### 3. Quality Assurance
```bash
# Before submitting, run full validation
cmake --build . --target format lint analyze
ctest -V
cmake --build . --target posix-test
pre-commit run --all-files
```

### 4. Submission
1. **Update documentation** if needed (especially README.md)
2. **Write detailed commit messages** explaining changes
3. **Submit pull request** with comprehensive description
4. **Respond to review feedback** promptly

## 🎯 Contribution Areas

### High-Priority Areas
- **🐛 Bug Fixes**: Fix issues and improve system stability
- **🚀 Performance**: Optimize critical paths and algorithms
- **🔒 Security**: Enhance security features and find vulnerabilities
- **🎯 POSIX**: Improve standards compliance and utility implementation
- **🧪 Testing**: Expand test coverage and add benchmarks
- **📚 Documentation**: Improve guides and API documentation

### Technical Focus Areas
- **C17 Modernization**: Converting legacy code to modern standards
- **Multi-Architecture**: Expanding HAL support and architecture coverage
- **IPC Optimization**: Achieving sub-1000 cycle latency targets
- **Capability System**: Enhancing security model and validation
- **POSIX Utilities**: Implementing and testing remaining utilities

## 📚 Resources and References

### Primary Documentation
- **[README.md](README.md)** ← **MAIN REFERENCE** (comprehensive)
- **[docs/](docs/)** ← Technical documentation by topic
- **[examples/](examples/)** ← Example code and tutorials

### External References
- [POSIX.1-2024 (SUSv5) Specification](https://pubs.opengroup.org/onlinepubs/9699919799/)
- [Exokernel Research Papers](https://pdos.csail.mit.edu/exo/) (MIT PDOS)
- [C17 Standard Documentation](https://en.cppreference.com/w/c/17)

### Development Tools
- [CMake Documentation](https://cmake.org/documentation/)
- [QEMU User Documentation](https://qemu.readthedocs.io/)
- [Pre-commit Framework](https://pre-commit.com/)

## 🤝 Code Review Process

### Review Criteria
- **Correctness**: Code functions as intended without bugs
- **Performance**: No degradation of target metrics
- **Security**: Maintains capability-based security model
- **Style**: Follows C17 coding standards and conventions
- **Testing**: Comprehensive test coverage included
- **Documentation**: Clear comments and updated README.md if needed

### Review Timeline
- **Initial Response**: Within 48 hours
- **Detailed Review**: Within 1 week
- **Feedback Cycle**: Ongoing until approved
- **Merge**: After all checks pass and 2 approvals

## 🚦 Release Process

### Version Scheme
- **Major**: Significant architectural changes
- **Minor**: New features and enhancements  
- **Patch**: Bug fixes and minor improvements

### Development Phases
- **Alpha**: Active development (current)
- **Beta**: Feature complete, stability focus
- **Stable**: Production ready releases

## ❓ Getting Help

### Support Channels
- **GitHub Issues**: Bug reports and feature requests
- **GitHub Discussions**: Technical questions and design discussions
- **Documentation**: Comprehensive guides in [README.md](README.md)

### Before Asking for Help
1. Read [README.md](README.md) thoroughly
2. Search existing issues and discussions
3. Try the development workflow locally
4. Review related code and tests

---

## 📄 License

By contributing to FeuerBird, you agree that your contributions will be licensed under the same [MIT License](LICENSE) that covers the project.

---

**Thank you for contributing to FeuerBird Exokernel!**  
**Together we're advancing the state of operating systems research and development.**

For questions about this contribution guide, please refer to [README.md](README.md) or open a GitHub issue.