# FeuerBird Documentation Index

**This directory contains organized technical documentation for the FeuerBird Exokernel project.**

## 📖 Primary Documentation

**Start here:** [**README.md**](../README.md) - **Canonical project documentation** containing comprehensive information about architecture, build system, development workflow, and all essential project details.

## 📂 Documentation Organization

### Core Architecture
- **[architecture/](architecture/)** - System design and architectural principles
  - [exokernel_design.md](architecture/exokernel_design.md) - Core exokernel principles
  - [three_zone_model.md](architecture/three_zone_model.md) - Zone architecture details
  - [capability_model.md](architecture/capability_model.md) - Security model specification
  - [multi_architecture.md](architecture/multi_architecture.md) - Platform abstraction

### API Documentation  
- **[api/](api/)** - Interface documentation and specifications
  - [kernel_api.md](api/kernel_api.md) - Kernel interface specifications
  - [libos_api.md](api/libos_api.md) - LibOS API documentation
  - [ipc_api.md](api/ipc_api.md) - IPC system interfaces
  - [capability_api.md](api/capability_api.md) - Capability system API

### Standards Compliance
- **[standards/](standards/)** - Standards implementation and compliance
  - [posix_compliance.md](standards/posix_compliance.md) - POSIX-2024 implementation
  - [c17_standards.md](standards/c17_standards.md) - C17 language compliance
  - [POSIX_UTILITIES_LIST.md](standards/POSIX_UTILITIES_LIST.md) - Utility implementation status

### Development Guides
- **[development/](development/)** - Developer guides and procedures
  - [build_system.md](development/build_system.md) - Build configuration and options
  - [debugging.md](development/debugging.md) - Debugging tools and techniques
  - [performance.md](development/performance.md) - Performance optimization guide
  - [testing.md](development/testing.md) - Testing procedures and frameworks

### Phase 4 Documentation (Phase 4C - 2025)
- **[LAMBDA_CAP_GUIDE.md](LAMBDA_CAP_GUIDE.md)** - Lambda Capability Engine user guide (Phase 3 integration)
  - Pi-calculus process algebra and channels
  - S-expression lambda calculus evaluation
  - Superforce energy accounting and fuel management
  - Affine/linear type semantics (single-use capabilities)
  - Octonion state vectors and 8D composition
  - Code examples and integration patterns

- **[CONAN_USAGE.md](CONAN_USAGE.md)** - Conan 2.x build system guide
  - Installation and quick start
  - Build profiles (default, release, freestanding, debug)
  - Conanfile configuration and dependency management
  - Lockfiles for reproducible builds
  - CI/CD integration (GitHub Actions, GitLab CI)
  - Common workflows and troubleshooting

- **[TESTING_STRATEGY.md](TESTING_STRATEGY.md)** - Comprehensive testing strategy
  - Test framework overview (C17 custom, pytest, CTest)
  - Test categories (unit, integration, POSIX, personality, kernel boot)
  - Running tests locally and in CI
  - Adding new tests and test organization
  - Code coverage with LLVM (40% minimum threshold)
  - Microbenchmarks and performance regression detection
  - Debugging failed tests and troubleshooting

### Phase 5 Planning & Roadmap
- **[PHASE5_ROADMAP.md](PHASE5_ROADMAP.md)** - Comprehensive Phase 5 development roadmap
  - Phase 5A: Critical Functionality (capability_lattice, exokernel implementation)
  - Phase 5B: Advanced Features (lattice IPC, fuzzing, performance optimization)
  - Phase 5C: Production Readiness (procfs, ISO creation, deployment)
  - Integration timeline and dependency graph
  - Task breakdown with effort estimates
  - Success metrics and risk assessment

### Formal Specifications
- **[formal/](../formal/)** - Mathematical models and formal specifications
  - [specs/](../formal/specs/) - TLA+ specifications
  - [coq/](../formal/coq/) - Coq proofs and verification

### Legacy Documentation
- **[legacy/](legacy/)** - Historical documentation and design notes
  - Older markdown files moved from previous doc/ structure
  - Historical design discussions and implementation notes
  - Kept for reference and historical context

## 🎯 Documentation by Topic

### Getting Started
1. **[README.md](../README.md)** - Start here for complete project overview
2. **[CONTRIBUTING.md](../CONTRIBUTING.md)** - Development setup and contribution guidelines  
3. **[development/build_system.md](development/build_system.md)** - Detailed build instructions

### Understanding the Architecture
1. **[architecture/exokernel_design.md](architecture/exokernel_design.md)** - Core design principles
2. **[architecture/three_zone_model.md](architecture/three_zone_model.md)** - Zone separation model
3. **[architecture/capability_model.md](architecture/capability_model.md)** - Security architecture

### Development and Implementation
1. **[api/](api/)** - Interface specifications for all system components
2. **[development/](development/)** - Developer guides and best practices
3. **[standards/posix_compliance.md](standards/posix_compliance.md)** - POSIX implementation details

### Advanced Topics
1. **[formal/](../formal/)** - Mathematical specifications and proofs
2. **[development/performance.md](development/performance.md)** - Performance optimization
3. **Research papers and synthesis documents** (archived in [archive/](../archive/))

## 🔗 External References

### Academic Resources
- [POSIX.1-2024 (SUSv5) Specification](https://pubs.opengroup.org/onlinepubs/9699919799/) - Standards reference
- [Exokernel Research Papers](https://pdos.csail.mit.edu/exo/) - MIT PDOS research
- [Capability-Based Systems](https://cap-lore.com/) - Academic papers on capabilities

### Development Tools
- [CMake Documentation](https://cmake.org/documentation/) - Build system reference
- [QEMU Documentation](https://qemu.readthedocs.io/) - Emulation platform
- [C17 Reference](https://en.cppreference.com/w/c/17) - Language standard

## 📋 Documentation Status

### ✅ Current (Synchronized with README.md)
- Architecture overview and design principles
- Build system and development workflow  
- POSIX compliance implementation
- Performance targets and benchmarks
- Repository structure and organization

### 🔧 In Progress
- Detailed API documentation for all interfaces
- Comprehensive developer guides and tutorials
- Formal specification documentation
- Advanced topic deep-dives

### 📋 Planned
- Complete API reference with examples
- Step-by-step development tutorials
- Performance optimization cookbook
- Security model implementation guide

## 🔄 Maintenance

### Keeping Documentation Current
- **Primary updates** happen in [README.md](../README.md) - the canonical source
- **Specialized documentation** in this directory provides detailed technical content
- **Cross-references** are validated regularly to ensure consistency
- **Archive directory** preserves legacy documentation for historical reference

### Contributing to Documentation
1. **Major changes** - Update [README.md](../README.md) first
2. **Technical details** - Add to appropriate subdirectory
3. **New topics** - Follow existing organization structure
4. **Validate links** - Ensure all cross-references work correctly

---

**For complete project information, see [README.md](../README.md) - the definitive project documentation.**