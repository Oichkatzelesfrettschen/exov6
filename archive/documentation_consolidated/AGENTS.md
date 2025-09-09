# Agent Instructions

**This file provides AI agent instructions for the FeuerBird Exokernel project.**

## 📖 Canonical Documentation

**All project information is consolidated in [README.md](README.md) - the single source of truth.**

The README.md contains comprehensive information about:
- Project architecture and design principles  
- Build system and development workflow
- POSIX compliance implementation status
- Performance benchmarks and optimization
- Complete repository structure and organization
- Contributing guidelines and coding standards
- Testing procedures and quality assurance

## 🤖 Agent-Specific Guidelines

### Code Modification Standards
All modifications must adhere to the project's core principles as defined in README.md:

- **Pure C17**: ALL new code must use ISO C17 standard with modern features
- **POSIX-2024 Compliance**: Strict adherence to SUSv5 specification
- **Performance First**: Changes must not degrade performance metrics  
- **Security Model**: Maintain capability-based security architecture
- **Three-Zone Model**: Respect Kernel/LibOS/Application boundaries

### Development Process
1. **Read README.md first** - Understand current project status and architecture
2. **Follow build instructions** - Use CMake build system as documented  
3. **Run full test suite** - Execute `ctest -V` before and after changes
4. **Maintain documentation** - Update README.md for significant changes
5. **Code quality checks** - Run `cmake --build . --target format lint analyze`

### Repository Organization
- **Source code**: Located in `src/` with functional organization
- **Headers**: Located in `include/` mirroring `src/` structure  
- **Tests**: Comprehensive suite in `tests/` directory
- **Documentation**: Organized in `docs/` by topic
- **Build system**: CMake-based with configuration in `CMakeLists.txt`

### Key Performance Targets
Maintain these performance metrics as documented in README.md:
- IPC Latency: < 1,000 cycles
- Context Switch: < 2,000 cycles  
- Capability Validation: < 100 cycles
- Boot Time: < 1 second

### Security Requirements
- Preserve capability-based security model
- Maintain zone isolation boundaries
- Use secure coding practices (C17 safety features)
- Validate all input at zone boundaries

## 🔄 Change Management

For any significant changes:
1. Update README.md with new information
2. Ensure consistency across all documentation
3. Update build configuration if needed
4. Add/update tests for new functionality
5. Verify POSIX compliance is maintained

## ⚡ Quick Reference

**Build Commands:**
```bash
mkdir build && cd build
cmake .. -DCMAKE_BUILD_TYPE=Debug
cmake --build . -j$(nproc)
ctest -V
```

**Quality Checks:**
```bash
cmake --build . --target format lint analyze
```

**QEMU Testing:**
```bash
cmake --build . --target qemu
```

---

**For complete information, see [README.md](README.md) - the canonical project documentation.**