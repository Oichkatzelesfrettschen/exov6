# ═══════════════════════════════════════════════════════════════════════════════
# FeuerBird Exokernel - Advanced Static Analysis Configuration Module
# Integrates additional industrial-strength static analyzers
# ═══════════════════════════════════════════════════════════════════════════════

option(ENABLE_ADVANCED_ANALYSIS "Enable advanced static analysis tools" OFF)

# ─────────────────────────────────────────────────────────────────────────────────
# Clang Static Analyzer (scan-build)
# ─────────────────────────────────────────────────────────────────────────────────
find_program(SCAN_BUILD_EXECUTABLE
    NAMES scan-build scan-build-18 scan-build-17
    DOC "Path to scan-build (Clang Static Analyzer)"
)

if(SCAN_BUILD_EXECUTABLE)
    message(STATUS "scan-build found: ${SCAN_BUILD_EXECUTABLE}")
    
    add_custom_target(scan-build
        COMMAND ${SCAN_BUILD_EXECUTABLE}
            -o ${CMAKE_BINARY_DIR}/scan-build-results
            --use-cc=clang --use-c++=clang++
            -enable-checker alpha.core.CastSize
            -enable-checker alpha.core.CastToStruct
            -enable-checker alpha.core.IdenticalExpr
            -enable-checker alpha.core.SizeofPtr
            -enable-checker alpha.security.ArrayBoundV2
            -enable-checker alpha.security.MallocOverflow
            -enable-checker alpha.security.ReturnPtrRange
            -enable-checker alpha.unix.SimpleStream
            -enable-checker alpha.unix.cstring.BufferOverlap
            -enable-checker alpha.unix.cstring.NotNullTerminated
            -enable-checker alpha.unix.cstring.OutOfBounds
            -enable-checker security.insecureAPI.UncheckedReturn
            -enable-checker security.insecureAPI.getpw
            -enable-checker security.insecureAPI.gets
            -enable-checker security.insecureAPI.mkstemp
            -enable-checker security.insecureAPI.mktemp
            ninja -C ${CMAKE_BINARY_DIR}
        WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
        COMMENT "Running Clang Static Analyzer (scan-build)"
    )
    
    message(STATUS "  - scan-build: Run Clang Static Analyzer")
else()
    message(STATUS "scan-build not found")
endif()

# ─────────────────────────────────────────────────────────────────────────────────
# Infer Static Analyzer (Facebook)
# ─────────────────────────────────────────────────────────────────────────────────
find_program(INFER_EXECUTABLE
    NAMES infer
    DOC "Path to Infer static analyzer"
)

if(INFER_EXECUTABLE)
    message(STATUS "Infer found: ${INFER_EXECUTABLE}")
    
    add_custom_target(infer
        COMMAND ${INFER_EXECUTABLE} run
            --compilation-database ${CMAKE_BINARY_DIR}/compile_commands.json
            --bufferoverrun --integer-overflow --memory-leak --null-dereference
            --resource-leak --thread-safety --uninit
            -o ${CMAKE_BINARY_DIR}/infer-results
        WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
        COMMENT "Running Infer static analyzer"
    )
    
    add_custom_target(infer-report
        COMMAND ${INFER_EXECUTABLE} explore --html
        WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
        COMMENT "Generating Infer HTML report"
    )
    
    message(STATUS "  - infer: Run Infer static analyzer")
    message(STATUS "  - infer-report: Generate Infer HTML report")
else()
    message(STATUS "Infer not found")
endif()

# ─────────────────────────────────────────────────────────────────────────────────
# Splint (Secure Programming Lint)
# ─────────────────────────────────────────────────────────────────────────────────
find_program(SPLINT_EXECUTABLE
    NAMES splint
    DOC "Path to Splint analyzer"
)

if(SPLINT_EXECUTABLE)
    message(STATUS "Splint found: ${SPLINT_EXECUTABLE}")
    
    add_custom_target(splint
        COMMAND find ${CMAKE_SOURCE_DIR}/kernel ${CMAKE_SOURCE_DIR}/libos
            -name "*.c" -exec ${SPLINT_EXECUTABLE}
            +posixlib -preproc
            -I${CMAKE_SOURCE_DIR}/include
            -I${CMAKE_SOURCE_DIR}/kernel/include
            {} +
            > ${CMAKE_BINARY_DIR}/splint-report.txt 2>&1 || true
        COMMENT "Running Splint security analyzer"
    )
    
    message(STATUS "  - splint: Run Splint security analyzer")
endif()

# ─────────────────────────────────────────────────────────────────────────────────
# Sparse (Linux kernel static analyzer)
# ─────────────────────────────────────────────────────────────────────────────────
find_program(SPARSE_EXECUTABLE
    NAMES sparse
    DOC "Path to Sparse analyzer"
)

if(SPARSE_EXECUTABLE)
    message(STATUS "Sparse found: ${SPARSE_EXECUTABLE}")
    
    add_custom_target(sparse
        COMMAND ${CMAKE_COMMAND} -E env CC=${SPARSE_EXECUTABLE}
            ninja -C ${CMAKE_BINARY_DIR}
        COMMENT "Running Sparse static analyzer"
    )
    
    message(STATUS "  - sparse: Run Sparse kernel analyzer")
endif()

# ─────────────────────────────────────────────────────────────────────────────────
# Flawfinder (Security vulnerability scanner)
# ─────────────────────────────────────────────────────────────────────────────────
find_program(FLAWFINDER_EXECUTABLE
    NAMES flawfinder
    DOC "Path to Flawfinder"
)

if(FLAWFINDER_EXECUTABLE)
    message(STATUS "Flawfinder found: ${FLAWFINDER_EXECUTABLE}")
    
    add_custom_target(flawfinder
        COMMAND ${FLAWFINDER_EXECUTABLE}
            --html --context --minlevel=2
            ${CMAKE_SOURCE_DIR}/kernel
            ${CMAKE_SOURCE_DIR}/libos
            ${CMAKE_SOURCE_DIR}/src
            > ${CMAKE_BINARY_DIR}/flawfinder-report.html
        COMMENT "Running Flawfinder security scanner"
    )
    
    message(STATUS "  - flawfinder: Run Flawfinder security scanner")
endif()

# ─────────────────────────────────────────────────────────────────────────────────
# RATS (Rough Auditing Tool for Security)
# ─────────────────────────────────────────────────────────────────────────────────
find_program(RATS_EXECUTABLE
    NAMES rats
    DOC "Path to RATS security auditor"
)

if(RATS_EXECUTABLE)
    message(STATUS "RATS found: ${RATS_EXECUTABLE}")
    
    add_custom_target(rats
        COMMAND ${RATS_EXECUTABLE}
            --html
            ${CMAKE_SOURCE_DIR}/kernel
            ${CMAKE_SOURCE_DIR}/libos
            > ${CMAKE_BINARY_DIR}/rats-report.html
        COMMENT "Running RATS security auditor"
    )
    
    message(STATUS "  - rats: Run RATS security auditor")
endif()

# ─────────────────────────────────────────────────────────────────────────────────
# Lizard (Code complexity analyzer)
# ─────────────────────────────────────────────────────────────────────────────────
find_program(LIZARD_EXECUTABLE
    NAMES lizard
    DOC "Path to Lizard complexity analyzer"
)

if(LIZARD_EXECUTABLE)
    message(STATUS "Lizard found: ${LIZARD_EXECUTABLE}")
    
    add_custom_target(lizard
        COMMAND ${LIZARD_EXECUTABLE}
            -l c -w
            ${CMAKE_SOURCE_DIR}/kernel
            ${CMAKE_SOURCE_DIR}/libos
            > ${CMAKE_BINARY_DIR}/lizard-report.txt
        COMMENT "Running Lizard complexity analyzer"
    )
    
    add_custom_target(lizard-html
        COMMAND ${LIZARD_EXECUTABLE}
            -l c -w --html
            ${CMAKE_SOURCE_DIR}/kernel
            ${CMAKE_SOURCE_DIR}/libos
            > ${CMAKE_BINARY_DIR}/lizard-report.html
        COMMENT "Generating Lizard HTML report"
    )
    
    message(STATUS "  - lizard: Run Lizard complexity analysis")
    message(STATUS "  - lizard-html: Generate Lizard HTML report")
endif()

# ─────────────────────────────────────────────────────────────────────────────────
# Semgrep (Lightweight static analysis)
# ─────────────────────────────────────────────────────────────────────────────────
find_program(SEMGREP_EXECUTABLE
    NAMES semgrep
    DOC "Path to Semgrep analyzer"
)

if(SEMGREP_EXECUTABLE)
    message(STATUS "Semgrep found: ${SEMGREP_EXECUTABLE}")
    
    add_custom_target(semgrep
        COMMAND ${SEMGREP_EXECUTABLE}
            --config=auto
            --json --output=${CMAKE_BINARY_DIR}/semgrep-report.json
            ${CMAKE_SOURCE_DIR}/kernel
            ${CMAKE_SOURCE_DIR}/libos
        COMMENT "Running Semgrep static analyzer"
    )
    
    message(STATUS "  - semgrep: Run Semgrep analyzer")
endif()

# ─────────────────────────────────────────────────────────────────────────────────
# Unified advanced analysis target
# ─────────────────────────────────────────────────────────────────────────────────
if(ENABLE_ADVANCED_ANALYSIS)
    set(ADVANCED_TARGETS "")
    
    if(TARGET scan-build)
        list(APPEND ADVANCED_TARGETS scan-build)
    endif()
    
    if(TARGET infer)
        list(APPEND ADVANCED_TARGETS infer)
    endif()
    
    if(TARGET splint)
        list(APPEND ADVANCED_TARGETS splint)
    endif()
    
    if(TARGET sparse)
        list(APPEND ADVANCED_TARGETS sparse)
    endif()
    
    if(TARGET flawfinder)
        list(APPEND ADVANCED_TARGETS flawfinder)
    endif()
    
    if(TARGET rats)
        list(APPEND ADVANCED_TARGETS rats)
    endif()
    
    if(TARGET lizard)
        list(APPEND ADVANCED_TARGETS lizard)
    endif()
    
    if(TARGET semgrep)
        list(APPEND ADVANCED_TARGETS semgrep)
    endif()
    
    if(ADVANCED_TARGETS)
        add_custom_target(advanced-analysis
            DEPENDS ${ADVANCED_TARGETS}
            COMMENT "Running all advanced static analysis tools"
        )
        
        message(STATUS "Advanced analysis targets:")
        foreach(target ${ADVANCED_TARGETS})
            message(STATUS "  - ${target}")
        endforeach()
        message(STATUS "  - advanced-analysis: Run all advanced analyzers")
    endif()
endif()

# ─────────────────────────────────────────────────────────────────────────────────
# Advanced analysis summary
# ─────────────────────────────────────────────────────────────────────────────────
add_custom_target(advanced-analysis-summary
    COMMAND ${CMAKE_COMMAND} -E echo "═══════════════════════════════════════════"
    COMMAND ${CMAKE_COMMAND} -E echo "Advanced Static Analysis Tools Summary"
    COMMAND ${CMAKE_COMMAND} -E echo "═══════════════════════════════════════════"
    COMMAND ${CMAKE_COMMAND} -E echo ""
    COMMAND ${CMAKE_COMMAND} -E echo "Available tools:"
    COMMAND ${CMAKE_COMMAND} -E echo "  scan-build:  ${SCAN_BUILD_EXECUTABLE}"
    COMMAND ${CMAKE_COMMAND} -E echo "  Infer:       ${INFER_EXECUTABLE}"
    COMMAND ${CMAKE_COMMAND} -E echo "  Splint:      ${SPLINT_EXECUTABLE}"
    COMMAND ${CMAKE_COMMAND} -E echo "  Sparse:      ${SPARSE_EXECUTABLE}"
    COMMAND ${CMAKE_COMMAND} -E echo "  Flawfinder:  ${FLAWFINDER_EXECUTABLE}"
    COMMAND ${CMAKE_COMMAND} -E echo "  RATS:        ${RATS_EXECUTABLE}"
    COMMAND ${CMAKE_COMMAND} -E echo "  Lizard:      ${LIZARD_EXECUTABLE}"
    COMMAND ${CMAKE_COMMAND} -E echo "  Semgrep:     ${SEMGREP_EXECUTABLE}"
    COMMAND ${CMAKE_COMMAND} -E echo ""
    COMMAND ${CMAKE_COMMAND} -E echo "Usage:"
    COMMAND ${CMAKE_COMMAND} -E echo "  ninja scan-build      # Clang Static Analyzer"
    COMMAND ${CMAKE_COMMAND} -E echo "  ninja infer           # Facebook Infer"
    COMMAND ${CMAKE_COMMAND} -E echo "  ninja flawfinder      # Security scanner"
    COMMAND ${CMAKE_COMMAND} -E echo "  ninja lizard          # Complexity analysis"
    COMMAND ${CMAKE_COMMAND} -E echo "  ninja advanced-analysis # Run all"
    COMMAND ${CMAKE_COMMAND} -E echo "═══════════════════════════════════════════"
    COMMENT "Displaying advanced analysis tools summary"
)
