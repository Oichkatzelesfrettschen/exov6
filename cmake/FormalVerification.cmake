# ═══════════════════════════════════════════════════════════════════════════════
# FeuerBird Exokernel - Formal Verification Configuration Module
# Integrates TLA+, Coq, Z3, and SMT-based verification tools
# ═══════════════════════════════════════════════════════════════════════════════

option(ENABLE_FORMAL_VERIFICATION "Enable formal verification tools" OFF)

# ─────────────────────────────────────────────────────────────────────────────────
# TLA+ Model Checking
# ─────────────────────────────────────────────────────────────────────────────────
find_program(TLC_EXECUTABLE
    NAMES tlc tla2tools.jar
    PATHS /usr/local/bin /usr/bin
    DOC "Path to TLA+ model checker"
)

if(TLC_EXECUTABLE)
    message(STATUS "TLA+ model checker found: ${TLC_EXECUTABLE}")
    
    file(GLOB TLA_SPECS
        "${CMAKE_SOURCE_DIR}/formal/specs/*.tla"
        "${CMAKE_SOURCE_DIR}/formal/specs/tla/*.tla"
        "${CMAKE_SOURCE_DIR}/docs/tla/*.tla"
    )
    
    if(TLA_SPECS)
        add_custom_target(tla-check
            COMMENT "Model checking TLA+ specifications"
        )
        
        foreach(spec ${TLA_SPECS})
            get_filename_component(spec_name ${spec} NAME_WE)
            add_custom_target(tla-check-${spec_name}
                COMMAND ${TLC_EXECUTABLE} ${spec}
                WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
                COMMENT "Model checking ${spec_name}.tla"
            )
            add_dependencies(tla-check tla-check-${spec_name})
        endforeach()
        
        message(STATUS "TLA+ specifications found: ${TLA_SPECS}")
        message(STATUS "  - tla-check: Verify all TLA+ specifications")
    endif()
else()
    message(STATUS "TLA+ model checker (tlc) not found - skipping TLA+ verification")
endif()

# ─────────────────────────────────────────────────────────────────────────────────
# Coq Proof Assistant
# ─────────────────────────────────────────────────────────────────────────────────
find_program(COQC_EXECUTABLE
    NAMES coqc
    DOC "Path to Coq compiler"
)

if(COQC_EXECUTABLE)
    message(STATUS "Coq found: ${COQC_EXECUTABLE}")
    
    if(EXISTS "${CMAKE_SOURCE_DIR}/formal/coq")
        add_custom_target(coq-check
            COMMAND make -C ${CMAKE_SOURCE_DIR}/formal/coq
            COMMENT "Type-checking Coq proofs"
        )
        
        message(STATUS "  - coq-check: Type-check Coq development")
    endif()
else()
    message(STATUS "Coq not found - skipping Coq verification")
endif()

# ─────────────────────────────────────────────────────────────────────────────────
# Z3 Theorem Prover
# ─────────────────────────────────────────────────────────────────────────────────
find_program(Z3_EXECUTABLE
    NAMES z3
    DOC "Path to Z3 theorem prover"
)

if(Z3_EXECUTABLE)
    message(STATUS "Z3 theorem prover found: ${Z3_EXECUTABLE}")
    
    # Find SMT2 files
    file(GLOB_RECURSE SMT2_FILES
        "${CMAKE_SOURCE_DIR}/formal/*.smt2"
        "${CMAKE_SOURCE_DIR}/tests/*.smt2"
    )
    
    if(SMT2_FILES)
        add_custom_target(z3-check
            COMMENT "Verifying SMT2 specifications with Z3"
        )
        
        foreach(smt2_file ${SMT2_FILES})
            get_filename_component(smt2_name ${smt2_file} NAME_WE)
            add_custom_target(z3-check-${smt2_name}
                COMMAND ${Z3_EXECUTABLE} ${smt2_file}
                WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
                COMMENT "Verifying ${smt2_name}.smt2 with Z3"
            )
            add_dependencies(z3-check z3-check-${smt2_name})
        endforeach()
        
        message(STATUS "SMT2 files found: ${SMT2_FILES}")
    endif()
    
    # Create Z3 verification helper target
    add_custom_target(z3-verify-capability-model
        COMMAND ${CMAKE_COMMAND} -E echo "Generating capability model verification..."
        COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_BINARY_DIR}/z3
        COMMAND ${CMAKE_COMMAND} -P ${CMAKE_SOURCE_DIR}/cmake/scripts/GenerateCapabilityZ3.cmake
        COMMENT "Generating Z3 verification for capability model"
    )
    
    message(STATUS "  - z3-check: Verify SMT2 specifications")
    message(STATUS "  - z3-verify-capability-model: Generate and verify capability model")
else()
    message(STATUS "Z3 not found - skipping Z3 verification")
endif()

# ─────────────────────────────────────────────────────────────────────────────────
# CVC5 SMT Solver (alternative to Z3)
# ─────────────────────────────────────────────────────────────────────────────────
find_program(CVC5_EXECUTABLE
    NAMES cvc5
    DOC "Path to CVC5 SMT solver"
)

if(CVC5_EXECUTABLE)
    message(STATUS "CVC5 SMT solver found: ${CVC5_EXECUTABLE}")
    
    if(SMT2_FILES)
        add_custom_target(cvc5-check
            COMMENT "Verifying SMT2 specifications with CVC5"
        )
        
        foreach(smt2_file ${SMT2_FILES})
            get_filename_component(smt2_name ${smt2_file} NAME_WE)
            add_custom_target(cvc5-check-${smt2_name}
                COMMAND ${CVC5_EXECUTABLE} ${smt2_file}
                WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
                COMMENT "Verifying ${smt2_name}.smt2 with CVC5"
            )
            add_dependencies(cvc5-check cvc5-check-${smt2_name})
        endforeach()
        
        message(STATUS "  - cvc5-check: Verify SMT2 specifications with CVC5")
    endif()
endif()

# ─────────────────────────────────────────────────────────────────────────────────
# Frama-C Static Analyzer with WP Plugin
# ─────────────────────────────────────────────────────────────────────────────────
find_program(FRAMAC_EXECUTABLE
    NAMES frama-c
    DOC "Path to Frama-C static analyzer"
)

if(FRAMAC_EXECUTABLE)
    message(STATUS "Frama-C found: ${FRAMAC_EXECUTABLE}")
    
    add_custom_target(frama-c-check
        COMMAND ${FRAMAC_EXECUTABLE} -wp -wp-prover alt-ergo,z3,cvc4
            ${CMAKE_SOURCE_DIR}/kernel/*.c
            ${CMAKE_SOURCE_DIR}/libos/*.c
            -cpp-extra-args="-I${CMAKE_SOURCE_DIR}/include -I${CMAKE_SOURCE_DIR}/kernel/include"
        COMMENT "Running Frama-C weakest precondition analysis"
    )
    
    message(STATUS "  - frama-c-check: Run Frama-C WP verification")
endif()

# ─────────────────────────────────────────────────────────────────────────────────
# CBMC (C Bounded Model Checker)
# ─────────────────────────────────────────────────────────────────────────────────
find_program(CBMC_EXECUTABLE
    NAMES cbmc
    DOC "Path to CBMC bounded model checker"
)

if(CBMC_EXECUTABLE)
    message(STATUS "CBMC found: ${CBMC_EXECUTABLE}")
    
    add_custom_target(cbmc-check
        COMMAND ${CBMC_EXECUTABLE}
            --bounds-check --pointer-check --memory-leak-check
            --unwind 10
            ${CMAKE_SOURCE_DIR}/kernel/capability.c
            -I ${CMAKE_SOURCE_DIR}/include
            -I ${CMAKE_SOURCE_DIR}/kernel/include
        COMMENT "Running CBMC bounded model checking"
    )
    
    message(STATUS "  - cbmc-check: Run CBMC bounded model checking")
endif()

# ─────────────────────────────────────────────────────────────────────────────────
# Unified formal verification target
# ─────────────────────────────────────────────────────────────────────────────────
if(ENABLE_FORMAL_VERIFICATION)
    set(FORMAL_TARGETS "")
    
    if(TARGET tla-check)
        list(APPEND FORMAL_TARGETS tla-check)
    endif()
    
    if(TARGET coq-check)
        list(APPEND FORMAL_TARGETS coq-check)
    endif()
    
    if(TARGET z3-check)
        list(APPEND FORMAL_TARGETS z3-check)
    endif()
    
    if(TARGET cvc5-check)
        list(APPEND FORMAL_TARGETS cvc5-check)
    endif()
    
    if(TARGET frama-c-check)
        list(APPEND FORMAL_TARGETS frama-c-check)
    endif()
    
    if(TARGET cbmc-check)
        list(APPEND FORMAL_TARGETS cbmc-check)
    endif()
    
    if(FORMAL_TARGETS)
        add_custom_target(formal-verification
            DEPENDS ${FORMAL_TARGETS}
            COMMENT "Running all formal verification tools"
        )
        
        message(STATUS "Formal verification targets:")
        foreach(target ${FORMAL_TARGETS})
            message(STATUS "  - ${target}")
        endforeach()
        message(STATUS "  - formal-verification: Run all verification tools")
    endif()
endif()

# ─────────────────────────────────────────────────────────────────────────────────
# Formal verification summary
# ─────────────────────────────────────────────────────────────────────────────────
add_custom_target(formal-verification-summary
    COMMAND ${CMAKE_COMMAND} -E echo "═══════════════════════════════════════════"
    COMMAND ${CMAKE_COMMAND} -E echo "Formal Verification Tools Summary"
    COMMAND ${CMAKE_COMMAND} -E echo "═══════════════════════════════════════════"
    COMMAND ${CMAKE_COMMAND} -E echo ""
    COMMAND ${CMAKE_COMMAND} -E echo "Available tools:"
    COMMAND ${CMAKE_COMMAND} -E echo "  TLA+:      ${TLC_EXECUTABLE}"
    COMMAND ${CMAKE_COMMAND} -E echo "  Coq:       ${COQC_EXECUTABLE}"
    COMMAND ${CMAKE_COMMAND} -E echo "  Z3:        ${Z3_EXECUTABLE}"
    COMMAND ${CMAKE_COMMAND} -E echo "  CVC5:      ${CVC5_EXECUTABLE}"
    COMMAND ${CMAKE_COMMAND} -E echo "  Frama-C:   ${FRAMAC_EXECUTABLE}"
    COMMAND ${CMAKE_COMMAND} -E echo "  CBMC:      ${CBMC_EXECUTABLE}"
    COMMAND ${CMAKE_COMMAND} -E echo ""
    COMMAND ${CMAKE_COMMAND} -E echo "Usage:"
    COMMAND ${CMAKE_COMMAND} -E echo "  ninja tla-check          # Model check TLA+ specs"
    COMMAND ${CMAKE_COMMAND} -E echo "  ninja coq-check          # Type-check Coq proofs"
    COMMAND ${CMAKE_COMMAND} -E echo "  ninja z3-check           # Verify with Z3"
    COMMAND ${CMAKE_COMMAND} -E echo "  ninja formal-verification # Run all tools"
    COMMAND ${CMAKE_COMMAND} -E echo "═══════════════════════════════════════════"
    COMMENT "Displaying formal verification tools summary"
)
