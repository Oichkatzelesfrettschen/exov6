# ═══════════════════════════════════════════════════════════════════════════════
# FeuerBird Exokernel - Dynamic Analysis Tools Configuration Module
# Integrates valgrind, sanitizers, and runtime profiling tools
# ═══════════════════════════════════════════════════════════════════════════════

option(ENABLE_VALGRIND "Enable Valgrind memory analysis" OFF)
option(ENABLE_PROFILING "Enable performance profiling with gprof/perf" OFF)

# ─────────────────────────────────────────────────────────────────────────────────
# Valgrind Configuration
# ─────────────────────────────────────────────────────────────────────────────────
if(ENABLE_VALGRIND)
    find_program(VALGRIND_EXECUTABLE
        NAMES valgrind
        DOC "Path to valgrind executable"
    )
    
    if(VALGRIND_EXECUTABLE)
        message(STATUS "Valgrind found: ${VALGRIND_EXECUTABLE}")
        
        # Valgrind suppression file
        set(VALGRIND_SUPPRESSIONS "${CMAKE_SOURCE_DIR}/.valgrind.supp")
        if(NOT EXISTS ${VALGRIND_SUPPRESSIONS})
            file(WRITE ${VALGRIND_SUPPRESSIONS} "# Valgrind suppressions\n")
        endif()
        
        # Memcheck target
        add_custom_target(valgrind-memcheck
            COMMAND ${VALGRIND_EXECUTABLE}
                --tool=memcheck
                --leak-check=full
                --show-leak-kinds=all
                --track-origins=yes
                --verbose
                --suppressions=${VALGRIND_SUPPRESSIONS}
                --log-file=${CMAKE_BINARY_DIR}/valgrind-memcheck.log
                $<TARGET_FILE:kernel>
            DEPENDS kernel
            COMMENT "Running Valgrind memcheck on kernel"
        )
        
        # Cachegrind target for cache profiling
        add_custom_target(valgrind-cachegrind
            COMMAND ${VALGRIND_EXECUTABLE}
                --tool=cachegrind
                --cachegrind-out-file=${CMAKE_BINARY_DIR}/cachegrind.out
                $<TARGET_FILE:kernel>
            DEPENDS kernel
            COMMENT "Running Valgrind cachegrind on kernel"
        )
        
        # Callgrind target for call graph profiling
        add_custom_target(valgrind-callgrind
            COMMAND ${VALGRIND_EXECUTABLE}
                --tool=callgrind
                --callgrind-out-file=${CMAKE_BINARY_DIR}/callgrind.out
                $<TARGET_FILE:kernel>
            DEPENDS kernel
            COMMENT "Running Valgrind callgrind on kernel"
        )
        
        # Massif target for heap profiling
        add_custom_target(valgrind-massif
            COMMAND ${VALGRIND_EXECUTABLE}
                --tool=massif
                --massif-out-file=${CMAKE_BINARY_DIR}/massif.out
                $<TARGET_FILE:kernel>
            DEPENDS kernel
            COMMENT "Running Valgrind massif heap profiler on kernel"
        )
        
        # Helgrind target for thread analysis
        add_custom_target(valgrind-helgrind
            COMMAND ${VALGRIND_EXECUTABLE}
                --tool=helgrind
                --log-file=${CMAKE_BINARY_DIR}/valgrind-helgrind.log
                $<TARGET_FILE:kernel>
            DEPENDS kernel
            COMMENT "Running Valgrind helgrind thread analyzer on kernel"
        )
        
        # DRD target for data race detection
        add_custom_target(valgrind-drd
            COMMAND ${VALGRIND_EXECUTABLE}
                --tool=drd
                --log-file=${CMAKE_BINARY_DIR}/valgrind-drd.log
                $<TARGET_FILE:kernel>
            DEPENDS kernel
            COMMENT "Running Valgrind DRD data race detector on kernel"
        )
        
        # Unified valgrind target
        add_custom_target(valgrind
            DEPENDS valgrind-memcheck
            COMMENT "Running Valgrind memory analysis"
        )
        
        message(STATUS "Valgrind targets available:")
        message(STATUS "  - valgrind: Run memory leak analysis")
        message(STATUS "  - valgrind-memcheck: Detailed memory check")
        message(STATUS "  - valgrind-cachegrind: Cache profiling")
        message(STATUS "  - valgrind-callgrind: Call graph profiling")
        message(STATUS "  - valgrind-massif: Heap profiling")
        message(STATUS "  - valgrind-helgrind: Thread analysis")
        message(STATUS "  - valgrind-drd: Data race detection")
    else()
        message(WARNING "Valgrind not found")
    endif()
endif()

# ─────────────────────────────────────────────────────────────────────────────────
# Performance Profiling Configuration
# ─────────────────────────────────────────────────────────────────────────────────
if(ENABLE_PROFILING)
    message(STATUS "Performance profiling enabled")
    
    # gprof support
    find_program(GPROF_EXECUTABLE
        NAMES gprof
        DOC "Path to gprof executable"
    )
    
    if(GPROF_EXECUTABLE)
        message(STATUS "gprof found: ${GPROF_EXECUTABLE}")
        set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -pg")
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -pg")
        set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -pg")
    endif()
    
    # perf support
    find_program(PERF_EXECUTABLE
        NAMES perf
        DOC "Path to perf executable"
    )
    
    if(PERF_EXECUTABLE)
        message(STATUS "perf found: ${PERF_EXECUTABLE}")
        
        add_custom_target(perf-record
            COMMAND ${PERF_EXECUTABLE} record -g $<TARGET_FILE:kernel>
            DEPENDS kernel
            COMMENT "Recording performance data with perf"
        )
        
        add_custom_target(perf-report
            COMMAND ${PERF_EXECUTABLE} report
            COMMENT "Generating perf report"
        )
        
        add_custom_target(perf-stat
            COMMAND ${PERF_EXECUTABLE} stat $<TARGET_FILE:kernel>
            DEPENDS kernel
            COMMENT "Running perf stat on kernel"
        )
    endif()
    
    # Flamegraph support
    find_program(FLAMEGRAPH_EXECUTABLE
        NAMES flamegraph.pl
        DOC "Path to flamegraph.pl script"
    )
    
    find_program(STACKCOLLAPSE_EXECUTABLE
        NAMES stackcollapse-perf.pl
        DOC "Path to stackcollapse-perf.pl script"
    )
    
    if(PERF_EXECUTABLE AND STACKCOLLAPSE_EXECUTABLE AND FLAMEGRAPH_EXECUTABLE)
        message(STATUS "Flamegraph tools found")
        
        add_custom_target(flamegraph
            COMMAND ${PERF_EXECUTABLE} record -F 99 -g $<TARGET_FILE:kernel>
            COMMAND ${PERF_EXECUTABLE} script | ${STACKCOLLAPSE_EXECUTABLE} | ${FLAMEGRAPH_EXECUTABLE} > ${CMAKE_BINARY_DIR}/flamegraph.svg
            DEPENDS kernel
            COMMENT "Generating flamegraph at ${CMAKE_BINARY_DIR}/flamegraph.svg"
        )
        
        message(STATUS "  - flamegraph: Generate flame graph visualization")
    elseif(PERF_EXECUTABLE)
        # Fallback: just collect perf data
        add_custom_target(flamegraph
            COMMAND ${PERF_EXECUTABLE} record -F 99 -g $<TARGET_FILE:kernel>
            COMMAND ${CMAKE_COMMAND} -E echo "Perf data recorded. Install FlameGraph tools to generate SVG:"
            COMMAND ${CMAKE_COMMAND} -E echo "  git clone https://github.com/brendangregg/FlameGraph"
            COMMAND ${CMAKE_COMMAND} -E echo "  perf script | FlameGraph/stackcollapse-perf.pl | FlameGraph/flamegraph.pl > flamegraph.svg"
            DEPENDS kernel
            COMMENT "Recording perf data for flamegraph (manual processing needed)"
        )
    endif()
endif()

# ─────────────────────────────────────────────────────────────────────────────────
# Dynamic analysis summary
# ─────────────────────────────────────────────────────────────────────────────────
add_custom_target(dynamic-analysis-summary
    COMMAND ${CMAKE_COMMAND} -E echo "═══════════════════════════════════════════"
    COMMAND ${CMAKE_COMMAND} -E echo "Dynamic Analysis Tools Summary"
    COMMAND ${CMAKE_COMMAND} -E echo "═══════════════════════════════════════════"
    COMMAND ${CMAKE_COMMAND} -E echo ""
    COMMAND ${CMAKE_COMMAND} -E echo "Available tools:"
    COMMAND ${CMAKE_COMMAND} -E echo "  Valgrind:   ${VALGRIND_EXECUTABLE}"
    COMMAND ${CMAKE_COMMAND} -E echo "  gprof:      ${GPROF_EXECUTABLE}"
    COMMAND ${CMAKE_COMMAND} -E echo "  perf:       ${PERF_EXECUTABLE}"
    COMMAND ${CMAKE_COMMAND} -E echo "  FlameGraph: ${FLAMEGRAPH_EXECUTABLE}"
    COMMAND ${CMAKE_COMMAND} -E echo ""
    COMMAND ${CMAKE_COMMAND} -E echo "Usage:"
    COMMAND ${CMAKE_COMMAND} -E echo "  ninja valgrind          # Memory leak detection"
    COMMAND ${CMAKE_COMMAND} -E echo "  ninja valgrind-callgrind # Call graph profiling"
    COMMAND ${CMAKE_COMMAND} -E echo "  ninja perf-record       # Performance recording"
    COMMAND ${CMAKE_COMMAND} -E echo "  ninja flamegraph        # Generate flame graph"
    COMMAND ${CMAKE_COMMAND} -E echo "═══════════════════════════════════════════"
    COMMENT "Displaying dynamic analysis tools summary"
)
