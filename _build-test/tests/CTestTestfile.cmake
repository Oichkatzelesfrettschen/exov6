# CMake generated Testfile for 
# Source directory: /home/runner/work/exov6/exov6/tests
# Build directory: /home/runner/work/exov6/exov6/_build-test/tests
# 
# This file includes the relevant testing commands required for 
# testing this directory and lists subdirectories to be tested as well.
add_test(microbench-cap_verify_bench "phoenix-microbench-cap_verify_bench")
set_tests_properties(microbench-cap_verify_bench PROPERTIES  LABELS "microbench;performance" TIMEOUT "120" _BACKTRACE_TRIPLES "/home/runner/work/exov6/exov6/tests/CMakeLists.txt;71;add_test;/home/runner/work/exov6/exov6/tests/CMakeLists.txt;0;")
add_test(microbench-exo_yield_to_bench "phoenix-microbench-exo_yield_to_bench")
set_tests_properties(microbench-exo_yield_to_bench PROPERTIES  LABELS "microbench;performance" TIMEOUT "120" _BACKTRACE_TRIPLES "/home/runner/work/exov6/exov6/tests/CMakeLists.txt;71;add_test;/home/runner/work/exov6/exov6/tests/CMakeLists.txt;0;")
add_test(microbench-lattice_pipe_bench "phoenix-microbench-lattice_pipe_bench")
set_tests_properties(microbench-lattice_pipe_bench PROPERTIES  LABELS "microbench;performance" TIMEOUT "120" _BACKTRACE_TRIPLES "/home/runner/work/exov6/exov6/tests/CMakeLists.txt;71;add_test;/home/runner/work/exov6/exov6/tests/CMakeLists.txt;0;")
add_test(microbench-proc_cap_test "phoenix-microbench-proc_cap_test")
set_tests_properties(microbench-proc_cap_test PROPERTIES  LABELS "microbench;performance" TIMEOUT "120" _BACKTRACE_TRIPLES "/home/runner/work/exov6/exov6/tests/CMakeLists.txt;71;add_test;/home/runner/work/exov6/exov6/tests/CMakeLists.txt;0;")
add_test(libos-integration-test "/usr/local/bin/cmake" "-E" "echo" "LibOS integration test placeholder")
set_tests_properties(libos-integration-test PROPERTIES  LABELS "integration;libos" TIMEOUT "30" _BACKTRACE_TRIPLES "/home/runner/work/exov6/exov6/tests/CMakeLists.txt;117;add_test;/home/runner/work/exov6/exov6/tests/CMakeLists.txt;0;")
subdirs("c17")
