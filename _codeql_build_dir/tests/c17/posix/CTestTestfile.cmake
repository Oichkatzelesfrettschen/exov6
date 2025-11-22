# CMake generated Testfile for 
# Source directory: /home/runner/work/exov6/exov6/tests/c17/posix
# Build directory: /home/runner/work/exov6/exov6/_codeql_build_dir/tests/c17/posix
# 
# This file includes the relevant testing commands required for 
# testing this directory and lists subdirectories to be tested as well.
add_test(posix_test_posix_apis "/home/runner/work/exov6/exov6/_codeql_build_dir/tests/c17/posix/test_posix_apis")
set_tests_properties(posix_test_posix_apis PROPERTIES  LABELS "posix;compliance" TIMEOUT "45" WORKING_DIRECTORY "/home/runner/work/exov6/exov6/_codeql_build_dir/tests/c17/posix" _BACKTRACE_TRIPLES "/home/runner/work/exov6/exov6/tests/c17/posix/CMakeLists.txt;20;add_test;/home/runner/work/exov6/exov6/tests/c17/posix/CMakeLists.txt;0;")
add_test(posix_test_posix_compat "/home/runner/work/exov6/exov6/_codeql_build_dir/tests/c17/posix/test_posix_compat")
set_tests_properties(posix_test_posix_compat PROPERTIES  LABELS "posix;compliance" TIMEOUT "45" WORKING_DIRECTORY "/home/runner/work/exov6/exov6/_codeql_build_dir/tests/c17/posix" _BACKTRACE_TRIPLES "/home/runner/work/exov6/exov6/tests/c17/posix/CMakeLists.txt;20;add_test;/home/runner/work/exov6/exov6/tests/c17/posix/CMakeLists.txt;0;")
