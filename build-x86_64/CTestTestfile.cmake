# CMake generated Testfile for 
# Source directory: /Users/eirikr/Documents/GitHub/exov6
# Build directory: /Users/eirikr/Documents/GitHub/exov6/build-x86_64
# 
# This file includes the relevant testing commands required for 
# testing this directory and lists subdirectories to be tested as well.
add_test([=[pytest_suite]=] "python3" "-m" "pytest" "-v" "tests/")
set_tests_properties([=[pytest_suite]=] PROPERTIES  WORKING_DIRECTORY "/Users/eirikr/Documents/GitHub/exov6" _BACKTRACE_TRIPLES "/Users/eirikr/Documents/GitHub/exov6/CMakeLists.txt;513;add_test;/Users/eirikr/Documents/GitHub/exov6/CMakeLists.txt;0;")
