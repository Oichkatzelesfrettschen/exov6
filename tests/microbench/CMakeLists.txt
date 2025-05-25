add_executable(cap_verify_bench cap_verify_bench.c)
add_executable(exo_yield_to_bench exo_yield_to_bench.c)
add_executable(proc_cap_test
  proc_cap_test.c
  ../../libos/procwrap.c
  ../../libos/capwrap.c)

foreach(t cap_verify_bench exo_yield_to_bench proc_cap_test)
  target_include_directories(${t} PRIVATE
    ${CMAKE_SOURCE_DIR}/libos/include
    ${CMAKE_SOURCE_DIR}/src-headers)
endforeach()
