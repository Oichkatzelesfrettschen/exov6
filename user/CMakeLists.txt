# user/CMakeLists.txt (Phase 3 Reconstruction)

# Init process (The First Contractor)
add_executable(init init.c)
target_link_libraries(init libos)
target_include_directories(init PRIVATE ${CMAKE_SOURCE_DIR}/include)

# Install to bin
install(TARGETS init RUNTIME DESTINATION bin)
