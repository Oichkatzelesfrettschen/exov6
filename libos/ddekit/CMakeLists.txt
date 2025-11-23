# libos/ddekit/CMakeLists.txt - Device Driver Environment Kit (LibOS Port)

# Collect sources
file(GLOB DDEKIT_SOURCES *.c)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/badgerferret")
    file(GLOB BADGERFERRET_SOURCES badgerferret/*.c)
    list(APPEND DDEKIT_SOURCES ${BADGERFERRET_SOURCES})
endif()

# Define the library
phoenix_add_library(phoenix-libos-ddekit
    STATIC
    SOURCES ${DDEKIT_SOURCES}
    INCLUDES
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
        ${CMAKE_SOURCE_DIR}/libos
    DEPENDENCIES
        phoenix-architecture
        phoenix-userland
)

# Link against optional LibOS components if they exist
# Note: ddekit.c depends on procwrap and capwrap functions.
# If these targets are not available, ddekit might fail to link or need stubs.
if(TARGET phoenix-libos-procwrap)
    target_link_libraries(phoenix-libos-ddekit PUBLIC phoenix-libos-procwrap)
endif()

if(TARGET phoenix-libos-capwrap)
    target_link_libraries(phoenix-libos-ddekit PUBLIC phoenix-libos-capwrap)
endif()
