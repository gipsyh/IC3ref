cmake_minimum_required(VERSION 3.14)
project(ic3ref VERSION 1.0.0)

enable_language(C CXX)
set(CMAKE_CXX_STANDARD 11)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -D__STDC_LIMIT_MACROS -D__STDC_FORMAT_MACROS -O3 -g -fpermissive")

add_library(ic3ref STATIC IC3.cpp aiger/aiger.c Model.cpp pic3.cpp)
target_include_directories(ic3ref PUBLIC aiger minisat minisat/minisat/core minisat/minisat/simp
                                        minisat/minisat/mtl)

add_subdirectory(minisat)
target_link_libraries(ic3ref PUBLIC minisat-lib-static)

add_subdirectory("${CMAKE_CURRENT_SOURCE_DIR}/../pic3/pic3/pic3cpp" pic3cpp)
target_link_libraries(ic3ref PUBLIC pic3cpp)

# add_executable(ic3refmain main.cpp)
# target_link_libraries(ic3refmain PUBLIC ic3ref)

install(TARGETS ic3ref
        RUNTIME DESTINATION bin
        LIBRARY DESTINATION lib
        ARCHIVE DESTINATION lib
        PUBLIC_HEADER DESTINATION include
        )
