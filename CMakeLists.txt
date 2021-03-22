cmake_minimum_required(VERSION 3.17)
project(aaf_cpp)

SET(CMAKE_CXX_STANDARD_LIBRARIES "${CMAKE_CXX_STANDARD_LIBRARIES} ${CMAKE_SOURCE_DIR}/libcadical.a")

set(CMAKE_CXX_STANDARD 14)

add_compile_definitions(NDEBUG)

add_compile_options(-Wall -Wextra -O3)

add_executable(aaf-cf cf.cpp)
add_executable(aaf-adm adm.cpp)
add_executable(aaf-cmp cmp.cpp)
add_executable(aaf-prf prf.cpp)
add_executable(aaf-stb stb.cpp)
