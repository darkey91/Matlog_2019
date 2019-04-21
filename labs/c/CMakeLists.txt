cmake_minimum_required(VERSION 2.8)
project(glivenko)

set(CMAKE_CXX_STANDARD 14)

add_executable(glivenko main.cpp AxiomChecker.cpp AxiomChecker.h Node.cpp Node.h)

#target_compile_options(b PUBLIC -fsanitize=address -Wall -mavx -fno-omit-frame-pointer)
#target_link_libraries(b -lasan)
