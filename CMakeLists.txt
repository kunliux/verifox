cmake_minimum_required(VERSION 3.12)
project(verifox)

set(CMAKE_CXX_STANDARD 14)

include_directories(src/hasco)
include_directories(src/path-symex-ed)
include_directories(src/solver)
include_directories(src/util)

add_executable(verifox
        src/hasco/hasco_main.cpp
        src/hasco/hasco_parseoptions.cpp
        src/hasco/hasco_parseoptions.h
        src/hasco/path_search.cpp
        src/hasco/path_search.h
        src/hasco/trace_partition.cpp
        src/hasco/trace_partition.h
        src/path-symex-ed/path_symex.cpp
        src/path-symex-ed/path_symex.h
        src/path-symex-ed/path_symex_state_ed.cpp
        src/path-symex-ed/path_symex_state_ed.h
        src/solver/incremental_solver.cpp
        src/solver/incremental_solver.h
        src/solver/verifox_solver.h
        src/util/parse_options.cpp
        src/util/parse_options.h
        src/util/std_utils.cpp
        src/util/ui_message.cpp
        src/util/ui_message.h
        src/util/version.h)
