# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.13

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:


#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:


# Remove some rules from gmake that .SUFFIXES does not remove.
SUFFIXES =

.SUFFIXES: .hpux_make_needs_suffix_list


# Suppress display of executed commands.
$(VERBOSE).SILENT:


# A target that is always out of date.
cmake_force:

.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /home/darkey/.local/share/JetBrains/Toolbox/apps/CLion/ch-0/183.5153.40/bin/cmake/linux/bin/cmake

# The command to remove a file.
RM = /home/darkey/.local/share/JetBrains/Toolbox/apps/CLion/ch-0/183.5153.40/bin/cmake/linux/bin/cmake -E remove -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/darkey/univer/matlog/labs/b

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/darkey/univer/matlog/labs/b/cmake-build-debug

# Include any dependencies generated for this target.
include CMakeFiles/b.dir/depend.make

# Include the progress variables for this target.
include CMakeFiles/b.dir/progress.make

# Include the compile flags for this target's objects.
include CMakeFiles/b.dir/flags.make

CMakeFiles/b.dir/main.cpp.o: CMakeFiles/b.dir/flags.make
CMakeFiles/b.dir/main.cpp.o: ../main.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/darkey/univer/matlog/labs/b/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object CMakeFiles/b.dir/main.cpp.o"
	/usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/b.dir/main.cpp.o -c /home/darkey/univer/matlog/labs/b/main.cpp

CMakeFiles/b.dir/main.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/b.dir/main.cpp.i"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/darkey/univer/matlog/labs/b/main.cpp > CMakeFiles/b.dir/main.cpp.i

CMakeFiles/b.dir/main.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/b.dir/main.cpp.s"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/darkey/univer/matlog/labs/b/main.cpp -o CMakeFiles/b.dir/main.cpp.s

CMakeFiles/b.dir/AxiomChecker.cpp.o: CMakeFiles/b.dir/flags.make
CMakeFiles/b.dir/AxiomChecker.cpp.o: ../AxiomChecker.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/darkey/univer/matlog/labs/b/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Building CXX object CMakeFiles/b.dir/AxiomChecker.cpp.o"
	/usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/b.dir/AxiomChecker.cpp.o -c /home/darkey/univer/matlog/labs/b/AxiomChecker.cpp

CMakeFiles/b.dir/AxiomChecker.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/b.dir/AxiomChecker.cpp.i"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/darkey/univer/matlog/labs/b/AxiomChecker.cpp > CMakeFiles/b.dir/AxiomChecker.cpp.i

CMakeFiles/b.dir/AxiomChecker.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/b.dir/AxiomChecker.cpp.s"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/darkey/univer/matlog/labs/b/AxiomChecker.cpp -o CMakeFiles/b.dir/AxiomChecker.cpp.s

CMakeFiles/b.dir/Node.cpp.o: CMakeFiles/b.dir/flags.make
CMakeFiles/b.dir/Node.cpp.o: ../Node.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/darkey/univer/matlog/labs/b/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_3) "Building CXX object CMakeFiles/b.dir/Node.cpp.o"
	/usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/b.dir/Node.cpp.o -c /home/darkey/univer/matlog/labs/b/Node.cpp

CMakeFiles/b.dir/Node.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/b.dir/Node.cpp.i"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/darkey/univer/matlog/labs/b/Node.cpp > CMakeFiles/b.dir/Node.cpp.i

CMakeFiles/b.dir/Node.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/b.dir/Node.cpp.s"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/darkey/univer/matlog/labs/b/Node.cpp -o CMakeFiles/b.dir/Node.cpp.s

# Object files for target b
b_OBJECTS = \
"CMakeFiles/b.dir/main.cpp.o" \
"CMakeFiles/b.dir/AxiomChecker.cpp.o" \
"CMakeFiles/b.dir/Node.cpp.o"

# External object files for target b
b_EXTERNAL_OBJECTS =

b : CMakeFiles/b.dir/main.cpp.o
b : CMakeFiles/b.dir/AxiomChecker.cpp.o
b : CMakeFiles/b.dir/Node.cpp.o
b : CMakeFiles/b.dir/build.make
b : CMakeFiles/b.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/home/darkey/univer/matlog/labs/b/cmake-build-debug/CMakeFiles --progress-num=$(CMAKE_PROGRESS_4) "Linking CXX executable b"
	$(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/b.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
CMakeFiles/b.dir/build: b

.PHONY : CMakeFiles/b.dir/build

CMakeFiles/b.dir/clean:
	$(CMAKE_COMMAND) -P CMakeFiles/b.dir/cmake_clean.cmake
.PHONY : CMakeFiles/b.dir/clean

CMakeFiles/b.dir/depend:
	cd /home/darkey/univer/matlog/labs/b/cmake-build-debug && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/darkey/univer/matlog/labs/b /home/darkey/univer/matlog/labs/b /home/darkey/univer/matlog/labs/b/cmake-build-debug /home/darkey/univer/matlog/labs/b/cmake-build-debug /home/darkey/univer/matlog/labs/b/cmake-build-debug/CMakeFiles/b.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : CMakeFiles/b.dir/depend
