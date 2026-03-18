CXX = g++
CXXFLAGS = -std=c++20 -Wall

# Z3 (your local build)
Z3_ROOT   = $(HOME)/extend_z3/z3
Z3_INC_CXX= $(Z3_ROOT)/src/api/c++
Z3_INC_C  = $(Z3_ROOT)/src/api
Z3_LIBDIR = $(Z3_ROOT)/build

# Singular via pkg-config (installs headers/libs in /usr/include, /usr/lib)
SINGULAR_PKG = $(shell pkg-config --cflags --libs Singular)

# GMP (Ubuntu packages usually place headers in /usr/include and libs in /usr/lib)
GMP_LIB = -lgmp

# Include paths
INCLUDES = -I$(Z3_INC_CXX) -I$(Z3_INC_C) -Isrc

# Link flags:
# - use Z3 build dir
# - embed rpath so the executable can find libz3.so at runtime
LDFLAGS = -L$(Z3_LIBDIR) -Wl,-rpath=$(Z3_LIBDIR) -lz3

# Build rule: foo from foo.cpp
%: %.cpp
	$(CXX) $(CXXFLAGS) $(INCLUDES) -o $@ $< $(LDFLAGS) $(SINGULAR_PKG) $(GMP_LIB)

clean:
	rm -f $(basename $(wildcard *.cpp))
