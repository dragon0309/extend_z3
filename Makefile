CXX = g++
CXXFLAGS = -std=c++20 -Wall

# Z3 (your local build)
Z3_ROOT    = $(CURDIR)/z3
Z3_INC_CXX = $(Z3_ROOT)/src/api/c++
Z3_INC_C   = $(Z3_ROOT)/src/api
Z3_LIBDIR  = $(Z3_ROOT)/build

# Singular via pkg-config (installs headers/libs in /usr/include, /usr/lib)
SINGULAR_PKG = $(shell pkg-config --cflags --libs Singular)

# GMP (Ubuntu packages usually place headers in /usr/include and libs in /usr/lib)
GMP_LIB = -lgmp

# Include paths
INCLUDES = -I$(Z3_INC_CXX) -I$(Z3_INC_C) -Isrc

# Link flags:
# - use Z3 build dir
# - embed rpath so the executable can find libz3.so at runtime
LDFLAGS = -L$(Z3_LIBDIR) -Wl,-rpath,$(Z3_LIBDIR) -lz3

MAIN_SRC := src/main.cpp src/util/rewrite.cpp

# What to build = goals you typed, except clean. Bare `make` → main.
BIN_TARGETS := $(filter-out clean,$(MAKECMDGOALS))
ifeq ($(strip $(BIN_TARGETS)),)
BIN_TARGETS := main
endif

.PHONY: clean

# One recipe for whatever path(s) you pass: make src/main, make build/foo, ...
$(BIN_TARGETS): $(MAIN_SRC)
	@mkdir -p $(dir $@)
	$(CXX) $(CXXFLAGS) $(INCLUDES) -o $@ $(MAIN_SRC) $(LDFLAGS) $(SINGULAR_PKG) $(GMP_LIB)

clean:
	rm -f main src/main
