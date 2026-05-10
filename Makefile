CXX ?= g++
TARGET ?= bin/main
BUILD_DIR ?= .build

SRCS := src/main.cpp src/util/rewrite.cpp
OBJS := $(SRCS:%.cpp=$(BUILD_DIR)/%.o)
DEPS := $(OBJS:.o=.d)

CPPFLAGS += -Isrc
CXXFLAGS += -std=c++20 -Wall -MMD -MP

# Z3 (your local build)
Z3_ROOT    = $(CURDIR)/z3
Z3_INC_CXX = $(Z3_ROOT)/src/api/c++
Z3_INC_C   = $(Z3_ROOT)/src/api
Z3_LIBDIR  = $(Z3_ROOT)/build

# Singular via pkg-config (installs headers/libs in /usr/include, /usr/lib)
SINGULAR_CFLAGS := $(patsubst -I%,-isystem %,$(shell pkg-config --cflags Singular))
SINGULAR_LIBS   := $(shell pkg-config --libs Singular)

# GMP (Ubuntu packages usually place headers in /usr/include and libs in /usr/lib)
GMP_LIB = -lgmp

# Include paths
CPPFLAGS += -isystem $(Z3_INC_CXX) -isystem $(Z3_INC_C) $(SINGULAR_CFLAGS)

# Link flags:
# - use Z3 build dir
# - embed rpath so the executable can find libz3.so at runtime
LDFLAGS += -L$(Z3_LIBDIR) -Wl,-rpath,$(Z3_LIBDIR)
LDLIBS  += -lz3 $(SINGULAR_LIBS) $(GMP_LIB)

.PHONY: all run clean
.DEFAULT_GOAL := all

all: $(TARGET)

$(TARGET): $(OBJS)
	@mkdir -p $(dir $@)
	$(CXX) $(LDFLAGS) -o $@ $^ $(LDLIBS)

run: $(TARGET)
	./$(TARGET)

# Compatibility for old commands that built ./main or ./src/main directly.
main src/main: $(TARGET)
	@mkdir -p $(dir $@)
	cp $< $@

$(BUILD_DIR)/%.o: %.cpp
	@mkdir -p $(dir $@)
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) -c -o $@ $<

$(OBJS): Makefile

clean:
	rm -rf $(BUILD_DIR) bin main src/main

-include $(DEPS)
