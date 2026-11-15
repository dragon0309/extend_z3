# Machine-specific paths belong in this optional, Git-ignored file.
-include config.local.mk

CXX ?= g++
PKG_CONFIG ?= pkg-config
HOST_OS ?= $(shell uname -s)
comma := ,
SINGULAR_BUILD ?=

ifeq ($(strip $(SINGULAR_BUILD)),)
BUILD_DIR ?= .build
else ifeq ($(origin BUILD_DIR), undefined)
BUILD_DIR := .build/singular-local
endif

MAIN_SRCS := \
	src/main.cpp \
	src/eqmod_engine.cpp \
	src/eqmod_lowering.cpp \
	src/eqmod_refutation.cpp \
	src/eqmod_true_lemma.cpp \
	src/eqmod_validation.cpp \
	src/cli_options.cpp \
	src/cli_report.cpp \
	src/smt2_frontend.cpp \
	src/solver_option_adapters.cpp \
	src/util/auto_zero_lemmas.cpp \
	src/util/bv_eq.cpp \
	src/util/live_global_eq_validator.cpp \
	src/util/implied_eq_partition_refiner.cpp \
	src/util/implied_eq_partition_variants.cpp \
	src/util/implied_eq_partition_prepass.cpp \
	src/util/pconst_purification.cpp \
	src/util/rewrite.cpp \
	src/util/ideal_rewrite.cpp \
	src/util/singular_dump.cpp \
	src/util/singular_poly.cpp \
	src/util/singular_lowering.cpp \
	src/util/singular_membership_prover.cpp \
	src/util/singular_process_pool.cpp \
	src/util/singular_lift_prover.cpp \
	src/util/gb_preprocess.cpp \
	src/util/singular_runtime_stats.cpp
MAIN_OBJS := $(MAIN_SRCS:%.cpp=$(BUILD_DIR)/%.o)
TARGET ?= bin/main
LINK_STAMP := $(TARGET).link

DEPS := $(MAIN_OBJS:.o=.d)

PROJECT_CPPFLAGS := -Isrc
PROJECT_CXXFLAGS := -std=c++20 -Wall -MMD -MP -pthread
CXXFLAGS ?= -O2 -DNDEBUG

# Z3 defaults to the local build of upstream Z3 (commit 4b8a27090) in z3/. All paths can be overridden.
Z3_ROOT    ?= $(CURDIR)/z3
Z3_INC_CXX ?= $(Z3_ROOT)/src/api/c++
Z3_INC_C   ?= $(Z3_ROOT)/src/api
Z3_LIBDIR  ?= $(Z3_ROOT)/build

# Boolector 3.2.4 C API and its static parser/Lingeling dependencies. CaDiCaL is
# selected independently so removing an unrelated shared library cannot
# silently change Boolector's SAT engine implementation through ELF symbol
# resolution.
BOOLECTOR_ROOT ?= /usr/local
BOOLECTOR_DEPS_ROOT ?= $(BOOLECTOR_ROOT)
BOOLECTOR_LIBDIR ?= $(BOOLECTOR_ROOT)/lib
BOOLECTOR_DEPS_LIBDIR ?= $(BOOLECTOR_DEPS_ROOT)/lib
BOOLECTOR_CPPFLAGS ?= -isystem $(BOOLECTOR_ROOT)/include
BOOLECTOR_LDFLAGS ?= -L$(BOOLECTOR_LIBDIR) -Wl,-rpath,$(abspath $(BOOLECTOR_LIBDIR))
CADICAL_VERSION ?= 2.2.1
CADICAL_ROOT ?= $(CURDIR)/.deps/cadical-$(CADICAL_VERSION)
CADICAL_LIB ?= $(CADICAL_ROOT)/build/libcadical.a
BOOLECTOR_LIBS ?= -lboolector \
	$(BOOLECTOR_DEPS_LIBDIR)/libbtor2parser.a \
	$(BOOLECTOR_DEPS_LIBDIR)/liblgl.a \
	$(CADICAL_LIB)

# Singular:
#   default: use the system installation reported by pkg-config.
#   custom:  make SINGULAR_BUILD=/path/to/Singular/build
SINGULAR_SRC ?= $(patsubst %/build,%,$(SINGULAR_BUILD))

ifeq ($(strip $(SINGULAR_BUILD)),)
SINGULAR_CFLAGS ?= $(patsubst -I%,-isystem %,$(shell $(PKG_CONFIG) --cflags Singular))
SINGULAR_LIBS   ?= $(shell $(PKG_CONFIG) --libs Singular)
else
SINGULAR_LIBDIRS := \
	$(SINGULAR_BUILD)/Singular/.libs \
	$(SINGULAR_BUILD)/libpolys/polys/.libs \
	$(SINGULAR_BUILD)/factory/.libs \
	$(SINGULAR_BUILD)/resources/.libs \
	$(SINGULAR_BUILD)/omalloc/.libs
SINGULAR_CFLAGS ?= \
	-isystem $(SINGULAR_BUILD) \
	-isystem $(SINGULAR_BUILD)/libpolys \
	-isystem $(SINGULAR_BUILD)/factory/include \
	-isystem $(SINGULAR_BUILD)/omalloc \
	-isystem $(SINGULAR_SRC) \
	-isystem $(SINGULAR_SRC)/libpolys \
	-isystem $(SINGULAR_SRC)/factory \
	-isystem $(SINGULAR_SRC)/factory/include
SINGULAR_LDFLAGS ?= \
	$(addprefix -L,$(SINGULAR_LIBDIRS)) \
	$(foreach dir,$(SINGULAR_LIBDIRS),-Wl$(comma)-rpath$(comma)$(abspath $(dir))) \
	$(if $(filter Linux,$(HOST_OS)),$(foreach dir,$(SINGULAR_LIBDIRS),-Wl$(comma)-rpath-link$(comma)$(abspath $(dir))))
SINGULAR_LIBS ?= -lSingular -lpolys -lfactory -lsingular_resources -lomalloc -lflint -lmpfr -lntl -lgmp -lreadline
endif

GMP_LIB ?= -lgmp

# Include paths
PROJECT_CPPFLAGS += -isystem $(Z3_INC_CXX) -isystem $(Z3_INC_C) $(SINGULAR_CFLAGS) $(BOOLECTOR_CPPFLAGS)

# Link flags:
# - use Z3 build dir
# - embed absolute rpath so execution does not depend on the working directory
# - LDFLAGS and LDLIBS given on the command line are appended, not substituted
PROJECT_LDFLAGS := -L$(Z3_LIBDIR) -Wl,-rpath,$(abspath $(Z3_LIBDIR)) $(SINGULAR_LDFLAGS) $(BOOLECTOR_LDFLAGS)
PROJECT_LDLIBS := -lz3 $(SINGULAR_LIBS) $(GMP_LIB) $(BOOLECTOR_LIBS) -pthread

.PHONY: all clean check-deps setup-cadical check-cadical print-cadical-config FORCE
# Every target is explicit; drop make's built-in suffix rules.
.SUFFIXES:
.DEFAULT_GOAL := all

all: $(TARGET)

setup-cadical:
	./scripts/setup_cadical.sh "$(CADICAL_VERSION)" "$(CADICAL_ROOT)"

check-cadical:
	@test -r "$(CADICAL_ROOT)/VERSION" || { \
		echo "Missing CaDiCaL $(CADICAL_VERSION) source at $(CADICAL_ROOT); run 'make setup-cadical'" >&2; \
		exit 1; \
	}
	@test "$$(cat "$(CADICAL_ROOT)/VERSION")" = "$(CADICAL_VERSION)" || { \
		echo "CaDiCaL version mismatch: expected $(CADICAL_VERSION), found $$(cat "$(CADICAL_ROOT)/VERSION")" >&2; \
		exit 1; \
	}
	@test -s "$(CADICAL_LIB)" || { \
		echo "Missing CaDiCaL archive $(CADICAL_LIB); run 'make setup-cadical'" >&2; \
		exit 1; \
	}

print-cadical-config: check-cadical
	@echo "CaDiCaL version: $(CADICAL_VERSION)"
	@echo "CaDiCaL root:    $(CADICAL_ROOT)"
	@echo "CaDiCaL archive: $(CADICAL_LIB)"

# Stop before compiling when a dependency is not where the flags point.
check-deps: check-cadical
	@test -f "$(Z3_INC_C)/z3.h" && test -f "$(Z3_INC_CXX)/z3++.h" || { \
		echo "Missing Z3 headers in $(Z3_INC_C) or $(Z3_INC_CXX); build Z3 as in README.md or set Z3_ROOT" >&2; \
		exit 1; \
	}
	@ls "$(Z3_LIBDIR)"/libz3.* >/dev/null 2>&1 || { \
		echo "Missing libz3 in $(Z3_LIBDIR); build Z3 as in README.md or set Z3_LIBDIR" >&2; \
		exit 1; \
	}
	@$(if $(strip $(SINGULAR_BUILD)),test -d "$(SINGULAR_BUILD)" || { echo "SINGULAR_BUILD $(SINGULAR_BUILD) does not exist" >&2; exit 1; },true)
	@test -n "$(strip $(SINGULAR_LIBS))" || { \
		echo "Singular not found: $(PKG_CONFIG) --libs Singular is empty; install the Singular development package or set SINGULAR_BUILD" >&2; \
		exit 1; \
	}
	@$(if $(findstring $(BOOLECTOR_ROOT)/include,$(BOOLECTOR_CPPFLAGS)),test -f "$(BOOLECTOR_ROOT)/include/boolector/boolector.h" || { echo "Missing boolector/boolector.h under $(BOOLECTOR_ROOT)/include; set BOOLECTOR_ROOT" >&2; exit 1; },true)
	@$(if $(findstring -L$(BOOLECTOR_LIBDIR),$(BOOLECTOR_LDFLAGS)),ls "$(BOOLECTOR_LIBDIR)"/libboolector.* >/dev/null 2>&1 || { echo "Missing libboolector in $(BOOLECTOR_LIBDIR); set BOOLECTOR_ROOT" >&2; exit 1; },true)
	@for archive in $(filter %.a,$(BOOLECTOR_LIBS)); do \
		test -f "$$archive" || { echo "Missing static library $$archive; set BOOLECTOR_DEPS_ROOT" >&2; exit 1; }; \
	done

# bin/main is shared by every BUILD_DIR. Record its link command and static
# archive checksums beside it, so a different SINGULAR_BUILD, link flag, or
# rebuilt archive relinks it even when every object is older.
$(LINK_STAMP): FORCE | check-deps
	@mkdir -p "$(dir $@)"
	@set -e; temporary="$@.tmp"; \
	{ \
		echo '$(CXX) $(PROJECT_LDFLAGS) $(LDFLAGS) $(MAIN_OBJS) $(PROJECT_LDLIBS) $(LDLIBS)'; \
		cksum $(filter %.a,$(PROJECT_LDLIBS) $(LDLIBS)) </dev/null; \
	} > "$$temporary"; \
	if ! test -r "$@" || ! cmp -s "$$temporary" "$@"; then \
		mv "$$temporary" "$@"; \
	else \
		rm -f "$$temporary"; \
	fi

FORCE:

$(TARGET): $(MAIN_OBJS) $(LINK_STAMP)
	@mkdir -p "$(dir $@)"
	$(CXX) $(PROJECT_LDFLAGS) $(LDFLAGS) -o "$@" $(MAIN_OBJS) $(PROJECT_LDLIBS) $(LDLIBS)

$(BUILD_DIR)/%.o: %.cpp
	@mkdir -p "$(dir $@)"
	$(CXX) $(PROJECT_CPPFLAGS) $(CPPFLAGS) $(PROJECT_CXXFLAGS) $(CXXFLAGS) -c -o "$@" "$<"

$(MAIN_OBJS): Makefile $(wildcard config.local.mk) | check-deps

clean:
	rm -rf -- "$(BUILD_DIR)" "$(TARGET)" "$(LINK_STAMP)"

-include $(DEPS)
