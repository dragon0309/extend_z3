# extend_z3

Build from the repository root with GNU Make and a C++20 compiler. The source
uses POSIX APIs (`fork`, `waitpid`, `unistd.h`); native Windows builds are not
supported by this Makefile. Linux is the locally verified platform.

Required dependencies:

- Z3 headers and library from upstream Z3 at commit `4b8a27090`, normally in
  `z3/src/api` and `z3/build`. Use matching headers and libraries from the same
  build. Building Z3 needs CMake and Python 3.
- Singular development headers and libraries, discoverable as `Singular` by
  `pkg-config`, plus GMP and Boost headers.
- Boolector 3.2.4 with its btor2parser and Lingeling static libraries.
  Boolector's `make install` copies neither library; both stay in
  `deps/install/lib` of the Boolector source tree, so set `BOOLECTOR_DEPS_ROOT`
  to that tree's `deps/install` (see `config.local.mk` below).
- CaDiCaL 2.2.1, installed using `make setup-cadical` (requires Bash, curl, tar,
  and network access), or provided via `CADICAL_ROOT` and `CADICAL_LIB`.
  `CADICAL_ROOT` must be a CaDiCaL source tree, since `make` checks its
  `VERSION` file.

```sh
git clone https://github.com/Z3Prover/z3.git z3
git -C z3 checkout 4b8a27090109b51023b29c756b9822f5ee89418a
cmake -S z3 -B z3/build -DCMAKE_BUILD_TYPE=Release
cmake --build z3/build -j"$(nproc)"
make setup-cadical
make -j2
bash tests/eqmod/run.sh
```

`bash tests/eqmod/run.sh` runs the end-to-end eqmod tests (about a second), and
`./scripts/regression_76.sh` runs the fixed 76-case regression (about 11
minutes). The regression runs each case under `systemd-run --user` with a 15 GB
memory cap; pass `--no-systemd` where no systemd user session is available.
Before compiling, `make` checks that Z3, Singular, Boolector, and CaDiCaL are
where the flags point and stops with a message naming the missing piece;
`make check-deps` runs only that check.

Paths default to `z3/` for Z3, `/usr/local` for Boolector and its dependencies,
and `.deps/cadical-2.2.1` for CaDiCaL. Put machine-specific settings in the
optional, Git-ignored `config.local.mk`, for example:

```make
BOOLECTOR_DEPS_ROOT := /path/to/boolector-3.2.4/deps/install
# BOOLECTOR_ROOT := /opt/boolector
# Z3_ROOT := /opt/custom-z3
# Z3_INC_CXX := /opt/custom-z3/include
# Z3_INC_C := /opt/custom-z3/include
# Z3_LIBDIR := /opt/custom-z3/lib
```

Command-line assignments override the local configuration:

```sh
make CXX=c++ BOOLECTOR_ROOT=/opt/boolector \
  BOOLECTOR_DEPS_ROOT=/path/to/boolector-3.2.4/deps/install
make SINGULAR_BUILD=/path/to/Singular/build SINGULAR_SRC=/path/to/Singular
make CXXFLAGS='-O0 -g' CPPFLAGS='-I/opt/boost/include'
```

`CPPFLAGS`, `LDFLAGS`, and `LDLIBS` are appended to the project's own flags;
`CXXFLAGS` replaces only the default `-O2 -DNDEBUG`.

For nonstandard layouts, override `BOOLECTOR_LIBDIR`, `BOOLECTOR_DEPS_LIBDIR`,
`BOOLECTOR_CPPFLAGS`, `BOOLECTOR_LDFLAGS`, or `BOOLECTOR_LIBS`. Singular flags
can likewise be overridden with `SINGULAR_CFLAGS`, `SINGULAR_LDFLAGS`, and
`SINGULAR_LIBS`; `PKG_CONFIG` selects the discovery tool. `rpath-link` is emitted
only on Linux; `HOST_OS` can be set explicitly for a target platform.

Use paths without whitespace for dependency and build directories. When changing
compiler, dependency paths, or flags, run `make clean` before rebuilding. A custom
Singular build defaults to `.build/singular-local`; otherwise objects go to
`.build`. `BUILD_DIR` and `TARGET` can override these locations. `make clean`
removes the selected object directory and executable.
