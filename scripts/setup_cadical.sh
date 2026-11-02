#!/usr/bin/env bash

set -euo pipefail

# Build with CaDiCaL's own configured flags; a calling make would otherwise
# pass its command-line variables (such as CXXFLAGS) down through MAKEFLAGS.
unset MAKEFLAGS MFLAGS MAKELEVEL

version=${1:-2.2.1}
script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
project_root=$(cd "${script_dir}/.." && pwd)
target=${2:-"${project_root}/.deps/cadical-${version}"}
archive_url="https://github.com/arminbiere/cadical/archive/refs/tags/rel-${version}.tar.gz"

if [[ -r "${target}/VERSION" && -s "${target}/build/libcadical.a" ]]; then
    installed_version=$(<"${target}/VERSION")
    if [[ "${installed_version}" == "${version}" ]]; then
        echo "CaDiCaL ${version} is already built at ${target}"
        exit 0
    fi
    echo "Error: ${target} contains CaDiCaL ${installed_version}, expected ${version}" >&2
    exit 1
fi

if [[ -e "${target}" ]]; then
    echo "Error: incomplete CaDiCaL directory ${target}; remove it and run again" >&2
    exit 1
fi

dependency_dir=$(dirname "${target}")
mkdir -p "${dependency_dir}"
temporary_dir=$(mktemp -d "${dependency_dir}/.cadical-${version}.XXXXXX")
archive="${temporary_dir}/cadical.tar.gz"
partial_target=

cleanup() {
    rm -rf -- "${temporary_dir}" ${partial_target:+"${partial_target}"}
}
trap cleanup EXIT

echo "Downloading CaDiCaL ${version} from ${archive_url}"
curl --fail --location --silent --show-error "${archive_url}" --output "${archive}"
tar -xzf "${archive}" -C "${temporary_dir}"
source_dir="${temporary_dir}/cadical-rel-${version}"
if [[ ! -r "${source_dir}/VERSION" || "$(<"${source_dir}/VERSION")" != "${version}" ]]; then
    echo "Error: downloaded archive does not contain CaDiCaL ${version}" >&2
    exit 1
fi

mv "${source_dir}" "${target}"
# configure records absolute paths, so build in place; until the build
# finishes, the exit trap removes the tree so that a rerun starts clean.
partial_target=${target}
jobs=$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)
(
    cd "${target}"
    ./configure
    make -j"${jobs}"
)

test -s "${target}/build/libcadical.a"
partial_target=
echo "Built CaDiCaL ${version} at ${target}"
