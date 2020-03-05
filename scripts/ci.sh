#!/bin/bash
# Norbert Manthey, 2020
#
# This script builds relevant targets and runs the fuzzer on the solvers.
#
# It is intended to be used as a script for a CI-runner but can be used for local runs too.

# Exits the script immediately if a command exits with a non-zero status
set -e

# We will check 2K formulas before declaring success
declare -r n_runs=2000

# Directory of this script (in repo/scripts)
script_dir=$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )
# Get absolute path for root directory of the repository
repo_dir="$(dirname "$script_dir")"

echo "Building targets"
cd "$repo_dir"

# Clean repository
make clean

# Perform release build
make pcassoRS

# Clean again
make clean

# Perform debug build
make pcassod

# Some status update
echo "build complete"

# Enter fuzzing directory
cd "$repo_dir"/cnfs

# Build required tools
make

# Fuzz the current solver for some formulas
declare -i exitcode=0
./fuzzcheck.sh "$repo_dir"/cnfs/pcasso.sh "$n_runs" || exitcode=$?

exit $exitcode
