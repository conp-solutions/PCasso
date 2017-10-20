#!/bin/bash
# build.sh, Norbert Manthey, 2017
#
# build pcasso solver to be used with the pcasso.sh script
#
# Note, pcasso has to be build separately after a "make clean", because the
# build system does not understand the differences when compiling pcasso or
# the other systems that are implemented in this code base. Hence, this script
# automates the process.

# fail if a step fails
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# build coprocessor in root of repository and move it here
make clean
make coprocessorRS -j $(nproc) -C "$DIR/.."
mv "$DIR/../coprocessor" "$DIR"

# build pcasso in root of repository and move it here
make clean
make pcassoRS -j $(nproc) -C "$DIR/.."
mv "$DIR/../pcasso" "$DIR"
