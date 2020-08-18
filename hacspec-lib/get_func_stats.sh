#! /bin/bash

set -e

cwd=$(cd $(dirname $0); pwd -P)
pushd $cwd

NIGHTLY="${RUST_NIGHTLY:-nightly}"

cargo +$NIGHTLY build --tests --features="use_attributes"

REMOVE='\033[1;31m'
INTERNAL='\033[1;32m'
EXTERNAL='\033[1;33m'
LIBRARY='\033[1;34m'
PRIMITIVE='\033[1;36m'
NC='\033[0m' # No Color

echo -e -n "${PRIMITIVE}Primitive functions:${NC} "
cargo +$NIGHTLY build --features="use_attributes" 2>&1 | grep --color=always "Primitive" | wc -l
echo -e -n "${EXTERNAL}External functions:${NC} "
cargo +$NIGHTLY build --features="use_attributes" 2>&1 | grep --color=always "External" | wc -l
echo -e -n "${LIBRARY}Library functions:${NC} "
cargo +$NIGHTLY build --features="use_attributes" 2>&1 | grep --color=always "Library" | wc -l
echo -e -n "${REMOVE}To remove functions:${NC} "
cargo +$NIGHTLY build --features="use_attributes" 2>&1 | grep --color=always "To remove" | wc -l
echo -e -n "${INTERNAL}Internal functions:${NC} "
cargo +$NIGHTLY build --features="use_attributes" 2>&1 | grep --color=always "Internal" | wc -l

popd
