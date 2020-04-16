#! /bin/bash

echo "Primitive functions:"
cargo +nightly build --features="use_attributes" 2>&1 | grep --color=always "Primitive" | wc -l
echo "External functions:"
cargo +nightly build --features="use_attributes" 2>&1 | grep --color=always "External" | wc -l
echo "Library functions:"
cargo +nightly uild --features="use_attributes" 2>&1 | grep --color=always "Library" | wc -l
echo "To remove functions:"
cargo +nightly build --features="use_attributes" 2>&1 | grep --color=always "To remove" | wc -l
echo "Internal functions:"
cargo +nightly build --features="use_attributes" 2>&1 | grep --color=always "Internal" | wc -l
