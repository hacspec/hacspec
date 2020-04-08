#! /bin/bash

echo "Primitive functions:"
cargo build --features="print_attributes" 2>&1 | grep --color=always "Primitive" | wc -l
echo "External functions:"
cargo build --features="print_attributes" 2>&1 | grep --color=always "External" | wc -l
echo "Library functions:"
cargo build --features="print_attributes" 2>&1 | grep --color=always "Library" | wc -l
echo "To remove functions:"
cargo build --features="print_attributes" 2>&1 | grep --color=always "To remove" | wc -l
echo "Internal functions:"
cargo build --features="print_attributes" 2>&1 | grep --color=always "Internal" | wc -l
