# Hacspec lib

## Print attributes and statistics

Using the `attributes` crate, we can monitor the number of functions in each
category : primitive, external, library, to remove, internal.

To get the statistics simply use

    bash get_func_stats.sh

*Note* : you need to have the nightly Rust toolchain installed to enable
this feature. Install it using :

    rustup toolchain install nightly
