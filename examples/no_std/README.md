# Introduction

This folder contains a bare metal (no_std) application for Cortex-M, intended
to be used to test hacspec on no_std targets.

It's configured to work on the lm3s6965evb (Cortex-M3) board, which happens to
be supported by QEMU's system emulation.

## Prerequisites

- install QEMU
- `rustup target add thumbv7m-none-eabi`

## How to use

This folder's `.cargo/config.toml` configures the target (`thumbv7m-none-eabi`)
and some needed RUSTFLAGS, so this should pretty much just work(tm):

    cargo run

You can exit QEMU pressing `CTRL-A`, then `X`. Or, if you're using tmux like
me, `CTRL-A`, `A`, `X`.
