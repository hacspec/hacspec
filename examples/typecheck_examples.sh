#!/bin/bash

function typecheck {
  cargo build -p $1
  cargo hacspec $1
}

cargo clean
cargo install --path language
typecheck hacspec-chacha20
typecheck hacspec-chacha20poly1305
typecheck hacspec-poly1305
typecheck hacspec-curve25519
typecheck hacspec-hkdf
typecheck hacspec-hmac
typecheck hacspec-sha256
typecheck hacspec-ntru-prime
typecheck hacspec-p256
typecheck hacspec-riot-bootloader
typecheck hacspec-sha3
typecheck hacspec-gimli
typecheck hacspec-bls12-381
typecheck hacspec-ecdsa-p256-sha256
