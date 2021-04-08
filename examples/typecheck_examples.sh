#!/bin/bash

set -e

function typecheck {
  echo "Typechecking $1 ..."
  cargo build -p $1
  if [ "$2" == "ec" ];
  then
    echo "    extracting EC ..."
    cargo hacspec -o $1.ec $1
  else
    cargo hacspec $1
  fi
  if [ "$3" == "fst" ];
  then
    echo "    extracting F* ..."
    cargo hacspec -o $1.fst $1
  fi
}

cargo clean
cargo install --path language
typecheck hacspec-chacha20             ec      fst
typecheck hacspec-chacha20poly1305     ec      fst
typecheck hacspec-poly1305             ec      fst
typecheck hacspec-curve25519           ec      fst
typecheck hacspec-hkdf                 ec      fst
typecheck hacspec-hmac              no-ec      fst
typecheck hacspec-sha256            no-ec      fst
typecheck hacspec-ntru-prime           ec      fst
typecheck hacspec-p256                 ec      fst
typecheck hacspec-riot-bootloader      ec      fst
typecheck hacspec-sha3              no-ec      fst
typecheck hacspec-gimli                ec      fst
typecheck hacspec-bls12-381         no-ec   no-fst
typecheck hacspec-ecdsa-p256-sha256 no-ec   no-fst
typecheck hacspec-aes               no-ec      fst
typecheck hacspec-gf128             no-ec      fst
