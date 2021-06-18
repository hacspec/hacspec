#!/bin/bash

set -e

function typecheck {
  echo "Typechecking $1 ..."
  if [ "$2" == "ec" ];
  then
    echo "    extracting EC ..."
    mkdir -p target/easycrypt
    cargo hacspec -o target/easycrypt/$1.ec $1
  else
    cargo hacspec $1
  fi
  if [ -z "$5" ];
  then
    mkdir -p target/fstar
    fstar_file=target/fstar/$1.fst
  else
    fstar_file=fstar/$5
  fi
  if [ "$3" == "fst" ];
  then
    echo "    extracting F* ..."
    cargo hacspec -o $fstar_file $1
  fi
  if [ "$4" == "json" ];
  then
    echo "    extracting JSON ..."
    mkdir -p target/json
    cargo hacspec -o target/json/$1.json $1
  fi
}

cd $(dirname "$0")/../
cargo clean
cargo build
cargo install --path language
typecheck hacspec-chacha20             ec      fst    json  Hacspec.Chacha20.fst
typecheck hacspec-chacha20poly1305  no-ec      fst    json  Hacspec.Chacha20Poly1305.fst
typecheck hacspec-poly1305             ec      fst    json  Hacspec.Poly1305.fst
typecheck hacspec-curve25519           ec      fst    json
typecheck hacspec-hkdf              no-ec      fst    json
typecheck hacspec-hmac              no-ec      fst    json
typecheck hacspec-sha256            no-ec      fst    json
typecheck hacspec-ntru-prime           ec      fst    json
typecheck hacspec-p256              no-ec      fst    json
typecheck hacspec-riot-bootloader      ec      fst    json     Hacspec.Riot.Bootloader.fst
typecheck hacspec-riot-runqueue     no-ec      fst    no-json  Hacspec.Riot.Runqueue.fst
typecheck hacspec-sha3              no-ec      fst    json
typecheck hacspec-gimli                ec      fst    json
typecheck hacspec-bls12-381         no-ec   no-fst    json
typecheck hacspec-ecdsa-p256-sha256 no-ec   no-fst    json
typecheck hacspec-aes               no-ec      fst    json
typecheck hacspec-gf128             no-ec      fst    json
typecheck hacspec-aes128-gcm        no-ec      fst    json
