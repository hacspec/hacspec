#!/bin/bash

set -e

function typecheck {
  echo "Typechecking $1 ..."
  if [ "$2" == "ec" ];
  then
    echo "    extracting EC ..."
    mkdir -p target/easycrypt
    cargo hacspec -e ec -dir target/easycrypt/ $1
  else
    cargo hacspec $1
  fi
  if [ -z "$6" ];
  then
    mkdir -p target/fstar
    fstar_dir=target/fstar/
    fstar_file=$1
  else
    fstar_dir=fstar/
    fstar_file=$6
  fi
  if [ "$3" == "fst" ];
  then
    echo "    extracting F* ..."
    cargo hacspec -e fst -dir $fstar_dir -o $fstar_file $1
  fi
  if [ "$4" == "json" ];
  then
    echo "    extracting JSON ..."
    mkdir -p target/json
    cargo hacspec -e json -dir target/json/ $1
  fi
  if [ "$5" == "coq" ];
  then
    echo "    extracting coq ..."
    mkdir -p target/coq
    cratename=$1
    prefix="hacspec-"
    outname=${cratename#"$prefix"}
    # capitalize first letter - macOS safe version (bash <= 3.2)
    outname=$(tr '[:lower:]' '[:upper:]' <<<"${outname:0:1}")${outname:1}
    cargo hacspec -e v -dir target/coq/ -o ${outname} $1
  fi
}

cd $(dirname "$0")/../
cargo clean
cargo build
cargo install --path language
typecheck hacspec-chacha20             ec      fst    json      coq  Hacspec.Chacha20.fst
typecheck hacspec-chacha20poly1305  no-ec      fst    json      coq  Hacspec.Chacha20Poly1305.fst
typecheck hacspec-poly1305             ec      fst    json      coq  Hacspec.Poly1305.fst
typecheck hacspec-curve25519           ec      fst    json      coq  Hacspec.Curve25519.fst
typecheck hacspec-hkdf              no-ec      fst    json      no-coq  Hacspec.Hkdf.fst
typecheck hacspec-hmac              no-ec      fst    json      coq  Hacspec.Hmac.fst
typecheck hacspec-sha256            no-ec      fst    json      coq     Hacspec.Sha256.fst
typecheck hacspec-ntru-prime           ec      fst    json      no-coq  Hacspec.NtruPrime.fst
typecheck hacspec-p256              no-ec      fst    json      coq  Hacspec.P256.fst
typecheck hacspec-riot-bootloader      ec      fst    json      no-coq  Hacspec.Riot.Bootloader.fst
typecheck hacspec-riot-runqueue     no-ec      fst    no-json   no-coq  Hacspec.Riot.Runqueue.fst
typecheck hacspec-sha3              no-ec      fst    json      no-coq  Hacspec.Sha3.fst
typecheck hacspec-gimli                ec      fst    json      no-coq
typecheck hacspec-bls12-381         no-ec   no-fst    json      coq
typecheck hacspec-ecdsa-p256-sha256 no-ec   no-fst    json      coq
typecheck hacspec-aes               no-ec      fst    json      no-coq
typecheck hacspec-gf128             no-ec      fst    json      coq
typecheck hacspec-aes128-gcm        no-ec      fst    json      no-coq
typecheck hacspec-bls12-381-hash    no-ec   no-fst    json      coq
typecheck hacspec-sha512            no-ec   no-fst    json      coq
typecheck hacspec-ed25519           no-ec   no-fst    json      coq
