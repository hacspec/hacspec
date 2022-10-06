#!/usr/bin/env bash

set -e

function typecheck {
  echo "Typechecking $1 ..."
  if [ "$2" == "ec" ];
  then
    echo "    extracting EC ..."
    mkdir -p ../target/easycrypt
    cargo hacspec -e ec --dir ../target/easycrypt/ $1
  else
    cargo hacspec $1
  fi
  if [ -z "$6" ];
  then
    mkdir -p ../target/fstar
    fstar_dir=../target/fstar/
  else
    fstar_dir=../fstar/
  fi
  if [ "$3" == "fst" ];
  then
    echo "    extracting F* ..."
    cargo hacspec -e fst --dir $fstar_dir $1
  fi
  if [ "$4" == "json" ];
  then
    echo "    extracting JSON ..."
    mkdir -p ../target/json
    cargo hacspec -e json --dir ../target/json/ $1
  fi
  if [ "$5" == "coq" ];
  then
    echo "    extracting coq ..."
    mkdir -p ../target/coq
    cratename=$1
    prefix="hacspec-"
    outname=${cratename#"$prefix"}
    # capitalize first letter - macOS safe version (bash <= 3.2)
    outname=$(tr '[:lower:]' '[:upper:]' <<<"${outname:0:1}")${outname:1}
    cargo hacspec -e v --dir ../target/coq/ -o ${outname} $1
  fi
}

cwd=$(cd $(dirname $0); pwd -P)
cd $cwd/../
cargo clean
cargo build
cargo install --path language
cd $cwd
cargo clean
cargo build
# Examples:
typecheck hacspec-chacha20             ec      fst    json      coq
typecheck hacspec-chacha20poly1305  no-ec      fst    json      coq
typecheck hacspec-poly1305             ec      fst    json      coq
typecheck hacspec-curve25519           ec      fst    json      coq
typecheck hacspec-hkdf              no-ec      fst    json      no-coq
typecheck hacspec-hmac              no-ec      fst    json      coq
typecheck hacspec-sha256            no-ec      fst    json      coq
typecheck hacspec-ntru-prime           ec      fst    json      no-coq
typecheck hacspec-p256              no-ec      fst    json      coq
typecheck hacspec-riot-bootloader      ec      fst    json      no-coq
typecheck hacspec-riot-runqueue     no-ec      fst    no-json   no-coq
typecheck hacspec-sha3              no-ec      fst    json      no-coq
typecheck hacspec-gimli                ec      fst    json      no-coq
typecheck hacspec-bls12-381         no-ec   no-fst    json      coq
typecheck hacspec-ecdsa-p256-sha256 no-ec   no-fst    json      coq
typecheck hacspec-aes               no-ec      fst    json      no-coq
typecheck hacspec-gf128             no-ec      fst    json      coq
typecheck hacspec-aes128-gcm        no-ec      fst    json      no-coq
typecheck hacspec-bls12-381-hash    no-ec   no-fst    json      coq
typecheck hacspec-sha512            no-ec   no-fst    json      coq
typecheck hacspec-ed25519           no-ec   no-fst    json      coq
typecheck hacspec-linalg            no-ec   no-fst    json      coq
typecheck hacspec-ristretto         no-ec   no-fst    json      coq
typecheck hacspec-edwards25519      no-ec   no-fst    json      coq
typecheck hacspec-edwards25519-hash no-ec   no-fst    json      coq
typecheck hacspec-linalg            no-ec   no-fst    json      coq
typecheck hacspec-rsa-pkcs1         no-ec   no-fst    json      coq
typecheck hacspec-rsa-fdh-vrf       no-ec   no-fst    json      coq
typecheck hacspec-bip-340           no-ec   no-fst    json      coq
typecheck hacspec-sha1                 ec      fst    json      coq
# Protocols:
typecheck tls_cryptolib             no-ec      fst    json      coq
