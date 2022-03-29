#!/bin/bash

set -e

function typecheck {
  echo "Typechecking $1 ..."
  if [ "$2" == "ec" ];
  then
    echo "    extracting EC ..."
    mkdir -p target/easycrypt
    cargo hacspec -e ec -dir target/easycrypt/ -o $1 $1
  else
    cargo hacspec $1
  fi
  if [ -z "$5" ];
  then
    mkdir -p target/fstar
    fstar_dir=target/fstar/
    fstar_file=$1
  else
    fstar_dir=fstar/
    fstar_file=$5
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
    cargo hacspec -e json -dir target/json/ -o $1 $1
  fi
}

cd $(dirname "$0")/../
cargo clean
cargo build -p tls_cryptolib
cargo install --path language
typecheck tls_cryptolib             no-ec      fst    json  Hacspec.Tls.Cryptolib.fst
