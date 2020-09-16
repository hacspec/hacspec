module Hacspec.Lib.Loop

open Hacspec.Lib.Int

assume val foldi (#acc: Type) (lo: uint_size) (hi: uint_size) (f: (uint_size & acc) -> acc) (init: acc) : acc
