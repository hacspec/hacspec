module Rustspec.Loop

open Rustspec.Int

assume val foldi (#acc: Type) (lo: usize) (hi: usize) (f: (usize & acc) -> acc) (init: acc) : acc
