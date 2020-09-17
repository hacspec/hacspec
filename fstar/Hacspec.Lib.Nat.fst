module Hacspec.Lib.Nat

open Hacspec.Lib.Int
open Hacspec.Lib.Seq

let nat_mod (n: nat) = x:nat{x < n}

assume val from_secret_literal (x:uint128) : n:nat{v x == n}

assume val from_literal (x:pub_uint128) : n:nat{v x == n}

assume val to_public_byte_seq_le (n:nat) : seq pub_uint8

let pow2 (x: nat) : nat = pow2 x
