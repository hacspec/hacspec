module Hacspec.Lib.Nat

open Hacspec.Lib.Int

let nat_mod (n: nat) = x:nat{x < n}

assume val from_secret_literal (x:uint128) : n:nat{v x == n}

let pow2 (x: nat) : nat = pow2 x
