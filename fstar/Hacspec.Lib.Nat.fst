module Hacspec.Lib.Nat

open Hacspec.Lib.Int

let nat_mod (n: nat) = x:nat{x < n}

assume val from_secret_literal (#n: nat) (x:uint128) : nat_mod n
