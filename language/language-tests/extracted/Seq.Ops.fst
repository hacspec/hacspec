module Seq.Ops

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

let foo (x_0 : seq uint8) (y_1 : seq uint8) : seq uint8 =
  (x_0) `seq_add (+.)` (y_1)

let bar (x_2 : seq uint8) (y_3 : seq uint8) : seq uint8 =
  (x_2) `seq_or (|.)` (y_3)

