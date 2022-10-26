module Expr.Block

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

let foo (x_0 : (option pub_uint32)) : bool =
  begin match x_0 with | None -> false | Some _ -> true end

let final_if (a_1 : seq pub_uint8) : seq pub_uint8 =
  if (true) then (a_1) else (a_1)

