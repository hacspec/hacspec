module Another.Submod1.File

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Crate

noeq type res_typ_t =
| Ok_res_typ_t : res_t -> res_typ_t

let some_fun () : pub_uint8 =
  error_value_v

