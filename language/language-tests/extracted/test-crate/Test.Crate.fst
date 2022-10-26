module Test.Crate

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Submod1

open Submod2

let test_simpl_fails () : res_t =
  begin match Ok_res_typ_t ((usize 42, usize 42)) with
  | Ok_res_typ_t res_0 -> res_0 end

let test_tuple_destructuring () : unit =
  let tuple_1 : my_tuple_type_t =
    my_tuple_type_clone (
      MyTupleType_my_tuple_type_t ((pub_u16 0x1, pub_u8 0x2)))
  in
  let MyTupleType_my_tuple_type_t ((a_2, b_3)) : my_tuple_type_t =
    tuple_1
  in
  ()

