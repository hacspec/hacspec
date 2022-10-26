module Tuples

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

type res_t = (uint_size & uint_size)

noeq type res_typ_t =
| Ok_res_typ_t : res_t -> res_typ_t

let test_simpl_fails () : res_t =
  begin match Ok_res_typ_t ((usize 42, usize 42)) with
  | Ok_res_typ_t res_0 -> res_0 end

noeq type my_tuple_type_t =
| MyTupleType_my_tuple_type_t : (pub_uint16 & pub_uint8) -> my_tuple_type_t

let test_tuple_destructuring () : unit =
  let tuple_1 : my_tuple_type_t =
    my_tuple_type_clone (
      MyTupleType_my_tuple_type_t ((pub_u16 0x1, pub_u8 0x2)))
  in
  let MyTupleType_my_tuple_type_t ((a_2, b_3)) : my_tuple_type_t =
    tuple_1
  in
  ()

let unit_type () : unit =
  let () =
    if true then begin () end else begin () end
  in
  ()

noeq type empty_tuple_t =
| EmptyTuple_empty_tuple_t : unit -> empty_tuple_t

let test_empty_tuple () : empty_tuple_t =
  EmptyTuple_empty_tuple_t (())

