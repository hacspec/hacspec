module Result

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

type simple_output_t = lseq (uint8) (usize 3)

type simple_output_result_t = (result simple_output_t pub_uint8)

type s_result_t = simple_output_result_t

let foo (x_0 : (result (result uint32 uint_size) uint_size)) : uint32 =
  let y_1 : (result uint32 uint_size) =
    Ok (secret (pub_u32 0x1))
  in
  let z_2 : (result uint32 uint_size) =
    Err (usize 8)
  in
  begin match x_0 with
  | Ok _ -> secret (pub_u32 0x0)
  | Err x_3 -> secret (pub_u32 (x_3)) end

let other () : (result simple_output_t pub_uint8) =
  Err (pub_u8 0x1)

let other_result_alias () : simple_output_result_t =
  Err (pub_u8 0x1)

let type_confusion () : (result simple_output_t pub_uint8) =
  other ()

let return_type_alias () : (result simple_output_t pub_uint8) =
  Err (pub_u8 0x1)

let type_alias_question_mark () : (result simple_output_t pub_uint8) =
  begin match (other_result_alias ()) with
  | Err x -> Err x
  | Ok  (other_result_4 : simple_output_t) ->
    Err (pub_u8 0x1) end

let type_alias_question_mark_return () : simple_output_result_t =
  begin match (other ()) with
  | Err x -> Err x
  | Ok  (other_result_5 : simple_output_t) ->
    Err (pub_u8 0x1) end

let type_double_alias_question_mark_return () : s_result_t =
  begin match (other ()) with
  | Err x -> Err x
  | Ok  (other_result_6 : simple_output_t) ->
    Err (pub_u8 0x1) end

let unwrap_result () : simple_output_t =
  result_unwrap (other ())

let match_result () : simple_output_t =
  let result_value_7 : (result simple_output_t pub_uint8) =
    type_double_alias_question_mark_return ()
  in
  begin match result_value_7 with
  | Ok r_8 -> r_8
  | Err _ -> array_new_ (secret (pub_u8 0x0)) (3) end

