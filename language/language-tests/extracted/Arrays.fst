module Arrays

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

type block_t = lseq (uint32) (usize 8)

let shuffle (b_0 : block_t) : block_t =
  let b_1 : block_t =
    b_0
  in
  let tmp_2 : uint32 =
    array_index (b_1) (usize 0)
  in
  let b_1 =
    array_upd b_1 (usize 0) (array_index (b_1) (usize 1))
  in
  let b_1 =
    array_upd b_1 (usize 1) (tmp_2)
  in
  b_1

let linear_manipulations (a_3 : seq pub_uint8) : seq pub_uint8 =
  let b_4 : seq pub_uint8 =
    if (true) then (a_3) else (a_3)
  in
  let c_5 : seq pub_uint8 =
    seq_clone (b_4)
  in
  let (c_5) =
    if false then begin
      let c_5 =
        seq_update_start (c_5) (b_4)
      in
      (c_5)
    end else begin
      let c_5 =
        b_4
      in
      (c_5)
    end
  in
  c_5

let creating_public_byte_seq () : seq pub_uint8 =
  array_from_list (
    let l =
      [pub_u8 0x0; pub_u8 0x1; pub_u8 0x2; pub_u8 0x3]
    in assert_norm (List.Tot.length l == 4); l)

let creating_byte_seq () : seq uint8 =
  array_from_list (
    let l =
      [
        secret (pub_u8 0x0);
        secret (pub_u8 0x1);
        secret (pub_u8 0x2);
        secret (pub_u8 0x3)
      ]
    in assert_norm (List.Tot.length l == 4); l)

