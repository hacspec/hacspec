module Hacspec.Poly1305

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open Hacspec.Lib
open FStar.Mul



type key_poly = lseq (uint8) (usize 32)

let blocksize : uint_size =
  usize 16

type block = lseq (uint8) (blocksize)

type tag = lseq (pub_uint8) (blocksize)

type field_canvas = lseq (pub_uint8) (17)

type field_element = nat_mod 0x03fffffffffffffffffffffffffffffffb

let le_bytes_to_num (b_0 : byte_seq) : uint128 =
  let block_as_u128_1 =
    array_from_slice (secret (pub_u8 0x8)) (16) (b_0) (usize 0) (
      min (blocksize) (seq_len (b_0)))
  in
  uint128_from_le_bytes (block_as_u128_1)

let clamp (r_2 : uint128) : field_element =
  let r_uint_3 =
    (r_2) &. (secret (pub_u128 0xffffffc0ffffffc0ffffffc0fffffff))
  in
  nat_from_secret_literal (0x03fffffffffffffffffffffffffffffffb) (r_uint_3)

let encode (block_uint_4 : uint128) (len_5 : uint_size{
  (**) len_5 < 17
  }) : field_element =
  let w_elem_6 =
    nat_from_secret_literal (0x03fffffffffffffffffffffffffffffffb) (
      block_uint_4)
  in
  (**) assert_norm (pow2 128 < 0x03fffffffffffffffffffffffffffffffb);
  (**) Math.Lemmas.pow2_le_compat 128 (8 * len_5);
  let l_elem_7 =
    nat_pow2 (0x03fffffffffffffffffffffffffffffffb) ((usize 8) * (len_5))
  in
  (w_elem_6) +% (l_elem_7)

let num_to_16_le_bytes (a_8 : field_element) : tag =
  let n_v_9 =
    nat_to_public_byte_seq_le (0x03fffffffffffffffffffffffffffffffb) (17) (a_8)
  in
  array_from_seq (blocksize) (seq_slice (n_v_9) (usize 0) (blocksize))

let poly (m_10 : byte_seq) (key_11 : key_poly) : tag =
  let r_12 = le_bytes_to_num (array_slice (key_11) (usize 0) (blocksize)) in
  let r_13 = clamp (r_12) in
  let s_14 = le_bytes_to_num (array_slice (key_11) (blocksize) (blocksize)) in
  let s_15 =
    nat_from_secret_literal (0x03fffffffffffffffffffffffffffffffb) (s_14)
  in
  let a_16 =
    nat_from_literal (0x03fffffffffffffffffffffffffffffffb) (pub_u128 0x0)
  in
  let (a_16) =
    foldi (usize 0) (seq_num_chunks (m_10) (blocksize)) (fun i_17 (a_16) ->
      let (len_18, block_19) = seq_get_chunk (m_10) (blocksize) (i_17) in
      let block_uint_20 = le_bytes_to_num (block_19) in
      let n_21 = encode (block_uint_20) (len_18) in
      let a_16 = (a_16) +% (n_21) in
      let a_16 = (r_13) *% (a_16) in
      (a_16))
    (a_16)
  in
  let a_22 = (a_16) +% (s_15) in
  num_to_16_le_bytes (a_22)

