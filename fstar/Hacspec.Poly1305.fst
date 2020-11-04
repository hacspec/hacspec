module Hacspec.Poly1305

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open Hacspec.Lib
open FStar.Mul



type key_poly = lseq (uint8) (usize 32)

let blocksize : uint_size =
  usize 16

type block = lseq (uint8) (usize 16)

type tag = lseq (pub_uint8) (usize 16)

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

let poly_finish (a_8 : field_element) (s_9 : field_element) : tag =
  let a_10 =
    seq_slice (
      nat_to_public_byte_seq_be (0x03fffffffffffffffffffffffffffffffb) (17) (
        a_8)) (usize 1) (blocksize)
  in
  let a_11 = u128_from_be_bytes (array_from_seq (16) (a_10)) in
  let s_12 =
    seq_slice (
      nat_to_public_byte_seq_be (0x03fffffffffffffffffffffffffffffffb) (17) (
        s_9)) (usize 1) (blocksize)
  in
  let s_13 = u128_from_be_bytes (array_from_seq (16) (s_12)) in
  let a_14 = pub_uint128_wrapping_add (a_11) (s_13) in
  array_from_seq (16) (u128_to_le_bytes (a_14))

let poly (m_15 : byte_seq) (key_16 : key_poly) : tag =
  let r_17 = le_bytes_to_num (array_slice (key_16) (usize 0) (blocksize)) in
  let r_18 = clamp (r_17) in
  let s_19 = le_bytes_to_num (array_slice (key_16) (blocksize) (blocksize)) in
  let s_20 =
    nat_from_secret_literal (0x03fffffffffffffffffffffffffffffffb) (s_19)
  in
  let a_21 =
    nat_from_literal (0x03fffffffffffffffffffffffffffffffb) (pub_u128 0x0)
  in
  let (a_21) =
    foldi (usize 0) (seq_num_chunks (m_15) (blocksize)) (fun i_22 (a_21) ->
      let (len_23, block_24) = seq_get_chunk (m_15) (blocksize) (i_22) in
      let block_uint_25 = le_bytes_to_num (block_24) in
      let n_26 = encode (block_uint_25) (len_23) in
      let a_21 = (a_21) +% (n_26) in
      let a_21 = (r_18) *% (a_21) in
      (a_21))
    (a_21)
  in
  poly_finish (a_21) (s_20)

