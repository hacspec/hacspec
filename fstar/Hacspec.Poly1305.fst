module Hacspec.Poly1305

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open Hacspec.Lib
open FStar.Mul



type sub_block = byte_seq

type poly_key = lseq (uint8) (usize 32)

let blocksize : uint_size =
  usize 16

type poly_block = lseq (uint8) (usize 16)

type tag = lseq (uint8) (usize 16)

type field_canvas = lseq (pub_uint8) (17)

type field_element = nat_mod 0x03fffffffffffffffffffffffffffffffb
type poly_state = (field_element & field_element & poly_key)

let poly1305_encode_r (b_0 : poly_block) : field_element =
  let n_1 = uint128_from_le_bytes (array_from_seq (16) (b_0)) in
  let n_1 = (n_1) &. (secret (pub_u128 0xffffffc0ffffffc0ffffffc0fffffff)) in
  nat_from_secret_literal (0x03fffffffffffffffffffffffffffffffb) (n_1)

let poly1305_encode_block
  (len_2 : uint_size{len_2 <= 16})
  (b_3 : sub_block{seq_len b_3 <= 16})
  : field_element =
  let n_4 =
    uint128_from_le_bytes (
      array_from_slice (secret (pub_u8 0x8)) (16) (b_3) (usize 0) (
        seq_len (b_3)))
  in
  let f_5 =
    nat_from_secret_literal (0x03fffffffffffffffffffffffffffffffb) (n_4)
  in
  admit();
  (f_5) +% (
    nat_pow2 (0x03fffffffffffffffffffffffffffffffb) ((usize 8) * (len_2)))

let poly1305_init (k_6 : poly_key) : poly_state =
  let r_7 =
    poly1305_encode_r (
      array_from_slice (secret (pub_u8 0x8)) (16) (k_6) (usize 0) (usize 16))
  in
  (nat_zero (0x03fffffffffffffffffffffffffffffffb), r_7, k_6)

let poly1305_update1
  (len_8 : uint_size{len_8 <= 16})
  (b_9 : sub_block{seq_len b_9 <= 16})
  (st_10 : poly_state)
  : poly_state =
  let (acc_11, r_12, k_13) = st_10 in
  (((poly1305_encode_block (len_8) (b_9)) +% (acc_11)) *% (r_12), r_12, k_13)

let poly1305_finish (st_14 : poly_state) : tag =
  let (acc_15, _, k_16) = st_14 in
  let n_17 =
    uint128_from_le_bytes (
      array_from_slice (secret (pub_u8 0x8)) (16) (k_16) (usize 16) (usize 16))
  in
  let aby_18 =
    nat_to_byte_seq_le (0x03fffffffffffffffffffffffffffffffb) 16 (acc_15)
  in
  let a_19 =
    uint128_from_le_bytes (
      array_from_slice (secret (pub_u8 0x8)) (16) (aby_18) (usize 0) (usize 16))
  in
  array_from_seq (16) (uint128_to_le_bytes ((a_19) +. (n_17)))

let poly1305_update (m_20 : byte_seq) (st_21 : poly_state) : poly_state =
  let st_22 = st_21 in
  let (st_22) =
    foldi (usize 0) (seq_num_chunks (m_20) (blocksize)) (fun i_23 (st_22) ->
      let (len_24, block_25) = seq_get_chunk (m_20) (blocksize) (i_23) in
      let st_22 = poly1305_update1 (len_24) (block_25) (st_22) in
      (st_22))
    (st_22)
  in
  st_22

let poly1305 (m_26 : byte_seq) (key_27 : poly_key) : tag =
  let st_28 = poly1305_init (key_27) in
  let st_28 = poly1305_update (m_26) (st_28) in
  poly1305_finish (st_28)

