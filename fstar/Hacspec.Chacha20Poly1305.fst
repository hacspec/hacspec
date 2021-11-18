module Hacspec.Chacha20Poly1305

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

open Hacspec.Chacha20

open Hacspec.Poly1305
noeq
type error_t = | InvalidTag_error_t : error_t

type cha_cha_poly_key_t = cha_cha_key_t

type cha_cha_poly_iv_t = cha_cha_iv_t

type byte_seq_result_t = (result byte_seq error_t)

let init (key_0: cha_cha_poly_key_t) (iv_1: cha_cha_poly_iv_t) : poly_state_t =
  let key_block0_2 = chacha20_key_block0 (key_0) (iv_1) in
  let poly_key_3 =
    array_from_slice (secret (pub_u8 0x0)) (32) (key_block0_2) (usize 0) (usize 32)
  in
  poly1305_init (poly_key_3)

let poly1305_update_padded (m_4: byte_seq) (st_5: poly_state_t) : poly_state_t =
  let st_6 = poly1305_update_blocks (m_4) (st_5) in
  let last_7 = seq_get_remainder_chunk (m_4) (usize 16) in
  poly1305_update_last (usize 16) (last_7) (st_6)

let finish (aad_len_8 cipher_len_9: uint_size) (st_10: poly_state_t) : poly1305_tag_t =
  let last_block_11 = array_new_ (secret (pub_u8 0x0)) (16) in
  let last_block_11 =
    array_update (last_block_11) (usize 0) (uint64_to_le_bytes (secret (pub_u64 (aad_len_8))))
  in
  let last_block_11 =
    array_update (last_block_11) (usize 8) (uint64_to_le_bytes (secret (pub_u64 (cipher_len_9))))
  in
  let st_12 = poly1305_update_block (last_block_11) (st_10) in
  poly1305_finish (st_12)

let chacha20_poly1305_encrypt
      (key_13: cha_cha_poly_key_t)
      (iv_14: cha_cha_poly_iv_t)
      (aad_15 msg_16: byte_seq)
    : (byte_seq & poly1305_tag_t) =
  let cipher_text_17 = chacha20 (key_13) (iv_14) (pub_u32 0x1) (msg_16) in
  let poly_st_18 = init (key_13) (iv_14) in
  let poly_st_18 = poly1305_update_padded (aad_15) (poly_st_18) in
  let poly_st_18 = poly1305_update_padded (cipher_text_17) (poly_st_18) in
  let tag_19 = finish (seq_len (aad_15)) (seq_len (cipher_text_17)) (poly_st_18) in
  (cipher_text_17, tag_19)

let chacha20_poly1305_decrypt
      (key_20: cha_cha_poly_key_t)
      (iv_21: cha_cha_poly_iv_t)
      (aad_22 cipher_text_23: byte_seq)
      (tag_24: poly1305_tag_t)
    : byte_seq_result_t =
  let poly_st_25 = init (key_20) (iv_21) in
  let poly_st_25 = poly1305_update_padded (aad_22) (poly_st_25) in
  let poly_st_25 = poly1305_update_padded (cipher_text_23) (poly_st_25) in
  let my_tag_26 = finish (seq_len (aad_22)) (seq_len (cipher_text_23)) (poly_st_25) in
  if (array_declassify_eq (my_tag_26) (tag_24))
  then (Ok (chacha20 (key_20) (iv_21) (pub_u32 0x1) (cipher_text_23)))
  else (Err (InvalidTag_error_t))

