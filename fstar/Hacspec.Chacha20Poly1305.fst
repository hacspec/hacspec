module Hacspec.Chacha20Poly1305

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open Hacspec.Lib
open FStar.Mul

open Hacspec.Chacha20
open Hacspec.Poly1305

let key_gen (key_0 : key_poly) (iv_1 : iv) : key_poly =
  let block_2 =
    chacha_block (array_from_seq (32) (key_0)) (secret (pub_u32 0x0)) (iv_1)
  in
  array_from_slice_range (block_2) ((usize 0, usize 32))

let poly_mac (m_3 : byte_seq) (key_4 : key_poly) (iv_5 : iv) : tag =
  let mac_key_6 = key_gen (key_4) (iv_5) in
  poly (m_3) (mac_key_6)

let pad_aad_msg (aad_7 : byte_seq) (msg_8 : byte_seq) : byte_seq =
  let laad_9 = seq_len (aad_7) in
  let lmsg_10 = seq_len (msg_8) in
  let pad_aad_11 =
    (usize 16) * (((laad_9) `usize_shift_right` (pub_u32 0x4)) + (usize 1))
  in
  let pad_msg_12 =
    (usize 16) * (((lmsg_10) `usize_shift_right` (pub_u32 0x4)) + (usize 1))
  in
  (**) assume(range pad_aad_11 U32);
  let (pad_aad_11, pad_msg_12) =
    if ((laad_9) % (usize 16)) = (usize 0) then begin
      let pad_aad_11 = laad_9 in
      let pad_msg_12 = lmsg_10 in
      (pad_aad_11, pad_msg_12)
    end else begin (pad_aad_11, pad_msg_12)
    end
  in
  (**) assume(range (((pad_aad_11) + (pad_msg_12)) + (usize 16)) U32);
  let padded_msg_13 =
    seq_new_ (secret (pub_u8 0x8)) (((pad_aad_11) + (pad_msg_12)) + (usize 16))
  in
  (**) assume(seq_len aad_7 <= seq_len padded_msg_13);
  let padded_msg_13 = seq_update (padded_msg_13) (usize 0) (aad_7) in
  (**) assume(pad_aad_11 + seq_len msg_8 <= seq_len padded_msg_13);
  let padded_msg_13 = seq_update (padded_msg_13) (pad_aad_11) (msg_8) in
  let padded_msg_13 =
    seq_update (padded_msg_13) ((pad_aad_11) + (pad_msg_12)) (
      uint64_to_le_bytes (secret (cast U64 PUB (size laad_9))))
  in
  let padded_msg_13 =
    seq_update (padded_msg_13) (((pad_aad_11) + (pad_msg_12)) + (usize 8)) (
      uint64_to_le_bytes (secret (cast U64 PUB (size lmsg_10))))
  in
  padded_msg_13

let encrypt
  (key_14 : key)
  (iv_15 : iv)
  (aad_16 : byte_seq)
  (msg_17 : byte_seq)
  : (byte_seq & tag) =
  let key_block_18 = chacha_block (key_14) (secret (pub_u32 0x0)) (iv_15) in
  let mac_key_19 =
    array_from_slice_range (key_block_18) ((usize 0, usize 32))
  in
  let cipher_text_20 = chacha (key_14) (iv_15) (msg_17) in
  let padded_msg_21 = pad_aad_msg (aad_16) (cipher_text_20) in
  let tag_22 = poly (padded_msg_21) (array_from_seq (32) (mac_key_19)) in
  (cipher_text_20, tag_22)

let decrypt
  (key_23 : key)
  (iv_24 : iv)
  (aad_25 : byte_seq)
  (cipher_text_26 : byte_seq)
  (tag_27 : tag)
  : (byte_seq & bool) =
  let key_block_28 = chacha_block (key_23) (secret (pub_u32 0x0)) (iv_24) in
  let mac_key_29 =
    array_from_slice_range (key_block_28) ((usize 0, usize 32))
  in
  let padded_msg_30 = pad_aad_msg (aad_25) (cipher_text_26) in
  let my_tag_31 = poly (padded_msg_30) (array_from_seq (32) (mac_key_29)) in
  let plain_text_32 = chacha (key_23) (iv_24) (cipher_text_26) in
  (plain_text_32, (my_tag_31) = (tag_27))
