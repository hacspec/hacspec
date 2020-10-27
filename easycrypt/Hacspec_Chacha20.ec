module Hacspec_Chacha20

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open Hacspec.Lib
open FStar.Mul



type state = lseq (uint32) (usize 16)

let state_idx =
  nat_mod (usize 16)

type state_bytes = lseq (uint8) (usize 64)

type iv = lseq (uint8) (usize 12)

type key = lseq (uint8) (usize 32)

let state_to_bytes (x_0 : state) : state_bytes =
  let r_1 = array_new_ (secret (pub_u8 0x8)) (64) in
  let (r_1) =
    foldi (usize 0) (array_len (x_0)) (fun i_2 (r_1) ->
      let bytes_3 = uint32_to_be_bytes (array_index (x_0) (i_2)) in
      let r_1 =
        array_upd r_1 ((i_2) * (usize 4)) (array_index (bytes_3) (usize 3))
      in
      let r_1 =
        array_upd r_1 (((i_2) * (usize 4)) + (usize 1)) (
          array_index (bytes_3) (usize 2))
      in
      let r_1 =
        array_upd r_1 (((i_2) * (usize 4)) + (usize 2)) (
          array_index (bytes_3) (usize 1))
      in
      let r_1 =
        array_upd r_1 (((i_2) * (usize 4)) + (usize 3)) (
          array_index (bytes_3) (usize 0))
      in
      (r_1))
    (r_1)
  in
  r_1

let chacha_line
  (a_4 : state_idx)
  (b_5 : state_idx)
  (d_6 : state_idx)
  (s_7 : uint_size)
  (m_8 : state)
  : state =
  let state_9 = m_8 in
  let state_9 =
    array_upd state_9 (a_4) (
      (array_index (state_9) (a_4)) +. (array_index (state_9) (b_5)))
  in
  let state_9 =
    array_upd state_9 (d_6) (
      (array_index (state_9) (d_6)) ^. (array_index (state_9) (a_4)))
  in
  let state_9 =
    array_upd state_9 (d_6) (
      uint32_rotate_left (array_index (state_9) (d_6)) (s_7))
  in
  state_9

let chacha_quarter_round
  (a_10 : state_idx)
  (b_11 : state_idx)
  (c_12 : state_idx)
  (d_13 : state_idx)
  (state_14 : state)
  : state =
  let state_15 = chacha_line (a_10) (b_11) (d_13) (usize 16) (state_14) in
  let state_16 = chacha_line (c_12) (d_13) (b_11) (usize 12) (state_15) in
  let state_17 = chacha_line (a_10) (b_11) (d_13) (usize 8) (state_16) in
  chacha_line (c_12) (d_13) (b_11) (usize 7) (state_17)

let chacha_double_round (state_18 : state) : state =
  let state_19 =
    chacha_quarter_round (usize 0) (usize 4) (usize 8) (usize 12) (state_18)
  in
  let state_20 =
    chacha_quarter_round (usize 1) (usize 5) (usize 9) (usize 13) (state_19)
  in
  let state_21 =
    chacha_quarter_round (usize 2) (usize 6) (usize 10) (usize 14) (state_20)
  in
  let state_22 =
    chacha_quarter_round (usize 3) (usize 7) (usize 11) (usize 15) (state_21)
  in
  let state_23 =
    chacha_quarter_round (usize 0) (usize 5) (usize 10) (usize 15) (state_22)
  in
  let state_24 =
    chacha_quarter_round (usize 1) (usize 6) (usize 11) (usize 12) (state_23)
  in
  let state_25 =
    chacha_quarter_round (usize 2) (usize 7) (usize 8) (usize 13) (state_24)
  in
  chacha_quarter_round (usize 3) (usize 4) (usize 9) (usize 14) (state_25)

let chacha20_constants_init () : seq uint32 =
  let constants_26 = seq_new_ (secret (pub_u32 0x8)) (usize 4) in
  let constants_26 =
    array_upd constants_26 (usize 0) (secret (pub_u32 0x61707865))
  in
  let constants_26 =
    array_upd constants_26 (usize 1) (secret (pub_u32 0x3320646e))
  in
  let constants_26 =
    array_upd constants_26 (usize 2) (secret (pub_u32 0x79622d32))
  in
  let constants_26 =
    array_upd constants_26 (usize 3) (secret (pub_u32 0x6b206574))
  in
  constants_26

let chacha20_key_to_u32s (key_27 : key) : seq uint32 =
  let uints_28 = seq_new_ (secret (pub_u32 0x8)) (usize 8) in
  let uints_28 =
    array_upd uints_28 (usize 0) (
      uint32_from_le_bytes (
        array_from_slice_range (key_27) ((usize 0, usize 4))))
  in
  let uints_28 =
    array_upd uints_28 (usize 1) (
      uint32_from_le_bytes (
        array_from_slice_range (key_27) ((usize 4, usize 8))))
  in
  let uints_28 =
    array_upd uints_28 (usize 2) (
      uint32_from_le_bytes (
        array_from_slice_range (key_27) ((usize 8, usize 12))))
  in
  let uints_28 =
    array_upd uints_28 (usize 3) (
      uint32_from_le_bytes (
        array_from_slice_range (key_27) ((usize 12, usize 16))))
  in
  let uints_28 =
    array_upd uints_28 (usize 4) (
      uint32_from_le_bytes (
        array_from_slice_range (key_27) ((usize 16, usize 20))))
  in
  let uints_28 =
    array_upd uints_28 (usize 5) (
      uint32_from_le_bytes (
        array_from_slice_range (key_27) ((usize 20, usize 24))))
  in
  let uints_28 =
    array_upd uints_28 (usize 6) (
      uint32_from_le_bytes (
        array_from_slice_range (key_27) ((usize 24, usize 28))))
  in
  let uints_28 =
    array_upd uints_28 (usize 7) (
      uint32_from_le_bytes (
        array_from_slice_range (key_27) ((usize 28, usize 32))))
  in
  uints_28

let chacha20_iv_to_u32s (iv_29 : iv) : seq uint32 =
  let uints_30 = seq_new_ (secret (pub_u32 0x8)) (usize 3) in
  let uints_30 =
    array_upd uints_30 (usize 0) (
      uint32_from_le_bytes (
        array_from_slice_range (iv_29) ((usize 0, usize 4))))
  in
  let uints_30 =
    array_upd uints_30 (usize 1) (
      uint32_from_le_bytes (
        array_from_slice_range (iv_29) ((usize 4, usize 8))))
  in
  let uints_30 =
    array_upd uints_30 (usize 2) (
      uint32_from_le_bytes (
        array_from_slice_range (iv_29) ((usize 8, usize 12))))
  in
  uints_30

let chacha20_ctr_to_seq (ctr_31 : uint32) : seq uint32 =
  let uints_32 = seq_new_ (secret (pub_u32 0x8)) (usize 1) in
  let uints_32 = array_upd uints_32 (usize 0) (ctr_31) in
  uints_32

let chacha_block_init (key_33 : key) (ctr_34 : uint32) (iv_35 : iv) : state =
  array_from_seq (16) (
    seq_concat (
      seq_concat (
        seq_concat (chacha20_constants_init ()) (
          chacha20_key_to_u32s (key_33))) (chacha20_ctr_to_seq (ctr_34))) (
      chacha20_iv_to_u32s (iv_35)))

let chacha_block_inner (key_36 : key) (ctr_37 : uint32) (iv_38 : iv) : state =
  let st_39 = chacha_block_init (key_36) (ctr_37) (iv_38) in
  let state_40 = st_39 in
  let (state_40) =
    foldi (usize 0) (usize 10) (fun i_41 (state_40) ->
      let state_40 = chacha_double_round (state_40) in
      (state_40))
    (state_40)
  in
  let (state_40) =
    foldi (usize 0) (usize 16) (fun i_42 (state_40) ->
      let state_40 =
        array_upd state_40 (i_42) (
          (array_index (state_40) (i_42)) +. (array_index (st_39) (i_42)))
      in
      (state_40))
    (state_40)
  in
  state_40

let chacha_block (key_43 : key) (ctr_44 : uint32) (iv_45 : iv) : state_bytes =
  let state_46 = chacha_block_inner (key_43) (ctr_44) (iv_45) in
  state_to_bytes (state_46)

let chacha (key_47 : key) (iv_48 : iv) (m_49 : byte_seq) : byte_seq =
  let ctr_50 = secret (pub_u32 0x1) in
  let blocks_out_51 = seq_new_ (secret (pub_u8 0x8)) (seq_len (m_49)) in
  let (ctr_50, blocks_out_51) =
    foldi (usize 0) (seq_num_chunks (m_49) (usize 64)) (fun i_52 (
        ctr_50,
        blocks_out_51
      ) ->
      let (block_len_53, msg_block_54) =
        seq_get_chunk (m_49) (usize 64) (i_52)
      in
      let key_block_55 = chacha_block (key_47) (ctr_50) (iv_48) in
      let msg_block_padded_56 = array_new_ (secret (pub_u8 0x8)) (64) in
      let msg_block_padded_57 =
        array_update_start (msg_block_padded_56) (msg_block_54)
      in
      let blocks_out_51 =
        seq_set_chunk (blocks_out_51) (usize 64) (i_52) (
          array_slice_range (
            (msg_block_padded_57) `array_xor (^.)` (key_block_55)) (
            (usize 0, block_len_53)))
      in
      let ctr_50 = (ctr_50) +. (secret (pub_u32 0x1)) in
      (ctr_50, blocks_out_51))
    (ctr_50, blocks_out_51)
  in
  blocks_out_51

