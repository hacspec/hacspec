module Hacspec.Chacha20

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
  (s_7 : uint_size{
  (**) s_7 > 0 /\ s_7 < 32
  })
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

let chacha_block_init (key_26 : key) (ctr_27 : uint32) (iv_28 : iv) : state =
  array_from_list (
    let l =
      [
        secret (pub_u32 0x61707865);
        secret (pub_u32 0x3320646e);
        secret (pub_u32 0x79622d32);
        secret (pub_u32 0x6b206574);
        uint32_from_le_bytes (
          array_from_slice_range (key_26) ((usize 0, usize 4)));
        uint32_from_le_bytes (
          array_from_slice_range (key_26) ((usize 4, usize 8)));
        uint32_from_le_bytes (
          array_from_slice_range (key_26) ((usize 8, usize 12)));
        uint32_from_le_bytes (
          array_from_slice_range (key_26) ((usize 12, usize 16)));
        uint32_from_le_bytes (
          array_from_slice_range (key_26) ((usize 16, usize 20)));
        uint32_from_le_bytes (
          array_from_slice_range (key_26) ((usize 20, usize 24)));
        uint32_from_le_bytes (
          array_from_slice_range (key_26) ((usize 24, usize 28)));
        uint32_from_le_bytes (
          array_from_slice_range (key_26) ((usize 28, usize 32)));
        ctr_27;
        uint32_from_le_bytes (
          array_from_slice_range (iv_28) ((usize 0, usize 4)));
        uint32_from_le_bytes (
          array_from_slice_range (iv_28) ((usize 4, usize 8)));
        uint32_from_le_bytes (
          array_from_slice_range (iv_28) ((usize 8, usize 12)))
      ]
    in assert_norm (List.Tot.length l == 16); l)

let chacha_block_inner (key_29 : key) (ctr_30 : uint32) (iv_31 : iv) : state =
  let st_32 = chacha_block_init (key_29) (ctr_30) (iv_31) in
  let state_33 = st_32 in
  let (state_33) =
    foldi (usize 0) (usize 10) (fun i_34 (state_33) ->
      let state_33 = chacha_double_round (state_33) in
      (state_33))
    (state_33)
  in
  let (state_33) =
    foldi (usize 0) (usize 16) (fun i_35 (state_33) ->
      let state_33 =
        array_upd state_33 (i_35) (
          (array_index (state_33) (i_35)) +. (array_index (st_32) (i_35)))
      in
      (state_33))
    (state_33)
  in
  state_33

let chacha_block (key_36 : key) (ctr_37 : uint32) (iv_38 : iv) : state_bytes =
  let state_39 = chacha_block_inner (key_36) (ctr_37) (iv_38) in
  state_to_bytes (state_39)

let chacha (key_40 : key) (iv_41 : iv) (m_42 : byte_seq) : byte_seq =
  let ctr_43 = secret (pub_u32 0x1) in
  let blocks_out_44 = seq_new_ (secret (pub_u8 0x8)) (seq_len (m_42)) in
  let (blocks_out_44, ctr_43) =
    foldi (usize 0) (seq_num_chunks (m_42) (usize 64)) (fun i_45 (
        blocks_out_44,
        ctr_43
      ) ->
      let (block_len_46, msg_block_47) =
        seq_get_chunk (m_42) (usize 64) (i_45)
      in
      let key_block_48 = chacha_block (key_40) (ctr_43) (iv_41) in
      let msg_block_padded_49 = array_new_ (secret (pub_u8 0x8)) (64) in
      let msg_block_padded_50 =
        array_update_start (msg_block_padded_49) (msg_block_47)
      in
      let blocks_out_44 =
        seq_set_chunk (blocks_out_44) (usize 64) (i_45) (
          array_slice_range (
            (msg_block_padded_50) `array_xor (^.)` (key_block_48)) (
            (usize 0, block_len_46)))
      in
      let ctr_43 = (ctr_43) +. (secret (pub_u32 0x1)) in
      (blocks_out_44, ctr_43))
    (blocks_out_44, ctr_43)
  in
  blocks_out_44

