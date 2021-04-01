module Hacspec.Chacha20

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open Hacspec.Lib
open FStar.Mul





type state = lseq (uint32) (usize 16)

let state_idx =
  nat_mod (usize 16)

type constants = lseq (uint32) (usize 4)

let constants_idx =
  nat_mod (usize 4)

type block = lseq (uint8) (usize 64)

type cha_cha_iv = lseq (uint8) (usize 12)

type cha_cha_key = lseq (uint8) (usize 32)

let chacha20_line
  (a_0 : state_idx)
  (b_1 : state_idx)
  (d_2 : state_idx)
  (s_3 : uint_size)
  (m_4 : state)
  : state =
  let state_5 = m_4 in
  let state_5 =
    array_upd state_5 (a_0) (
      (array_index (state_5) (a_0)) +. (array_index (state_5) (b_1)))
  in
  let state_5 =
    array_upd state_5 (d_2) (
      (array_index (state_5) (d_2)) ^. (array_index (state_5) (a_0)))
  in
  let state_5 =
    array_upd state_5 (d_2) (
      uint32_rotate_left (array_index (state_5) (d_2)) (s_3))
  in
  state_5

let chacha20_quarter_round
  (a_6 : state_idx)
  (b_7 : state_idx)
  (c_8 : state_idx)
  (d_9 : state_idx)
  (state_10 : state)
  : state =
  let state_11 = chacha20_line (a_6) (b_7) (d_9) (usize 16) (state_10) in
  let state_12 = chacha20_line (c_8) (d_9) (b_7) (usize 12) (state_11) in
  let state_13 = chacha20_line (a_6) (b_7) (d_9) (usize 8) (state_12) in
  chacha20_line (c_8) (d_9) (b_7) (usize 7) (state_13)

let chacha20_double_round (state_14 : state) : state =
  let state_15 =
    chacha20_quarter_round (usize 0) (usize 4) (usize 8) (usize 12) (state_14)
  in
  let state_16 =
    chacha20_quarter_round (usize 1) (usize 5) (usize 9) (usize 13) (state_15)
  in
  let state_17 =
    chacha20_quarter_round (usize 2) (usize 6) (usize 10) (usize 14) (state_16)
  in
  let state_18 =
    chacha20_quarter_round (usize 3) (usize 7) (usize 11) (usize 15) (state_17)
  in
  let state_19 =
    chacha20_quarter_round (usize 0) (usize 5) (usize 10) (usize 15) (state_18)
  in
  let state_20 =
    chacha20_quarter_round (usize 1) (usize 6) (usize 11) (usize 12) (state_19)
  in
  let state_21 =
    chacha20_quarter_round (usize 2) (usize 7) (usize 8) (usize 13) (state_20)
  in
  chacha20_quarter_round (usize 3) (usize 4) (usize 9) (usize 14) (state_21)

let chacha20_rounds (state_22 : state) : state =
  let st_23 = state_22 in
  let (st_23) =
    foldi (usize 0) (usize 10) (fun i_24 (st_23) ->
      let st_23 = chacha20_double_round (st_23) in
      (st_23))
    (st_23)
  in
  st_23

let chacha20_sum_state (st0_25 : state) (st1_26 : state) : state =
  let st_27 = st0_25 in
  let (st_27) =
    foldi (usize 0) (usize 16) (fun i_28 (st_27) ->
      let st_27 =
        array_upd st_27 (i_28) (
          (array_index (st0_25) (i_28)) +. (array_index (st1_26) (i_28)))
      in
      (st_27))
    (st_27)
  in
  st_27

let chacha20_core (ctr_29 : uint32) (st0_30 : state) : state =
  let state_31 = st0_30 in
  let state_31 =
    array_upd state_31 (usize 12) (
      (array_index (state_31) (usize 12)) +. (ctr_29))
  in
  let k_32 = chacha20_rounds (state_31) in
  chacha20_sum_state (k_32) (state_31)

let chacha20_constants_init () : constants =
  let constants_33 = array_new_ (secret (pub_u32 0x8)) (4) in
  let constants_33 =
    array_upd constants_33 (usize 0) (secret (pub_u32 0x61707865))
  in
  let constants_33 =
    array_upd constants_33 (usize 1) (secret (pub_u32 0x3320646e))
  in
  let constants_33 =
    array_upd constants_33 (usize 2) (secret (pub_u32 0x79622d32))
  in
  let constants_33 =
    array_upd constants_33 (usize 3) (secret (pub_u32 0x6b206574))
  in
  constants_33

let chacha20_init
  (key_34 : cha_cha_key)
  (iv_35 : cha_cha_iv)
  (ctr_36 : uint32)
  : state =
  let st_37 = array_new_ (secret (pub_u32 0x8)) (16) in
  let st_37 =
    array_update_slice (st_37) (usize 0) (chacha20_constants_init ()) (
      usize 0) (usize 4)
  in
  let st_37 =
    array_update_slice (st_37) (usize 4) (array_to_le_uint32s (key_34)) (
      usize 0) (usize 8)
  in
  let st_37 = array_upd st_37 (usize 12) (ctr_36) in
  let st_37 =
    array_update_slice (st_37) (usize 13) (array_to_le_uint32s (iv_35)) (
      usize 0) (usize 3)
  in
  st_37

let chacha20_key_block (state_38 : state) : block =
  let state_39 = chacha20_core (secret (pub_u32 0x0)) (state_38) in
  array_from_seq (64) (array_to_le_bytes (state_39))

let chacha20_key_block0 (key_40 : cha_cha_key) (iv_41 : cha_cha_iv) : block =
  let state_42 = chacha20_init (key_40) (iv_41) (secret (pub_u32 0x0)) in
  chacha20_key_block (state_42)

let chacha20_encrypt_block
  (st0_43 : state)
  (ctr_44 : uint32)
  (plain_45 : block)
  : block =
  let st_46 = chacha20_core (ctr_44) (st0_43) in
  let pl_47 = array_from_seq (16) (array_to_le_uint32s (plain_45)) in
  let st_48 = (st_46) `array_xor (^.)` (pl_47) in
  array_from_seq (64) (array_to_le_bytes (st_48))

let chacha20_encrypt_last
  (st0_49 : state)
  (ctr_50 : uint32)
  (plain_51 : byte_seq)
  : byte_seq =
  let b_52 = array_new_ (secret (pub_u8 0x8)) (64) in
  let b_52 =
    array_update_slice (b_52) (usize 0) (plain_51) (usize 0) (
      seq_len (plain_51))
  in
  let b_52 = chacha20_encrypt_block (st0_49) (ctr_50) (b_52) in
  array_slice (b_52) (usize 0) (seq_len (plain_51))

let chacha20_update (st0_53 : state) (m_54 : byte_seq) : byte_seq =
  let blocks_out_55 = seq_new_ (secret (pub_u8 0x8)) (seq_len (m_54)) in
  let (blocks_out_55) =
    foldi (usize 0) (seq_num_chunks (m_54) (usize 64)) (fun i_56 (blocks_out_55
      ) ->
      let (block_len_57, msg_block_58) =
        seq_get_chunk (m_54) (usize 64) (i_56)
      in
      let (blocks_out_55) =
        if (block_len_57) = (usize 64) then begin
          let b_59 =
            chacha20_encrypt_block (st0_53) (secret (pub_u32 (i_56))) (
              array_from_seq (64) (msg_block_58))
          in
          let blocks_out_55 =
            seq_set_chunk (blocks_out_55) (usize 64) (i_56) (b_59)
          in
          (blocks_out_55)
        end else begin
          let b_60 =
            chacha20_encrypt_last (st0_53) (secret (pub_u32 (i_56))) (
              msg_block_58)
          in
          let blocks_out_55 =
            seq_set_chunk (blocks_out_55) (usize 64) (i_56) (b_60)
          in
          (blocks_out_55)
        end
      in
      (blocks_out_55))
    (blocks_out_55)
  in
  blocks_out_55

let chacha20
  (key_61 : cha_cha_key)
  (iv_62 : cha_cha_iv)
  (ctr_63 : pub_uint32)
  (m_64 : byte_seq)
  : byte_seq =
  let state_65 = chacha20_init (key_61) (iv_62) (secret (ctr_63)) in
  chacha20_update (state_65) (m_64)

