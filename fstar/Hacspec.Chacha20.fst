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

let chacha20_core (ctr_25 : uint32) (st0_26 : state) : state =
  let state_27 = st0_26 in
  let state_27 =
    array_upd state_27 (usize 12) (
      (array_index (state_27) (usize 12)) +. (ctr_25))
  in
  let k_28 = chacha20_rounds (state_27) in
  (k_28) `array_add (+.)` (state_27)

let chacha20_constants_init () : constants =
  let constants_29 = array_new_ (secret (pub_u32 0x8)) (4) in
  let constants_29 =
    array_upd constants_29 (usize 0) (secret (pub_u32 0x61707865))
  in
  let constants_29 =
    array_upd constants_29 (usize 1) (secret (pub_u32 0x3320646e))
  in
  let constants_29 =
    array_upd constants_29 (usize 2) (secret (pub_u32 0x79622d32))
  in
  let constants_29 =
    array_upd constants_29 (usize 3) (secret (pub_u32 0x6b206574))
  in
  constants_29

let chacha20_init
  (key_30 : cha_cha_key)
  (iv_31 : cha_cha_iv)
  (ctr_32 : uint32)
  : state =
  let st_33 = array_new_ (secret (pub_u32 0x8)) (16) in
  let st_33 = array_update (st_33) (usize 0) (chacha20_constants_init ()) in
  let st_33 = array_update (st_33) (usize 4) (array_to_le_uint32s (key_30)) in
  let st_33 = array_upd st_33 (usize 12) (ctr_32) in
  let st_33 = array_update (st_33) (usize 13) (array_to_le_uint32s (iv_31)) in
  st_33

let chacha20_key_block (state_34 : state) : block =
  let state_35 = chacha20_core (secret (pub_u32 0x0)) (state_34) in
  array_from_seq (64) (array_to_le_bytes (state_35))

let chacha20_key_block0 (key_36 : cha_cha_key) (iv_37 : cha_cha_iv) : block =
  let state_38 = chacha20_init (key_36) (iv_37) (secret (pub_u32 0x0)) in
  chacha20_key_block (state_38)

let chacha20_encrypt_block
  (st0_39 : state)
  (ctr_40 : uint32)
  (plain_41 : block)
  : block =
  let st_42 = chacha20_core (ctr_40) (st0_39) in
  let pl_43 = array_from_seq (16) (array_to_le_uint32s (plain_41)) in
  let st_44 = (pl_43) `array_xor (^.)` (st_42) in
  array_from_seq (64) (array_to_le_bytes (st_44))

let chacha20_encrypt_last
  (st0_45 : state)
  (ctr_46 : uint32)
  (plain_47 : byte_seq)
  : byte_seq =
  let b_48 = array_new_ (secret (pub_u8 0x8)) (64) in
  let b_48 = array_update (b_48) (usize 0) (plain_47) in
  let b_48 = chacha20_encrypt_block (st0_45) (ctr_46) (b_48) in
  array_slice (b_48) (usize 0) (seq_len (plain_47))

let chacha20_update (st0_49 : state) (m_50 : byte_seq) : byte_seq =
  let blocks_out_51 = seq_new_ (secret (pub_u8 0x8)) (seq_len (m_50)) in
  let (blocks_out_51) =
    foldi (usize 0) (seq_num_chunks (m_50) (usize 64)) (fun i_52 (blocks_out_51
      ) ->
      let (block_len_53, msg_block_54) =
        seq_get_chunk (m_50) (usize 64) (i_52)
      in
      let (blocks_out_51) =
        if (block_len_53) = (usize 64) then begin
          let b_55 =
            chacha20_encrypt_block (st0_49) (secret (pub_u32 (i_52))) (
              array_from_seq (64) (msg_block_54))
          in
          let blocks_out_51 =
            seq_set_chunk (blocks_out_51) (usize 64) (i_52) (b_55)
          in
          (blocks_out_51)
        end else begin
          let b_56 =
            chacha20_encrypt_last (st0_49) (secret (pub_u32 (i_52))) (
              msg_block_54)
          in
          let blocks_out_51 =
            seq_set_chunk (blocks_out_51) (usize 64) (i_52) (b_56)
          in
          (blocks_out_51)
        end
      in
      (blocks_out_51))
    (blocks_out_51)
  in
  blocks_out_51

let chacha20
  (key_57 : cha_cha_key)
  (iv_58 : cha_cha_iv)
  (ctr_59 : pub_uint32)
  (m_60 : byte_seq)
  : byte_seq =
  let state_61 = chacha20_init (key_57) (iv_58) (secret (ctr_59)) in
  chacha20_update (state_61) (m_60)

