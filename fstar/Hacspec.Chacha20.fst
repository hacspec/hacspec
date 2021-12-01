module Hacspec.Chacha20

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

type state_t = lseq (uint32) (usize 16)

let state_idx_t = nat_mod (usize 16)

type constants_t = lseq (uint32) (usize 4)

let constants_idx_t = nat_mod (usize 4)

type block_t = lseq (uint8) (usize 64)

type cha_cha_iv_t = lseq (uint8) (usize 12)

type cha_cha_key_t = lseq (uint8) (usize 32)

let chacha20_line (a_0 b_1 d_2: state_idx_t) (s_3: uint_size) (m_4: state_t) : state_t =
  let state_5 = m_4 in
  let state_5 =
    array_upd state_5 (a_0) ((array_index (state_5) (a_0)) +. (array_index (state_5) (b_1)))
  in
  let state_5 =
    array_upd state_5 (d_2) ((array_index (state_5) (d_2)) ^. (array_index (state_5) (a_0)))
  in
  let state_5 = array_upd state_5 (d_2) (uint32_rotate_left (array_index (state_5) (d_2)) (s_3)) in
  state_5

let chacha20_quarter_round (a_6 b_7 c_8 d_9: state_idx_t) (state_10: state_t) : state_t =
  let state_11 = chacha20_line (a_6) (b_7) (d_9) (usize 16) (state_10) in
  let state_12 = chacha20_line (c_8) (d_9) (b_7) (usize 12) (state_11) in
  let state_13 = chacha20_line (a_6) (b_7) (d_9) (usize 8) (state_12) in
  chacha20_line (c_8) (d_9) (b_7) (usize 7) (state_13)

let chacha20_double_round (state_14: state_t) : state_t =
  let state_15 = chacha20_quarter_round (usize 0) (usize 4) (usize 8) (usize 12) (state_14) in
  let state_16 = chacha20_quarter_round (usize 1) (usize 5) (usize 9) (usize 13) (state_15) in
  let state_17 = chacha20_quarter_round (usize 2) (usize 6) (usize 10) (usize 14) (state_16) in
  let state_18 = chacha20_quarter_round (usize 3) (usize 7) (usize 11) (usize 15) (state_17) in
  let state_19 = chacha20_quarter_round (usize 0) (usize 5) (usize 10) (usize 15) (state_18) in
  let state_20 = chacha20_quarter_round (usize 1) (usize 6) (usize 11) (usize 12) (state_19) in
  let state_21 = chacha20_quarter_round (usize 2) (usize 7) (usize 8) (usize 13) (state_20) in
  chacha20_quarter_round (usize 3) (usize 4) (usize 9) (usize 14) (state_21)

let chacha20_rounds (state_22: state_t) : state_t =
  let st_23 = state_22 in
  let st_23 =
    foldi (usize 0)
      (usize 10)
      (fun i_24 st_23 ->
          let st_23 = chacha20_double_round (st_23) in
          (st_23))
      (st_23)
  in
  st_23

let chacha20_core (ctr_25: uint32) (st0_26: state_t) : state_t =
  let state_27 = st0_26 in
  let state_27 = array_upd state_27 (usize 12) ((array_index (state_27) (usize 12)) +. (ctr_25)) in
  let k_28 = chacha20_rounds (state_27) in
  array_add ( +. ) (k_28) (state_27)

let chacha20_constants_init () : constants_t =
  let constants_29 = array_new_ (secret (pub_u32 0x0)) (4) in
  let constants_29 = array_upd constants_29 (usize 0) (secret (pub_u32 0x61707865)) in
  let constants_29 = array_upd constants_29 (usize 1) (secret (pub_u32 0x3320646e)) in
  let constants_29 = array_upd constants_29 (usize 2) (secret (pub_u32 0x79622d32)) in
  let constants_29 = array_upd constants_29 (usize 3) (secret (pub_u32 0x6b206574)) in
  constants_29

let chacha20_init (key_30: cha_cha_key_t) (iv_31: cha_cha_iv_t) (ctr_32: uint32) : state_t =
  let st_33 = array_new_ (secret (pub_u32 0x0)) (16) in
  let st_33 = array_update (st_33) (usize 0) (chacha20_constants_init ()) in
  let st_33 = array_update (st_33) (usize 4) (array_to_le_uint32s (key_30)) in
  let st_33 = array_upd st_33 (usize 12) (ctr_32) in
  let st_33 = array_update (st_33) (usize 13) (array_to_le_uint32s (iv_31)) in
  st_33

let chacha20_key_block (state_34: state_t) : block_t =
  let state_35 = chacha20_core (secret (pub_u32 0x0)) (state_34) in
  array_from_seq (64) (array_to_le_bytes (state_35))

let chacha20_key_block0 (key_36: cha_cha_key_t) (iv_37: cha_cha_iv_t) : block_t =
  let state_38 = chacha20_init (key_36) (iv_37) (secret (pub_u32 0x0)) in
  chacha20_key_block (state_38)

let chacha20_encrypt_block (st0_39: state_t) (ctr_40: uint32) (plain_41: block_t) : block_t =
  let st_42 = chacha20_core (ctr_40) (st0_39) in
  let pl_43 = array_from_seq (16) (array_to_le_uint32s (plain_41)) in
  let st_44 = array_xor ( ^. ) (pl_43) (st_42) in
  array_from_seq (64) (array_to_le_bytes (st_44))

let chacha20_encrypt_last (st0_45: state_t) (ctr_46: uint32) (plain_47: byte_seq) : byte_seq =
  let b_48 = array_new_ (secret (pub_u8 0x0)) (64) in
  let b_48 = array_update (b_48) (usize 0) (plain_47) in
  let b_48 = chacha20_encrypt_block (st0_45) (ctr_46) (b_48) in
  array_slice (b_48) (usize 0) (seq_len (plain_47))

let chacha20_update (st0_49: state_t) (m_50: byte_seq) : byte_seq =
  let blocks_out_51 = seq_new_ (secret (pub_u8 0x0)) (seq_len (m_50)) in
  let n_blocks_52 = seq_num_exact_chunks (m_50) (usize 64) in
  let blocks_out_51 =
    foldi (usize 0)
      (n_blocks_52)
      (fun i_53 blocks_out_51 ->
          let msg_block_54 = seq_get_exact_chunk (m_50) (usize 64) (i_53) in
          let b_55 =
            chacha20_encrypt_block (st0_49)
              (secret (pub_u32 (i_53)))
              (array_from_seq (64) (msg_block_54))
          in
          let blocks_out_51 = seq_set_exact_chunk (blocks_out_51) (usize 64) (i_53) (b_55) in
          (blocks_out_51))
      (blocks_out_51)
  in
  let last_block_56 = seq_get_remainder_chunk (m_50) (usize 64) in
  let blocks_out_51 =
    if (seq_len (last_block_56)) <> (usize 0)
    then
      let b_57 = chacha20_encrypt_last (st0_49) (secret (pub_u32 (n_blocks_52))) (last_block_56) in
      let blocks_out_51 = seq_set_chunk (blocks_out_51) (usize 64) (n_blocks_52) (b_57) in
      (blocks_out_51)
    else (blocks_out_51)
  in
  blocks_out_51

let chacha20 (key_58: cha_cha_key_t) (iv_59: cha_cha_iv_t) (ctr_60: pub_uint32) (m_61: byte_seq)
    : byte_seq =
  let state_62 = chacha20_init (key_58) (iv_59) (secret (ctr_60)) in
  chacha20_update (state_62) (m_61)

