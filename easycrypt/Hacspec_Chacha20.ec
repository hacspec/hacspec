require import List Int IntDiv CoreMap AllCore.
require import Array3 Array4 Array8 Array12 Array16 Array17 Array32 Array64.
require import WArray64.

from Jasmin require import JModel JMemory JArray.
require import Hacspec.


type state = uint32 Array16.t.

type state_idx = uint_size.

type constants = uint32 Array4.t.

type constants_idx = uint_size.

type block = uint8 Array64.t.

type cha_cha_iv = uint8 Array12.t.

type cha_cha_key = uint8 Array32.t.

op chacha20_line
  (a_0 : state_idx)
  (b_1 : state_idx)
  (d_2 : state_idx)
  (s_3 : uint_size)
  (m_4 : state)
  : state =
  let state_5 = m_4 in
  let state_5 = state_5.[(a_0) <- ((state_5.[a_0]) + (state_5.[b_1]))] in
  let state_5 = state_5.[(d_2) <- ((state_5.[d_2]) +^ (state_5.[a_0]))] in
  let state_5 = state_5.[(d_2) <- (uint32_rotate_left (state_5.[d_2]) (s_3))] in
  state_5.

op chacha20_quarter_round
  (a_6 : state_idx)
  (b_7 : state_idx)
  (c_8 : state_idx)
  (d_9 : state_idx)
  (state_10 : state)
  : state =
  let state_11 = chacha20_line (a_6) (b_7) (d_9) (16) (state_10) in
  let state_12 = chacha20_line (c_8) (d_9) (b_7) (12) (state_11) in
  let state_13 = chacha20_line (a_6) (b_7) (d_9) (8) (state_12) in
  chacha20_line (c_8) (d_9) (b_7) (7) (state_13).

op chacha20_double_round (state_14 : state) : state =
  let state_15 = chacha20_quarter_round (0) (4) (8) (12) (state_14) in
  let state_16 = chacha20_quarter_round (1) (5) (9) (13) (state_15) in
  let state_17 = chacha20_quarter_round (2) (6) (10) (14) (state_16) in
  let state_18 = chacha20_quarter_round (3) (7) (11) (15) (state_17) in
  let state_19 = chacha20_quarter_round (0) (5) (10) (15) (state_18) in
  let state_20 = chacha20_quarter_round (1) (6) (11) (12) (state_19) in
  let state_21 = chacha20_quarter_round (2) (7) (8) (13) (state_20) in
  chacha20_quarter_round (3) (4) (9) (14) (state_21).

op chacha20_rounds (state_22 : state) : state =
  let st_23 = state_22 in
  let st_23 =
    foldi (0) (10) (fun i_24 st_23 =>
      let st_23 = chacha20_double_round (st_23) in
      st_23)
    st_23
  in
  st_23.

op chacha20_core (ctr_25 : uint32) (st0_26 : state) : state =
  let state_27 = st0_26 in
  let state_27 = state_27.[(12) <- ((state_27.[12]) + (ctr_25))] in
  let k_28 = chacha20_rounds (state_27) in
  array_16_add Unknown.(+) (k_28) (state_27).

op chacha20_constants_init (_: unit) : constants =
  let constants_29 = array_4_new_ (secret (pub_u32 8)) in
  let constants_29 = constants_29.[(0) <- (secret (pub_u32 1634760805))] in
  let constants_29 = constants_29.[(1) <- (secret (pub_u32 857760878))] in
  let constants_29 = constants_29.[(2) <- (secret (pub_u32 2036477234))] in
  let constants_29 = constants_29.[(3) <- (secret (pub_u32 1797285236))] in
  constants_29.

op chacha20_init
  (key_30 : cha_cha_key)
  (iv_31 : cha_cha_iv)
  (ctr_32 : uint32)
  : state =
  let st_33 = array_16_new_ (secret (pub_u32 8)) in
  let st_33 = array_16_update (st_33) (0) (chacha20_constants_init ()) in
  let st_33 = array_16_update (st_33) (4) (array_32_to_le_uint32s (key_30)) in
  let st_33 = st_33.[(12) <- (ctr_32)] in
  let st_33 = array_16_update (st_33) (13) (array_12_to_le_uint32s (iv_31)) in
  st_33.

op chacha20_key_block (state_34 : state) : block =
  let state_35 = chacha20_core (secret (pub_u32 0)) (state_34) in
  array_64_from_seq (array_16_to_le_bytes (state_35)).

op chacha20_key_block0 (key_36 : cha_cha_key) (iv_37 : cha_cha_iv) : block =
  let state_38 = chacha20_init (key_36) (iv_37) (secret (pub_u32 0)) in
  chacha20_key_block (state_38).

op chacha20_encrypt_block
  (st0_39 : state)
  (ctr_40 : uint32)
  (plain_41 : block)
  : block =
  let st_42 = chacha20_core (ctr_40) (st0_39) in
  let pl_43 = array_16_from_seq (array_64_to_le_uint32s (plain_41)) in
  let st_44 = array_16_xor Unknown.(+^) (st_42) (pl_43) in
  array_64_from_seq (array_16_to_le_bytes (st_44)).

op chacha20_encrypt_last
  (st0_45 : state)
  (ctr_46 : uint32)
  (plain_47 : byte_seq)
  : byte_seq =
  let b_48 = array_64_new_ (secret (pub_u8 8)) in
  let b_48 = array_64_update (b_48) (0) (plain_47) in
  let b_48 = chacha20_encrypt_block (st0_45) (ctr_46) (b_48) in
  array_64_slice (b_48) (0) (seq_len (plain_47)).

op chacha20_update (st0_49 : state) (m_50 : byte_seq) : byte_seq =
  let blocks_out_51 = seq_new_ (secret (pub_u8 8)) (seq_len (m_50)) in
  let blocks_out_51 =
    foldi (0) (seq_num_chunks (m_50) (64)) (fun i_52 blocks_out_51 =>
      let (block_len_53, msg_block_54) = seq_get_chunk (m_50) (64) (i_52) in
      let blocks_out_51 =
        if (block_len_53) = (64) then begin
          let b_55 =
            chacha20_encrypt_block (st0_49) (secret (pub_u32 (i_52))) (
              array_64_from_seq (msg_block_54))
          in
          let blocks_out_51 =
            seq_set_chunk (blocks_out_51) (64) (i_52) (b_55)
          in
          blocks_out_51
        end else begin
          let b_56 =
            chacha20_encrypt_last (st0_49) (secret (pub_u32 (i_52))) (
              msg_block_54)
          in
          let blocks_out_51 =
            seq_set_chunk (blocks_out_51) (64) (i_52) (b_56)
          in
          blocks_out_51
        end
      in
      blocks_out_51)
    blocks_out_51
  in
  blocks_out_51.

op chacha20
  (key_57 : cha_cha_key)
  (iv_58 : cha_cha_iv)
  (ctr_59 : pub_uint32)
  (m_60 : byte_seq)
  : byte_seq =
  let state_61 = chacha20_init (key_57) (iv_58) (secret (ctr_59)) in
  chacha20_update (state_61) (m_60).

