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

op chacha20_sum_state (st0_25 : state) (st1_26 : state) : state =
  let st_27 = st0_25 in
  let st_27 =
    foldi (0) (16) (fun i_28 st_27 =>
      let st_27 = st_27.[(i_28) <- ((st0_25.[i_28]) + (st1_26.[i_28]))] in
      st_27)
    st_27
  in
  st_27.

op chacha20_core (ctr_29 : uint32) (st0_30 : state) : state =
  let state_31 = st0_30 in
  let state_31 = state_31.[(12) <- ((state_31.[12]) + (ctr_29))] in
  let k_32 = chacha20_rounds (state_31) in
  chacha20_sum_state (k_32) (state_31).

op chacha20_constants_init (_: unit) : constants =
  let constants_33 = array_4_new_ (secret (pub_u32 8)) in
  let constants_33 = constants_33.[(0) <- (secret (pub_u32 1634760805))] in
  let constants_33 = constants_33.[(1) <- (secret (pub_u32 857760878))] in
  let constants_33 = constants_33.[(2) <- (secret (pub_u32 2036477234))] in
  let constants_33 = constants_33.[(3) <- (secret (pub_u32 1797285236))] in
  constants_33.

op chacha20_init
  (key_34 : cha_cha_key)
  (iv_35 : cha_cha_iv)
  (ctr_36 : uint32)
  : state =
  let st_37 = array_16_new_ (secret (pub_u32 8)) in
  let st_37 =
    array_16_update_slice (st_37) (0) (chacha20_constants_init ()) (0) (4)
  in
  let st_37 =
    array_16_update_slice (st_37) (4) (array_32_to_le_uint32s (key_34)) (0) (8)
  in
  let st_37 = st_37.[(12) <- (ctr_36)] in
  let st_37 =
    array_16_update_slice (st_37) (13) (array_12_to_le_uint32s (iv_35)) (0) (3)
  in
  st_37.

op chacha20_key_block (state_38 : state) : block =
  let state_39 = chacha20_core (secret (pub_u32 0)) (state_38) in
  array_64_from_seq (array_16_to_le_bytes (state_39)).

op chacha20_key_block0 (key_40 : cha_cha_key) (iv_41 : cha_cha_iv) : block =
  let state_42 = chacha20_init (key_40) (iv_41) (secret (pub_u32 0)) in
  chacha20_key_block (state_42).

op chacha20_encrypt_block
  (st0_43 : state)
  (ctr_44 : uint32)
  (plain_45 : block)
  : block =
  let st_46 = chacha20_core (ctr_44) (st0_43) in
  let pl_47 = array_16_from_seq (array_64_to_le_uint32s (plain_45)) in
  let st_48 = array_16_xor Unknown.(+^) (st_46) (pl_47) in
  array_64_from_seq (array_16_to_le_bytes (st_48)).

op chacha20_encrypt_last
  (st0_49 : state)
  (ctr_50 : uint32)
  (plain_51 : byte_seq)
  : byte_seq =
  let b_52 = array_64_new_ (secret (pub_u8 8)) in
  let b_52 =
    array_64_update_slice (b_52) (0) (plain_51) (0) (seq_len (plain_51))
  in
  let b_52 = chacha20_encrypt_block (st0_49) (ctr_50) (b_52) in
  array_64_slice (b_52) (0) (seq_len (plain_51)).

op chacha20_update (st0_53 : state) (m_54 : byte_seq) : byte_seq =
  let blocks_out_55 = seq_new_ (secret (pub_u8 8)) (seq_len (m_54)) in
  let blocks_out_55 =
    foldi (0) (seq_num_chunks (m_54) (64)) (fun i_56 blocks_out_55 =>
      let (block_len_57, msg_block_58) = seq_get_chunk (m_54) (64) (i_56) in
      let blocks_out_55 =
        if (block_len_57) = (64) then begin
          let b_59 =
            chacha20_encrypt_block (st0_53) (secret (pub_u32 (i_56))) (
              array_64_from_seq (msg_block_58))
          in
          let blocks_out_55 =
            seq_set_chunk (blocks_out_55) (64) (i_56) (b_59)
          in
          blocks_out_55
        end else begin
          let b_60 =
            chacha20_encrypt_last (st0_53) (secret (pub_u32 (i_56))) (
              msg_block_58)
          in
          let blocks_out_55 =
            seq_set_chunk (blocks_out_55) (64) (i_56) (b_60)
          in
          blocks_out_55
        end
      in
      blocks_out_55)
    blocks_out_55
  in
  blocks_out_55.

op chacha20
  (key_61 : cha_cha_key)
  (iv_62 : cha_cha_iv)
  (ctr_63 : pub_uint32)
  (m_64 : byte_seq)
  : byte_seq =
  let state_65 = chacha20_init (key_61) (iv_62) (secret (ctr_63)) in
  chacha20_update (state_65) (m_64).

