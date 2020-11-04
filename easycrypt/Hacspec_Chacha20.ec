require import List Int IntDiv CoreMap AllCore.
require import Array3 Array4 Array8 Array12 Array16 Array17 Array32 Array64.
require import WArray64.

from Jasmin require import JModel JMemory JArray.
require import Hacspec.


type state = uint32 Array16.t.

type state_idx = uint_size.

type state_bytes = uint8 Array64.t.

type iv = uint8 Array12.t.

type key = uint8 Array32.t.

op state_to_bytes (x_0 : state) : state_bytes =
  let r_1 = array_64_new_ (secret (pub_u8 8)) in
  let r_1 =
    foldi (0) (array_16_len (x_0)) (fun i_2 (r_1 : 
      (* *) uint8 Array64.t
    ) =>
      let bytes_3 = uint32_to_be_bytes (x_0.[i_2]) in
      let r_1 = r_1.[((i_2) * (4)) <- (bytes_3.[3])] in
      let r_1 = r_1.[(((i_2) * (4)) + (1)) <- (bytes_3.[2])] in
      let r_1 = r_1.[(((i_2) * (4)) + (2)) <- (bytes_3.[1])] in
      let r_1 = r_1.[(((i_2) * (4)) + (3)) <- (bytes_3.[0])] in
      r_1)
    r_1
  in
  r_1.

op chacha_line
  (a_4 : state_idx)
  (b_5 : state_idx)
  (d_6 : state_idx)
  (s_7 : uint_size)
  (m_8 : state)
  : state =
  let state_9 = m_8 in
  let state_9 = state_9.[(a_4) <- ((state_9.[a_4]) + (state_9.[b_5]))] in
  let state_9 = state_9.[(d_6) <- ((state_9.[d_6]) +^ (state_9.[a_4]))] in
  let state_9 = state_9.[(d_6) <- (uint32_rotate_left (state_9.[d_6]) (s_7))] in
  state_9.

op chacha_quarter_round
  (a_10 : state_idx)
  (b_11 : state_idx)
  (c_12 : state_idx)
  (d_13 : state_idx)
  (state_14 : state)
  : state =
  let state_15 = chacha_line (a_10) (b_11) (d_13) (16) (state_14) in
  let state_16 = chacha_line (c_12) (d_13) (b_11) (12) (state_15) in
  let state_17 = chacha_line (a_10) (b_11) (d_13) (8) (state_16) in
  chacha_line (c_12) (d_13) (b_11) (7) (state_17).

op chacha_double_round (state_18 : state) : state =
  let state_19 = chacha_quarter_round (0) (4) (8) (12) (state_18) in
  let state_20 = chacha_quarter_round (1) (5) (9) (13) (state_19) in
  let state_21 = chacha_quarter_round (2) (6) (10) (14) (state_20) in
  let state_22 = chacha_quarter_round (3) (7) (11) (15) (state_21) in
  let state_23 = chacha_quarter_round (0) (5) (10) (15) (state_22) in
  let state_24 = chacha_quarter_round (1) (6) (11) (12) (state_23) in
  let state_25 = chacha_quarter_round (2) (7) (8) (13) (state_24) in
  chacha_quarter_round (3) (4) (9) (14) (state_25).

op chacha20_constants_init (_: unit) : uint32 Sequence.t =
  let constants_26 = seq_new_ (secret (pub_u32 8)) (4) in
  let constants_26 = constants_26.[(0) <- (secret (pub_u32 1634760805))] in
  let constants_26 = constants_26.[(1) <- (secret (pub_u32 857760878))] in
  let constants_26 = constants_26.[(2) <- (secret (pub_u32 2036477234))] in
  let constants_26 = constants_26.[(3) <- (secret (pub_u32 1797285236))] in
  constants_26.

op chacha20_key_to_u32s (key_27 : key) : uint32 Sequence.t =
  (* *) let key_27 = Sequence.of_list witness (Array32.to_list key_27) in
  let uints_28 = seq_new_ (secret (pub_u32 8)) (8) in
  let uints_28 =
    uints_28.[(0) <- (
        uint32_from_le_bytes (
          array_4_from_slice_range (secret (pub_u8 8)) (key_27) ((0, 4))))]
  in
  let uints_28 =
    uints_28.[(1) <- (
        uint32_from_le_bytes (
          array_4_from_slice_range (secret (pub_u8 8)) (key_27) ((4, 8))))]
  in
  let uints_28 =
    uints_28.[(2) <- (
        uint32_from_le_bytes (
          array_4_from_slice_range (secret (pub_u8 8)) (key_27) ((8, 12))))]
  in
  let uints_28 =
    uints_28.[(3) <- (
        uint32_from_le_bytes (
          array_4_from_slice_range (secret (pub_u8 8)) (key_27) ((12, 16))))]
  in
  let uints_28 =
    uints_28.[(4) <- (
        uint32_from_le_bytes (
          array_4_from_slice_range (secret (pub_u8 8)) (key_27) ((16, 20))))]
  in
  let uints_28 =
    uints_28.[(5) <- (
        uint32_from_le_bytes (
          array_4_from_slice_range (secret (pub_u8 8)) (key_27) ((20, 24))))]
  in
  let uints_28 =
    uints_28.[(6) <- (
        uint32_from_le_bytes (
          array_4_from_slice_range (secret (pub_u8 8)) (key_27) ((24, 28))))]
  in
  let uints_28 =
    uints_28.[(7) <- (
        uint32_from_le_bytes (
          array_4_from_slice_range (secret (pub_u8 8)) (key_27) ((28, 32))))]
  in
  uints_28.

op chacha20_iv_to_u32s (iv_29 : iv) : uint32 Sequence.t =
  (* *) let iv_29 = Sequence.of_list witness (Array12.to_list iv_29) in  
  let uints_30 = seq_new_ (secret (pub_u32 8)) (3) in
  let uints_30 =
    uints_30.[(0) <- (
        uint32_from_le_bytes (
          array_4_from_slice_range (secret (pub_u8 8)) (iv_29) ((0, 4))))]
  in
  let uints_30 =
    uints_30.[(1) <- (
        uint32_from_le_bytes (
          array_4_from_slice_range (secret (pub_u8 8)) (iv_29) ((4, 8))))]
  in
  let uints_30 =
    uints_30.[(2) <- (
        uint32_from_le_bytes (
          array_4_from_slice_range (secret (pub_u8 8)) (iv_29) ((8, 12))))]
  in
  uints_30.

op chacha20_ctr_to_seq (ctr_31 : uint32) : uint32 Sequence.t =
  let uints_32 = seq_new_ (secret (pub_u32 8)) (1) in
  let uints_32 = uints_32.[(0) <- (ctr_31)] in
  uints_32.

op chacha_block_init (key_33 : key) (ctr_34 : uint32) (iv_35 : iv) : state =
  array_16_from_seq (
    seq_concat (
      seq_concat (
        seq_concat (chacha20_constants_init ()) (
          chacha20_key_to_u32s (key_33))) (chacha20_ctr_to_seq (ctr_34))) (
      chacha20_iv_to_u32s (iv_35))).

op chacha_block_inner (key_36 : key) (ctr_37 : uint32) (iv_38 : iv) : state =
  let st_39 = chacha_block_init (key_36) (ctr_37) (iv_38) in
  let state_40 = st_39 in
  let state_40 =
    foldi (0) (10) (fun i_41 state_40 =>
      let state_40 = chacha_double_round (state_40) in
      state_40)
    state_40
  in
  let state_40 =
    foldi (0) (16) (fun i_42 (state_40: 
      (* *) state
    ) =>
      let state_40 =
        state_40.[(i_42) <- ((state_40.[i_42]) + (st_39.[i_42]))]
      in
      state_40)
    state_40
  in
  state_40.

op chacha_block (key_43 : key) (ctr_44 : uint32) (iv_45 : iv) : state_bytes =
  let state_46 = chacha_block_inner (key_43) (ctr_44) (iv_45) in
  state_to_bytes (state_46).

op chacha (key_47 : key) (iv_48 : iv) (m_49 : byte_seq) : byte_seq =
  let ctr_50 = secret (pub_u32 1) in
  let blocks_out_51 = seq_new_ (secret (pub_u8 8)) (seq_len (m_49)) in
  let (ctr_50, blocks_out_51) =
    foldi (0) (seq_num_chunks (m_49) (64)) (fun i_52 acc =>
      let (ctr_50, blocks_out_51) =
        acc
      in
      let (block_len_53, msg_block_54) = seq_get_chunk (m_49) (64) (i_52) in
      let key_block_55 = chacha_block (key_47) (ctr_50) (iv_48) in
      let msg_block_padded_56 = array_64_new_ (secret (pub_u8 8)) in
      let msg_block_padded_57 =
        array_64_update_start (msg_block_padded_56) (msg_block_54)
      in
      let blocks_out_51 =
        seq_set_chunk (blocks_out_51) (64) (i_52) (
          array_64_slice_range (
            array_64_xor W8.(+^) (msg_block_padded_57) (key_block_55)) (
            (0, block_len_53)))
      in
      let ctr_50 = (ctr_50) + (secret (pub_u32 1)) in
      (ctr_50, blocks_out_51))
    (ctr_50, blocks_out_51)
  in
  blocks_out_51.

