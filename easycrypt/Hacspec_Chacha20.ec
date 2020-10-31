require import List Int IntDiv CoreMap AllCore.
require import Array3 Array4 Array8 Array12 Array16 Array32 Array64.
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
