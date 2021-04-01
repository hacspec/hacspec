require import List Int IntDiv CoreMap AllCore.
require import Array3 Array4 Array8 Array12 Array16 Array17 Array32 Array64.
require import WArray64.

from Jasmin require import JModel JMemory JArray.
require import Hacspec.


type poly_key = uint8 Array32.t.

op blocksize : uint_size =
  16.

type poly_block = uint8 Array16.t.

type tag = uint8 Array16.t.

type field_canvas = pub_uint8 Array17.t.

type field_element = int.

op poly1305_encode_r (b_0 : poly_block) : field_element =
  let n_1 = uint128_from_le_bytes (array_16_from_seq (b_0)) in
  let n_1 =
    W128.andw (n_1) (secret (pub_u128 21267647620597763993911028882763415551))
  in
  nat_from_secret_literal (n_1).

op poly1305_encode_block (len_2 : uint_size) (b_3 : sub_block) : field_element =
  let n_4 =
    uint128_from_le_bytes (
      array_16_from_slice (secret (pub_u8 8)) (b_3) (0) (seq_len (b_3)))
  in
  let f_5 = nat_from_secret_literal (n_4) in
  (f_5) + (nat_pow2 ((8) * (len_2))).

op poly1305_init (k_6 : poly_key) : poly_state =
  let r_7 =
    poly1305_encode_r (array_16_from_slice (secret (pub_u8 8)) (k_6) (0) (16))
  in
  (nat_zero (), r_7, k_6).

op poly1305_update1
  (len_8 : uint_size)
  (b_9 : sub_block)
  (st_10 : poly_state)
  : poly_state =
  let (acc_11, r_12, k_13) = st_10 in
  (((poly1305_encode_block (len_8) (b_9)) + (acc_11)) * (r_12), r_12, k_13).

op poly1305_finish (st_14 : poly_state) : tag =
  let (acc_15, _, k_16) = st_14 in
  let n_17 =
    uint128_from_le_bytes (
      array_16_from_slice (secret (pub_u8 8)) (k_16) (16) (16))
  in
  let aby_18 = nat_to_byte_seq_le (acc_15) in
  let a_19 =
    uint128_from_le_bytes (
      array_16_from_slice (secret (pub_u8 8)) (aby_18) (0) (16))
  in
  array_16_from_seq (uint128_to_le_bytes ((a_19) + (n_17))).

op poly1305_update (m_20 : byte_seq) (st_21 : poly_state) : poly_state =
  let st_22 = st_21 in
  let st_22 =
    foldi (0) (seq_num_chunks (m_20) (blocksize)) (fun i_23 st_22 =>
      let (len_24, block_25) = seq_get_chunk (m_20) (blocksize) (i_23) in
      let st_22 = poly1305_update1 (len_24) (block_25) (st_22) in
      st_22)
    st_22
  in
  st_22.

op poly1305 (m_26 : byte_seq) (key_27 : poly_key) : tag =
  let st_28 = poly1305_init (key_27) in
  let st_28 = poly1305_update (m_26) (st_28) in
  poly1305_finish (st_28).

