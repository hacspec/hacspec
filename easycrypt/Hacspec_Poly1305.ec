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

op poly1305_encode_block (b_2 : poly_block) : field_element =
  let n_3 = uint128_from_le_bytes (array_16_from_seq (b_2)) in
  let f_4 = nat_from_secret_literal (n_3) in
  (f_4) + (nat_pow2 (128)).

op poly1305_encode_last
  (pad_len_5 : block_index)
  (b_6 : sub_block)
  : field_element =
  let n_7 =
    uint128_from_le_bytes (
      array_16_from_slice (secret (pub_u8 8)) (b_6) (0) (seq_len (b_6)))
  in
  let f_8 = nat_from_secret_literal (n_7) in
  (f_8) + (nat_pow2 ((8) * (pad_len_5))).

op poly1305_init (k_9 : poly_key) : poly_state =
  let r_10 =
    poly1305_encode_r (array_16_from_slice (secret (pub_u8 8)) (k_9) (0) (16))
  in
  (nat_zero (), r_10, k_9).

op poly1305_update_block (b_11 : poly_block) (st_12 : poly_state) : poly_state =
  let (acc_13, r_14, k_15) = st_12 in
  (((poly1305_encode_block (b_11)) + (acc_13)) * (r_14), r_14, k_15).

op get_full_chunk
  (m_16 : uint8 Sequence.t)
  (cs_17 : uint_size)
  (i_18 : uint_size)
  : uint8 Sequence.t =
  let (len_19, block_20) = seq_get_chunk (m_16) (cs_17) (i_18) in
  block_20.

op get_last_chunk
  (m_21 : uint8 Sequence.t)
  (cs_22 : uint_size)
  : uint8 Sequence.t =
  let nblocks_23 = (seq_len (m_21)) / (cs_22) in
  let (len_24, block_25) = seq_get_chunk (m_21) (cs_22) (nblocks_23) in
  block_25.

op poly1305_update_blocks (m_26 : byte_seq) (st_27 : poly_state) : poly_state =
  let st_28 = st_27 in
  let nblocks_29 = (seq_len (m_26)) / (blocksize) in
  let st_28 =
    foldi (0) (nblocks_29) (fun i_30 st_28 =>
      let block_31 =
        array_16_from_seq (get_full_chunk (m_26) (blocksize) (i_30))
      in
      let st_28 = poly1305_update_block (block_31) (st_28) in
      st_28)
    st_28
  in
  st_28.

op poly1305_update_last
  (pad_len_32 : uint_size)
  (b_33 : sub_block)
  (st_34 : poly_state)
  : poly_state =
  let st_35 = st_34 in
  let st_35 =
    if (seq_len (b_33)) != (0) then begin
      let (acc_36, r_37, k_38) = st_35 in
      let st_35 =
        (
          ((poly1305_encode_last (pad_len_32) (b_33)) + (acc_36)) * (r_37),
          r_37,
          k_38
        )
      in
      st_35
    end else begin st_35
    end
  in
  st_35.

op poly1305_update (m_39 : byte_seq) (st_40 : poly_state) : poly_state =
  let st_41 = poly1305_update_blocks (m_39) (st_40) in
  let last_42 = get_last_chunk (m_39) (blocksize) in
  poly1305_update_last (seq_len (last_42)) (last_42) (st_41).

op poly1305_finish (st_43 : poly_state) : tag =
  let (acc_44, _, k_45) = st_43 in
  let n_46 =
    uint128_from_le_bytes (
      array_16_from_slice (secret (pub_u8 8)) (k_45) (16) (16))
  in
  let aby_47 = nat_to_byte_seq_le (acc_44) in
  let a_48 =
    uint128_from_le_bytes (
      array_16_from_slice (secret (pub_u8 8)) (aby_47) (0) (16))
  in
  array_16_from_seq (uint128_to_le_bytes ((a_48) + (n_46))).

op poly1305 (m_49 : byte_seq) (key_50 : poly_key) : tag =
  let st_51 = poly1305_init (key_50) in
  let st_51 = poly1305_update (m_49) (st_51) in
  poly1305_finish (st_51).

