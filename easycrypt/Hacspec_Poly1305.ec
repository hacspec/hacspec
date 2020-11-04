require import List Int IntDiv CoreMap AllCore.
require import Array3 Array4 Array8 Array12 Array16 Array17 Array32 Array64.
require import WArray64.

from Jasmin require import JModel JMemory JArray.
require import Hacspec.


type key_poly = uint8 Array32.t.

op blocksize : uint_size =
  16.

type block = uint8 Array16.t.

type tag = pub_uint8 Array16.t.

type field_canvas = pub_uint8 Array17.t.

type field_element = int.

op le_bytes_to_num (b_0 : byte_seq) : uint128 =
  let block_as_u128_1 =
    array_16_from_slice (secret (pub_u8 8)) (b_0) (0) (
      min (blocksize) (seq_len (b_0)))
  in
  uint128_from_le_bytes (block_as_u128_1).

op clamp (r_2 : uint128) : field_element =
  let r_uint_3 =
    W128.andw (r_2) (secret (pub_u128 21267647620597763993911028882763415551))
  in
  nat_from_secret_literal (r_uint_3).

op encode (block_uint_4 : uint128) (len_5 : uint_size) : field_element =
  let w_elem_6 = nat_from_secret_literal (block_uint_4) in
  let l_elem_7 = nat_pow2 ((8) * (len_5)) in
  (w_elem_6) + (l_elem_7).

op poly_finish (a_8 : field_element) (s_9 : field_element) : tag =
  let a_10 = seq_slice (nat_to_public_byte_seq_be (17) (a_8)) (1) (blocksize) in
  let a_11 = u128_from_be_bytes (array_16_from_seq (a_10)) in
  let s_12 = seq_slice (nat_to_public_byte_seq_be (17) (s_9)) (1) (blocksize) in
  let s_13 = u128_from_be_bytes (array_16_from_seq (s_12)) in
  let a_14 = pub_uint128_wrapping_add (a_11) (s_13) in
  (* *) let tmp = u128_to_le_bytes (a_14) in 
  (* *) let tmp = Sequence.of_list witness (Array16.to_list tmp) in
  array_16_from_seq tmp.

op poly (m_15 : byte_seq) (key_16 : key_poly) : tag =
  let r_17 = le_bytes_to_num (array_32_slice (key_16) (0) (blocksize)) in
  let r_18 = clamp (r_17) in
  let s_19 =
    le_bytes_to_num (array_32_slice (key_16) (blocksize) (blocksize))
  in
  let s_20 = nat_from_secret_literal (s_19) in
  let a_21 = nat_from_literal (pub_u128 0) in
  let a_21 =
    foldi (0) (seq_num_chunks (m_15) (blocksize)) (fun i_22 a_21 =>
      let (len_23, block_24) = seq_get_chunk (m_15) (blocksize) (i_22) in
      let block_uint_25 = le_bytes_to_num (block_24) in
      let n_26 = encode (block_uint_25) (len_23) in
      let a_21 = (a_21) + (n_26) in
      let a_21 = (r_18) * (a_21) in
      a_21)
    a_21
  in
  poly_finish (a_21) (s_20).

