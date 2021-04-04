module Hacspec.Poly1305.Edited

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open Hacspec.Lib
open FStar.Mul



type poly_key = lseq (uint8) (usize 32)

let blocksize : uint_size =
  usize 16

type poly_block = lseq (uint8) (usize 16)

type tag = lseq (uint8) (usize 16)

type field_canvas = lseq (pub_uint8) (17)

type field_element = nat_mod 0x03fffffffffffffffffffffffffffffffb

type sub_block = b:byte_seq{seq_len b <= 16}
type block_index = n:uint_size{n <= 16}
type poly_state = (field_element & field_element & poly_key)


let poly1305_encode_r (b_0 : poly_block) : field_element =
  let n_1 = uint128_from_le_bytes (array_from_seq (16) (b_0)) in
  let n_1 = (n_1) &. (secret (pub_u128 0xffffffc0ffffffc0ffffffc0fffffff)) in
  nat_from_secret_literal (0x03fffffffffffffffffffffffffffffffb) (n_1)

let poly1305_encode_block (b_2 : poly_block) : field_element =
  let n_3 = uint128_from_le_bytes (array_from_seq (16) (b_2)) in
  let f_4 =
    nat_from_secret_literal (0x03fffffffffffffffffffffffffffffffb) (n_3)
  in
  (f_4) +% (nat_pow2 (0x03fffffffffffffffffffffffffffffffb) (usize 128))

let poly1305_encode_last
  (pad_len_5 : block_index)
  (b_6 : sub_block)
  : field_element =
  let n_7 =
    uint128_from_le_bytes (
      array_from_slice (secret (pub_u8 0x0)) (16) (b_6) (usize 0) (
        seq_len (b_6)))
  in
  let f_8 =
    nat_from_secret_literal (0x03fffffffffffffffffffffffffffffffb) (n_7)
  in
  pow2_le_compat (8 * pad_len_5) 128;
  (f_8) +% (
    nat_pow2 (0x03fffffffffffffffffffffffffffffffb) ((usize 8) * (pad_len_5)))

let poly1305_init (k_9 : poly_key) : poly_state =
  let r_10 =
    poly1305_encode_r (
      array_from_slice (secret (pub_u8 0x0)) (16) (k_9) (usize 0) (usize 16))
  in
  (nat_zero (0x03fffffffffffffffffffffffffffffffb), r_10, k_9)

let poly1305_update_block
  (b_11 : poly_block)
  (st_12 : poly_state)
  : poly_state =
  let (acc_13, r_14, k_15) = st_12 in
  (((poly1305_encode_block (b_11)) +% (acc_13)) *% (r_14), r_14, k_15)

let get_full_chunk  (m_16 : seq uint8) (cs_17 : uint_size{cs_17 >0}) (i_18 : uint_size{i_18 < (seq_len m_16 / cs_17)})  : lseq uint8 cs_17 =
    assert ((i_18 + 1) * cs_17 <= seq_len m_16);
    Lib.Sequence.sub #_ #(seq_len m_16) (m_16) (cs_17 * i_18) cs_17

let get_last_chunk (m_21 : seq uint8) (cs_22 : uint_size{cs_22 > 0}) : seq uint8 =
  let nblocks_23 = (seq_len (m_21)) / (cs_22) in
  let rem = (seq_len (m_21)) % (cs_22) in
  Lib.Sequence.sub #_ #(seq_len m_21) (m_21) (cs_22 * nblocks_23) rem

let poly1305_update_blocks (m_26 : byte_seq) (st_27 : poly_state) : poly_state =
  let st_28 = st_27 in
  let nblocks_29 = (seq_len (m_26)) / (blocksize) in
  let (st_28) =
    foldi (usize 0) (nblocks_29) (fun i_30 (st_28) ->
      let block_31 =
        array_from_seq (16) (get_full_chunk (m_26) (blocksize) (i_30))
      in
      let st_28 = poly1305_update_block (block_31) (st_28) in
      (st_28))
    (st_28)
  in
  st_28

let poly1305_update_last
  (pad_len_32 : block_index)
  (b_33 : sub_block)
  (st_34 : poly_state)
  : poly_state =
  let st_35 = st_34 in
  let (st_35) =
    if (seq_len (b_33)) <> (usize 0) then begin
      let (acc_36, r_37, k_38) = st_35 in
      let st_35 =
        (
          ((poly1305_encode_last (pad_len_32) (b_33)) +% (acc_36)) *% (r_37),
          r_37,
          k_38
        )
      in
      (st_35)
    end else begin (st_35)
    end
  in
  st_35

let poly1305_update (m_39 : byte_seq) (st_40 : poly_state) : poly_state =
  let st_41 = poly1305_update_blocks (m_39) (st_40) in
  let last_42 = get_last_chunk (m_39) (blocksize) in
  poly1305_update_last (seq_len (last_42)) (last_42) (st_41)

let poly1305_finish (st_43 : poly_state) : tag =
  let (acc_44, _, k_45) = st_43 in
  let n_46 =
    uint128_from_le_bytes (
      array_from_slice (secret (pub_u8 0x0)) (16) (k_45) (usize 16) (usize 16))
  in
  let aby_47 =
    nat_to_byte_seq_le (0x03fffffffffffffffffffffffffffffffb) 16 (acc_44)
  in
  let a_48 =
    uint128_from_le_bytes aby_47
  in
  array_from_seq (16) (uint128_to_le_bytes ((a_48) +. (n_46)))

let poly1305 (m_49 : byte_seq) (key_50 : poly_key) : tag =
  let st_51 = poly1305_init (key_50) in
  let st_51 = poly1305_update (m_49) (st_51) in
  poly1305_finish (st_51)

