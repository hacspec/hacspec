Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Lib.

Definition poly_key := nseq (uint8) (usize 32).

Definition blocksize : uint_size :=
  usize 16.

Definition poly_block := nseq (uint8) (usize 16).

Definition tag := nseq (uint8) (usize 16).

Notation "'sub_block'" := (byte_seq) : hacspec_scope.

Notation "'block_index'" := (uint_size) : hacspec_scope.

Definition field_canvas := nseq (int8) (17).
Definition field_element := nat_mod 0x03fffffffffffffffffffffffffffffffb.

Notation "'poly_state'" := ((field_element × field_element × poly_key
)) : hacspec_scope.

Definition poly1305_encode_r (b_0 : poly_block) : field_element :=
  let n_1 :=
    uint128_from_le_bytes (array_from_seq (16) (b_0)) in 
  let n_1 :=
    (n_1) .& (secret (repr 21267647620597763993911028882763415551)) in 
  nat_mod_from_secret_literal (n_1).

Definition poly1305_encode_block (b_2 : poly_block) : field_element :=
  let n_3 :=
    uint128_from_le_bytes (array_from_seq (16) (b_2)) in 
  let f_4 :=
    nat_mod_from_secret_literal (n_3) in 
  (f_4) +% (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (usize 128)).

Definition poly1305_encode_last
  (pad_len_5 : block_index)
  (b_6 : sub_block)
  : field_element :=
  let n_7 :=
    uint128_from_le_bytes (
      array_from_slice (secret (repr 0)) (16) (b_6) (usize 0) (
        seq_len (b_6))) in 
  let f_8 :=
    nat_mod_from_secret_literal (n_7) in 
  (f_8) +% (
    nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (
      (usize 8) * (pad_len_5))).

Definition poly1305_init (k_9 : poly_key) : poly_state :=
  let r_10 :=
    poly1305_encode_r (
      array_from_slice (secret (repr 0)) (16) (k_9) (usize 0) (usize 16)) in 
  (nat_mod_zero , r_10, k_9).

Definition poly1305_update_block
  (b_11 : poly_block)
  (st_12 : poly_state)
  : poly_state :=
  let '(acc_13, r_14, k_15) :=
    st_12 in 
  (((poly1305_encode_block (b_11)) +% (acc_13)) *% (r_14), r_14, k_15).

Definition poly1305_update_blocks
  (m_16 : byte_seq)
  (st_17 : poly_state)
  : poly_state :=
  let st_18 :=
    st_17 in 
  let nblocks_19 :=
    (seq_len (m_16)) / (blocksize) in 
  let st_18 :=
    foldi (usize 0) (nblocks_19) (fun i_20 st_18 =>
      let block_21 :=
        array_from_seq (16) (seq_get_exact_chunk (m_16) (blocksize) (i_20)) in 
      let st_18 :=
        poly1305_update_block (block_21) (st_18) in 
      (st_18))
    st_18 in 
  st_18.

Definition poly1305_update_last
  (pad_len_22 : uint_size)
  (b_23 : sub_block)
  (st_24 : poly_state)
  : poly_state :=
  let st_25 :=
    st_24 in 
  let '(st_25) :=
    if (seq_len (b_23)) !=.? (usize 0):bool then (
      let '(acc_26, r_27, k_28) :=
        st_25 in 
      let st_25 :=
        (
          ((poly1305_encode_last (pad_len_22) (b_23)) +% (acc_26)) *% (r_27),
          r_27,
          k_28
        ) in 
      (st_25)
    ) else ( (st_25)
    ) in 
  st_25.

Definition poly1305_update
  (m_29 : byte_seq)
  (st_30 : poly_state)
  : poly_state :=
  let st_31 :=
    poly1305_update_blocks (m_29) (st_30) in 
  let last_32 :=
    seq_get_remainder_chunk (m_29) (blocksize) in 
  poly1305_update_last (seq_len (last_32)) (last_32) (st_31).

Definition poly1305_finish (st_33 : poly_state) : tag :=
  let '(acc_34, _, k_35) :=
    st_33 in 
  let n_36 :=
    uint128_from_le_bytes (
      array_from_slice (secret (repr 0)) (16) (k_35) (usize 16) (usize 16)) in 
  let aby_37 :=
    nat_mod_to_byte_seq_le (acc_34) in 
  let a_38 :=
    uint128_from_le_bytes (
      array_from_slice (secret (repr 0)) (16) (aby_37) (usize 0) (usize 16)) in 
  array_from_seq (16) (uint128_to_le_bytes ((a_38) .+ (n_36))).

Definition poly1305 (m_39 : byte_seq) (key_40 : poly_key) : tag :=
  let st_41 :=
    poly1305_init (key_40) in 
  let st_41 :=
    poly1305_update (m_39) (st_41) in 
  poly1305_finish (st_41).

