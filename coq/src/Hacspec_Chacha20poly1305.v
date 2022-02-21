(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Hacspec_Chacha20.

Require Import Hacspec_Poly1305.

Inductive error_t :=
| InvalidTag : error_t.

Notation "'cha_cha_poly_key_t'" := (cha_cha_key_t) : hacspec_scope.

Notation "'cha_cha_poly_iv_t'" := (cha_cha_iv_t) : hacspec_scope.

Notation "'byte_seq_result_t'" := ((result byte_seq error_t)) : hacspec_scope.

Definition init
  (key_0 : cha_cha_poly_key_t)
  (iv_1 : cha_cha_poly_iv_t)
  : poly_state_t :=
  let key_block0_2 : block_t :=
    chacha20_key_block0 (key_0) (iv_1) in 
  let poly_key_3 : poly_key_t :=
    array_from_slice (default) (32) (key_block0_2) (usize 0) (usize 32) in 
  poly1305_init (poly_key_3).

Definition poly1305_update_padded
  (m_4 : byte_seq)
  (st_5 : poly_state_t)
  : poly_state_t :=
  let st_6 : (field_element_t × field_element_t × poly_key_t) :=
    poly1305_update_blocks (m_4) (st_5) in 
  let last_7 : seq uint8 :=
    seq_get_remainder_chunk (m_4) (usize 16) in 
  poly1305_update_last (usize 16) (last_7) (st_6).

Definition finish
  (aad_len_8 : uint_size)
  (cipher_len_9 : uint_size)
  (st_10 : poly_state_t)
  : poly1305_tag_t :=
  let last_block_11 : poly_block_t :=
    array_new_ (default) (16) in 
  let last_block_11 :=
    array_update (last_block_11) (usize 0) (uint64_to_le_bytes (secret (
          pub_u64 (aad_len_8)) : int64)) in 
  let last_block_11 :=
    array_update (last_block_11) (usize 8) (uint64_to_le_bytes (secret (
          pub_u64 (cipher_len_9)) : int64)) in 
  let st_12 : (field_element_t × field_element_t × poly_key_t) :=
    poly1305_update_block (last_block_11) (st_10) in 
  poly1305_finish (st_12).

Definition chacha20_poly1305_encrypt
  (key_13 : cha_cha_poly_key_t)
  (iv_14 : cha_cha_poly_iv_t)
  (aad_15 : byte_seq)
  (msg_16 : byte_seq)
  : (byte_seq × poly1305_tag_t) :=
  let cipher_text_17 : seq uint8 :=
    chacha20 (key_13) (iv_14) (@repr WORDSIZE32 1) (msg_16) in 
  let poly_st_18 : (field_element_t × field_element_t × poly_key_t) :=
    init (key_13) (iv_14) in 
  let poly_st_18 :=
    poly1305_update_padded (aad_15) (poly_st_18) in 
  let poly_st_18 :=
    poly1305_update_padded (cipher_text_17) (poly_st_18) in 
  let tag_19 : poly1305_tag_t :=
    finish (seq_len (aad_15)) (seq_len (cipher_text_17)) (poly_st_18) in 
  (cipher_text_17, tag_19).

Definition chacha20_poly1305_decrypt
  (key_20 : cha_cha_poly_key_t)
  (iv_21 : cha_cha_poly_iv_t)
  (aad_22 : byte_seq)
  (cipher_text_23 : byte_seq)
  (tag_24 : poly1305_tag_t)
  : byte_seq_result_t :=
  let poly_st_25 : (field_element_t × field_element_t × poly_key_t) :=
    init (key_20) (iv_21) in 
  let poly_st_25 :=
    poly1305_update_padded (aad_22) (poly_st_25) in 
  let poly_st_25 :=
    poly1305_update_padded (cipher_text_23) (poly_st_25) in 
  let my_tag_26 : poly1305_tag_t :=
    finish (seq_len (aad_22)) (seq_len (cipher_text_23)) (poly_st_25) in 
  (if (array_declassify_eq (my_tag_26) (tag_24)):bool then (
      @Ok byte_seq error_t (chacha20 (key_20) (iv_21) (@repr WORDSIZE32 1) (
          cipher_text_23))) else (@Err byte_seq error_t (InvalidTag))).

