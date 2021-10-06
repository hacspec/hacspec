Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Lib.

Require Import Hacspec.Chacha20.

Require Import Hacspec.Poly1305.

Notation "'cha_cha_poly_key'" := (cha_cha_key) : hacspec_scope.

Notation "'cha_cha_poly_iv'" := (cha_cha_iv) : hacspec_scope.

Definition init
  (key_0 : cha_cha_poly_key)
  (iv_1 : cha_cha_poly_iv)
  : poly_state :=
  let key_block0_2 :=
    chacha20_key_block0 (key_0) (iv_1) in 
  let poly_key_3 :=
    array_from_slice (secret (repr 0)) (32) (key_block0_2) (usize 0) (
      usize 32) in 
  poly1305_init (poly_key_3).

Definition poly1305_update_padded
  (m_4 : byte_seq)
  (st_5 : poly_state)
  : poly_state :=
  let st_6 :=
    poly1305_update_blocks (m_4) (st_5) in 
  let last_7 :=
    seq_get_remainder_chunk (m_4) (usize 16) in 
  poly1305_update_last (usize 16) (last_7) (st_6).

Definition finish
  (aadlen_8 : uint_size)
  (cipherlen_9 : uint_size)
  (st_10 : poly_state)
  : tag :=
  let last_block_11 :=
    array_new_ (secret (repr 0)) (16) in 
  let last_block_11 :=
    array_update (last_block_11) (usize 0) (
      uint64_to_le_bytes (secret (pub_u64 (aadlen_8)))) in 
  let last_block_11 :=
    array_update (last_block_11) (usize 8) (
      uint64_to_le_bytes (secret (pub_u64 (cipherlen_9)))) in 
  let st_12 :=
    poly1305_update_block (last_block_11) (st_10) in 
  poly1305_finish (st_12).

Definition encrypt
  (key_13 : cha_cha_poly_key)
  (iv_14 : cha_cha_poly_iv)
  (aad_15 : byte_seq)
  (msg_16 : byte_seq)
  : (byte_seq × tag) :=
  let cipher_text_17 :=
    chacha20 (key_13) (iv_14) (repr 1) (msg_16) in 
  let poly_st_18 :=
    init (key_13) (iv_14) in 
  let poly_st_18 :=
    poly1305_update_padded (aad_15) (poly_st_18) in 
  let poly_st_18 :=
    poly1305_update_padded (cipher_text_17) (poly_st_18) in 
  let tag_19 :=
    finish (seq_len (aad_15)) (seq_len (cipher_text_17)) (poly_st_18) in 
  (cipher_text_17, tag_19).

Definition decrypt
  (key_20 : cha_cha_poly_key)
  (iv_21 : cha_cha_poly_iv)
  (aad_22 : byte_seq)
  (cipher_text_23 : byte_seq)
  (tag_24 : tag)
  : (bool × byte_seq) :=
  let poly_st_25 :=
    init (key_20) (iv_21) in 
  let poly_st_25 :=
    poly1305_update_padded (aad_22) (poly_st_25) in 
  let poly_st_25 :=
    poly1305_update_padded (cipher_text_23) (poly_st_25) in 
  let my_tag_26 :=
    finish (seq_len (aad_22)) (seq_len (cipher_text_23)) (poly_st_25) in 
  if (array_declassify_eq (my_tag_26) (tag_24)):bool then (
    (true, chacha20 (key_20) (iv_21) (repr 1) (cipher_text_23))) else (
    (false, seq_new_ (secret (repr 0)) (usize 0))).

