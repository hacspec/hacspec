(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Hacspec_Sha256.

Definition block_len_v : uint_size :=
  k_size_v.

Definition prk_t := nseq (uint8) (hash_size_v).

Definition block_t := nseq (uint8) (block_len_v).

Definition i_pad_v : block_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8
      ] in  l).

Definition o_pad_v : block_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8
      ] in  l).

Definition k_block (k_0 : byte_seq) : block_t :=
  (if ((seq_len (k_0)) >.? (block_len_v)):bool then (array_update_start (
        array_new_ (default) (block_len_v)) (hash (k_0))) else (
      array_update_start (array_new_ (default) (block_len_v)) (k_0))).

Definition hmac (k_1 : byte_seq) (txt_2 : byte_seq) : prk_t :=
  let k_block_3 : block_t :=
    k_block (k_1) in 
  let h_in_4 : seq uint8 :=
    seq_from_seq ((k_block_3) array_xor (i_pad_v)) in 
  let h_in_4 :=
    seq_concat (h_in_4) (txt_2) in 
  let h_inner_5 : sha256_digest_t :=
    hash (h_in_4) in 
  let h_in_6 : seq uint8 :=
    seq_from_seq ((k_block_3) array_xor (o_pad_v)) in 
  let h_in_6 :=
    seq_concat (h_in_6) (h_inner_5) in 
  array_from_seq (hash_size_v) (hash (h_in_6)).

