(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp.word Require Import ssrZ word.
From Jasmin Require Import word.

From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope bool_scope.

Require Import ChoiceEquality.
Require Import LocationUtility.
Require Import Hacspec_Lib_Comparable.
Require Import Hacspec_Lib_Pre.
Require Import Hacspec_Lib.

Open Scope hacspec_scope.

Obligation Tactic := try timeout 8 solve_ssprove_obligations.


Require Import Hacspec_Sha256.

Definition block_len_v : uint_size :=
  k_size_v.

Definition prk_t := nseq (uint8) (hash_size_v).

Definition block_t := nseq (uint8) (block_len_v).

Definition i_pad_v : block_t :=
  array_from_list uint8 [
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8
  ].

Definition o_pad_v : block_t :=
  array_from_list uint8 [
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8
  ].


Notation "'k_block_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'k_block_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'k_block_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'k_block_out'" :=(block_t : ChoiceEquality) (at level 2).
Definition K_BLOCK : nat :=
  929.
Program Definition k_block (k_928 : byte_seq)
  : both (fset.fset0) [interface] (block_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((seq_len (lift_to_both0 k_928)) >.? (
            lift_to_both0 block_len_v))
        then array_update_start (array_new_ (default : uint8) (block_len_v)) (
          array_to_seq (hash (lift_to_both0 k_928)))
        else array_update_start (array_new_ (default : uint8) (block_len_v)) (
          lift_to_both0 k_928))
      ) : both (fset.fset0) [interface] (block_t)).
Fail Next Obligation.

Definition h_in_930_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 932%nat).
Definition h_in_931_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 933%nat).
Notation "'hmac_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'hmac_inp'" :=(byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'hmac_out'" :=(prk_t : choice_type) (in custom pack_type at level 2).
Notation "'hmac_out'" :=(prk_t : ChoiceEquality) (at level 2).
Definition HMAC : nat :=
  938.
Program Definition hmac (k_934 : byte_seq) (txt_936 : byte_seq)
  : both (CEfset ([h_in_930_loc ; h_in_931_loc])) [interface] (prk_t) :=
  ((letb k_block_935 : block_t := k_block (lift_to_both0 k_934) in
      letbm h_in_930 : seq uint8 loc( h_in_930_loc ) :=
        seq_from_seq (array_to_seq ((lift_to_both0 k_block_935) array_xor (
            lift_to_both0 i_pad_v))) in
      letbm h_in_930 loc( h_in_930_loc ) :=
        seq_concat (lift_to_both0 h_in_930) (lift_to_both0 txt_936) in
      letb h_inner_937 : sha256_digest_t := hash (lift_to_both0 h_in_930) in
      letbm h_in_931 : seq uint8 loc( h_in_931_loc ) :=
        seq_from_seq (array_to_seq ((lift_to_both0 k_block_935) array_xor (
            lift_to_both0 o_pad_v))) in
      letbm h_in_931 loc( h_in_931_loc ) :=
        seq_concat (lift_to_both0 h_in_931) (
          array_to_seq (lift_to_both0 h_inner_937)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (
          hash_size_v) (array_to_seq (hash (lift_to_both0 h_in_931))))
      ) : both (CEfset ([h_in_930_loc ; h_in_931_loc])) [interface] (prk_t)).
Fail Next Obligation.

