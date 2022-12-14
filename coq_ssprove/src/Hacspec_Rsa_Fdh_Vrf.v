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

Require Import Hacspec_Rsa_Pkcs1.

Definition int_byte_t := nseq (uint8) (usize 1).

Definition one_v : int_byte_t :=
  array_from_list uint8 [(secret (@repr U8 1)) : uint8].

Definition two_v : int_byte_t :=
  array_from_list uint8 [(secret (@repr U8 2)) : uint8].

Definition suite_string_v : int_byte_t :=
  one_v.


Notation "'vrf_mgf1_inp'" :=(
  rsa_int_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'vrf_mgf1_inp'" :=(
  rsa_int_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'vrf_mgf1_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'vrf_mgf1_out'" :=(byte_seq_result_t : ChoiceEquality) (at level 2).
Definition VRF_MGF1 : nat :=
  3294.
Program Definition vrf_mgf1 (n_3288 : rsa_int_t) (alpha_3291 : byte_seq)
  : both (fset.fset0) [interface] (byte_seq_result_t) :=
  ((letbnd(_) mgf_salt1_3287 : seq uint8 :=
        i2osp (rsa_int_from_literal (
            (fun x => lift_to_both0 (repr (unsigned x)))(
              lift_to_both0 byte_size_v))) (lift_to_both0 (@repr U32 4)) in
      letbnd(_) mgf_salt2_3289 : seq uint8 :=
        i2osp (lift_to_both0 n_3288) (lift_to_both0 byte_size_v) in
      letb mgf_salt_3290 : seq uint8 :=
        seq_concat (lift_to_both0 mgf_salt1_3287) (
          lift_to_both0 mgf_salt2_3289) in
      letb mgf_string_3292 : seq uint8 :=
        seq_concat (seq_concat (array_concat (lift_to_both0 suite_string_v) (
              array_to_seq (lift_to_both0 one_v))) (
            lift_to_both0 mgf_salt_3290)) (lift_to_both0 alpha_3291) in
      letbnd(_) mgf_3293 : seq uint8 :=
        mgf1 (lift_to_both0 mgf_string_3292) ((
            (fun x => lift_to_both0 (repr (unsigned x)))(
              lift_to_both0 byte_size_v)) .- (lift_to_both0 (usize 1))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok seq uint8 error_t (
          lift_to_both0 mgf_3293))
      ) : both (fset.fset0) [interface] (byte_seq_result_t)).
Fail Next Obligation.


Notation "'prove_inp'" :=(
  sk_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'prove_inp'" :=(sk_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'prove_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'prove_out'" :=(byte_seq_result_t : ChoiceEquality) (at level 2).
Definition PROVE : nat :=
  3302.
Program Definition prove (sk_3295 : sk_t) (alpha_3298 : byte_seq)
  : both (fset.fset0) [interface] (byte_seq_result_t) :=
  ((letb '(n_3296, d_3297) : (rsa_int_t '× rsa_int_t) :=
        (lift_to_both0 sk_3295) in
      letbnd(_) em_3299 : seq uint8 :=
        vrf_mgf1 (lift_to_both0 n_3296) (lift_to_both0 alpha_3298) in
      letb m_3300 : rsa_int_t := os2ip (lift_to_both0 em_3299) in
      letbnd(_) s_3301 : rsa_int_t :=
        rsasp1 (lift_to_both0 sk_3295) (lift_to_both0 m_3300) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (i2osp (
          lift_to_both0 s_3301) (lift_to_both0 byte_size_v))
      ) : both (fset.fset0) [interface] (byte_seq_result_t)).
Fail Next Obligation.


Notation "'proof_to_hash_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'proof_to_hash_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'proof_to_hash_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'proof_to_hash_out'" :=(
  byte_seq_result_t : ChoiceEquality) (at level 2).
Definition PROOF_TO_HASH : nat :=
  3305.
Program Definition proof_to_hash (pi_string_3303 : byte_seq)
  : both (fset.fset0) [interface] (byte_seq_result_t) :=
  ((letb hash_string_3304 : seq uint8 :=
        array_concat (lift_to_both0 suite_string_v) (array_concat (
            lift_to_both0 two_v) (lift_to_both0 pi_string_3303)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok seq uint8 error_t (
          array_slice (sha256 (lift_to_both0 hash_string_3304)) (lift_to_both0 (
              usize 0)) (lift_to_both0 (usize 32))))
      ) : both (fset.fset0) [interface] (byte_seq_result_t)).
Fail Next Obligation.


Notation "'verify_inp'" :=(
  pk_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'verify_inp'" :=(
  pk_t '× byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'verify_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'verify_out'" :=(byte_seq_result_t : ChoiceEquality) (at level 2).
Definition VERIFY : nat :=
  3315.
Program Definition verify (pk_3306 : pk_t) (alpha_3312 : byte_seq) (
    pi_string_3309 : byte_seq)
  : both (fset.fset0) [interface] (byte_seq_result_t) :=
  ((letb '(n_3307, e_3308) : (rsa_int_t '× rsa_int_t) :=
        (lift_to_both0 pk_3306) in
      letb s_3310 : rsa_int_t := os2ip (lift_to_both0 pi_string_3309) in
      letbnd(_) m_3311 : rsa_int_t :=
        rsavp1 (lift_to_both0 pk_3306) (lift_to_both0 s_3310) in
      letbnd(_) em_prime_3313 : seq uint8 :=
        vrf_mgf1 (lift_to_both0 n_3307) (lift_to_both0 alpha_3312) in
      letb m_prime_3314 : rsa_int_t := os2ip (lift_to_both0 em_prime_3313) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 m_3311) =.? (
            lift_to_both0 m_prime_3314))
        then proof_to_hash (lift_to_both0 pi_string_3309)
        else @Err seq uint8 error_t (VerificationFailed))
      ) : both (fset.fset0) [interface] (byte_seq_result_t)).
Fail Next Obligation.

