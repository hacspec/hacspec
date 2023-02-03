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
  @array_from_list uint8 [(secret (@repr U8 1)) : uint8].

Definition two_v : int_byte_t :=
  @array_from_list uint8 [(secret (@repr U8 2)) : uint8].

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
  3374.
Program Definition vrf_mgf1 (n_3368 : rsa_int_t) (alpha_3371 : byte_seq)
  : both (fset.fset0) [interface] (byte_seq_result_t) :=
  ((letbnd(_) mgf_salt1_3367 : seq uint8 :=
        i2osp (rsa_int_from_literal (
            (fun x => lift_to_both0 (repr (unsigned x)))(
              lift_to_both0 byte_size_v))) (lift_to_both0 (@repr U32 4)) in
      letbnd(_) mgf_salt2_3369 : seq uint8 :=
        i2osp (lift_to_both0 n_3368) (lift_to_both0 byte_size_v) in
      letb mgf_salt_3370 : seq uint8 :=
        seq_concat (lift_to_both0 mgf_salt1_3367) (
          lift_to_both0 mgf_salt2_3369) in
      letb mgf_string_3372 : seq uint8 :=
        seq_concat (seq_concat (array_concat (lift_to_both0 suite_string_v) (
              array_to_seq (lift_to_both0 one_v))) (
            lift_to_both0 mgf_salt_3370)) (lift_to_both0 alpha_3371) in
      letbnd(_) mgf_3373 : seq uint8 :=
        mgf1 (lift_to_both0 mgf_string_3372) ((
            (fun x => lift_to_both0 (repr (unsigned x)))(
              lift_to_both0 byte_size_v)) .- (lift_to_both0 (usize 1))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok seq uint8 error_t (
          lift_to_both0 mgf_3373))
      ) : both (fset.fset0) [interface] (byte_seq_result_t)).
Fail Next Obligation.


Notation "'prove_inp'" :=(
  sk_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'prove_inp'" :=(sk_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'prove_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'prove_out'" :=(byte_seq_result_t : ChoiceEquality) (at level 2).
Definition PROVE : nat :=
  3382.
Program Definition prove (sk_3375 : sk_t) (alpha_3378 : byte_seq)
  : both (fset.fset0) [interface] (byte_seq_result_t) :=
  ((letb '(n_3376, d_3377) : (rsa_int_t '× rsa_int_t) :=
        (lift_to_both0 sk_3375) in
      letbnd(_) em_3379 : seq uint8 :=
        vrf_mgf1 (lift_to_both0 n_3376) (lift_to_both0 alpha_3378) in
      letb m_3380 : rsa_int_t := os2ip (lift_to_both0 em_3379) in
      letbnd(_) s_3381 : rsa_int_t :=
        rsasp1 (lift_to_both0 sk_3375) (lift_to_both0 m_3380) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (i2osp (
          lift_to_both0 s_3381) (lift_to_both0 byte_size_v))
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
  3385.
Program Definition proof_to_hash (pi_string_3383 : byte_seq)
  : both (fset.fset0) [interface] (byte_seq_result_t) :=
  ((letb hash_string_3384 : seq uint8 :=
        array_concat (lift_to_both0 suite_string_v) (array_concat (
            lift_to_both0 two_v) (lift_to_both0 pi_string_3383)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok seq uint8 error_t (
          array_slice (sha256 (lift_to_both0 hash_string_3384)) (lift_to_both0 (
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
  3395.
Program Definition verify (pk_3386 : pk_t) (alpha_3392 : byte_seq) (
    pi_string_3389 : byte_seq)
  : both (fset.fset0) [interface] (byte_seq_result_t) :=
  ((letb '(n_3387, e_3388) : (rsa_int_t '× rsa_int_t) :=
        (lift_to_both0 pk_3386) in
      letb s_3390 : rsa_int_t := os2ip (lift_to_both0 pi_string_3389) in
      letbnd(_) m_3391 : rsa_int_t :=
        rsavp1 (lift_to_both0 pk_3386) (lift_to_both0 s_3390) in
      letbnd(_) em_prime_3393 : seq uint8 :=
        vrf_mgf1 (lift_to_both0 n_3387) (lift_to_both0 alpha_3392) in
      letb m_prime_3394 : rsa_int_t := os2ip (lift_to_both0 em_prime_3393) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 m_3391) =.? (
            lift_to_both0 m_prime_3394))
        then proof_to_hash (lift_to_both0 pi_string_3389)
        else @Err seq uint8 error_t (VerificationFailed))
      ) : both (fset.fset0) [interface] (byte_seq_result_t)).
Fail Next Obligation.

