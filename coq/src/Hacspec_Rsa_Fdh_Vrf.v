(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Hacspec_Sha256.

Require Import Hacspec_Rsa_Pkcs1.

Definition int_byte_t := nseq (uint8) (usize 1).

Definition one_v : int_byte_t :=
  array_from_list uint8 (let l := [secret (@repr WORDSIZE8 1) : int8] in  l).

Definition two_v : int_byte_t :=
  array_from_list uint8 (let l := [secret (@repr WORDSIZE8 2) : int8] in  l).

Definition suite_string_v : int_byte_t :=
  one_v.

Definition vrf_mgf1
  (n_2747 : rsa_int_t)
  (alpha_2748 : byte_seq)
  
  : byte_seq_result_t :=
  bind (i2osp (rsa_int_from_literal (@cast _ uint128 _ (byte_size_v))) (
      @repr WORDSIZE32 4)) (fun mgf_salt1_2749 => bind (i2osp (n_2747) (
        byte_size_v)) (fun mgf_salt2_2750 => let mgf_salt_2751 : seq uint8 :=
        seq_concat (mgf_salt1_2749) (mgf_salt2_2750) in 
      let mgf_string_2752 : seq uint8 :=
        seq_concat (seq_concat (array_concat (suite_string_v) (
              array_to_seq (one_v))) (mgf_salt_2751)) (alpha_2748) in 
      bind (mgf1 (mgf_string_2752) ((@cast _ uint32 _ (byte_size_v)) - (
            usize 1))) (fun mgf_2753 => @Ok seq uint8 error_t (mgf_2753)))).

Definition prove
  (sk_2754 : sk_t)
  (alpha_2755 : byte_seq)
  
  : byte_seq_result_t :=
  let '(n_2756, d_2757) :=
    (sk_2754) in 
  bind (vrf_mgf1 (n_2756) (alpha_2755)) (fun em_2758 =>
    let m_2759 : rsa_int_t :=
      os2ip (em_2758) in 
    bind (rsasp1 (sk_2754) (m_2759)) (fun s_2760 => i2osp (s_2760) (
        byte_size_v))).

Definition proof_to_hash (pi_string_2761 : byte_seq)  : byte_seq_result_t :=
  let hash_string_2762 : seq uint8 :=
    array_concat (suite_string_v) (array_concat (two_v) (pi_string_2761)) in 
  @Ok seq uint8 error_t (array_slice (sha256 (hash_string_2762)) (usize 0) (
      usize 32)).

Definition verify
  (pk_2763 : pk_t)
  (alpha_2764 : byte_seq)
  (pi_string_2765 : byte_seq)
  
  : byte_seq_result_t :=
  let '(n_2766, e_2767) :=
    (pk_2763) in 
  let s_2768 : rsa_int_t :=
    os2ip (pi_string_2765) in 
  bind (rsavp1 (pk_2763) (s_2768)) (fun m_2769 => bind (vrf_mgf1 (n_2766) (
        alpha_2764)) (fun em_prime_2770 => let m_prime_2771 : rsa_int_t :=
        os2ip (em_prime_2770) in 
      (if ((m_2769) =.? (m_prime_2771)):bool then (proof_to_hash (
            pi_string_2765)) else (@Err seq uint8 error_t (
            VerificationFailed))))).

