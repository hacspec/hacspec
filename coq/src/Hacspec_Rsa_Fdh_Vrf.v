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
  (n_2547 : rsa_int_t)
  (alpha_2548 : byte_seq)
  : byte_seq_result_t :=
  let mgf_salt1_2549 : seq uint8 :=
    i2osp (rsa_int_from_literal (@cast _ uint128 _ (byte_size_v))) (
      @repr WORDSIZE32 4) in 
  let mgf_salt2_2550 : seq uint8 :=
    i2osp (n_2547) (byte_size_v) in 
  let mgf_salt_2551 : seq uint8 :=
    seq_concat (mgf_salt1_2549) (mgf_salt2_2550) in 
  let mgf_string_2552 : seq uint8 :=
    seq_concat (seq_concat (array_concat (suite_string_v) (
          array_to_seq (one_v))) (mgf_salt_2551)) (alpha_2548) in 
  let mgf_2553 : seq uint8 :=
    mgf1 (mgf_string_2552) ((@cast _ uint32 _ (byte_size_v)) - (usize 1)) in 
  @Ok seq uint8 error_t (mgf_2553).

Definition prove (sk_2554 : sk_t) (alpha_2555 : byte_seq) : byte_seq_result_t :=
  let '(n_2556, d_2557) :=
    (sk_2554) in 
  let em_2558 : seq uint8 :=
    vrf_mgf1 (n_2556) (alpha_2555) in 
  let m_2559 : rsa_int_t :=
    os2ip (em_2558) in 
  let s_2560 : rsa_int_t :=
    rsasp1 (sk_2554) (m_2559) in 
  i2osp (s_2560) (byte_size_v).

Definition proof_to_hash (pi_string_2561 : byte_seq) : byte_seq_result_t :=
  let hash_string_2562 : seq uint8 :=
    array_concat (suite_string_v) (array_concat (two_v) (pi_string_2561)) in 
  @Ok seq uint8 error_t (array_slice (sha256 (hash_string_2562)) (usize 0) (
      usize 32)).

Definition verify
  (pk_2563 : pk_t)
  (alpha_2564 : byte_seq)
  (pi_string_2565 : byte_seq)
  : byte_seq_result_t :=
  let '(n_2566, e_2567) :=
    (pk_2563) in 
  let s_2568 : rsa_int_t :=
    os2ip (pi_string_2565) in 
  let m_2569 : rsa_int_t :=
    rsavp1 (pk_2563) (s_2568) in 
  let em_prime_2570 : seq uint8 :=
    vrf_mgf1 (n_2566) (alpha_2564) in 
  let m_prime_2571 : rsa_int_t :=
    os2ip (em_prime_2570) in 
  (if ((m_2569) =.? (m_prime_2571)):bool then (proof_to_hash (
        pi_string_2565)) else (@Err seq uint8 error_t (VerificationFailed))).

