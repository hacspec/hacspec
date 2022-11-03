(** This file was automatically generated using Hacspec **)
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
  (n_2489 : rsa_int_t)
  (alpha_2490 : byte_seq)
  : byte_seq_result_t :=
  let mgf_salt1_2491 : seq uint8 :=
    i2osp (rsa_int_from_literal (@cast _ uint128 _ (byte_size_v))) (
      @repr WORDSIZE32 4) in 
  let mgf_salt2_2492 : seq uint8 :=
    i2osp (n_2489) (byte_size_v) in 
  let mgf_salt_2493 : seq uint8 :=
    seq_concat (mgf_salt1_2491) (mgf_salt2_2492) in 
  let mgf_string_2494 : seq uint8 :=
    seq_concat (seq_concat (array_concat (suite_string_v) (
          array_to_seq (one_v))) (mgf_salt_2493)) (alpha_2490) in 
  let mgf_2495 : seq uint8 :=
    mgf1 (mgf_string_2494) ((@cast _ uint32 _ (byte_size_v)) - (usize 1)) in 
  @Ok seq uint8 error_t (mgf_2495).

Definition prove (sk_2496 : sk_t) (alpha_2497 : byte_seq) : byte_seq_result_t :=
  let '(n_2498, d_2499) :=
    (sk_2496) in 
  let em_2500 : seq uint8 :=
    vrf_mgf1 (n_2498) (alpha_2497) in 
  let m_2501 : rsa_int_t :=
    os2ip (em_2500) in 
  let s_2502 : rsa_int_t :=
    rsasp1 (sk_2496) (m_2501) in 
  i2osp (s_2502) (byte_size_v).

Definition proof_to_hash (pi_string_2503 : byte_seq) : byte_seq_result_t :=
  let hash_string_2504 : seq uint8 :=
    array_concat (suite_string_v) (array_concat (two_v) (pi_string_2503)) in 
  @Ok seq uint8 error_t (array_slice (sha256 (hash_string_2504)) (usize 0) (
      usize 32)).

Definition verify
  (pk_2505 : pk_t)
  (alpha_2506 : byte_seq)
  (pi_string_2507 : byte_seq)
  : byte_seq_result_t :=
  let '(n_2508, e_2509) :=
    (pk_2505) in 
  let s_2510 : rsa_int_t :=
    os2ip (pi_string_2507) in 
  let m_2511 : rsa_int_t :=
    rsavp1 (pk_2505) (s_2510) in 
  let em_prime_2512 : seq uint8 :=
    vrf_mgf1 (n_2508) (alpha_2506) in 
  let m_prime_2513 : rsa_int_t :=
    os2ip (em_prime_2512) in 
  (if ((m_2511) =.? (m_prime_2513)):bool then (proof_to_hash (
        pi_string_2507)) else (@Err seq uint8 error_t (VerificationFailed))).

