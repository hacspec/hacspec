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
  (n_2571 : rsa_int_t)
  (alpha_2572 : byte_seq)
  : byte_seq_result_t :=
  bind (i2osp (rsa_int_from_literal (@cast _ uint128 _ (byte_size_v))) (
      @repr WORDSIZE32 4)) (fun mgf_salt1_2573 => bind (i2osp (n_2571) (
        byte_size_v)) (fun mgf_salt2_2574 => let mgf_salt_2575 : seq uint8 :=
        seq_concat (mgf_salt1_2573) (mgf_salt2_2574) in 
      let mgf_string_2576 : seq uint8 :=
        seq_concat (seq_concat (array_concat (suite_string_v) (
              array_to_seq (one_v))) (mgf_salt_2575)) (alpha_2572) in 
      bind (mgf1 (mgf_string_2576) ((@cast _ uint32 _ (byte_size_v)) - (
            usize 1))) (fun mgf_2577 => @Ok seq uint8 error_t (mgf_2577)))).

Definition prove (sk_2578 : sk_t) (alpha_2579 : byte_seq) : byte_seq_result_t :=
  let '(n_2580, d_2581) :=
    (sk_2578) in 
  bind (vrf_mgf1 (n_2580) (alpha_2579)) (fun em_2582 =>
    let m_2583 : rsa_int_t :=
      os2ip (em_2582) in 
    bind (rsasp1 (sk_2578) (m_2583)) (fun s_2584 => i2osp (s_2584) (
        byte_size_v))).

Definition proof_to_hash (pi_string_2585 : byte_seq) : byte_seq_result_t :=
  let hash_string_2586 : seq uint8 :=
    array_concat (suite_string_v) (array_concat (two_v) (pi_string_2585)) in 
  @Ok seq uint8 error_t (array_slice (sha256 (hash_string_2586)) (usize 0) (
      usize 32)).

Definition verify
  (pk_2587 : pk_t)
  (alpha_2588 : byte_seq)
  (pi_string_2589 : byte_seq)
  : byte_seq_result_t :=
  let '(n_2590, e_2591) :=
    (pk_2587) in 
  let s_2592 : rsa_int_t :=
    os2ip (pi_string_2589) in 
  bind (rsavp1 (pk_2587) (s_2592)) (fun m_2593 => bind (vrf_mgf1 (n_2590) (
        alpha_2588)) (fun em_prime_2594 => let m_prime_2595 : rsa_int_t :=
        os2ip (em_prime_2594) in 
      (if ((m_2593) =.? (m_prime_2595)):bool then (proof_to_hash (
            pi_string_2589)) else (@Err seq uint8 error_t (
            VerificationFailed))))).

