(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Hacspec_Edwards25519.

Require Import Hacspec_Sha512.

Require Import Hacspec_Edwards25519_Hash.

Inductive errorec_t :=
| FailedVerify : errorec_t
| MessageTooLarge : errorec_t
| InvalidProof : errorec_t
| InvalidPublicKey : errorec_t
| FailedDecompression : errorec_t
| FailedE2C : errorec_t.

Notation "'byte_seq_result_t'" := ((result byte_seq errorec_t)) : hacspec_scope.

Notation "'proof_result_t'" := ((result (ed_point_t '× scalar_t '× scalar_t
  ) errorec_t)) : hacspec_scope.

Notation "'ed_point_result_t'" := ((
  result ed_point_t errorec_t)) : hacspec_scope.

Definition large_mod_canvas_t := nseq (int8) (32).
Definition large_mod_t :=
  nat_mod 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff.

Definition arr_large_mod_t := nseq (uint64) (usize 4).

Definition q_v : arr_large_mod_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 9223372036854775807) : int64;
        secret (@repr WORDSIZE64 18446744073709551615) : int64;
        secret (@repr WORDSIZE64 18446744073709551615) : int64;
        secret (@repr WORDSIZE64 18446744073709551597) : int64
      ] in  l).

Definition c_len_v : uint_size :=
  usize 16.

Definition pt_len_v : uint_size :=
  usize 32.

Definition q_len_v : uint_size :=
  usize 32.

Definition int_byte_t := nseq (uint8) (usize 1).

Definition zero_v : int_byte_t :=
  array_from_list uint8 (let l := [secret (@repr WORDSIZE8 0) : int8] in  l).

Definition one_v : int_byte_t :=
  array_from_list uint8 (let l := [secret (@repr WORDSIZE8 1) : int8] in  l).

Definition two_v : int_byte_t :=
  array_from_list uint8 (let l := [secret (@repr WORDSIZE8 2) : int8] in  l).

Definition three_v : int_byte_t :=
  array_from_list uint8 (let l := [secret (@repr WORDSIZE8 3) : int8] in  l).

Definition four_v : int_byte_t :=
  array_from_list uint8 (let l := [secret (@repr WORDSIZE8 4) : int8] in  l).

Definition suite_string_v : int_byte_t :=
  four_v.

Definition dst_t := nseq (uint8) (usize 39).

Definition h2c_suite_id_string_v : dst_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 69) : int8;
        secret (@repr WORDSIZE8 67) : int8;
        secret (@repr WORDSIZE8 86) : int8;
        secret (@repr WORDSIZE8 82) : int8;
        secret (@repr WORDSIZE8 70) : int8;
        secret (@repr WORDSIZE8 95) : int8;
        secret (@repr WORDSIZE8 101) : int8;
        secret (@repr WORDSIZE8 100) : int8;
        secret (@repr WORDSIZE8 119) : int8;
        secret (@repr WORDSIZE8 97) : int8;
        secret (@repr WORDSIZE8 114) : int8;
        secret (@repr WORDSIZE8 100) : int8;
        secret (@repr WORDSIZE8 115) : int8;
        secret (@repr WORDSIZE8 50) : int8;
        secret (@repr WORDSIZE8 53) : int8;
        secret (@repr WORDSIZE8 53) : int8;
        secret (@repr WORDSIZE8 49) : int8;
        secret (@repr WORDSIZE8 57) : int8;
        secret (@repr WORDSIZE8 95) : int8;
        secret (@repr WORDSIZE8 88) : int8;
        secret (@repr WORDSIZE8 77) : int8;
        secret (@repr WORDSIZE8 68) : int8;
        secret (@repr WORDSIZE8 58) : int8;
        secret (@repr WORDSIZE8 83) : int8;
        secret (@repr WORDSIZE8 72) : int8;
        secret (@repr WORDSIZE8 65) : int8;
        secret (@repr WORDSIZE8 45) : int8;
        secret (@repr WORDSIZE8 53) : int8;
        secret (@repr WORDSIZE8 49) : int8;
        secret (@repr WORDSIZE8 50) : int8;
        secret (@repr WORDSIZE8 95) : int8;
        secret (@repr WORDSIZE8 69) : int8;
        secret (@repr WORDSIZE8 76) : int8;
        secret (@repr WORDSIZE8 76) : int8;
        secret (@repr WORDSIZE8 50) : int8;
        secret (@repr WORDSIZE8 95) : int8;
        secret (@repr WORDSIZE8 78) : int8;
        secret (@repr WORDSIZE8 85) : int8;
        secret (@repr WORDSIZE8 95) : int8
      ] in  l).

Definition ecvrf_encode_to_curve_try_and_increment
  (encode_to_curve_salt_2560 : byte_seq)
  (alpha_2561 : byte_seq)
  
  : ed_point_result_t :=
  let h_2562 : (option ed_point_t) :=
    @None ed_point_t in 
  let x_2563 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let '(h_2562, x_2563) :=
    foldi (usize 1) (usize 256) (fun ctr_2564 '(h_2562, x_2563) =>
      let '(h_2562, x_2563) :=
        if ((h_2562)) =.? (@None ed_point_t):bool then (
          let ctr_string_2565 : seq uint8 :=
            seq_slice (nat_mod_to_byte_seq_be (x_2563)) (usize 31) (usize 1) in 
          let hash_string_2566 : sha512_digest_t :=
            sha512 (seq_concat (seq_concat (seq_concat (seq_concat (
                      array_concat (suite_string_v) (array_to_seq (one_v))) (
                      encode_to_curve_salt_2560)) (alpha_2561)) (
                  ctr_string_2565)) (array_to_seq (zero_v))) in 
          let h_2562 :=
            decompress (array_from_slice (default : uint8) (32) (
                array_to_seq (hash_string_2566)) (usize 0) (usize 32)) in 
          let x_2563 :=
            (x_2563) +% (nat_mod_one ) in 
          (h_2562, x_2563)) else ((h_2562, x_2563)) in 
      (h_2562, x_2563))
    (h_2562, x_2563) in 
  bind (option_ok_or (h_2562) (FailedE2C)) (fun h_2567 =>
    @Ok ed_point_t errorec_t (point_mul_by_cofactor (h_2567))).

Definition ecvrf_encode_to_curve_h2c_suite
  (encode_to_curve_salt_2568 : byte_seq)
  (alpha_2569 : byte_seq)
  
  : ed_point_result_t :=
  let string_to_be_hashed_2570 : seq uint8 :=
    seq_concat (encode_to_curve_salt_2568) (alpha_2569) in 
  let dst_2571 : seq uint8 :=
    array_concat (h2c_suite_id_string_v) (array_to_seq (suite_string_v)) in 
  let h_2572 : (result (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) error_t) :=
    ed_encode_to_curve (string_to_be_hashed_2570) (dst_2571) in 
  bind (option_ok_or (result_ok (h_2572)) (FailedE2C)) (fun h_2573 =>
    @Ok ed_point_t errorec_t (h_2573)).

Definition ecvrf_nonce_generation
  (sk_2574 : secret_key_t)
  (h_string_2575 : byte_seq)
  
  : scalar_t :=
  let hashed_sk_string_2576 : sha512_digest_t :=
    sha512 (array_to_le_bytes (sk_2574)) in 
  let truncated_hashed_sk_string_2577 : seq uint8 :=
    array_slice (hashed_sk_string_2576) (usize 32) (usize 32) in 
  let k_string_2578 : sha512_digest_t :=
    sha512 (seq_concat (truncated_hashed_sk_string_2577) (h_string_2575)) in 
  let nonce_2579 : big_scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (k_string_2578)) : big_scalar_t in 
  let nonceseq_2580 : seq uint8 :=
    seq_slice (nat_mod_to_byte_seq_le (nonce_2579)) (usize 0) (usize 32) in 
  nat_mod_from_byte_seq_le (nonceseq_2580) : scalar_t.

Definition ecvrf_challenge_generation
  (p1_2581 : ed_point_t)
  (p2_2582 : ed_point_t)
  (p3_2583 : ed_point_t)
  (p4_2584 : ed_point_t)
  (p5_2585 : ed_point_t)
  
  : scalar_t :=
  let string_2586 : seq uint8 :=
    seq_concat (seq_concat (seq_concat (seq_concat (seq_concat (seq_concat (
                array_concat (suite_string_v) (array_to_seq (two_v))) (encode (
                  p1_2581))) (encode (p2_2582))) (encode (p3_2583))) (encode (
            p4_2584))) (encode (p5_2585))) (array_to_seq (zero_v)) in 
  let c_string_2587 : sha512_digest_t :=
    sha512 (string_2586) in 
  let truncated_c_string_2588 : seq uint8 :=
    seq_concat (array_slice (c_string_2587) (usize 0) (c_len_v)) (seq_new_ (
        default : uint8) (usize 16)) in 
  nat_mod_from_byte_seq_le (truncated_c_string_2588) : scalar_t.

Definition ecvrf_decode_proof (pi_2589 : byte_seq)  : proof_result_t :=
  let gamma_string_2590 : seq uint8 :=
    seq_slice (pi_2589) (usize 0) (pt_len_v) in 
  let c_string_2591 : seq uint8 :=
    seq_slice (pi_2589) (pt_len_v) (c_len_v) in 
  let s_string_2592 : seq uint8 :=
    seq_slice (pi_2589) ((pt_len_v) + (c_len_v)) (q_len_v) in 
  bind (option_ok_or (decompress (array_from_slice (default : uint8) (32) (
          gamma_string_2590) (usize 0) (usize 32))) (InvalidProof)) (
    fun gamma_2593 => let c_2594 : scalar_t :=
      nat_mod_from_byte_seq_le (seq_concat (c_string_2591) (seq_new_ (
            default : uint8) (usize 16))) : scalar_t in 
    let s_2595 : scalar_t :=
      nat_mod_from_byte_seq_le ((s_string_2592)) : scalar_t in 
    let s_test_2596 : large_mod_t :=
      nat_mod_from_byte_seq_le (s_string_2592) : large_mod_t in 
    let q_2597 : large_mod_t :=
      nat_mod_from_byte_seq_be (array_to_be_bytes (q_v)) : large_mod_t in 
    (if ((s_test_2596) >=.? (q_2597)):bool then (@Err (
          ed_point_t '×
          scalar_t '×
          scalar_t
        ) errorec_t (InvalidProof)) else (@Ok (
          ed_point_t '×
          scalar_t '×
          scalar_t
        ) errorec_t ((gamma_2593, c_2594, s_2595))))).

Definition ecvrf_validate_key
  (y_2598 : public_key_t)
  
  : (result unit errorec_t) :=
  bind (option_ok_or (decompress (y_2598)) (InvalidPublicKey)) (fun y_2599 =>
    let y_prime_2600 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul_by_cofactor (y_2599) in 
    (if ((y_prime_2600) =.? (point_identity )):bool then (@Err unit errorec_t (
          InvalidPublicKey)) else (@Ok unit errorec_t (tt)))).

Definition ecvrf_prove
  (sk_2601 : secret_key_t)
  (alpha_2602 : byte_seq)
  
  : byte_seq_result_t :=
  bind (option_ok_or (decompress (base_v)) (FailedDecompression)) (fun b_2603 =>
    let '(x_2604, _) :=
      secret_expand (sk_2601) in 
    let x_2605 : scalar_t :=
      nat_mod_from_byte_seq_le (array_to_seq (x_2604)) : scalar_t in 
    let y_2606 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul (x_2605) (b_2603) in 
    let pk_2607 : compressed_ed_point_t :=
      compress (y_2606) in 
    let encode_to_curve_salt_2608 : seq uint8 :=
      array_slice (pk_2607) (usize 0) (usize 32) in 
    bind (ecvrf_encode_to_curve_h2c_suite (encode_to_curve_salt_2608) (
        alpha_2602)) (fun h_2609 => let h_string_2610 : seq uint8 :=
        encode (h_2609) in 
      let gamma_2611 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (x_2605) (h_2609) in 
      let k_2612 : scalar_t :=
        ecvrf_nonce_generation (sk_2601) (h_string_2610) in 
      let u_2613 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (k_2612) (b_2603) in 
      let v_2614 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (k_2612) (h_2609) in 
      let c_2615 : scalar_t :=
        ecvrf_challenge_generation (y_2606) (h_2609) (gamma_2611) (u_2613) (
          v_2614) in 
      let s_2616 : scalar_t :=
        (k_2612) +% ((c_2615) *% (x_2605)) in 
      @Ok byte_seq errorec_t (seq_slice (seq_concat (seq_concat (encode (
                gamma_2611)) (seq_slice (nat_mod_to_byte_seq_le (c_2615)) (
                usize 0) (c_len_v))) (seq_slice (nat_mod_to_byte_seq_le (
                s_2616)) (usize 0) (q_len_v))) (usize 0) (((c_len_v) + (
              q_len_v)) + (pt_len_v))))).

Definition ecvrf_proof_to_hash (pi_2617 : byte_seq)  : byte_seq_result_t :=
  bind (ecvrf_decode_proof (pi_2617)) (fun '(gamma_2618, _, _) =>
    @Ok byte_seq errorec_t (array_slice (sha512 (seq_concat (seq_concat (
              array_concat (suite_string_v) (array_to_seq (three_v))) (encode (
                point_mul_by_cofactor (gamma_2618)))) (
            array_to_seq (zero_v)))) (usize 0) (usize 64))).

Definition ecvrf_verify
  (pk_2619 : public_key_t)
  (alpha_2620 : byte_seq)
  (pi_2621 : byte_seq)
  (validate_key_2622 : bool)
  
  : byte_seq_result_t :=
  bind (option_ok_or (decompress (base_v)) (FailedDecompression)) (fun b_2623 =>
    bind (option_ok_or (decompress (pk_2619)) (InvalidPublicKey)) (fun y_2624 =>
      ifbnd validate_key_2622 : bool
      thenbnd (bind (ecvrf_validate_key (pk_2619)) (fun _ =>
          @Ok unit errorec_t (tt)))
      else (tt) >> (fun 'tt =>
      bind (ecvrf_decode_proof (pi_2621)) (fun '(gamma_2625, c_2626, s_2627) =>
        let encode_to_curve_salt_2628 : seq uint8 :=
          array_slice (pk_2619) (usize 0) (usize 32) in 
        bind (ecvrf_encode_to_curve_h2c_suite (encode_to_curve_salt_2628) (
            alpha_2620)) (fun h_2629 => let u_2630 : (
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t
            ) :=
            point_add (point_mul (s_2627) (b_2623)) (point_neg (point_mul (
                  c_2626) (y_2624))) in 
          let v_2631 : (
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t
            ) :=
            point_add (point_mul (s_2627) (h_2629)) (point_neg (point_mul (
                  c_2626) (gamma_2625))) in 
          let c_prime_2632 : scalar_t :=
            ecvrf_challenge_generation (y_2624) (h_2629) (gamma_2625) (u_2630) (
              v_2631) in 
          (if ((c_2626) =.? (c_prime_2632)):bool then (ecvrf_proof_to_hash (
                pi_2621)) else (@Err byte_seq errorec_t (FailedVerify)))))))).

