(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp Require Import ssrZ word.
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


Require Import Hacspec_Sha512.

Require Import Hacspec_Edwards25519.


Notation "'scalar_from_hash_inp'" :=(
  sha512_digest_t : choice_type) (in custom pack_type at level 2).
Notation "'scalar_from_hash_inp'" :=(
  sha512_digest_t : ChoiceEquality) (at level 2).
Notation "'scalar_from_hash_out'" :=(
  scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'scalar_from_hash_out'" :=(scalar_t : ChoiceEquality) (at level 2).
Definition SCALAR_FROM_HASH : nat :=
  2520.
Program Definition scalar_from_hash (h_2518 : sha512_digest_t)
  : both (fset.fset0) [interface] (scalar_t) :=
  ((letb s_2519 : big_scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 h_2518)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        nat_mod_from_byte_seq_le (seq_slice (nat_mod_to_byte_seq_le (
              lift_to_both0 s_2519)) (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 32))))
      ) : both (fset.fset0) [interface] (scalar_t)).
Fail Next Obligation.


Notation "'sign_inp'" :=(
  secret_key_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sign_inp'" :=(
  secret_key_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'sign_out'" :=(
  signature_t : choice_type) (in custom pack_type at level 2).
Notation "'sign_out'" :=(signature_t : ChoiceEquality) (at level 2).
Definition SIGN : nat :=
  2534.
Program Definition sign (sk_2521 : secret_key_t) (msg_2527 : byte_seq)
  : both (fset.fset0) [interface] (signature_t) :=
  ((letb '(a_2522, prefix_2523) : (serialized_scalar_t '× serialized_scalar_t
        ) :=
        secret_expand (lift_to_both0 sk_2521) in
      letb a_2524 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 a_2522)) in
      letb b_2525 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letb a_p_2526 : compressed_ed_point_t :=
        compress (point_mul (lift_to_both0 a_2524) (lift_to_both0 b_2525)) in
      letb r_2528 : scalar_t :=
        scalar_from_hash (sha512 (array_concat (lift_to_both0 prefix_2523) (
              lift_to_both0 msg_2527))) in
      letb r_p_2529 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 r_2528) (lift_to_both0 b_2525) in
      letb r_s_2530 : compressed_ed_point_t :=
        compress (lift_to_both0 r_p_2529) in
      letb h_2531 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (
                lift_to_both0 r_s_2530) (
                array_to_seq (lift_to_both0 a_p_2526))) (
              lift_to_both0 msg_2527))) in
      letb s_2532 : scalar_t :=
        (lift_to_both0 r_2528) +% ((lift_to_both0 h_2531) *% (
            lift_to_both0 a_2524)) in
      letb s_bytes_2533 : seq uint8 :=
        seq_slice (nat_mod_to_byte_seq_le (lift_to_both0 s_2532)) (
          lift_to_both0 (usize 0)) (lift_to_both0 (usize 32)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_update (
          array_update (array_new_ (default : uint8) (64)) (lift_to_both0 (
              usize 0)) (array_to_seq (lift_to_both0 r_s_2530))) (
          lift_to_both0 (usize 32)) (lift_to_both0 s_bytes_2533))
      ) : both (fset.fset0) [interface] (signature_t)).
Fail Next Obligation.


Notation "'zcash_verify_inp'" :=(
  public_key_t '× signature_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'zcash_verify_inp'" :=(
  public_key_t '× signature_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'zcash_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Notation "'zcash_verify_out'" :=(verify_result_t : ChoiceEquality) (at level 2).
Definition ZCASH_VERIFY : nat :=
  2548.
Program Definition zcash_verify (pk_2536 : public_key_t) (
    signature_2538 : signature_t) (msg_2543 : byte_seq)
  : both (fset.fset0) [interface] (verify_result_t) :=
  ((letb b_2535 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress_non_canonical (lift_to_both0 base_v)) in
      letbnd(_) a_2537 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress_non_canonical (lift_to_both0 pk_2536)) (
          InvalidPublickey) in
      letb r_bytes_2539 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2538)) (lift_to_both0 (
            usize 0)) (lift_to_both0 (usize 32)) in
      letb s_bytes_2540 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2538)) (lift_to_both0 (
            usize 32)) (lift_to_both0 (usize 32)) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if negb (check_canonical_scalar (
            lift_to_both0 s_bytes_2540)) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
              _) _ : unit_ChoiceEquality :=
            @Err unit_ChoiceEquality error_t (InvalidS) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok unit_ChoiceEquality error_t (lift_to_both0 (
              (tt : unit_ChoiceEquality))))
         in
      letbnd(_) r_2541 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress_non_canonical (lift_to_both0 r_bytes_2539)) (
          InvalidR) in
      letb s_2542 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 s_bytes_2540)) in
      letb k_2544 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (
                lift_to_both0 r_bytes_2539) (lift_to_both0 pk_2536)) (
              lift_to_both0 msg_2543))) in
      letb sb_2545 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (lift_to_both0 s_2542) (
            lift_to_both0 b_2535)) in
      letb rc_2546 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (lift_to_both0 r_2541) in
      letb ka_2547 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (lift_to_both0 k_2544) (
            lift_to_both0 a_2537)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (point_eq (lift_to_both0 sb_2545) (
            point_add (lift_to_both0 rc_2546) (lift_to_both0 ka_2547)))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (fset.fset0) [interface] (verify_result_t)).
Fail Next Obligation.


Notation "'ietf_cofactored_verify_inp'" :=(
  public_key_t '× signature_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactored_verify_inp'" :=(
  public_key_t '× signature_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'ietf_cofactored_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactored_verify_out'" :=(
  verify_result_t : ChoiceEquality) (at level 2).
Definition IETF_COFACTORED_VERIFY : nat :=
  2562.
Program Definition ietf_cofactored_verify (pk_2550 : public_key_t) (
    signature_2552 : signature_t) (msg_2557 : byte_seq)
  : both (fset.fset0) [interface] (verify_result_t) :=
  ((letb b_2549 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letbnd(_) a_2551 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 pk_2550)) (InvalidPublickey) in
      letb r_bytes_2553 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2552)) (lift_to_both0 (
            usize 0)) (lift_to_both0 (usize 32)) in
      letb s_bytes_2554 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2552)) (lift_to_both0 (
            usize 32)) (lift_to_both0 (usize 32)) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if negb (check_canonical_scalar (
            lift_to_both0 s_bytes_2554)) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
              _) _ : unit_ChoiceEquality :=
            @Err unit_ChoiceEquality error_t (InvalidS) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok unit_ChoiceEquality error_t (lift_to_both0 (
              (tt : unit_ChoiceEquality))))
         in
      letbnd(_) r_2555 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 r_bytes_2553)) (InvalidR) in
      letb s_2556 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 s_bytes_2554)) in
      letb k_2558 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (
                lift_to_both0 r_bytes_2553) (lift_to_both0 pk_2550)) (
              lift_to_both0 msg_2557))) in
      letb sb_2559 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (lift_to_both0 s_2556) (
            lift_to_both0 b_2549)) in
      letb rc_2560 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (lift_to_both0 r_2555) in
      letb ka_2561 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (lift_to_both0 k_2558) (
            lift_to_both0 a_2551)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (point_eq (lift_to_both0 sb_2559) (
            point_add (lift_to_both0 rc_2560) (lift_to_both0 ka_2561)))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (fset.fset0) [interface] (verify_result_t)).
Fail Next Obligation.


Notation "'ietf_cofactorless_verify_inp'" :=(
  public_key_t '× signature_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactorless_verify_inp'" :=(
  public_key_t '× signature_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'ietf_cofactorless_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactorless_verify_out'" :=(
  verify_result_t : ChoiceEquality) (at level 2).
Definition IETF_COFACTORLESS_VERIFY : nat :=
  2575.
Program Definition ietf_cofactorless_verify (pk_2564 : public_key_t) (
    signature_2566 : signature_t) (msg_2571 : byte_seq)
  : both (fset.fset0) [interface] (verify_result_t) :=
  ((letb b_2563 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letbnd(_) a_2565 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 pk_2564)) (InvalidPublickey) in
      letb r_bytes_2567 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2566)) (lift_to_both0 (
            usize 0)) (lift_to_both0 (usize 32)) in
      letb s_bytes_2568 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2566)) (lift_to_both0 (
            usize 32)) (lift_to_both0 (usize 32)) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if negb (check_canonical_scalar (
            lift_to_both0 s_bytes_2568)) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
              _) _ : unit_ChoiceEquality :=
            @Err unit_ChoiceEquality error_t (InvalidS) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok unit_ChoiceEquality error_t (lift_to_both0 (
              (tt : unit_ChoiceEquality))))
         in
      letbnd(_) r_2569 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 r_bytes_2567)) (InvalidR) in
      letb s_2570 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 s_bytes_2568)) in
      letb k_2572 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (
                lift_to_both0 r_bytes_2567) (lift_to_both0 pk_2564)) (
              lift_to_both0 msg_2571))) in
      letb sb_2573 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 s_2570) (lift_to_both0 b_2563) in
      letb ka_2574 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 k_2572) (lift_to_both0 a_2565) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (point_eq (lift_to_both0 sb_2573) (
            point_add (lift_to_both0 r_2569) (lift_to_both0 ka_2574)))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (fset.fset0) [interface] (verify_result_t)).
Fail Next Obligation.


Notation "'is_identity_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'is_identity_inp'" :=(ed_point_t : ChoiceEquality) (at level 2).
Notation "'is_identity_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'is_identity_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition IS_IDENTITY : nat :=
  2577.
Program Definition is_identity (p_2576 : ed_point_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (point_eq (
          lift_to_both0 p_2576) (point_identity ))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'alg2_verify_inp'" :=(
  public_key_t '× signature_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'alg2_verify_inp'" :=(
  public_key_t '× signature_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'alg2_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Notation "'alg2_verify_out'" :=(verify_result_t : ChoiceEquality) (at level 2).
Definition ALG2_VERIFY : nat :=
  2591.
Program Definition alg2_verify (pk_2579 : public_key_t) (
    signature_2581 : signature_t) (msg_2586 : byte_seq)
  : both (fset.fset0) [interface] (verify_result_t) :=
  ((letb b_2578 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letbnd(_) a_2580 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 pk_2579)) (InvalidPublickey) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if is_identity (point_mul_by_cofactor (
            lift_to_both0 a_2580)) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
              _) _ : unit_ChoiceEquality :=
            @Err unit_ChoiceEquality error_t (SmallOrderPoint) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok unit_ChoiceEquality error_t (lift_to_both0 (
              (tt : unit_ChoiceEquality))))
         in
      letb r_bytes_2582 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2581)) (lift_to_both0 (
            usize 0)) (lift_to_both0 (usize 32)) in
      letb s_bytes_2583 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2581)) (lift_to_both0 (
            usize 32)) (lift_to_both0 (usize 32)) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if negb (check_canonical_scalar (
            lift_to_both0 s_bytes_2583)) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
              _) _ : unit_ChoiceEquality :=
            @Err unit_ChoiceEquality error_t (InvalidS) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok unit_ChoiceEquality error_t (lift_to_both0 (
              (tt : unit_ChoiceEquality))))
         in
      letbnd(_) r_2584 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 r_bytes_2582)) (InvalidR) in
      letb s_2585 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 s_bytes_2583)) in
      letb k_2587 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (
                lift_to_both0 r_bytes_2582) (lift_to_both0 pk_2579)) (
              lift_to_both0 msg_2586))) in
      letb sb_2588 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (lift_to_both0 s_2585) (
            lift_to_both0 b_2578)) in
      letb rc_2589 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (lift_to_both0 r_2584) in
      letb ka_2590 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (lift_to_both0 k_2587) (
            lift_to_both0 a_2580)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (point_eq (lift_to_both0 sb_2588) (
            point_add (lift_to_both0 rc_2589) (lift_to_both0 ka_2590)))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (fset.fset0) [interface] (verify_result_t)).
Fail Next Obligation.

Definition batch_entry_t : ChoiceEquality :=
  (public_key_t '× byte_seq '× signature_t).
Definition BatchEntry (x : (public_key_t '× byte_seq '× signature_t
    )) : batch_entry_t :=
   x.

Definition a_sum_2594_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2595%nat).
Definition s_sum_2592_loc : ChoiceEqualityLocation :=
  (scalar_t ; 2596%nat).
Definition r_sum_2593_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2597%nat).
Notation "'zcash_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'zcash_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'zcash_batch_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Notation "'zcash_batch_verify_out'" :=(
  verify_result_t : ChoiceEquality) (at level 2).
Definition ZCASH_BATCH_VERIFY : nat :=
  2615.
Program Definition zcash_batch_verify (entries_2599 : seq batch_entry_t) (
    entropy_2598 : byte_seq)
  : both (CEfset (
      [s_sum_2592_loc ; r_sum_2593_loc ; a_sum_2594_loc])) [interface] (
    verify_result_t) :=
  ((letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if (seq_len (lift_to_both0 entropy_2598)) <.? ((lift_to_both0 (
              usize 16)) .* (seq_len (
              lift_to_both0 entries_2599))) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := CEfset (
            [s_sum_2592_loc ; r_sum_2593_loc ; a_sum_2594_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
              _) _ : unit_ChoiceEquality :=
            @Err unit_ChoiceEquality error_t (NotEnoughRandomness) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok unit_ChoiceEquality error_t (lift_to_both0 (
              (tt : unit_ChoiceEquality))))
         in
      letbm s_sum_2592 : scalar_t loc( s_sum_2592_loc ) := nat_mod_zero  in
      letbm r_sum_2593 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( r_sum_2593_loc ) :=
        point_identity  in
      letbm a_sum_2594 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( a_sum_2594_loc ) :=
        point_identity  in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) '(
          s_sum_2592,
          r_sum_2593,
          a_sum_2594
        ) :=
        foldi_bind_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 entries_2599)) prod_ce(
            s_sum_2592,
            r_sum_2593,
            a_sum_2594
          ) (L := (CEfset (
                [s_sum_2592_loc ; r_sum_2593_loc ; a_sum_2594_loc]))) (
            I := [interface]) (fun i_2600 '(s_sum_2592, r_sum_2593, a_sum_2594
            ) =>
            letb BatchEntry ((pk_2601, msg_2602, signature_2603
                )) : batch_entry_t :=
              (seq_index (entries_2599) (lift_to_both0 i_2600)) in
            letbnd(_) a_2604 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress_non_canonical (lift_to_both0 pk_2601)) (
                InvalidPublickey) in
            letb r_bytes_2605 : compressed_ed_point_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2603)) (lift_to_both0 (
                  usize 0)) (lift_to_both0 (usize 32)) in
            letb s_bytes_2606 : serialized_scalar_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2603)) (lift_to_both0 (
                  usize 32)) (lift_to_both0 (usize 32)) in
            letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
              if negb (check_canonical_scalar (
                  lift_to_both0 s_bytes_2606)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [s_sum_2592_loc ; r_sum_2593_loc ; a_sum_2594_loc])) (
                L2 := CEfset (
                  [s_sum_2592_loc ; r_sum_2593_loc ; a_sum_2594_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbnd(_) _ : unit_ChoiceEquality :=
                  @Err unit_ChoiceEquality error_t (InvalidS) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                      (tt : unit_ChoiceEquality))))
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                    (tt : unit_ChoiceEquality))))
               in
            letbnd(_) r_2607 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress_non_canonical (
                  lift_to_both0 r_bytes_2605)) (InvalidR) in
            letb s_2608 : scalar_t :=
              nat_mod_from_byte_seq_le (
                array_to_seq (lift_to_both0 s_bytes_2606)) in
            letb c_2609 : scalar_t :=
              scalar_from_hash (sha512 (seq_concat (array_concat (
                      lift_to_both0 r_bytes_2605) (
                      array_to_seq (lift_to_both0 pk_2601))) (
                    lift_to_both0 msg_2602))) in
            letb z_2610 : seq uint8 :=
              seq_slice (lift_to_both0 entropy_2598) ((lift_to_both0 (
                    usize 16)) .* (lift_to_both0 i_2600)) (lift_to_both0 (
                  usize 16)) in
            letb z_2611 : scalar_t :=
              nat_mod_from_byte_seq_le (seq_concat (lift_to_both0 z_2610) (
                  seq_new_ (default : uint8) (lift_to_both0 (usize 16)))) in
            letbm s_sum_2592 loc( s_sum_2592_loc ) :=
              (lift_to_both0 s_sum_2592) +% ((lift_to_both0 s_2608) *% (
                  lift_to_both0 z_2611)) in
            letbm r_sum_2593 loc( r_sum_2593_loc ) :=
              point_add (lift_to_both0 r_sum_2593) (point_mul (
                  lift_to_both0 z_2611) (lift_to_both0 r_2607)) in
            letbm a_sum_2594 loc( a_sum_2594_loc ) :=
              point_add (lift_to_both0 a_sum_2594) (point_mul ((
                    lift_to_both0 z_2611) *% (lift_to_both0 c_2609)) (
                  lift_to_both0 a_2604)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (
                scalar_t '×
                (
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t
                ) '×
                (
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t
                )
              ) error_t (prod_b(
                  lift_to_both0 s_sum_2592,
                  lift_to_both0 r_sum_2593,
                  lift_to_both0 a_sum_2594
                )))
            ) in
      letb b_2612 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letb sb_2613 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 s_sum_2592) (lift_to_both0 b_2612) in
      letb check_2614 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_add (point_neg (lift_to_both0 sb_2613)) (
            point_add (lift_to_both0 r_sum_2593) (lift_to_both0 a_sum_2594))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (is_identity (lift_to_both0 check_2614))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (CEfset (
        [s_sum_2592_loc ; r_sum_2593_loc ; a_sum_2594_loc])) [interface] (
      verify_result_t)).
Fail Next Obligation.

Definition s_sum_2616_loc : ChoiceEqualityLocation :=
  (scalar_t ; 2619%nat).
Definition a_sum_2618_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2620%nat).
Definition r_sum_2617_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2621%nat).
Notation "'ietf_cofactored_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactored_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'ietf_cofactored_batch_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactored_batch_verify_out'" :=(
  verify_result_t : ChoiceEquality) (at level 2).
Definition IETF_COFACTORED_BATCH_VERIFY : nat :=
  2639.
Program Definition ietf_cofactored_batch_verify (
    entries_2623 : seq batch_entry_t) (entropy_2622 : byte_seq)
  : both (CEfset (
      [s_sum_2616_loc ; r_sum_2617_loc ; a_sum_2618_loc])) [interface] (
    verify_result_t) :=
  ((letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if (seq_len (lift_to_both0 entropy_2622)) <.? ((lift_to_both0 (
              usize 16)) .* (seq_len (
              lift_to_both0 entries_2623))) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := CEfset (
            [s_sum_2616_loc ; r_sum_2617_loc ; a_sum_2618_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
              _) _ : unit_ChoiceEquality :=
            @Err unit_ChoiceEquality error_t (NotEnoughRandomness) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok unit_ChoiceEquality error_t (lift_to_both0 (
              (tt : unit_ChoiceEquality))))
         in
      letbm s_sum_2616 : scalar_t loc( s_sum_2616_loc ) := nat_mod_zero  in
      letbm r_sum_2617 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( r_sum_2617_loc ) :=
        point_identity  in
      letbm a_sum_2618 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( a_sum_2618_loc ) :=
        point_identity  in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) '(
          s_sum_2616,
          r_sum_2617,
          a_sum_2618
        ) :=
        foldi_bind_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 entries_2623)) prod_ce(
            s_sum_2616,
            r_sum_2617,
            a_sum_2618
          ) (L := (CEfset (
                [s_sum_2616_loc ; r_sum_2617_loc ; a_sum_2618_loc]))) (
            I := [interface]) (fun i_2624 '(s_sum_2616, r_sum_2617, a_sum_2618
            ) =>
            letb BatchEntry ((pk_2625, msg_2626, signature_2627
                )) : batch_entry_t :=
              (seq_index (entries_2623) (lift_to_both0 i_2624)) in
            letbnd(_) a_2628 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 pk_2625)) (
                InvalidPublickey) in
            letb r_bytes_2629 : compressed_ed_point_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2627)) (lift_to_both0 (
                  usize 0)) (lift_to_both0 (usize 32)) in
            letb s_bytes_2630 : serialized_scalar_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2627)) (lift_to_both0 (
                  usize 32)) (lift_to_both0 (usize 32)) in
            letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
              if negb (check_canonical_scalar (
                  lift_to_both0 s_bytes_2630)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [s_sum_2616_loc ; r_sum_2617_loc ; a_sum_2618_loc])) (
                L2 := CEfset (
                  [s_sum_2616_loc ; r_sum_2617_loc ; a_sum_2618_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbnd(_) _ : unit_ChoiceEquality :=
                  @Err unit_ChoiceEquality error_t (InvalidS) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                      (tt : unit_ChoiceEquality))))
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                    (tt : unit_ChoiceEquality))))
               in
            letbnd(_) r_2631 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 r_bytes_2629)) (
                InvalidR) in
            letb s_2632 : scalar_t :=
              nat_mod_from_byte_seq_le (
                array_to_seq (lift_to_both0 s_bytes_2630)) in
            letb c_2633 : scalar_t :=
              scalar_from_hash (sha512 (seq_concat (array_concat (
                      lift_to_both0 r_bytes_2629) (
                      array_to_seq (lift_to_both0 pk_2625))) (
                    lift_to_both0 msg_2626))) in
            letb z_2634 : seq uint8 :=
              seq_slice (lift_to_both0 entropy_2622) ((lift_to_both0 (
                    usize 16)) .* (lift_to_both0 i_2624)) (lift_to_both0 (
                  usize 16)) in
            letb z_2635 : scalar_t :=
              nat_mod_from_byte_seq_le (seq_concat (lift_to_both0 z_2634) (
                  seq_new_ (default : uint8) (lift_to_both0 (usize 16)))) in
            letbm s_sum_2616 loc( s_sum_2616_loc ) :=
              (lift_to_both0 s_sum_2616) +% ((lift_to_both0 s_2632) *% (
                  lift_to_both0 z_2635)) in
            letbm r_sum_2617 loc( r_sum_2617_loc ) :=
              point_add (lift_to_both0 r_sum_2617) (point_mul (
                  lift_to_both0 z_2635) (lift_to_both0 r_2631)) in
            letbm a_sum_2618 loc( a_sum_2618_loc ) :=
              point_add (lift_to_both0 a_sum_2618) (point_mul ((
                    lift_to_both0 z_2635) *% (lift_to_both0 c_2633)) (
                  lift_to_both0 a_2628)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (
                scalar_t '×
                (
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t
                ) '×
                (
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t
                )
              ) error_t (prod_b(
                  lift_to_both0 s_sum_2616,
                  lift_to_both0 r_sum_2617,
                  lift_to_both0 a_sum_2618
                )))
            ) in
      letb b_2636 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letb sb_2637 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 s_sum_2616) (lift_to_both0 b_2636) in
      letb check_2638 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_add (point_neg (lift_to_both0 sb_2637)) (
            point_add (lift_to_both0 r_sum_2617) (lift_to_both0 a_sum_2618))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (is_identity (lift_to_both0 check_2638))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (CEfset (
        [s_sum_2616_loc ; r_sum_2617_loc ; a_sum_2618_loc])) [interface] (
      verify_result_t)).
Fail Next Obligation.

Definition r_sum_2641_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2643%nat).
Definition s_sum_2640_loc : ChoiceEqualityLocation :=
  (scalar_t ; 2644%nat).
Definition a_sum_2642_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2645%nat).
Notation "'ietf_cofactorless_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactorless_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'ietf_cofactorless_batch_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactorless_batch_verify_out'" :=(
  verify_result_t : ChoiceEquality) (at level 2).
Definition IETF_COFACTORLESS_BATCH_VERIFY : nat :=
  2663.
Program Definition ietf_cofactorless_batch_verify (
    entries_2647 : seq batch_entry_t) (entropy_2646 : byte_seq)
  : both (CEfset (
      [s_sum_2640_loc ; r_sum_2641_loc ; a_sum_2642_loc])) [interface] (
    verify_result_t) :=
  ((letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if (seq_len (lift_to_both0 entropy_2646)) <.? ((lift_to_both0 (
              usize 16)) .* (seq_len (
              lift_to_both0 entries_2647))) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := CEfset (
            [s_sum_2640_loc ; r_sum_2641_loc ; a_sum_2642_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
              _) _ : unit_ChoiceEquality :=
            @Err unit_ChoiceEquality error_t (NotEnoughRandomness) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok unit_ChoiceEquality error_t (lift_to_both0 (
              (tt : unit_ChoiceEquality))))
         in
      letbm s_sum_2640 : scalar_t loc( s_sum_2640_loc ) := nat_mod_zero  in
      letbm r_sum_2641 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( r_sum_2641_loc ) :=
        point_identity  in
      letbm a_sum_2642 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( a_sum_2642_loc ) :=
        point_identity  in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) '(
          s_sum_2640,
          r_sum_2641,
          a_sum_2642
        ) :=
        foldi_bind_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 entries_2647)) prod_ce(
            s_sum_2640,
            r_sum_2641,
            a_sum_2642
          ) (L := (CEfset (
                [s_sum_2640_loc ; r_sum_2641_loc ; a_sum_2642_loc]))) (
            I := [interface]) (fun i_2648 '(s_sum_2640, r_sum_2641, a_sum_2642
            ) =>
            letb BatchEntry ((pk_2649, msg_2650, signature_2651
                )) : batch_entry_t :=
              (seq_index (entries_2647) (lift_to_both0 i_2648)) in
            letbnd(_) a_2652 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 pk_2649)) (
                InvalidPublickey) in
            letb r_bytes_2653 : compressed_ed_point_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2651)) (lift_to_both0 (
                  usize 0)) (lift_to_both0 (usize 32)) in
            letb s_bytes_2654 : serialized_scalar_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2651)) (lift_to_both0 (
                  usize 32)) (lift_to_both0 (usize 32)) in
            letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
              if negb (check_canonical_scalar (
                  lift_to_both0 s_bytes_2654)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [s_sum_2640_loc ; r_sum_2641_loc ; a_sum_2642_loc])) (
                L2 := CEfset (
                  [s_sum_2640_loc ; r_sum_2641_loc ; a_sum_2642_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbnd(_) _ : unit_ChoiceEquality :=
                  @Err unit_ChoiceEquality error_t (InvalidS) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                      (tt : unit_ChoiceEquality))))
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                    (tt : unit_ChoiceEquality))))
               in
            letbnd(_) r_2655 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 r_bytes_2653)) (
                InvalidR) in
            letb s_2656 : scalar_t :=
              nat_mod_from_byte_seq_le (
                array_to_seq (lift_to_both0 s_bytes_2654)) in
            letb c_2657 : scalar_t :=
              scalar_from_hash (sha512 (seq_concat (array_concat (
                      lift_to_both0 r_bytes_2653) (
                      array_to_seq (lift_to_both0 pk_2649))) (
                    lift_to_both0 msg_2650))) in
            letb z_2658 : seq uint8 :=
              seq_slice (lift_to_both0 entropy_2646) ((lift_to_both0 (
                    usize 16)) .* (lift_to_both0 i_2648)) (lift_to_both0 (
                  usize 16)) in
            letb z_2659 : scalar_t :=
              nat_mod_from_byte_seq_le (seq_concat (lift_to_both0 z_2658) (
                  seq_new_ (default : uint8) (lift_to_both0 (usize 16)))) in
            letbm s_sum_2640 loc( s_sum_2640_loc ) :=
              (lift_to_both0 s_sum_2640) +% ((lift_to_both0 s_2656) *% (
                  lift_to_both0 z_2659)) in
            letbm r_sum_2641 loc( r_sum_2641_loc ) :=
              point_add (lift_to_both0 r_sum_2641) (point_mul (
                  lift_to_both0 z_2659) (lift_to_both0 r_2655)) in
            letbm a_sum_2642 loc( a_sum_2642_loc ) :=
              point_add (lift_to_both0 a_sum_2642) (point_mul ((
                    lift_to_both0 z_2659) *% (lift_to_both0 c_2657)) (
                  lift_to_both0 a_2652)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (
                scalar_t '×
                (
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t
                ) '×
                (
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t
                )
              ) error_t (prod_b(
                  lift_to_both0 s_sum_2640,
                  lift_to_both0 r_sum_2641,
                  lift_to_both0 a_sum_2642
                )))
            ) in
      letb b_2660 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letb sb_2661 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 s_sum_2640) (lift_to_both0 b_2660) in
      letb check_2662 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_add (point_neg (lift_to_both0 sb_2661)) (point_add (
            lift_to_both0 r_sum_2641) (lift_to_both0 a_sum_2642)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (is_identity (lift_to_both0 check_2662))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (CEfset (
        [s_sum_2640_loc ; r_sum_2641_loc ; a_sum_2642_loc])) [interface] (
      verify_result_t)).
Fail Next Obligation.

Definition r_sum_2665_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2667%nat).
Definition s_sum_2664_loc : ChoiceEqualityLocation :=
  (scalar_t ; 2668%nat).
Definition a_sum_2666_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2669%nat).
Notation "'alg3_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'alg3_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'alg3_batch_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Notation "'alg3_batch_verify_out'" :=(
  verify_result_t : ChoiceEquality) (at level 2).
Definition ALG3_BATCH_VERIFY : nat :=
  2687.
Program Definition alg3_batch_verify (entries_2671 : seq batch_entry_t) (
    entropy_2670 : byte_seq)
  : both (CEfset (
      [s_sum_2664_loc ; r_sum_2665_loc ; a_sum_2666_loc])) [interface] (
    verify_result_t) :=
  ((letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if (seq_len (lift_to_both0 entropy_2670)) <.? ((lift_to_both0 (
              usize 16)) .* (seq_len (
              lift_to_both0 entries_2671))) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := CEfset (
            [s_sum_2664_loc ; r_sum_2665_loc ; a_sum_2666_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
              _) _ : unit_ChoiceEquality :=
            @Err unit_ChoiceEquality error_t (NotEnoughRandomness) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok unit_ChoiceEquality error_t (lift_to_both0 (
              (tt : unit_ChoiceEquality))))
         in
      letbm s_sum_2664 : scalar_t loc( s_sum_2664_loc ) := nat_mod_zero  in
      letbm r_sum_2665 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( r_sum_2665_loc ) :=
        point_identity  in
      letbm a_sum_2666 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( a_sum_2666_loc ) :=
        point_identity  in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) '(
          s_sum_2664,
          r_sum_2665,
          a_sum_2666
        ) :=
        foldi_bind_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 entries_2671)) prod_ce(
            s_sum_2664,
            r_sum_2665,
            a_sum_2666
          ) (L := (CEfset (
                [s_sum_2664_loc ; r_sum_2665_loc ; a_sum_2666_loc]))) (
            I := [interface]) (fun i_2672 '(s_sum_2664, r_sum_2665, a_sum_2666
            ) =>
            letb BatchEntry ((pk_2673, msg_2674, signature_2675
                )) : batch_entry_t :=
              (seq_index (entries_2671) (lift_to_both0 i_2672)) in
            letbnd(_) a_2676 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 pk_2673)) (
                InvalidPublickey) in
            letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
              if is_identity (point_mul_by_cofactor (
                  lift_to_both0 a_2676)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [s_sum_2664_loc ; r_sum_2665_loc ; a_sum_2666_loc])) (
                L2 := CEfset (
                  [s_sum_2664_loc ; r_sum_2665_loc ; a_sum_2666_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbnd(_) _ : unit_ChoiceEquality :=
                  @Err unit_ChoiceEquality error_t (SmallOrderPoint) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                      (tt : unit_ChoiceEquality))))
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                    (tt : unit_ChoiceEquality))))
               in
            letb r_bytes_2677 : compressed_ed_point_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2675)) (lift_to_both0 (
                  usize 0)) (lift_to_both0 (usize 32)) in
            letb s_bytes_2678 : serialized_scalar_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2675)) (lift_to_both0 (
                  usize 32)) (lift_to_both0 (usize 32)) in
            letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
              if negb (check_canonical_scalar (
                  lift_to_both0 s_bytes_2678)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [s_sum_2664_loc ; r_sum_2665_loc ; a_sum_2666_loc])) (
                L2 := CEfset (
                  [s_sum_2664_loc ; r_sum_2665_loc ; a_sum_2666_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbnd(_) _ : unit_ChoiceEquality :=
                  @Err unit_ChoiceEquality error_t (InvalidS) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                      (tt : unit_ChoiceEquality))))
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                @Ok unit_ChoiceEquality error_t (lift_to_both0 (
                    (tt : unit_ChoiceEquality))))
               in
            letbnd(_) r_2679 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 r_bytes_2677)) (
                InvalidR) in
            letb s_2680 : scalar_t :=
              nat_mod_from_byte_seq_le (
                array_to_seq (lift_to_both0 s_bytes_2678)) in
            letb c_2681 : scalar_t :=
              scalar_from_hash (sha512 (seq_concat (array_concat (
                      lift_to_both0 r_bytes_2677) (
                      array_to_seq (lift_to_both0 pk_2673))) (
                    lift_to_both0 msg_2674))) in
            letb z_2682 : seq uint8 :=
              seq_slice (lift_to_both0 entropy_2670) ((lift_to_both0 (
                    usize 16)) .* (lift_to_both0 i_2672)) (lift_to_both0 (
                  usize 16)) in
            letb z_2683 : scalar_t :=
              nat_mod_from_byte_seq_le (seq_concat (lift_to_both0 z_2682) (
                  seq_new_ (default : uint8) (lift_to_both0 (usize 16)))) in
            letbm s_sum_2664 loc( s_sum_2664_loc ) :=
              (lift_to_both0 s_sum_2664) +% ((lift_to_both0 s_2680) *% (
                  lift_to_both0 z_2683)) in
            letbm r_sum_2665 loc( r_sum_2665_loc ) :=
              point_add (lift_to_both0 r_sum_2665) (point_mul (
                  lift_to_both0 z_2683) (lift_to_both0 r_2679)) in
            letbm a_sum_2666 loc( a_sum_2666_loc ) :=
              point_add (lift_to_both0 a_sum_2666) (point_mul ((
                    lift_to_both0 z_2683) *% (lift_to_both0 c_2681)) (
                  lift_to_both0 a_2676)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (
                scalar_t '×
                (
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t
                ) '×
                (
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t
                )
              ) error_t (prod_b(
                  lift_to_both0 s_sum_2664,
                  lift_to_both0 r_sum_2665,
                  lift_to_both0 a_sum_2666
                )))
            ) in
      letb b_2684 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letb sb_2685 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 s_sum_2664) (lift_to_both0 b_2684) in
      letb check_2686 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_add (point_neg (lift_to_both0 sb_2685)) (
            point_add (lift_to_both0 r_sum_2665) (lift_to_both0 a_sum_2666))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (is_identity (lift_to_both0 check_2686))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (CEfset (
        [s_sum_2664_loc ; r_sum_2665_loc ; a_sum_2666_loc])) [interface] (
      verify_result_t)).
Fail Next Obligation.

