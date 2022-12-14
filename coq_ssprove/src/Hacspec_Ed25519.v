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
  2570.
Program Definition scalar_from_hash (h_2568 : sha512_digest_t)
  : both (fset.fset0) [interface] (scalar_t) :=
  ((letb s_2569 : big_scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 h_2568)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        nat_mod_from_byte_seq_le (seq_slice (nat_mod_to_byte_seq_le (
              lift_to_both0 s_2569)) (lift_to_both0 (usize 0)) (lift_to_both0 (
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
  2584.
Program Definition sign (sk_2571 : secret_key_t) (msg_2577 : byte_seq)
  : both (fset.fset0) [interface] (signature_t) :=
  ((letb '(a_2572, prefix_2573) : (serialized_scalar_t '× serialized_scalar_t
        ) :=
        secret_expand (lift_to_both0 sk_2571) in
      letb a_2574 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 a_2572)) in
      letb b_2575 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letb a_p_2576 : compressed_ed_point_t :=
        compress (point_mul (lift_to_both0 a_2574) (lift_to_both0 b_2575)) in
      letb r_2578 : scalar_t :=
        scalar_from_hash (sha512 (array_concat (lift_to_both0 prefix_2573) (
              lift_to_both0 msg_2577))) in
      letb r_p_2579 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 r_2578) (lift_to_both0 b_2575) in
      letb r_s_2580 : compressed_ed_point_t :=
        compress (lift_to_both0 r_p_2579) in
      letb h_2581 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (
                lift_to_both0 r_s_2580) (
                array_to_seq (lift_to_both0 a_p_2576))) (
              lift_to_both0 msg_2577))) in
      letb s_2582 : scalar_t :=
        (lift_to_both0 r_2578) +% ((lift_to_both0 h_2581) *% (
            lift_to_both0 a_2574)) in
      letb s_bytes_2583 : seq uint8 :=
        seq_slice (nat_mod_to_byte_seq_le (lift_to_both0 s_2582)) (
          lift_to_both0 (usize 0)) (lift_to_both0 (usize 32)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_update (
          array_update (array_new_ (default : uint8) (64)) (lift_to_both0 (
              usize 0)) (array_to_seq (lift_to_both0 r_s_2580))) (
          lift_to_both0 (usize 32)) (lift_to_both0 s_bytes_2583))
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
  2598.
Program Definition zcash_verify (pk_2586 : public_key_t) (
    signature_2588 : signature_t) (msg_2593 : byte_seq)
  : both (fset.fset0) [interface] (verify_result_t) :=
  ((letb b_2585 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress_non_canonical (lift_to_both0 base_v)) in
      letbnd(_) a_2587 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress_non_canonical (lift_to_both0 pk_2586)) (
          InvalidPublickey) in
      letb r_bytes_2589 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2588)) (lift_to_both0 (
            usize 0)) (lift_to_both0 (usize 32)) in
      letb s_bytes_2590 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2588)) (lift_to_both0 (
            usize 32)) (lift_to_both0 (usize 32)) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if negb (check_canonical_scalar (
            lift_to_both0 s_bytes_2590)) :bool_ChoiceEquality
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
      letbnd(_) r_2591 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress_non_canonical (lift_to_both0 r_bytes_2589)) (
          InvalidR) in
      letb s_2592 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 s_bytes_2590)) in
      letb k_2594 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (
                lift_to_both0 r_bytes_2589) (lift_to_both0 pk_2586)) (
              lift_to_both0 msg_2593))) in
      letb sb_2595 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (lift_to_both0 s_2592) (
            lift_to_both0 b_2585)) in
      letb rc_2596 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (lift_to_both0 r_2591) in
      letb ka_2597 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (lift_to_both0 k_2594) (
            lift_to_both0 a_2587)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (point_eq (lift_to_both0 sb_2595) (
            point_add (lift_to_both0 rc_2596) (lift_to_both0 ka_2597)))
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
  2612.
Program Definition ietf_cofactored_verify (pk_2600 : public_key_t) (
    signature_2602 : signature_t) (msg_2607 : byte_seq)
  : both (fset.fset0) [interface] (verify_result_t) :=
  ((letb b_2599 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letbnd(_) a_2601 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 pk_2600)) (InvalidPublickey) in
      letb r_bytes_2603 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2602)) (lift_to_both0 (
            usize 0)) (lift_to_both0 (usize 32)) in
      letb s_bytes_2604 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2602)) (lift_to_both0 (
            usize 32)) (lift_to_both0 (usize 32)) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if negb (check_canonical_scalar (
            lift_to_both0 s_bytes_2604)) :bool_ChoiceEquality
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
      letbnd(_) r_2605 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 r_bytes_2603)) (InvalidR) in
      letb s_2606 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 s_bytes_2604)) in
      letb k_2608 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (
                lift_to_both0 r_bytes_2603) (lift_to_both0 pk_2600)) (
              lift_to_both0 msg_2607))) in
      letb sb_2609 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (lift_to_both0 s_2606) (
            lift_to_both0 b_2599)) in
      letb rc_2610 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (lift_to_both0 r_2605) in
      letb ka_2611 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (lift_to_both0 k_2608) (
            lift_to_both0 a_2601)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (point_eq (lift_to_both0 sb_2609) (
            point_add (lift_to_both0 rc_2610) (lift_to_both0 ka_2611)))
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
  2625.
Program Definition ietf_cofactorless_verify (pk_2614 : public_key_t) (
    signature_2616 : signature_t) (msg_2621 : byte_seq)
  : both (fset.fset0) [interface] (verify_result_t) :=
  ((letb b_2613 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letbnd(_) a_2615 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 pk_2614)) (InvalidPublickey) in
      letb r_bytes_2617 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2616)) (lift_to_both0 (
            usize 0)) (lift_to_both0 (usize 32)) in
      letb s_bytes_2618 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2616)) (lift_to_both0 (
            usize 32)) (lift_to_both0 (usize 32)) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if negb (check_canonical_scalar (
            lift_to_both0 s_bytes_2618)) :bool_ChoiceEquality
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
      letbnd(_) r_2619 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 r_bytes_2617)) (InvalidR) in
      letb s_2620 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 s_bytes_2618)) in
      letb k_2622 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (
                lift_to_both0 r_bytes_2617) (lift_to_both0 pk_2614)) (
              lift_to_both0 msg_2621))) in
      letb sb_2623 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 s_2620) (lift_to_both0 b_2613) in
      letb ka_2624 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 k_2622) (lift_to_both0 a_2615) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (point_eq (lift_to_both0 sb_2623) (
            point_add (lift_to_both0 r_2619) (lift_to_both0 ka_2624)))
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
  2627.
Program Definition is_identity (p_2626 : ed_point_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (point_eq (
          lift_to_both0 p_2626) (point_identity ))
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
  2641.
Program Definition alg2_verify (pk_2629 : public_key_t) (
    signature_2631 : signature_t) (msg_2636 : byte_seq)
  : both (fset.fset0) [interface] (verify_result_t) :=
  ((letb b_2628 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letbnd(_) a_2630 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 pk_2629)) (InvalidPublickey) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if is_identity (point_mul_by_cofactor (
            lift_to_both0 a_2630)) :bool_ChoiceEquality
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
      letb r_bytes_2632 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2631)) (lift_to_both0 (
            usize 0)) (lift_to_both0 (usize 32)) in
      letb s_bytes_2633 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2631)) (lift_to_both0 (
            usize 32)) (lift_to_both0 (usize 32)) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if negb (check_canonical_scalar (
            lift_to_both0 s_bytes_2633)) :bool_ChoiceEquality
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
      letbnd(_) r_2634 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 r_bytes_2632)) (InvalidR) in
      letb s_2635 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 s_bytes_2633)) in
      letb k_2637 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (
                lift_to_both0 r_bytes_2632) (lift_to_both0 pk_2629)) (
              lift_to_both0 msg_2636))) in
      letb sb_2638 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (lift_to_both0 s_2635) (
            lift_to_both0 b_2628)) in
      letb rc_2639 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (lift_to_both0 r_2634) in
      letb ka_2640 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (lift_to_both0 k_2637) (
            lift_to_both0 a_2630)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (point_eq (lift_to_both0 sb_2638) (
            point_add (lift_to_both0 rc_2639) (lift_to_both0 ka_2640)))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (fset.fset0) [interface] (verify_result_t)).
Fail Next Obligation.

Definition batch_entry_t : ChoiceEquality :=
  (public_key_t '× byte_seq '× signature_t).
Definition BatchEntry (x : (public_key_t '× byte_seq '× signature_t
    )) : batch_entry_t :=
   x.

Definition r_sum_2643_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2645%nat).
Definition s_sum_2642_loc : ChoiceEqualityLocation :=
  (scalar_t ; 2646%nat).
Definition a_sum_2644_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2647%nat).
Notation "'zcash_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'zcash_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'zcash_batch_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Notation "'zcash_batch_verify_out'" :=(
  verify_result_t : ChoiceEquality) (at level 2).
Definition ZCASH_BATCH_VERIFY : nat :=
  2665.
Program Definition zcash_batch_verify (entries_2649 : seq batch_entry_t) (
    entropy_2648 : byte_seq)
  : both (CEfset (
      [s_sum_2642_loc ; r_sum_2643_loc ; a_sum_2644_loc])) [interface] (
    verify_result_t) :=
  ((letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if (seq_len (lift_to_both0 entropy_2648)) <.? ((lift_to_both0 (
              usize 16)) .* (seq_len (
              lift_to_both0 entries_2649))) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := CEfset (
            [s_sum_2642_loc ; r_sum_2643_loc ; a_sum_2644_loc])) (
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
      letbm s_sum_2642 : scalar_t loc( s_sum_2642_loc ) := nat_mod_zero  in
      letbm r_sum_2643 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( r_sum_2643_loc ) :=
        point_identity  in
      letbm a_sum_2644 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( a_sum_2644_loc ) :=
        point_identity  in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) '(
          s_sum_2642,
          r_sum_2643,
          a_sum_2644
        ) :=
        foldi_bind_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 entries_2649)) prod_ce(
            s_sum_2642,
            r_sum_2643,
            a_sum_2644
          ) (L := (CEfset (
                [s_sum_2642_loc ; r_sum_2643_loc ; a_sum_2644_loc]))) (
            I := [interface]) (fun i_2650 '(s_sum_2642, r_sum_2643, a_sum_2644
            ) =>
            letb BatchEntry ((pk_2651, msg_2652, signature_2653
                )) : batch_entry_t :=
              (seq_index (entries_2649) (lift_to_both0 i_2650)) in
            letbnd(_) a_2654 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress_non_canonical (lift_to_both0 pk_2651)) (
                InvalidPublickey) in
            letb r_bytes_2655 : compressed_ed_point_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2653)) (lift_to_both0 (
                  usize 0)) (lift_to_both0 (usize 32)) in
            letb s_bytes_2656 : serialized_scalar_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2653)) (lift_to_both0 (
                  usize 32)) (lift_to_both0 (usize 32)) in
            letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
              if negb (check_canonical_scalar (
                  lift_to_both0 s_bytes_2656)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [s_sum_2642_loc ; r_sum_2643_loc ; a_sum_2644_loc])) (
                L2 := CEfset (
                  [s_sum_2642_loc ; r_sum_2643_loc ; a_sum_2644_loc])) (
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
            letbnd(_) r_2657 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress_non_canonical (
                  lift_to_both0 r_bytes_2655)) (InvalidR) in
            letb s_2658 : scalar_t :=
              nat_mod_from_byte_seq_le (
                array_to_seq (lift_to_both0 s_bytes_2656)) in
            letb c_2659 : scalar_t :=
              scalar_from_hash (sha512 (seq_concat (array_concat (
                      lift_to_both0 r_bytes_2655) (
                      array_to_seq (lift_to_both0 pk_2651))) (
                    lift_to_both0 msg_2652))) in
            letb z_2660 : seq uint8 :=
              seq_slice (lift_to_both0 entropy_2648) ((lift_to_both0 (
                    usize 16)) .* (lift_to_both0 i_2650)) (lift_to_both0 (
                  usize 16)) in
            letb z_2661 : scalar_t :=
              nat_mod_from_byte_seq_le (seq_concat (lift_to_both0 z_2660) (
                  seq_new_ (default : uint8) (lift_to_both0 (usize 16)))) in
            letbm s_sum_2642 loc( s_sum_2642_loc ) :=
              (lift_to_both0 s_sum_2642) +% ((lift_to_both0 s_2658) *% (
                  lift_to_both0 z_2661)) in
            letbm r_sum_2643 loc( r_sum_2643_loc ) :=
              point_add (lift_to_both0 r_sum_2643) (point_mul (
                  lift_to_both0 z_2661) (lift_to_both0 r_2657)) in
            letbm a_sum_2644 loc( a_sum_2644_loc ) :=
              point_add (lift_to_both0 a_sum_2644) (point_mul ((
                    lift_to_both0 z_2661) *% (lift_to_both0 c_2659)) (
                  lift_to_both0 a_2654)) in
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
                  lift_to_both0 s_sum_2642,
                  lift_to_both0 r_sum_2643,
                  lift_to_both0 a_sum_2644
                )))
            ) in
      letb b_2662 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letb sb_2663 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 s_sum_2642) (lift_to_both0 b_2662) in
      letb check_2664 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_add (point_neg (lift_to_both0 sb_2663)) (
            point_add (lift_to_both0 r_sum_2643) (lift_to_both0 a_sum_2644))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (is_identity (lift_to_both0 check_2664))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (CEfset (
        [s_sum_2642_loc ; r_sum_2643_loc ; a_sum_2644_loc])) [interface] (
      verify_result_t)).
Fail Next Obligation.

Definition a_sum_2668_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2669%nat).
Definition r_sum_2667_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2670%nat).
Definition s_sum_2666_loc : ChoiceEqualityLocation :=
  (scalar_t ; 2671%nat).
Notation "'ietf_cofactored_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactored_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'ietf_cofactored_batch_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactored_batch_verify_out'" :=(
  verify_result_t : ChoiceEquality) (at level 2).
Definition IETF_COFACTORED_BATCH_VERIFY : nat :=
  2689.
Program Definition ietf_cofactored_batch_verify (
    entries_2673 : seq batch_entry_t) (entropy_2672 : byte_seq)
  : both (CEfset (
      [s_sum_2666_loc ; r_sum_2667_loc ; a_sum_2668_loc])) [interface] (
    verify_result_t) :=
  ((letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if (seq_len (lift_to_both0 entropy_2672)) <.? ((lift_to_both0 (
              usize 16)) .* (seq_len (
              lift_to_both0 entries_2673))) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := CEfset (
            [s_sum_2666_loc ; r_sum_2667_loc ; a_sum_2668_loc])) (
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
      letbm s_sum_2666 : scalar_t loc( s_sum_2666_loc ) := nat_mod_zero  in
      letbm r_sum_2667 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( r_sum_2667_loc ) :=
        point_identity  in
      letbm a_sum_2668 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( a_sum_2668_loc ) :=
        point_identity  in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) '(
          s_sum_2666,
          r_sum_2667,
          a_sum_2668
        ) :=
        foldi_bind_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 entries_2673)) prod_ce(
            s_sum_2666,
            r_sum_2667,
            a_sum_2668
          ) (L := (CEfset (
                [s_sum_2666_loc ; r_sum_2667_loc ; a_sum_2668_loc]))) (
            I := [interface]) (fun i_2674 '(s_sum_2666, r_sum_2667, a_sum_2668
            ) =>
            letb BatchEntry ((pk_2675, msg_2676, signature_2677
                )) : batch_entry_t :=
              (seq_index (entries_2673) (lift_to_both0 i_2674)) in
            letbnd(_) a_2678 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 pk_2675)) (
                InvalidPublickey) in
            letb r_bytes_2679 : compressed_ed_point_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2677)) (lift_to_both0 (
                  usize 0)) (lift_to_both0 (usize 32)) in
            letb s_bytes_2680 : serialized_scalar_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2677)) (lift_to_both0 (
                  usize 32)) (lift_to_both0 (usize 32)) in
            letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
              if negb (check_canonical_scalar (
                  lift_to_both0 s_bytes_2680)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [s_sum_2666_loc ; r_sum_2667_loc ; a_sum_2668_loc])) (
                L2 := CEfset (
                  [s_sum_2666_loc ; r_sum_2667_loc ; a_sum_2668_loc])) (
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
            letbnd(_) r_2681 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 r_bytes_2679)) (
                InvalidR) in
            letb s_2682 : scalar_t :=
              nat_mod_from_byte_seq_le (
                array_to_seq (lift_to_both0 s_bytes_2680)) in
            letb c_2683 : scalar_t :=
              scalar_from_hash (sha512 (seq_concat (array_concat (
                      lift_to_both0 r_bytes_2679) (
                      array_to_seq (lift_to_both0 pk_2675))) (
                    lift_to_both0 msg_2676))) in
            letb z_2684 : seq uint8 :=
              seq_slice (lift_to_both0 entropy_2672) ((lift_to_both0 (
                    usize 16)) .* (lift_to_both0 i_2674)) (lift_to_both0 (
                  usize 16)) in
            letb z_2685 : scalar_t :=
              nat_mod_from_byte_seq_le (seq_concat (lift_to_both0 z_2684) (
                  seq_new_ (default : uint8) (lift_to_both0 (usize 16)))) in
            letbm s_sum_2666 loc( s_sum_2666_loc ) :=
              (lift_to_both0 s_sum_2666) +% ((lift_to_both0 s_2682) *% (
                  lift_to_both0 z_2685)) in
            letbm r_sum_2667 loc( r_sum_2667_loc ) :=
              point_add (lift_to_both0 r_sum_2667) (point_mul (
                  lift_to_both0 z_2685) (lift_to_both0 r_2681)) in
            letbm a_sum_2668 loc( a_sum_2668_loc ) :=
              point_add (lift_to_both0 a_sum_2668) (point_mul ((
                    lift_to_both0 z_2685) *% (lift_to_both0 c_2683)) (
                  lift_to_both0 a_2678)) in
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
                  lift_to_both0 s_sum_2666,
                  lift_to_both0 r_sum_2667,
                  lift_to_both0 a_sum_2668
                )))
            ) in
      letb b_2686 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letb sb_2687 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 s_sum_2666) (lift_to_both0 b_2686) in
      letb check_2688 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_add (point_neg (lift_to_both0 sb_2687)) (
            point_add (lift_to_both0 r_sum_2667) (lift_to_both0 a_sum_2668))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (is_identity (lift_to_both0 check_2688))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (CEfset (
        [s_sum_2666_loc ; r_sum_2667_loc ; a_sum_2668_loc])) [interface] (
      verify_result_t)).
Fail Next Obligation.

Definition s_sum_2690_loc : ChoiceEqualityLocation :=
  (scalar_t ; 2693%nat).
Definition r_sum_2691_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2694%nat).
Definition a_sum_2692_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2695%nat).
Notation "'ietf_cofactorless_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactorless_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'ietf_cofactorless_batch_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactorless_batch_verify_out'" :=(
  verify_result_t : ChoiceEquality) (at level 2).
Definition IETF_COFACTORLESS_BATCH_VERIFY : nat :=
  2713.
Program Definition ietf_cofactorless_batch_verify (
    entries_2697 : seq batch_entry_t) (entropy_2696 : byte_seq)
  : both (CEfset (
      [s_sum_2690_loc ; r_sum_2691_loc ; a_sum_2692_loc])) [interface] (
    verify_result_t) :=
  ((letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if (seq_len (lift_to_both0 entropy_2696)) <.? ((lift_to_both0 (
              usize 16)) .* (seq_len (
              lift_to_both0 entries_2697))) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := CEfset (
            [s_sum_2690_loc ; r_sum_2691_loc ; a_sum_2692_loc])) (
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
      letbm s_sum_2690 : scalar_t loc( s_sum_2690_loc ) := nat_mod_zero  in
      letbm r_sum_2691 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( r_sum_2691_loc ) :=
        point_identity  in
      letbm a_sum_2692 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( a_sum_2692_loc ) :=
        point_identity  in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) '(
          s_sum_2690,
          r_sum_2691,
          a_sum_2692
        ) :=
        foldi_bind_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 entries_2697)) prod_ce(
            s_sum_2690,
            r_sum_2691,
            a_sum_2692
          ) (L := (CEfset (
                [s_sum_2690_loc ; r_sum_2691_loc ; a_sum_2692_loc]))) (
            I := [interface]) (fun i_2698 '(s_sum_2690, r_sum_2691, a_sum_2692
            ) =>
            letb BatchEntry ((pk_2699, msg_2700, signature_2701
                )) : batch_entry_t :=
              (seq_index (entries_2697) (lift_to_both0 i_2698)) in
            letbnd(_) a_2702 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 pk_2699)) (
                InvalidPublickey) in
            letb r_bytes_2703 : compressed_ed_point_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2701)) (lift_to_both0 (
                  usize 0)) (lift_to_both0 (usize 32)) in
            letb s_bytes_2704 : serialized_scalar_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2701)) (lift_to_both0 (
                  usize 32)) (lift_to_both0 (usize 32)) in
            letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
              if negb (check_canonical_scalar (
                  lift_to_both0 s_bytes_2704)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [s_sum_2690_loc ; r_sum_2691_loc ; a_sum_2692_loc])) (
                L2 := CEfset (
                  [s_sum_2690_loc ; r_sum_2691_loc ; a_sum_2692_loc])) (
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
            letbnd(_) r_2705 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 r_bytes_2703)) (
                InvalidR) in
            letb s_2706 : scalar_t :=
              nat_mod_from_byte_seq_le (
                array_to_seq (lift_to_both0 s_bytes_2704)) in
            letb c_2707 : scalar_t :=
              scalar_from_hash (sha512 (seq_concat (array_concat (
                      lift_to_both0 r_bytes_2703) (
                      array_to_seq (lift_to_both0 pk_2699))) (
                    lift_to_both0 msg_2700))) in
            letb z_2708 : seq uint8 :=
              seq_slice (lift_to_both0 entropy_2696) ((lift_to_both0 (
                    usize 16)) .* (lift_to_both0 i_2698)) (lift_to_both0 (
                  usize 16)) in
            letb z_2709 : scalar_t :=
              nat_mod_from_byte_seq_le (seq_concat (lift_to_both0 z_2708) (
                  seq_new_ (default : uint8) (lift_to_both0 (usize 16)))) in
            letbm s_sum_2690 loc( s_sum_2690_loc ) :=
              (lift_to_both0 s_sum_2690) +% ((lift_to_both0 s_2706) *% (
                  lift_to_both0 z_2709)) in
            letbm r_sum_2691 loc( r_sum_2691_loc ) :=
              point_add (lift_to_both0 r_sum_2691) (point_mul (
                  lift_to_both0 z_2709) (lift_to_both0 r_2705)) in
            letbm a_sum_2692 loc( a_sum_2692_loc ) :=
              point_add (lift_to_both0 a_sum_2692) (point_mul ((
                    lift_to_both0 z_2709) *% (lift_to_both0 c_2707)) (
                  lift_to_both0 a_2702)) in
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
                  lift_to_both0 s_sum_2690,
                  lift_to_both0 r_sum_2691,
                  lift_to_both0 a_sum_2692
                )))
            ) in
      letb b_2710 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letb sb_2711 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 s_sum_2690) (lift_to_both0 b_2710) in
      letb check_2712 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_add (point_neg (lift_to_both0 sb_2711)) (point_add (
            lift_to_both0 r_sum_2691) (lift_to_both0 a_sum_2692)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (is_identity (lift_to_both0 check_2712))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (CEfset (
        [s_sum_2690_loc ; r_sum_2691_loc ; a_sum_2692_loc])) [interface] (
      verify_result_t)).
Fail Next Obligation.

Definition a_sum_2716_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2717%nat).
Definition s_sum_2714_loc : ChoiceEqualityLocation :=
  (scalar_t ; 2718%nat).
Definition r_sum_2715_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2719%nat).
Notation "'alg3_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'alg3_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'alg3_batch_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Notation "'alg3_batch_verify_out'" :=(
  verify_result_t : ChoiceEquality) (at level 2).
Definition ALG3_BATCH_VERIFY : nat :=
  2737.
Program Definition alg3_batch_verify (entries_2721 : seq batch_entry_t) (
    entropy_2720 : byte_seq)
  : both (CEfset (
      [s_sum_2714_loc ; r_sum_2715_loc ; a_sum_2716_loc])) [interface] (
    verify_result_t) :=
  ((letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if (seq_len (lift_to_both0 entropy_2720)) <.? ((lift_to_both0 (
              usize 16)) .* (seq_len (
              lift_to_both0 entries_2721))) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := CEfset (
            [s_sum_2714_loc ; r_sum_2715_loc ; a_sum_2716_loc])) (
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
      letbm s_sum_2714 : scalar_t loc( s_sum_2714_loc ) := nat_mod_zero  in
      letbm r_sum_2715 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( r_sum_2715_loc ) :=
        point_identity  in
      letbm a_sum_2716 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( a_sum_2716_loc ) :=
        point_identity  in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) '(
          s_sum_2714,
          r_sum_2715,
          a_sum_2716
        ) :=
        foldi_bind_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 entries_2721)) prod_ce(
            s_sum_2714,
            r_sum_2715,
            a_sum_2716
          ) (L := (CEfset (
                [s_sum_2714_loc ; r_sum_2715_loc ; a_sum_2716_loc]))) (
            I := [interface]) (fun i_2722 '(s_sum_2714, r_sum_2715, a_sum_2716
            ) =>
            letb BatchEntry ((pk_2723, msg_2724, signature_2725
                )) : batch_entry_t :=
              (seq_index (entries_2721) (lift_to_both0 i_2722)) in
            letbnd(_) a_2726 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 pk_2723)) (
                InvalidPublickey) in
            letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
              if is_identity (point_mul_by_cofactor (
                  lift_to_both0 a_2726)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [s_sum_2714_loc ; r_sum_2715_loc ; a_sum_2716_loc])) (
                L2 := CEfset (
                  [s_sum_2714_loc ; r_sum_2715_loc ; a_sum_2716_loc])) (
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
            letb r_bytes_2727 : compressed_ed_point_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2725)) (lift_to_both0 (
                  usize 0)) (lift_to_both0 (usize 32)) in
            letb s_bytes_2728 : serialized_scalar_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2725)) (lift_to_both0 (
                  usize 32)) (lift_to_both0 (usize 32)) in
            letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
              if negb (check_canonical_scalar (
                  lift_to_both0 s_bytes_2728)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [s_sum_2714_loc ; r_sum_2715_loc ; a_sum_2716_loc])) (
                L2 := CEfset (
                  [s_sum_2714_loc ; r_sum_2715_loc ; a_sum_2716_loc])) (
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
            letbnd(_) r_2729 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 r_bytes_2727)) (
                InvalidR) in
            letb s_2730 : scalar_t :=
              nat_mod_from_byte_seq_le (
                array_to_seq (lift_to_both0 s_bytes_2728)) in
            letb c_2731 : scalar_t :=
              scalar_from_hash (sha512 (seq_concat (array_concat (
                      lift_to_both0 r_bytes_2727) (
                      array_to_seq (lift_to_both0 pk_2723))) (
                    lift_to_both0 msg_2724))) in
            letb z_2732 : seq uint8 :=
              seq_slice (lift_to_both0 entropy_2720) ((lift_to_both0 (
                    usize 16)) .* (lift_to_both0 i_2722)) (lift_to_both0 (
                  usize 16)) in
            letb z_2733 : scalar_t :=
              nat_mod_from_byte_seq_le (seq_concat (lift_to_both0 z_2732) (
                  seq_new_ (default : uint8) (lift_to_both0 (usize 16)))) in
            letbm s_sum_2714 loc( s_sum_2714_loc ) :=
              (lift_to_both0 s_sum_2714) +% ((lift_to_both0 s_2730) *% (
                  lift_to_both0 z_2733)) in
            letbm r_sum_2715 loc( r_sum_2715_loc ) :=
              point_add (lift_to_both0 r_sum_2715) (point_mul (
                  lift_to_both0 z_2733) (lift_to_both0 r_2729)) in
            letbm a_sum_2716 loc( a_sum_2716_loc ) :=
              point_add (lift_to_both0 a_sum_2716) (point_mul ((
                    lift_to_both0 z_2733) *% (lift_to_both0 c_2731)) (
                  lift_to_both0 a_2726)) in
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
                  lift_to_both0 s_sum_2714,
                  lift_to_both0 r_sum_2715,
                  lift_to_both0 a_sum_2716
                )))
            ) in
      letb b_2734 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letb sb_2735 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 s_sum_2714) (lift_to_both0 b_2734) in
      letb check_2736 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_add (point_neg (lift_to_both0 sb_2735)) (
            point_add (lift_to_both0 r_sum_2715) (lift_to_both0 a_sum_2716))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (is_identity (lift_to_both0 check_2736))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (CEfset (
        [s_sum_2714_loc ; r_sum_2715_loc ; a_sum_2716_loc])) [interface] (
      verify_result_t)).
Fail Next Obligation.

