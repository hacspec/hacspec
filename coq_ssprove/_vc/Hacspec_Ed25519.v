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
  2650.
Program Definition scalar_from_hash (h_2648 : sha512_digest_t)
  : both (fset.fset0) [interface] (scalar_t) :=
  ((letb s_2649 : big_scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 h_2648)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        nat_mod_from_byte_seq_le (seq_slice (nat_mod_to_byte_seq_le (
              lift_to_both0 s_2649)) (lift_to_both0 (usize 0)) (lift_to_both0 (
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
  2664.
Program Definition sign (sk_2651 : secret_key_t) (msg_2657 : byte_seq)
  : both (fset.fset0) [interface] (signature_t) :=
  ((letb '(a_2652, prefix_2653) : (serialized_scalar_t '× serialized_scalar_t
        ) :=
        secret_expand (lift_to_both0 sk_2651) in
      letb a_2654 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 a_2652)) in
      letb b_2655 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letb a_p_2656 : compressed_ed_point_t :=
        compress (point_mul (lift_to_both0 a_2654) (lift_to_both0 b_2655)) in
      letb r_2658 : scalar_t :=
        scalar_from_hash (sha512 (array_concat (lift_to_both0 prefix_2653) (
              lift_to_both0 msg_2657))) in
      letb r_p_2659 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 r_2658) (lift_to_both0 b_2655) in
      letb r_s_2660 : compressed_ed_point_t :=
        compress (lift_to_both0 r_p_2659) in
      letb h_2661 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (
                lift_to_both0 r_s_2660) (
                array_to_seq (lift_to_both0 a_p_2656))) (
              lift_to_both0 msg_2657))) in
      letb s_2662 : scalar_t :=
        (lift_to_both0 r_2658) +% ((lift_to_both0 h_2661) *% (
            lift_to_both0 a_2654)) in
      letb s_bytes_2663 : seq uint8 :=
        seq_slice (nat_mod_to_byte_seq_le (lift_to_both0 s_2662)) (
          lift_to_both0 (usize 0)) (lift_to_both0 (usize 32)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_update (
          array_update (array_new_ (default : uint8) (64)) (lift_to_both0 (
              usize 0)) (array_to_seq (lift_to_both0 r_s_2660))) (
          lift_to_both0 (usize 32)) (lift_to_both0 s_bytes_2663))
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
  2678.
Program Definition zcash_verify (pk_2666 : public_key_t) (
    signature_2668 : signature_t) (msg_2673 : byte_seq)
  : both (fset.fset0) [interface] (verify_result_t) :=
  ((letb b_2665 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress_non_canonical (lift_to_both0 base_v)) in
      letbnd(_) a_2667 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress_non_canonical (lift_to_both0 pk_2666)) (
          InvalidPublickey) in
      letb r_bytes_2669 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2668)) (lift_to_both0 (
            usize 0)) (lift_to_both0 (usize 32)) in
      letb s_bytes_2670 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2668)) (lift_to_both0 (
            usize 32)) (lift_to_both0 (usize 32)) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if negb (check_canonical_scalar (
            lift_to_both0 s_bytes_2670)) :bool_ChoiceEquality
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
      letbnd(_) r_2671 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress_non_canonical (lift_to_both0 r_bytes_2669)) (
          InvalidR) in
      letb s_2672 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 s_bytes_2670)) in
      letb k_2674 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (
                lift_to_both0 r_bytes_2669) (lift_to_both0 pk_2666)) (
              lift_to_both0 msg_2673))) in
      letb sb_2675 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (lift_to_both0 s_2672) (
            lift_to_both0 b_2665)) in
      letb rc_2676 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (lift_to_both0 r_2671) in
      letb ka_2677 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (lift_to_both0 k_2674) (
            lift_to_both0 a_2667)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (point_eq (lift_to_both0 sb_2675) (
            point_add (lift_to_both0 rc_2676) (lift_to_both0 ka_2677)))
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
  2692.
Program Definition ietf_cofactored_verify (pk_2680 : public_key_t) (
    signature_2682 : signature_t) (msg_2687 : byte_seq)
  : both (fset.fset0) [interface] (verify_result_t) :=
  ((letb b_2679 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letbnd(_) a_2681 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 pk_2680)) (InvalidPublickey) in
      letb r_bytes_2683 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2682)) (lift_to_both0 (
            usize 0)) (lift_to_both0 (usize 32)) in
      letb s_bytes_2684 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2682)) (lift_to_both0 (
            usize 32)) (lift_to_both0 (usize 32)) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if negb (check_canonical_scalar (
            lift_to_both0 s_bytes_2684)) :bool_ChoiceEquality
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
      letbnd(_) r_2685 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 r_bytes_2683)) (InvalidR) in
      letb s_2686 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 s_bytes_2684)) in
      letb k_2688 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (
                lift_to_both0 r_bytes_2683) (lift_to_both0 pk_2680)) (
              lift_to_both0 msg_2687))) in
      letb sb_2689 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (lift_to_both0 s_2686) (
            lift_to_both0 b_2679)) in
      letb rc_2690 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (lift_to_both0 r_2685) in
      letb ka_2691 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (lift_to_both0 k_2688) (
            lift_to_both0 a_2681)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (point_eq (lift_to_both0 sb_2689) (
            point_add (lift_to_both0 rc_2690) (lift_to_both0 ka_2691)))
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
  2705.
Program Definition ietf_cofactorless_verify (pk_2694 : public_key_t) (
    signature_2696 : signature_t) (msg_2701 : byte_seq)
  : both (fset.fset0) [interface] (verify_result_t) :=
  ((letb b_2693 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letbnd(_) a_2695 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 pk_2694)) (InvalidPublickey) in
      letb r_bytes_2697 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2696)) (lift_to_both0 (
            usize 0)) (lift_to_both0 (usize 32)) in
      letb s_bytes_2698 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2696)) (lift_to_both0 (
            usize 32)) (lift_to_both0 (usize 32)) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if negb (check_canonical_scalar (
            lift_to_both0 s_bytes_2698)) :bool_ChoiceEquality
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
      letbnd(_) r_2699 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 r_bytes_2697)) (InvalidR) in
      letb s_2700 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 s_bytes_2698)) in
      letb k_2702 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (
                lift_to_both0 r_bytes_2697) (lift_to_both0 pk_2694)) (
              lift_to_both0 msg_2701))) in
      letb sb_2703 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 s_2700) (lift_to_both0 b_2693) in
      letb ka_2704 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 k_2702) (lift_to_both0 a_2695) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (point_eq (lift_to_both0 sb_2703) (
            point_add (lift_to_both0 r_2699) (lift_to_both0 ka_2704)))
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
  2707.
Program Definition is_identity (p_2706 : ed_point_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (point_eq (
          lift_to_both0 p_2706) (point_identity ))
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
  2721.
Program Definition alg2_verify (pk_2709 : public_key_t) (
    signature_2711 : signature_t) (msg_2716 : byte_seq)
  : both (fset.fset0) [interface] (verify_result_t) :=
  ((letb b_2708 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letbnd(_) a_2710 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 pk_2709)) (InvalidPublickey) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if is_identity (point_mul_by_cofactor (
            lift_to_both0 a_2710)) :bool_ChoiceEquality
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
      letb r_bytes_2712 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2711)) (lift_to_both0 (
            usize 0)) (lift_to_both0 (usize 32)) in
      letb s_bytes_2713 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 signature_2711)) (lift_to_both0 (
            usize 32)) (lift_to_both0 (usize 32)) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if negb (check_canonical_scalar (
            lift_to_both0 s_bytes_2713)) :bool_ChoiceEquality
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
      letbnd(_) r_2714 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (lift_to_both0 r_bytes_2712)) (InvalidR) in
      letb s_2715 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 s_bytes_2713)) in
      letb k_2717 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (
                lift_to_both0 r_bytes_2712) (lift_to_both0 pk_2709)) (
              lift_to_both0 msg_2716))) in
      letb sb_2718 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (lift_to_both0 s_2715) (
            lift_to_both0 b_2708)) in
      letb rc_2719 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (lift_to_both0 r_2714) in
      letb ka_2720 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (lift_to_both0 k_2717) (
            lift_to_both0 a_2710)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (point_eq (lift_to_both0 sb_2718) (
            point_add (lift_to_both0 rc_2719) (lift_to_both0 ka_2720)))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (fset.fset0) [interface] (verify_result_t)).
Fail Next Obligation.

Definition batch_entry_t : ChoiceEquality :=
  (public_key_t '× byte_seq '× signature_t).
Definition BatchEntry (x : (public_key_t '× byte_seq '× signature_t
    )) : batch_entry_t :=
   x.

Definition a_sum_2724_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2725%nat).
Definition r_sum_2723_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2726%nat).
Definition s_sum_2722_loc : ChoiceEqualityLocation :=
  (scalar_t ; 2727%nat).
Notation "'zcash_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'zcash_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'zcash_batch_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Notation "'zcash_batch_verify_out'" :=(
  verify_result_t : ChoiceEquality) (at level 2).
Definition ZCASH_BATCH_VERIFY : nat :=
  2745.
Program Definition zcash_batch_verify (entries_2729 : seq batch_entry_t) (
    entropy_2728 : byte_seq)
  : both (CEfset (
      [s_sum_2722_loc ; r_sum_2723_loc ; a_sum_2724_loc])) [interface] (
    verify_result_t) :=
  ((letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if (seq_len (lift_to_both0 entropy_2728)) <.? ((lift_to_both0 (
              usize 16)) .* (seq_len (
              lift_to_both0 entries_2729))) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := CEfset (
            [s_sum_2722_loc ; r_sum_2723_loc ; a_sum_2724_loc])) (
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
      letbm s_sum_2722 : scalar_t loc( s_sum_2722_loc ) := nat_mod_zero  in
      letbm r_sum_2723 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( r_sum_2723_loc ) :=
        point_identity  in
      letbm a_sum_2724 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( a_sum_2724_loc ) :=
        point_identity  in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) '(
          s_sum_2722,
          r_sum_2723,
          a_sum_2724
        ) :=
        foldi_bind_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 entries_2729)) prod_ce(
            s_sum_2722,
            r_sum_2723,
            a_sum_2724
          ) (L := (CEfset (
                [s_sum_2722_loc ; r_sum_2723_loc ; a_sum_2724_loc]))) (
            I := [interface]) (fun i_2730 '(s_sum_2722, r_sum_2723, a_sum_2724
            ) =>
            letb BatchEntry ((pk_2731, msg_2732, signature_2733
                )) : batch_entry_t :=
              (seq_index (entries_2729) (lift_to_both0 i_2730)) in
            letbnd(_) a_2734 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress_non_canonical (lift_to_both0 pk_2731)) (
                InvalidPublickey) in
            letb r_bytes_2735 : compressed_ed_point_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2733)) (lift_to_both0 (
                  usize 0)) (lift_to_both0 (usize 32)) in
            letb s_bytes_2736 : serialized_scalar_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2733)) (lift_to_both0 (
                  usize 32)) (lift_to_both0 (usize 32)) in
            letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
              if negb (check_canonical_scalar (
                  lift_to_both0 s_bytes_2736)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [s_sum_2722_loc ; r_sum_2723_loc ; a_sum_2724_loc])) (
                L2 := CEfset (
                  [s_sum_2722_loc ; r_sum_2723_loc ; a_sum_2724_loc])) (
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
            letbnd(_) r_2737 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress_non_canonical (
                  lift_to_both0 r_bytes_2735)) (InvalidR) in
            letb s_2738 : scalar_t :=
              nat_mod_from_byte_seq_le (
                array_to_seq (lift_to_both0 s_bytes_2736)) in
            letb c_2739 : scalar_t :=
              scalar_from_hash (sha512 (seq_concat (array_concat (
                      lift_to_both0 r_bytes_2735) (
                      array_to_seq (lift_to_both0 pk_2731))) (
                    lift_to_both0 msg_2732))) in
            letb z_2740 : seq uint8 :=
              seq_slice (lift_to_both0 entropy_2728) ((lift_to_both0 (
                    usize 16)) .* (lift_to_both0 i_2730)) (lift_to_both0 (
                  usize 16)) in
            letb z_2741 : scalar_t :=
              nat_mod_from_byte_seq_le (seq_concat (lift_to_both0 z_2740) (
                  seq_new_ (default : uint8) (lift_to_both0 (usize 16)))) in
            letbm s_sum_2722 loc( s_sum_2722_loc ) :=
              (lift_to_both0 s_sum_2722) +% ((lift_to_both0 s_2738) *% (
                  lift_to_both0 z_2741)) in
            letbm r_sum_2723 loc( r_sum_2723_loc ) :=
              point_add (lift_to_both0 r_sum_2723) (point_mul (
                  lift_to_both0 z_2741) (lift_to_both0 r_2737)) in
            letbm a_sum_2724 loc( a_sum_2724_loc ) :=
              point_add (lift_to_both0 a_sum_2724) (point_mul ((
                    lift_to_both0 z_2741) *% (lift_to_both0 c_2739)) (
                  lift_to_both0 a_2734)) in
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
                  lift_to_both0 s_sum_2722,
                  lift_to_both0 r_sum_2723,
                  lift_to_both0 a_sum_2724
                )))
            ) in
      letb b_2742 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letb sb_2743 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 s_sum_2722) (lift_to_both0 b_2742) in
      letb check_2744 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_add (point_neg (lift_to_both0 sb_2743)) (
            point_add (lift_to_both0 r_sum_2723) (lift_to_both0 a_sum_2724))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (is_identity (lift_to_both0 check_2744))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (CEfset (
        [s_sum_2722_loc ; r_sum_2723_loc ; a_sum_2724_loc])) [interface] (
      verify_result_t)).
Fail Next Obligation.

Definition a_sum_2748_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2749%nat).
Definition r_sum_2747_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2750%nat).
Definition s_sum_2746_loc : ChoiceEqualityLocation :=
  (scalar_t ; 2751%nat).
Notation "'ietf_cofactored_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactored_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'ietf_cofactored_batch_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactored_batch_verify_out'" :=(
  verify_result_t : ChoiceEquality) (at level 2).
Definition IETF_COFACTORED_BATCH_VERIFY : nat :=
  2769.
Program Definition ietf_cofactored_batch_verify (
    entries_2753 : seq batch_entry_t) (entropy_2752 : byte_seq)
  : both (CEfset (
      [s_sum_2746_loc ; r_sum_2747_loc ; a_sum_2748_loc])) [interface] (
    verify_result_t) :=
  ((letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if (seq_len (lift_to_both0 entropy_2752)) <.? ((lift_to_both0 (
              usize 16)) .* (seq_len (
              lift_to_both0 entries_2753))) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := CEfset (
            [s_sum_2746_loc ; r_sum_2747_loc ; a_sum_2748_loc])) (
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
      letbm s_sum_2746 : scalar_t loc( s_sum_2746_loc ) := nat_mod_zero  in
      letbm r_sum_2747 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( r_sum_2747_loc ) :=
        point_identity  in
      letbm a_sum_2748 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( a_sum_2748_loc ) :=
        point_identity  in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) '(
          s_sum_2746,
          r_sum_2747,
          a_sum_2748
        ) :=
        foldi_bind_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 entries_2753)) prod_ce(
            s_sum_2746,
            r_sum_2747,
            a_sum_2748
          ) (L := (CEfset (
                [s_sum_2746_loc ; r_sum_2747_loc ; a_sum_2748_loc]))) (
            I := [interface]) (fun i_2754 '(s_sum_2746, r_sum_2747, a_sum_2748
            ) =>
            letb BatchEntry ((pk_2755, msg_2756, signature_2757
                )) : batch_entry_t :=
              (seq_index (entries_2753) (lift_to_both0 i_2754)) in
            letbnd(_) a_2758 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 pk_2755)) (
                InvalidPublickey) in
            letb r_bytes_2759 : compressed_ed_point_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2757)) (lift_to_both0 (
                  usize 0)) (lift_to_both0 (usize 32)) in
            letb s_bytes_2760 : serialized_scalar_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2757)) (lift_to_both0 (
                  usize 32)) (lift_to_both0 (usize 32)) in
            letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
              if negb (check_canonical_scalar (
                  lift_to_both0 s_bytes_2760)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [s_sum_2746_loc ; r_sum_2747_loc ; a_sum_2748_loc])) (
                L2 := CEfset (
                  [s_sum_2746_loc ; r_sum_2747_loc ; a_sum_2748_loc])) (
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
            letbnd(_) r_2761 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 r_bytes_2759)) (
                InvalidR) in
            letb s_2762 : scalar_t :=
              nat_mod_from_byte_seq_le (
                array_to_seq (lift_to_both0 s_bytes_2760)) in
            letb c_2763 : scalar_t :=
              scalar_from_hash (sha512 (seq_concat (array_concat (
                      lift_to_both0 r_bytes_2759) (
                      array_to_seq (lift_to_both0 pk_2755))) (
                    lift_to_both0 msg_2756))) in
            letb z_2764 : seq uint8 :=
              seq_slice (lift_to_both0 entropy_2752) ((lift_to_both0 (
                    usize 16)) .* (lift_to_both0 i_2754)) (lift_to_both0 (
                  usize 16)) in
            letb z_2765 : scalar_t :=
              nat_mod_from_byte_seq_le (seq_concat (lift_to_both0 z_2764) (
                  seq_new_ (default : uint8) (lift_to_both0 (usize 16)))) in
            letbm s_sum_2746 loc( s_sum_2746_loc ) :=
              (lift_to_both0 s_sum_2746) +% ((lift_to_both0 s_2762) *% (
                  lift_to_both0 z_2765)) in
            letbm r_sum_2747 loc( r_sum_2747_loc ) :=
              point_add (lift_to_both0 r_sum_2747) (point_mul (
                  lift_to_both0 z_2765) (lift_to_both0 r_2761)) in
            letbm a_sum_2748 loc( a_sum_2748_loc ) :=
              point_add (lift_to_both0 a_sum_2748) (point_mul ((
                    lift_to_both0 z_2765) *% (lift_to_both0 c_2763)) (
                  lift_to_both0 a_2758)) in
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
                  lift_to_both0 s_sum_2746,
                  lift_to_both0 r_sum_2747,
                  lift_to_both0 a_sum_2748
                )))
            ) in
      letb b_2766 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letb sb_2767 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 s_sum_2746) (lift_to_both0 b_2766) in
      letb check_2768 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_add (point_neg (lift_to_both0 sb_2767)) (
            point_add (lift_to_both0 r_sum_2747) (lift_to_both0 a_sum_2748))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (is_identity (lift_to_both0 check_2768))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (CEfset (
        [s_sum_2746_loc ; r_sum_2747_loc ; a_sum_2748_loc])) [interface] (
      verify_result_t)).
Fail Next Obligation.

Definition s_sum_2770_loc : ChoiceEqualityLocation :=
  (scalar_t ; 2773%nat).
Definition r_sum_2771_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2774%nat).
Definition a_sum_2772_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2775%nat).
Notation "'ietf_cofactorless_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactorless_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'ietf_cofactorless_batch_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactorless_batch_verify_out'" :=(
  verify_result_t : ChoiceEquality) (at level 2).
Definition IETF_COFACTORLESS_BATCH_VERIFY : nat :=
  2793.
Program Definition ietf_cofactorless_batch_verify (
    entries_2777 : seq batch_entry_t) (entropy_2776 : byte_seq)
  : both (CEfset (
      [s_sum_2770_loc ; r_sum_2771_loc ; a_sum_2772_loc])) [interface] (
    verify_result_t) :=
  ((letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if (seq_len (lift_to_both0 entropy_2776)) <.? ((lift_to_both0 (
              usize 16)) .* (seq_len (
              lift_to_both0 entries_2777))) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := CEfset (
            [s_sum_2770_loc ; r_sum_2771_loc ; a_sum_2772_loc])) (
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
      letbm s_sum_2770 : scalar_t loc( s_sum_2770_loc ) := nat_mod_zero  in
      letbm r_sum_2771 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( r_sum_2771_loc ) :=
        point_identity  in
      letbm a_sum_2772 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( a_sum_2772_loc ) :=
        point_identity  in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) '(
          s_sum_2770,
          r_sum_2771,
          a_sum_2772
        ) :=
        foldi_bind_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 entries_2777)) prod_ce(
            s_sum_2770,
            r_sum_2771,
            a_sum_2772
          ) (L := (CEfset (
                [s_sum_2770_loc ; r_sum_2771_loc ; a_sum_2772_loc]))) (
            I := [interface]) (fun i_2778 '(s_sum_2770, r_sum_2771, a_sum_2772
            ) =>
            letb BatchEntry ((pk_2779, msg_2780, signature_2781
                )) : batch_entry_t :=
              (seq_index (entries_2777) (lift_to_both0 i_2778)) in
            letbnd(_) a_2782 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 pk_2779)) (
                InvalidPublickey) in
            letb r_bytes_2783 : compressed_ed_point_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2781)) (lift_to_both0 (
                  usize 0)) (lift_to_both0 (usize 32)) in
            letb s_bytes_2784 : serialized_scalar_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2781)) (lift_to_both0 (
                  usize 32)) (lift_to_both0 (usize 32)) in
            letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
              if negb (check_canonical_scalar (
                  lift_to_both0 s_bytes_2784)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [s_sum_2770_loc ; r_sum_2771_loc ; a_sum_2772_loc])) (
                L2 := CEfset (
                  [s_sum_2770_loc ; r_sum_2771_loc ; a_sum_2772_loc])) (
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
            letbnd(_) r_2785 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 r_bytes_2783)) (
                InvalidR) in
            letb s_2786 : scalar_t :=
              nat_mod_from_byte_seq_le (
                array_to_seq (lift_to_both0 s_bytes_2784)) in
            letb c_2787 : scalar_t :=
              scalar_from_hash (sha512 (seq_concat (array_concat (
                      lift_to_both0 r_bytes_2783) (
                      array_to_seq (lift_to_both0 pk_2779))) (
                    lift_to_both0 msg_2780))) in
            letb z_2788 : seq uint8 :=
              seq_slice (lift_to_both0 entropy_2776) ((lift_to_both0 (
                    usize 16)) .* (lift_to_both0 i_2778)) (lift_to_both0 (
                  usize 16)) in
            letb z_2789 : scalar_t :=
              nat_mod_from_byte_seq_le (seq_concat (lift_to_both0 z_2788) (
                  seq_new_ (default : uint8) (lift_to_both0 (usize 16)))) in
            letbm s_sum_2770 loc( s_sum_2770_loc ) :=
              (lift_to_both0 s_sum_2770) +% ((lift_to_both0 s_2786) *% (
                  lift_to_both0 z_2789)) in
            letbm r_sum_2771 loc( r_sum_2771_loc ) :=
              point_add (lift_to_both0 r_sum_2771) (point_mul (
                  lift_to_both0 z_2789) (lift_to_both0 r_2785)) in
            letbm a_sum_2772 loc( a_sum_2772_loc ) :=
              point_add (lift_to_both0 a_sum_2772) (point_mul ((
                    lift_to_both0 z_2789) *% (lift_to_both0 c_2787)) (
                  lift_to_both0 a_2782)) in
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
                  lift_to_both0 s_sum_2770,
                  lift_to_both0 r_sum_2771,
                  lift_to_both0 a_sum_2772
                )))
            ) in
      letb b_2790 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letb sb_2791 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 s_sum_2770) (lift_to_both0 b_2790) in
      letb check_2792 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_add (point_neg (lift_to_both0 sb_2791)) (point_add (
            lift_to_both0 r_sum_2771) (lift_to_both0 a_sum_2772)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (is_identity (lift_to_both0 check_2792))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (CEfset (
        [s_sum_2770_loc ; r_sum_2771_loc ; a_sum_2772_loc])) [interface] (
      verify_result_t)).
Fail Next Obligation.

Definition a_sum_2796_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2797%nat).
Definition s_sum_2794_loc : ChoiceEqualityLocation :=
  (scalar_t ; 2798%nat).
Definition r_sum_2795_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2799%nat).
Notation "'alg3_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'alg3_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'alg3_batch_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Notation "'alg3_batch_verify_out'" :=(
  verify_result_t : ChoiceEquality) (at level 2).
Definition ALG3_BATCH_VERIFY : nat :=
  2817.
Program Definition alg3_batch_verify (entries_2801 : seq batch_entry_t) (
    entropy_2800 : byte_seq)
  : both (CEfset (
      [s_sum_2794_loc ; r_sum_2795_loc ; a_sum_2796_loc])) [interface] (
    verify_result_t) :=
  ((letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
        if (seq_len (lift_to_both0 entropy_2800)) <.? ((lift_to_both0 (
              usize 16)) .* (seq_len (
              lift_to_both0 entries_2801))) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := CEfset (
            [s_sum_2794_loc ; r_sum_2795_loc ; a_sum_2796_loc])) (
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
      letbm s_sum_2794 : scalar_t loc( s_sum_2794_loc ) := nat_mod_zero  in
      letbm r_sum_2795 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( r_sum_2795_loc ) :=
        point_identity  in
      letbm a_sum_2796 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( a_sum_2796_loc ) :=
        point_identity  in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) '(
          s_sum_2794,
          r_sum_2795,
          a_sum_2796
        ) :=
        foldi_bind_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 entries_2801)) prod_ce(
            s_sum_2794,
            r_sum_2795,
            a_sum_2796
          ) (L := (CEfset (
                [s_sum_2794_loc ; r_sum_2795_loc ; a_sum_2796_loc]))) (
            I := [interface]) (fun i_2802 '(s_sum_2794, r_sum_2795, a_sum_2796
            ) =>
            letb BatchEntry ((pk_2803, msg_2804, signature_2805
                )) : batch_entry_t :=
              (seq_index (entries_2801) (lift_to_both0 i_2802)) in
            letbnd(_) a_2806 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 pk_2803)) (
                InvalidPublickey) in
            letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
              if is_identity (point_mul_by_cofactor (
                  lift_to_both0 a_2806)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [s_sum_2794_loc ; r_sum_2795_loc ; a_sum_2796_loc])) (
                L2 := CEfset (
                  [s_sum_2794_loc ; r_sum_2795_loc ; a_sum_2796_loc])) (
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
            letb r_bytes_2807 : compressed_ed_point_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2805)) (lift_to_both0 (
                  usize 0)) (lift_to_both0 (usize 32)) in
            letb s_bytes_2808 : serialized_scalar_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2805)) (lift_to_both0 (
                  usize 32)) (lift_to_both0 (usize 32)) in
            letbnd(ChoiceEqualityMonad.result_bind_both error_t) 'tt :=
              if negb (check_canonical_scalar (
                  lift_to_both0 s_bytes_2808)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [s_sum_2794_loc ; r_sum_2795_loc ; a_sum_2796_loc])) (
                L2 := CEfset (
                  [s_sum_2794_loc ; r_sum_2795_loc ; a_sum_2796_loc])) (
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
            letbnd(_) r_2809 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 r_bytes_2807)) (
                InvalidR) in
            letb s_2810 : scalar_t :=
              nat_mod_from_byte_seq_le (
                array_to_seq (lift_to_both0 s_bytes_2808)) in
            letb c_2811 : scalar_t :=
              scalar_from_hash (sha512 (seq_concat (array_concat (
                      lift_to_both0 r_bytes_2807) (
                      array_to_seq (lift_to_both0 pk_2803))) (
                    lift_to_both0 msg_2804))) in
            letb z_2812 : seq uint8 :=
              seq_slice (lift_to_both0 entropy_2800) ((lift_to_both0 (
                    usize 16)) .* (lift_to_both0 i_2802)) (lift_to_both0 (
                  usize 16)) in
            letb z_2813 : scalar_t :=
              nat_mod_from_byte_seq_le (seq_concat (lift_to_both0 z_2812) (
                  seq_new_ (default : uint8) (lift_to_both0 (usize 16)))) in
            letbm s_sum_2794 loc( s_sum_2794_loc ) :=
              (lift_to_both0 s_sum_2794) +% ((lift_to_both0 s_2810) *% (
                  lift_to_both0 z_2813)) in
            letbm r_sum_2795 loc( r_sum_2795_loc ) :=
              point_add (lift_to_both0 r_sum_2795) (point_mul (
                  lift_to_both0 z_2813) (lift_to_both0 r_2809)) in
            letbm a_sum_2796 loc( a_sum_2796_loc ) :=
              point_add (lift_to_both0 a_sum_2796) (point_mul ((
                    lift_to_both0 z_2813) *% (lift_to_both0 c_2811)) (
                  lift_to_both0 a_2806)) in
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
                  lift_to_both0 s_sum_2794,
                  lift_to_both0 r_sum_2795,
                  lift_to_both0 a_sum_2796
                )))
            ) in
      letb b_2814 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letb sb_2815 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 s_sum_2794) (lift_to_both0 b_2814) in
      letb check_2816 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_add (point_neg (lift_to_both0 sb_2815)) (
            point_add (lift_to_both0 r_sum_2795) (lift_to_both0 a_sum_2796))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (is_identity (lift_to_both0 check_2816))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (CEfset (
        [s_sum_2794_loc ; r_sum_2795_loc ; a_sum_2796_loc])) [interface] (
      verify_result_t)).
Fail Next Obligation.

