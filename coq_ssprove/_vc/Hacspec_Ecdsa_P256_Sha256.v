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


Require Import Hacspec_P256.

Require Import Hacspec_Sha256.

Definition error_t : ChoiceEquality :=
  unit_ChoiceEquality '+ unit_ChoiceEquality.
Definition InvalidScalar : error_t :=
  inl tt.
Definition InvalidSignature : error_t :=
  inr tt.

Notation "'p256_public_key_t'" := (affine_t) : hacspec_scope.

Notation "'p256_secret_key_t'" := (p256_scalar_t) : hacspec_scope.

Notation "'p256_signature_t'" := ((p256_scalar_t '× p256_scalar_t
)) : hacspec_scope.

Notation "'p256_signature_result_t'" := ((
  result error_t p256_signature_t)) : hacspec_scope.

Notation "'p256_verify_result_t'" := ((result error_t unit)) : hacspec_scope.

Notation "'check_result_t'" := ((result error_t unit)) : hacspec_scope.

Notation "'arithmetic_result_t'" := ((result error_t affine_t)) : hacspec_scope.


Notation "'check_scalar_zero_inp'" :=(
  p256_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'check_scalar_zero_inp'" :=(
  p256_scalar_t : ChoiceEquality) (at level 2).
Notation "'check_scalar_zero_out'" :=(
  check_result_t : choice_type) (in custom pack_type at level 2).
Notation "'check_scalar_zero_out'" :=(
  check_result_t : ChoiceEquality) (at level 2).
Definition CHECK_SCALAR_ZERO : nat :=
  674.
Program Definition check_scalar_zero (r_673 : p256_scalar_t)
  : both (fset.fset0) [interface] (check_result_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (nat_mod_equal (lift_to_both0 r_673) (
            nat_mod_zero ))
        then @Err unit_ChoiceEquality error_t (InvalidScalar)
        else @Ok unit_ChoiceEquality error_t (tt))
      ) : both (fset.fset0) [interface] (check_result_t)).
Fail Next Obligation.


Notation "'ecdsa_point_mul_base_inp'" :=(
  p256_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'ecdsa_point_mul_base_inp'" :=(
  p256_scalar_t : ChoiceEquality) (at level 2).
Notation "'ecdsa_point_mul_base_out'" :=(
  arithmetic_result_t : choice_type) (in custom pack_type at level 2).
Notation "'ecdsa_point_mul_base_out'" :=(
  arithmetic_result_t : ChoiceEquality) (at level 2).
Definition ECDSA_POINT_MUL_BASE : nat :=
  675.
Program Definition ecdsa_point_mul_base (x_676 : p256_scalar_t)
  : both (fset.fset0) [interface] (arithmetic_result_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
      fset.fset0) [interface] (arithmetic_result_t)).
Fail Next Obligation.


Notation "'ecdsa_point_mul_inp'" :=(
  p256_scalar_t '× affine_t : choice_type) (in custom pack_type at level 2).
Notation "'ecdsa_point_mul_inp'" :=(
  p256_scalar_t '× affine_t : ChoiceEquality) (at level 2).
Notation "'ecdsa_point_mul_out'" :=(
  arithmetic_result_t : choice_type) (in custom pack_type at level 2).
Notation "'ecdsa_point_mul_out'" :=(
  arithmetic_result_t : ChoiceEquality) (at level 2).
Definition ECDSA_POINT_MUL : nat :=
  677.
Program Definition ecdsa_point_mul (k_678 : p256_scalar_t) (p_679 : affine_t)
  : both (fset.fset0) [interface] (arithmetic_result_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
      fset.fset0) [interface] (arithmetic_result_t)).
Fail Next Obligation.


Notation "'ecdsa_point_add_inp'" :=(
  affine_t '× affine_t : choice_type) (in custom pack_type at level 2).
Notation "'ecdsa_point_add_inp'" :=(
  affine_t '× affine_t : ChoiceEquality) (at level 2).
Notation "'ecdsa_point_add_out'" :=(
  arithmetic_result_t : choice_type) (in custom pack_type at level 2).
Notation "'ecdsa_point_add_out'" :=(
  arithmetic_result_t : ChoiceEquality) (at level 2).
Definition ECDSA_POINT_ADD : nat :=
  680.
Program Definition ecdsa_point_add (p_681 : affine_t) (q_682 : affine_t)
  : both (fset.fset0) [interface] (arithmetic_result_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
      fset.fset0) [interface] (arithmetic_result_t)).
Fail Next Obligation.


Notation "'sign_inp'" :=(
  byte_seq '× p256_secret_key_t '× p256_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'sign_inp'" :=(
  byte_seq '× p256_secret_key_t '× p256_scalar_t : ChoiceEquality) (at level 2).
Notation "'sign_out'" :=(
  p256_signature_result_t : choice_type) (in custom pack_type at level 2).
Notation "'sign_out'" :=(p256_signature_result_t : ChoiceEquality) (at level 2).
Definition SIGN : nat :=
  695.
Program Definition sign (payload_687 : byte_seq) (sk_690 : p256_secret_key_t) (
    nonce_683 : p256_scalar_t)
  : both (fset.fset0) [interface] (p256_signature_result_t) :=
  ((letbnd(_) _ : unit_ChoiceEquality :=
        check_scalar_zero (lift_to_both0 nonce_683) in
      letbnd(_) '(k_x_684, k_y_685) : affine_t :=
        ecdsa_point_mul_base (lift_to_both0 nonce_683) in
      letb r_686 : p256_scalar_t :=
        nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (
            lift_to_both0 k_x_684)) in
      letbnd(_) _ : unit_ChoiceEquality :=
        check_scalar_zero (lift_to_both0 r_686) in
      letb payload_hash_688 : sha256_digest_t :=
        hash (lift_to_both0 payload_687) in
      letb payload_hash_689 : p256_scalar_t :=
        nat_mod_from_byte_seq_be (
          array_to_seq (lift_to_both0 payload_hash_688)) in
      letb rsk_691 : p256_scalar_t :=
        (lift_to_both0 r_686) *% (lift_to_both0 sk_690) in
      letb hash_rsk_692 : p256_scalar_t :=
        (lift_to_both0 payload_hash_689) +% (lift_to_both0 rsk_691) in
      letb nonce_inv_693 : p256_scalar_t :=
        nat_mod_inv (lift_to_both0 nonce_683) in
      letb s_694 : p256_scalar_t :=
        (lift_to_both0 nonce_inv_693) *% (lift_to_both0 hash_rsk_692) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        @Ok p256_signature_t error_t (prod_b(
            lift_to_both0 r_686,
            lift_to_both0 s_694
          )))
      ) : both (fset.fset0) [interface] (p256_signature_result_t)).
Fail Next Obligation.


Notation "'ecdsa_p256_sha256_sign_inp'" :=(
  byte_seq '× p256_secret_key_t '× p256_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'ecdsa_p256_sha256_sign_inp'" :=(
  byte_seq '× p256_secret_key_t '× p256_scalar_t : ChoiceEquality) (at level 2).
Notation "'ecdsa_p256_sha256_sign_out'" :=(
  p256_signature_result_t : choice_type) (in custom pack_type at level 2).
Notation "'ecdsa_p256_sha256_sign_out'" :=(
  p256_signature_result_t : ChoiceEquality) (at level 2).
Definition ECDSA_P256_SHA256_SIGN : nat :=
  699.
Program Definition ecdsa_p256_sha256_sign (payload_696 : byte_seq) (
    sk_697 : p256_secret_key_t) (nonce_698 : p256_scalar_t)
  : both (fset.fset0) [interface] (p256_signature_result_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (sign (
          lift_to_both0 payload_696) (lift_to_both0 sk_697) (
          lift_to_both0 nonce_698))
      ) : both (fset.fset0) [interface] (p256_signature_result_t)).
Fail Next Obligation.


Notation "'verify_inp'" :=(
  byte_seq '× p256_public_key_t '× p256_signature_t : choice_type) (in custom pack_type at level 2).
Notation "'verify_inp'" :=(
  byte_seq '× p256_public_key_t '× p256_signature_t : ChoiceEquality) (at level 2).
Notation "'verify_out'" :=(
  p256_verify_result_t : choice_type) (in custom pack_type at level 2).
Notation "'verify_out'" :=(p256_verify_result_t : ChoiceEquality) (at level 2).
Definition VERIFY : nat :=
  715.
Program Definition verify (payload_703 : byte_seq) (
    pk_710 : p256_public_key_t) (signature_700 : p256_signature_t)
  : both (fset.fset0) [interface] (p256_verify_result_t) :=
  ((letb '(r_701, s_702) : (p256_scalar_t '× p256_scalar_t) :=
        lift_to_both0 signature_700 in
      letb payload_hash_704 : sha256_digest_t :=
        hash (lift_to_both0 payload_703) in
      letb payload_hash_705 : p256_scalar_t :=
        nat_mod_from_byte_seq_be (
          array_to_seq (lift_to_both0 payload_hash_704)) in
      letb s_inv_706 : p256_scalar_t := nat_mod_inv (lift_to_both0 s_702) in
      letb u1_707 : p256_scalar_t :=
        (lift_to_both0 payload_hash_705) *% (lift_to_both0 s_inv_706) in
      letbnd(_) u1_708 : affine_t :=
        ecdsa_point_mul_base (lift_to_both0 u1_707) in
      letb u2_709 : p256_scalar_t :=
        (lift_to_both0 r_701) *% (lift_to_both0 s_inv_706) in
      letbnd(_) u2_711 : affine_t :=
        ecdsa_point_mul (lift_to_both0 u2_709) (lift_to_both0 pk_710) in
      letbnd(_) '(x_712, y_713) : affine_t :=
        ecdsa_point_add (lift_to_both0 u1_708) (lift_to_both0 u2_711) in
      letb x_714 : p256_scalar_t :=
        nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (
            lift_to_both0 x_712)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 x_714) =.? (
            lift_to_both0 r_701))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (fset.fset0) [interface] (p256_verify_result_t)).
Fail Next Obligation.


Notation "'ecdsa_p256_sha256_verify_inp'" :=(
  byte_seq '× p256_public_key_t '× p256_signature_t : choice_type) (in custom pack_type at level 2).
Notation "'ecdsa_p256_sha256_verify_inp'" :=(
  byte_seq '× p256_public_key_t '× p256_signature_t : ChoiceEquality) (at level 2).
Notation "'ecdsa_p256_sha256_verify_out'" :=(
  p256_verify_result_t : choice_type) (in custom pack_type at level 2).
Notation "'ecdsa_p256_sha256_verify_out'" :=(
  p256_verify_result_t : ChoiceEquality) (at level 2).
Definition ECDSA_P256_SHA256_VERIFY : nat :=
  719.
Program Definition ecdsa_p256_sha256_verify (payload_716 : byte_seq) (
    pk_717 : p256_public_key_t) (signature_718 : p256_signature_t)
  : both (fset.fset0) [interface] (p256_verify_result_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (verify (
          lift_to_both0 payload_716) (lift_to_both0 pk_717) (
          lift_to_both0 signature_718))
      ) : both (fset.fset0) [interface] (p256_verify_result_t)).
Fail Next Obligation.

