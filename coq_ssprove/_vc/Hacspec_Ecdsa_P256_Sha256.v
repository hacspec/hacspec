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
Program Definition check_scalar_zero
  : both_package (fset.fset0) [interface] [(CHECK_SCALAR_ZERO,(
      check_scalar_zero_inp,check_scalar_zero_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(r_673) := temp_inp : p256_scalar_t in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) (nat_mod_equal (lift_to_both0 r_673) (
              nat_mod_zero ))
          then @Err unit_ChoiceEquality error_t (InvalidScalar)
          else @Ok unit_ChoiceEquality error_t (tt))
        ) : both (fset.fset0) [interface] (check_result_t)))in
  both_package' _ _ (CHECK_SCALAR_ZERO,(
      check_scalar_zero_inp,check_scalar_zero_out)) temp_package_both.
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
Program Definition ecdsa_point_mul_base
  : both_package (fset.fset0) [interface
  #val #[ P256_POINT_MUL_BASE ] : p256_point_mul_base_inp → p256_point_mul_base_out
  ] [(ECDSA_POINT_MUL_BASE,(
      ecdsa_point_mul_base_inp,ecdsa_point_mul_base_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_676) := temp_inp : p256_scalar_t in
    
    let p256_point_mul_base := fun x_0 => package_both p256_point_mul_base (
      x_0) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
        fset.fset0) [interface
      #val #[ P256_POINT_MUL_BASE ] : p256_point_mul_base_inp → p256_point_mul_base_out
      ] (arithmetic_result_t)))in
  both_package' _ _ (ECDSA_POINT_MUL_BASE,(
      ecdsa_point_mul_base_inp,ecdsa_point_mul_base_out)) temp_package_both.
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
Program Definition ecdsa_point_mul
  : both_package (fset.fset0) [interface
  #val #[ P256_POINT_MUL ] : p256_point_mul_inp → p256_point_mul_out ] [(
    ECDSA_POINT_MUL,(ecdsa_point_mul_inp,ecdsa_point_mul_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(k_678 , p_679) := temp_inp : p256_scalar_t '× affine_t in
    
    let p256_point_mul := fun x_0 x_1 => package_both p256_point_mul (
      x_0,x_1) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
        fset.fset0) [interface
      #val #[ P256_POINT_MUL ] : p256_point_mul_inp → p256_point_mul_out ] (
        arithmetic_result_t)))in
  both_package' _ _ (ECDSA_POINT_MUL,(
      ecdsa_point_mul_inp,ecdsa_point_mul_out)) temp_package_both.
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
Program Definition ecdsa_point_add
  : both_package (fset.fset0) [interface
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ] [(ECDSA_POINT_ADD,(
      ecdsa_point_add_inp,ecdsa_point_add_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_681 , q_682) := temp_inp : affine_t '× affine_t in
    
    let point_add := fun x_0 x_1 => package_both point_add (x_0,x_1) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
        fset.fset0) [interface
      #val #[ POINT_ADD ] : point_add_inp → point_add_out ] (
        arithmetic_result_t)))in
  both_package' _ _ (ECDSA_POINT_ADD,(
      ecdsa_point_add_inp,ecdsa_point_add_out)) temp_package_both.
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
Program Definition sign
  : both_package (fset.fset0) [interface
  #val #[ CHECK_SCALAR_ZERO ] : check_scalar_zero_inp → check_scalar_zero_out ;
  #val #[ ECDSA_POINT_MUL_BASE ] : ecdsa_point_mul_base_inp → ecdsa_point_mul_base_out ;
  #val #[ HASH ] : hash_inp → hash_out ] [(SIGN,(sign_inp,sign_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      payload_687 , sk_690 , nonce_683) := temp_inp : byte_seq '× p256_secret_key_t '× p256_scalar_t in
    
    let check_scalar_zero := fun x_0 => package_both check_scalar_zero (x_0) in
    let ecdsa_point_mul_base := fun x_0 => package_both ecdsa_point_mul_base (
      x_0) in
    let hash := fun x_0 => package_both hash (x_0) in
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
        ) : both (fset.fset0) [interface
      #val #[ CHECK_SCALAR_ZERO ] : check_scalar_zero_inp → check_scalar_zero_out ;
      #val #[ ECDSA_POINT_MUL_BASE ] : ecdsa_point_mul_base_inp → ecdsa_point_mul_base_out ;
      #val #[ HASH ] : hash_inp → hash_out ] (p256_signature_result_t)))in
  both_package' _ _ (SIGN,(sign_inp,sign_out)) temp_package_both.
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
Program Definition ecdsa_p256_sha256_sign
  : both_package (fset.fset0) [interface #val #[ SIGN ] : sign_inp → sign_out
  ] [(ECDSA_P256_SHA256_SIGN,(
      ecdsa_p256_sha256_sign_inp,ecdsa_p256_sha256_sign_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      payload_696 , sk_697 , nonce_698) := temp_inp : byte_seq '× p256_secret_key_t '× p256_scalar_t in
    
    let sign := fun x_0 x_1 x_2 => package_both sign (x_0,x_1,x_2) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (sign (
            lift_to_both0 payload_696) (lift_to_both0 sk_697) (
            lift_to_both0 nonce_698))
        ) : both (fset.fset0) [interface #val #[ SIGN ] : sign_inp → sign_out
      ] (p256_signature_result_t)))in
  both_package' _ _ (ECDSA_P256_SHA256_SIGN,(
      ecdsa_p256_sha256_sign_inp,ecdsa_p256_sha256_sign_out)) temp_package_both.
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
Program Definition verify
  : both_package (fset.fset0) [interface
  #val #[ ECDSA_POINT_ADD ] : ecdsa_point_add_inp → ecdsa_point_add_out ;
  #val #[ ECDSA_POINT_MUL ] : ecdsa_point_mul_inp → ecdsa_point_mul_out ;
  #val #[ ECDSA_POINT_MUL_BASE ] : ecdsa_point_mul_base_inp → ecdsa_point_mul_base_out ;
  #val #[ HASH ] : hash_inp → hash_out ] [(VERIFY,(verify_inp,verify_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      payload_703 , pk_710 , signature_700) := temp_inp : byte_seq '× p256_public_key_t '× p256_signature_t in
    
    let ecdsa_point_add := fun x_0 x_1 => package_both ecdsa_point_add (
      x_0,x_1) in
    let ecdsa_point_mul := fun x_0 x_1 => package_both ecdsa_point_mul (
      x_0,x_1) in
    let ecdsa_point_mul_base := fun x_0 => package_both ecdsa_point_mul_base (
      x_0) in
    let hash := fun x_0 => package_both hash (x_0) in
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
        ) : both (fset.fset0) [interface
      #val #[ ECDSA_POINT_ADD ] : ecdsa_point_add_inp → ecdsa_point_add_out ;
      #val #[ ECDSA_POINT_MUL ] : ecdsa_point_mul_inp → ecdsa_point_mul_out ;
      #val #[ ECDSA_POINT_MUL_BASE ] : ecdsa_point_mul_base_inp → ecdsa_point_mul_base_out ;
      #val #[ HASH ] : hash_inp → hash_out ] (p256_verify_result_t)))in
  both_package' _ _ (VERIFY,(verify_inp,verify_out)) temp_package_both.
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
Program Definition ecdsa_p256_sha256_verify
  : both_package (fset.fset0) [interface
  #val #[ VERIFY ] : verify_inp → verify_out ] [(ECDSA_P256_SHA256_VERIFY,(
      ecdsa_p256_sha256_verify_inp,ecdsa_p256_sha256_verify_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      payload_716 , pk_717 , signature_718) := temp_inp : byte_seq '× p256_public_key_t '× p256_signature_t in
    
    let verify := fun x_0 x_1 x_2 => package_both verify (x_0,x_1,x_2) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (verify (
            lift_to_both0 payload_716) (lift_to_both0 pk_717) (
            lift_to_both0 signature_718))
        ) : both (fset.fset0) [interface
      #val #[ VERIFY ] : verify_inp → verify_out ] (p256_verify_result_t)))in
  both_package' _ _ (ECDSA_P256_SHA256_VERIFY,(
      ecdsa_p256_sha256_verify_inp,ecdsa_p256_sha256_verify_out)) temp_package_both.
Fail Next Obligation.

