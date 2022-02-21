(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Hacspec_P256.

Require Import Hacspec_Sha256.

Inductive error_t :=
| InvalidScalar : error_t
| InvalidSignature : error_t.

Notation "'public_key_t'" := (affine_t) : hacspec_scope.

Notation "'secret_key_t'" := (p256_scalar_t) : hacspec_scope.

Notation "'signature_t'" := ((p256_scalar_t × p256_scalar_t)) : hacspec_scope.

Notation "'signature_result_t'" := ((
  result signature_t error_t)) : hacspec_scope.

Notation "'verify_result_t'" := ((result unit error_t)) : hacspec_scope.

Notation "'check_result_t'" := ((result unit error_t)) : hacspec_scope.

Notation "'arithmetic_result_t'" := ((result affine_t error_t)) : hacspec_scope.

Definition check_scalar_zero (r_0 : p256_scalar_t) : check_result_t :=
  (if (nat_mod_equal (r_0) (nat_mod_zero )):bool then (@Err unit error_t (
        InvalidScalar)) else (@Ok unit error_t (tt))).

Definition ecdsa_point_mul_base (x_1 : p256_scalar_t) : arithmetic_result_t :=
  match p256_point_mul_base (x_1) with
  | Ok s_2 => @Ok affine_t error_t (s_2)
  | Err _ => @Err affine_t error_t (InvalidScalar)
  end.

Definition ecdsa_point_mul
  (k_3 : p256_scalar_t)
  (p_4 : affine_t)
  : arithmetic_result_t :=
  match p256_point_mul (k_3) (p_4) with
  | Ok s_5 => @Ok affine_t error_t (s_5)
  | Err _ => @Err affine_t error_t (InvalidScalar)
  end.

Definition ecdsa_point_add
  (p_6 : affine_t)
  (q_7 : affine_t)
  : arithmetic_result_t :=
  match point_add (p_6) (q_7) with
  | Ok s_8 => @Ok affine_t error_t (s_8)
  | Err _ => @Err affine_t error_t (InvalidScalar)
  end.

Definition sign
  (payload_9 : byte_seq)
  (sk_10 : secret_key_t)
  (nonce_11 : p256_scalar_t)
  : signature_result_t :=
  bind (check_scalar_zero (nonce_11)) (fun _ => bind (ecdsa_point_mul_base (
        nonce_11)) (fun '(k_x_12, k_y_13) => let r_14 : p256_scalar_t :=
        nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (
            k_x_12)) : p256_scalar_t in 
      bind (check_scalar_zero (r_14)) (fun _ =>
        let payload_hash_15 : sha256_digest_t :=
          hash (payload_9) in 
        let payload_hash_16 : p256_scalar_t :=
          nat_mod_from_byte_seq_be (payload_hash_15) : p256_scalar_t in 
        let rsk_17 : p256_scalar_t :=
          (r_14) *% (sk_10) in 
        let hash_rsk_18 : p256_scalar_t :=
          (payload_hash_16) +% (rsk_17) in 
        let nonce_inv_19 : p256_scalar_t :=
          nat_mod_inv (nonce_11) in 
        let s_20 : p256_scalar_t :=
          (nonce_inv_19) *% (hash_rsk_18) in 
        @Ok signature_t error_t ((r_14, s_20))))).

Definition ecdsa_p256_sha256_sign
  (payload_21 : byte_seq)
  (sk_22 : secret_key_t)
  (nonce_23 : p256_scalar_t)
  : signature_result_t :=
  sign (payload_21) (sk_22) (nonce_23).

Definition verify
  (payload_24 : byte_seq)
  (pk_25 : public_key_t)
  (signature_26 : signature_t)
  : verify_result_t :=
  let '(r_27, s_28) :=
    signature_26 in 
  let payload_hash_29 : sha256_digest_t :=
    hash (payload_24) in 
  let payload_hash_30 : p256_scalar_t :=
    nat_mod_from_byte_seq_be (payload_hash_29) : p256_scalar_t in 
  let s_inv_31 : p256_scalar_t :=
    nat_mod_inv (s_28) in 
  let u1_32 : p256_scalar_t :=
    (payload_hash_30) *% (s_inv_31) in 
  bind (ecdsa_point_mul_base (u1_32)) (fun u1_33 => let u2_34 : p256_scalar_t :=
      (r_27) *% (s_inv_31) in 
    bind (ecdsa_point_mul (u2_34) (pk_25)) (fun u2_35 => bind (ecdsa_point_add (
          u1_33) (u2_35)) (fun '(x_36, y_37) => let x_38 : p256_scalar_t :=
          nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (
              x_36)) : p256_scalar_t in 
        (if ((x_38) =.? (r_27)):bool then (@Ok unit error_t (tt)) else (
            @Err unit error_t (InvalidSignature)))))).

Definition ecdsa_p256_sha256_verify
  (payload_39 : byte_seq)
  (pk_40 : public_key_t)
  (signature_41 : signature_t)
  : verify_result_t :=
  verify (payload_39) (pk_40) (signature_41).

