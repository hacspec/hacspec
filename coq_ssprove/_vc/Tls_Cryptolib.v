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


Require Import Hacspec_Aes.

Require Import Hacspec_Aes128_Gcm.

Require Import Hacspec_Chacha20.

Require Import Hacspec_Poly1305.

Require Import Hacspec_Chacha20poly1305.

Require Import Hacspec_Curve25519.

Require Import Hacspec_P256.

Require Import Hacspec_Sha256.

Require Import Hacspec_Ecdsa_P256_Sha256.

Require Import Hacspec_Gf128.

Require Import Hacspec_Hkdf.

Require Import Hacspec_Hmac.

Definition crypto_error_t : ChoiceEquality :=
  unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality.
Definition CryptoError : crypto_error_t :=
  inl (inl (inl (inl (inl (inl tt))))).
Definition HkdfError : crypto_error_t :=
  inl (inl (inl (inl (inl (inr tt))))).
Definition InsufficientEntropy : crypto_error_t :=
  inl (inl (inl (inl (inr tt)))).
Definition InvalidCert : crypto_error_t :=
  inl (inl (inl (inr tt))).
Definition MacFailed : crypto_error_t :=
  inl (inl (inr tt)).
Definition UnsupportedAlgorithm : crypto_error_t :=
  inl (inr tt).
Definition VerifyFailed : crypto_error_t :=
  inr tt.


Notation "'empty_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'empty_inp'" :=(unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'empty_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'empty_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition EMPTY : nat :=
  0.
Program Definition empty
  : both_package (fset.fset0) [interface] [(EMPTY,(empty_inp,empty_out))] :=
  let temp_package_both := (fun temp_inp => 
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (seq_new_ (
            default : uint8) (lift_to_both0 (usize 0)))
        ) : both (fset.fset0) [interface] (byte_seq)))in
  both_package' _ _ (EMPTY,(empty_inp,empty_out)) temp_package_both.
Fail Next Obligation.


Notation "'zeros_inp'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'zeros_inp'" :=(uint_size : ChoiceEquality) (at level 2).
Notation "'zeros_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'zeros_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition ZEROS : nat :=
  2.
Program Definition zeros
  : both_package (fset.fset0) [interface] [(ZEROS,(zeros_inp,zeros_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(u_1) := temp_inp : uint_size in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (seq_new_ (
            default : uint8) (lift_to_both0 u_1))
        ) : both (fset.fset0) [interface] (byte_seq)))in
  both_package' _ _ (ZEROS,(zeros_inp,zeros_out)) temp_package_both.
Fail Next Obligation.

Notation "'entropy_t'" := (byte_seq) : hacspec_scope.

Definition random_t := nseq (uint8) (usize 32).

Notation "'dh_sk_t'" := (byte_seq) : hacspec_scope.

Notation "'dh_pk_t'" := (byte_seq) : hacspec_scope.

Notation "'signature_key_t'" := (byte_seq) : hacspec_scope.

Notation "'verification_key_t'" := (byte_seq) : hacspec_scope.

Notation "'mac_key_t'" := (byte_seq) : hacspec_scope.

Notation "'aead_key_t'" := (byte_seq) : hacspec_scope.

Notation "'key_t'" := (byte_seq) : hacspec_scope.

Notation "'psk_t'" := (key_t) : hacspec_scope.

Notation "'digest_t'" := (byte_seq) : hacspec_scope.

Notation "'hmac_t'" := (byte_seq) : hacspec_scope.

Notation "'signature_t'" := (byte_seq) : hacspec_scope.

Notation "'aead_iv_t'" := (byte_seq) : hacspec_scope.

Notation "'aead_key_iv_t'" := ((aead_key_t '× aead_iv_t)) : hacspec_scope.

Definition named_group_t : ChoiceEquality :=
  unit_ChoiceEquality '+ unit_ChoiceEquality.
Definition X25519 : named_group_t :=
  inl tt.
Definition Secp256r1 : named_group_t :=
  inr tt.

Definition hash_algorithm_t : ChoiceEquality :=
  unit_ChoiceEquality '+ unit_ChoiceEquality.
Definition SHA256 : hash_algorithm_t :=
  inl tt.
Definition SHA384 : hash_algorithm_t :=
  inr tt.

Definition aead_algorithm_t : ChoiceEquality :=
  unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality.
Definition Chacha20Poly1305 : aead_algorithm_t :=
  inl (inl tt).
Definition Aes128Gcm : aead_algorithm_t :=
  inl (inr tt).
Definition Aes256Gcm : aead_algorithm_t :=
  inr tt.

Definition signature_scheme_t : ChoiceEquality :=
  unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality.
Definition ED25519 : signature_scheme_t :=
  inl (inl tt).
Definition EcdsaSecp256r1Sha256 : signature_scheme_t :=
  inl (inr tt).
Definition RsaPssRsaSha256 : signature_scheme_t :=
  inr tt.


Notation "'hash_len_inp'" :=(
  hash_algorithm_t : choice_type) (in custom pack_type at level 2).
Notation "'hash_len_inp'" :=(hash_algorithm_t : ChoiceEquality) (at level 2).
Notation "'hash_len_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'hash_len_out'" :=(uint_size : ChoiceEquality) (at level 2).
Definition HASH_LEN : nat :=
  3.
Program Definition hash_len
  : both_package (fset.fset0) [interface] [(HASH_LEN,(
      hash_len_inp,hash_len_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(ha_4) := temp_inp : hash_algorithm_t in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
        fset.fset0) [interface] (uint_size)))in
  both_package' _ _ (HASH_LEN,(hash_len_inp,hash_len_out)) temp_package_both.
Fail Next Obligation.


Notation "'hmac_key_len_inp'" :=(
  hash_algorithm_t : choice_type) (in custom pack_type at level 2).
Notation "'hmac_key_len_inp'" :=(
  hash_algorithm_t : ChoiceEquality) (at level 2).
Notation "'hmac_key_len_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'hmac_key_len_out'" :=(uint_size : ChoiceEquality) (at level 2).
Definition HMAC_KEY_LEN : nat :=
  5.
Program Definition hmac_key_len
  : both_package (fset.fset0) [interface] [(HMAC_KEY_LEN,(
      hmac_key_len_inp,hmac_key_len_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(ha_6) := temp_inp : hash_algorithm_t in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
        fset.fset0) [interface] (uint_size)))in
  both_package' _ _ (HMAC_KEY_LEN,(
      hmac_key_len_inp,hmac_key_len_out)) temp_package_both.
Fail Next Obligation.


Notation "'ae_key_len_inp'" :=(
  aead_algorithm_t : choice_type) (in custom pack_type at level 2).
Notation "'ae_key_len_inp'" :=(aead_algorithm_t : ChoiceEquality) (at level 2).
Notation "'ae_key_len_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'ae_key_len_out'" :=(uint_size : ChoiceEquality) (at level 2).
Definition AE_KEY_LEN : nat :=
  7.
Program Definition ae_key_len
  : both_package (fset.fset0) [interface] [(AE_KEY_LEN,(
      ae_key_len_inp,ae_key_len_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(ae_8) := temp_inp : aead_algorithm_t in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
        fset.fset0) [interface] (uint_size)))in
  both_package' _ _ (AE_KEY_LEN,(
      ae_key_len_inp,ae_key_len_out)) temp_package_both.
Fail Next Obligation.


Notation "'ae_iv_len_inp'" :=(
  aead_algorithm_t : choice_type) (in custom pack_type at level 2).
Notation "'ae_iv_len_inp'" :=(aead_algorithm_t : ChoiceEquality) (at level 2).
Notation "'ae_iv_len_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'ae_iv_len_out'" :=(uint_size : ChoiceEquality) (at level 2).
Definition AE_IV_LEN : nat :=
  9.
Program Definition ae_iv_len
  : both_package (fset.fset0) [interface] [(AE_IV_LEN,(
      ae_iv_len_inp,ae_iv_len_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(ae_10) := temp_inp : aead_algorithm_t in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
        fset.fset0) [interface] (uint_size)))in
  both_package' _ _ (AE_IV_LEN,(ae_iv_len_inp,ae_iv_len_out)) temp_package_both.
Fail Next Obligation.


Notation "'dh_priv_len_inp'" :=(
  named_group_t : choice_type) (in custom pack_type at level 2).
Notation "'dh_priv_len_inp'" :=(named_group_t : ChoiceEquality) (at level 2).
Notation "'dh_priv_len_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'dh_priv_len_out'" :=(uint_size : ChoiceEquality) (at level 2).
Definition DH_PRIV_LEN : nat :=
  11.
Program Definition dh_priv_len
  : both_package (fset.fset0) [interface] [(DH_PRIV_LEN,(
      dh_priv_len_inp,dh_priv_len_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(gn_12) := temp_inp : named_group_t in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
        fset.fset0) [interface] (uint_size)))in
  both_package' _ _ (DH_PRIV_LEN,(
      dh_priv_len_inp,dh_priv_len_out)) temp_package_both.
Fail Next Obligation.


Notation "'dh_pub_len_inp'" :=(
  named_group_t : choice_type) (in custom pack_type at level 2).
Notation "'dh_pub_len_inp'" :=(named_group_t : ChoiceEquality) (at level 2).
Notation "'dh_pub_len_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'dh_pub_len_out'" :=(uint_size : ChoiceEquality) (at level 2).
Definition DH_PUB_LEN : nat :=
  13.
Program Definition dh_pub_len
  : both_package (fset.fset0) [interface] [(DH_PUB_LEN,(
      dh_pub_len_inp,dh_pub_len_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(gn_14) := temp_inp : named_group_t in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
        fset.fset0) [interface] (uint_size)))in
  both_package' _ _ (DH_PUB_LEN,(
      dh_pub_len_inp,dh_pub_len_out)) temp_package_both.
Fail Next Obligation.


Notation "'zero_key_inp'" :=(
  hash_algorithm_t : choice_type) (in custom pack_type at level 2).
Notation "'zero_key_inp'" :=(hash_algorithm_t : ChoiceEquality) (at level 2).
Notation "'zero_key_out'" :=(
  key_t : choice_type) (in custom pack_type at level 2).
Notation "'zero_key_out'" :=(key_t : ChoiceEquality) (at level 2).
Definition ZERO_KEY : nat :=
  16.
Program Definition zero_key
  : both_package (fset.fset0) [interface
  #val #[ HASH_LEN ] : hash_len_inp → hash_len_out ] [(ZERO_KEY,(
      zero_key_inp,zero_key_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(ha_15) := temp_inp : hash_algorithm_t in
    
    let hash_len := fun x_0 => package_both hash_len (x_0) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (seq_new_ (
            default : uint8) (usize (is_pure (hash_len (lift_to_both0 ha_15)))))
        ) : both (fset.fset0) [interface
      #val #[ HASH_LEN ] : hash_len_inp → hash_len_out ] (key_t)))in
  both_package' _ _ (ZERO_KEY,(zero_key_inp,zero_key_out)) temp_package_both.
Fail Next Obligation.


Notation "'secret_to_public_inp'" :=(
  named_group_t '× dh_sk_t : choice_type) (in custom pack_type at level 2).
Notation "'secret_to_public_inp'" :=(
  named_group_t '× dh_sk_t : ChoiceEquality) (at level 2).
Notation "'secret_to_public_out'" :=((result (crypto_error_t) (
      dh_pk_t)) : choice_type) (in custom pack_type at level 2).
Notation "'secret_to_public_out'" :=((result (crypto_error_t) (
      dh_pk_t)) : ChoiceEquality) (at level 2).
Definition SECRET_TO_PUBLIC : nat :=
  17.
Program Definition secret_to_public
  : both_package (fset.fset0) [interface
  #val #[ P256_POINT_MUL_BASE ] : p256_point_mul_base_inp → p256_point_mul_base_out ;
  #val #[ X25519_SECRET_TO_PUBLIC ] : x25519_secret_to_public_inp → x25519_secret_to_public_out
  ] [(SECRET_TO_PUBLIC,(secret_to_public_inp,secret_to_public_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(group_name_18 , x_19) := temp_inp : named_group_t '× dh_sk_t in
    
    let p256_point_mul_base := fun x_0 => package_both p256_point_mul_base (
      x_0) in
    let x25519_secret_to_public := fun x_0 => package_both x25519_secret_to_public (
      x_0) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
        fset.fset0) [interface
      #val #[ P256_POINT_MUL_BASE ] : p256_point_mul_base_inp → p256_point_mul_base_out ;
      #val #[ X25519_SECRET_TO_PUBLIC ] : x25519_secret_to_public_inp → x25519_secret_to_public_out
      ] ((result (crypto_error_t) (dh_pk_t)))))in
  both_package' _ _ (SECRET_TO_PUBLIC,(
      secret_to_public_inp,secret_to_public_out)) temp_package_both.
Fail Next Obligation.


Notation "'p256_check_point_len_inp'" :=(
  dh_pk_t : choice_type) (in custom pack_type at level 2).
Notation "'p256_check_point_len_inp'" :=(dh_pk_t : ChoiceEquality) (at level 2).
Notation "'p256_check_point_len_out'" :=((result (crypto_error_t) (
      unit_ChoiceEquality)) : choice_type) (in custom pack_type at level 2).
Notation "'p256_check_point_len_out'" :=((result (crypto_error_t) (
      unit_ChoiceEquality)) : ChoiceEquality) (at level 2).
Definition P256_CHECK_POINT_LEN : nat :=
  21.
Program Definition p256_check_point_len
  : both_package (fset.fset0) [interface] [(P256_CHECK_POINT_LEN,(
      p256_check_point_len_inp,p256_check_point_len_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_20) := temp_inp : dh_pk_t in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) ((seq_len (lift_to_both0 p_20)) !=.? (
              lift_to_both0 (usize 64)))
          then @Err unit_ChoiceEquality crypto_error_t (CryptoError)
          else @Ok unit_ChoiceEquality crypto_error_t (tt))
        ) : both (fset.fset0) [interface] ((result (crypto_error_t) (
            unit_ChoiceEquality)))))in
  both_package' _ _ (P256_CHECK_POINT_LEN,(
      p256_check_point_len_inp,p256_check_point_len_out)) temp_package_both.
Fail Next Obligation.


Notation "'p256_ecdh_inp'" :=(
  dh_sk_t '× dh_pk_t : choice_type) (in custom pack_type at level 2).
Notation "'p256_ecdh_inp'" :=(
  dh_sk_t '× dh_pk_t : ChoiceEquality) (at level 2).
Notation "'p256_ecdh_out'" :=((result (crypto_error_t) (
      key_t)) : choice_type) (in custom pack_type at level 2).
Notation "'p256_ecdh_out'" :=((result (crypto_error_t) (
      key_t)) : ChoiceEquality) (at level 2).
Definition P256_ECDH : nat :=
  24.
Program Definition p256_ecdh
  : both_package (fset.fset0) [interface
  #val #[ P256_CHECK_POINT_LEN ] : p256_check_point_len_inp → p256_check_point_len_out ;
  #val #[ P256_POINT_MUL ] : p256_point_mul_inp → p256_point_mul_out ] [(
    P256_ECDH,(p256_ecdh_inp,p256_ecdh_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_25 , y_22) := temp_inp : dh_sk_t '× dh_pk_t in
    
    let p256_check_point_len := fun x_0 => package_both p256_check_point_len (
      x_0) in
    let p256_point_mul := fun x_0 x_1 => package_both p256_point_mul (
      x_0,x_1) in
    ((letbnd(_) _ : unit_ChoiceEquality :=
          p256_check_point_len (lift_to_both0 y_22) in
        letb pk_23 : (p256_field_element_t '× p256_field_element_t) :=
          prod_b(
            nat_mod_from_byte_seq_be (seq_slice_range (lift_to_both0 y_22) (
                prod_b(lift_to_both0 (usize 0), lift_to_both0 (usize 32)))),
            nat_mod_from_byte_seq_be (seq_slice_range (lift_to_both0 y_22) (
                prod_b(lift_to_both0 (usize 32), lift_to_both0 (usize 64))))
          ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match)
        ) : both (fset.fset0) [interface
      #val #[ P256_CHECK_POINT_LEN ] : p256_check_point_len_inp → p256_check_point_len_out ;
      #val #[ P256_POINT_MUL ] : p256_point_mul_inp → p256_point_mul_out ] ((
          result (crypto_error_t) (key_t)))))in
  both_package' _ _ (P256_ECDH,(p256_ecdh_inp,p256_ecdh_out)) temp_package_both.
Fail Next Obligation.


Notation "'ecdh_inp'" :=(
  named_group_t '× dh_sk_t '× dh_pk_t : choice_type) (in custom pack_type at level 2).
Notation "'ecdh_inp'" :=(
  named_group_t '× dh_sk_t '× dh_pk_t : ChoiceEquality) (at level 2).
Notation "'ecdh_out'" :=((result (crypto_error_t) (
      key_t)) : choice_type) (in custom pack_type at level 2).
Notation "'ecdh_out'" :=((result (crypto_error_t) (
      key_t)) : ChoiceEquality) (at level 2).
Definition ECDH : nat :=
  26.
Program Definition ecdh
  : both_package (fset.fset0) [interface
  #val #[ P256_ECDH ] : p256_ecdh_inp → p256_ecdh_out ;
  #val #[ X25519_SCALARMULT ] : x25519_scalarmult_inp → x25519_scalarmult_out
  ] [(ECDH,(ecdh_inp,ecdh_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      group_name_27 , x_28 , y_29) := temp_inp : named_group_t '× dh_sk_t '× dh_pk_t in
    
    let p256_ecdh := fun x_0 x_1 => package_both p256_ecdh (x_0,x_1) in
    let x25519_scalarmult := fun x_0 x_1 => package_both x25519_scalarmult (
      x_0,x_1) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
        fset.fset0) [interface
      #val #[ P256_ECDH ] : p256_ecdh_inp → p256_ecdh_out ;
      #val #[ X25519_SCALARMULT ] : x25519_scalarmult_inp → x25519_scalarmult_out
      ] ((result (crypto_error_t) (key_t)))))in
  both_package' _ _ (ECDH,(ecdh_inp,ecdh_out)) temp_package_both.
Fail Next Obligation.

Notation "'kem_scheme_t'" := (named_group_t) : hacspec_scope.

Notation "'kem_sk_t'" := (byte_seq) : hacspec_scope.

Notation "'kem_pk_t'" := (byte_seq) : hacspec_scope.


Notation "'kem_priv_len_inp'" :=(
  kem_scheme_t : choice_type) (in custom pack_type at level 2).
Notation "'kem_priv_len_inp'" :=(kem_scheme_t : ChoiceEquality) (at level 2).
Notation "'kem_priv_len_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'kem_priv_len_out'" :=(uint_size : ChoiceEquality) (at level 2).
Definition KEM_PRIV_LEN : nat :=
  31.
Program Definition kem_priv_len
  : both_package (fset.fset0) [interface
  #val #[ DH_PRIV_LEN ] : dh_priv_len_inp → dh_priv_len_out ] [(KEM_PRIV_LEN,(
      kem_priv_len_inp,kem_priv_len_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(ks_30) := temp_inp : kem_scheme_t in
    
    let dh_priv_len := fun x_0 => package_both dh_priv_len (x_0) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (dh_priv_len (
            lift_to_both0 ks_30))
        ) : both (fset.fset0) [interface
      #val #[ DH_PRIV_LEN ] : dh_priv_len_inp → dh_priv_len_out ] (
        uint_size)))in
  both_package' _ _ (KEM_PRIV_LEN,(
      kem_priv_len_inp,kem_priv_len_out)) temp_package_both.
Fail Next Obligation.


Notation "'kem_pub_len_inp'" :=(
  kem_scheme_t : choice_type) (in custom pack_type at level 2).
Notation "'kem_pub_len_inp'" :=(kem_scheme_t : ChoiceEquality) (at level 2).
Notation "'kem_pub_len_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'kem_pub_len_out'" :=(uint_size : ChoiceEquality) (at level 2).
Definition KEM_PUB_LEN : nat :=
  33.
Program Definition kem_pub_len
  : both_package (fset.fset0) [interface
  #val #[ DH_PUB_LEN ] : dh_pub_len_inp → dh_pub_len_out ] [(KEM_PUB_LEN,(
      kem_pub_len_inp,kem_pub_len_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(ks_32) := temp_inp : kem_scheme_t in
    
    let dh_pub_len := fun x_0 => package_both dh_pub_len (x_0) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (dh_pub_len (
            lift_to_both0 ks_32))
        ) : both (fset.fset0) [interface
      #val #[ DH_PUB_LEN ] : dh_pub_len_inp → dh_pub_len_out ] (uint_size)))in
  both_package' _ _ (KEM_PUB_LEN,(
      kem_pub_len_inp,kem_pub_len_out)) temp_package_both.
Fail Next Obligation.


Notation "'kem_priv_to_pub_inp'" :=(
  kem_scheme_t '× kem_sk_t : choice_type) (in custom pack_type at level 2).
Notation "'kem_priv_to_pub_inp'" :=(
  kem_scheme_t '× kem_sk_t : ChoiceEquality) (at level 2).
Notation "'kem_priv_to_pub_out'" :=((result (crypto_error_t) (
      kem_pk_t)) : choice_type) (in custom pack_type at level 2).
Notation "'kem_priv_to_pub_out'" :=((result (crypto_error_t) (
      kem_pk_t)) : ChoiceEquality) (at level 2).
Definition KEM_PRIV_TO_PUB : nat :=
  36.
Program Definition kem_priv_to_pub
  : both_package (fset.fset0) [interface
  #val #[ SECRET_TO_PUBLIC ] : secret_to_public_inp → secret_to_public_out
  ] [(KEM_PRIV_TO_PUB,(kem_priv_to_pub_inp,kem_priv_to_pub_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(ks_34 , sk_35) := temp_inp : kem_scheme_t '× kem_sk_t in
    
    let secret_to_public := fun x_0 x_1 => package_both secret_to_public (
      x_0,x_1) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (secret_to_public (
            lift_to_both0 ks_34) (lift_to_both0 sk_35))
        ) : both (fset.fset0) [interface
      #val #[ SECRET_TO_PUBLIC ] : secret_to_public_inp → secret_to_public_out
      ] ((result (crypto_error_t) (kem_pk_t)))))in
  both_package' _ _ (KEM_PRIV_TO_PUB,(
      kem_priv_to_pub_inp,kem_priv_to_pub_out)) temp_package_both.
Fail Next Obligation.


Notation "'kem_keygen_inner_inp'" :=(
  kem_scheme_t '× entropy_t : choice_type) (in custom pack_type at level 2).
Notation "'kem_keygen_inner_inp'" :=(
  kem_scheme_t '× entropy_t : ChoiceEquality) (at level 2).
Notation "'kem_keygen_inner_out'" :=((result (crypto_error_t) ((
        kem_sk_t '×
        kem_pk_t
      ))) : choice_type) (in custom pack_type at level 2).
Notation "'kem_keygen_inner_out'" :=((result (crypto_error_t) ((
        kem_sk_t '×
        kem_pk_t
      ))) : ChoiceEquality) (at level 2).
Definition KEM_KEYGEN_INNER : nat :=
  41.
Program Definition kem_keygen_inner
  : both_package (fset.fset0) [interface
  #val #[ DH_PRIV_LEN ] : dh_priv_len_inp → dh_priv_len_out ;
  #val #[ KEM_PRIV_TO_PUB ] : kem_priv_to_pub_inp → kem_priv_to_pub_out ] [(
    KEM_KEYGEN_INNER,(kem_keygen_inner_inp,kem_keygen_inner_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(ks_38 , ent_37) := temp_inp : kem_scheme_t '× entropy_t in
    
    let dh_priv_len := fun x_0 => package_both dh_priv_len (x_0) in
    let kem_priv_to_pub := fun x_0 x_1 => package_both kem_priv_to_pub (
      x_0,x_1) in
    ((letb sk_39 : seq uint8 :=
          seq_from_seq (seq_slice_range (lift_to_both0 ent_37) (prod_b(
                lift_to_both0 (usize 0),
                dh_priv_len (lift_to_both0 ks_38)
              ))) in
        letbnd(_) pk_40 : kem_pk_t :=
          kem_priv_to_pub (lift_to_both0 ks_38) (lift_to_both0 sk_39) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (
            kem_sk_t '×
            kem_pk_t
          ) crypto_error_t (prod_b(lift_to_both0 sk_39, lift_to_both0 pk_40)))
        ) : both (fset.fset0) [interface
      #val #[ DH_PRIV_LEN ] : dh_priv_len_inp → dh_priv_len_out ;
      #val #[ KEM_PRIV_TO_PUB ] : kem_priv_to_pub_inp → kem_priv_to_pub_out
      ] ((result (crypto_error_t) ((kem_sk_t '× kem_pk_t))))))in
  both_package' _ _ (KEM_KEYGEN_INNER,(
      kem_keygen_inner_inp,kem_keygen_inner_out)) temp_package_both.
Fail Next Obligation.


Notation "'kem_keygen_inp'" :=(
  kem_scheme_t '× entropy_t : choice_type) (in custom pack_type at level 2).
Notation "'kem_keygen_inp'" :=(
  kem_scheme_t '× entropy_t : ChoiceEquality) (at level 2).
Notation "'kem_keygen_out'" :=((result (crypto_error_t) ((kem_sk_t '× kem_pk_t
      ))) : choice_type) (in custom pack_type at level 2).
Notation "'kem_keygen_out'" :=((result (crypto_error_t) ((kem_sk_t '× kem_pk_t
      ))) : ChoiceEquality) (at level 2).
Definition KEM_KEYGEN : nat :=
  44.
Program Definition kem_keygen
  : both_package (fset.fset0) [interface
  #val #[ DH_PRIV_LEN ] : dh_priv_len_inp → dh_priv_len_out ;
  #val #[ KEM_KEYGEN_INNER ] : kem_keygen_inner_inp → kem_keygen_inner_out
  ] [(KEM_KEYGEN,(kem_keygen_inp,kem_keygen_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(ks_43 , ent_42) := temp_inp : kem_scheme_t '× entropy_t in
    
    let dh_priv_len := fun x_0 => package_both dh_priv_len (x_0) in
    let kem_keygen_inner := fun x_0 x_1 => package_both kem_keygen_inner (
      x_0,x_1) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) ((seq_len (lift_to_both0 ent_42)) <.? (
              dh_priv_len (lift_to_both0 ks_43)))
          then @Err (kem_sk_t '× kem_pk_t) crypto_error_t (InsufficientEntropy)
          else kem_keygen_inner (lift_to_both0 ks_43) (lift_to_both0 ent_42))
        ) : both (fset.fset0) [interface
      #val #[ DH_PRIV_LEN ] : dh_priv_len_inp → dh_priv_len_out ;
      #val #[ KEM_KEYGEN_INNER ] : kem_keygen_inner_inp → kem_keygen_inner_out
      ] ((result (crypto_error_t) ((kem_sk_t '× kem_pk_t))))))in
  both_package' _ _ (KEM_KEYGEN,(
      kem_keygen_inp,kem_keygen_out)) temp_package_both.
Fail Next Obligation.


Notation "'kem_encap_inp'" :=(
  kem_scheme_t '× kem_pk_t '× entropy_t : choice_type) (in custom pack_type at level 2).
Notation "'kem_encap_inp'" :=(
  kem_scheme_t '× kem_pk_t '× entropy_t : ChoiceEquality) (at level 2).
Notation "'kem_encap_out'" :=((result (crypto_error_t) ((key_t '× byte_seq
      ))) : choice_type) (in custom pack_type at level 2).
Notation "'kem_encap_out'" :=((result (crypto_error_t) ((key_t '× byte_seq
      ))) : ChoiceEquality) (at level 2).
Definition KEM_ENCAP : nat :=
  51.
Program Definition kem_encap
  : both_package (fset.fset0) [interface
  #val #[ ECDH ] : ecdh_inp → ecdh_out ;
  #val #[ KEM_KEYGEN ] : kem_keygen_inp → kem_keygen_out ] [(KEM_ENCAP,(
      kem_encap_inp,kem_encap_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      ks_45 , pk_49 , ent_46) := temp_inp : kem_scheme_t '× kem_pk_t '× entropy_t in
    
    let ecdh := fun x_0 x_1 x_2 => package_both ecdh (x_0,x_1,x_2) in
    let kem_keygen := fun x_0 x_1 => package_both kem_keygen (x_0,x_1) in
    ((letbnd(_) '(x_47, gx_48) : (kem_sk_t '× kem_pk_t) :=
          kem_keygen (lift_to_both0 ks_45) (lift_to_both0 ent_46) in
        letbnd(_) gxy_50 : key_t :=
          ecdh (lift_to_both0 ks_45) (lift_to_both0 x_47) (
            lift_to_both0 pk_49) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (
            key_t '×
            byte_seq
          ) crypto_error_t (prod_b(lift_to_both0 gxy_50, lift_to_both0 gx_48)))
        ) : both (fset.fset0) [interface
      #val #[ ECDH ] : ecdh_inp → ecdh_out ;
      #val #[ KEM_KEYGEN ] : kem_keygen_inp → kem_keygen_out ] ((result (
            crypto_error_t) ((key_t '× byte_seq))))))in
  both_package' _ _ (KEM_ENCAP,(kem_encap_inp,kem_encap_out)) temp_package_both.
Fail Next Obligation.


Notation "'kem_decap_inp'" :=(
  kem_scheme_t '× byte_seq '× kem_sk_t : choice_type) (in custom pack_type at level 2).
Notation "'kem_decap_inp'" :=(
  kem_scheme_t '× byte_seq '× kem_sk_t : ChoiceEquality) (at level 2).
Notation "'kem_decap_out'" :=((result (crypto_error_t) (
      key_t)) : choice_type) (in custom pack_type at level 2).
Notation "'kem_decap_out'" :=((result (crypto_error_t) (
      key_t)) : ChoiceEquality) (at level 2).
Definition KEM_DECAP : nat :=
  56.
Program Definition kem_decap
  : both_package (fset.fset0) [interface #val #[ ECDH ] : ecdh_inp → ecdh_out
  ] [(KEM_DECAP,(kem_decap_inp,kem_decap_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      ks_52 , ct_54 , sk_53) := temp_inp : kem_scheme_t '× byte_seq '× kem_sk_t in
    
    let ecdh := fun x_0 x_1 x_2 => package_both ecdh (x_0,x_1,x_2) in
    ((letbnd(_) gxy_55 : key_t :=
          ecdh (lift_to_both0 ks_52) (lift_to_both0 sk_53) (
            lift_to_both0 ct_54) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok key_t crypto_error_t (lift_to_both0 gxy_55))
        ) : both (fset.fset0) [interface #val #[ ECDH ] : ecdh_inp → ecdh_out
      ] ((result (crypto_error_t) (key_t)))))in
  both_package' _ _ (KEM_DECAP,(kem_decap_inp,kem_decap_out)) temp_package_both.
Fail Next Obligation.


Notation "'hash_inp'" :=(
  hash_algorithm_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'hash_inp'" :=(
  hash_algorithm_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'hash_out'" :=((result (crypto_error_t) (
      digest_t)) : choice_type) (in custom pack_type at level 2).
Notation "'hash_out'" :=((result (crypto_error_t) (
      digest_t)) : ChoiceEquality) (at level 2).
Definition HASH : nat :=
  57.
Program Definition hash
  : both_package (fset.fset0) [interface
  #val #[ SHA256 ] : sha256_inp → sha256_out ] [(HASH,(hash_inp,hash_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(ha_58 , payload_59) := temp_inp : hash_algorithm_t '× byte_seq in
    
    let sha256 := fun x_0 => package_both sha256 (x_0) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
        fset.fset0) [interface #val #[ SHA256 ] : sha256_inp → sha256_out ] ((
          result (crypto_error_t) (digest_t)))))in
  both_package' _ _ (HASH,(hash_inp,hash_out)) temp_package_both.
Fail Next Obligation.


Notation "'hmac_tag_inp'" :=(
  hash_algorithm_t '× mac_key_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'hmac_tag_inp'" :=(
  hash_algorithm_t '× mac_key_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'hmac_tag_out'" :=((result (crypto_error_t) (
      hmac_t)) : choice_type) (in custom pack_type at level 2).
Notation "'hmac_tag_out'" :=((result (crypto_error_t) (
      hmac_t)) : ChoiceEquality) (at level 2).
Definition HMAC_TAG : nat :=
  60.
Program Definition hmac_tag
  : both_package (fset.fset0) [interface #val #[ HMAC ] : hmac_inp → hmac_out
  ] [(HMAC_TAG,(hmac_tag_inp,hmac_tag_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      ha_61 , mk_62 , payload_63) := temp_inp : hash_algorithm_t '× mac_key_t '× byte_seq in
    
    let hmac := fun x_0 x_1 => package_both hmac (x_0,x_1) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
        fset.fset0) [interface #val #[ HMAC ] : hmac_inp → hmac_out ] ((
          result (crypto_error_t) (hmac_t)))))in
  both_package' _ _ (HMAC_TAG,(hmac_tag_inp,hmac_tag_out)) temp_package_both.
Fail Next Obligation.


Notation "'check_tag_len_inp'" :=(
  hmac_t '× hmac_t : choice_type) (in custom pack_type at level 2).
Notation "'check_tag_len_inp'" :=(
  hmac_t '× hmac_t : ChoiceEquality) (at level 2).
Notation "'check_tag_len_out'" :=((result (crypto_error_t) (
      unit_ChoiceEquality)) : choice_type) (in custom pack_type at level 2).
Notation "'check_tag_len_out'" :=((result (crypto_error_t) (
      unit_ChoiceEquality)) : ChoiceEquality) (at level 2).
Definition CHECK_TAG_LEN : nat :=
  66.
Program Definition check_tag_len
  : both_package (fset.fset0) [interface] [(CHECK_TAG_LEN,(
      check_tag_len_inp,check_tag_len_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(a_64 , b_65) := temp_inp : hmac_t '× hmac_t in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) ((seq_len (lift_to_both0 a_64)) =.? (
              seq_len (lift_to_both0 b_65)))
          then @Ok unit_ChoiceEquality crypto_error_t (tt)
          else @Err unit_ChoiceEquality crypto_error_t (MacFailed))
        ) : both (fset.fset0) [interface] ((result (crypto_error_t) (
            unit_ChoiceEquality)))))in
  both_package' _ _ (CHECK_TAG_LEN,(
      check_tag_len_inp,check_tag_len_out)) temp_package_both.
Fail Next Obligation.


Notation "'check_bytes_inp'" :=(
  uint8 '× uint8 : choice_type) (in custom pack_type at level 2).
Notation "'check_bytes_inp'" :=(uint8 '× uint8 : ChoiceEquality) (at level 2).
Notation "'check_bytes_out'" :=((result (crypto_error_t) (
      unit_ChoiceEquality)) : choice_type) (in custom pack_type at level 2).
Notation "'check_bytes_out'" :=((result (crypto_error_t) (
      unit_ChoiceEquality)) : ChoiceEquality) (at level 2).
Definition CHECK_BYTES : nat :=
  69.
Program Definition check_bytes
  : both_package (fset.fset0) [interface] [(CHECK_BYTES,(
      check_bytes_inp,check_bytes_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(a_67 , b_68) := temp_inp : uint8 '× uint8 in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) (negb (uint8_equal (
                lift_to_both0 a_67) (lift_to_both0 b_68)))
          then @Err unit_ChoiceEquality crypto_error_t (MacFailed)
          else @Ok unit_ChoiceEquality crypto_error_t (tt))
        ) : both (fset.fset0) [interface] ((result (crypto_error_t) (
            unit_ChoiceEquality)))))in
  both_package' _ _ (CHECK_BYTES,(
      check_bytes_inp,check_bytes_out)) temp_package_both.
Fail Next Obligation.


Notation "'hmac_verify_inp'" :=(
  hash_algorithm_t '× mac_key_t '× byte_seq '× hmac_t : choice_type) (in custom pack_type at level 2).
Notation "'hmac_verify_inp'" :=(
  hash_algorithm_t '× mac_key_t '× byte_seq '× hmac_t : ChoiceEquality) (at level 2).
Notation "'hmac_verify_out'" :=((result (crypto_error_t) (
      unit_ChoiceEquality)) : choice_type) (in custom pack_type at level 2).
Notation "'hmac_verify_out'" :=((result (crypto_error_t) (
      unit_ChoiceEquality)) : ChoiceEquality) (at level 2).
Definition HMAC_VERIFY : nat :=
  76.
Program Definition hmac_verify
  : both_package (fset.fset0) [interface
  #val #[ CHECK_BYTES ] : check_bytes_inp → check_bytes_out ;
  #val #[ CHECK_TAG_LEN ] : check_tag_len_inp → check_tag_len_out ;
  #val #[ HMAC_TAG ] : hmac_tag_inp → hmac_tag_out ] [(HMAC_VERIFY,(
      hmac_verify_inp,hmac_verify_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      ha_70 , mk_71 , payload_72 , m_74) := temp_inp : hash_algorithm_t '× mac_key_t '× byte_seq '× hmac_t in
    
    let check_bytes := fun x_0 x_1 => package_both check_bytes (x_0,x_1) in
    let check_tag_len := fun x_0 x_1 => package_both check_tag_len (x_0,x_1) in
    let hmac_tag := fun x_0 x_1 x_2 => package_both hmac_tag (x_0,x_1,x_2) in
    ((letbnd(_) my_hmac_73 : hmac_t :=
          hmac_tag (lift_to_both0 ha_70) (lift_to_both0 mk_71) (
            lift_to_both0 payload_72) in
        letbnd(_) _ : unit_ChoiceEquality :=
          check_tag_len (lift_to_both0 m_74) (lift_to_both0 my_hmac_73) in
        letbnd(_) 'tt :=
          foldi_bind_both' (lift_to_both0 (usize 0)) (seq_len (
                lift_to_both0 m_74)) prod_cett (L := (fset.fset0)) (I := (
              [interface
              #val #[ CHECK_BYTES ] : check_bytes_inp → check_bytes_out ;
              #val #[ CHECK_TAG_LEN ] : check_tag_len_inp → check_tag_len_out ;
              #val #[ HMAC_TAG ] : hmac_tag_inp → hmac_tag_out
              ])) (fun i_75 'tt =>
            letbnd(_) _ : unit_ChoiceEquality :=
              check_bytes (seq_index (my_hmac_73) (lift_to_both0 i_75)) (
                seq_index (m_74) (lift_to_both0 i_75)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              @Ok unit_ChoiceEquality crypto_error_t (lift_to_both0 (
                  (tt : unit_ChoiceEquality))))
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok unit_ChoiceEquality crypto_error_t (tt))
        ) : both (fset.fset0) [interface
      #val #[ CHECK_BYTES ] : check_bytes_inp → check_bytes_out ;
      #val #[ CHECK_TAG_LEN ] : check_tag_len_inp → check_tag_len_out ;
      #val #[ HMAC_TAG ] : hmac_tag_inp → hmac_tag_out ] ((result (
            crypto_error_t) (unit_ChoiceEquality)))))in
  both_package' _ _ (HMAC_VERIFY,(
      hmac_verify_inp,hmac_verify_out)) temp_package_both.
Fail Next Obligation.

Definition ec_oid_tag_t := nseq (uint8) (usize 9).


Notation "'get_length_length_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'get_length_length_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'get_length_length_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'get_length_length_out'" :=(uint_size : ChoiceEquality) (at level 2).
Definition GET_LENGTH_LENGTH : nat :=
  78.
Program Definition get_length_length
  : both_package (fset.fset0) [interface] [(GET_LENGTH_LENGTH,(
      get_length_length_inp,get_length_length_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(b_77) := temp_inp : byte_seq in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) (((uint8_declassify (seq_index (b_77) (
                    lift_to_both0 (usize 0)))) shift_right (lift_to_both0 (
                  usize 7))) =.? (lift_to_both0 (@repr U8 1)))
          then declassify_usize_from_uint8 ((seq_index (b_77) (lift_to_both0 (
                  usize 0))) .& (secret (lift_to_both0 (@repr U8 127))))
          else lift_to_both0 (usize 0))
        ) : both (fset.fset0) [interface] (uint_size)))in
  both_package' _ _ (GET_LENGTH_LENGTH,(
      get_length_length_inp,get_length_length_out)) temp_package_both.
Fail Next Obligation.


Notation "'get_length_inp'" :=(
  byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'get_length_inp'" :=(
  byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'get_length_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'get_length_out'" :=(uint_size : ChoiceEquality) (at level 2).
Definition GET_LENGTH : nat :=
  81.
Program Definition get_length
  : both_package (fset.fset0) [interface
  #val #[ DECLASSIFY_U32_FROM_U32 ] : declassify_u32_from_uint32_inp → declassify_u32_from_uint32_out
  ] [(GET_LENGTH,(get_length_inp,get_length_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(b_79 , len_80) := temp_inp : byte_seq '× uint_size in
    
    let declassify_u32_from_uint32 := fun x_0 => package_both declassify_u32_from_uint32 (
      x_0) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((@cast _ uint32 _ (
              declassify_u32_from_uint32 (uint32_from_be_bytes (
                  array_from_slice (default : uint8) (4) (lift_to_both0 b_79) (
                    lift_to_both0 (usize 0)) (
                    lift_to_both0 len_80))))) usize_shift_right (((
                lift_to_both0 (usize 4)) .- (lift_to_both0 len_80)) .* (
              lift_to_both0 (usize 8))))
        ) : both (fset.fset0) [interface
      #val #[ DECLASSIFY_U32_FROM_U32 ] : declassify_u32_from_uint32_inp → declassify_u32_from_uint32_out
      ] (uint_size)))in
  both_package' _ _ (GET_LENGTH,(
      get_length_inp,get_length_out)) temp_package_both.
Fail Next Obligation.


Notation "'get_short_length_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'get_short_length_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'get_short_length_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'get_short_length_out'" :=(uint_size : ChoiceEquality) (at level 2).
Definition GET_SHORT_LENGTH : nat :=
  83.
Program Definition get_short_length
  : both_package (fset.fset0) [interface] [(GET_SHORT_LENGTH,(
      get_short_length_inp,get_short_length_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(b_82) := temp_inp : byte_seq in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          declassify_usize_from_uint8 ((seq_index (b_82) (lift_to_both0 (
                  usize 0))) .& (secret (lift_to_both0 (@repr U8 127)))))
        ) : both (fset.fset0) [interface] (uint_size)))in
  both_package' _ _ (GET_SHORT_LENGTH,(
      get_short_length_inp,get_short_length_out)) temp_package_both.
Fail Next Obligation.

Definition len_86_loc : ChoiceEqualityLocation :=
  (uint_size ; 88%nat).
Definition ec_pk_oid_87_loc : ChoiceEqualityLocation :=
  (bool_ChoiceEquality ; 89%nat).
Definition seq1_84_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 90%nat).
Definition pk_85_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 91%nat).
Notation "'verification_key_from_cert_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'verification_key_from_cert_inp'" :=(
  byte_seq : ChoiceEquality) (at level 2).
Notation "'verification_key_from_cert_out'" :=((result (crypto_error_t) (
      verification_key_t)) : choice_type) (in custom pack_type at level 2).
Notation "'verification_key_from_cert_out'" :=((result (crypto_error_t) (
      verification_key_t)) : ChoiceEquality) (at level 2).
Definition VERIFICATION_KEY_FROM_CERT : nat :=
  113.
Program Definition verification_key_from_cert
  : both_package (CEfset (
      [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) [interface
  #val #[ GET_LENGTH ] : get_length_inp → get_length_out ;
  #val #[ GET_LENGTH_LENGTH ] : get_length_length_inp → get_length_length_out ;
  #val #[ GET_SHORT_LENGTH ] : get_short_length_inp → get_short_length_out
  ] [(VERIFICATION_KEY_FROM_CERT,(
      verification_key_from_cert_inp,verification_key_from_cert_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(cert_92) := temp_inp : byte_seq in
    
    let get_length := fun x_0 x_1 => package_both get_length (x_0,x_1) in
    let get_length_length := fun x_0 => package_both get_length_length (x_0) in
    let get_short_length := fun x_0 => package_both get_short_length (x_0) in
    ((letb skip_93 : uint_size :=
          ((lift_to_both0 (usize 2)) .+ (get_length_length (seq_slice_range (
                  lift_to_both0 cert_92) (prod_b(
                    lift_to_both0 (usize 1),
                    seq_len (lift_to_both0 cert_92)
                  ))))) .+ (lift_to_both0 (usize 1)) in
        letb seq1_len_len_94 : uint_size :=
          get_length_length (seq_slice_range (lift_to_both0 cert_92) (prod_b(
                lift_to_both0 skip_93,
                seq_len (lift_to_both0 cert_92)
              ))) in
        letb skip_95 : uint_size :=
          (lift_to_both0 skip_93) .+ (lift_to_both0 (usize 1)) in
        letb seq1_len_96 : uint_size :=
          get_length (seq_slice (lift_to_both0 cert_92) (
              lift_to_both0 skip_95) ((seq_len (lift_to_both0 cert_92)) .- (
                lift_to_both0 skip_95))) (lift_to_both0 seq1_len_len_94) in
        letbm seq1_84 : seq uint8 loc( seq1_84_loc ) :=
          seq_slice_range (lift_to_both0 cert_92) (prod_b(
              (lift_to_both0 skip_95) .+ (lift_to_both0 seq1_len_len_94),
              ((lift_to_both0 skip_95) .+ (lift_to_both0 seq1_len_len_94)) .+ (
                lift_to_both0 seq1_len_96)
            )) in
        letbm pk_85 : seq uint8 loc( pk_85_loc ) :=
          seq_new_ (default : uint8) (lift_to_both0 (usize 0)) in
        letb '(seq1_84, pk_85) :=
          foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                lift_to_both0 seq1_84)) prod_ce(seq1_84, pk_85) (L := (CEfset (
                [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc]))) (I := (
              [interface
              #val #[ GET_LENGTH ] : get_length_inp → get_length_out ;
              #val #[ GET_LENGTH_LENGTH ] : get_length_length_inp → get_length_length_out ;
              #val #[ GET_SHORT_LENGTH ] : get_short_length_inp → get_short_length_out
              ])) (fun i_97 '(seq1_84, pk_85) =>
            letb '(seq1_84, pk_85) :=
              if (seq_len (lift_to_both0 seq1_84)) >.? (lift_to_both0 (
                  usize 0)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (L2 := CEfset (
                [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (I1 := [interface
              #val #[ GET_LENGTH ] : get_length_inp → get_length_out ;
              #val #[ GET_LENGTH_LENGTH ] : get_length_length_inp → get_length_length_out ;
              #val #[ GET_SHORT_LENGTH ] : get_short_length_inp → get_short_length_out
              ]) (I2 := [interface
              #val #[ GET_LENGTH ] : get_length_inp → get_length_out ;
              #val #[ GET_LENGTH_LENGTH ] : get_length_length_inp → get_length_length_out ;
              #val #[ GET_SHORT_LENGTH ] : get_short_length_inp → get_short_length_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb element_type_98 : int8 :=
                  uint8_declassify (seq_index (seq1_84) (lift_to_both0 (
                        usize 0))) in
                letbm seq1_84 loc( seq1_84_loc ) :=
                  seq_slice (lift_to_both0 seq1_84) (lift_to_both0 (usize 1)) ((
                      seq_len (lift_to_both0 seq1_84)) .- (lift_to_both0 (
                        usize 1))) in
                letb len_len_99 : uint_size :=
                  get_length_length (lift_to_both0 seq1_84) in
                letbm len_86 : uint_size loc( len_86_loc ) :=
                  get_short_length (lift_to_both0 seq1_84) in
                letbm seq1_84 loc( seq1_84_loc ) :=
                  seq_slice (lift_to_both0 seq1_84) (lift_to_both0 (usize 1)) ((
                      seq_len (lift_to_both0 seq1_84)) .- (lift_to_both0 (
                        usize 1))) in
                letb 'len_86 :=
                  if (lift_to_both0 len_len_99) !=.? (lift_to_both0 (
                      usize 0)) :bool_ChoiceEquality
                  then lift_scope (L1 := CEfset (
                    [seq1_84_loc ; pk_85_loc ; len_86_loc])) (L2 := CEfset (
                    [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (I1 := [interface
                  #val #[ GET_LENGTH ] : get_length_inp → get_length_out
                  ]) (I2 := [interface
                  #val #[ GET_LENGTH ] : get_length_inp → get_length_out ;
                  #val #[ GET_LENGTH_LENGTH ] : get_length_length_inp → get_length_length_out ;
                  #val #[ GET_SHORT_LENGTH ] : get_short_length_inp → get_short_length_out
                  ]) (H_loc_incl := _) (H_opsig_incl := _) (
                    letbm len_86 loc( len_86_loc ) :=
                      (get_length (lift_to_both0 seq1_84) (
                          lift_to_both0 len_len_99)) .+ (
                        lift_to_both0 len_len_99) in
                    lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                      lift_to_both0 len_86)
                    )
                  else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                    lift_to_both0 len_86)
                   in
                letb 'pk_85 :=
                  if ((lift_to_both0 element_type_98) =.? (lift_to_both0 (
                        @repr U8 48))) && ((seq_len (lift_to_both0 pk_85)) =.? (
                      lift_to_both0 (usize 0))) :bool_ChoiceEquality
                  then lift_scope (L1 := CEfset (
                    [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (L2 := CEfset (
                    [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (I1 := [interface
                  #val #[ GET_LENGTH_LENGTH ] : get_length_length_inp → get_length_length_out ;
                  #val #[ GET_SHORT_LENGTH ] : get_short_length_inp → get_short_length_out
                  ]) (I2 := [interface
                  #val #[ GET_LENGTH ] : get_length_inp → get_length_out ;
                  #val #[ GET_LENGTH_LENGTH ] : get_length_length_inp → get_length_length_out ;
                  #val #[ GET_SHORT_LENGTH ] : get_short_length_inp → get_short_length_out
                  ]) (H_loc_incl := _) (H_opsig_incl := _) (
                    letb seq2_100 : seq uint8 :=
                      seq_slice (lift_to_both0 seq1_84) (
                        lift_to_both0 len_len_99) (lift_to_both0 len_86) in
                    letb element_type_101 : int8 :=
                      uint8_declassify (seq_index (seq2_100) (lift_to_both0 (
                            usize 0))) in
                    letb seq2_102 : seq uint8 :=
                      seq_slice (lift_to_both0 seq2_100) (lift_to_both0 (
                          usize 1)) ((seq_len (lift_to_both0 seq2_100)) .- (
                          lift_to_both0 (usize 1))) in
                    letb 'pk_85 :=
                      if (lift_to_both0 element_type_101) =.? (lift_to_both0 (
                          @repr U8 48)) :bool_ChoiceEquality
                      then lift_scope (L1 := CEfset (
                        [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (L2 := CEfset (
                        [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (I1 := [interface
                      #val #[ GET_LENGTH_LENGTH ] : get_length_length_inp → get_length_length_out ;
                      #val #[ GET_SHORT_LENGTH ] : get_short_length_inp → get_short_length_out
                      ]) (I2 := [interface
                      #val #[ GET_LENGTH_LENGTH ] : get_length_length_inp → get_length_length_out ;
                      #val #[ GET_SHORT_LENGTH ] : get_short_length_inp → get_short_length_out
                      ]) (H_loc_incl := _) (H_opsig_incl := _) (
                        letb len_len_103 : uint_size :=
                          get_length_length (lift_to_both0 seq2_102) in
                        letb 'pk_85 :=
                          if (lift_to_both0 len_len_103) =.? (lift_to_both0 (
                              usize 0)) :bool_ChoiceEquality
                          then lift_scope (L1 := CEfset (
                            [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (L2 := CEfset (
                            [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (I1 := [interface
                          #val #[ GET_SHORT_LENGTH ] : get_short_length_inp → get_short_length_out
                          ]) (I2 := [interface
                          #val #[ GET_LENGTH_LENGTH ] : get_length_length_inp → get_length_length_out ;
                          #val #[ GET_SHORT_LENGTH ] : get_short_length_inp → get_short_length_out
                          ]) (H_loc_incl := _) (H_opsig_incl := _) (
                            letb oid_len_104 : uint_size :=
                              get_short_length (lift_to_both0 seq2_102) in
                            letb 'pk_85 :=
                              if (lift_to_both0 oid_len_104) >=.? (
                                lift_to_both0 (usize 9)) :bool_ChoiceEquality
                              then lift_scope (L1 := CEfset (
                                [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (L2 := CEfset (
                                [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (I1 := [interface]) (I2 := [interface
                              #val #[ GET_SHORT_LENGTH ] : get_short_length_inp → get_short_length_out
                              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                                letb expected_105 : seq uint8 :=
                                  seq_from_seq (
                                    array_to_seq (array_from_list uint8 ([
                                        (secret (lift_to_both0 (
                                              @repr U8 6))) : uint8;
                                        (secret (lift_to_both0 (
                                              @repr U8 7))) : uint8;
                                        (secret (lift_to_both0 (
                                              @repr U8 42))) : uint8;
                                        (secret (lift_to_both0 (
                                              @repr U8 134))) : uint8;
                                        (secret (lift_to_both0 (
                                              @repr U8 72))) : uint8;
                                        (secret (lift_to_both0 (
                                              @repr U8 206))) : uint8;
                                        (secret (lift_to_both0 (
                                              @repr U8 61))) : uint8;
                                        (secret (lift_to_both0 (
                                              @repr U8 2))) : uint8;
                                        (secret (lift_to_both0 (
                                              @repr U8 1))) : uint8
                                      ]))) in
                                letb oid_106 : seq uint8 :=
                                  seq_slice (lift_to_both0 seq2_102) (
                                    lift_to_both0 (usize 1)) (lift_to_both0 (
                                      usize 9)) in
                                letbm ec_pk_oid_87 : bool_ChoiceEquality loc( ec_pk_oid_87_loc ) :=
                                  lift_to_both0 (
                                    (true : bool_ChoiceEquality)) in
                                letb ec_pk_oid_87 :=
                                  foldi_both' (lift_to_both0 (usize 0)) (
                                      lift_to_both0 (
                                        usize 9)) ec_pk_oid_87 (L := (CEfset (
                                        [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc]))) (I := (
                                      [interface])) (fun i_107 ec_pk_oid_87 =>
                                    letb oid_byte_equal_108 : bool_ChoiceEquality :=
                                      (uint8_declassify (seq_index (oid_106) (
                                            lift_to_both0 i_107))) =.? (
                                        uint8_declassify (seq_index (
                                            expected_105) (
                                            lift_to_both0 i_107))) in
                                    letbm ec_pk_oid_87 loc( ec_pk_oid_87_loc ) :=
                                      (lift_to_both0 ec_pk_oid_87) && (
                                        lift_to_both0 oid_byte_equal_108) in
                                    lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                                      lift_to_both0 ec_pk_oid_87)
                                    ) in
                                letb 'pk_85 :=
                                  if lift_to_both0 ec_pk_oid_87 :bool_ChoiceEquality
                                  then lift_scope (L1 := CEfset (
                                    [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (L2 := CEfset (
                                    [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (I1 := [interface]) (I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                                    letb bit_string_109 : seq uint8 :=
                                      seq_slice (lift_to_both0 seq2_102) ((
                                          lift_to_both0 oid_len_104) .+ (
                                          lift_to_both0 (usize 1))) (((seq_len (
                                              lift_to_both0 seq2_102)) .- (
                                            lift_to_both0 oid_len_104)) .- (
                                          lift_to_both0 (usize 1))) in
                                    letb 'pk_85 :=
                                      if (uint8_declassify (seq_index (
                                            bit_string_109) (lift_to_both0 (
                                              usize 0)))) =.? (lift_to_both0 (
                                          @repr U8 3)) :bool_ChoiceEquality
                                      then lift_scope (L1 := CEfset (
                                        [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (L2 := CEfset (
                                        [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (I1 := [interface]) (I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                                        letb pk_len_110 : uint_size :=
                                          declassify_usize_from_uint8 (
                                            seq_index (bit_string_109) (
                                              lift_to_both0 (usize 1))) in
                                        letb zeroes_111 : uint_size :=
                                          declassify_usize_from_uint8 (
                                            seq_index (bit_string_109) (
                                              lift_to_both0 (usize 2))) in
                                        letb uncompressed_112 : uint_size :=
                                          declassify_usize_from_uint8 (
                                            seq_index (bit_string_109) (
                                              lift_to_both0 (usize 3))) in
                                        letbm pk_85 loc( pk_85_loc ) :=
                                          seq_slice (
                                            lift_to_both0 bit_string_109) (
                                            lift_to_both0 (usize 4)) ((
                                              lift_to_both0 pk_len_110) .- (
                                              lift_to_both0 (usize 2))) in
                                        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                                          lift_to_both0 pk_85)
                                        )
                                      else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                                        lift_to_both0 pk_85)
                                       in
                                    lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                                      lift_to_both0 pk_85)
                                    )
                                  else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                                    lift_to_both0 pk_85)
                                   in
                                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                                  lift_to_both0 pk_85)
                                )
                              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                                lift_to_both0 pk_85)
                               in
                            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                              lift_to_both0 pk_85)
                            )
                          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                            lift_to_both0 pk_85)
                           in
                        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                          lift_to_both0 pk_85)
                        )
                      else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                        lift_to_both0 pk_85)
                       in
                    lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                      lift_to_both0 pk_85)
                    )
                  else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                    lift_to_both0 pk_85)
                   in
                letbm seq1_84 loc( seq1_84_loc ) :=
                  seq_slice (lift_to_both0 seq1_84) (lift_to_both0 len_86) ((
                      seq_len (lift_to_both0 seq1_84)) .- (
                      lift_to_both0 len_86)) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 seq1_84,
                    lift_to_both0 pk_85
                  ))
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                  lift_to_both0 seq1_84,
                  lift_to_both0 pk_85
                ))
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 seq1_84,
                lift_to_both0 pk_85
              ))
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) ((seq_len (lift_to_both0 pk_85)) =.? (
              lift_to_both0 (usize 0)))
          then @Err verification_key_t crypto_error_t (InvalidCert)
          else @Ok verification_key_t crypto_error_t (lift_to_both0 pk_85))
        ) : both (CEfset (
          [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) [interface
      #val #[ GET_LENGTH ] : get_length_inp → get_length_out ;
      #val #[ GET_LENGTH_LENGTH ] : get_length_length_inp → get_length_length_out ;
      #val #[ GET_SHORT_LENGTH ] : get_short_length_inp → get_short_length_out
      ] ((result (crypto_error_t) (verification_key_t)))))in
  both_package' _ _ (VERIFICATION_KEY_FROM_CERT,(
      verification_key_from_cert_inp,verification_key_from_cert_out)) temp_package_both.
Fail Next Obligation.


Notation "'concat_signature_inp'" :=(
  p256_scalar_t '× p256_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'concat_signature_inp'" :=(
  p256_scalar_t '× p256_scalar_t : ChoiceEquality) (at level 2).
Notation "'concat_signature_out'" :=((result (crypto_error_t) (
      signature_t)) : choice_type) (in custom pack_type at level 2).
Notation "'concat_signature_out'" :=((result (crypto_error_t) (
      signature_t)) : ChoiceEquality) (at level 2).
Definition CONCAT_SIGNATURE : nat :=
  117.
Program Definition concat_signature
  : both_package (fset.fset0) [interface] [(CONCAT_SIGNATURE,(
      concat_signature_inp,concat_signature_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(r_114 , s_115) := temp_inp : p256_scalar_t '× p256_scalar_t in
    
    ((letb signature_116 : seq uint8 :=
          seq_concat (seq_concat (seq_new_ (default : uint8) (lift_to_both0 (
                  usize 0))) (nat_mod_to_byte_seq_be (lift_to_both0 r_114))) (
            nat_mod_to_byte_seq_be (lift_to_both0 s_115)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok signature_t crypto_error_t (lift_to_both0 signature_116))
        ) : both (fset.fset0) [interface] ((result (crypto_error_t) (
            signature_t)))))in
  both_package' _ _ (CONCAT_SIGNATURE,(
      concat_signature_inp,concat_signature_out)) temp_package_both.
Fail Next Obligation.


Notation "'p256_sign_inp'" :=(
  signature_key_t '× byte_seq '× entropy_t : choice_type) (in custom pack_type at level 2).
Notation "'p256_sign_inp'" :=(
  signature_key_t '× byte_seq '× entropy_t : ChoiceEquality) (at level 2).
Notation "'p256_sign_out'" :=((result (crypto_error_t) (
      signature_t)) : choice_type) (in custom pack_type at level 2).
Notation "'p256_sign_out'" :=((result (crypto_error_t) (
      signature_t)) : ChoiceEquality) (at level 2).
Definition P256_SIGN : nat :=
  121.
Program Definition p256_sign
  : both_package (fset.fset0) [interface
  #val #[ CONCAT_SIGNATURE ] : concat_signature_inp → concat_signature_out ;
  #val #[ ECDSA_P256_SHA256_SIGN ] : ecdsa_p256_sha256_sign_inp → ecdsa_p256_sha256_sign_out
  ] [(P256_SIGN,(p256_sign_inp,p256_sign_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      ps_122 , payload_123 , ent_118) := temp_inp : signature_key_t '× byte_seq '× entropy_t in
    
    let concat_signature := fun x_0 x_1 => package_both concat_signature (
      x_0,x_1) in
    let ecdsa_p256_sha256_sign := fun x_0 x_1 x_2 => package_both ecdsa_p256_sha256_sign (
      x_0,x_1,x_2) in
    ((letb random_119 : random_t :=
          array_from_seq (32) (seq_slice_range (lift_to_both0 ent_118) (prod_b(
                lift_to_both0 (usize 0),
                lift_to_both0 (usize 32)
              ))) in
        letb nonce_120 : p256_scalar_t :=
          nat_mod_from_byte_seq_be (array_to_seq (lift_to_both0 random_119)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match)
        ) : both (fset.fset0) [interface
      #val #[ CONCAT_SIGNATURE ] : concat_signature_inp → concat_signature_out ;
      #val #[ ECDSA_P256_SHA256_SIGN ] : ecdsa_p256_sha256_sign_inp → ecdsa_p256_sha256_sign_out
      ] ((result (crypto_error_t) (signature_t)))))in
  both_package' _ _ (P256_SIGN,(p256_sign_inp,p256_sign_out)) temp_package_both.
Fail Next Obligation.


Notation "'sign_inp'" :=(
  signature_scheme_t '× signature_key_t '× byte_seq '× entropy_t : choice_type) (in custom pack_type at level 2).
Notation "'sign_inp'" :=(
  signature_scheme_t '× signature_key_t '× byte_seq '× entropy_t : ChoiceEquality) (at level 2).
Notation "'sign_out'" :=((result (crypto_error_t) (
      signature_t)) : choice_type) (in custom pack_type at level 2).
Notation "'sign_out'" :=((result (crypto_error_t) (
      signature_t)) : ChoiceEquality) (at level 2).
Definition SIGN : nat :=
  124.
Program Definition sign
  : both_package (fset.fset0) [interface
  #val #[ P256_SIGN ] : p256_sign_inp → p256_sign_out ] [(SIGN,(
      sign_inp,sign_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      sa_125 , ps_126 , payload_127 , ent_128) := temp_inp : signature_scheme_t '× signature_key_t '× byte_seq '× entropy_t in
    
    let p256_sign := fun x_0 x_1 x_2 => package_both p256_sign (x_0,x_1,x_2) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
        fset.fset0) [interface
      #val #[ P256_SIGN ] : p256_sign_inp → p256_sign_out ] ((result (
            crypto_error_t) (signature_t)))))in
  both_package' _ _ (SIGN,(sign_inp,sign_out)) temp_package_both.
Fail Next Obligation.


Notation "'p256_verify_inp'" :=(
  verification_key_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'p256_verify_inp'" :=(
  verification_key_t '× byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'p256_verify_out'" :=((result (crypto_error_t) (
      unit_ChoiceEquality)) : choice_type) (in custom pack_type at level 2).
Notation "'p256_verify_out'" :=((result (crypto_error_t) (
      unit_ChoiceEquality)) : ChoiceEquality) (at level 2).
Definition P256_VERIFY : nat :=
  135.
Program Definition p256_verify
  : both_package (fset.fset0) [interface
  #val #[ ECDSA_P256_SHA256_VERIFY ] : ecdsa_p256_sha256_verify_inp → ecdsa_p256_sha256_verify_out
  ] [(P256_VERIFY,(p256_verify_inp,p256_verify_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      pk_129 , payload_136 , sig_132) := temp_inp : verification_key_t '× byte_seq '× byte_seq in
    
    let ecdsa_p256_sha256_verify := fun x_0 x_1 x_2 => package_both ecdsa_p256_sha256_verify (
      x_0,x_1,x_2) in
    ((letb '(pk_x_130, pk_y_131) : (
            p256_field_element_t '×
            p256_field_element_t
          ) :=
          prod_b(
            nat_mod_from_byte_seq_be (seq_slice (lift_to_both0 pk_129) (
                lift_to_both0 (usize 0)) (lift_to_both0 (usize 32))),
            nat_mod_from_byte_seq_be (seq_slice (lift_to_both0 pk_129) (
                lift_to_both0 (usize 32)) (lift_to_both0 (usize 32)))
          ) in
        letb '(r_133, s_134) : (p256_scalar_t '× p256_scalar_t) :=
          prod_b(
            nat_mod_from_byte_seq_be (seq_slice (lift_to_both0 sig_132) (
                lift_to_both0 (usize 0)) (lift_to_both0 (usize 32))),
            nat_mod_from_byte_seq_be (seq_slice (lift_to_both0 sig_132) (
                lift_to_both0 (usize 32)) (lift_to_both0 (usize 32)))
          ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match)
        ) : both (fset.fset0) [interface
      #val #[ ECDSA_P256_SHA256_VERIFY ] : ecdsa_p256_sha256_verify_inp → ecdsa_p256_sha256_verify_out
      ] ((result (crypto_error_t) (unit_ChoiceEquality)))))in
  both_package' _ _ (P256_VERIFY,(
      p256_verify_inp,p256_verify_out)) temp_package_both.
Fail Next Obligation.


Notation "'verify_inp'" :=(
  signature_scheme_t '× verification_key_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'verify_inp'" :=(
  signature_scheme_t '× verification_key_t '× byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'verify_out'" :=((result (crypto_error_t) (
      unit_ChoiceEquality)) : choice_type) (in custom pack_type at level 2).
Notation "'verify_out'" :=((result (crypto_error_t) (
      unit_ChoiceEquality)) : ChoiceEquality) (at level 2).
Definition VERIFY : nat :=
  137.
Program Definition verify
  : both_package (fset.fset0) [interface
  #val #[ P256_VERIFY ] : p256_verify_inp → p256_verify_out ] [(VERIFY,(
      verify_inp,verify_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      sa_138 , pk_139 , payload_140 , sig_141) := temp_inp : signature_scheme_t '× verification_key_t '× byte_seq '× byte_seq in
    
    let p256_verify := fun x_0 x_1 x_2 => package_both p256_verify (
      x_0,x_1,x_2) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
        fset.fset0) [interface
      #val #[ P256_VERIFY ] : p256_verify_inp → p256_verify_out ] ((result (
            crypto_error_t) (unit_ChoiceEquality)))))in
  both_package' _ _ (VERIFY,(verify_inp,verify_out)) temp_package_both.
Fail Next Obligation.


Notation "'hkdf_extract_inp'" :=(
  hash_algorithm_t '× key_t '× key_t : choice_type) (in custom pack_type at level 2).
Notation "'hkdf_extract_inp'" :=(
  hash_algorithm_t '× key_t '× key_t : ChoiceEquality) (at level 2).
Notation "'hkdf_extract_out'" :=((result (crypto_error_t) (
      key_t)) : choice_type) (in custom pack_type at level 2).
Notation "'hkdf_extract_out'" :=((result (crypto_error_t) (
      key_t)) : ChoiceEquality) (at level 2).
Definition HKDF_EXTRACT : nat :=
  142.
Program Definition hkdf_extract
  : both_package (fset.fset0) [interface
  #val #[ EXTRACT ] : extract_inp → extract_out ] [(HKDF_EXTRACT,(
      hkdf_extract_inp,hkdf_extract_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      ha_143 , k_144 , salt_145) := temp_inp : hash_algorithm_t '× key_t '× key_t in
    
    let extract := fun x_0 x_1 => package_both extract (x_0,x_1) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
        fset.fset0) [interface #val #[ EXTRACT ] : extract_inp → extract_out
      ] ((result (crypto_error_t) (key_t)))))in
  both_package' _ _ (HKDF_EXTRACT,(
      hkdf_extract_inp,hkdf_extract_out)) temp_package_both.
Fail Next Obligation.


Notation "'hkdf_expand_inp'" :=(
  hash_algorithm_t '× key_t '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'hkdf_expand_inp'" :=(
  hash_algorithm_t '× key_t '× byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'hkdf_expand_out'" :=((result (crypto_error_t) (
      key_t)) : choice_type) (in custom pack_type at level 2).
Notation "'hkdf_expand_out'" :=((result (crypto_error_t) (
      key_t)) : ChoiceEquality) (at level 2).
Definition HKDF_EXPAND : nat :=
  146.
Program Definition hkdf_expand
  : both_package (fset.fset0) [interface
  #val #[ EXPAND ] : expand_inp → expand_out ] [(HKDF_EXPAND,(
      hkdf_expand_inp,hkdf_expand_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      ha_147 , k_148 , info_149 , len_150) := temp_inp : hash_algorithm_t '× key_t '× byte_seq '× uint_size in
    
    let expand := fun x_0 x_1 x_2 => package_both expand (x_0,x_1,x_2) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
        fset.fset0) [interface #val #[ EXPAND ] : expand_inp → expand_out ] ((
          result (crypto_error_t) (key_t)))))in
  both_package' _ _ (HKDF_EXPAND,(
      hkdf_expand_inp,hkdf_expand_out)) temp_package_both.
Fail Next Obligation.


Notation "'aes128_encrypt_inp'" :=(
  aead_key_t '× aead_iv_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'aes128_encrypt_inp'" :=(
  aead_key_t '× aead_iv_t '× byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'aes128_encrypt_out'" :=((result (crypto_error_t) (
      byte_seq)) : choice_type) (in custom pack_type at level 2).
Notation "'aes128_encrypt_out'" :=((result (crypto_error_t) (
      byte_seq)) : ChoiceEquality) (at level 2).
Definition AES128_ENCRYPT : nat :=
  157.
Program Definition aes128_encrypt
  : both_package (fset.fset0) [interface
  #val #[ ENCRYPT_AES128 ] : encrypt_aes128_inp → encrypt_aes128_out ] [(
    AES128_ENCRYPT,(aes128_encrypt_inp,aes128_encrypt_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      k_151 , iv_152 , payload_154 , ad_153) := temp_inp : aead_key_t '× aead_iv_t '× byte_seq '× byte_seq in
    
    let encrypt_aes128 := fun x_0 x_1 x_2 x_3 => package_both encrypt_aes128 (
      x_0,x_1,x_2,x_3) in
    ((letb '(ctxt_155, tag_156) : (seq uint8 '× gf128_tag_t) :=
          encrypt_aes128 (array_from_seq (_) (lift_to_both0 k_151)) (
            array_from_seq (_) (lift_to_both0 iv_152)) (lift_to_both0 ad_153) (
            lift_to_both0 payload_154) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok byte_seq crypto_error_t (seq_concat (lift_to_both0 ctxt_155) (
              seq_from_seq (array_to_seq (lift_to_both0 tag_156)))))
        ) : both (fset.fset0) [interface
      #val #[ ENCRYPT_AES128 ] : encrypt_aes128_inp → encrypt_aes128_out ] ((
          result (crypto_error_t) (byte_seq)))))in
  both_package' _ _ (AES128_ENCRYPT,(
      aes128_encrypt_inp,aes128_encrypt_out)) temp_package_both.
Fail Next Obligation.


Notation "'chacha_encrypt_inp'" :=(
  aead_key_t '× aead_iv_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'chacha_encrypt_inp'" :=(
  aead_key_t '× aead_iv_t '× byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'chacha_encrypt_out'" :=((result (crypto_error_t) (
      byte_seq)) : choice_type) (in custom pack_type at level 2).
Notation "'chacha_encrypt_out'" :=((result (crypto_error_t) (
      byte_seq)) : ChoiceEquality) (at level 2).
Definition CHACHA_ENCRYPT : nat :=
  164.
Program Definition chacha_encrypt
  : both_package (fset.fset0) [interface
  #val #[ CHACHA20_POLY1305_ENCRYPT ] : chacha20_poly1305_encrypt_inp → chacha20_poly1305_encrypt_out
  ] [(CHACHA_ENCRYPT,(chacha_encrypt_inp,chacha_encrypt_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      k_158 , iv_159 , payload_161 , ad_160) := temp_inp : aead_key_t '× aead_iv_t '× byte_seq '× byte_seq in
    
    let chacha20_poly1305_encrypt := fun x_0 x_1 x_2 x_3 => package_both chacha20_poly1305_encrypt (
      x_0,x_1,x_2,x_3) in
    ((letb '(ctxt_162, tag_163) : (seq uint8 '× poly1305_tag_t) :=
          chacha20_poly1305_encrypt (array_from_seq (32) (
              lift_to_both0 k_158)) (array_from_seq (12) (
              lift_to_both0 iv_159)) (lift_to_both0 ad_160) (
            lift_to_both0 payload_161) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok byte_seq crypto_error_t (seq_concat (lift_to_both0 ctxt_162) (
              array_to_seq (lift_to_both0 tag_163))))
        ) : both (fset.fset0) [interface
      #val #[ CHACHA20_POLY1305_ENCRYPT ] : chacha20_poly1305_encrypt_inp → chacha20_poly1305_encrypt_out
      ] ((result (crypto_error_t) (byte_seq)))))in
  both_package' _ _ (CHACHA_ENCRYPT,(
      chacha_encrypt_inp,chacha_encrypt_out)) temp_package_both.
Fail Next Obligation.


Notation "'aead_encrypt_inp'" :=(
  aead_algorithm_t '× aead_key_t '× aead_iv_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'aead_encrypt_inp'" :=(
  aead_algorithm_t '× aead_key_t '× aead_iv_t '× byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'aead_encrypt_out'" :=((result (crypto_error_t) (
      byte_seq)) : choice_type) (in custom pack_type at level 2).
Notation "'aead_encrypt_out'" :=((result (crypto_error_t) (
      byte_seq)) : ChoiceEquality) (at level 2).
Definition AEAD_ENCRYPT : nat :=
  165.
Program Definition aead_encrypt
  : both_package (fset.fset0) [interface
  #val #[ AES128_ENCRYPT ] : aes128_encrypt_inp → aes128_encrypt_out ;
  #val #[ CHACHA_ENCRYPT ] : chacha_encrypt_inp → chacha_encrypt_out ] [(
    AEAD_ENCRYPT,(aead_encrypt_inp,aead_encrypt_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      a_166 , k_167 , iv_168 , payload_169 , ad_170) := temp_inp : aead_algorithm_t '× aead_key_t '× aead_iv_t '× byte_seq '× byte_seq in
    
    let aes128_encrypt := fun x_0 x_1 x_2 x_3 => package_both aes128_encrypt (
      x_0,x_1,x_2,x_3) in
    let chacha_encrypt := fun x_0 x_1 x_2 x_3 => package_both chacha_encrypt (
      x_0,x_1,x_2,x_3) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
        fset.fset0) [interface
      #val #[ AES128_ENCRYPT ] : aes128_encrypt_inp → aes128_encrypt_out ;
      #val #[ CHACHA_ENCRYPT ] : chacha_encrypt_inp → chacha_encrypt_out ] ((
          result (crypto_error_t) (byte_seq)))))in
  both_package' _ _ (AEAD_ENCRYPT,(
      aead_encrypt_inp,aead_encrypt_out)) temp_package_both.
Fail Next Obligation.


Notation "'aes128_decrypt_inp'" :=(
  aead_key_t '× aead_iv_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'aes128_decrypt_inp'" :=(
  aead_key_t '× aead_iv_t '× byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'aes128_decrypt_out'" :=((result (crypto_error_t) (
      byte_seq)) : choice_type) (in custom pack_type at level 2).
Notation "'aes128_decrypt_out'" :=((result (crypto_error_t) (
      byte_seq)) : ChoiceEquality) (at level 2).
Definition AES128_DECRYPT : nat :=
  171.
Program Definition aes128_decrypt
  : both_package (fset.fset0) [interface
  #val #[ DECRYPT_AES128 ] : decrypt_aes128_inp → decrypt_aes128_out ] [(
    AES128_DECRYPT,(aes128_decrypt_inp,aes128_decrypt_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      k_172 , iv_173 , ciphertext_174 , ad_175) := temp_inp : aead_key_t '× aead_iv_t '× byte_seq '× byte_seq in
    
    let decrypt_aes128 := fun x_0 x_1 x_2 x_3 x_4 => package_both decrypt_aes128 (
      x_0,x_1,x_2,x_3,x_4) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
        fset.fset0) [interface
      #val #[ DECRYPT_AES128 ] : decrypt_aes128_inp → decrypt_aes128_out ] ((
          result (crypto_error_t) (byte_seq)))))in
  both_package' _ _ (AES128_DECRYPT,(
      aes128_decrypt_inp,aes128_decrypt_out)) temp_package_both.
Fail Next Obligation.


Notation "'chacha_decrypt_inp'" :=(
  aead_key_t '× aead_iv_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'chacha_decrypt_inp'" :=(
  aead_key_t '× aead_iv_t '× byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'chacha_decrypt_out'" :=((result (crypto_error_t) (
      byte_seq)) : choice_type) (in custom pack_type at level 2).
Notation "'chacha_decrypt_out'" :=((result (crypto_error_t) (
      byte_seq)) : ChoiceEquality) (at level 2).
Definition CHACHA_DECRYPT : nat :=
  176.
Program Definition chacha_decrypt
  : both_package (fset.fset0) [interface
  #val #[ CHACHA20_POLY1305_DECRYPT ] : chacha20_poly1305_decrypt_inp → chacha20_poly1305_decrypt_out
  ] [(CHACHA_DECRYPT,(chacha_decrypt_inp,chacha_decrypt_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      k_177 , iv_178 , ciphertext_179 , ad_180) := temp_inp : aead_key_t '× aead_iv_t '× byte_seq '× byte_seq in
    
    let chacha20_poly1305_decrypt := fun x_0 x_1 x_2 x_3 x_4 => package_both chacha20_poly1305_decrypt (
      x_0,x_1,x_2,x_3,x_4) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
        fset.fset0) [interface
      #val #[ CHACHA20_POLY1305_DECRYPT ] : chacha20_poly1305_decrypt_inp → chacha20_poly1305_decrypt_out
      ] ((result (crypto_error_t) (byte_seq)))))in
  both_package' _ _ (CHACHA_DECRYPT,(
      chacha_decrypt_inp,chacha_decrypt_out)) temp_package_both.
Fail Next Obligation.


Notation "'aead_decrypt_inp'" :=(
  aead_algorithm_t '× aead_key_t '× aead_iv_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'aead_decrypt_inp'" :=(
  aead_algorithm_t '× aead_key_t '× aead_iv_t '× byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'aead_decrypt_out'" :=((result (crypto_error_t) (
      byte_seq)) : choice_type) (in custom pack_type at level 2).
Notation "'aead_decrypt_out'" :=((result (crypto_error_t) (
      byte_seq)) : ChoiceEquality) (at level 2).
Definition AEAD_DECRYPT : nat :=
  181.
Program Definition aead_decrypt
  : both_package (fset.fset0) [interface
  #val #[ AES128_DECRYPT ] : aes128_decrypt_inp → aes128_decrypt_out ;
  #val #[ CHACHA_DECRYPT ] : chacha_decrypt_inp → chacha_decrypt_out ] [(
    AEAD_DECRYPT,(aead_decrypt_inp,aead_decrypt_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      a_182 , k_183 , iv_184 , ciphertext_185 , ad_186) := temp_inp : aead_algorithm_t '× aead_key_t '× aead_iv_t '× byte_seq '× byte_seq in
    
    let aes128_decrypt := fun x_0 x_1 x_2 x_3 => package_both aes128_decrypt (
      x_0,x_1,x_2,x_3) in
    let chacha_decrypt := fun x_0 x_1 x_2 x_3 => package_both chacha_decrypt (
      x_0,x_1,x_2,x_3) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
        fset.fset0) [interface
      #val #[ AES128_DECRYPT ] : aes128_decrypt_inp → aes128_decrypt_out ;
      #val #[ CHACHA_DECRYPT ] : chacha_decrypt_inp → chacha_decrypt_out ] ((
          result (crypto_error_t) (byte_seq)))))in
  both_package' _ _ (AEAD_DECRYPT,(
      aead_decrypt_inp,aead_decrypt_out)) temp_package_both.
Fail Next Obligation.

