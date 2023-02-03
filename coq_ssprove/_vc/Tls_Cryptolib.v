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


Require Import Hacspec_Aes.

Require Import Hacspec_Aes128_Gcm.

Require Import Hacspec_Chacha20.

Require Import Hacspec_Chacha20poly1305.

Require Import Hacspec_Curve25519.

Require Import Hacspec_Ecdsa_P256_Sha256.

Require Import Hacspec_Gf128.

Require Import Hacspec_Hkdf.

Require Import Hacspec_Hmac.

Require Import Hacspec_P256.

Require Import Hacspec_Poly1305.

Require Import Hacspec_Sha256.

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
Program Definition empty  : both (fset.fset0) [interface] (byte_seq) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (seq_new_ (
          default : uint8) (lift_to_both0 (usize 0)))
      ) : both (fset.fset0) [interface] (byte_seq)).
Fail Next Obligation.


Notation "'zeros_inp'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'zeros_inp'" :=(uint_size : ChoiceEquality) (at level 2).
Notation "'zeros_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'zeros_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition ZEROS : nat :=
  2.
Program Definition zeros (u_1 : uint_size)
  : both (fset.fset0) [interface] (byte_seq) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (seq_new_ (
          default : uint8) (lift_to_both0 u_1))
      ) : both (fset.fset0) [interface] (byte_seq)).
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
Program Definition hash_len (ha_4 : hash_algorithm_t)
  : both (fset.fset0) [interface] (uint_size) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
      fset.fset0) [interface] (uint_size)).
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
Program Definition hmac_key_len (ha_6 : hash_algorithm_t)
  : both (fset.fset0) [interface] (uint_size) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
      fset.fset0) [interface] (uint_size)).
Fail Next Obligation.


Notation "'ae_key_len_inp'" :=(
  aead_algorithm_t : choice_type) (in custom pack_type at level 2).
Notation "'ae_key_len_inp'" :=(aead_algorithm_t : ChoiceEquality) (at level 2).
Notation "'ae_key_len_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'ae_key_len_out'" :=(uint_size : ChoiceEquality) (at level 2).
Definition AE_KEY_LEN : nat :=
  7.
Program Definition ae_key_len (ae_8 : aead_algorithm_t)
  : both (fset.fset0) [interface] (uint_size) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
      fset.fset0) [interface] (uint_size)).
Fail Next Obligation.


Notation "'ae_iv_len_inp'" :=(
  aead_algorithm_t : choice_type) (in custom pack_type at level 2).
Notation "'ae_iv_len_inp'" :=(aead_algorithm_t : ChoiceEquality) (at level 2).
Notation "'ae_iv_len_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'ae_iv_len_out'" :=(uint_size : ChoiceEquality) (at level 2).
Definition AE_IV_LEN : nat :=
  9.
Program Definition ae_iv_len (ae_10 : aead_algorithm_t)
  : both (fset.fset0) [interface] (uint_size) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
      fset.fset0) [interface] (uint_size)).
Fail Next Obligation.


Notation "'dh_priv_len_inp'" :=(
  named_group_t : choice_type) (in custom pack_type at level 2).
Notation "'dh_priv_len_inp'" :=(named_group_t : ChoiceEquality) (at level 2).
Notation "'dh_priv_len_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'dh_priv_len_out'" :=(uint_size : ChoiceEquality) (at level 2).
Definition DH_PRIV_LEN : nat :=
  11.
Program Definition dh_priv_len (gn_12 : named_group_t)
  : both (fset.fset0) [interface] (uint_size) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
      fset.fset0) [interface] (uint_size)).
Fail Next Obligation.


Notation "'dh_pub_len_inp'" :=(
  named_group_t : choice_type) (in custom pack_type at level 2).
Notation "'dh_pub_len_inp'" :=(named_group_t : ChoiceEquality) (at level 2).
Notation "'dh_pub_len_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'dh_pub_len_out'" :=(uint_size : ChoiceEquality) (at level 2).
Definition DH_PUB_LEN : nat :=
  13.
Program Definition dh_pub_len (gn_14 : named_group_t)
  : both (fset.fset0) [interface] (uint_size) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
      fset.fset0) [interface] (uint_size)).
Fail Next Obligation.


Notation "'zero_key_inp'" :=(
  hash_algorithm_t : choice_type) (in custom pack_type at level 2).
Notation "'zero_key_inp'" :=(hash_algorithm_t : ChoiceEquality) (at level 2).
Notation "'zero_key_out'" :=(
  key_t : choice_type) (in custom pack_type at level 2).
Notation "'zero_key_out'" :=(key_t : ChoiceEquality) (at level 2).
Definition ZERO_KEY : nat :=
  16.
Program Definition zero_key (ha_15 : hash_algorithm_t)
  : both (fset.fset0) [interface] (key_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (seq_new_ (
          default : uint8) (usize (is_pure (hash_len (lift_to_both0 ha_15)))))
      ) : both (fset.fset0) [interface] (key_t)).
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
Program Definition secret_to_public (group_name_18 : named_group_t) (
    x_19 : dh_sk_t)
  : both (fset.fset0) [interface] ((result (crypto_error_t) (dh_pk_t))) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
      fset.fset0) [interface] ((result (crypto_error_t) (dh_pk_t)))).
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
Program Definition p256_check_point_len (p_20 : dh_pk_t)
  : both (fset.fset0) [interface] ((result (crypto_error_t) (
        unit_ChoiceEquality))) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((seq_len (lift_to_both0 p_20)) !=.? (
            lift_to_both0 (usize 64)))
        then @Err unit_ChoiceEquality crypto_error_t (CryptoError)
        else @Ok unit_ChoiceEquality crypto_error_t (tt))
      ) : both (fset.fset0) [interface] ((result (crypto_error_t) (
          unit_ChoiceEquality)))).
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
Program Definition p256_ecdh (x_25 : dh_sk_t) (y_22 : dh_pk_t)
  : both (fset.fset0) [interface] ((result (crypto_error_t) (key_t))) :=
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
      ) : both (fset.fset0) [interface] ((result (crypto_error_t) (key_t)))).
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
Program Definition ecdh (group_name_27 : named_group_t) (x_28 : dh_sk_t) (
    y_29 : dh_pk_t)
  : both (fset.fset0) [interface] ((result (crypto_error_t) (key_t))) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
      fset.fset0) [interface] ((result (crypto_error_t) (key_t)))).
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
Program Definition kem_priv_len (ks_30 : kem_scheme_t)
  : both (fset.fset0) [interface] (uint_size) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (dh_priv_len (
          lift_to_both0 ks_30))
      ) : both (fset.fset0) [interface] (uint_size)).
Fail Next Obligation.


Notation "'kem_pub_len_inp'" :=(
  kem_scheme_t : choice_type) (in custom pack_type at level 2).
Notation "'kem_pub_len_inp'" :=(kem_scheme_t : ChoiceEquality) (at level 2).
Notation "'kem_pub_len_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'kem_pub_len_out'" :=(uint_size : ChoiceEquality) (at level 2).
Definition KEM_PUB_LEN : nat :=
  33.
Program Definition kem_pub_len (ks_32 : kem_scheme_t)
  : both (fset.fset0) [interface] (uint_size) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (dh_pub_len (
          lift_to_both0 ks_32))
      ) : both (fset.fset0) [interface] (uint_size)).
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
Program Definition kem_priv_to_pub (ks_34 : kem_scheme_t) (sk_35 : kem_sk_t)
  : both (fset.fset0) [interface] ((result (crypto_error_t) (kem_pk_t))) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (secret_to_public (
          lift_to_both0 ks_34) (lift_to_both0 sk_35))
      ) : both (fset.fset0) [interface] ((result (crypto_error_t) (kem_pk_t)))).
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
Program Definition kem_keygen_inner (ks_38 : kem_scheme_t) (ent_37 : entropy_t)
  : both (fset.fset0) [interface] ((result (crypto_error_t) ((
          kem_sk_t '×
          kem_pk_t
        )))) :=
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
      ) : both (fset.fset0) [interface] ((result (crypto_error_t) ((
            kem_sk_t '×
            kem_pk_t
          ))))).
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
Program Definition kem_keygen (ks_43 : kem_scheme_t) (ent_42 : entropy_t)
  : both (fset.fset0) [interface] ((result (crypto_error_t) ((
          kem_sk_t '×
          kem_pk_t
        )))) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((seq_len (lift_to_both0 ent_42)) <.? (
            dh_priv_len (lift_to_both0 ks_43)))
        then @Err (kem_sk_t '× kem_pk_t) crypto_error_t (InsufficientEntropy)
        else kem_keygen_inner (lift_to_both0 ks_43) (lift_to_both0 ent_42))
      ) : both (fset.fset0) [interface] ((result (crypto_error_t) ((
            kem_sk_t '×
            kem_pk_t
          ))))).
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
Program Definition kem_encap (ks_45 : kem_scheme_t) (pk_49 : kem_pk_t) (
    ent_46 : entropy_t)
  : both (fset.fset0) [interface] ((result (crypto_error_t) ((key_t '× byte_seq
        )))) :=
  ((letbnd(_) '(x_47, gx_48) : (kem_sk_t '× kem_pk_t) :=
        kem_keygen (lift_to_both0 ks_45) (lift_to_both0 ent_46) in
      letbnd(_) gxy_50 : key_t :=
        ecdh (lift_to_both0 ks_45) (lift_to_both0 x_47) (lift_to_both0 pk_49) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (key_t '× byte_seq
        ) crypto_error_t (prod_b(lift_to_both0 gxy_50, lift_to_both0 gx_48)))
      ) : both (fset.fset0) [interface] ((result (crypto_error_t) ((
            key_t '×
            byte_seq
          ))))).
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
Program Definition kem_decap (ks_52 : kem_scheme_t) (ct_54 : byte_seq) (
    sk_53 : kem_sk_t)
  : both (fset.fset0) [interface] ((result (crypto_error_t) (key_t))) :=
  ((letbnd(_) gxy_55 : key_t :=
        ecdh (lift_to_both0 ks_52) (lift_to_both0 sk_53) (
          lift_to_both0 ct_54) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        @Ok key_t crypto_error_t (lift_to_both0 gxy_55))
      ) : both (fset.fset0) [interface] ((result (crypto_error_t) (key_t)))).
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
Program Definition hash (ha_58 : hash_algorithm_t) (payload_59 : byte_seq)
  : both (fset.fset0) [interface] ((result (crypto_error_t) (digest_t))) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
      fset.fset0) [interface] ((result (crypto_error_t) (digest_t)))).
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
Program Definition hmac_tag (ha_61 : hash_algorithm_t) (mk_62 : mac_key_t) (
    payload_63 : byte_seq)
  : both (fset.fset0) [interface] ((result (crypto_error_t) (hmac_t))) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
      fset.fset0) [interface] ((result (crypto_error_t) (hmac_t)))).
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
Program Definition check_tag_len (a_64 : hmac_t) (b_65 : hmac_t)
  : both (fset.fset0) [interface] ((result (crypto_error_t) (
        unit_ChoiceEquality))) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((seq_len (lift_to_both0 a_64)) =.? (
            seq_len (lift_to_both0 b_65)))
        then @Ok unit_ChoiceEquality crypto_error_t (tt)
        else @Err unit_ChoiceEquality crypto_error_t (MacFailed))
      ) : both (fset.fset0) [interface] ((result (crypto_error_t) (
          unit_ChoiceEquality)))).
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
Program Definition check_bytes (a_67 : uint8) (b_68 : uint8)
  : both (fset.fset0) [interface] ((result (crypto_error_t) (
        unit_ChoiceEquality))) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (negb (uint8_equal (lift_to_both0 a_67) (
              lift_to_both0 b_68)))
        then @Err unit_ChoiceEquality crypto_error_t (MacFailed)
        else @Ok unit_ChoiceEquality crypto_error_t (tt))
      ) : both (fset.fset0) [interface] ((result (crypto_error_t) (
          unit_ChoiceEquality)))).
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
Program Definition hmac_verify (ha_70 : hash_algorithm_t) (mk_71 : mac_key_t) (
    payload_72 : byte_seq) (m_74 : hmac_t)
  : both (fset.fset0) [interface] ((result (crypto_error_t) (
        unit_ChoiceEquality))) :=
  ((letbnd(_) my_hmac_73 : hmac_t :=
        hmac_tag (lift_to_both0 ha_70) (lift_to_both0 mk_71) (
          lift_to_both0 payload_72) in
      letbnd(_) _ : unit_ChoiceEquality :=
        check_tag_len (lift_to_both0 m_74) (lift_to_both0 my_hmac_73) in
      letbnd(ChoiceEqualityMonad.result_bind_both crypto_error_t) 'tt :=
        foldi_bind_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 m_74)) prod_cett (L := (fset.fset0)) (
            I := [interface]) (fun i_75 'tt =>
            letbnd(_) _ : unit_ChoiceEquality :=
              check_bytes (seq_index (my_hmac_73) (lift_to_both0 i_75)) (
                seq_index (m_74) (lift_to_both0 i_75)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              @Ok unit_ChoiceEquality crypto_error_t (lift_to_both0 (
                  (tt : unit_ChoiceEquality))))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        @Ok unit_ChoiceEquality crypto_error_t (tt))
      ) : both (fset.fset0) [interface] ((result (crypto_error_t) (
          unit_ChoiceEquality)))).
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
Program Definition get_length_length (b_77 : byte_seq)
  : both (fset.fset0) [interface] (uint_size) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (((uint8_declassify (seq_index (b_77) (
                  lift_to_both0 (usize 0)))) shift_right (lift_to_both0 (
                usize 7))) =.? (lift_to_both0 (@repr U8 1)))
        then declassify_usize_from_uint8 ((seq_index (b_77) (lift_to_both0 (
                usize 0))) .& (secret (lift_to_both0 (@repr U8 127))))
        else lift_to_both0 (usize 0))
      ) : both (fset.fset0) [interface] (uint_size)).
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
Program Definition get_length (b_79 : byte_seq) (len_80 : uint_size)
  : both (fset.fset0) [interface] (uint_size) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          (fun x => lift_to_both0 (repr (unsigned x)))(
            declassify_u32_from_uint32 (uint32_from_be_bytes (array_from_slice (
                  default : uint8) (4) (lift_to_both0 b_79) (lift_to_both0 (
                    usize 0)) (lift_to_both0 len_80))))) usize_shift_right (((
              lift_to_both0 (usize 4)) .- (lift_to_both0 len_80)) .* (
            lift_to_both0 (usize 8))))
      ) : both (fset.fset0) [interface] (uint_size)).
Fail Next Obligation.


Notation "'get_short_length_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'get_short_length_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'get_short_length_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'get_short_length_out'" :=(uint_size : ChoiceEquality) (at level 2).
Definition GET_SHORT_LENGTH : nat :=
  83.
Program Definition get_short_length (b_82 : byte_seq)
  : both (fset.fset0) [interface] (uint_size) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        declassify_usize_from_uint8 ((seq_index (b_82) (lift_to_both0 (
                usize 0))) .& (secret (lift_to_both0 (@repr U8 127)))))
      ) : both (fset.fset0) [interface] (uint_size)).
Fail Next Obligation.

Definition seq1_84_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 88%nat).
Definition ec_pk_oid_87_loc : ChoiceEqualityLocation :=
  (bool_ChoiceEquality ; 89%nat).
Definition len_86_loc : ChoiceEqualityLocation :=
  (uint_size ; 90%nat).
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
Program Definition verification_key_from_cert (cert_92 : byte_seq)
  : both (CEfset (
      [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) [interface] ((
      result (crypto_error_t) (verification_key_t))) :=
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
        get_length (seq_slice (lift_to_both0 cert_92) (lift_to_both0 skip_95) ((
              seq_len (lift_to_both0 cert_92)) .- (lift_to_both0 skip_95))) (
          lift_to_both0 seq1_len_len_94) in
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
                [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc]))) (
            I := [interface]) (fun i_97 '(seq1_84, pk_85) =>
            letb '(seq1_84, pk_85) :=
              if (seq_len (lift_to_both0 seq1_84)) >.? (lift_to_both0 (
                  usize 0)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (
                L2 := CEfset (
                  [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
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
                letb '(len_86) :=
                  if (lift_to_both0 len_len_99) !=.? (lift_to_both0 (
                      usize 0)) :bool_ChoiceEquality
                  then lift_scope (L1 := CEfset (
                      [seq1_84_loc ; pk_85_loc ; len_86_loc])) (L2 := CEfset (
                      [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (
                    I1 := [interface]) (
                    I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
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
                letb '(pk_85) :=
                  if ((lift_to_both0 element_type_98) =.? (lift_to_both0 (
                        @repr U8 48))) && ((seq_len (lift_to_both0 pk_85)) =.? (
                      lift_to_both0 (usize 0))) :bool_ChoiceEquality
                  then lift_scope (L1 := CEfset (
                      [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (
                    L2 := CEfset (
                      [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (
                    I1 := [interface]) (
                    I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
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
                    letb '(pk_85) :=
                      if (lift_to_both0 element_type_101) =.? (lift_to_both0 (
                          @repr U8 48)) :bool_ChoiceEquality
                      then lift_scope (L1 := CEfset (
                          [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (
                        L2 := CEfset (
                          [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (
                        I1 := [interface]) (
                        I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                        letb len_len_103 : uint_size :=
                          get_length_length (lift_to_both0 seq2_102) in
                        letb '(pk_85) :=
                          if (lift_to_both0 len_len_103) =.? (lift_to_both0 (
                              usize 0)) :bool_ChoiceEquality
                          then lift_scope (L1 := CEfset (
                              [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (
                            L2 := CEfset (
                              [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (
                            I1 := [interface]) (
                            I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                            letb oid_len_104 : uint_size :=
                              get_short_length (lift_to_both0 seq2_102) in
                            letb '(pk_85) :=
                              if (lift_to_both0 oid_len_104) >=.? (
                                lift_to_both0 (usize 9)) :bool_ChoiceEquality
                              then lift_scope (L1 := CEfset (
                                  [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (
                                L2 := CEfset (
                                  [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (
                                I1 := [interface]) (
                                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                                letb expected_105 : seq uint8 :=
                                  seq_from_seq (
                                    array_to_seq (@array_from_list uint8 ([
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
                                      lift_to_both0 (usize 9)) ec_pk_oid_87 (
                                      L := (CEfset (
                                          [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc]))) (
                                      I := [interface]) (
                                      fun i_107 ec_pk_oid_87 =>
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
                                letb '(pk_85) :=
                                  if lift_to_both0 ec_pk_oid_87 :bool_ChoiceEquality
                                  then lift_scope (L1 := CEfset (
                                      [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (
                                    L2 := CEfset (
                                      [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (
                                    I1 := [interface]) (
                                    I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                                    letb bit_string_109 : seq uint8 :=
                                      seq_slice (lift_to_both0 seq2_102) ((
                                          lift_to_both0 oid_len_104) .+ (
                                          lift_to_both0 (usize 1))) (((seq_len (
                                              lift_to_both0 seq2_102)) .- (
                                            lift_to_both0 oid_len_104)) .- (
                                          lift_to_both0 (usize 1))) in
                                    letb '(pk_85) :=
                                      if (uint8_declassify (seq_index (
                                            bit_string_109) (lift_to_both0 (
                                              usize 0)))) =.? (lift_to_both0 (
                                          @repr U8 3)) :bool_ChoiceEquality
                                      then lift_scope (L1 := CEfset (
                                          [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (
                                        L2 := CEfset (
                                          [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) (
                                        I1 := [interface]) (
                                        I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
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
        [seq1_84_loc ; pk_85_loc ; len_86_loc ; ec_pk_oid_87_loc])) [interface] (
      (result (crypto_error_t) (verification_key_t)))).
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
Program Definition concat_signature (r_114 : p256_scalar_t) (
    s_115 : p256_scalar_t)
  : both (fset.fset0) [interface] ((result (crypto_error_t) (signature_t))) :=
  ((letb signature_116 : seq uint8 :=
        seq_concat (seq_concat (seq_new_ (default : uint8) (lift_to_both0 (
                usize 0))) (nat_mod_to_byte_seq_be (lift_to_both0 r_114))) (
          nat_mod_to_byte_seq_be (lift_to_both0 s_115)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        @Ok signature_t crypto_error_t (lift_to_both0 signature_116))
      ) : both (fset.fset0) [interface] ((result (crypto_error_t) (
          signature_t)))).
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
Program Definition p256_sign (ps_122 : signature_key_t) (
    payload_123 : byte_seq) (ent_118 : entropy_t)
  : both (fset.fset0) [interface] ((result (crypto_error_t) (signature_t))) :=
  ((letb random_119 : random_t :=
        array_from_seq (32) (seq_slice_range (lift_to_both0 ent_118) (prod_b(
              lift_to_both0 (usize 0),
              lift_to_both0 (usize 32)
            ))) in
      letb nonce_120 : p256_scalar_t :=
        nat_mod_from_byte_seq_be (array_to_seq (lift_to_both0 random_119)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match)
      ) : both (fset.fset0) [interface] ((result (crypto_error_t) (
          signature_t)))).
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
Program Definition sign (sa_125 : signature_scheme_t) (
    ps_126 : signature_key_t) (payload_127 : byte_seq) (ent_128 : entropy_t)
  : both (fset.fset0) [interface] ((result (crypto_error_t) (signature_t))) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
      fset.fset0) [interface] ((result (crypto_error_t) (signature_t)))).
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
Program Definition p256_verify (pk_129 : verification_key_t) (
    payload_136 : byte_seq) (sig_132 : byte_seq)
  : both (fset.fset0) [interface] ((result (crypto_error_t) (
        unit_ChoiceEquality))) :=
  ((letb '(pk_x_130, pk_y_131) : (p256_field_element_t '× p256_field_element_t
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
      ) : both (fset.fset0) [interface] ((result (crypto_error_t) (
          unit_ChoiceEquality)))).
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
Program Definition verify (sa_138 : signature_scheme_t) (
    pk_139 : verification_key_t) (payload_140 : byte_seq) (sig_141 : byte_seq)
  : both (fset.fset0) [interface] ((result (crypto_error_t) (
        unit_ChoiceEquality))) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
      fset.fset0) [interface] ((result (crypto_error_t) (
          unit_ChoiceEquality)))).
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
Program Definition hkdf_extract (ha_143 : hash_algorithm_t) (k_144 : key_t) (
    salt_145 : key_t)
  : both (fset.fset0) [interface] ((result (crypto_error_t) (key_t))) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
      fset.fset0) [interface] ((result (crypto_error_t) (key_t)))).
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
Program Definition hkdf_expand (ha_147 : hash_algorithm_t) (k_148 : key_t) (
    info_149 : byte_seq) (len_150 : uint_size)
  : both (fset.fset0) [interface] ((result (crypto_error_t) (key_t))) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
      fset.fset0) [interface] ((result (crypto_error_t) (key_t)))).
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
Program Definition aes128_encrypt (k_151 : aead_key_t) (iv_152 : aead_iv_t) (
    payload_154 : byte_seq) (ad_153 : byte_seq)
  : both (fset.fset0) [interface] ((result (crypto_error_t) (byte_seq))) :=
  ((letb '(ctxt_155, tag_156) : (seq uint8 '× gf128_tag_t) :=
        encrypt_aes128 (array_from_seq (_) (lift_to_both0 k_151)) (
          array_from_seq (_) (lift_to_both0 iv_152)) (lift_to_both0 ad_153) (
          lift_to_both0 payload_154) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        @Ok byte_seq crypto_error_t (seq_concat (lift_to_both0 ctxt_155) (
            seq_from_seq (array_to_seq (lift_to_both0 tag_156)))))
      ) : both (fset.fset0) [interface] ((result (crypto_error_t) (byte_seq)))).
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
Program Definition chacha_encrypt (k_158 : aead_key_t) (iv_159 : aead_iv_t) (
    payload_161 : byte_seq) (ad_160 : byte_seq)
  : both (fset.fset0) [interface] ((result (crypto_error_t) (byte_seq))) :=
  ((letb '(ctxt_162, tag_163) : (seq uint8 '× poly1305_tag_t) :=
        chacha20_poly1305_encrypt (array_from_seq (32) (lift_to_both0 k_158)) (
          array_from_seq (12) (lift_to_both0 iv_159)) (lift_to_both0 ad_160) (
          lift_to_both0 payload_161) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        @Ok byte_seq crypto_error_t (seq_concat (lift_to_both0 ctxt_162) (
            array_to_seq (lift_to_both0 tag_163))))
      ) : both (fset.fset0) [interface] ((result (crypto_error_t) (byte_seq)))).
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
Program Definition aead_encrypt (a_166 : aead_algorithm_t) (
    k_167 : aead_key_t) (iv_168 : aead_iv_t) (payload_169 : byte_seq) (
    ad_170 : byte_seq)
  : both (fset.fset0) [interface] ((result (crypto_error_t) (byte_seq))) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
      fset.fset0) [interface] ((result (crypto_error_t) (byte_seq)))).
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
Program Definition aes128_decrypt (k_172 : aead_key_t) (iv_173 : aead_iv_t) (
    ciphertext_174 : byte_seq) (ad_175 : byte_seq)
  : both (fset.fset0) [interface] ((result (crypto_error_t) (byte_seq))) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
      fset.fset0) [interface] ((result (crypto_error_t) (byte_seq)))).
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
Program Definition chacha_decrypt (k_177 : aead_key_t) (iv_178 : aead_iv_t) (
    ciphertext_179 : byte_seq) (ad_180 : byte_seq)
  : both (fset.fset0) [interface] ((result (crypto_error_t) (byte_seq))) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
      fset.fset0) [interface] ((result (crypto_error_t) (byte_seq)))).
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
Program Definition aead_decrypt (a_182 : aead_algorithm_t) (
    k_183 : aead_key_t) (iv_184 : aead_iv_t) (ciphertext_185 : byte_seq) (
    ad_186 : byte_seq)
  : both (fset.fset0) [interface] ((result (crypto_error_t) (byte_seq))) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
      fset.fset0) [interface] ((result (crypto_error_t) (byte_seq)))).
Fail Next Obligation.

