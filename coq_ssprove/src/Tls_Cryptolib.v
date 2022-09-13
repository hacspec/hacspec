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

Require Import Hacspec_Poly1305.

Require Import Hacspec_Chacha20poly1305.

Require Import Hacspec_Curve25519.

Require Import Hacspec_P256.

Require Import Hacspec_Sha256.

Require Import Hacspec_Ecdsa_P256_Sha256.

Require Import Hacspec_Gf128.

Require Import Hacspec_Hkdf.

Require Import Hacspec_Hmac.

Inductive crypto_error_t :=
| CryptoError : crypto_error_t
| HkdfError : crypto_error_t
| InsufficientEntropy : crypto_error_t
| InvalidCert : crypto_error_t
| MacFailed : crypto_error_t
| UnsupportedAlgorithm : crypto_error_t
| VerifyFailed : crypto_error_t.

Definition empty_pure  : byte_seq :=
  seq_new_ (default : uint8) (usize 0).
Definition empty_pure_code  : code fset.fset0 [interface] (@ct (byte_seq)) :=
  lift_to_code (empty_pure ).


Notation "'empty_state_inp'" := (
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'empty_state_out'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition EMPTY_STATE : nat :=
  (2).
Program Definition empty_state
   : package (fset.fset0) [interface] [interface
  #val #[ EMPTY_STATE ] : empty_state_inp → empty_state_out ] :=
  (
    [package #def #[ EMPTY_STATE ] (temp_inp : empty_state_inp) : empty_state_out { 
    ({ code  temp_1 ←
        (seq_new_ (default : uint8) (usize 0)) ;;
      @ret (seq uint8) (temp_1) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_empty_state : package _ _ _ :=
  (empty_state).
Fail Next Obligation.

Notation "'empty_inp'" :=( : choice_type) (in custom pack_type at level 2).
Notation "'empty_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition EMPTY : nat :=
  (3).
Program Definition empty  :both (fset.fset0) [interface] (byte_seq) :=
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (seq_new_ (default : uint8) (
      lift_to_both0 (usize 0)))
  .
Fail Next Obligation.

Definition zeros_pure (u_4 : uint_size) : byte_seq :=
  seq_new_ (default : uint8) (u_4).
Definition zeros_pure_code
  (u_4 : uint_size)
  : code fset.fset0 [interface] (@ct (byte_seq)) :=
  lift_to_code (zeros_pure u_4).


Notation "'zeros_state_inp'" := (
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'zeros_state_out'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition ZEROS_STATE : nat :=
  (7).
Program Definition zeros_state
   : package (fset.fset0) [interface] [interface
  #val #[ ZEROS_STATE ] : zeros_state_inp → zeros_state_out ] :=
  (
    [package #def #[ ZEROS_STATE ] (temp_inp : zeros_state_inp) : zeros_state_out { 
    let '(u_4) := temp_inp : uint_size in
    ({ code  temp_6 ←
        (seq_new_ (default : uint8) (u_4)) ;;
      @ret (seq uint8) (temp_6) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_zeros_state : package _ _ _ :=
  (zeros_state).
Fail Next Obligation.

Notation "'zeros_inp'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'zeros_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition ZEROS : nat :=
  (8).
Program Definition zeros
  (u_4 : uint_size)
  :both (fset.fset0) [interface] (byte_seq) :=
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (seq_new_ (default : uint8) (
      lift_to_both0 u_4))
  .
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

Inductive named_group_t :=
| X25519 : named_group_t
| Secp256r1 : named_group_t.

Definition eqb_named_group_t (x y : named_group_t) : bool_ChoiceEquality :=
match x with
   | X25519 => match y with | X25519=> true | _ => false end
   | Secp256r1 => match y with | Secp256r1=> true | _ => false end
   end.

Definition eqb_leibniz_named_group_t (x y : named_group_t) : eqb_named_group_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_named_group_t : EqDec (named_group_t) :=
Build_EqDec (named_group_t) (eqb_named_group_t) (eqb_leibniz_named_group_t).


Inductive hash_algorithm_t :=
| SHA256 : hash_algorithm_t
| SHA384 : hash_algorithm_t.

Definition eqb_hash_algorithm_t (x y : hash_algorithm_t) : bool_ChoiceEquality :=
match x with
   | SHA256 => match y with | SHA256=> true | _ => false end
   | SHA384 => match y with | SHA384=> true | _ => false end
   end.

Definition eqb_leibniz_hash_algorithm_t (x y : hash_algorithm_t) : eqb_hash_algorithm_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_hash_algorithm_t : EqDec (hash_algorithm_t) :=
Build_EqDec (hash_algorithm_t) (eqb_hash_algorithm_t) (eqb_leibniz_hash_algorithm_t).


Inductive aead_algorithm_t :=
| Chacha20Poly1305 : aead_algorithm_t
| Aes128Gcm : aead_algorithm_t
| Aes256Gcm : aead_algorithm_t.

Definition eqb_aead_algorithm_t (x y : aead_algorithm_t) : bool_ChoiceEquality :=
match x with
   | Chacha20Poly1305 => match y with | Chacha20Poly1305=> true | _ => false end
   | Aes128Gcm => match y with | Aes128Gcm=> true | _ => false end
   | Aes256Gcm => match y with | Aes256Gcm=> true | _ => false end
   end.

Definition eqb_leibniz_aead_algorithm_t (x y : aead_algorithm_t) : eqb_aead_algorithm_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_aead_algorithm_t : EqDec (aead_algorithm_t) :=
Build_EqDec (aead_algorithm_t) (eqb_aead_algorithm_t) (eqb_leibniz_aead_algorithm_t).


Inductive signature_scheme_t :=
| ED25519 : signature_scheme_t
| EcdsaSecp256r1Sha256 : signature_scheme_t
| RsaPssRsaSha256 : signature_scheme_t.

Definition eqb_signature_scheme_t (x y : signature_scheme_t) : bool_ChoiceEquality :=
match x with
   | ED25519 => match y with | ED25519=> true | _ => false end
   | EcdsaSecp256r1Sha256 =>
       match y with
       | EcdsaSecp256r1Sha256=> true
       | _ => false
       end
   | RsaPssRsaSha256 => match y with | RsaPssRsaSha256=> true | _ => false end
   end.

Definition eqb_leibniz_signature_scheme_t (x y : signature_scheme_t) : eqb_signature_scheme_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_signature_scheme_t : EqDec (signature_scheme_t) :=
Build_EqDec (signature_scheme_t) (eqb_signature_scheme_t) (eqb_leibniz_signature_scheme_t).


Definition hash_len_pure (ha_9 : hash_algorithm_t) : uint_size :=
  match ha_9 with | SHA256 => usize 32 | SHA384 => usize 48 end.
Definition hash_len_pure_code
  (ha_9 : hash_algorithm_t)
  : code fset.fset0 [interface] (@ct (uint_size)) :=
  lift_to_code (hash_len_pure ha_9).


Notation "'hash_len_state_inp'" := (
  hash_algorithm_t : choice_type) (in custom pack_type at level 2).
Notation "'hash_len_state_out'" := (
  uint_size : choice_type) (in custom pack_type at level 2).
Definition HASH_LEN_STATE : nat :=
  (12).
Program Definition hash_len_state
   : package (fset.fset0) [interface] [interface
  #val #[ HASH_LEN_STATE ] : hash_len_state_inp → hash_len_state_out ] :=
  (
    [package #def #[ HASH_LEN_STATE ] (temp_inp : hash_len_state_inp) : hash_len_state_out { 
    let '(ha_9) := temp_inp : hash_algorithm_t in
    ({ code  temp_11 ←
        ((({ code match ha_9 with
              | SHA256 => ret (usize 32)
              | SHA384 => ret (usize 48)
              end } : code _ _ _))) ;;
      @ret (uint_size) (temp_11) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_hash_len_state : package _ _ _ :=
  (hash_len_state).
Fail Next Obligation.

Notation "'hash_len_inp'" :=(
  hash_algorithm_t : choice_type) (in custom pack_type at level 2).
Notation "'hash_len_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Definition HASH_LEN : nat :=
  (13).
Program Definition hash_len
  (ha_9 : hash_algorithm_t)
  :both (fset.fset0) [interface] (uint_size) :=
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) .
Fail Next Obligation.

Definition hmac_key_len_pure (ha_14 : hash_algorithm_t) : uint_size :=
  match ha_14 with | SHA256 => usize 32 | SHA384 => usize 48 end.
Definition hmac_key_len_pure_code
  (ha_14 : hash_algorithm_t)
  : code fset.fset0 [interface] (@ct (uint_size)) :=
  lift_to_code (hmac_key_len_pure ha_14).


Notation "'hmac_key_len_state_inp'" := (
  hash_algorithm_t : choice_type) (in custom pack_type at level 2).
Notation "'hmac_key_len_state_out'" := (
  uint_size : choice_type) (in custom pack_type at level 2).
Definition HMAC_KEY_LEN_STATE : nat :=
  (17).
Program Definition hmac_key_len_state
   : package (fset.fset0) [interface] [interface
  #val #[ HMAC_KEY_LEN_STATE ] : hmac_key_len_state_inp → hmac_key_len_state_out
  ] :=
  (
    [package #def #[ HMAC_KEY_LEN_STATE ] (temp_inp : hmac_key_len_state_inp) : hmac_key_len_state_out { 
    let '(ha_14) := temp_inp : hash_algorithm_t in
    ({ code  temp_16 ←
        ((({ code match ha_14 with
              | SHA256 => ret (usize 32)
              | SHA384 => ret (usize 48)
              end } : code _ _ _))) ;;
      @ret (uint_size) (temp_16) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_hmac_key_len_state : package _ _ _ :=
  (hmac_key_len_state).
Fail Next Obligation.

Notation "'hmac_key_len_inp'" :=(
  hash_algorithm_t : choice_type) (in custom pack_type at level 2).
Notation "'hmac_key_len_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Definition HMAC_KEY_LEN : nat :=
  (18).
Program Definition hmac_key_len
  (ha_14 : hash_algorithm_t)
  :both (fset.fset0) [interface] (uint_size) :=
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) .
Fail Next Obligation.

Definition ae_key_len_pure (ae_19 : aead_algorithm_t) : uint_size :=
  match ae_19 with
  | Chacha20Poly1305 => usize 32
  | Aes128Gcm => usize 16
  | Aes256Gcm => usize 16
  end.
Definition ae_key_len_pure_code
  (ae_19 : aead_algorithm_t)
  : code fset.fset0 [interface] (@ct (uint_size)) :=
  lift_to_code (ae_key_len_pure ae_19).


Notation "'ae_key_len_state_inp'" := (
  aead_algorithm_t : choice_type) (in custom pack_type at level 2).
Notation "'ae_key_len_state_out'" := (
  uint_size : choice_type) (in custom pack_type at level 2).
Definition AE_KEY_LEN_STATE : nat :=
  (22).
Program Definition ae_key_len_state
   : package (fset.fset0) [interface] [interface
  #val #[ AE_KEY_LEN_STATE ] : ae_key_len_state_inp → ae_key_len_state_out
  ] :=
  (
    [package #def #[ AE_KEY_LEN_STATE ] (temp_inp : ae_key_len_state_inp) : ae_key_len_state_out { 
    let '(ae_19) := temp_inp : aead_algorithm_t in
    ({ code  temp_21 ←
        ((({ code match ae_19 with
              | Chacha20Poly1305 => ret (usize 32)
              | Aes128Gcm => ret (usize 16)
              | Aes256Gcm => ret (usize 16)
              end } : code _ _ _))) ;;
      @ret (uint_size) (temp_21) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_ae_key_len_state : package _ _ _ :=
  (ae_key_len_state).
Fail Next Obligation.

Notation "'ae_key_len_inp'" :=(
  aead_algorithm_t : choice_type) (in custom pack_type at level 2).
Notation "'ae_key_len_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Definition AE_KEY_LEN : nat :=
  (23).
Program Definition ae_key_len
  (ae_19 : aead_algorithm_t)
  :both (fset.fset0) [interface] (uint_size) :=
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) .
Fail Next Obligation.

Definition ae_iv_len_pure (ae_24 : aead_algorithm_t) : uint_size :=
  match ae_24 with
  | Chacha20Poly1305 => usize 12
  | Aes128Gcm => usize 12
  | Aes256Gcm => usize 12
  end.
Definition ae_iv_len_pure_code
  (ae_24 : aead_algorithm_t)
  : code fset.fset0 [interface] (@ct (uint_size)) :=
  lift_to_code (ae_iv_len_pure ae_24).


Notation "'ae_iv_len_state_inp'" := (
  aead_algorithm_t : choice_type) (in custom pack_type at level 2).
Notation "'ae_iv_len_state_out'" := (
  uint_size : choice_type) (in custom pack_type at level 2).
Definition AE_IV_LEN_STATE : nat :=
  (27).
Program Definition ae_iv_len_state
   : package (fset.fset0) [interface] [interface
  #val #[ AE_IV_LEN_STATE ] : ae_iv_len_state_inp → ae_iv_len_state_out ] :=
  (
    [package #def #[ AE_IV_LEN_STATE ] (temp_inp : ae_iv_len_state_inp) : ae_iv_len_state_out { 
    let '(ae_24) := temp_inp : aead_algorithm_t in
    ({ code  temp_26 ←
        ((({ code match ae_24 with
              | Chacha20Poly1305 => ret (usize 12)
              | Aes128Gcm => ret (usize 12)
              | Aes256Gcm => ret (usize 12)
              end } : code _ _ _))) ;;
      @ret (uint_size) (temp_26) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_ae_iv_len_state : package _ _ _ :=
  (ae_iv_len_state).
Fail Next Obligation.

Notation "'ae_iv_len_inp'" :=(
  aead_algorithm_t : choice_type) (in custom pack_type at level 2).
Notation "'ae_iv_len_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Definition AE_IV_LEN : nat :=
  (28).
Program Definition ae_iv_len
  (ae_24 : aead_algorithm_t)
  :both (fset.fset0) [interface] (uint_size) :=
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) .
Fail Next Obligation.

Definition dh_priv_len_pure (gn_29 : named_group_t) : uint_size :=
  match gn_29 with | X25519 => usize 32 | Secp256r1 => usize 32 end.
Definition dh_priv_len_pure_code
  (gn_29 : named_group_t)
  : code fset.fset0 [interface] (@ct (uint_size)) :=
  lift_to_code (dh_priv_len_pure gn_29).


Notation "'dh_priv_len_state_inp'" := (
  named_group_t : choice_type) (in custom pack_type at level 2).
Notation "'dh_priv_len_state_out'" := (
  uint_size : choice_type) (in custom pack_type at level 2).
Definition DH_PRIV_LEN_STATE : nat :=
  (32).
Program Definition dh_priv_len_state
   : package (fset.fset0) [interface] [interface
  #val #[ DH_PRIV_LEN_STATE ] : dh_priv_len_state_inp → dh_priv_len_state_out
  ] :=
  (
    [package #def #[ DH_PRIV_LEN_STATE ] (temp_inp : dh_priv_len_state_inp) : dh_priv_len_state_out { 
    let '(gn_29) := temp_inp : named_group_t in
    ({ code  temp_31 ←
        ((({ code match gn_29 with
              | X25519 => ret (usize 32)
              | Secp256r1 => ret (usize 32)
              end } : code _ _ _))) ;;
      @ret (uint_size) (temp_31) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_dh_priv_len_state : package _ _ _ :=
  (dh_priv_len_state).
Fail Next Obligation.

Notation "'dh_priv_len_inp'" :=(
  named_group_t : choice_type) (in custom pack_type at level 2).
Notation "'dh_priv_len_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Definition DH_PRIV_LEN : nat :=
  (33).
Program Definition dh_priv_len
  (gn_29 : named_group_t)
  :both (fset.fset0) [interface] (uint_size) :=
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) .
Fail Next Obligation.

Definition dh_pub_len_pure (gn_34 : named_group_t) : uint_size :=
  match gn_34 with | X25519 => usize 32 | Secp256r1 => usize 64 end.
Definition dh_pub_len_pure_code
  (gn_34 : named_group_t)
  : code fset.fset0 [interface] (@ct (uint_size)) :=
  lift_to_code (dh_pub_len_pure gn_34).


Notation "'dh_pub_len_state_inp'" := (
  named_group_t : choice_type) (in custom pack_type at level 2).
Notation "'dh_pub_len_state_out'" := (
  uint_size : choice_type) (in custom pack_type at level 2).
Definition DH_PUB_LEN_STATE : nat :=
  (37).
Program Definition dh_pub_len_state
   : package (fset.fset0) [interface] [interface
  #val #[ DH_PUB_LEN_STATE ] : dh_pub_len_state_inp → dh_pub_len_state_out
  ] :=
  (
    [package #def #[ DH_PUB_LEN_STATE ] (temp_inp : dh_pub_len_state_inp) : dh_pub_len_state_out { 
    let '(gn_34) := temp_inp : named_group_t in
    ({ code  temp_36 ←
        ((({ code match gn_34 with
              | X25519 => ret (usize 32)
              | Secp256r1 => ret (usize 64)
              end } : code _ _ _))) ;;
      @ret (uint_size) (temp_36) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_dh_pub_len_state : package _ _ _ :=
  (dh_pub_len_state).
Fail Next Obligation.

Notation "'dh_pub_len_inp'" :=(
  named_group_t : choice_type) (in custom pack_type at level 2).
Notation "'dh_pub_len_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Definition DH_PUB_LEN : nat :=
  (38).
Program Definition dh_pub_len
  (gn_34 : named_group_t)
  :both (fset.fset0) [interface] (uint_size) :=
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) .
Fail Next Obligation.

Definition zero_key_pure (ha_39 : hash_algorithm_t) : key_t :=
  seq_new_ (default : uint8) (usize (hash_len (ha_39))).
Definition zero_key_pure_code
  (ha_39 : hash_algorithm_t)
  : code fset.fset0 [interface] (@ct (key_t)) :=
  lift_to_code (zero_key_pure ha_39).


Notation "'zero_key_state_inp'" := (
  hash_algorithm_t : choice_type) (in custom pack_type at level 2).
Notation "'zero_key_state_out'" := (
  key_t : choice_type) (in custom pack_type at level 2).
Definition ZERO_KEY_STATE : nat :=
  (44).
Program Definition zero_key_state
   : package (fset.fset0) [interface
  #val #[ HASH_LEN_STATE ] : hash_len_state_inp → hash_len_state_out
  ] [interface
  #val #[ ZERO_KEY_STATE ] : zero_key_state_inp → zero_key_state_out ] :=
  (
    [package #def #[ ZERO_KEY_STATE ] (temp_inp : zero_key_state_inp) : zero_key_state_out { 
    let '(ha_39) := temp_inp : hash_algorithm_t in
    #import {sig #[ HASH_LEN_STATE ] : hash_len_state_inp → hash_len_state_out } as hash_len_state ;;
    let hash_len_state := fun x_0 => hash_len_state (x_0) in
    ({ code  temp_41 ←
        (hash_len (ha_39)) ;;
       temp_43 ←
        (seq_new_ (default : uint8) (usize (temp_41))) ;;
      @ret (seq uint8) (temp_43) } : code (fset.fset0) [interface
      #val #[ HASH_LEN_STATE ] : hash_len_state_inp → hash_len_state_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_zero_key_state : package _ _ _ :=
  (seq_link zero_key_state link_rest(package_hash_len_state)).
Fail Next Obligation.

Notation "'zero_key_inp'" :=(
  hash_algorithm_t : choice_type) (in custom pack_type at level 2).
Notation "'zero_key_out'" :=(
  key_t : choice_type) (in custom pack_type at level 2).
Definition ZERO_KEY : nat :=
  (45).
Program Definition zero_key
  (ha_39 : hash_algorithm_t)
  :both (fset.fset0) [interface
  #val #[ HASH_LEN ] : hash_len_inp → hash_len_out ] (key_t) :=
  #import {sig #[ HASH_LEN ] : hash_len_inp → hash_len_out } as hash_len ;;
  let hash_len := fun x_0 => hash_len (x_0) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (seq_new_ (default : uint8) (
      usize (is_pure (hash_len (lift_to_both0 ha_39)))))
  .
Fail Next Obligation.

Definition secret_to_public_pure
  (group_name_46 : named_group_t)
  (x_47 : dh_sk_t)
  : (result crypto_error_t dh_pk_t) :=
  match group_name_46 with
  | Secp256r1 => match p256_point_mul_base (nat_mod_from_byte_seq_be (
      x_47)) with
  | Ok (x_48, y_49) => @Ok dh_pk_t crypto_error_t (seq_concat (
      nat_mod_to_byte_seq_be (x_48)) (nat_mod_to_byte_seq_be (y_49)))
  | Err _ => @Err dh_pk_t crypto_error_t (CryptoError)
  end
  | X25519 => @Ok dh_pk_t crypto_error_t (seq_from_seq (
      array_to_seq (x25519_secret_to_public (array_from_seq (32) (x_47)))))
  end.
Definition secret_to_public_pure_code
  (group_name_46 : named_group_t)
  (x_47 : dh_sk_t)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t dh_pk_t))) :=
  lift_to_code (secret_to_public_pure group_name_46 x_47).


Notation "'secret_to_public_state_inp'" := (
  named_group_t '× dh_sk_t : choice_type) (in custom pack_type at level 2).
Notation "'secret_to_public_state_out'" := ((
    result crypto_error_t dh_pk_t) : choice_type) (in custom pack_type at level 2).
Definition SECRET_TO_PUBLIC_STATE : nat :=
  (72).
Program Definition secret_to_public_state
   : package (fset.fset0) [interface] [interface
  #val #[ SECRET_TO_PUBLIC_STATE ] : secret_to_public_state_inp → secret_to_public_state_out
  ] :=
  (
    [package #def #[ SECRET_TO_PUBLIC_STATE ] (temp_inp : secret_to_public_state_inp) : secret_to_public_state_out { 
    let '(group_name_46 , x_47) := temp_inp : named_group_t '× dh_sk_t in
    ({ code  temp_71 ←
        ((({ code match group_name_46 with
              | Secp256r1 => '(temp_51 : p256_scalar_t) ←
                (nat_mod_from_byte_seq_be (x_47)) ;;
               temp_53 ←
                (p256_point_mul_base (temp_51)) ;;
               temp_61 ←
                ((({ code match temp_53 with
                      | inl (x_48, y_49) => temp_55 ←
                        (nat_mod_to_byte_seq_be (x_48)) ;;
                       temp_57 ←
                        (nat_mod_to_byte_seq_be (y_49)) ;;
                       '(temp_59 : seq uint8) ←
                        (seq_concat (temp_55) (temp_57)) ;;
                       ret (@inl dh_pk_t crypto_error_t (temp_59))
                      | inr _ => ret (@inr dh_pk_t crypto_error_t (CryptoError))
                      end } : code _ _ _))) ;;
               ret (temp_61)
              | X25519 => '(temp_63 : x25519_serialized_scalar_t) ←
                (array_from_seq (32) (x_47)) ;;
               temp_65 ←
                (x25519_secret_to_public (temp_63)) ;;
               '(temp_67 : seq uint8) ←
                (array_to_seq (temp_65)) ;;
               '(temp_69 : dh_pk_t) ←
                (seq_from_seq (temp_67)) ;;
               ret (@inl dh_pk_t crypto_error_t (temp_69))
              end } : code _ _ _))) ;;
      @ret ((result crypto_error_t dh_pk_t)) (temp_71) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_secret_to_public_state : package _ _ _ :=
  (secret_to_public_state).
Fail Next Obligation.

Notation "'secret_to_public_inp'" :=(
  named_group_t '× dh_sk_t : choice_type) (in custom pack_type at level 2).
Notation "'secret_to_public_out'" :=((
    result crypto_error_t dh_pk_t) : choice_type) (in custom pack_type at level 2).
Definition SECRET_TO_PUBLIC : nat :=
  (73).
Program Definition secret_to_public
  (group_name_46 : named_group_t)
  (x_47 : dh_sk_t)
  :both (fset.fset0) [interface
  #val #[ P256_POINT_MUL_BASE ] : p256_point_mul_base_inp → p256_point_mul_base_out ;
  #val #[ X25519_SECRET_TO_PUBLIC ] : x25519_secret_to_public_inp → x25519_secret_to_public_out
  ] ((result crypto_error_t dh_pk_t)) :=
  #import {sig #[ P256_POINT_MUL_BASE ] : p256_point_mul_base_inp → p256_point_mul_base_out } as p256_point_mul_base ;;
  let p256_point_mul_base := fun x_0 => p256_point_mul_base (x_0) in
  #import {sig #[ X25519_SECRET_TO_PUBLIC ] : x25519_secret_to_public_inp → x25519_secret_to_public_out } as x25519_secret_to_public ;;
  let x25519_secret_to_public := fun x_0 => x25519_secret_to_public (x_0) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) .
Fail Next Obligation.

Definition p256_check_point_len_pure
  (p_74 : dh_pk_t)
  : (result crypto_error_t unit) :=
  (if (((seq_len (p_74)) !=.? (usize 64))):bool_ChoiceEquality then (
      @Err unit crypto_error_t (CryptoError)) else (@Ok unit crypto_error_t (
        tt))).
Definition p256_check_point_len_pure_code
  (p_74 : dh_pk_t)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t unit))) :=
  lift_to_code (p256_check_point_len_pure p_74).


Notation "'p256_check_point_len_state_inp'" := (
  dh_pk_t : choice_type) (in custom pack_type at level 2).
Notation "'p256_check_point_len_state_out'" := ((
    result crypto_error_t unit_ChoiceEquality) : choice_type) (in custom pack_type at level 2).
Definition P256_CHECK_POINT_LEN_STATE : nat :=
  (79).
Program Definition p256_check_point_len_state
   : package (fset.fset0) [interface] [interface
  #val #[ P256_CHECK_POINT_LEN_STATE ] : p256_check_point_len_state_inp → p256_check_point_len_state_out
  ] :=
  (
    [package #def #[ P256_CHECK_POINT_LEN_STATE ] (temp_inp : p256_check_point_len_state_inp) : p256_check_point_len_state_out { 
    let '(p_74) := temp_inp : dh_pk_t in
    ({ code  '(temp_76 : uint_size) ←
        (seq_len (p_74)) ;;
       '(temp_78 : bool_ChoiceEquality) ←
        ((temp_76) !=.? (usize 64)) ;;
      @ret ((result crypto_error_t unit_ChoiceEquality)) ((if (
            temp_78):bool_ChoiceEquality then (*inline*) (
            @inr unit_ChoiceEquality crypto_error_t (CryptoError)) else (
            @inl unit_ChoiceEquality crypto_error_t (tt)))) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_p256_check_point_len_state : package _ _ _ :=
  (p256_check_point_len_state).
Fail Next Obligation.

Notation "'p256_check_point_len_inp'" :=(
  dh_pk_t : choice_type) (in custom pack_type at level 2).
Notation "'p256_check_point_len_out'" :=((
    result crypto_error_t unit_ChoiceEquality) : choice_type) (in custom pack_type at level 2).
Definition P256_CHECK_POINT_LEN : nat :=
  (80).
Program Definition p256_check_point_len
  (p_74 : dh_pk_t)
  :both (fset.fset0) [interface] ((
      result crypto_error_t unit_ChoiceEquality)) :=
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
    if is_pure (I := [interface]) ((seq_len (lift_to_both0 p_74)) !=.? (
        lift_to_both0 (usize 64)))
    then @Err unit_ChoiceEquality crypto_error_t (CryptoError)
    else @Ok unit_ChoiceEquality crypto_error_t (tt))
  .
Fail Next Obligation.

Definition p256_ecdh_pure
  (x_81 : dh_sk_t)
  (y_82 : dh_pk_t)
  : (result crypto_error_t key_t) :=
   _ m( _ ) ⇠ (p256_check_point_len (y_82)) ;;
  (let pk_83 : (p256_field_element_t '× p256_field_element_t) :=
      prod_ce(
        nat_mod_from_byte_seq_be (seq_slice_range (y_82) (prod_ce(
              usize 0,
              usize 32
            ))),
        nat_mod_from_byte_seq_be (seq_slice_range (y_82) (prod_ce(
              usize 32,
              usize 64
            )))
      ) in 
    match p256_point_mul (nat_mod_from_byte_seq_be (x_81)) (pk_83) with
    | Ok (x_84, y_85) => @Ok key_t crypto_error_t (seq_concat (
        nat_mod_to_byte_seq_be (x_84)) (nat_mod_to_byte_seq_be (y_85)))
    | Err _ => @Err key_t crypto_error_t (CryptoError)
    end).
Definition p256_ecdh_pure_code
  (x_81 : dh_sk_t)
  (y_82 : dh_pk_t)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t key_t))) :=
  lift_to_code (p256_ecdh_pure x_81 y_82).


Notation "'p256_ecdh_state_inp'" := (
  dh_sk_t '× dh_pk_t : choice_type) (in custom pack_type at level 2).
Notation "'p256_ecdh_state_out'" := ((
    result crypto_error_t key_t) : choice_type) (in custom pack_type at level 2).
Definition P256_ECDH_STATE : nat :=
  (108).
Program Definition p256_ecdh_state
   : package (fset.fset0) [interface
  #val #[ P256_CHECK_POINT_LEN_STATE ] : p256_check_point_len_state_inp → p256_check_point_len_state_out
  ] [interface
  #val #[ P256_ECDH_STATE ] : p256_ecdh_state_inp → p256_ecdh_state_out ] :=
  (
    [package #def #[ P256_ECDH_STATE ] (temp_inp : p256_ecdh_state_inp) : p256_ecdh_state_out { 
    let '(x_81 , y_82) := temp_inp : dh_sk_t '× dh_pk_t in
    #import {sig #[ P256_CHECK_POINT_LEN_STATE ] : p256_check_point_len_state_inp → p256_check_point_len_state_out } as p256_check_point_len_state ;;
    let p256_check_point_len_state := fun x_0 => p256_check_point_len_state (
      x_0) in
    ({ code bnd(
        ChoiceEqualityMonad.result_bind_code crypto_error_t , unit_ChoiceEquality , _ , fset.fset0) _ ⇠
      (({ code  temp_87 ←
            (p256_check_point_len (y_82)) ;;
          @ret _ (temp_87) } : code (fset.fset0) [interface] _)) in
      ({ code  '(pk_83 : (p256_field_element_t '× p256_field_element_t)) ←
          ( '(temp_89 : dh_pk_t) ←
              (seq_slice_range (y_82) (prod_ce(usize 0, usize 32))) ;;
             '(temp_91 : p256_field_element_t) ←
              (nat_mod_from_byte_seq_be (temp_89)) ;;
             '(temp_93 : dh_pk_t) ←
              (seq_slice_range (y_82) (prod_ce(usize 32, usize 64))) ;;
             '(temp_95 : p256_field_element_t) ←
              (nat_mod_from_byte_seq_be (temp_93)) ;;
            ret (prod_ce(temp_91, temp_95))) ;;
         '(temp_97 : p256_scalar_t) ←
          (nat_mod_from_byte_seq_be (x_81)) ;;
         temp_99 ←
          (p256_point_mul (temp_97) (pk_83)) ;;
         temp_107 ←
          ((({ code match temp_99 with
                | inl (x_84, y_85) => temp_101 ←
                  (nat_mod_to_byte_seq_be (x_84)) ;;
                 temp_103 ←
                  (nat_mod_to_byte_seq_be (y_85)) ;;
                 '(temp_105 : seq uint8) ←
                  (seq_concat (temp_101) (temp_103)) ;;
                 ret (@inl key_t crypto_error_t (temp_105))
                | inr _ => ret (@inr key_t crypto_error_t (CryptoError))
                end } : code _ _ _))) ;;
        @ret ((result crypto_error_t key_t)) (temp_107) } : code (
          fset.fset0) [interface
        #val #[ P256_CHECK_POINT_LEN_STATE ] : p256_check_point_len_state_inp → p256_check_point_len_state_out
        ] _) } : code (fset.fset0) [interface
      #val #[ P256_CHECK_POINT_LEN_STATE ] : p256_check_point_len_state_inp → p256_check_point_len_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_p256_ecdh_state : package _ _ _ :=
  (seq_link p256_ecdh_state link_rest(package_p256_check_point_len_state)).
Fail Next Obligation.

Notation "'p256_ecdh_inp'" :=(
  dh_sk_t '× dh_pk_t : choice_type) (in custom pack_type at level 2).
Notation "'p256_ecdh_out'" :=((
    result crypto_error_t key_t) : choice_type) (in custom pack_type at level 2).
Definition P256_ECDH : nat :=
  (109).
Program Definition p256_ecdh
  (x_81 : dh_sk_t)
  (y_82 : dh_pk_t)
  :both (fset.fset0) [interface
  #val #[ P256_CHECK_POINT_LEN ] : p256_check_point_len_inp → p256_check_point_len_out ;
  #val #[ P256_POINT_MUL ] : p256_point_mul_inp → p256_point_mul_out ] ((
      result crypto_error_t key_t)) :=
  #import {sig #[ P256_CHECK_POINT_LEN ] : p256_check_point_len_inp → p256_check_point_len_out } as p256_check_point_len ;;
  let p256_check_point_len := fun x_0 => p256_check_point_len (x_0) in
  #import {sig #[ P256_POINT_MUL ] : p256_point_mul_inp → p256_point_mul_out } as p256_point_mul ;;
  let p256_point_mul := fun x_0 x_1 => p256_point_mul (x_0,x_1) in
  letbnd(
      ChoiceEqualityMonad.result_bind_both crypto_error_t) _ : unit_ChoiceEquality :=
    p256_check_point_len (lift_to_both0 y_82) in
  letb pk_83 : (p256_field_element_t '× p256_field_element_t) :=
    prod_b(
      nat_mod_from_byte_seq_be (seq_slice_range (lift_to_both0 y_82) (prod_b(
            lift_to_both0 (usize 0),
            lift_to_both0 (usize 32)
          ))),
      nat_mod_from_byte_seq_be (seq_slice_range (lift_to_both0 y_82) (prod_b(
            lift_to_both0 (usize 32),
            lift_to_both0 (usize 64)
          )))
    ) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match)
  .
Fail Next Obligation.

Definition ecdh_pure
  (group_name_110 : named_group_t)
  (x_111 : dh_sk_t)
  (y_112 : dh_pk_t)
  : (result crypto_error_t key_t) :=
  match group_name_110 with
  | Secp256r1 => p256_ecdh (x_111) (y_112)
  | X25519 => @Ok key_t crypto_error_t (seq_from_seq (
      array_to_seq (x25519_scalarmult (array_from_seq (32) (x_111)) (
        array_from_seq (32) (y_112)))))
  end.
Definition ecdh_pure_code
  (group_name_110 : named_group_t)
  (x_111 : dh_sk_t)
  (y_112 : dh_pk_t)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t key_t))) :=
  lift_to_code (ecdh_pure group_name_110 x_111 y_112).


Notation "'ecdh_state_inp'" := (
  named_group_t '× dh_sk_t '× dh_pk_t : choice_type) (in custom pack_type at level 2).
Notation "'ecdh_state_out'" := ((
    result crypto_error_t key_t) : choice_type) (in custom pack_type at level 2).
Definition ECDH_STATE : nat :=
  (127).
Program Definition ecdh_state
   : package (fset.fset0) [interface
  #val #[ P256_ECDH_STATE ] : p256_ecdh_state_inp → p256_ecdh_state_out
  ] [interface #val #[ ECDH_STATE ] : ecdh_state_inp → ecdh_state_out ] :=
  ([package #def #[ ECDH_STATE ] (temp_inp : ecdh_state_inp) : ecdh_state_out { 
    let '(
      group_name_110 , x_111 , y_112) := temp_inp : named_group_t '× dh_sk_t '× dh_pk_t in
    #import {sig #[ P256_ECDH_STATE ] : p256_ecdh_state_inp → p256_ecdh_state_out } as p256_ecdh_state ;;
    let p256_ecdh_state := fun x_0 x_1 => p256_ecdh_state (x_0,x_1) in
    ({ code  temp_126 ←
        ((({ code match group_name_110 with
              | Secp256r1 => temp_114 ←
                (p256_ecdh (x_111) (y_112)) ;;
               ret (temp_114)
              | X25519 => '(temp_116 : x25519_serialized_scalar_t) ←
                (array_from_seq (32) (x_111)) ;;
               '(temp_118 : x25519_serialized_point_t) ←
                (array_from_seq (32) (y_112)) ;;
               temp_120 ←
                (x25519_scalarmult (temp_116) (temp_118)) ;;
               '(temp_122 : seq uint8) ←
                (array_to_seq (temp_120)) ;;
               '(temp_124 : dh_pk_t) ←
                (seq_from_seq (temp_122)) ;;
               ret (@inl key_t crypto_error_t (temp_124))
              end } : code _ _ _))) ;;
      @ret ((result crypto_error_t key_t)) (temp_126) } : code (
        fset.fset0) [interface
      #val #[ P256_ECDH_STATE ] : p256_ecdh_state_inp → p256_ecdh_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_ecdh_state : package _ _ _ :=
  (seq_link ecdh_state link_rest(package_p256_ecdh_state)).
Fail Next Obligation.

Notation "'ecdh_inp'" :=(
  named_group_t '× dh_sk_t '× dh_pk_t : choice_type) (in custom pack_type at level 2).
Notation "'ecdh_out'" :=((
    result crypto_error_t key_t) : choice_type) (in custom pack_type at level 2).
Definition ECDH : nat :=
  (128).
Program Definition ecdh
  (group_name_110 : named_group_t)
  (x_111 : dh_sk_t)
  (y_112 : dh_pk_t)
  :both (fset.fset0) [interface
  #val #[ P256_ECDH ] : p256_ecdh_inp → p256_ecdh_out ;
  #val #[ X25519_SCALARMULT ] : x25519_scalarmult_inp → x25519_scalarmult_out
  ] ((result crypto_error_t key_t)) :=
  #import {sig #[ P256_ECDH ] : p256_ecdh_inp → p256_ecdh_out } as p256_ecdh ;;
  let p256_ecdh := fun x_0 x_1 => p256_ecdh (x_0,x_1) in
  #import {sig #[ X25519_SCALARMULT ] : x25519_scalarmult_inp → x25519_scalarmult_out } as x25519_scalarmult ;;
  let x25519_scalarmult := fun x_0 x_1 => x25519_scalarmult (x_0,x_1) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) .
Fail Next Obligation.

Notation "'kem_scheme_t'" := (named_group_t) : hacspec_scope.

Notation "'kem_sk_t'" := (byte_seq) : hacspec_scope.

Notation "'kem_pk_t'" := (byte_seq) : hacspec_scope.

Definition kem_priv_len_pure (ks_129 : kem_scheme_t) : uint_size :=
  dh_priv_len (ks_129).
Definition kem_priv_len_pure_code
  (ks_129 : kem_scheme_t)
  : code fset.fset0 [interface] (@ct (uint_size)) :=
  lift_to_code (kem_priv_len_pure ks_129).


Notation "'kem_priv_len_state_inp'" := (
  kem_scheme_t : choice_type) (in custom pack_type at level 2).
Notation "'kem_priv_len_state_out'" := (
  uint_size : choice_type) (in custom pack_type at level 2).
Definition KEM_PRIV_LEN_STATE : nat :=
  (132).
Program Definition kem_priv_len_state
   : package (fset.fset0) [interface
  #val #[ DH_PRIV_LEN_STATE ] : dh_priv_len_state_inp → dh_priv_len_state_out
  ] [interface
  #val #[ KEM_PRIV_LEN_STATE ] : kem_priv_len_state_inp → kem_priv_len_state_out
  ] :=
  (
    [package #def #[ KEM_PRIV_LEN_STATE ] (temp_inp : kem_priv_len_state_inp) : kem_priv_len_state_out { 
    let '(ks_129) := temp_inp : kem_scheme_t in
    #import {sig #[ DH_PRIV_LEN_STATE ] : dh_priv_len_state_inp → dh_priv_len_state_out } as dh_priv_len_state ;;
    let dh_priv_len_state := fun x_0 => dh_priv_len_state (x_0) in
    ({ code  temp_131 ←
        (dh_priv_len (ks_129)) ;;
      @ret (uint_size) (temp_131) } : code (fset.fset0) [interface
      #val #[ DH_PRIV_LEN_STATE ] : dh_priv_len_state_inp → dh_priv_len_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_kem_priv_len_state : package _ _ _ :=
  (seq_link kem_priv_len_state link_rest(package_dh_priv_len_state)).
Fail Next Obligation.

Notation "'kem_priv_len_inp'" :=(
  kem_scheme_t : choice_type) (in custom pack_type at level 2).
Notation "'kem_priv_len_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Definition KEM_PRIV_LEN : nat :=
  (133).
Program Definition kem_priv_len
  (ks_129 : kem_scheme_t)
  :both (fset.fset0) [interface
  #val #[ DH_PRIV_LEN ] : dh_priv_len_inp → dh_priv_len_out ] (uint_size) :=
  #import {sig #[ DH_PRIV_LEN ] : dh_priv_len_inp → dh_priv_len_out } as dh_priv_len ;;
  let dh_priv_len := fun x_0 => dh_priv_len (x_0) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (dh_priv_len (
      lift_to_both0 ks_129))
  .
Fail Next Obligation.

Definition kem_pub_len_pure (ks_134 : kem_scheme_t) : uint_size :=
  dh_pub_len (ks_134).
Definition kem_pub_len_pure_code
  (ks_134 : kem_scheme_t)
  : code fset.fset0 [interface] (@ct (uint_size)) :=
  lift_to_code (kem_pub_len_pure ks_134).


Notation "'kem_pub_len_state_inp'" := (
  kem_scheme_t : choice_type) (in custom pack_type at level 2).
Notation "'kem_pub_len_state_out'" := (
  uint_size : choice_type) (in custom pack_type at level 2).
Definition KEM_PUB_LEN_STATE : nat :=
  (137).
Program Definition kem_pub_len_state
   : package (fset.fset0) [interface
  #val #[ DH_PUB_LEN_STATE ] : dh_pub_len_state_inp → dh_pub_len_state_out
  ] [interface
  #val #[ KEM_PUB_LEN_STATE ] : kem_pub_len_state_inp → kem_pub_len_state_out
  ] :=
  (
    [package #def #[ KEM_PUB_LEN_STATE ] (temp_inp : kem_pub_len_state_inp) : kem_pub_len_state_out { 
    let '(ks_134) := temp_inp : kem_scheme_t in
    #import {sig #[ DH_PUB_LEN_STATE ] : dh_pub_len_state_inp → dh_pub_len_state_out } as dh_pub_len_state ;;
    let dh_pub_len_state := fun x_0 => dh_pub_len_state (x_0) in
    ({ code  temp_136 ←
        (dh_pub_len (ks_134)) ;;
      @ret (uint_size) (temp_136) } : code (fset.fset0) [interface
      #val #[ DH_PUB_LEN_STATE ] : dh_pub_len_state_inp → dh_pub_len_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_kem_pub_len_state : package _ _ _ :=
  (seq_link kem_pub_len_state link_rest(package_dh_pub_len_state)).
Fail Next Obligation.

Notation "'kem_pub_len_inp'" :=(
  kem_scheme_t : choice_type) (in custom pack_type at level 2).
Notation "'kem_pub_len_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Definition KEM_PUB_LEN : nat :=
  (138).
Program Definition kem_pub_len
  (ks_134 : kem_scheme_t)
  :both (fset.fset0) [interface
  #val #[ DH_PUB_LEN ] : dh_pub_len_inp → dh_pub_len_out ] (uint_size) :=
  #import {sig #[ DH_PUB_LEN ] : dh_pub_len_inp → dh_pub_len_out } as dh_pub_len ;;
  let dh_pub_len := fun x_0 => dh_pub_len (x_0) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (dh_pub_len (
      lift_to_both0 ks_134))
  .
Fail Next Obligation.

Definition kem_priv_to_pub_pure
  (ks_139 : kem_scheme_t)
  (sk_140 : kem_sk_t)
  : (result crypto_error_t kem_pk_t) :=
  secret_to_public (ks_139) (sk_140).
Definition kem_priv_to_pub_pure_code
  (ks_139 : kem_scheme_t)
  (sk_140 : kem_sk_t)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t kem_pk_t))) :=
  lift_to_code (kem_priv_to_pub_pure ks_139 sk_140).


Notation "'kem_priv_to_pub_state_inp'" := (
  kem_scheme_t '× kem_sk_t : choice_type) (in custom pack_type at level 2).
Notation "'kem_priv_to_pub_state_out'" := ((
    result crypto_error_t kem_pk_t) : choice_type) (in custom pack_type at level 2).
Definition KEM_PRIV_TO_PUB_STATE : nat :=
  (143).
Program Definition kem_priv_to_pub_state
   : package (fset.fset0) [interface
  #val #[ SECRET_TO_PUBLIC_STATE ] : secret_to_public_state_inp → secret_to_public_state_out
  ] [interface
  #val #[ KEM_PRIV_TO_PUB_STATE ] : kem_priv_to_pub_state_inp → kem_priv_to_pub_state_out
  ] :=
  (
    [package #def #[ KEM_PRIV_TO_PUB_STATE ] (temp_inp : kem_priv_to_pub_state_inp) : kem_priv_to_pub_state_out { 
    let '(ks_139 , sk_140) := temp_inp : kem_scheme_t '× kem_sk_t in
    #import {sig #[ SECRET_TO_PUBLIC_STATE ] : secret_to_public_state_inp → secret_to_public_state_out } as secret_to_public_state ;;
    let secret_to_public_state := fun x_0 x_1 => secret_to_public_state (
      x_0,x_1) in
    ({ code  temp_142 ←
        (secret_to_public (ks_139) (sk_140)) ;;
      @ret ((result crypto_error_t dh_pk_t)) (temp_142) } : code (
        fset.fset0) [interface
      #val #[ SECRET_TO_PUBLIC_STATE ] : secret_to_public_state_inp → secret_to_public_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_kem_priv_to_pub_state : package _ _ _ :=
  (seq_link kem_priv_to_pub_state link_rest(package_secret_to_public_state)).
Fail Next Obligation.

Notation "'kem_priv_to_pub_inp'" :=(
  kem_scheme_t '× kem_sk_t : choice_type) (in custom pack_type at level 2).
Notation "'kem_priv_to_pub_out'" :=((
    result crypto_error_t kem_pk_t) : choice_type) (in custom pack_type at level 2).
Definition KEM_PRIV_TO_PUB : nat :=
  (144).
Program Definition kem_priv_to_pub
  (ks_139 : kem_scheme_t)
  (sk_140 : kem_sk_t)
  :both (fset.fset0) [interface
  #val #[ SECRET_TO_PUBLIC ] : secret_to_public_inp → secret_to_public_out ] (
    (result crypto_error_t kem_pk_t)) :=
  #import {sig #[ SECRET_TO_PUBLIC ] : secret_to_public_inp → secret_to_public_out } as secret_to_public ;;
  let secret_to_public := fun x_0 x_1 => secret_to_public (x_0,x_1) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (secret_to_public (
      lift_to_both0 ks_139) (lift_to_both0 sk_140))
  .
Fail Next Obligation.

Definition kem_keygen_inner_pure
  (ks_145 : kem_scheme_t)
  (ent_146 : entropy_t)
  : (result crypto_error_t (kem_sk_t '× kem_pk_t)) :=
  let sk_147 : seq uint8 :=
    seq_from_seq (seq_slice_range (ent_146) (prod_ce(
          usize 0,
          dh_priv_len (ks_145)
        ))) in 
   pk_148 m( _ ) ⇠ (kem_priv_to_pub (ks_145) (sk_147)) ;;
  (@Ok (kem_sk_t '× kem_pk_t) crypto_error_t (prod_ce(sk_147, pk_148))).
Definition kem_keygen_inner_pure_code
  (ks_145 : kem_scheme_t)
  (ent_146 : entropy_t)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t (
        kem_sk_t '×
        kem_pk_t
      )))) :=
  lift_to_code (kem_keygen_inner_pure ks_145 ent_146).


Notation "'kem_keygen_inner_state_inp'" := (
  kem_scheme_t '× entropy_t : choice_type) (in custom pack_type at level 2).
Notation "'kem_keygen_inner_state_out'" := ((result crypto_error_t (
      kem_sk_t '×
      kem_pk_t
    )) : choice_type) (in custom pack_type at level 2).
Definition KEM_KEYGEN_INNER_STATE : nat :=
  (157).
Program Definition kem_keygen_inner_state
   : package (fset.fset0) [interface
  #val #[ DH_PRIV_LEN_STATE ] : dh_priv_len_state_inp → dh_priv_len_state_out ;
  #val #[ KEM_PRIV_TO_PUB_STATE ] : kem_priv_to_pub_state_inp → kem_priv_to_pub_state_out
  ] [interface
  #val #[ KEM_KEYGEN_INNER_STATE ] : kem_keygen_inner_state_inp → kem_keygen_inner_state_out
  ] :=
  (
    [package #def #[ KEM_KEYGEN_INNER_STATE ] (temp_inp : kem_keygen_inner_state_inp) : kem_keygen_inner_state_out { 
    let '(ks_145 , ent_146) := temp_inp : kem_scheme_t '× entropy_t in
    #import {sig #[ DH_PRIV_LEN_STATE ] : dh_priv_len_state_inp → dh_priv_len_state_out } as dh_priv_len_state ;;
    let dh_priv_len_state := fun x_0 => dh_priv_len_state (x_0) in
    #import {sig #[ KEM_PRIV_TO_PUB_STATE ] : kem_priv_to_pub_state_inp → kem_priv_to_pub_state_out } as kem_priv_to_pub_state ;;
    let kem_priv_to_pub_state := fun x_0 x_1 => kem_priv_to_pub_state (
      x_0,x_1) in
    ({ code  '(sk_147 : seq uint8) ←
        ( temp_150 ←
            (dh_priv_len (ks_145)) ;;
           '(temp_152 : entropy_t) ←
            (seq_slice_range (ent_146) (prod_ce(usize 0, temp_150))) ;;
           '(temp_154 : kem_sk_t) ←
            (seq_from_seq (temp_152)) ;;
          ret (temp_154)) ;;
      bnd(
        ChoiceEqualityMonad.result_bind_code crypto_error_t , kem_pk_t , _ , fset.fset0) pk_148 ⇠
      (({ code  temp_156 ←
            (kem_priv_to_pub (ks_145) (sk_147)) ;;
          @ret _ (temp_156) } : code (fset.fset0) [interface] _)) in
      ({ code @ret ((result crypto_error_t (kem_sk_t '× kem_pk_t))) (@inl (
            kem_sk_t '×
            kem_pk_t
          ) crypto_error_t (prod_ce(sk_147, pk_148))) } : code (
          fset.fset0) [interface
        #val #[ DH_PRIV_LEN_STATE ] : dh_priv_len_state_inp → dh_priv_len_state_out ;
        #val #[ KEM_PRIV_TO_PUB_STATE ] : kem_priv_to_pub_state_inp → kem_priv_to_pub_state_out
        ] _) } : code (fset.fset0) [interface
      #val #[ DH_PRIV_LEN_STATE ] : dh_priv_len_state_inp → dh_priv_len_state_out ;
      #val #[ KEM_PRIV_TO_PUB_STATE ] : kem_priv_to_pub_state_inp → kem_priv_to_pub_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_kem_keygen_inner_state : package _ _ _ :=
  (seq_link kem_keygen_inner_state link_rest(
      package_dh_priv_len_state,package_kem_priv_to_pub_state)).
Fail Next Obligation.

Notation "'kem_keygen_inner_inp'" :=(
  kem_scheme_t '× entropy_t : choice_type) (in custom pack_type at level 2).
Notation "'kem_keygen_inner_out'" :=((result crypto_error_t (
      kem_sk_t '×
      kem_pk_t
    )) : choice_type) (in custom pack_type at level 2).
Definition KEM_KEYGEN_INNER : nat :=
  (158).
Program Definition kem_keygen_inner
  (ks_145 : kem_scheme_t)
  (ent_146 : entropy_t)
  :both (fset.fset0) [interface
  #val #[ DH_PRIV_LEN ] : dh_priv_len_inp → dh_priv_len_out ;
  #val #[ KEM_PRIV_TO_PUB ] : kem_priv_to_pub_inp → kem_priv_to_pub_out ] ((
      result crypto_error_t (kem_sk_t '× kem_pk_t))) :=
  #import {sig #[ DH_PRIV_LEN ] : dh_priv_len_inp → dh_priv_len_out } as dh_priv_len ;;
  let dh_priv_len := fun x_0 => dh_priv_len (x_0) in
  #import {sig #[ KEM_PRIV_TO_PUB ] : kem_priv_to_pub_inp → kem_priv_to_pub_out } as kem_priv_to_pub ;;
  let kem_priv_to_pub := fun x_0 x_1 => kem_priv_to_pub (x_0,x_1) in
  letb sk_147 : seq uint8 :=
    seq_from_seq (seq_slice_range (lift_to_both0 ent_146) (prod_b(
          lift_to_both0 (usize 0),
          dh_priv_len (lift_to_both0 ks_145)
        ))) in
  letbnd(
      ChoiceEqualityMonad.result_bind_both crypto_error_t) pk_148 : kem_pk_t :=
    kem_priv_to_pub (lift_to_both0 ks_145) (lift_to_both0 sk_147) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (kem_sk_t '× kem_pk_t
    ) crypto_error_t (prod_b(lift_to_both0 sk_147, lift_to_both0 pk_148)))
  .
Fail Next Obligation.

Definition kem_keygen_pure
  (ks_159 : kem_scheme_t)
  (ent_160 : entropy_t)
  : (result crypto_error_t (kem_sk_t '× kem_pk_t)) :=
  (if (((seq_len (ent_160)) <.? (dh_priv_len (
            ks_159)))):bool_ChoiceEquality then (@Err (kem_sk_t '× kem_pk_t
      ) crypto_error_t (InsufficientEntropy)) else (kem_keygen_inner (ks_159) (
        ent_160))).
Definition kem_keygen_pure_code
  (ks_159 : kem_scheme_t)
  (ent_160 : entropy_t)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t (
        kem_sk_t '×
        kem_pk_t
      )))) :=
  lift_to_code (kem_keygen_pure ks_159 ent_160).


Notation "'kem_keygen_state_inp'" := (
  kem_scheme_t '× entropy_t : choice_type) (in custom pack_type at level 2).
Notation "'kem_keygen_state_out'" := ((result crypto_error_t (
      kem_sk_t '×
      kem_pk_t
    )) : choice_type) (in custom pack_type at level 2).
Definition KEM_KEYGEN_STATE : nat :=
  (169).
Program Definition kem_keygen_state
   : package (fset.fset0) [interface
  #val #[ DH_PRIV_LEN_STATE ] : dh_priv_len_state_inp → dh_priv_len_state_out ;
  #val #[ KEM_KEYGEN_INNER_STATE ] : kem_keygen_inner_state_inp → kem_keygen_inner_state_out
  ] [interface
  #val #[ KEM_KEYGEN_STATE ] : kem_keygen_state_inp → kem_keygen_state_out
  ] :=
  (
    [package #def #[ KEM_KEYGEN_STATE ] (temp_inp : kem_keygen_state_inp) : kem_keygen_state_out { 
    let '(ks_159 , ent_160) := temp_inp : kem_scheme_t '× entropy_t in
    #import {sig #[ DH_PRIV_LEN_STATE ] : dh_priv_len_state_inp → dh_priv_len_state_out } as dh_priv_len_state ;;
    let dh_priv_len_state := fun x_0 => dh_priv_len_state (x_0) in
    #import {sig #[ KEM_KEYGEN_INNER_STATE ] : kem_keygen_inner_state_inp → kem_keygen_inner_state_out } as kem_keygen_inner_state ;;
    let kem_keygen_inner_state := fun x_0 x_1 => kem_keygen_inner_state (
      x_0,x_1) in
    ({ code  '(temp_162 : uint_size) ←
        (seq_len (ent_160)) ;;
       temp_164 ←
        (dh_priv_len (ks_159)) ;;
       '(temp_166 : bool_ChoiceEquality) ←
        ((temp_162) <.? (temp_164)) ;;
       temp_168 ←
        (kem_keygen_inner (ks_159) (ent_160)) ;;
      @ret ((result crypto_error_t (kem_sk_t '× kem_pk_t))) ((if (
            temp_166):bool_ChoiceEquality then (*inline*) (@inr (
              kem_sk_t '×
              kem_pk_t
            ) crypto_error_t (InsufficientEntropy)) else (temp_168))) } : code (
        fset.fset0) [interface
      #val #[ DH_PRIV_LEN_STATE ] : dh_priv_len_state_inp → dh_priv_len_state_out ;
      #val #[ KEM_KEYGEN_INNER_STATE ] : kem_keygen_inner_state_inp → kem_keygen_inner_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_kem_keygen_state : package _ _ _ :=
  (seq_link kem_keygen_state link_rest(
      package_dh_priv_len_state,package_kem_keygen_inner_state)).
Fail Next Obligation.

Notation "'kem_keygen_inp'" :=(
  kem_scheme_t '× entropy_t : choice_type) (in custom pack_type at level 2).
Notation "'kem_keygen_out'" :=((result crypto_error_t (kem_sk_t '× kem_pk_t
    )) : choice_type) (in custom pack_type at level 2).
Definition KEM_KEYGEN : nat :=
  (170).
Program Definition kem_keygen
  (ks_159 : kem_scheme_t)
  (ent_160 : entropy_t)
  :both (fset.fset0) [interface
  #val #[ DH_PRIV_LEN ] : dh_priv_len_inp → dh_priv_len_out ;
  #val #[ KEM_KEYGEN_INNER ] : kem_keygen_inner_inp → kem_keygen_inner_out ] (
    (result crypto_error_t (kem_sk_t '× kem_pk_t))) :=
  #import {sig #[ DH_PRIV_LEN ] : dh_priv_len_inp → dh_priv_len_out } as dh_priv_len ;;
  let dh_priv_len := fun x_0 => dh_priv_len (x_0) in
  #import {sig #[ KEM_KEYGEN_INNER ] : kem_keygen_inner_inp → kem_keygen_inner_out } as kem_keygen_inner ;;
  let kem_keygen_inner := fun x_0 x_1 => kem_keygen_inner (x_0,x_1) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
    if is_pure (I := [interface]) ((seq_len (lift_to_both0 ent_160)) <.? (
        dh_priv_len (lift_to_both0 ks_159)))
    then @Err (kem_sk_t '× kem_pk_t) crypto_error_t (InsufficientEntropy)
    else kem_keygen_inner (lift_to_both0 ks_159) (lift_to_both0 ent_160))
  .
Fail Next Obligation.

Definition kem_encap_pure
  (ks_171 : kem_scheme_t)
  (pk_172 : kem_pk_t)
  (ent_173 : entropy_t)
  : (result crypto_error_t (key_t '× byte_seq)) :=
   '(x_174, gx_175) m( _ ) ⇠ (kem_keygen (ks_171) (ent_173)) ;;
  ( gxy_176 m( _ ) ⇠ (ecdh (ks_171) (x_174) (pk_172)) ;;
    (@Ok (key_t '× byte_seq) crypto_error_t (prod_ce(gxy_176, gx_175)))).
Definition kem_encap_pure_code
  (ks_171 : kem_scheme_t)
  (pk_172 : kem_pk_t)
  (ent_173 : entropy_t)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t (key_t '× byte_seq
      )))) :=
  lift_to_code (kem_encap_pure ks_171 pk_172 ent_173).


Notation "'kem_encap_state_inp'" := (
  kem_scheme_t '× kem_pk_t '× entropy_t : choice_type) (in custom pack_type at level 2).
Notation "'kem_encap_state_out'" := ((result crypto_error_t (key_t '× byte_seq
    )) : choice_type) (in custom pack_type at level 2).
Definition KEM_ENCAP_STATE : nat :=
  (181).
Program Definition kem_encap_state
   : package (fset.fset0) [interface
  #val #[ ECDH_STATE ] : ecdh_state_inp → ecdh_state_out ;
  #val #[ KEM_KEYGEN_STATE ] : kem_keygen_state_inp → kem_keygen_state_out
  ] [interface
  #val #[ KEM_ENCAP_STATE ] : kem_encap_state_inp → kem_encap_state_out ] :=
  (
    [package #def #[ KEM_ENCAP_STATE ] (temp_inp : kem_encap_state_inp) : kem_encap_state_out { 
    let '(
      ks_171 , pk_172 , ent_173) := temp_inp : kem_scheme_t '× kem_pk_t '× entropy_t in
    #import {sig #[ ECDH_STATE ] : ecdh_state_inp → ecdh_state_out } as ecdh_state ;;
    let ecdh_state := fun x_0 x_1 x_2 => ecdh_state (x_0,x_1,x_2) in
    #import {sig #[ KEM_KEYGEN_STATE ] : kem_keygen_state_inp → kem_keygen_state_out } as kem_keygen_state ;;
    let kem_keygen_state := fun x_0 x_1 => kem_keygen_state (x_0,x_1) in
    ({ code bnd(ChoiceEqualityMonad.result_bind_code crypto_error_t , (
          kem_sk_t '×
          kem_pk_t
        ) , _ , fset.fset0) '(x_174, gx_175) ⇠
      (({ code  temp_178 ←
            (kem_keygen (ks_171) (ent_173)) ;;
          @ret _ (temp_178) } : code (fset.fset0) [interface] _)) in
      ({ code bnd(
          ChoiceEqualityMonad.result_bind_code crypto_error_t , key_t , _ , fset.fset0) gxy_176 ⇠
        (({ code  temp_180 ←
              (ecdh (ks_171) (x_174) (pk_172)) ;;
            @ret _ (temp_180) } : code (fset.fset0) [interface] _)) in
        ({ code @ret ((result crypto_error_t (key_t '× byte_seq))) (@inl (
              key_t '×
              byte_seq
            ) crypto_error_t (prod_ce(gxy_176, gx_175))) } : code (
            fset.fset0) [interface
          #val #[ ECDH_STATE ] : ecdh_state_inp → ecdh_state_out ;
          #val #[ KEM_KEYGEN_STATE ] : kem_keygen_state_inp → kem_keygen_state_out
          ] _) } : code (fset.fset0) [interface
        #val #[ ECDH_STATE ] : ecdh_state_inp → ecdh_state_out ;
        #val #[ KEM_KEYGEN_STATE ] : kem_keygen_state_inp → kem_keygen_state_out
        ] _) } : code (fset.fset0) [interface
      #val #[ ECDH_STATE ] : ecdh_state_inp → ecdh_state_out ;
      #val #[ KEM_KEYGEN_STATE ] : kem_keygen_state_inp → kem_keygen_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_kem_encap_state : package _ _ _ :=
  (seq_link kem_encap_state link_rest(
      package_ecdh_state,package_kem_keygen_state)).
Fail Next Obligation.

Notation "'kem_encap_inp'" :=(
  kem_scheme_t '× kem_pk_t '× entropy_t : choice_type) (in custom pack_type at level 2).
Notation "'kem_encap_out'" :=((result crypto_error_t (key_t '× byte_seq
    )) : choice_type) (in custom pack_type at level 2).
Definition KEM_ENCAP : nat :=
  (182).
Program Definition kem_encap
  (ks_171 : kem_scheme_t)
  (pk_172 : kem_pk_t)
  (ent_173 : entropy_t)
  :both (fset.fset0) [interface #val #[ ECDH ] : ecdh_inp → ecdh_out ;
  #val #[ KEM_KEYGEN ] : kem_keygen_inp → kem_keygen_out ] ((
      result crypto_error_t (key_t '× byte_seq))) :=
  #import {sig #[ ECDH ] : ecdh_inp → ecdh_out } as ecdh ;;
  let ecdh := fun x_0 x_1 x_2 => ecdh (x_0,x_1,x_2) in
  #import {sig #[ KEM_KEYGEN ] : kem_keygen_inp → kem_keygen_out } as kem_keygen ;;
  let kem_keygen := fun x_0 x_1 => kem_keygen (x_0,x_1) in
  letbnd(ChoiceEqualityMonad.result_bind_both crypto_error_t) '(x_174, gx_175
    ) : (kem_sk_t '× kem_pk_t) :=
    kem_keygen (lift_to_both0 ks_171) (lift_to_both0 ent_173) in
  letbnd(ChoiceEqualityMonad.result_bind_both crypto_error_t) gxy_176 : key_t :=
    ecdh (lift_to_both0 ks_171) (lift_to_both0 x_174) (lift_to_both0 pk_172) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (key_t '× byte_seq
    ) crypto_error_t (prod_b(lift_to_both0 gxy_176, lift_to_both0 gx_175)))
  .
Fail Next Obligation.

Definition kem_decap_pure
  (ks_183 : kem_scheme_t)
  (ct_184 : byte_seq)
  (sk_185 : kem_sk_t)
  : (result crypto_error_t key_t) :=
   gxy_186 m( _ ) ⇠ (ecdh (ks_183) (sk_185) (ct_184)) ;;
  (@Ok key_t crypto_error_t (gxy_186)).
Definition kem_decap_pure_code
  (ks_183 : kem_scheme_t)
  (ct_184 : byte_seq)
  (sk_185 : kem_sk_t)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t key_t))) :=
  lift_to_code (kem_decap_pure ks_183 ct_184 sk_185).


Notation "'kem_decap_state_inp'" := (
  kem_scheme_t '× byte_seq '× kem_sk_t : choice_type) (in custom pack_type at level 2).
Notation "'kem_decap_state_out'" := ((
    result crypto_error_t key_t) : choice_type) (in custom pack_type at level 2).
Definition KEM_DECAP_STATE : nat :=
  (189).
Program Definition kem_decap_state
   : package (fset.fset0) [interface
  #val #[ ECDH_STATE ] : ecdh_state_inp → ecdh_state_out ] [interface
  #val #[ KEM_DECAP_STATE ] : kem_decap_state_inp → kem_decap_state_out ] :=
  (
    [package #def #[ KEM_DECAP_STATE ] (temp_inp : kem_decap_state_inp) : kem_decap_state_out { 
    let '(
      ks_183 , ct_184 , sk_185) := temp_inp : kem_scheme_t '× byte_seq '× kem_sk_t in
    #import {sig #[ ECDH_STATE ] : ecdh_state_inp → ecdh_state_out } as ecdh_state ;;
    let ecdh_state := fun x_0 x_1 x_2 => ecdh_state (x_0,x_1,x_2) in
    ({ code bnd(
        ChoiceEqualityMonad.result_bind_code crypto_error_t , key_t , _ , fset.fset0) gxy_186 ⇠
      (({ code  temp_188 ←
            (ecdh (ks_183) (sk_185) (ct_184)) ;;
          @ret _ (temp_188) } : code (fset.fset0) [interface] _)) in
      ({ code @ret ((result crypto_error_t key_t)) (@inl key_t crypto_error_t (
            gxy_186)) } : code (fset.fset0) [interface
        #val #[ ECDH_STATE ] : ecdh_state_inp → ecdh_state_out ] _) } : code (
        fset.fset0) [interface
      #val #[ ECDH_STATE ] : ecdh_state_inp → ecdh_state_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_kem_decap_state : package _ _ _ :=
  (seq_link kem_decap_state link_rest(package_ecdh_state)).
Fail Next Obligation.

Notation "'kem_decap_inp'" :=(
  kem_scheme_t '× byte_seq '× kem_sk_t : choice_type) (in custom pack_type at level 2).
Notation "'kem_decap_out'" :=((
    result crypto_error_t key_t) : choice_type) (in custom pack_type at level 2).
Definition KEM_DECAP : nat :=
  (190).
Program Definition kem_decap
  (ks_183 : kem_scheme_t)
  (ct_184 : byte_seq)
  (sk_185 : kem_sk_t)
  :both (fset.fset0) [interface #val #[ ECDH ] : ecdh_inp → ecdh_out ] ((
      result crypto_error_t key_t)) :=
  #import {sig #[ ECDH ] : ecdh_inp → ecdh_out } as ecdh ;;
  let ecdh := fun x_0 x_1 x_2 => ecdh (x_0,x_1,x_2) in
  letbnd(ChoiceEqualityMonad.result_bind_both crypto_error_t) gxy_186 : key_t :=
    ecdh (lift_to_both0 ks_183) (lift_to_both0 sk_185) (lift_to_both0 ct_184) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok key_t crypto_error_t (
      lift_to_both0 gxy_186))
  .
Fail Next Obligation.

Definition hash_pure
  (ha_191 : hash_algorithm_t)
  (payload_192 : byte_seq)
  : (result crypto_error_t digest_t) :=
  match ha_191 with
  | SHA256 => @Ok digest_t crypto_error_t (seq_from_seq (array_to_seq (sha256 (
        payload_192))))
  | SHA384 => @Err digest_t crypto_error_t (UnsupportedAlgorithm)
  end.
Definition hash_pure_code
  (ha_191 : hash_algorithm_t)
  (payload_192 : byte_seq)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t digest_t))) :=
  lift_to_code (hash_pure ha_191 payload_192).


Notation "'hash_state_inp'" := (
  hash_algorithm_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'hash_state_out'" := ((
    result crypto_error_t digest_t) : choice_type) (in custom pack_type at level 2).
Definition HASH_STATE : nat :=
  (201).
Program Definition hash_state
   : package (fset.fset0) [interface] [interface
  #val #[ HASH_STATE ] : hash_state_inp → hash_state_out ] :=
  ([package #def #[ HASH_STATE ] (temp_inp : hash_state_inp) : hash_state_out { 
    let '(ha_191 , payload_192) := temp_inp : hash_algorithm_t '× byte_seq in
    ({ code  temp_200 ←
        ((({ code match ha_191 with
              | SHA256 => temp_194 ←
                (sha256 (payload_192)) ;;
               '(temp_196 : seq uint8) ←
                (array_to_seq (temp_194)) ;;
               '(temp_198 : digest_t) ←
                (seq_from_seq (temp_196)) ;;
               ret (@inl digest_t crypto_error_t (temp_198))
              | SHA384 => ret (@inr digest_t crypto_error_t (
                  UnsupportedAlgorithm))
              end } : code _ _ _))) ;;
      @ret ((result crypto_error_t digest_t)) (temp_200) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_hash_state : package _ _ _ :=
  (hash_state).
Fail Next Obligation.

Notation "'hash_inp'" :=(
  hash_algorithm_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'hash_out'" :=((
    result crypto_error_t digest_t) : choice_type) (in custom pack_type at level 2).
Definition HASH : nat :=
  (202).
Program Definition hash
  (ha_191 : hash_algorithm_t)
  (payload_192 : byte_seq)
  :both (fset.fset0) [interface #val #[ SHA256 ] : sha256_inp → sha256_out ] (
    (result crypto_error_t digest_t)) :=
  #import {sig #[ SHA256 ] : sha256_inp → sha256_out } as sha256 ;;
  let sha256 := fun x_0 => sha256 (x_0) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) .
Fail Next Obligation.

Definition hmac_tag_pure
  (ha_203 : hash_algorithm_t)
  (mk_204 : mac_key_t)
  (payload_205 : byte_seq)
  : (result crypto_error_t hmac_t) :=
  match ha_203 with
  | SHA256 => @Ok hmac_t crypto_error_t (seq_from_seq (array_to_seq (hmac (
        mk_204) (payload_205))))
  | SHA384 => @Err hmac_t crypto_error_t (UnsupportedAlgorithm)
  end.
Definition hmac_tag_pure_code
  (ha_203 : hash_algorithm_t)
  (mk_204 : mac_key_t)
  (payload_205 : byte_seq)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t hmac_t))) :=
  lift_to_code (hmac_tag_pure ha_203 mk_204 payload_205).


Notation "'hmac_tag_state_inp'" := (
  hash_algorithm_t '× mac_key_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'hmac_tag_state_out'" := ((
    result crypto_error_t hmac_t) : choice_type) (in custom pack_type at level 2).
Definition HMAC_TAG_STATE : nat :=
  (214).
Program Definition hmac_tag_state
   : package (fset.fset0) [interface] [interface
  #val #[ HMAC_TAG_STATE ] : hmac_tag_state_inp → hmac_tag_state_out ] :=
  (
    [package #def #[ HMAC_TAG_STATE ] (temp_inp : hmac_tag_state_inp) : hmac_tag_state_out { 
    let '(
      ha_203 , mk_204 , payload_205) := temp_inp : hash_algorithm_t '× mac_key_t '× byte_seq in
    ({ code  temp_213 ←
        ((({ code match ha_203 with
              | SHA256 => temp_207 ←
                (hmac (mk_204) (payload_205)) ;;
               '(temp_209 : seq uint8) ←
                (array_to_seq (temp_207)) ;;
               '(temp_211 : hmac_t) ←
                (seq_from_seq (temp_209)) ;;
               ret (@inl hmac_t crypto_error_t (temp_211))
              | SHA384 => ret (@inr hmac_t crypto_error_t (
                  UnsupportedAlgorithm))
              end } : code _ _ _))) ;;
      @ret ((result crypto_error_t hmac_t)) (temp_213) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_hmac_tag_state : package _ _ _ :=
  (hmac_tag_state).
Fail Next Obligation.

Notation "'hmac_tag_inp'" :=(
  hash_algorithm_t '× mac_key_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'hmac_tag_out'" :=((
    result crypto_error_t hmac_t) : choice_type) (in custom pack_type at level 2).
Definition HMAC_TAG : nat :=
  (215).
Program Definition hmac_tag
  (ha_203 : hash_algorithm_t)
  (mk_204 : mac_key_t)
  (payload_205 : byte_seq)
  :both (fset.fset0) [interface #val #[ HMAC ] : hmac_inp → hmac_out ] ((
      result crypto_error_t hmac_t)) :=
  #import {sig #[ HMAC ] : hmac_inp → hmac_out } as hmac ;;
  let hmac := fun x_0 x_1 => hmac (x_0,x_1) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) .
Fail Next Obligation.

Definition check_tag_len_pure
  (a_216 : hmac_t)
  (b_217 : hmac_t)
  : (result crypto_error_t unit) :=
  (if (((seq_len (a_216)) =.? (seq_len (b_217)))):bool_ChoiceEquality then (
      @Ok unit crypto_error_t (tt)) else (@Err unit crypto_error_t (
        MacFailed))).
Definition check_tag_len_pure_code
  (a_216 : hmac_t)
  (b_217 : hmac_t)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t unit))) :=
  lift_to_code (check_tag_len_pure a_216 b_217).


Notation "'check_tag_len_state_inp'" := (
  hmac_t '× hmac_t : choice_type) (in custom pack_type at level 2).
Notation "'check_tag_len_state_out'" := ((
    result crypto_error_t unit_ChoiceEquality) : choice_type) (in custom pack_type at level 2).
Definition CHECK_TAG_LEN_STATE : nat :=
  (224).
Program Definition check_tag_len_state
   : package (fset.fset0) [interface] [interface
  #val #[ CHECK_TAG_LEN_STATE ] : check_tag_len_state_inp → check_tag_len_state_out
  ] :=
  (
    [package #def #[ CHECK_TAG_LEN_STATE ] (temp_inp : check_tag_len_state_inp) : check_tag_len_state_out { 
    let '(a_216 , b_217) := temp_inp : hmac_t '× hmac_t in
    ({ code  '(temp_219 : uint_size) ←
        (seq_len (a_216)) ;;
       '(temp_221 : uint_size) ←
        (seq_len (b_217)) ;;
       '(temp_223 : bool_ChoiceEquality) ←
        ((temp_219) =.? (temp_221)) ;;
      @ret ((result crypto_error_t unit_ChoiceEquality)) ((if (
            temp_223):bool_ChoiceEquality then (*inline*) (
            @inl unit_ChoiceEquality crypto_error_t (tt)) else (
            @inr unit_ChoiceEquality crypto_error_t (MacFailed)))) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_check_tag_len_state : package _ _ _ :=
  (check_tag_len_state).
Fail Next Obligation.

Notation "'check_tag_len_inp'" :=(
  hmac_t '× hmac_t : choice_type) (in custom pack_type at level 2).
Notation "'check_tag_len_out'" :=((
    result crypto_error_t unit_ChoiceEquality) : choice_type) (in custom pack_type at level 2).
Definition CHECK_TAG_LEN : nat :=
  (225).
Program Definition check_tag_len
  (a_216 : hmac_t)
  (b_217 : hmac_t)
  :both (fset.fset0) [interface] ((
      result crypto_error_t unit_ChoiceEquality)) :=
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
    if is_pure (I := [interface]) ((seq_len (lift_to_both0 a_216)) =.? (
        seq_len (lift_to_both0 b_217)))
    then @Ok unit_ChoiceEquality crypto_error_t (tt)
    else @Err unit_ChoiceEquality crypto_error_t (MacFailed))
  .
Fail Next Obligation.

Definition check_bytes_pure
  (a_226 : uint8)
  (b_227 : uint8)
  : (result crypto_error_t unit) :=
  (if (negb (uint8_equal (a_226) (b_227))):bool_ChoiceEquality then (
      @Err unit crypto_error_t (MacFailed)) else (@Ok unit crypto_error_t (
        tt))).
Definition check_bytes_pure_code
  (a_226 : uint8)
  (b_227 : uint8)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t unit))) :=
  lift_to_code (check_bytes_pure a_226 b_227).


Notation "'check_bytes_state_inp'" := (
  uint8 '× uint8 : choice_type) (in custom pack_type at level 2).
Notation "'check_bytes_state_out'" := ((
    result crypto_error_t unit_ChoiceEquality) : choice_type) (in custom pack_type at level 2).
Definition CHECK_BYTES_STATE : nat :=
  (230).
Program Definition check_bytes_state
   : package (fset.fset0) [interface] [interface
  #val #[ CHECK_BYTES_STATE ] : check_bytes_state_inp → check_bytes_state_out
  ] :=
  (
    [package #def #[ CHECK_BYTES_STATE ] (temp_inp : check_bytes_state_inp) : check_bytes_state_out { 
    let '(a_226 , b_227) := temp_inp : uint8 '× uint8 in
    ({ code  temp_229 ←
        (uint8_equal (a_226) (b_227)) ;;
      @ret ((result crypto_error_t unit_ChoiceEquality)) ((if (negb (
              temp_229)):bool_ChoiceEquality then (*inline*) (
            @inr unit_ChoiceEquality crypto_error_t (MacFailed)) else (
            @inl unit_ChoiceEquality crypto_error_t (tt)))) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_check_bytes_state : package _ _ _ :=
  (check_bytes_state).
Fail Next Obligation.

Notation "'check_bytes_inp'" :=(
  uint8 '× uint8 : choice_type) (in custom pack_type at level 2).
Notation "'check_bytes_out'" :=((
    result crypto_error_t unit_ChoiceEquality) : choice_type) (in custom pack_type at level 2).
Definition CHECK_BYTES : nat :=
  (231).
Program Definition check_bytes
  (a_226 : uint8)
  (b_227 : uint8)
  :both (fset.fset0) [interface] ((
      result crypto_error_t unit_ChoiceEquality)) :=
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
    if is_pure (I := [interface]) (negb (uint8_equal (lift_to_both0 a_226) (
          lift_to_both0 b_227)))
    then @Err unit_ChoiceEquality crypto_error_t (MacFailed)
    else @Ok unit_ChoiceEquality crypto_error_t (tt))
  .
Fail Next Obligation.

Definition hmac_verify_pure
  (ha_232 : hash_algorithm_t)
  (mk_233 : mac_key_t)
  (payload_234 : byte_seq)
  (m_235 : hmac_t)
  : (result crypto_error_t unit) :=
   my_hmac_236 m( _ ) ⇠ (hmac_tag (ha_232) (mk_233) (payload_234)) ;;
  ( _ m( _ ) ⇠ (check_tag_len (m_235) (my_hmac_236)) ;;
    (_ m( _ ) ⇠ (foldibnd (usize 0) to (seq_len (
            m_235)) M( _ ) for prod_cett >> (fun i_237 'tt =>
         _ m( _ ) ⇠ (check_bytes (seq_index (my_hmac_236) (i_237)) (
            seq_index (m_235) (i_237))) ;;
        (Ok ((tt : unit_ChoiceEquality))))) ;;
      (@Ok unit crypto_error_t (tt)))).
Definition hmac_verify_pure_code
  (ha_232 : hash_algorithm_t)
  (mk_233 : mac_key_t)
  (payload_234 : byte_seq)
  (m_235 : hmac_t)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t unit))) :=
  lift_to_code (hmac_verify_pure ha_232 mk_233 payload_234 m_235).


Notation "'hmac_verify_state_inp'" := (
  hash_algorithm_t '× mac_key_t '× byte_seq '× hmac_t : choice_type) (in custom pack_type at level 2).
Notation "'hmac_verify_state_out'" := ((
    result crypto_error_t unit_ChoiceEquality) : choice_type) (in custom pack_type at level 2).
Definition HMAC_VERIFY_STATE : nat :=
  (250).
Program Definition hmac_verify_state
   : package (fset.fset0) [interface
  #val #[ CHECK_BYTES_STATE ] : check_bytes_state_inp → check_bytes_state_out ;
  #val #[ CHECK_TAG_LEN_STATE ] : check_tag_len_state_inp → check_tag_len_state_out ;
  #val #[ HMAC_TAG_STATE ] : hmac_tag_state_inp → hmac_tag_state_out
  ] [interface
  #val #[ HMAC_VERIFY_STATE ] : hmac_verify_state_inp → hmac_verify_state_out
  ] :=
  (
    [package #def #[ HMAC_VERIFY_STATE ] (temp_inp : hmac_verify_state_inp) : hmac_verify_state_out { 
    let '(
      ha_232 , mk_233 , payload_234 , m_235) := temp_inp : hash_algorithm_t '× mac_key_t '× byte_seq '× hmac_t in
    #import {sig #[ CHECK_BYTES_STATE ] : check_bytes_state_inp → check_bytes_state_out } as check_bytes_state ;;
    let check_bytes_state := fun x_0 x_1 => check_bytes_state (x_0,x_1) in
    #import {sig #[ CHECK_TAG_LEN_STATE ] : check_tag_len_state_inp → check_tag_len_state_out } as check_tag_len_state ;;
    let check_tag_len_state := fun x_0 x_1 => check_tag_len_state (x_0,x_1) in
    #import {sig #[ HMAC_TAG_STATE ] : hmac_tag_state_inp → hmac_tag_state_out } as hmac_tag_state ;;
    let hmac_tag_state := fun x_0 x_1 x_2 => hmac_tag_state (x_0,x_1,x_2) in
    ({ code bnd(
        ChoiceEqualityMonad.result_bind_code crypto_error_t , hmac_t , _ , fset.fset0) my_hmac_236 ⇠
      (({ code  temp_239 ←
            (hmac_tag (ha_232) (mk_233) (payload_234)) ;;
          @ret _ (temp_239) } : code (fset.fset0) [interface] _)) in
      ({ code bnd(
          ChoiceEqualityMonad.result_bind_code crypto_error_t , unit_ChoiceEquality , _ , fset.fset0) _ ⇠
        (({ code  temp_241 ←
              (check_tag_len (m_235) (my_hmac_236)) ;;
            @ret _ (temp_241) } : code (fset.fset0) [interface] _)) in
        ({ code  '(temp_243 : uint_size) ←
            (seq_len (m_235)) ;;
          bnd(
            ChoiceEqualityMonad.result_bind_code crypto_error_t , unit_ChoiceEquality , _ , fset.fset0) 'tt ⇠
          (foldi_bind_code' (usize 0) (temp_243) (prod_cett) (fun i_237 'tt =>
            ({ code bnd(
                ChoiceEqualityMonad.result_bind_code crypto_error_t , unit_ChoiceEquality , _ , fset.fset0) _ ⇠
              (({ code  '(temp_245 : uint8) ←
                    (seq_index (my_hmac_236) (i_237)) ;;
                   temp_247 ←
                    (seq_index (m_235) (i_237)) ;;
                   temp_249 ←
                    (check_bytes (temp_245) (temp_247)) ;;
                  @ret _ (temp_249) } : code (fset.fset0) [interface] _)) in
              ({ code @ret ((result crypto_error_t unit_ChoiceEquality)) (
                  @inl unit_ChoiceEquality crypto_error_t (
                    (tt : unit_ChoiceEquality))) } : code (
                  fset.fset0) [interface] _) } : code (
                fset.fset0) [interface] _))) in
          ({ code @ret ((result crypto_error_t unit_ChoiceEquality)) (
              @inl unit_ChoiceEquality crypto_error_t (tt)) } : code (
              fset.fset0) [interface] _) } : code (fset.fset0) [interface
          #val #[ CHECK_BYTES_STATE ] : check_bytes_state_inp → check_bytes_state_out ;
          #val #[ CHECK_TAG_LEN_STATE ] : check_tag_len_state_inp → check_tag_len_state_out ;
          #val #[ HMAC_TAG_STATE ] : hmac_tag_state_inp → hmac_tag_state_out
          ] _) } : code (fset.fset0) [interface
        #val #[ CHECK_BYTES_STATE ] : check_bytes_state_inp → check_bytes_state_out ;
        #val #[ CHECK_TAG_LEN_STATE ] : check_tag_len_state_inp → check_tag_len_state_out ;
        #val #[ HMAC_TAG_STATE ] : hmac_tag_state_inp → hmac_tag_state_out
        ] _) } : code (fset.fset0) [interface
      #val #[ CHECK_BYTES_STATE ] : check_bytes_state_inp → check_bytes_state_out ;
      #val #[ CHECK_TAG_LEN_STATE ] : check_tag_len_state_inp → check_tag_len_state_out ;
      #val #[ HMAC_TAG_STATE ] : hmac_tag_state_inp → hmac_tag_state_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_hmac_verify_state : package _ _ _ :=
  (seq_link hmac_verify_state link_rest(
      package_check_bytes_state,package_check_tag_len_state,package_hmac_tag_state)).
Fail Next Obligation.

Notation "'hmac_verify_inp'" :=(
  hash_algorithm_t '× mac_key_t '× byte_seq '× hmac_t : choice_type) (in custom pack_type at level 2).
Notation "'hmac_verify_out'" :=((
    result crypto_error_t unit_ChoiceEquality) : choice_type) (in custom pack_type at level 2).
Definition HMAC_VERIFY : nat :=
  (251).
Program Definition hmac_verify
  (ha_232 : hash_algorithm_t)
  (mk_233 : mac_key_t)
  (payload_234 : byte_seq)
  (m_235 : hmac_t)
  :both (fset.fset0) [interface
  #val #[ CHECK_BYTES ] : check_bytes_inp → check_bytes_out ;
  #val #[ CHECK_TAG_LEN ] : check_tag_len_inp → check_tag_len_out ;
  #val #[ HMAC_TAG ] : hmac_tag_inp → hmac_tag_out ] ((
      result crypto_error_t unit_ChoiceEquality)) :=
  #import {sig #[ CHECK_BYTES ] : check_bytes_inp → check_bytes_out } as check_bytes ;;
  let check_bytes := fun x_0 x_1 => check_bytes (x_0,x_1) in
  #import {sig #[ CHECK_TAG_LEN ] : check_tag_len_inp → check_tag_len_out } as check_tag_len ;;
  let check_tag_len := fun x_0 x_1 => check_tag_len (x_0,x_1) in
  #import {sig #[ HMAC_TAG ] : hmac_tag_inp → hmac_tag_out } as hmac_tag ;;
  let hmac_tag := fun x_0 x_1 x_2 => hmac_tag (x_0,x_1,x_2) in
  letbnd(
      ChoiceEqualityMonad.result_bind_both crypto_error_t) my_hmac_236 : hmac_t :=
    hmac_tag (lift_to_both0 ha_232) (lift_to_both0 mk_233) (
      lift_to_both0 payload_234) in
  letbnd(
      ChoiceEqualityMonad.result_bind_both crypto_error_t) _ : unit_ChoiceEquality :=
    check_tag_len (lift_to_both0 m_235) (lift_to_both0 my_hmac_236) in
  letbnd(_) 'tt :=
    foldi_bind_both' (lift_to_both0 (usize 0)) (seq_len (
          lift_to_both0 m_235)) prod_cett (L := (fset.fset0)) (I := ([interface
        #val #[ CHECK_BYTES ] : check_bytes_inp → check_bytes_out ;
        #val #[ CHECK_TAG_LEN ] : check_tag_len_inp → check_tag_len_out ;
        #val #[ HMAC_TAG ] : hmac_tag_inp → hmac_tag_out ])) (fun i_237 'tt =>
      letbnd(
          ChoiceEqualityMonad.result_bind_both crypto_error_t) _ : unit_ChoiceEquality :=
        check_bytes (seq_index (my_hmac_236) (lift_to_both0 i_237)) (seq_index (
            m_235) (lift_to_both0 i_237)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        @Ok unit_ChoiceEquality crypto_error_t (lift_to_both0 (
            (tt : unit_ChoiceEquality))))
      ) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
    @Ok unit_ChoiceEquality crypto_error_t (tt))
  .
Fail Next Obligation.

Definition ec_oid_tag_t := nseq (uint8) (usize 9).

Definition get_length_length_pure (b_252 : byte_seq) : uint_size :=
  (if (((((uint8_declassify (seq_index (b_252) (usize 0))) shift_right (
              usize 7))) =.? (@repr U8 1))):bool_ChoiceEquality then (
      declassify_usize_from_uint8 (((seq_index (b_252) (usize 0)) .& (secret (
              @repr U8 127))))) else (usize 0)).
Definition get_length_length_pure_code
  (b_252 : byte_seq)
  : code fset.fset0 [interface] (@ct (uint_size)) :=
  lift_to_code (get_length_length_pure b_252).


Notation "'get_length_length_state_inp'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'get_length_length_state_out'" := (
  uint_size : choice_type) (in custom pack_type at level 2).
Definition GET_LENGTH_LENGTH_STATE : nat :=
  (269).
Program Definition get_length_length_state
   : package (fset.fset0) [interface] [interface
  #val #[ GET_LENGTH_LENGTH_STATE ] : get_length_length_state_inp → get_length_length_state_out
  ] :=
  (
    [package #def #[ GET_LENGTH_LENGTH_STATE ] (temp_inp : get_length_length_state_inp) : get_length_length_state_out { 
    let '(b_252) := temp_inp : byte_seq in
    ({ code  temp_254 ←
        (seq_index (b_252) (usize 0)) ;;
       temp_256 ←
        (uint8_declassify (temp_254)) ;;
       temp_258 ←
        ((temp_256) shift_right (usize 7)) ;;
       '(temp_260 : bool_ChoiceEquality) ←
        ((temp_258) =.? (@repr U8 1)) ;;
       temp_262 ←
        (seq_index (b_252) (usize 0)) ;;
       '(temp_264 : int8) ←
        (secret (@repr U8 127)) ;;
       temp_266 ←
        ((temp_262) .& (temp_264)) ;;
       temp_268 ←
        (declassify_usize_from_uint8 (temp_266)) ;;
      @ret (uint_size) ((if (temp_260):bool_ChoiceEquality then (*inline*) (
            temp_268) else (usize 0))) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_get_length_length_state : package _ _ _ :=
  (get_length_length_state).
Fail Next Obligation.

Notation "'get_length_length_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'get_length_length_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Definition GET_LENGTH_LENGTH : nat :=
  (270).
Program Definition get_length_length
  (b_252 : byte_seq)
  :both (fset.fset0) [interface] (uint_size) :=
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
    if is_pure (I := [interface]) (((uint8_declassify (seq_index (b_252) (
              lift_to_both0 (usize 0)))) shift_right (lift_to_both0 (
            usize 7))) =.? (lift_to_both0 (@repr U8 1)))
    then declassify_usize_from_uint8 ((seq_index (b_252) (lift_to_both0 (
            usize 0))) .& (secret (lift_to_both0 (@repr U8 127))))
    else lift_to_both0 (usize 0))
  .
Fail Next Obligation.

Definition get_length_pure
  (b_271 : byte_seq)
  (len_272 : uint_size)
  : uint_size :=
  ((@cast _ uint32 _ (declassify_u32_from_uint32 (uint32_from_be_bytes (
            array_from_slice (default : uint8) (4) (b_271) (usize 0) (
              len_272))))) usize_shift_right (((((usize 4) .- (len_272))) .* (
          usize 8)))).
Definition get_length_pure_code
  (b_271 : byte_seq)
  (len_272 : uint_size)
  : code fset.fset0 [interface] (@ct (uint_size)) :=
  lift_to_code (get_length_pure b_271 len_272).


Notation "'get_length_state_inp'" := (
  byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'get_length_state_out'" := (
  uint_size : choice_type) (in custom pack_type at level 2).
Definition GET_LENGTH_STATE : nat :=
  (285).
Program Definition get_length_state
   : package (fset.fset0) [interface] [interface
  #val #[ GET_LENGTH_STATE ] : get_length_state_inp → get_length_state_out
  ] :=
  (
    [package #def #[ GET_LENGTH_STATE ] (temp_inp : get_length_state_inp) : get_length_state_out { 
    let '(b_271 , len_272) := temp_inp : byte_seq '× uint_size in
    ({ code  '(temp_274 : uint32_word_t) ←
        (array_from_slice (default : uint8) (4) (b_271) (usize 0) (len_272)) ;;
       '(temp_276 : int32) ←
        (uint32_from_be_bytes (temp_274)) ;;
       temp_278 ←
        (declassify_u32_from_uint32 (temp_276)) ;;
       '(temp_280 : uint_size) ←
        ((usize 4) .- (len_272)) ;;
       '(temp_282 : uint_size) ←
        ((temp_280) .* (usize 8)) ;;
       temp_284 ←
        ((@cast _ uint32 _ (temp_278)) usize_shift_right (temp_282)) ;;
      @ret (uint_size) (temp_284) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_get_length_state : package _ _ _ :=
  (get_length_state).
Fail Next Obligation.

Notation "'get_length_inp'" :=(
  byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'get_length_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Definition GET_LENGTH : nat :=
  (286).
Program Definition get_length
  (b_271 : byte_seq)
  (len_272 : uint_size)
  :both (fset.fset0) [interface
  #val #[ DECLASSIFY_U32_FROM_U32 ] : declassify_u32_from_uint32_inp → declassify_u32_from_uint32_out
  ] (uint_size) :=
  #import {sig #[ DECLASSIFY_U32_FROM_U32 ] : declassify_u32_from_uint32_inp → declassify_u32_from_uint32_out } as declassify_u32_from_uint32 ;;
  let declassify_u32_from_uint32 := fun x_0 => declassify_u32_from_uint32 (
    x_0) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((@cast _ uint32 _ (
        declassify_u32_from_uint32 (uint32_from_be_bytes (array_from_slice (
              default : uint8) (4) (lift_to_both0 b_271) (lift_to_both0 (
                usize 0)) (lift_to_both0 len_272))))) usize_shift_right (((
          lift_to_both0 (usize 4)) .- (lift_to_both0 len_272)) .* (
        lift_to_both0 (usize 8))))
  .
Fail Next Obligation.

Definition get_short_length_pure (b_287 : byte_seq) : uint_size :=
  declassify_usize_from_uint8 (((seq_index (b_287) (usize 0)) .& (secret (
          @repr U8 127)))).
Definition get_short_length_pure_code
  (b_287 : byte_seq)
  : code fset.fset0 [interface] (@ct (uint_size)) :=
  lift_to_code (get_short_length_pure b_287).


Notation "'get_short_length_state_inp'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'get_short_length_state_out'" := (
  uint_size : choice_type) (in custom pack_type at level 2).
Definition GET_SHORT_LENGTH_STATE : nat :=
  (296).
Program Definition get_short_length_state
   : package (fset.fset0) [interface] [interface
  #val #[ GET_SHORT_LENGTH_STATE ] : get_short_length_state_inp → get_short_length_state_out
  ] :=
  (
    [package #def #[ GET_SHORT_LENGTH_STATE ] (temp_inp : get_short_length_state_inp) : get_short_length_state_out { 
    let '(b_287) := temp_inp : byte_seq in
    ({ code  temp_289 ←
        (seq_index (b_287) (usize 0)) ;;
       '(temp_291 : int8) ←
        (secret (@repr U8 127)) ;;
       temp_293 ←
        ((temp_289) .& (temp_291)) ;;
       temp_295 ←
        (declassify_usize_from_uint8 (temp_293)) ;;
      @ret (uint_size) (temp_295) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_get_short_length_state : package _ _ _ :=
  (get_short_length_state).
Fail Next Obligation.

Notation "'get_short_length_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'get_short_length_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Definition GET_SHORT_LENGTH : nat :=
  (297).
Program Definition get_short_length
  (b_287 : byte_seq)
  :both (fset.fset0) [interface] (uint_size) :=
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
    declassify_usize_from_uint8 ((seq_index (b_287) (lift_to_both0 (
            usize 0))) .& (secret (lift_to_both0 (@repr U8 127)))))
  .
Fail Next Obligation.

Definition verification_key_from_cert_pure
  (cert_306 : byte_seq)
  : (result crypto_error_t verification_key_t) :=
  let skip_307 : uint_size :=
    ((((usize 2) .+ (get_length_length (seq_slice_range (cert_306) (prod_ce(
                  usize 1,
                  seq_len (cert_306)
                )))))) .+ (usize 1)) in 
  let seq1_len_len_308 : uint_size :=
    get_length_length (seq_slice_range (cert_306) (prod_ce(
          skip_307,
          seq_len (cert_306)
        ))) in 
  let skip_309 : uint_size :=
    ((skip_307) .+ (usize 1)) in 
  let seq1_len_310 : uint_size :=
    get_length (seq_slice (cert_306) (skip_309) (((seq_len (cert_306)) .- (
            skip_309)))) (seq1_len_len_308) in 
  let seq1_298 : seq uint8 :=
    seq_slice_range (cert_306) (prod_ce(
        ((skip_309) .+ (seq1_len_len_308)),
        ((((skip_309) .+ (seq1_len_len_308))) .+ (seq1_len_310))
      )) in 
  let pk_299 : seq uint8 :=
    seq_new_ (default : uint8) (usize 0) in 
  let '(seq1_298, pk_299) :=
    Hacspec_Lib_Pre.foldi (usize 0) (seq_len (seq1_298)) (seq1_298, pk_299)
      (fun i_311 '(seq1_298, pk_299) =>
      let '(seq1_298, pk_299) :=
        ((if (((seq_len (seq1_298)) >.? (usize 0))):bool_ChoiceEquality
            then (let element_type_312 : int8 :=
                uint8_declassify (seq_index (seq1_298) (usize 0)) in 
              let seq1_298 :=
                seq_slice (seq1_298) (usize 1) (((seq_len (seq1_298)) .- (
                      usize 1))) in 
              let len_len_313 : uint_size :=
                get_length_length (seq1_298) in 
              let len_300 : uint_size :=
                get_short_length (seq1_298) in 
              let seq1_298 :=
                seq_slice (seq1_298) (usize 1) (((seq_len (seq1_298)) .- (
                      usize 1))) in 
              let '(len_300) :=
                ((if (((len_len_313) !=.? (usize 0))):bool_ChoiceEquality
                    then (let len_300 :=
                        ((get_length (seq1_298) (len_len_313)) .+ (
                            len_len_313)) in 
                      (len_300))
                    else ((len_300))) : T _) in 
              let '(pk_299) :=
                ((if (((((element_type_312) =.? (@repr U8 48))) && (((seq_len (
                                pk_299)) =.? (usize 0))))):bool_ChoiceEquality
                    then (let seq2_314 : seq uint8 :=
                        seq_slice (seq1_298) (len_len_313) (len_300) in 
                      let element_type_315 : int8 :=
                        uint8_declassify (seq_index (seq2_314) (usize 0)) in 
                      let seq2_316 : seq uint8 :=
                        seq_slice (seq2_314) (usize 1) (((seq_len (
                                seq2_314)) .- (usize 1))) in 
                      let '(pk_299) :=
                        ((if (((element_type_315) =.? (
                                  @repr U8 48))):bool_ChoiceEquality
                            then (let len_len_317 : uint_size :=
                                get_length_length (seq2_316) in 
                              let '(pk_299) :=
                                ((if (((len_len_317) =.? (
                                          usize 0))):bool_ChoiceEquality
                                    then (let oid_len_318 : uint_size :=
                                        get_short_length (seq2_316) in 
                                      let '(pk_299) :=
                                        ((if (((oid_len_318) >=.? (
                                                  usize 9))):bool_ChoiceEquality
                                            then (
                                              let expected_319 : seq uint8 :=
                                                seq_from_seq (
                                                  array_to_seq (array_from_list uint8 [
                                                    (secret (
                                                        @repr U8 6)) : uint8;
                                                    (secret (
                                                        @repr U8 7)) : uint8;
                                                    (secret (
                                                        @repr U8 42)) : uint8;
                                                    (secret (
                                                        @repr U8 134)) : uint8;
                                                    (secret (
                                                        @repr U8 72)) : uint8;
                                                    (secret (
                                                        @repr U8 206)) : uint8;
                                                    (secret (
                                                        @repr U8 61)) : uint8;
                                                    (secret (
                                                        @repr U8 2)) : uint8;
                                                    (secret (
                                                        @repr U8 1)) : uint8
                                                  ])) in 
                                              let oid_320 : seq uint8 :=
                                                seq_slice (seq2_316) (usize 1) (
                                                  usize 9) in 
                                              let ec_pk_oid_301 : bool_ChoiceEquality :=
                                                (true : bool_ChoiceEquality) in 
                                              let ec_pk_oid_301 :=
                                                Hacspec_Lib_Pre.foldi (
                                                    usize 0) (
                                                    usize 9) ec_pk_oid_301
                                                  (fun i_321 ec_pk_oid_301 =>
                                                  let oid_byte_equal_322 : bool_ChoiceEquality :=
                                                    ((uint8_declassify (
                                                          seq_index (oid_320) (
                                                            i_321))) =.? (
                                                        uint8_declassify (
                                                          seq_index (
                                                            expected_319) (
                                                            i_321)))) in 
                                                  let ec_pk_oid_301 :=
                                                    ((ec_pk_oid_301) && (
                                                        oid_byte_equal_322)) in 
                                                  (ec_pk_oid_301)) in 
                                              let '(pk_299) :=
                                                ((if (
                                                      ec_pk_oid_301):bool_ChoiceEquality
                                                    then (
                                                      let bit_string_323 : seq uint8 :=
                                                        seq_slice (seq2_316) (((
                                                              oid_len_318) .+ (
                                                              usize 1))) (((((
                                                                  seq_len (
                                                                    seq2_316)) .- (
                                                                  oid_len_318))) .- (
                                                              usize 1))) in 
                                                      let '(pk_299) :=
                                                        ((if (((
                                                                  uint8_declassify (
                                                                    seq_index (
                                                                      bit_string_323) (
                                                                      usize 0))) =.? (
                                                                  @repr U8 3))):bool_ChoiceEquality
                                                            then (
                                                              let pk_len_324 : uint_size :=
                                                                declassify_usize_from_uint8 (
                                                                  seq_index (
                                                                    bit_string_323) (
                                                                    usize 1)) in 
                                                              let zeroes_325 : uint_size :=
                                                                declassify_usize_from_uint8 (
                                                                  seq_index (
                                                                    bit_string_323) (
                                                                    usize 2)) in 
                                                              let uncompressed_326 : uint_size :=
                                                                declassify_usize_from_uint8 (
                                                                  seq_index (
                                                                    bit_string_323) (
                                                                    usize 3)) in 
                                                              let pk_299 :=
                                                                seq_slice (
                                                                  bit_string_323) (
                                                                  usize 4) (((
                                                                      pk_len_324) .- (
                                                                      usize 2))) in 
                                                              (pk_299))
                                                            else ((pk_299
                                                              ))) : T _) in 
                                                      (pk_299))
                                                    else ((pk_299))) : T _) in 
                                              (pk_299))
                                            else ((pk_299))) : T _) in 
                                      (pk_299))
                                    else ((pk_299))) : T _) in 
                              (pk_299))
                            else ((pk_299))) : T _) in 
                      (pk_299))
                    else ((pk_299))) : T _) in 
              let seq1_298 :=
                seq_slice (seq1_298) (len_300) (((seq_len (seq1_298)) .- (
                      len_300))) in 
              prod_ce(seq1_298, pk_299))
            else (prod_ce(seq1_298, pk_299))) : T _) in 
      prod_ce(seq1_298, pk_299)) in 
  (if (((seq_len (pk_299)) =.? (usize 0))):bool_ChoiceEquality then (
      @Err verification_key_t crypto_error_t (InvalidCert)) else (
      @Ok verification_key_t crypto_error_t (pk_299))).
Definition verification_key_from_cert_pure_code
  (cert_306 : byte_seq)
  : code fset.fset0 [interface] (@ct ((
      result crypto_error_t verification_key_t))) :=
  lift_to_code (verification_key_from_cert_pure cert_306).

Definition ec_pk_oid_301_loc : ChoiceEqualityLocation :=
  ((bool_ChoiceEquality ; 509%nat)).
Definition pk_299_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 510%nat)).
Definition len_300_loc : ChoiceEqualityLocation :=
  ((uint_size ; 511%nat)).
Definition seq1_298_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 512%nat)).
Notation "'verification_key_from_cert_state_inp'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'verification_key_from_cert_state_out'" := ((
    result crypto_error_t verification_key_t) : choice_type) (in custom pack_type at level 2).
Definition VERIFICATION_KEY_FROM_CERT_STATE : nat :=
  (513).
Program Definition verification_key_from_cert_state
   : package (CEfset (
      [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) [interface
  #val #[ GET_LENGTH_LENGTH_STATE ] : get_length_length_state_inp → get_length_length_state_out ;
  #val #[ GET_LENGTH_STATE ] : get_length_state_inp → get_length_state_out ;
  #val #[ GET_SHORT_LENGTH_STATE ] : get_short_length_state_inp → get_short_length_state_out
  ] [interface
  #val #[ VERIFICATION_KEY_FROM_CERT_STATE ] : verification_key_from_cert_state_inp → verification_key_from_cert_state_out
  ] :=
  (
    [package #def #[ VERIFICATION_KEY_FROM_CERT_STATE ] (temp_inp : verification_key_from_cert_state_inp) : verification_key_from_cert_state_out { 
    let '(cert_306) := temp_inp : byte_seq in
    #import {sig #[ GET_LENGTH_LENGTH_STATE ] : get_length_length_state_inp → get_length_length_state_out } as get_length_length_state ;;
    let get_length_length_state := fun x_0 => get_length_length_state (x_0) in
    #import {sig #[ GET_LENGTH_STATE ] : get_length_state_inp → get_length_state_out } as get_length_state ;;
    let get_length_state := fun x_0 x_1 => get_length_state (x_0,x_1) in
    #import {sig #[ GET_SHORT_LENGTH_STATE ] : get_short_length_state_inp → get_short_length_state_out } as get_short_length_state ;;
    let get_short_length_state := fun x_0 => get_short_length_state (x_0) in
    ({ code  '(skip_307 : uint_size) ←
        ( '(temp_328 : uint_size) ←
            (seq_len (cert_306)) ;;
           '(temp_330 : byte_seq) ←
            (seq_slice_range (cert_306) (prod_ce(usize 1, temp_328))) ;;
           temp_332 ←
            (get_length_length (temp_330)) ;;
           '(temp_334 : uint_size) ←
            ((usize 2) .+ (temp_332)) ;;
           '(temp_336 : uint_size) ←
            ((temp_334) .+ (usize 1)) ;;
          ret (temp_336)) ;;
       '(seq1_len_len_308 : uint_size) ←
        ( '(temp_338 : uint_size) ←
            (seq_len (cert_306)) ;;
           '(temp_340 : byte_seq) ←
            (seq_slice_range (cert_306) (prod_ce(skip_307, temp_338))) ;;
           temp_342 ←
            (get_length_length (temp_340)) ;;
          ret (temp_342)) ;;
       '(skip_309 : uint_size) ←
        ( '(temp_344 : uint_size) ←
            ((skip_307) .+ (usize 1)) ;;
          ret (temp_344)) ;;
       '(seq1_len_310 : uint_size) ←
        ( '(temp_346 : uint_size) ←
            (seq_len (cert_306)) ;;
           '(temp_348 : uint_size) ←
            ((temp_346) .- (skip_309)) ;;
           '(temp_350 : byte_seq) ←
            (seq_slice (cert_306) (skip_309) (temp_348)) ;;
           temp_352 ←
            (get_length (temp_350) (seq1_len_len_308)) ;;
          ret (temp_352)) ;;
       '(seq1_298 : seq uint8) ←
          ( '(temp_354 : uint_size) ←
              ((skip_309) .+ (seq1_len_len_308)) ;;
             '(temp_356 : uint_size) ←
              ((skip_309) .+ (seq1_len_len_308)) ;;
             '(temp_358 : uint_size) ←
              ((temp_356) .+ (seq1_len_310)) ;;
             '(temp_360 : byte_seq) ←
              (seq_slice_range (cert_306) (prod_ce(temp_354, temp_358))) ;;
            ret (temp_360)) ;;
        #put seq1_298_loc := seq1_298 ;;
       '(pk_299 : seq uint8) ←
          ( temp_362 ←
              (seq_new_ (default : uint8) (usize 0)) ;;
            ret (temp_362)) ;;
        #put pk_299_loc := pk_299 ;;
       '(temp_364 : uint_size) ←
        (seq_len (seq1_298)) ;;
       temp_508 ←
        (foldi' (usize 0) (temp_364) prod_ce(seq1_298, pk_299) (L2 := CEfset (
                [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) (
              I2 := [interface
              #val #[ GET_LENGTH_LENGTH_STATE ] : get_length_length_state_inp → get_length_length_state_out ;
              #val #[ GET_LENGTH_STATE ] : get_length_state_inp → get_length_state_out ;
              #val #[ GET_SHORT_LENGTH_STATE ] : get_short_length_state_inp → get_short_length_state_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_311 '(
              seq1_298,
              pk_299
            ) =>
            ({ code  '(temp_366 : uint_size) ←
                (seq_len (seq1_298)) ;;
               '(temp_368 : bool_ChoiceEquality) ←
                ((temp_366) >.? (usize 0)) ;;
               temp_502 ←
                (if temp_368:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(
                        element_type_312 : int8) ←
                      ( '(temp_370 : uint8) ←
                          (seq_index (seq1_298) (usize 0)) ;;
                         temp_372 ←
                          (uint8_declassify (temp_370)) ;;
                        ret (temp_372)) ;;
                     '(seq1_298 : seq uint8) ←
                        (( '(temp_374 : uint_size) ←
                              (seq_len (seq1_298)) ;;
                             '(temp_376 : uint_size) ←
                              ((temp_374) .- (usize 1)) ;;
                             '(temp_378 : seq uint8) ←
                              (seq_slice (seq1_298) (usize 1) (temp_376)) ;;
                            ret (temp_378))) ;;
                      #put seq1_298_loc := seq1_298 ;;
                    
                     '(len_len_313 : uint_size) ←
                      ( temp_380 ←
                          (get_length_length (seq1_298)) ;;
                        ret (temp_380)) ;;
                     '(len_300 : uint_size) ←
                        ( temp_382 ←
                            (get_short_length (seq1_298)) ;;
                          ret (temp_382)) ;;
                      #put len_300_loc := len_300 ;;
                     '(seq1_298 : seq uint8) ←
                        (( '(temp_384 : uint_size) ←
                              (seq_len (seq1_298)) ;;
                             '(temp_386 : uint_size) ←
                              ((temp_384) .- (usize 1)) ;;
                             '(temp_388 : seq uint8) ←
                              (seq_slice (seq1_298) (usize 1) (temp_386)) ;;
                            ret (temp_388))) ;;
                      #put seq1_298_loc := seq1_298 ;;
                    
                     '(temp_390 : bool_ChoiceEquality) ←
                      ((len_len_313) !=.? (usize 0)) ;;
                     '(len_300 : (uint_size)) ←
                      (if temp_390:bool_ChoiceEquality
                        then (*not state*) (let temp_then :=  '(
                                len_300 : uint_size) ←
                              (( temp_392 ←
                                    (get_length (seq1_298) (len_len_313)) ;;
                                   '(temp_394 : uint_size) ←
                                    ((temp_392) .+ (len_len_313)) ;;
                                  ret (temp_394))) ;;
                            #put len_300_loc := len_300 ;;
                          
                          @ret ((uint_size)) (len_300) in
                          ({ code temp_then } : code (CEfset (
                                [seq1_298_loc ; pk_299_loc ; len_300_loc])) [interface] _))
                        else @ret ((uint_size)) (len_300)) ;;
                    
                     '(temp_396 : bool_ChoiceEquality) ←
                      ((element_type_312) =.? (@repr U8 48)) ;;
                     '(temp_398 : uint_size) ←
                      (seq_len (pk_299)) ;;
                     '(temp_400 : bool_ChoiceEquality) ←
                      ((temp_398) =.? (usize 0)) ;;
                     '(temp_402 : bool_ChoiceEquality) ←
                      ((temp_396) && (temp_400)) ;;
                     '(pk_299 : (seq uint8)) ←
                      (if temp_402:bool_ChoiceEquality
                        then (*not state*) (let temp_then :=  '(
                              seq2_314 : seq uint8) ←
                            ( '(temp_404 : seq uint8) ←
                                (seq_slice (seq1_298) (len_len_313) (
                                    len_300)) ;;
                              ret (temp_404)) ;;
                           '(element_type_315 : int8) ←
                            ( '(temp_406 : uint8) ←
                                (seq_index (seq2_314) (usize 0)) ;;
                               temp_408 ←
                                (uint8_declassify (temp_406)) ;;
                              ret (temp_408)) ;;
                           '(seq2_316 : seq uint8) ←
                            ( '(temp_410 : uint_size) ←
                                (seq_len (seq2_314)) ;;
                               '(temp_412 : uint_size) ←
                                ((temp_410) .- (usize 1)) ;;
                               '(temp_414 : seq uint8) ←
                                (seq_slice (seq2_314) (usize 1) (temp_412)) ;;
                              ret (temp_414)) ;;
                           '(temp_416 : bool_ChoiceEquality) ←
                            ((element_type_315) =.? (@repr U8 48)) ;;
                           '(pk_299 : (seq uint8)) ←
                            (if temp_416:bool_ChoiceEquality
                              then (*not state*) (let temp_then :=  '(
                                    len_len_317 : uint_size) ←
                                  ( temp_418 ←
                                      (get_length_length (seq2_316)) ;;
                                    ret (temp_418)) ;;
                                 '(temp_420 : bool_ChoiceEquality) ←
                                  ((len_len_317) =.? (usize 0)) ;;
                                 '(pk_299 : (seq uint8)) ←
                                  (if temp_420:bool_ChoiceEquality
                                    then (*not state*) (let temp_then :=  '(
                                          oid_len_318 : uint_size) ←
                                        ( temp_422 ←
                                            (get_short_length (seq2_316)) ;;
                                          ret (temp_422)) ;;
                                       '(temp_424 : bool_ChoiceEquality) ←
                                        ((oid_len_318) >=.? (usize 9)) ;;
                                       '(pk_299 : (seq uint8)) ←
                                        (if temp_424:bool_ChoiceEquality
                                          then (*not state*) (
                                            let temp_then :=  '(
                                                expected_319 : seq uint8) ←
                                              ( '(temp_426 : int8) ←
                                                  (secret (@repr U8 6)) ;;
                                                 '(temp_428 : int8) ←
                                                  (secret (@repr U8 7)) ;;
                                                 '(temp_430 : int8) ←
                                                  (secret (@repr U8 42)) ;;
                                                 '(temp_432 : int8) ←
                                                  (secret (@repr U8 134)) ;;
                                                 '(temp_434 : int8) ←
                                                  (secret (@repr U8 72)) ;;
                                                 '(temp_436 : int8) ←
                                                  (secret (@repr U8 206)) ;;
                                                 '(temp_438 : int8) ←
                                                  (secret (@repr U8 61)) ;;
                                                 '(temp_440 : int8) ←
                                                  (secret (@repr U8 2)) ;;
                                                 '(temp_442 : int8) ←
                                                  (secret (@repr U8 1)) ;;
                                                 '(temp_444 : nseq uint8 9) ←
                                                  (array_from_list uint8 [
                                                      temp_426;
                                                      temp_428;
                                                      temp_430;
                                                      temp_432;
                                                      temp_434;
                                                      temp_436;
                                                      temp_438;
                                                      temp_440;
                                                      temp_442
                                                    ]) ;;
                                                 '(temp_446 : seq uint8) ←
                                                  (array_to_seq (temp_444)) ;;
                                                 '(temp_448 : byte_seq) ←
                                                  (seq_from_seq (temp_446)) ;;
                                                ret (temp_448)) ;;
                                             '(oid_320 : seq uint8) ←
                                              ( '(temp_450 : seq uint8) ←
                                                  (seq_slice (seq2_316) (
                                                      usize 1) (usize 9)) ;;
                                                ret (temp_450)) ;;
                                             '(
                                                  ec_pk_oid_301 : bool_ChoiceEquality) ←
                                                (ret (
                                                    (true : bool_ChoiceEquality))) ;;
                                              #put ec_pk_oid_301_loc := ec_pk_oid_301 ;;
                                             '(ec_pk_oid_301 : (
                                                  bool_ChoiceEquality
                                                )) ←
                                              (foldi' (usize 0) (
                                                    usize 9) ec_pk_oid_301 (
                                                    L2 := CEfset (
                                                      [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) (
                                                    I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_321 ec_pk_oid_301 =>
                                                  ({ code  '(
                                                        oid_byte_equal_322 : bool_ChoiceEquality) ←
                                                      ( '(temp_452 : uint8) ←
                                                          (seq_index (oid_320) (
                                                              i_321)) ;;
                                                         temp_454 ←
                                                          (uint8_declassify (
                                                              temp_452)) ;;
                                                         '(temp_456 : uint8) ←
                                                          (seq_index (
                                                              expected_319) (
                                                              i_321)) ;;
                                                         temp_458 ←
                                                          (uint8_declassify (
                                                              temp_456)) ;;
                                                         '(
                                                            temp_460 : bool_ChoiceEquality) ←
                                                          ((temp_454) =.? (
                                                              temp_458)) ;;
                                                        ret (temp_460)) ;;
                                                     '(
                                                          ec_pk_oid_301 : bool_ChoiceEquality) ←
                                                        (( '(
                                                                temp_462 : bool_ChoiceEquality) ←
                                                              ((
                                                                  ec_pk_oid_301) && (
                                                                  oid_byte_equal_322)) ;;
                                                            ret (temp_462))) ;;
                                                      #put ec_pk_oid_301_loc := ec_pk_oid_301 ;;
                                                    
                                                    @ret ((bool_ChoiceEquality
                                                      )) (
                                                      ec_pk_oid_301) } : code (
                                                      CEfset (
                                                        [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) [interface] _))) ;;
                                            
                                             '(pk_299 : (seq uint8)) ←
                                              (
                                                if ec_pk_oid_301:bool_ChoiceEquality
                                                then (*not state*) (
                                                  let temp_then :=  '(
                                                      bit_string_323 : seq uint8) ←
                                                    ( '(
                                                          temp_464 : uint_size) ←
                                                        ((oid_len_318) .+ (
                                                            usize 1)) ;;
                                                       '(
                                                          temp_466 : uint_size) ←
                                                        (seq_len (seq2_316)) ;;
                                                       '(
                                                          temp_468 : uint_size) ←
                                                        ((temp_466) .- (
                                                            oid_len_318)) ;;
                                                       '(
                                                          temp_470 : uint_size) ←
                                                        ((temp_468) .- (
                                                            usize 1)) ;;
                                                       '(
                                                          temp_472 : seq uint8) ←
                                                        (seq_slice (seq2_316) (
                                                            temp_464) (
                                                            temp_470)) ;;
                                                      ret (temp_472)) ;;
                                                   '(temp_474 : uint8) ←
                                                    (seq_index (
                                                        bit_string_323) (
                                                        usize 0)) ;;
                                                   temp_476 ←
                                                    (uint8_declassify (
                                                        temp_474)) ;;
                                                   '(
                                                      temp_478 : bool_ChoiceEquality) ←
                                                    ((temp_476) =.? (
                                                        @repr U8 3)) ;;
                                                   '(pk_299 : (seq uint8)) ←
                                                    (
                                                      if temp_478:bool_ChoiceEquality
                                                      then (*not state*) (
                                                        let temp_then :=  '(
                                                            pk_len_324 : uint_size) ←
                                                          ( '(
                                                                temp_480 : uint8) ←
                                                              (seq_index (
                                                                  bit_string_323) (
                                                                  usize 1)) ;;
                                                             temp_482 ←
                                                              (
                                                                declassify_usize_from_uint8 (
                                                                  temp_480)) ;;
                                                            ret (temp_482)) ;;
                                                         '(
                                                            zeroes_325 : uint_size) ←
                                                          ( '(
                                                                temp_484 : uint8) ←
                                                              (seq_index (
                                                                  bit_string_323) (
                                                                  usize 2)) ;;
                                                             temp_486 ←
                                                              (
                                                                declassify_usize_from_uint8 (
                                                                  temp_484)) ;;
                                                            ret (temp_486)) ;;
                                                         '(
                                                            uncompressed_326 : uint_size) ←
                                                          ( '(
                                                                temp_488 : uint8) ←
                                                              (seq_index (
                                                                  bit_string_323) (
                                                                  usize 3)) ;;
                                                             temp_490 ←
                                                              (
                                                                declassify_usize_from_uint8 (
                                                                  temp_488)) ;;
                                                            ret (temp_490)) ;;
                                                         '(
                                                              pk_299 : seq uint8) ←
                                                            (( '(
                                                                    temp_492 : uint_size) ←
                                                                  ((
                                                                      pk_len_324) .- (
                                                                      usize 2)) ;;
                                                                 '(
                                                                    temp_494 : seq uint8) ←
                                                                  (seq_slice (
                                                                      bit_string_323) (
                                                                      usize 4) (
                                                                      temp_492)) ;;
                                                                ret (
                                                                  temp_494))) ;;
                                                          #put pk_299_loc := pk_299 ;;
                                                        
                                                        @ret ((seq uint8)) (
                                                          pk_299) in
                                                        (
                                                          { code temp_then } : code (
                                                            CEfset (
                                                              [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) [interface] _))
                                                      else @ret ((seq uint8)) (
                                                        pk_299)) ;;
                                                  
                                                  @ret ((seq uint8)) (pk_299) in
                                                  ({ code temp_then } : code (
                                                      CEfset (
                                                        [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) [interface] _))
                                                else @ret ((seq uint8)) (
                                                  pk_299)) ;;
                                            
                                            @ret ((seq uint8)) (pk_299) in
                                            ({ code temp_then } : code (CEfset (
                                                  [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) [interface] _))
                                          else @ret ((seq uint8)) (pk_299)) ;;
                                      
                                      @ret ((seq uint8)) (pk_299) in
                                      ({ code temp_then } : code (CEfset (
                                            [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) [interface] _))
                                    else @ret ((seq uint8)) (pk_299)) ;;
                                
                                @ret ((seq uint8)) (pk_299) in
                                ({ code temp_then } : code (CEfset (
                                      [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) [interface] _))
                              else @ret ((seq uint8)) (pk_299)) ;;
                          
                          @ret ((seq uint8)) (pk_299) in
                          ({ code temp_then } : code (CEfset (
                                [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) [interface] _))
                        else @ret ((seq uint8)) (pk_299)) ;;
                    
                     '(seq1_298 : seq uint8) ←
                        (( '(temp_496 : uint_size) ←
                              (seq_len (seq1_298)) ;;
                             '(temp_498 : uint_size) ←
                              ((temp_496) .- (len_300)) ;;
                             '(temp_500 : seq uint8) ←
                              (seq_slice (seq1_298) (len_300) (temp_498)) ;;
                            ret (temp_500))) ;;
                      #put seq1_298_loc := seq1_298 ;;
                    
                    @ret ((seq uint8 '× seq uint8)) (prod_ce(seq1_298, pk_299
                      )) in
                    ({ code temp_then } : code (CEfset (
                          [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) [interface] _))
                  else @ret ((seq uint8 '× seq uint8)) (prod_ce(
                      seq1_298,
                      pk_299
                    ))) ;;
              let '(seq1_298, pk_299) :=
                (temp_502) : (seq uint8 '× seq uint8) in
              
              @ret ((seq uint8 '× seq uint8)) (prod_ce(seq1_298, pk_299
                )) } : code (CEfset (
                  [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) [interface] _))) ;;
      let '(seq1_298, pk_299) :=
        (temp_508) : (seq uint8 '× seq uint8) in
      
       '(temp_504 : uint_size) ←
        (seq_len (pk_299)) ;;
       '(temp_506 : bool_ChoiceEquality) ←
        ((temp_504) =.? (usize 0)) ;;
      @ret ((result crypto_error_t verification_key_t)) ((if (
            temp_506):bool_ChoiceEquality then (*inline*) (
            @inr verification_key_t crypto_error_t (InvalidCert)) else (
            @inl verification_key_t crypto_error_t (pk_299)))) } : code (
        CEfset (
          [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) [interface
      #val #[ GET_LENGTH_LENGTH_STATE ] : get_length_length_state_inp → get_length_length_state_out ;
      #val #[ GET_LENGTH_STATE ] : get_length_state_inp → get_length_state_out ;
      #val #[ GET_SHORT_LENGTH_STATE ] : get_short_length_state_inp → get_short_length_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_verification_key_from_cert_state : package _ _ _ :=
  (seq_link verification_key_from_cert_state link_rest(
      package_get_length_length_state,package_get_length_state,package_get_short_length_state)).
Fail Next Obligation.

Notation "'verification_key_from_cert_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'verification_key_from_cert_out'" :=((
    result crypto_error_t verification_key_t) : choice_type) (in custom pack_type at level 2).
Definition VERIFICATION_KEY_FROM_CERT : nat :=
  (514).
Program Definition verification_key_from_cert
  (cert_306 : byte_seq)
  :both (CEfset (
      [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) [interface
  #val #[ GET_LENGTH ] : get_length_inp → get_length_out ;
  #val #[ GET_LENGTH_LENGTH ] : get_length_length_inp → get_length_length_out ;
  #val #[ GET_SHORT_LENGTH ] : get_short_length_inp → get_short_length_out ] (
    (result crypto_error_t verification_key_t)) :=
  #import {sig #[ GET_LENGTH ] : get_length_inp → get_length_out } as get_length ;;
  let get_length := fun x_0 x_1 => get_length (x_0,x_1) in
  #import {sig #[ GET_LENGTH_LENGTH ] : get_length_length_inp → get_length_length_out } as get_length_length ;;
  let get_length_length := fun x_0 => get_length_length (x_0) in
  #import {sig #[ GET_SHORT_LENGTH ] : get_short_length_inp → get_short_length_out } as get_short_length ;;
  let get_short_length := fun x_0 => get_short_length (x_0) in
  letb skip_307 : uint_size :=
    ((lift_to_both0 (usize 2)) .+ (get_length_length (seq_slice_range (
            lift_to_both0 cert_306) (prod_b(
              lift_to_both0 (usize 1),
              seq_len (lift_to_both0 cert_306)
            ))))) .+ (lift_to_both0 (usize 1)) in
  letb seq1_len_len_308 : uint_size :=
    get_length_length (seq_slice_range (lift_to_both0 cert_306) (prod_b(
          lift_to_both0 skip_307,
          seq_len (lift_to_both0 cert_306)
        ))) in
  letb skip_309 : uint_size :=
    (lift_to_both0 skip_307) .+ (lift_to_both0 (usize 1)) in
  letb seq1_len_310 : uint_size :=
    get_length (seq_slice (lift_to_both0 cert_306) (lift_to_both0 skip_309) ((
          seq_len (lift_to_both0 cert_306)) .- (lift_to_both0 skip_309))) (
      lift_to_both0 seq1_len_len_308) in
  letbm seq1_298 : seq uint8 loc( seq1_298_loc ) :=
    seq_slice_range (lift_to_both0 cert_306) (prod_b(
        (lift_to_both0 skip_309) .+ (lift_to_both0 seq1_len_len_308),
        ((lift_to_both0 skip_309) .+ (lift_to_both0 seq1_len_len_308)) .+ (
          lift_to_both0 seq1_len_310)
      )) in
  letbm pk_299 : seq uint8 loc( pk_299_loc ) :=
    seq_new_ (default : uint8) (lift_to_both0 (usize 0)) in
  letb '(seq1_298, pk_299) :=
    foldi_both' (lift_to_both0 (usize 0)) (seq_len (
          lift_to_both0 seq1_298)) prod_ce(seq1_298, pk_299) (L := (CEfset (
          [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc]))) (I := (
        [interface #val #[ GET_LENGTH ] : get_length_inp → get_length_out ;
        #val #[ GET_LENGTH_LENGTH ] : get_length_length_inp → get_length_length_out ;
        #val #[ GET_SHORT_LENGTH ] : get_short_length_inp → get_short_length_out
        ])) (fun i_311 '(seq1_298, pk_299) =>
      letb '(seq1_298, pk_299) :=
        if (seq_len (lift_to_both0 seq1_298)) >.? (lift_to_both0 (
            usize 0)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
          [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) (L2 := CEfset (
          [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) (H_loc_incl := _) (H_opsig_incl := _)a (
          letb element_type_312 : int8 :=
            uint8_declassify (seq_index (seq1_298) (lift_to_both0 (usize 0))) in
          letbm seq1_298 loc( seq1_298_loc ) :=
            seq_slice (lift_to_both0 seq1_298) (lift_to_both0 (usize 1)) ((
                seq_len (lift_to_both0 seq1_298)) .- (lift_to_both0 (
                  usize 1))) in
          letb len_len_313 : uint_size :=
            get_length_length (lift_to_both0 seq1_298) in
          letbm len_300 : uint_size loc( len_300_loc ) :=
            get_short_length (lift_to_both0 seq1_298) in
          letbm seq1_298 loc( seq1_298_loc ) :=
            seq_slice (lift_to_both0 seq1_298) (lift_to_both0 (usize 1)) ((
                seq_len (lift_to_both0 seq1_298)) .- (lift_to_both0 (
                  usize 1))) in
          letb 'len_300 :=
            if (lift_to_both0 len_len_313) !=.? (lift_to_both0 (
                usize 0)) :bool_ChoiceEquality
            then lift_scope (L1 := CEfset (
              [seq1_298_loc ; pk_299_loc ; len_300_loc])) (L2 := CEfset (
              [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) (H_loc_incl := _) (H_opsig_incl := _)a (
              letbm len_300 loc( len_300_loc ) :=
                (get_length (lift_to_both0 seq1_298) (
                    lift_to_both0 len_len_313)) .+ (
                  lift_to_both0 len_len_313) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 len_300)
              )
            else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 len_300)
             in
          letb 'pk_299 :=
            if ((lift_to_both0 element_type_312) =.? (lift_to_both0 (
                  @repr U8 48))) && ((seq_len (lift_to_both0 pk_299)) =.? (
                lift_to_both0 (usize 0))) :bool_ChoiceEquality
            then lift_scope (L1 := CEfset (
              [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) (L2 := CEfset (
              [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) (H_loc_incl := _) (H_opsig_incl := _)a (
              letb seq2_314 : seq uint8 :=
                seq_slice (lift_to_both0 seq1_298) (lift_to_both0 len_len_313) (
                  lift_to_both0 len_300) in
              letb element_type_315 : int8 :=
                uint8_declassify (seq_index (seq2_314) (lift_to_both0 (
                      usize 0))) in
              letb seq2_316 : seq uint8 :=
                seq_slice (lift_to_both0 seq2_314) (lift_to_both0 (usize 1)) ((
                    seq_len (lift_to_both0 seq2_314)) .- (lift_to_both0 (
                      usize 1))) in
              letb 'pk_299 :=
                if (lift_to_both0 element_type_315) =.? (lift_to_both0 (
                    @repr U8 48)) :bool_ChoiceEquality
                then lift_scope (L1 := CEfset (
                  [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) (L2 := CEfset (
                  [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) (H_loc_incl := _) (H_opsig_incl := _)a (
                  letb len_len_317 : uint_size :=
                    get_length_length (lift_to_both0 seq2_316) in
                  letb 'pk_299 :=
                    if (lift_to_both0 len_len_317) =.? (lift_to_both0 (
                        usize 0)) :bool_ChoiceEquality
                    then lift_scope (L1 := CEfset (
                      [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) (L2 := CEfset (
                      [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) (H_loc_incl := _) (H_opsig_incl := _)a (
                      letb oid_len_318 : uint_size :=
                        get_short_length (lift_to_both0 seq2_316) in
                      letb 'pk_299 :=
                        if (lift_to_both0 oid_len_318) >=.? (lift_to_both0 (
                            usize 9)) :bool_ChoiceEquality
                        then lift_scope (L1 := CEfset (
                          [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) (L2 := CEfset (
                          [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) (H_loc_incl := _) (H_opsig_incl := _)a (
                          letb expected_319 : seq uint8 :=
                            seq_from_seq (array_to_seq (array_from_list uint8 ([
                                  (secret (lift_to_both0 (@repr U8 6))) : uint8;
                                  (secret (lift_to_both0 (@repr U8 7))) : uint8;
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
                                  (secret (lift_to_both0 (@repr U8 2))) : uint8;
                                  (secret (lift_to_both0 (@repr U8 1))) : uint8
                                ]))) in
                          letb oid_320 : seq uint8 :=
                            seq_slice (lift_to_both0 seq2_316) (lift_to_both0 (
                                usize 1)) (lift_to_both0 (usize 9)) in
                          letbm ec_pk_oid_301 : bool_ChoiceEquality loc( ec_pk_oid_301_loc ) :=
                            lift_to_both0 ((true : bool_ChoiceEquality)) in
                          letb ec_pk_oid_301 :=
                            foldi_both' (lift_to_both0 (usize 0)) (
                                lift_to_both0 (usize 9)) ec_pk_oid_301 (L := (
                                CEfset (
                                  [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc]))) (I := (
                                [interface])) (fun i_321 ec_pk_oid_301 =>
                              letb oid_byte_equal_322 : bool_ChoiceEquality :=
                                (uint8_declassify (seq_index (oid_320) (
                                      lift_to_both0 i_321))) =.? (
                                  uint8_declassify (seq_index (expected_319) (
                                      lift_to_both0 i_321))) in
                              letbm ec_pk_oid_301 loc( ec_pk_oid_301_loc ) :=
                                (lift_to_both0 ec_pk_oid_301) && (
                                  lift_to_both0 oid_byte_equal_322) in
                              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                                lift_to_both0 ec_pk_oid_301)
                              ) in
                          letb 'pk_299 :=
                            if lift_to_both0 ec_pk_oid_301 :bool_ChoiceEquality
                            then lift_scope (L1 := CEfset (
                              [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) (L2 := CEfset (
                              [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) (H_loc_incl := _) (H_opsig_incl := _)a (
                              letb bit_string_323 : seq uint8 :=
                                seq_slice (lift_to_both0 seq2_316) ((
                                    lift_to_both0 oid_len_318) .+ (
                                    lift_to_both0 (usize 1))) (((seq_len (
                                        lift_to_both0 seq2_316)) .- (
                                      lift_to_both0 oid_len_318)) .- (
                                    lift_to_both0 (usize 1))) in
                              letb 'pk_299 :=
                                if (uint8_declassify (seq_index (
                                      bit_string_323) (lift_to_both0 (
                                        usize 0)))) =.? (lift_to_both0 (
                                    @repr U8 3)) :bool_ChoiceEquality
                                then lift_scope (L1 := CEfset (
                                  [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) (L2 := CEfset (
                                  [seq1_298_loc ; pk_299_loc ; len_300_loc ; ec_pk_oid_301_loc])) (H_loc_incl := _) (H_opsig_incl := _)a (
                                  letb pk_len_324 : uint_size :=
                                    declassify_usize_from_uint8 (seq_index (
                                        bit_string_323) (lift_to_both0 (
                                          usize 1))) in
                                  letb zeroes_325 : uint_size :=
                                    declassify_usize_from_uint8 (seq_index (
                                        bit_string_323) (lift_to_both0 (
                                          usize 2))) in
                                  letb uncompressed_326 : uint_size :=
                                    declassify_usize_from_uint8 (seq_index (
                                        bit_string_323) (lift_to_both0 (
                                          usize 3))) in
                                  letbm pk_299 loc( pk_299_loc ) :=
                                    seq_slice (lift_to_both0 bit_string_323) (
                                      lift_to_both0 (usize 4)) ((
                                        lift_to_both0 pk_len_324) .- (
                                        lift_to_both0 (usize 2))) in
                                  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                                    lift_to_both0 pk_299)
                                  )
                                else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                                  lift_to_both0 pk_299)
                                 in
                              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                                lift_to_both0 pk_299)
                              )
                            else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                              lift_to_both0 pk_299)
                             in
                          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                            lift_to_both0 pk_299)
                          )
                        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                          lift_to_both0 pk_299)
                         in
                      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                        lift_to_both0 pk_299)
                      )
                    else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                      lift_to_both0 pk_299)
                     in
                  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                    lift_to_both0 pk_299)
                  )
                else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 pk_299)
                 in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 pk_299)
              )
            else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 pk_299)
             in
          letbm seq1_298 loc( seq1_298_loc ) :=
            seq_slice (lift_to_both0 seq1_298) (lift_to_both0 len_300) ((
                seq_len (lift_to_both0 seq1_298)) .- (lift_to_both0 len_300)) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 seq1_298,
              lift_to_both0 pk_299
            ))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 seq1_298,
            lift_to_both0 pk_299
          ))
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 seq1_298,
          lift_to_both0 pk_299
        ))
      ) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
    if is_pure (I := [interface]) ((seq_len (lift_to_both0 pk_299)) =.? (
        lift_to_both0 (usize 0)))
    then @Err verification_key_t crypto_error_t (InvalidCert)
    else @Ok verification_key_t crypto_error_t (lift_to_both0 pk_299))
  .
Fail Next Obligation.

Definition concat_signature_pure
  (r_515 : p256_scalar_t)
  (s_516 : p256_scalar_t)
  : (result crypto_error_t signature_t) :=
  let signature_517 : seq uint8 :=
    seq_concat (seq_concat (seq_new_ (default : uint8) (usize 0)) (
        nat_mod_to_byte_seq_be (r_515))) (nat_mod_to_byte_seq_be (s_516)) in 
  @Ok signature_t crypto_error_t (signature_517).
Definition concat_signature_pure_code
  (r_515 : p256_scalar_t)
  (s_516 : p256_scalar_t)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t signature_t))) :=
  lift_to_code (concat_signature_pure r_515 s_516).


Notation "'concat_signature_state_inp'" := (
  p256_scalar_t '× p256_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'concat_signature_state_out'" := ((
    result crypto_error_t signature_t) : choice_type) (in custom pack_type at level 2).
Definition CONCAT_SIGNATURE_STATE : nat :=
  (528).
Program Definition concat_signature_state
   : package (fset.fset0) [interface] [interface
  #val #[ CONCAT_SIGNATURE_STATE ] : concat_signature_state_inp → concat_signature_state_out
  ] :=
  (
    [package #def #[ CONCAT_SIGNATURE_STATE ] (temp_inp : concat_signature_state_inp) : concat_signature_state_out { 
    let '(r_515 , s_516) := temp_inp : p256_scalar_t '× p256_scalar_t in
    ({ code  '(signature_517 : seq uint8) ←
        ( temp_519 ←
            (seq_new_ (default : uint8) (usize 0)) ;;
           temp_521 ←
            (nat_mod_to_byte_seq_be (r_515)) ;;
           '(temp_523 : seq uint8) ←
            (seq_concat (temp_519) (temp_521)) ;;
           temp_525 ←
            (nat_mod_to_byte_seq_be (s_516)) ;;
           '(temp_527 : seq uint8) ←
            (seq_concat (temp_523) (temp_525)) ;;
          ret (temp_527)) ;;
      @ret ((result crypto_error_t signature_t)) (
        @inl signature_t crypto_error_t (signature_517)) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_concat_signature_state : package _ _ _ :=
  (concat_signature_state).
Fail Next Obligation.

Notation "'concat_signature_inp'" :=(
  p256_scalar_t '× p256_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'concat_signature_out'" :=((
    result crypto_error_t signature_t) : choice_type) (in custom pack_type at level 2).
Definition CONCAT_SIGNATURE : nat :=
  (529).
Program Definition concat_signature
  (r_515 : p256_scalar_t)
  (s_516 : p256_scalar_t)
  :both (fset.fset0) [interface] ((result crypto_error_t signature_t)) :=
  letb signature_517 : seq uint8 :=
    seq_concat (seq_concat (seq_new_ (default : uint8) (lift_to_both0 (
            usize 0))) (nat_mod_to_byte_seq_be (lift_to_both0 r_515))) (
      nat_mod_to_byte_seq_be (lift_to_both0 s_516)) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
    @Ok signature_t crypto_error_t (lift_to_both0 signature_517))
  .
Fail Next Obligation.

Definition p256_sign_pure
  (ps_530 : signature_key_t)
  (payload_531 : byte_seq)
  (ent_532 : entropy_t)
  : (result crypto_error_t signature_t) :=
  let random_533 : random_t :=
    array_from_seq (32) (seq_slice_range (ent_532) (prod_ce(usize 0, usize 32
        ))) in 
  let nonce_534 : p256_scalar_t :=
    nat_mod_from_byte_seq_be (array_to_seq (random_533)) in 
  match ecdsa_p256_sha256_sign (payload_531) (nat_mod_from_byte_seq_be (
      ps_530)) (nonce_534) with
  | Ok (r_535, s_536) => concat_signature (r_535) (s_536)
  | Err _ => @Err signature_t crypto_error_t (CryptoError)
  end.
Definition p256_sign_pure_code
  (ps_530 : signature_key_t)
  (payload_531 : byte_seq)
  (ent_532 : entropy_t)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t signature_t))) :=
  lift_to_code (p256_sign_pure ps_530 payload_531 ent_532).


Notation "'p256_sign_state_inp'" := (
  signature_key_t '× byte_seq '× entropy_t : choice_type) (in custom pack_type at level 2).
Notation "'p256_sign_state_out'" := ((
    result crypto_error_t signature_t) : choice_type) (in custom pack_type at level 2).
Definition P256_SIGN_STATE : nat :=
  (553).
Program Definition p256_sign_state
   : package (fset.fset0) [interface
  #val #[ CONCAT_SIGNATURE_STATE ] : concat_signature_state_inp → concat_signature_state_out
  ] [interface
  #val #[ P256_SIGN_STATE ] : p256_sign_state_inp → p256_sign_state_out ] :=
  (
    [package #def #[ P256_SIGN_STATE ] (temp_inp : p256_sign_state_inp) : p256_sign_state_out { 
    let '(
      ps_530 , payload_531 , ent_532) := temp_inp : signature_key_t '× byte_seq '× entropy_t in
    #import {sig #[ CONCAT_SIGNATURE_STATE ] : concat_signature_state_inp → concat_signature_state_out } as concat_signature_state ;;
    let concat_signature_state := fun x_0 x_1 => concat_signature_state (
      x_0,x_1) in
    ({ code  '(random_533 : random_t) ←
        ( '(temp_538 : entropy_t) ←
            (seq_slice_range (ent_532) (prod_ce(usize 0, usize 32))) ;;
           '(temp_540 : random_t) ←
            (array_from_seq (32) (temp_538)) ;;
          ret (temp_540)) ;;
       '(nonce_534 : p256_scalar_t) ←
        ( '(temp_542 : seq uint8) ←
            (array_to_seq (random_533)) ;;
           '(temp_544 : p256_scalar_t) ←
            (nat_mod_from_byte_seq_be (temp_542)) ;;
          ret (temp_544)) ;;
       '(temp_546 : p256_scalar_t) ←
        (nat_mod_from_byte_seq_be (ps_530)) ;;
       temp_548 ←
        (ecdsa_p256_sha256_sign (payload_531) (temp_546) (nonce_534)) ;;
       temp_552 ←
        ((({ code match temp_548 with
              | inl (r_535, s_536) => temp_550 ←
                (concat_signature (r_535) (s_536)) ;;
               ret (temp_550)
              | inr _ => ret (@inr signature_t crypto_error_t (CryptoError))
              end } : code _ _ _))) ;;
      @ret ((result crypto_error_t signature_t)) (temp_552) } : code (
        fset.fset0) [interface
      #val #[ CONCAT_SIGNATURE_STATE ] : concat_signature_state_inp → concat_signature_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_p256_sign_state : package _ _ _ :=
  (seq_link p256_sign_state link_rest(package_concat_signature_state)).
Fail Next Obligation.

Notation "'p256_sign_inp'" :=(
  signature_key_t '× byte_seq '× entropy_t : choice_type) (in custom pack_type at level 2).
Notation "'p256_sign_out'" :=((
    result crypto_error_t signature_t) : choice_type) (in custom pack_type at level 2).
Definition P256_SIGN : nat :=
  (554).
Program Definition p256_sign
  (ps_530 : signature_key_t)
  (payload_531 : byte_seq)
  (ent_532 : entropy_t)
  :both (fset.fset0) [interface
  #val #[ CONCAT_SIGNATURE ] : concat_signature_inp → concat_signature_out ;
  #val #[ ECDSA_P256_SHA256_SIGN ] : ecdsa_p256_sha256_sign_inp → ecdsa_p256_sha256_sign_out
  ] ((result crypto_error_t signature_t)) :=
  #import {sig #[ CONCAT_SIGNATURE ] : concat_signature_inp → concat_signature_out } as concat_signature ;;
  let concat_signature := fun x_0 x_1 => concat_signature (x_0,x_1) in
  #import {sig #[ ECDSA_P256_SHA256_SIGN ] : ecdsa_p256_sha256_sign_inp → ecdsa_p256_sha256_sign_out } as ecdsa_p256_sha256_sign ;;
  let ecdsa_p256_sha256_sign := fun x_0 x_1 x_2 => ecdsa_p256_sha256_sign (
    x_0,x_1,x_2) in
  letb random_533 : random_t :=
    array_from_seq (32) (seq_slice_range (lift_to_both0 ent_532) (prod_b(
          lift_to_both0 (usize 0),
          lift_to_both0 (usize 32)
        ))) in
  letb nonce_534 : p256_scalar_t :=
    nat_mod_from_byte_seq_be (array_to_seq (lift_to_both0 random_533)) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match)
  .
Fail Next Obligation.

Definition sign_pure
  (sa_555 : signature_scheme_t)
  (ps_556 : signature_key_t)
  (payload_557 : byte_seq)
  (ent_558 : entropy_t)
  : (result crypto_error_t signature_t) :=
  match sa_555 with
  | EcdsaSecp256r1Sha256 => p256_sign (ps_556) (payload_557) (ent_558)
  | ED25519 => @Err signature_t crypto_error_t (UnsupportedAlgorithm)
  | RsaPssRsaSha256 => @Err signature_t crypto_error_t (UnsupportedAlgorithm)
  end.
Definition sign_pure_code
  (sa_555 : signature_scheme_t)
  (ps_556 : signature_key_t)
  (payload_557 : byte_seq)
  (ent_558 : entropy_t)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t signature_t))) :=
  lift_to_code (sign_pure sa_555 ps_556 payload_557 ent_558).


Notation "'sign_state_inp'" := (
  signature_scheme_t '× signature_key_t '× byte_seq '× entropy_t : choice_type) (in custom pack_type at level 2).
Notation "'sign_state_out'" := ((
    result crypto_error_t signature_t) : choice_type) (in custom pack_type at level 2).
Definition SIGN_STATE : nat :=
  (563).
Program Definition sign_state
   : package (fset.fset0) [interface
  #val #[ P256_SIGN_STATE ] : p256_sign_state_inp → p256_sign_state_out
  ] [interface #val #[ SIGN_STATE ] : sign_state_inp → sign_state_out ] :=
  ([package #def #[ SIGN_STATE ] (temp_inp : sign_state_inp) : sign_state_out { 
    let '(
      sa_555 , ps_556 , payload_557 , ent_558) := temp_inp : signature_scheme_t '× signature_key_t '× byte_seq '× entropy_t in
    #import {sig #[ P256_SIGN_STATE ] : p256_sign_state_inp → p256_sign_state_out } as p256_sign_state ;;
    let p256_sign_state := fun x_0 x_1 x_2 => p256_sign_state (x_0,x_1,x_2) in
    ({ code  temp_562 ←
        ((({ code match sa_555 with
              | EcdsaSecp256r1Sha256 => temp_560 ←
                (p256_sign (ps_556) (payload_557) (ent_558)) ;;
               ret (temp_560)
              | ED25519 => ret (@inr signature_t crypto_error_t (
                  UnsupportedAlgorithm))
              | RsaPssRsaSha256 => ret (@inr signature_t crypto_error_t (
                  UnsupportedAlgorithm))
              end } : code _ _ _))) ;;
      @ret ((result crypto_error_t signature_t)) (temp_562) } : code (
        fset.fset0) [interface
      #val #[ P256_SIGN_STATE ] : p256_sign_state_inp → p256_sign_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_sign_state : package _ _ _ :=
  (seq_link sign_state link_rest(package_p256_sign_state)).
Fail Next Obligation.

Notation "'sign_inp'" :=(
  signature_scheme_t '× signature_key_t '× byte_seq '× entropy_t : choice_type) (in custom pack_type at level 2).
Notation "'sign_out'" :=((
    result crypto_error_t signature_t) : choice_type) (in custom pack_type at level 2).
Definition SIGN : nat :=
  (564).
Program Definition sign
  (sa_555 : signature_scheme_t)
  (ps_556 : signature_key_t)
  (payload_557 : byte_seq)
  (ent_558 : entropy_t)
  :both (fset.fset0) [interface
  #val #[ P256_SIGN ] : p256_sign_inp → p256_sign_out ] ((
      result crypto_error_t signature_t)) :=
  #import {sig #[ P256_SIGN ] : p256_sign_inp → p256_sign_out } as p256_sign ;;
  let p256_sign := fun x_0 x_1 x_2 => p256_sign (x_0,x_1,x_2) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) .
Fail Next Obligation.

Definition p256_verify_pure
  (pk_565 : verification_key_t)
  (payload_566 : byte_seq)
  (sig_567 : byte_seq)
  : (result crypto_error_t unit) :=
  let '(pk_x_568, pk_y_569) :=
    prod_ce(
      nat_mod_from_byte_seq_be (seq_slice (pk_565) (usize 0) (usize 32)),
      nat_mod_from_byte_seq_be (seq_slice (pk_565) (usize 32) (usize 32))
    ) : (p256_field_element_t '× p256_field_element_t) in 
  let '(r_570, s_571) :=
    prod_ce(
      nat_mod_from_byte_seq_be (seq_slice (sig_567) (usize 0) (usize 32)),
      nat_mod_from_byte_seq_be (seq_slice (sig_567) (usize 32) (usize 32))
    ) : (p256_scalar_t '× p256_scalar_t) in 
  match ecdsa_p256_sha256_verify (payload_566) (prod_ce(pk_x_568, pk_y_569)) (
    prod_ce(r_570, s_571)) with
  | Ok tt => @Ok unit crypto_error_t (tt)
  | Err _ => @Err unit crypto_error_t (VerifyFailed)
  end.
Definition p256_verify_pure_code
  (pk_565 : verification_key_t)
  (payload_566 : byte_seq)
  (sig_567 : byte_seq)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t unit))) :=
  lift_to_code (p256_verify_pure pk_565 payload_566 sig_567).


Notation "'p256_verify_state_inp'" := (
  verification_key_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'p256_verify_state_out'" := ((
    result crypto_error_t unit_ChoiceEquality) : choice_type) (in custom pack_type at level 2).
Definition P256_VERIFY_STATE : nat :=
  (596).
Program Definition p256_verify_state
   : package (fset.fset0) [interface] [interface
  #val #[ P256_VERIFY_STATE ] : p256_verify_state_inp → p256_verify_state_out
  ] :=
  (
    [package #def #[ P256_VERIFY_STATE ] (temp_inp : p256_verify_state_inp) : p256_verify_state_out { 
    let '(
      pk_565 , payload_566 , sig_567) := temp_inp : verification_key_t '× byte_seq '× byte_seq in
    ({ code  temp_595 ←
        ( '(temp_573 : verification_key_t) ←
            (seq_slice (pk_565) (usize 0) (usize 32)) ;;
           '(temp_575 : p256_field_element_t) ←
            (nat_mod_from_byte_seq_be (temp_573)) ;;
           '(temp_577 : verification_key_t) ←
            (seq_slice (pk_565) (usize 32) (usize 32)) ;;
           '(temp_579 : p256_field_element_t) ←
            (nat_mod_from_byte_seq_be (temp_577)) ;;
          ret (prod_ce(temp_575, temp_579))) ;;
      let '(pk_x_568, pk_y_569) :=
        (temp_595) : (p256_field_element_t '× p256_field_element_t) in
       temp_593 ←
        ( '(temp_581 : byte_seq) ←
            (seq_slice (sig_567) (usize 0) (usize 32)) ;;
           '(temp_583 : p256_scalar_t) ←
            (nat_mod_from_byte_seq_be (temp_581)) ;;
           '(temp_585 : byte_seq) ←
            (seq_slice (sig_567) (usize 32) (usize 32)) ;;
           '(temp_587 : p256_scalar_t) ←
            (nat_mod_from_byte_seq_be (temp_585)) ;;
          ret (prod_ce(temp_583, temp_587))) ;;
      let '(r_570, s_571) :=
        (temp_593) : (p256_scalar_t '× p256_scalar_t) in
       temp_589 ←
        (ecdsa_p256_sha256_verify (payload_566) (prod_ce(pk_x_568, pk_y_569)) (
            prod_ce(r_570, s_571))) ;;
       temp_591 ←
        ((({ code match temp_589 with
              | inl tt => ret (@inl unit_ChoiceEquality crypto_error_t (tt))
              | inr _ => ret (@inr unit_ChoiceEquality crypto_error_t (
                  VerifyFailed))
              end } : code _ _ _))) ;;
      @ret ((result crypto_error_t unit_ChoiceEquality)) (temp_591) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_p256_verify_state : package _ _ _ :=
  (p256_verify_state).
Fail Next Obligation.

Notation "'p256_verify_inp'" :=(
  verification_key_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'p256_verify_out'" :=((
    result crypto_error_t unit_ChoiceEquality) : choice_type) (in custom pack_type at level 2).
Definition P256_VERIFY : nat :=
  (597).
Program Definition p256_verify
  (pk_565 : verification_key_t)
  (payload_566 : byte_seq)
  (sig_567 : byte_seq)
  :both (fset.fset0) [interface
  #val #[ ECDSA_P256_SHA256_VERIFY ] : ecdsa_p256_sha256_verify_inp → ecdsa_p256_sha256_verify_out
  ] ((result crypto_error_t unit_ChoiceEquality)) :=
  #import {sig #[ ECDSA_P256_SHA256_VERIFY ] : ecdsa_p256_sha256_verify_inp → ecdsa_p256_sha256_verify_out } as ecdsa_p256_sha256_verify ;;
  let ecdsa_p256_sha256_verify := fun x_0 x_1 x_2 => ecdsa_p256_sha256_verify (
    x_0,x_1,x_2) in
  letb '(pk_x_568, pk_y_569) : (p256_field_element_t '× p256_field_element_t
    ) :=
    prod_b(
      nat_mod_from_byte_seq_be (seq_slice (lift_to_both0 pk_565) (
          lift_to_both0 (usize 0)) (lift_to_both0 (usize 32))),
      nat_mod_from_byte_seq_be (seq_slice (lift_to_both0 pk_565) (
          lift_to_both0 (usize 32)) (lift_to_both0 (usize 32)))
    ) in
  letb '(r_570, s_571) : (p256_scalar_t '× p256_scalar_t) :=
    prod_b(
      nat_mod_from_byte_seq_be (seq_slice (lift_to_both0 sig_567) (
          lift_to_both0 (usize 0)) (lift_to_both0 (usize 32))),
      nat_mod_from_byte_seq_be (seq_slice (lift_to_both0 sig_567) (
          lift_to_both0 (usize 32)) (lift_to_both0 (usize 32)))
    ) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match)
  .
Fail Next Obligation.

Definition verify_pure
  (sa_598 : signature_scheme_t)
  (pk_599 : verification_key_t)
  (payload_600 : byte_seq)
  (sig_601 : byte_seq)
  : (result crypto_error_t unit) :=
  match sa_598 with
  | EcdsaSecp256r1Sha256 => p256_verify (pk_599) (payload_600) (sig_601)
  | ED25519 => @Err unit crypto_error_t (UnsupportedAlgorithm)
  | RsaPssRsaSha256 => @Err unit crypto_error_t (UnsupportedAlgorithm)
  end.
Definition verify_pure_code
  (sa_598 : signature_scheme_t)
  (pk_599 : verification_key_t)
  (payload_600 : byte_seq)
  (sig_601 : byte_seq)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t unit))) :=
  lift_to_code (verify_pure sa_598 pk_599 payload_600 sig_601).


Notation "'verify_state_inp'" := (
  signature_scheme_t '× verification_key_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'verify_state_out'" := ((
    result crypto_error_t unit_ChoiceEquality) : choice_type) (in custom pack_type at level 2).
Definition VERIFY_STATE : nat :=
  (606).
Program Definition verify_state
   : package (fset.fset0) [interface
  #val #[ P256_VERIFY_STATE ] : p256_verify_state_inp → p256_verify_state_out
  ] [interface #val #[ VERIFY_STATE ] : verify_state_inp → verify_state_out
  ] :=
  (
    [package #def #[ VERIFY_STATE ] (temp_inp : verify_state_inp) : verify_state_out { 
    let '(
      sa_598 , pk_599 , payload_600 , sig_601) := temp_inp : signature_scheme_t '× verification_key_t '× byte_seq '× byte_seq in
    #import {sig #[ P256_VERIFY_STATE ] : p256_verify_state_inp → p256_verify_state_out } as p256_verify_state ;;
    let p256_verify_state := fun x_0 x_1 x_2 => p256_verify_state (
      x_0,x_1,x_2) in
    ({ code  temp_605 ←
        ((({ code match sa_598 with
              | EcdsaSecp256r1Sha256 => temp_603 ←
                (p256_verify (pk_599) (payload_600) (sig_601)) ;;
               ret (temp_603)
              | ED25519 => ret (@inr unit_ChoiceEquality crypto_error_t (
                  UnsupportedAlgorithm))
              | RsaPssRsaSha256 => ret (
                @inr unit_ChoiceEquality crypto_error_t (UnsupportedAlgorithm))
              end } : code _ _ _))) ;;
      @ret ((result crypto_error_t unit_ChoiceEquality)) (temp_605) } : code (
        fset.fset0) [interface
      #val #[ P256_VERIFY_STATE ] : p256_verify_state_inp → p256_verify_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_verify_state : package _ _ _ :=
  (seq_link verify_state link_rest(package_p256_verify_state)).
Fail Next Obligation.

Notation "'verify_inp'" :=(
  signature_scheme_t '× verification_key_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'verify_out'" :=((
    result crypto_error_t unit_ChoiceEquality) : choice_type) (in custom pack_type at level 2).
Definition VERIFY : nat :=
  (607).
Program Definition verify
  (sa_598 : signature_scheme_t)
  (pk_599 : verification_key_t)
  (payload_600 : byte_seq)
  (sig_601 : byte_seq)
  :both (fset.fset0) [interface
  #val #[ P256_VERIFY ] : p256_verify_inp → p256_verify_out ] ((
      result crypto_error_t unit_ChoiceEquality)) :=
  #import {sig #[ P256_VERIFY ] : p256_verify_inp → p256_verify_out } as p256_verify ;;
  let p256_verify := fun x_0 x_1 x_2 => p256_verify (x_0,x_1,x_2) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) .
Fail Next Obligation.

Definition hkdf_extract_pure
  (ha_608 : hash_algorithm_t)
  (k_609 : key_t)
  (salt_610 : key_t)
  : (result crypto_error_t key_t) :=
  match ha_608 with
  | SHA256 => @Ok key_t crypto_error_t (seq_from_seq (array_to_seq (extract (
        salt_610) (k_609))))
  | SHA384 => @Err key_t crypto_error_t (UnsupportedAlgorithm)
  end.
Definition hkdf_extract_pure_code
  (ha_608 : hash_algorithm_t)
  (k_609 : key_t)
  (salt_610 : key_t)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t key_t))) :=
  lift_to_code (hkdf_extract_pure ha_608 k_609 salt_610).


Notation "'hkdf_extract_state_inp'" := (
  hash_algorithm_t '× key_t '× key_t : choice_type) (in custom pack_type at level 2).
Notation "'hkdf_extract_state_out'" := ((
    result crypto_error_t key_t) : choice_type) (in custom pack_type at level 2).
Definition HKDF_EXTRACT_STATE : nat :=
  (619).
Program Definition hkdf_extract_state
   : package (fset.fset0) [interface] [interface
  #val #[ HKDF_EXTRACT_STATE ] : hkdf_extract_state_inp → hkdf_extract_state_out
  ] :=
  (
    [package #def #[ HKDF_EXTRACT_STATE ] (temp_inp : hkdf_extract_state_inp) : hkdf_extract_state_out { 
    let '(
      ha_608 , k_609 , salt_610) := temp_inp : hash_algorithm_t '× key_t '× key_t in
    ({ code  temp_618 ←
        ((({ code match ha_608 with
              | SHA256 => temp_612 ←
                (extract (salt_610) (k_609)) ;;
               '(temp_614 : seq uint8) ←
                (array_to_seq (temp_612)) ;;
               '(temp_616 : key_t) ←
                (seq_from_seq (temp_614)) ;;
               ret (@inl key_t crypto_error_t (temp_616))
              | SHA384 => ret (@inr key_t crypto_error_t (UnsupportedAlgorithm))
              end } : code _ _ _))) ;;
      @ret ((result crypto_error_t key_t)) (temp_618) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_hkdf_extract_state : package _ _ _ :=
  (hkdf_extract_state).
Fail Next Obligation.

Notation "'hkdf_extract_inp'" :=(
  hash_algorithm_t '× key_t '× key_t : choice_type) (in custom pack_type at level 2).
Notation "'hkdf_extract_out'" :=((
    result crypto_error_t key_t) : choice_type) (in custom pack_type at level 2).
Definition HKDF_EXTRACT : nat :=
  (620).
Program Definition hkdf_extract
  (ha_608 : hash_algorithm_t)
  (k_609 : key_t)
  (salt_610 : key_t)
  :both (fset.fset0) [interface #val #[ EXTRACT ] : extract_inp → extract_out
  ] ((result crypto_error_t key_t)) :=
  #import {sig #[ EXTRACT ] : extract_inp → extract_out } as extract ;;
  let extract := fun x_0 x_1 => extract (x_0,x_1) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) .
Fail Next Obligation.

Definition hkdf_expand_pure
  (ha_621 : hash_algorithm_t)
  (k_622 : key_t)
  (info_623 : byte_seq)
  (len_624 : uint_size)
  : (result crypto_error_t key_t) :=
  match ha_621 with
  | SHA256 => match expand (k_622) (info_623) (len_624) with
  | Ok b_625 => @Ok key_t crypto_error_t (seq_from_seq (b_625))
  | Err _ => @Err key_t crypto_error_t (HkdfError)
  end
  | SHA384 => @Err key_t crypto_error_t (UnsupportedAlgorithm)
  end.
Definition hkdf_expand_pure_code
  (ha_621 : hash_algorithm_t)
  (k_622 : key_t)
  (info_623 : byte_seq)
  (len_624 : uint_size)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t key_t))) :=
  lift_to_code (hkdf_expand_pure ha_621 k_622 info_623 len_624).


Notation "'hkdf_expand_state_inp'" := (
  hash_algorithm_t '× key_t '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'hkdf_expand_state_out'" := ((
    result crypto_error_t key_t) : choice_type) (in custom pack_type at level 2).
Definition HKDF_EXPAND_STATE : nat :=
  (634).
Program Definition hkdf_expand_state
   : package (fset.fset0) [interface] [interface
  #val #[ HKDF_EXPAND_STATE ] : hkdf_expand_state_inp → hkdf_expand_state_out
  ] :=
  (
    [package #def #[ HKDF_EXPAND_STATE ] (temp_inp : hkdf_expand_state_inp) : hkdf_expand_state_out { 
    let '(
      ha_621 , k_622 , info_623 , len_624) := temp_inp : hash_algorithm_t '× key_t '× byte_seq '× uint_size in
    ({ code  temp_633 ←
        ((({ code match ha_621 with
              | SHA256 => temp_627 ←
                (expand (k_622) (info_623) (len_624)) ;;
               temp_631 ←
                ((({ code match temp_627 with
                      | inl b_625 => '(temp_629 : key_t) ←
                        (seq_from_seq (b_625)) ;;
                       ret (@inl key_t crypto_error_t (temp_629))
                      | inr _ => ret (@inr key_t crypto_error_t (HkdfError))
                      end } : code _ _ _))) ;;
               ret (temp_631)
              | SHA384 => ret (@inr key_t crypto_error_t (UnsupportedAlgorithm))
              end } : code _ _ _))) ;;
      @ret ((result crypto_error_t key_t)) (temp_633) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_hkdf_expand_state : package _ _ _ :=
  (hkdf_expand_state).
Fail Next Obligation.

Notation "'hkdf_expand_inp'" :=(
  hash_algorithm_t '× key_t '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'hkdf_expand_out'" :=((
    result crypto_error_t key_t) : choice_type) (in custom pack_type at level 2).
Definition HKDF_EXPAND : nat :=
  (635).
Program Definition hkdf_expand
  (ha_621 : hash_algorithm_t)
  (k_622 : key_t)
  (info_623 : byte_seq)
  (len_624 : uint_size)
  :both (fset.fset0) [interface #val #[ EXPAND ] : expand_inp → expand_out ] (
    (result crypto_error_t key_t)) :=
  #import {sig #[ EXPAND ] : expand_inp → expand_out } as expand ;;
  let expand := fun x_0 x_1 x_2 => expand (x_0,x_1,x_2) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) .
Fail Next Obligation.

Definition aes128_encrypt_pure
  (k_636 : aead_key_t)
  (iv_637 : aead_iv_t)
  (payload_638 : byte_seq)
  (ad_639 : byte_seq)
  : (result crypto_error_t byte_seq) :=
  let '(ctxt_640, tag_641) :=
    encrypt_aes128 (array_from_seq (_) (k_636)) (array_from_seq (_) (iv_637)) (
      ad_639) (payload_638) : (seq uint8 '× gf128_tag_t) in 
  @Ok byte_seq crypto_error_t (seq_concat (ctxt_640) (seq_from_seq (
        array_to_seq (tag_641)))).
Definition aes128_encrypt_pure_code
  (k_636 : aead_key_t)
  (iv_637 : aead_iv_t)
  (payload_638 : byte_seq)
  (ad_639 : byte_seq)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t byte_seq))) :=
  lift_to_code (aes128_encrypt_pure k_636 iv_637 payload_638 ad_639).


Notation "'aes128_encrypt_state_inp'" := (
  aead_key_t '× aead_iv_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'aes128_encrypt_state_out'" := ((
    result crypto_error_t byte_seq) : choice_type) (in custom pack_type at level 2).
Definition AES128_ENCRYPT_STATE : nat :=
  (656).
Program Definition aes128_encrypt_state
   : package (fset.fset0) [interface] [interface
  #val #[ AES128_ENCRYPT_STATE ] : aes128_encrypt_state_inp → aes128_encrypt_state_out
  ] :=
  (
    [package #def #[ AES128_ENCRYPT_STATE ] (temp_inp : aes128_encrypt_state_inp) : aes128_encrypt_state_out { 
    let '(
      k_636 , iv_637 , payload_638 , ad_639) := temp_inp : aead_key_t '× aead_iv_t '× byte_seq '× byte_seq in
    ({ code  temp_655 ←
        ( '(temp_643 : key128_t) ←
            (array_from_seq (_) (k_636)) ;;
           '(temp_645 : aes_nonce_t) ←
            (array_from_seq (_) (iv_637)) ;;
           temp_647 ←
            (encrypt_aes128 (temp_643) (temp_645) (ad_639) (payload_638)) ;;
          ret (temp_647)) ;;
      let '(ctxt_640, tag_641) :=
        (temp_655) : (seq uint8 '× gf128_tag_t) in
       '(temp_649 : seq uint8) ←
        (array_to_seq (tag_641)) ;;
       '(temp_651 : byte_seq) ←
        (seq_from_seq (temp_649)) ;;
       '(temp_653 : seq uint8) ←
        (seq_concat (ctxt_640) (temp_651)) ;;
      @ret ((result crypto_error_t byte_seq)) (@inl byte_seq crypto_error_t (
          temp_653)) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_aes128_encrypt_state : package _ _ _ :=
  (aes128_encrypt_state).
Fail Next Obligation.

Notation "'aes128_encrypt_inp'" :=(
  aead_key_t '× aead_iv_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'aes128_encrypt_out'" :=((
    result crypto_error_t byte_seq) : choice_type) (in custom pack_type at level 2).
Definition AES128_ENCRYPT : nat :=
  (657).
Program Definition aes128_encrypt
  (k_636 : aead_key_t)
  (iv_637 : aead_iv_t)
  (payload_638 : byte_seq)
  (ad_639 : byte_seq)
  :both (fset.fset0) [interface
  #val #[ ENCRYPT_AES128 ] : encrypt_aes128_inp → encrypt_aes128_out ] ((
      result crypto_error_t byte_seq)) :=
  #import {sig #[ ENCRYPT_AES128 ] : encrypt_aes128_inp → encrypt_aes128_out } as encrypt_aes128 ;;
  let encrypt_aes128 := fun x_0 x_1 x_2 x_3 => encrypt_aes128 (
    x_0,x_1,x_2,x_3) in
  letb '(ctxt_640, tag_641) : (seq uint8 '× gf128_tag_t) :=
    encrypt_aes128 (array_from_seq (_) (lift_to_both0 k_636)) (array_from_seq (
        _) (lift_to_both0 iv_637)) (lift_to_both0 ad_639) (
      lift_to_both0 payload_638) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
    @Ok byte_seq crypto_error_t (seq_concat (lift_to_both0 ctxt_640) (
        seq_from_seq (array_to_seq (lift_to_both0 tag_641)))))
  .
Fail Next Obligation.

Definition chacha_encrypt_pure
  (k_658 : aead_key_t)
  (iv_659 : aead_iv_t)
  (payload_660 : byte_seq)
  (ad_661 : byte_seq)
  : (result crypto_error_t byte_seq) :=
  let '(ctxt_662, tag_663) :=
    chacha20_poly1305_encrypt (array_from_seq (32) (k_658)) (array_from_seq (
        12) (iv_659)) (ad_661) (payload_660) : (seq uint8 '× poly1305_tag_t
    ) in 
  @Ok byte_seq crypto_error_t (seq_concat (ctxt_662) (array_to_seq (tag_663))).
Definition chacha_encrypt_pure_code
  (k_658 : aead_key_t)
  (iv_659 : aead_iv_t)
  (payload_660 : byte_seq)
  (ad_661 : byte_seq)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t byte_seq))) :=
  lift_to_code (chacha_encrypt_pure k_658 iv_659 payload_660 ad_661).


Notation "'chacha_encrypt_state_inp'" := (
  aead_key_t '× aead_iv_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'chacha_encrypt_state_out'" := ((
    result crypto_error_t byte_seq) : choice_type) (in custom pack_type at level 2).
Definition CHACHA_ENCRYPT_STATE : nat :=
  (676).
Program Definition chacha_encrypt_state
   : package (fset.fset0) [interface] [interface
  #val #[ CHACHA_ENCRYPT_STATE ] : chacha_encrypt_state_inp → chacha_encrypt_state_out
  ] :=
  (
    [package #def #[ CHACHA_ENCRYPT_STATE ] (temp_inp : chacha_encrypt_state_inp) : chacha_encrypt_state_out { 
    let '(
      k_658 , iv_659 , payload_660 , ad_661) := temp_inp : aead_key_t '× aead_iv_t '× byte_seq '× byte_seq in
    ({ code  temp_675 ←
        ( '(temp_665 : cha_cha_key_t) ←
            (array_from_seq (32) (k_658)) ;;
           '(temp_667 : cha_cha_iv_t) ←
            (array_from_seq (12) (iv_659)) ;;
           temp_669 ←
            (chacha20_poly1305_encrypt (temp_665) (temp_667) (ad_661) (
                payload_660)) ;;
          ret (temp_669)) ;;
      let '(ctxt_662, tag_663) :=
        (temp_675) : (seq uint8 '× poly1305_tag_t) in
       '(temp_671 : seq uint8) ←
        (array_to_seq (tag_663)) ;;
       '(temp_673 : seq uint8) ←
        (seq_concat (ctxt_662) (temp_671)) ;;
      @ret ((result crypto_error_t byte_seq)) (@inl byte_seq crypto_error_t (
          temp_673)) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_chacha_encrypt_state : package _ _ _ :=
  (chacha_encrypt_state).
Fail Next Obligation.

Notation "'chacha_encrypt_inp'" :=(
  aead_key_t '× aead_iv_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'chacha_encrypt_out'" :=((
    result crypto_error_t byte_seq) : choice_type) (in custom pack_type at level 2).
Definition CHACHA_ENCRYPT : nat :=
  (677).
Program Definition chacha_encrypt
  (k_658 : aead_key_t)
  (iv_659 : aead_iv_t)
  (payload_660 : byte_seq)
  (ad_661 : byte_seq)
  :both (fset.fset0) [interface
  #val #[ CHACHA20_POLY1305_ENCRYPT ] : chacha20_poly1305_encrypt_inp → chacha20_poly1305_encrypt_out
  ] ((result crypto_error_t byte_seq)) :=
  #import {sig #[ CHACHA20_POLY1305_ENCRYPT ] : chacha20_poly1305_encrypt_inp → chacha20_poly1305_encrypt_out } as chacha20_poly1305_encrypt ;;
  let chacha20_poly1305_encrypt := fun x_0 x_1 x_2 x_3 => chacha20_poly1305_encrypt (
    x_0,x_1,x_2,x_3) in
  letb '(ctxt_662, tag_663) : (seq uint8 '× poly1305_tag_t) :=
    chacha20_poly1305_encrypt (array_from_seq (32) (lift_to_both0 k_658)) (
      array_from_seq (12) (lift_to_both0 iv_659)) (lift_to_both0 ad_661) (
      lift_to_both0 payload_660) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
    @Ok byte_seq crypto_error_t (seq_concat (lift_to_both0 ctxt_662) (
        array_to_seq (lift_to_both0 tag_663))))
  .
Fail Next Obligation.

Definition aead_encrypt_pure
  (a_678 : aead_algorithm_t)
  (k_679 : aead_key_t)
  (iv_680 : aead_iv_t)
  (payload_681 : byte_seq)
  (ad_682 : byte_seq)
  : (result crypto_error_t byte_seq) :=
  match a_678 with
  | Aes128Gcm => aes128_encrypt (k_679) (iv_680) (payload_681) (ad_682)
  | Aes256Gcm => @Err byte_seq crypto_error_t (UnsupportedAlgorithm)
  | Chacha20Poly1305 => chacha_encrypt (k_679) (iv_680) (payload_681) (ad_682)
  end.
Definition aead_encrypt_pure_code
  (a_678 : aead_algorithm_t)
  (k_679 : aead_key_t)
  (iv_680 : aead_iv_t)
  (payload_681 : byte_seq)
  (ad_682 : byte_seq)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t byte_seq))) :=
  lift_to_code (aead_encrypt_pure a_678 k_679 iv_680 payload_681 ad_682).


Notation "'aead_encrypt_state_inp'" := (
  aead_algorithm_t '× aead_key_t '× aead_iv_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'aead_encrypt_state_out'" := ((
    result crypto_error_t byte_seq) : choice_type) (in custom pack_type at level 2).
Definition AEAD_ENCRYPT_STATE : nat :=
  (689).
Program Definition aead_encrypt_state
   : package (fset.fset0) [interface
  #val #[ AES128_ENCRYPT_STATE ] : aes128_encrypt_state_inp → aes128_encrypt_state_out ;
  #val #[ CHACHA_ENCRYPT_STATE ] : chacha_encrypt_state_inp → chacha_encrypt_state_out
  ] [interface
  #val #[ AEAD_ENCRYPT_STATE ] : aead_encrypt_state_inp → aead_encrypt_state_out
  ] :=
  (
    [package #def #[ AEAD_ENCRYPT_STATE ] (temp_inp : aead_encrypt_state_inp) : aead_encrypt_state_out { 
    let '(
      a_678 , k_679 , iv_680 , payload_681 , ad_682) := temp_inp : aead_algorithm_t '× aead_key_t '× aead_iv_t '× byte_seq '× byte_seq in
    #import {sig #[ AES128_ENCRYPT_STATE ] : aes128_encrypt_state_inp → aes128_encrypt_state_out } as aes128_encrypt_state ;;
    let aes128_encrypt_state := fun x_0 x_1 x_2 x_3 => aes128_encrypt_state (
      x_0,x_1,x_2,x_3) in
    #import {sig #[ CHACHA_ENCRYPT_STATE ] : chacha_encrypt_state_inp → chacha_encrypt_state_out } as chacha_encrypt_state ;;
    let chacha_encrypt_state := fun x_0 x_1 x_2 x_3 => chacha_encrypt_state (
      x_0,x_1,x_2,x_3) in
    ({ code  temp_688 ←
        ((({ code match a_678 with
              | Aes128Gcm => temp_684 ←
                (aes128_encrypt (k_679) (iv_680) (payload_681) (ad_682)) ;;
               ret (temp_684)
              | Aes256Gcm => ret (@inr byte_seq crypto_error_t (
                  UnsupportedAlgorithm))
              | Chacha20Poly1305 => temp_686 ←
                (chacha_encrypt (k_679) (iv_680) (payload_681) (ad_682)) ;;
               ret (temp_686)
              end } : code _ _ _))) ;;
      @ret ((result crypto_error_t byte_seq)) (temp_688) } : code (
        fset.fset0) [interface
      #val #[ AES128_ENCRYPT_STATE ] : aes128_encrypt_state_inp → aes128_encrypt_state_out ;
      #val #[ CHACHA_ENCRYPT_STATE ] : chacha_encrypt_state_inp → chacha_encrypt_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_aead_encrypt_state : package _ _ _ :=
  (seq_link aead_encrypt_state link_rest(
      package_aes128_encrypt_state,package_chacha_encrypt_state)).
Fail Next Obligation.

Notation "'aead_encrypt_inp'" :=(
  aead_algorithm_t '× aead_key_t '× aead_iv_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'aead_encrypt_out'" :=((
    result crypto_error_t byte_seq) : choice_type) (in custom pack_type at level 2).
Definition AEAD_ENCRYPT : nat :=
  (690).
Program Definition aead_encrypt
  (a_678 : aead_algorithm_t)
  (k_679 : aead_key_t)
  (iv_680 : aead_iv_t)
  (payload_681 : byte_seq)
  (ad_682 : byte_seq)
  :both (fset.fset0) [interface
  #val #[ AES128_ENCRYPT ] : aes128_encrypt_inp → aes128_encrypt_out ;
  #val #[ CHACHA_ENCRYPT ] : chacha_encrypt_inp → chacha_encrypt_out ] ((
      result crypto_error_t byte_seq)) :=
  #import {sig #[ AES128_ENCRYPT ] : aes128_encrypt_inp → aes128_encrypt_out } as aes128_encrypt ;;
  let aes128_encrypt := fun x_0 x_1 x_2 x_3 => aes128_encrypt (
    x_0,x_1,x_2,x_3) in
  #import {sig #[ CHACHA_ENCRYPT ] : chacha_encrypt_inp → chacha_encrypt_out } as chacha_encrypt ;;
  let chacha_encrypt := fun x_0 x_1 x_2 x_3 => chacha_encrypt (
    x_0,x_1,x_2,x_3) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) .
Fail Next Obligation.

Definition aes128_decrypt_pure
  (k_691 : aead_key_t)
  (iv_692 : aead_iv_t)
  (ciphertext_693 : byte_seq)
  (ad_694 : byte_seq)
  : (result crypto_error_t byte_seq) :=
  match decrypt_aes128 (array_from_seq (_) (k_691)) (array_from_seq (_) (
      iv_692)) (ad_694) (seq_slice_range (ciphertext_693) (prod_ce(
        usize 0,
        ((seq_len (ciphertext_693)) .- (usize 16))
      ))) (array_from_seq (_) (seq_slice_range (ciphertext_693) (prod_ce(
          ((seq_len (ciphertext_693)) .- (usize 16)),
          seq_len (ciphertext_693)
        )))) with
  | Ok m_695 => @Ok byte_seq crypto_error_t (m_695)
  | Err _ => @Err byte_seq crypto_error_t (MacFailed)
  end.
Definition aes128_decrypt_pure_code
  (k_691 : aead_key_t)
  (iv_692 : aead_iv_t)
  (ciphertext_693 : byte_seq)
  (ad_694 : byte_seq)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t byte_seq))) :=
  lift_to_code (aes128_decrypt_pure k_691 iv_692 ciphertext_693 ad_694).


Notation "'aes128_decrypt_state_inp'" := (
  aead_key_t '× aead_iv_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'aes128_decrypt_state_out'" := ((
    result crypto_error_t byte_seq) : choice_type) (in custom pack_type at level 2).
Definition AES128_DECRYPT_STATE : nat :=
  (720).
Program Definition aes128_decrypt_state
   : package (fset.fset0) [interface] [interface
  #val #[ AES128_DECRYPT_STATE ] : aes128_decrypt_state_inp → aes128_decrypt_state_out
  ] :=
  (
    [package #def #[ AES128_DECRYPT_STATE ] (temp_inp : aes128_decrypt_state_inp) : aes128_decrypt_state_out { 
    let '(
      k_691 , iv_692 , ciphertext_693 , ad_694) := temp_inp : aead_key_t '× aead_iv_t '× byte_seq '× byte_seq in
    ({ code  '(temp_697 : key128_t) ←
        (array_from_seq (_) (k_691)) ;;
       '(temp_699 : aes_nonce_t) ←
        (array_from_seq (_) (iv_692)) ;;
       '(temp_701 : uint_size) ←
        (seq_len (ciphertext_693)) ;;
       '(temp_703 : uint_size) ←
        ((temp_701) .- (usize 16)) ;;
       '(temp_705 : byte_seq) ←
        (seq_slice_range (ciphertext_693) (prod_ce(usize 0, temp_703))) ;;
       '(temp_707 : uint_size) ←
        (seq_len (ciphertext_693)) ;;
       '(temp_709 : uint_size) ←
        ((temp_707) .- (usize 16)) ;;
       '(temp_711 : uint_size) ←
        (seq_len (ciphertext_693)) ;;
       '(temp_713 : byte_seq) ←
        (seq_slice_range (ciphertext_693) (prod_ce(temp_709, temp_711))) ;;
       '(temp_715 : gf128_tag_t) ←
        (array_from_seq (_) (temp_713)) ;;
       temp_717 ←
        (decrypt_aes128 (temp_697) (temp_699) (ad_694) (temp_705) (temp_715)) ;;
       temp_719 ←
        ((({ code match temp_717 with
              | inl m_695 => ret (@inl byte_seq crypto_error_t (m_695))
              | inr _ => ret (@inr byte_seq crypto_error_t (MacFailed))
              end } : code _ _ _))) ;;
      @ret ((result crypto_error_t byte_seq)) (temp_719) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_aes128_decrypt_state : package _ _ _ :=
  (aes128_decrypt_state).
Fail Next Obligation.

Notation "'aes128_decrypt_inp'" :=(
  aead_key_t '× aead_iv_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'aes128_decrypt_out'" :=((
    result crypto_error_t byte_seq) : choice_type) (in custom pack_type at level 2).
Definition AES128_DECRYPT : nat :=
  (721).
Program Definition aes128_decrypt
  (k_691 : aead_key_t)
  (iv_692 : aead_iv_t)
  (ciphertext_693 : byte_seq)
  (ad_694 : byte_seq)
  :both (fset.fset0) [interface
  #val #[ DECRYPT_AES128 ] : decrypt_aes128_inp → decrypt_aes128_out ] ((
      result crypto_error_t byte_seq)) :=
  #import {sig #[ DECRYPT_AES128 ] : decrypt_aes128_inp → decrypt_aes128_out } as decrypt_aes128 ;;
  let decrypt_aes128 := fun x_0 x_1 x_2 x_3 x_4 => decrypt_aes128 (
    x_0,x_1,x_2,x_3,x_4) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) .
Fail Next Obligation.

Definition chacha_decrypt_pure
  (k_722 : aead_key_t)
  (iv_723 : aead_iv_t)
  (ciphertext_724 : byte_seq)
  (ad_725 : byte_seq)
  : (result crypto_error_t byte_seq) :=
  match chacha20_poly1305_decrypt (array_from_seq (32) (k_722)) (
    array_from_seq (12) (iv_723)) (ad_725) (seq_slice_range (ciphertext_724) (
      prod_ce(usize 0, ((seq_len (ciphertext_724)) .- (usize 16))))) (
    array_from_seq (16) (seq_slice_range (ciphertext_724) (prod_ce(
          ((seq_len (ciphertext_724)) .- (usize 16)),
          seq_len (ciphertext_724)
        )))) with
  | Ok ptxt_726 => @Ok byte_seq crypto_error_t (ptxt_726)
  | Err _ => @Err byte_seq crypto_error_t (MacFailed)
  end.
Definition chacha_decrypt_pure_code
  (k_722 : aead_key_t)
  (iv_723 : aead_iv_t)
  (ciphertext_724 : byte_seq)
  (ad_725 : byte_seq)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t byte_seq))) :=
  lift_to_code (chacha_decrypt_pure k_722 iv_723 ciphertext_724 ad_725).


Notation "'chacha_decrypt_state_inp'" := (
  aead_key_t '× aead_iv_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'chacha_decrypt_state_out'" := ((
    result crypto_error_t byte_seq) : choice_type) (in custom pack_type at level 2).
Definition CHACHA_DECRYPT_STATE : nat :=
  (751).
Program Definition chacha_decrypt_state
   : package (fset.fset0) [interface] [interface
  #val #[ CHACHA_DECRYPT_STATE ] : chacha_decrypt_state_inp → chacha_decrypt_state_out
  ] :=
  (
    [package #def #[ CHACHA_DECRYPT_STATE ] (temp_inp : chacha_decrypt_state_inp) : chacha_decrypt_state_out { 
    let '(
      k_722 , iv_723 , ciphertext_724 , ad_725) := temp_inp : aead_key_t '× aead_iv_t '× byte_seq '× byte_seq in
    ({ code  '(temp_728 : cha_cha_key_t) ←
        (array_from_seq (32) (k_722)) ;;
       '(temp_730 : cha_cha_iv_t) ←
        (array_from_seq (12) (iv_723)) ;;
       '(temp_732 : uint_size) ←
        (seq_len (ciphertext_724)) ;;
       '(temp_734 : uint_size) ←
        ((temp_732) .- (usize 16)) ;;
       '(temp_736 : byte_seq) ←
        (seq_slice_range (ciphertext_724) (prod_ce(usize 0, temp_734))) ;;
       '(temp_738 : uint_size) ←
        (seq_len (ciphertext_724)) ;;
       '(temp_740 : uint_size) ←
        ((temp_738) .- (usize 16)) ;;
       '(temp_742 : uint_size) ←
        (seq_len (ciphertext_724)) ;;
       '(temp_744 : byte_seq) ←
        (seq_slice_range (ciphertext_724) (prod_ce(temp_740, temp_742))) ;;
       '(temp_746 : poly1305_tag_t) ←
        (array_from_seq (16) (temp_744)) ;;
       temp_748 ←
        (chacha20_poly1305_decrypt (temp_728) (temp_730) (ad_725) (temp_736) (
            temp_746)) ;;
       temp_750 ←
        ((({ code match temp_748 with
              | inl ptxt_726 => ret (@inl byte_seq crypto_error_t (ptxt_726))
              | inr _ => ret (@inr byte_seq crypto_error_t (MacFailed))
              end } : code _ _ _))) ;;
      @ret ((result crypto_error_t byte_seq)) (temp_750) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_chacha_decrypt_state : package _ _ _ :=
  (chacha_decrypt_state).
Fail Next Obligation.

Notation "'chacha_decrypt_inp'" :=(
  aead_key_t '× aead_iv_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'chacha_decrypt_out'" :=((
    result crypto_error_t byte_seq) : choice_type) (in custom pack_type at level 2).
Definition CHACHA_DECRYPT : nat :=
  (752).
Program Definition chacha_decrypt
  (k_722 : aead_key_t)
  (iv_723 : aead_iv_t)
  (ciphertext_724 : byte_seq)
  (ad_725 : byte_seq)
  :both (fset.fset0) [interface
  #val #[ CHACHA20_POLY1305_DECRYPT ] : chacha20_poly1305_decrypt_inp → chacha20_poly1305_decrypt_out
  ] ((result crypto_error_t byte_seq)) :=
  #import {sig #[ CHACHA20_POLY1305_DECRYPT ] : chacha20_poly1305_decrypt_inp → chacha20_poly1305_decrypt_out } as chacha20_poly1305_decrypt ;;
  let chacha20_poly1305_decrypt := fun x_0 x_1 x_2 x_3 x_4 => chacha20_poly1305_decrypt (
    x_0,x_1,x_2,x_3,x_4) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) .
Fail Next Obligation.

Definition aead_decrypt_pure
  (a_753 : aead_algorithm_t)
  (k_754 : aead_key_t)
  (iv_755 : aead_iv_t)
  (ciphertext_756 : byte_seq)
  (ad_757 : byte_seq)
  : (result crypto_error_t byte_seq) :=
  match a_753 with
  | Aes128Gcm => aes128_decrypt (k_754) (iv_755) (ciphertext_756) (ad_757)
  | Aes256Gcm => @Err byte_seq crypto_error_t (UnsupportedAlgorithm)
  | Chacha20Poly1305 => chacha_decrypt (k_754) (iv_755) (ciphertext_756) (
    ad_757)
  end.
Definition aead_decrypt_pure_code
  (a_753 : aead_algorithm_t)
  (k_754 : aead_key_t)
  (iv_755 : aead_iv_t)
  (ciphertext_756 : byte_seq)
  (ad_757 : byte_seq)
  : code fset.fset0 [interface] (@ct ((result crypto_error_t byte_seq))) :=
  lift_to_code (aead_decrypt_pure a_753 k_754 iv_755 ciphertext_756 ad_757).


Notation "'aead_decrypt_state_inp'" := (
  aead_algorithm_t '× aead_key_t '× aead_iv_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'aead_decrypt_state_out'" := ((
    result crypto_error_t byte_seq) : choice_type) (in custom pack_type at level 2).
Definition AEAD_DECRYPT_STATE : nat :=
  (764).
Program Definition aead_decrypt_state
   : package (fset.fset0) [interface
  #val #[ AES128_DECRYPT_STATE ] : aes128_decrypt_state_inp → aes128_decrypt_state_out ;
  #val #[ CHACHA_DECRYPT_STATE ] : chacha_decrypt_state_inp → chacha_decrypt_state_out
  ] [interface
  #val #[ AEAD_DECRYPT_STATE ] : aead_decrypt_state_inp → aead_decrypt_state_out
  ] :=
  (
    [package #def #[ AEAD_DECRYPT_STATE ] (temp_inp : aead_decrypt_state_inp) : aead_decrypt_state_out { 
    let '(
      a_753 , k_754 , iv_755 , ciphertext_756 , ad_757) := temp_inp : aead_algorithm_t '× aead_key_t '× aead_iv_t '× byte_seq '× byte_seq in
    #import {sig #[ AES128_DECRYPT_STATE ] : aes128_decrypt_state_inp → aes128_decrypt_state_out } as aes128_decrypt_state ;;
    let aes128_decrypt_state := fun x_0 x_1 x_2 x_3 => aes128_decrypt_state (
      x_0,x_1,x_2,x_3) in
    #import {sig #[ CHACHA_DECRYPT_STATE ] : chacha_decrypt_state_inp → chacha_decrypt_state_out } as chacha_decrypt_state ;;
    let chacha_decrypt_state := fun x_0 x_1 x_2 x_3 => chacha_decrypt_state (
      x_0,x_1,x_2,x_3) in
    ({ code  temp_763 ←
        ((({ code match a_753 with
              | Aes128Gcm => temp_759 ←
                (aes128_decrypt (k_754) (iv_755) (ciphertext_756) (ad_757)) ;;
               ret (temp_759)
              | Aes256Gcm => ret (@inr byte_seq crypto_error_t (
                  UnsupportedAlgorithm))
              | Chacha20Poly1305 => temp_761 ←
                (chacha_decrypt (k_754) (iv_755) (ciphertext_756) (ad_757)) ;;
               ret (temp_761)
              end } : code _ _ _))) ;;
      @ret ((result crypto_error_t byte_seq)) (temp_763) } : code (
        fset.fset0) [interface
      #val #[ AES128_DECRYPT_STATE ] : aes128_decrypt_state_inp → aes128_decrypt_state_out ;
      #val #[ CHACHA_DECRYPT_STATE ] : chacha_decrypt_state_inp → chacha_decrypt_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_aead_decrypt_state : package _ _ _ :=
  (seq_link aead_decrypt_state link_rest(
      package_aes128_decrypt_state,package_chacha_decrypt_state)).
Fail Next Obligation.

Notation "'aead_decrypt_inp'" :=(
  aead_algorithm_t '× aead_key_t '× aead_iv_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'aead_decrypt_out'" :=((
    result crypto_error_t byte_seq) : choice_type) (in custom pack_type at level 2).
Definition AEAD_DECRYPT : nat :=
  (765).
Program Definition aead_decrypt
  (a_753 : aead_algorithm_t)
  (k_754 : aead_key_t)
  (iv_755 : aead_iv_t)
  (ciphertext_756 : byte_seq)
  (ad_757 : byte_seq)
  :both (fset.fset0) [interface
  #val #[ AES128_DECRYPT ] : aes128_decrypt_inp → aes128_decrypt_out ;
  #val #[ CHACHA_DECRYPT ] : chacha_decrypt_inp → chacha_decrypt_out ] ((
      result crypto_error_t byte_seq)) :=
  #import {sig #[ AES128_DECRYPT ] : aes128_decrypt_inp → aes128_decrypt_out } as aes128_decrypt ;;
  let aes128_decrypt := fun x_0 x_1 x_2 x_3 => aes128_decrypt (
    x_0,x_1,x_2,x_3) in
  #import {sig #[ CHACHA_DECRYPT ] : chacha_decrypt_inp → chacha_decrypt_out } as chacha_decrypt ;;
  let chacha_decrypt := fun x_0 x_1 x_2 x_3 => chacha_decrypt (
    x_0,x_1,x_2,x_3) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) .
Fail Next Obligation.

