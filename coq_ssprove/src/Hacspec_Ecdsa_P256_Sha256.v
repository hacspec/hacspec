(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From CoqWord Require Import ssrZ word.
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
Require Import Hacspec_Lib.

Require Import Hacspec_P256.

Require Import Hacspec_Sha256.

Definition error_t : ChoiceEquality :=
  (unit_ChoiceEquality '+ unit_ChoiceEquality).
Definition InvalidScalar : error_t :=
  (inl tt).
Definition InvalidSignature : error_t :=
  (inr tt).

Notation "'p256_public_key_t'" := (affine_t) : hacspec_scope.

Notation "'p256_secret_key_t'" := (p256_scalar_t) : hacspec_scope.

Notation "'p256_signature_t'" := ((p256_scalar_t '× p256_scalar_t
)) : hacspec_scope.

Notation "'p256_signature_result_t'" := ((
  result error_t p256_signature_t)) : hacspec_scope.

Notation "'p256_verify_result_t'" := ((
  result error_t unit_ChoiceEquality)) : hacspec_scope.

Notation "'check_result_t'" := ((
  result error_t unit_ChoiceEquality)) : hacspec_scope.

Notation "'arithmetic_result_t'" := ((result error_t affine_t)) : hacspec_scope.


Notation "'check_scalar_zero_inp'" := (
  p256_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'check_scalar_zero_out'" := (
  check_result_t : choice_type) (in custom pack_type at level 2).
Definition CHECK_SCALAR_ZERO : nat :=
  (5).
Program Definition check_scalar_zero
   : package (fset.fset0) [interface] [interface
  #val #[ CHECK_SCALAR_ZERO ] : check_scalar_zero_inp → check_scalar_zero_out
  ] :=
  (
    [package #def #[ CHECK_SCALAR_ZERO ] (temp_inp : check_scalar_zero_inp) : check_scalar_zero_out { 
    let '(r_0) := temp_inp : p256_scalar_t in
    ({ code  '(temp_2 : p256_scalar_t) ←
        (nat_mod_zero ) ;;
       temp_4 ←
        (nat_mod_equal (r_0) (temp_2)) ;;
      @ret ((result error_t unit_ChoiceEquality)) ((if (
            temp_4):bool_ChoiceEquality then (*inline*) (
            @inr unit_ChoiceEquality error_t (InvalidScalar)) else (
            @inl unit_ChoiceEquality error_t (tt)))) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_check_scalar_zero : package _ _ _ :=
  (check_scalar_zero).
Fail Next Obligation.


Notation "'ecdsa_point_mul_base_inp'" := (
  p256_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'ecdsa_point_mul_base_out'" := (
  arithmetic_result_t : choice_type) (in custom pack_type at level 2).
Definition ECDSA_POINT_MUL_BASE : nat :=
  (10).
Program Definition ecdsa_point_mul_base
   : package (fset.fset0) [interface
  #val #[ P256_POINT_MUL_BASE ] : p256_point_mul_base_inp → p256_point_mul_base_out
  ] [interface
  #val #[ ECDSA_POINT_MUL_BASE ] : ecdsa_point_mul_base_inp → ecdsa_point_mul_base_out
  ] :=
  (
    [package #def #[ ECDSA_POINT_MUL_BASE ] (temp_inp : ecdsa_point_mul_base_inp) : ecdsa_point_mul_base_out { 
    let '(x_6) := temp_inp : p256_scalar_t in
    #import {sig #[ P256_POINT_MUL_BASE ] : p256_point_mul_base_inp → p256_point_mul_base_out } as p256_point_mul_base ;;
    let p256_point_mul_base := fun x_0 => p256_point_mul_base (x_0) in
    ({ code  temp_8 ←
        (p256_point_mul_base (x_6)) ;;
      @ret ((result error_t affine_t)) (match temp_8 with
        | inl s_9 => @inl affine_t error_t (s_9)
        | inr _ => @inr affine_t error_t (InvalidScalar)
        end) } : code (fset.fset0) [interface
      #val #[ P256_POINT_MUL_BASE ] : p256_point_mul_base_inp → p256_point_mul_base_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_ecdsa_point_mul_base : package _ _ _ :=
  (seq_link ecdsa_point_mul_base link_rest(package_p256_point_mul_base)).
Fail Next Obligation.


Notation "'ecdsa_point_mul_inp'" := (
  p256_scalar_t '× affine_t : choice_type) (in custom pack_type at level 2).
Notation "'ecdsa_point_mul_out'" := (
  arithmetic_result_t : choice_type) (in custom pack_type at level 2).
Definition ECDSA_POINT_MUL : nat :=
  (16).
Program Definition ecdsa_point_mul
   : package (fset.fset0) [interface
  #val #[ P256_POINT_MUL ] : p256_point_mul_inp → p256_point_mul_out
  ] [interface
  #val #[ ECDSA_POINT_MUL ] : ecdsa_point_mul_inp → ecdsa_point_mul_out ] :=
  (
    [package #def #[ ECDSA_POINT_MUL ] (temp_inp : ecdsa_point_mul_inp) : ecdsa_point_mul_out { 
    let '(k_11 , p_12) := temp_inp : p256_scalar_t '× affine_t in
    #import {sig #[ P256_POINT_MUL ] : p256_point_mul_inp → p256_point_mul_out } as p256_point_mul ;;
    let p256_point_mul := fun x_0 x_1 => p256_point_mul (x_0,x_1) in
    ({ code  temp_14 ←
        (p256_point_mul (k_11) (p_12)) ;;
      @ret ((result error_t affine_t)) (match temp_14 with
        | inl s_15 => @inl affine_t error_t (s_15)
        | inr _ => @inr affine_t error_t (InvalidScalar)
        end) } : code (fset.fset0) [interface
      #val #[ P256_POINT_MUL ] : p256_point_mul_inp → p256_point_mul_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_ecdsa_point_mul : package _ _ _ :=
  (seq_link ecdsa_point_mul link_rest(package_p256_point_mul)).
Fail Next Obligation.


Notation "'ecdsa_point_add_inp'" := (
  affine_t '× affine_t : choice_type) (in custom pack_type at level 2).
Notation "'ecdsa_point_add_out'" := (
  arithmetic_result_t : choice_type) (in custom pack_type at level 2).
Definition ECDSA_POINT_ADD : nat :=
  (22).
Program Definition ecdsa_point_add
   : package (fset.fset0) [interface
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ] [interface
  #val #[ ECDSA_POINT_ADD ] : ecdsa_point_add_inp → ecdsa_point_add_out ] :=
  (
    [package #def #[ ECDSA_POINT_ADD ] (temp_inp : ecdsa_point_add_inp) : ecdsa_point_add_out { 
    let '(p_17 , q_18) := temp_inp : affine_t '× affine_t in
    #import {sig #[ POINT_ADD ] : point_add_inp → point_add_out } as point_add ;;
    let point_add := fun x_0 x_1 => point_add (x_0,x_1) in
    ({ code  temp_20 ←
        (point_add (p_17) (q_18)) ;;
      @ret ((result error_t affine_t)) (match temp_20 with
        | inl s_21 => @inl affine_t error_t (s_21)
        | inr _ => @inr affine_t error_t (InvalidScalar)
        end) } : code (fset.fset0) [interface
      #val #[ POINT_ADD ] : point_add_inp → point_add_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_ecdsa_point_add : package _ _ _ :=
  (seq_link ecdsa_point_add link_rest(package_point_add)).
Fail Next Obligation.


Notation "'sign_inp'" := (
  byte_seq '× p256_secret_key_t '× p256_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'sign_out'" := (
  p256_signature_result_t : choice_type) (in custom pack_type at level 2).
Definition SIGN : nat :=
  (59).
Program Definition sign
   : package (fset.fset0) [interface
  #val #[ CHECK_SCALAR_ZERO ] : check_scalar_zero_inp → check_scalar_zero_out ;
  #val #[ ECDSA_POINT_MUL_BASE ] : ecdsa_point_mul_base_inp → ecdsa_point_mul_base_out ;
  #val #[ HASH ] : hash_inp → hash_out ] [interface
  #val #[ SIGN ] : sign_inp → sign_out ] :=
  ([package #def #[ SIGN ] (temp_inp : sign_inp) : sign_out { 
    let '(
      payload_36 , sk_44 , nonce_23) := temp_inp : byte_seq '× p256_secret_key_t '× p256_scalar_t in
    #import {sig #[ CHECK_SCALAR_ZERO ] : check_scalar_zero_inp → check_scalar_zero_out } as check_scalar_zero ;;
    let check_scalar_zero := fun x_0 => check_scalar_zero (x_0) in
    #import {sig #[ ECDSA_POINT_MUL_BASE ] : ecdsa_point_mul_base_inp → ecdsa_point_mul_base_out } as ecdsa_point_mul_base ;;
    let ecdsa_point_mul_base := fun x_0 => ecdsa_point_mul_base (x_0) in
    #import {sig #[ HASH ] : hash_inp → hash_out } as hash ;;
    let hash := fun x_0 => hash (x_0) in
    ({ code bnd(
        ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , fset.fset0) _ ⇠
      (({ code  '(temp_25 : check_result_t) ←
            (check_scalar_zero (nonce_23)) ;;
          @ret _ (temp_25) } : code (fset.fset0) [interface
          #val #[ CHECK_SCALAR_ZERO ] : check_scalar_zero_inp → check_scalar_zero_out
          ] _)) in
      ({ code bnd(
          ChoiceEqualityMonad.result_bind_code error_t , affine_t , _ , fset.fset0) '(
          k_x_28,
          k_y_58
        ) ⇠
        (({ code  '(temp_27 : arithmetic_result_t) ←
              (ecdsa_point_mul_base (nonce_23)) ;;
            @ret _ (temp_27) } : code (fset.fset0) [interface
            #val #[ ECDSA_POINT_MUL_BASE ] : ecdsa_point_mul_base_inp → ecdsa_point_mul_base_out
            ] _)) in
        ({ code  '(r_33 : p256_scalar_t) ←
            ( '(temp_30 : seq int8) ←
                (nat_mod_to_byte_seq_be (k_x_28)) ;;
               '(temp_32 : p256_scalar_t) ←
                (nat_mod_from_byte_seq_be (temp_30)) ;;
              ret (temp_32)) ;;
          bnd(
            ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , fset.fset0) _ ⇠
          (({ code  '(temp_35 : check_result_t) ←
                (check_scalar_zero (r_33)) ;;
              @ret _ (temp_35) } : code (fset.fset0) [interface
              #val #[ CHECK_SCALAR_ZERO ] : check_scalar_zero_inp → check_scalar_zero_out
              ] _)) in
          ({ code  '(payload_hash_39 : sha256_digest_t) ←
              ( temp_38 ←
                  (hash (payload_36)) ;;
                ret (temp_38)) ;;
             '(payload_hash_47 : p256_scalar_t) ←
              ( '(temp_41 : seq uint8) ←
                  (array_to_seq (payload_hash_39)) ;;
                 '(temp_43 : p256_scalar_t) ←
                  (nat_mod_from_byte_seq_be (temp_41)) ;;
                ret (temp_43)) ;;
             '(rsk_48 : p256_scalar_t) ←
              ( '(temp_46 : p256_scalar_t) ←
                  ((r_33) *% (sk_44)) ;;
                ret (temp_46)) ;;
             '(hash_rsk_54 : p256_scalar_t) ←
              ( '(temp_50 : p256_scalar_t) ←
                  ((payload_hash_47) +% (rsk_48)) ;;
                ret (temp_50)) ;;
             '(nonce_inv_53 : p256_scalar_t) ←
              ( temp_52 ←
                  (nat_mod_inv (nonce_23)) ;;
                ret (temp_52)) ;;
             '(s_57 : p256_scalar_t) ←
              ( '(temp_56 : p256_scalar_t) ←
                  ((nonce_inv_53) *% (hash_rsk_54)) ;;
                ret (temp_56)) ;;
            @ret ((result error_t p256_signature_t)) (
              @inl p256_signature_t error_t (prod_ce(r_33, s_57))) } : code (
              fset.fset0) [interface
            #val #[ CHECK_SCALAR_ZERO ] : check_scalar_zero_inp → check_scalar_zero_out ;
            #val #[ ECDSA_POINT_MUL_BASE ] : ecdsa_point_mul_base_inp → ecdsa_point_mul_base_out ;
            #val #[ HASH ] : hash_inp → hash_out ] _) } : code (
            fset.fset0) [interface
          #val #[ CHECK_SCALAR_ZERO ] : check_scalar_zero_inp → check_scalar_zero_out ;
          #val #[ ECDSA_POINT_MUL_BASE ] : ecdsa_point_mul_base_inp → ecdsa_point_mul_base_out ;
          #val #[ HASH ] : hash_inp → hash_out ] _) } : code (
          fset.fset0) [interface
        #val #[ CHECK_SCALAR_ZERO ] : check_scalar_zero_inp → check_scalar_zero_out ;
        #val #[ ECDSA_POINT_MUL_BASE ] : ecdsa_point_mul_base_inp → ecdsa_point_mul_base_out ;
        #val #[ HASH ] : hash_inp → hash_out ] _) } : code (
        fset.fset0) [interface
      #val #[ CHECK_SCALAR_ZERO ] : check_scalar_zero_inp → check_scalar_zero_out ;
      #val #[ ECDSA_POINT_MUL_BASE ] : ecdsa_point_mul_base_inp → ecdsa_point_mul_base_out ;
      #val #[ HASH ] : hash_inp → hash_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_sign : package _ _ _ :=
  (seq_link sign link_rest(
      package_check_scalar_zero,package_ecdsa_point_mul_base,package_hash)).
Fail Next Obligation.


Notation "'ecdsa_p256_sha256_sign_inp'" := (
  byte_seq '× p256_secret_key_t '× p256_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'ecdsa_p256_sha256_sign_out'" := (
  p256_signature_result_t : choice_type) (in custom pack_type at level 2).
Definition ECDSA_P256_SHA256_SIGN : nat :=
  (65).
Program Definition ecdsa_p256_sha256_sign
   : package (fset.fset0) [interface #val #[ SIGN ] : sign_inp → sign_out
  ] [interface
  #val #[ ECDSA_P256_SHA256_SIGN ] : ecdsa_p256_sha256_sign_inp → ecdsa_p256_sha256_sign_out
  ] :=
  (
    [package #def #[ ECDSA_P256_SHA256_SIGN ] (temp_inp : ecdsa_p256_sha256_sign_inp) : ecdsa_p256_sha256_sign_out { 
    let '(
      payload_60 , sk_61 , nonce_62) := temp_inp : byte_seq '× p256_secret_key_t '× p256_scalar_t in
    #import {sig #[ SIGN ] : sign_inp → sign_out } as sign ;;
    let sign := fun x_0 x_1 x_2 => sign (x_0,x_1,x_2) in
    ({ code  '(temp_64 : p256_signature_result_t) ←
        (sign (payload_60) (sk_61) (nonce_62)) ;;
      @ret (p256_signature_result_t) (temp_64) } : code (fset.fset0) [interface
      #val #[ SIGN ] : sign_inp → sign_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_ecdsa_p256_sha256_sign : package _ _ _ :=
  (seq_link ecdsa_p256_sha256_sign link_rest(package_sign)).
Fail Next Obligation.


Notation "'verify_inp'" := (
  byte_seq '× p256_public_key_t '× p256_signature_t : choice_type) (in custom pack_type at level 2).
Notation "'verify_out'" := (
  p256_verify_result_t : choice_type) (in custom pack_type at level 2).
Definition VERIFY : nat :=
  (107).
Program Definition verify
   : package (fset.fset0) [interface
  #val #[ ECDSA_POINT_ADD ] : ecdsa_point_add_inp → ecdsa_point_add_out ;
  #val #[ ECDSA_POINT_MUL ] : ecdsa_point_mul_inp → ecdsa_point_mul_out ;
  #val #[ ECDSA_POINT_MUL_BASE ] : ecdsa_point_mul_base_inp → ecdsa_point_mul_base_out ;
  #val #[ HASH ] : hash_inp → hash_out ] [interface
  #val #[ VERIFY ] : verify_inp → verify_out ] :=
  ([package #def #[ VERIFY ] (temp_inp : verify_inp) : verify_out { 
    let '(
      payload_67 , pk_89 , signature_66) := temp_inp : byte_seq '× p256_public_key_t '× p256_signature_t in
    #import {sig #[ ECDSA_POINT_ADD ] : ecdsa_point_add_inp → ecdsa_point_add_out } as ecdsa_point_add ;;
    let ecdsa_point_add := fun x_0 x_1 => ecdsa_point_add (x_0,x_1) in
    #import {sig #[ ECDSA_POINT_MUL ] : ecdsa_point_mul_inp → ecdsa_point_mul_out } as ecdsa_point_mul ;;
    let ecdsa_point_mul := fun x_0 x_1 => ecdsa_point_mul (x_0,x_1) in
    #import {sig #[ ECDSA_POINT_MUL_BASE ] : ecdsa_point_mul_base_inp → ecdsa_point_mul_base_out } as ecdsa_point_mul_base ;;
    let ecdsa_point_mul_base := fun x_0 => ecdsa_point_mul_base (x_0) in
    #import {sig #[ HASH ] : hash_inp → hash_out } as hash ;;
    let hash := fun x_0 => hash (x_0) in
    ({ code  temp_106 ←
        (ret (signature_66)) ;;
      let '(r_85, s_75) :=
        (temp_106) : (p256_scalar_t '× p256_scalar_t) in
       '(payload_hash_70 : sha256_digest_t) ←
        ( temp_69 ←
            (hash (payload_67)) ;;
          ret (temp_69)) ;;
       '(payload_hash_78 : p256_scalar_t) ←
        ( '(temp_72 : seq uint8) ←
            (array_to_seq (payload_hash_70)) ;;
           '(temp_74 : p256_scalar_t) ←
            (nat_mod_from_byte_seq_be (temp_72)) ;;
          ret (temp_74)) ;;
       '(s_inv_79 : p256_scalar_t) ←
        ( temp_77 ←
            (nat_mod_inv (s_75)) ;;
          ret (temp_77)) ;;
       '(u1_82 : p256_scalar_t) ←
        ( '(temp_81 : p256_scalar_t) ←
            ((payload_hash_78) *% (s_inv_79)) ;;
          ret (temp_81)) ;;
      bnd(
        ChoiceEqualityMonad.result_bind_code error_t , affine_t , _ , fset.fset0) u1_92 ⇠
      (({ code  '(temp_84 : arithmetic_result_t) ←
            (ecdsa_point_mul_base (u1_82)) ;;
          @ret _ (temp_84) } : code (fset.fset0) [interface
          #val #[ ECDSA_POINT_MUL_BASE ] : ecdsa_point_mul_base_inp → ecdsa_point_mul_base_out
          ] _)) in
      ({ code  '(u2_88 : p256_scalar_t) ←
          ( '(temp_87 : p256_scalar_t) ←
              ((r_85) *% (s_inv_79)) ;;
            ret (temp_87)) ;;
        bnd(
          ChoiceEqualityMonad.result_bind_code error_t , affine_t , _ , fset.fset0) u2_93 ⇠
        (({ code  '(temp_91 : arithmetic_result_t) ←
              (ecdsa_point_mul (u2_88) (pk_89)) ;;
            @ret _ (temp_91) } : code (fset.fset0) [interface
            #val #[ ECDSA_POINT_MUL ] : ecdsa_point_mul_inp → ecdsa_point_mul_out
            ] _)) in
        ({ code bnd(
            ChoiceEqualityMonad.result_bind_code error_t , affine_t , _ , fset.fset0) '(
            x_96,
            y_104
          ) ⇠
          (({ code  '(temp_95 : arithmetic_result_t) ←
                (ecdsa_point_add (u1_92) (u2_93)) ;;
              @ret _ (temp_95) } : code (fset.fset0) [interface
              #val #[ ECDSA_POINT_ADD ] : ecdsa_point_add_inp → ecdsa_point_add_out
              ] _)) in
          ({ code  '(x_101 : p256_scalar_t) ←
              ( '(temp_98 : seq int8) ←
                  (nat_mod_to_byte_seq_be (x_96)) ;;
                 '(temp_100 : p256_scalar_t) ←
                  (nat_mod_from_byte_seq_be (temp_98)) ;;
                ret (temp_100)) ;;
             '(temp_103 : bool_ChoiceEquality) ←
              ((x_101) =.? (r_85)) ;;
            @ret ((result error_t unit_ChoiceEquality)) ((if (
                  temp_103):bool_ChoiceEquality then (*inline*) (
                  @inl unit_ChoiceEquality error_t (tt)) else (
                  @inr unit_ChoiceEquality error_t (
                    InvalidSignature)))) } : code (fset.fset0) [interface
            #val #[ ECDSA_POINT_ADD ] : ecdsa_point_add_inp → ecdsa_point_add_out ;
            #val #[ ECDSA_POINT_MUL ] : ecdsa_point_mul_inp → ecdsa_point_mul_out ;
            #val #[ ECDSA_POINT_MUL_BASE ] : ecdsa_point_mul_base_inp → ecdsa_point_mul_base_out ;
            #val #[ HASH ] : hash_inp → hash_out ] _) } : code (
            fset.fset0) [interface
          #val #[ ECDSA_POINT_ADD ] : ecdsa_point_add_inp → ecdsa_point_add_out ;
          #val #[ ECDSA_POINT_MUL ] : ecdsa_point_mul_inp → ecdsa_point_mul_out ;
          #val #[ ECDSA_POINT_MUL_BASE ] : ecdsa_point_mul_base_inp → ecdsa_point_mul_base_out ;
          #val #[ HASH ] : hash_inp → hash_out ] _) } : code (
          fset.fset0) [interface
        #val #[ ECDSA_POINT_ADD ] : ecdsa_point_add_inp → ecdsa_point_add_out ;
        #val #[ ECDSA_POINT_MUL ] : ecdsa_point_mul_inp → ecdsa_point_mul_out ;
        #val #[ ECDSA_POINT_MUL_BASE ] : ecdsa_point_mul_base_inp → ecdsa_point_mul_base_out ;
        #val #[ HASH ] : hash_inp → hash_out ] _) } : code (
        fset.fset0) [interface
      #val #[ ECDSA_POINT_ADD ] : ecdsa_point_add_inp → ecdsa_point_add_out ;
      #val #[ ECDSA_POINT_MUL ] : ecdsa_point_mul_inp → ecdsa_point_mul_out ;
      #val #[ ECDSA_POINT_MUL_BASE ] : ecdsa_point_mul_base_inp → ecdsa_point_mul_base_out ;
      #val #[ HASH ] : hash_inp → hash_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_verify : package _ _ _ :=
  (seq_link verify link_rest(
      package_ecdsa_point_add,package_ecdsa_point_mul,package_ecdsa_point_mul_base,package_hash)).
Fail Next Obligation.


Notation "'ecdsa_p256_sha256_verify_inp'" := (
  byte_seq '× p256_public_key_t '× p256_signature_t : choice_type) (in custom pack_type at level 2).
Notation "'ecdsa_p256_sha256_verify_out'" := (
  p256_verify_result_t : choice_type) (in custom pack_type at level 2).
Definition ECDSA_P256_SHA256_VERIFY : nat :=
  (113).
Program Definition ecdsa_p256_sha256_verify
   : package (fset.fset0) [interface
  #val #[ VERIFY ] : verify_inp → verify_out ] [interface
  #val #[ ECDSA_P256_SHA256_VERIFY ] : ecdsa_p256_sha256_verify_inp → ecdsa_p256_sha256_verify_out
  ] :=
  (
    [package #def #[ ECDSA_P256_SHA256_VERIFY ] (temp_inp : ecdsa_p256_sha256_verify_inp) : ecdsa_p256_sha256_verify_out { 
    let '(
      payload_108 , pk_109 , signature_110) := temp_inp : byte_seq '× p256_public_key_t '× p256_signature_t in
    #import {sig #[ VERIFY ] : verify_inp → verify_out } as verify ;;
    let verify := fun x_0 x_1 x_2 => verify (x_0,x_1,x_2) in
    ({ code  '(temp_112 : p256_verify_result_t) ←
        (verify (payload_108) (pk_109) (signature_110)) ;;
      @ret (p256_verify_result_t) (temp_112) } : code (fset.fset0) [interface
      #val #[ VERIFY ] : verify_inp → verify_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_ecdsa_p256_sha256_verify : package _ _ _ :=
  (seq_link ecdsa_p256_sha256_verify link_rest(package_verify)).
Fail Next Obligation.

