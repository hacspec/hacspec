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
Require Import Hacspec_Lib.

Require Import Hacspec_Sha512.

Require Import Hacspec_Edwards25519.


Notation "'scalar_from_hash_inp'" := (
  sha512_digest_t : choice_type) (in custom pack_type at level 2).
Notation "'scalar_from_hash_out'" := (
  scalar_t : choice_type) (in custom pack_type at level 2).
Definition SCALAR_FROM_HASH : nat :=
  (11492).
Program Definition scalar_from_hash
   : package (fset.fset0) [interface] [interface
  #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out
  ] :=
  (
    [package #def #[ SCALAR_FROM_HASH ] (temp_inp : scalar_from_hash_inp) : scalar_from_hash_out { 
    let '(h_11480) := temp_inp : sha512_digest_t in
    ({ code  '(s_11485 : big_scalar_t) ←
        ( '(temp_11482 : seq uint8) ←
            (array_to_seq (h_11480)) ;;
           '(temp_11484 : big_scalar_t) ←
            (nat_mod_from_byte_seq_le (temp_11482)) ;;
          ret (temp_11484)) ;;
       temp_11487 ←
        (nat_mod_to_byte_seq_le (s_11485)) ;;
       '(temp_11489 : seq uint8) ←
        (seq_slice (temp_11487) (usize 0) (usize 32)) ;;
       '(temp_11491 : scalar_t) ←
        (nat_mod_from_byte_seq_le (temp_11489)) ;;
      @ret (scalar_t) (temp_11491) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_scalar_from_hash : package _ _ _ :=
  (scalar_from_hash).
Fail Next Obligation.


Notation "'sign_inp'" := (
  secret_key_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sign_out'" := (
  signature_t : choice_type) (in custom pack_type at level 2).
Definition SIGN : nat :=
  (11558).
Program Definition sign
   : package (fset.fset0) [interface
  #val #[ COMPRESS ] : compress_inp → compress_out ;
  #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
  #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
  #val #[ SECRET_EXPAND ] : secret_expand_inp → secret_expand_out ;
  #val #[ SHA512 ] : sha512_inp → sha512_out ] [interface
  #val #[ SIGN ] : sign_inp → sign_out ] :=
  ([package #def #[ SIGN ] (temp_inp : sign_inp) : sign_out { 
    let '(sk_11493 , msg_11512) := temp_inp : secret_key_t '× byte_seq in
    #import {sig #[ COMPRESS ] : compress_inp → compress_out } as compress ;;
    let compress := fun x_0 => compress (x_0) in
    #import {sig #[ DECOMPRESS ] : decompress_inp → decompress_out } as decompress ;;
    let decompress := fun x_0 => decompress (x_0) in
    #import {sig #[ POINT_MUL ] : point_mul_inp → point_mul_out } as point_mul ;;
    let point_mul := fun x_0 x_1 => point_mul (x_0,x_1) in
    #import {sig #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out } as scalar_from_hash ;;
    let scalar_from_hash := fun x_0 => scalar_from_hash (x_0) in
    #import {sig #[ SECRET_EXPAND ] : secret_expand_inp → secret_expand_out } as secret_expand ;;
    let secret_expand := fun x_0 => secret_expand (x_0) in
    #import {sig #[ SHA512 ] : sha512_inp → sha512_out } as sha512 ;;
    let sha512 := fun x_0 => sha512 (x_0) in
    ({ code  temp_11557 ←
        ( temp_11495 ←
            (secret_expand (sk_11493)) ;;
          ret (temp_11495)) ;;
      let '(a_11496, prefix_11511) :=
        (temp_11557) : (serialized_scalar_t '× serialized_scalar_t) in
       '(a_11505 : scalar_t) ←
        ( '(temp_11498 : seq uint8) ←
            (array_to_seq (a_11496)) ;;
           '(temp_11500 : scalar_t) ←
            (nat_mod_from_byte_seq_le (temp_11498)) ;;
          ret (temp_11500)) ;;
       '(b_11506 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          )) ←
        ( temp_11502 ←
            (decompress (base_v)) ;;
           temp_11504 ←
            (option_unwrap (temp_11502)) ;;
          ret (temp_11504)) ;;
       '(a_p_11526 : compressed_ed_point_t) ←
        ( temp_11508 ←
            (point_mul (a_11505) (b_11506)) ;;
           temp_11510 ←
            (compress (temp_11508)) ;;
          ret (temp_11510)) ;;
       '(r_11519 : scalar_t) ←
        ( '(temp_11514 : seq uint8) ←
            (array_concat (prefix_11511) (msg_11512)) ;;
           temp_11516 ←
            (sha512 (temp_11514)) ;;
           '(temp_11518 : scalar_t) ←
            (scalar_from_hash (temp_11516)) ;;
          ret (temp_11518)) ;;
       '(r_p_11522 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          )) ←
        ( temp_11521 ←
            (point_mul (r_11519) (b_11506)) ;;
          ret (temp_11521)) ;;
       '(r_s_11525 : compressed_ed_point_t) ←
        ( temp_11524 ←
            (compress (r_p_11522)) ;;
          ret (temp_11524)) ;;
       '(h_11537 : scalar_t) ←
        ( '(temp_11528 : seq uint8) ←
            (array_to_seq (a_p_11526)) ;;
           '(temp_11530 : seq uint8) ←
            (array_concat (r_s_11525) (temp_11528)) ;;
           '(temp_11532 : seq uint8) ←
            (seq_concat (temp_11530) (msg_11512)) ;;
           temp_11534 ←
            (sha512 (temp_11532)) ;;
           '(temp_11536 : scalar_t) ←
            (scalar_from_hash (temp_11534)) ;;
          ret (temp_11536)) ;;
       '(s_11542 : scalar_t) ←
        ( '(temp_11539 : scalar_t) ←
            ((h_11537) *% (a_11505)) ;;
           '(temp_11541 : scalar_t) ←
            ((r_11519) +% (temp_11539)) ;;
          ret (temp_11541)) ;;
       '(s_bytes_11553 : seq uint8) ←
        ( temp_11544 ←
            (nat_mod_to_byte_seq_le (s_11542)) ;;
           '(temp_11546 : seq uint8) ←
            (seq_slice (temp_11544) (usize 0) (usize 32)) ;;
          ret (temp_11546)) ;;
       '(temp_11548 : signature_t) ←
        (array_new_ (default : uint8) (64)) ;;
       '(temp_11550 : seq uint8) ←
        (array_to_seq (r_s_11525)) ;;
       '(temp_11552 : signature_t) ←
        (array_update (temp_11548) (usize 0) (temp_11550)) ;;
       '(temp_11555 : signature_t) ←
        (array_update (temp_11552) (usize 32) (s_bytes_11553)) ;;
      @ret (signature_t) (temp_11555) } : code (fset.fset0) [interface
      #val #[ COMPRESS ] : compress_inp → compress_out ;
      #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
      #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
      #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
      #val #[ SECRET_EXPAND ] : secret_expand_inp → secret_expand_out ;
      #val #[ SHA512 ] : sha512_inp → sha512_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_sign : package _ _ _ :=
  (seq_link sign link_rest(
      package_compress,package_decompress,package_point_mul,package_scalar_from_hash,package_secret_expand,package_sha512)).
Fail Next Obligation.


Notation "'zcash_verify_inp'" := (
  public_key_t '× signature_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'zcash_verify_out'" := (
  verify_result_t : choice_type) (in custom pack_type at level 2).
Definition ZCASH_VERIFY : nat :=
  (11620).
Program Definition zcash_verify
   : package (fset.fset0) [interface
  #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
  #val #[ DECOMPRESS_NON_CANONICAL ] : decompress_non_canonical_inp → decompress_non_canonical_out ;
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
  #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
  #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
  #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
  #val #[ SHA512 ] : sha512_inp → sha512_out ] [interface
  #val #[ ZCASH_VERIFY ] : zcash_verify_inp → zcash_verify_out ] :=
  (
    [package #def #[ ZCASH_VERIFY ] (temp_inp : zcash_verify_inp) : zcash_verify_out { 
    let '(
      pk_11563 , signature_11568 , msg_11591) := temp_inp : public_key_t '× signature_t '× byte_seq in
    #import {sig #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out } as check_canonical_scalar ;;
    let check_canonical_scalar := fun x_0 => check_canonical_scalar (x_0) in
    #import {sig #[ DECOMPRESS_NON_CANONICAL ] : decompress_non_canonical_inp → decompress_non_canonical_out } as decompress_non_canonical ;;
    let decompress_non_canonical := fun x_0 => decompress_non_canonical (x_0) in
    #import {sig #[ POINT_ADD ] : point_add_inp → point_add_out } as point_add ;;
    let point_add := fun x_0 x_1 => point_add (x_0,x_1) in
    #import {sig #[ POINT_EQ ] : point_eq_inp → point_eq_out } as point_eq ;;
    let point_eq := fun x_0 x_1 => point_eq (x_0,x_1) in
    #import {sig #[ POINT_MUL ] : point_mul_inp → point_mul_out } as point_mul ;;
    let point_mul := fun x_0 x_1 => point_mul (x_0,x_1) in
    #import {sig #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out } as point_mul_by_cofactor ;;
    let point_mul_by_cofactor := fun x_0 => point_mul_by_cofactor (x_0) in
    #import {sig #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out } as scalar_from_hash ;;
    let scalar_from_hash := fun x_0 => scalar_from_hash (x_0) in
    #import {sig #[ SHA512 ] : sha512_inp → sha512_out } as sha512 ;;
    let sha512 := fun x_0 => sha512 (x_0) in
    ({ code  '(b_11599 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          )) ←
        ( temp_11560 ←
            (decompress_non_canonical (base_v)) ;;
           temp_11562 ←
            (option_unwrap (temp_11560)) ;;
          ret (temp_11562)) ;;
      bnd(ChoiceEqualityMonad.result_bind_code error_t , (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) , _ , fset.fset0) a_11608 ⇠
      (({ code  temp_11565 ←
            (decompress_non_canonical (pk_11563)) ;;
           temp_11567 ←
            (option_ok_or (temp_11565) (InvalidPublickey)) ;;
          @ret _ (temp_11567) } : code (fset.fset0) [interface
          #val #[ DECOMPRESS_NON_CANONICAL ] : decompress_non_canonical_inp → decompress_non_canonical_out
          ] _)) in
      ({ code  '(r_bytes_11580 : compressed_ed_point_t) ←
          ( '(temp_11570 : seq uint8) ←
              (array_to_seq (signature_11568)) ;;
             '(temp_11572 : compressed_ed_point_t) ←
              (array_from_slice (default : uint8) (32) (temp_11570) (usize 0) (
                  usize 32)) ;;
            ret (temp_11572)) ;;
         '(s_bytes_11577 : serialized_scalar_t) ←
          ( '(temp_11574 : seq uint8) ←
              (array_to_seq (signature_11568)) ;;
             '(temp_11576 : serialized_scalar_t) ←
              (array_from_slice (default : uint8) (32) (temp_11574) (usize 32) (
                  usize 32)) ;;
            ret (temp_11576)) ;;
         temp_11579 ←
          (check_canonical_scalar (s_bytes_11577)) ;;
        bnd(
          ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , fset.fset0) 'tt ⇠
        (if negb (temp_11579) : bool_ChoiceEquality
          then (*state*) (({ code bnd(
                ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , fset.fset0) _ ⇠
              (({ code @ret _ (@inr unit_ChoiceEquality error_t (
                      InvalidS)) } : code (fset.fset0) [interface] _)) in
              ({ code @ret ((result error_t unit_ChoiceEquality)) (
                  @inl unit_ChoiceEquality error_t (
                    (tt : unit_ChoiceEquality))) } : code (
                  fset.fset0) [interface] _) } : code (
                fset.fset0) [interface] _))
          else ({ code @ret ((result error_t unit_ChoiceEquality)) (
              @inl unit_ChoiceEquality error_t (
                (tt : unit_ChoiceEquality))) } : code _ _ _) ) in
        ({ code bnd(ChoiceEqualityMonad.result_bind_code error_t , (
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t
            ) , _ , fset.fset0) r_11604 ⇠
          (({ code  temp_11582 ←
                (decompress_non_canonical (r_bytes_11580)) ;;
               temp_11584 ←
                (option_ok_or (temp_11582) (InvalidR)) ;;
              @ret _ (temp_11584) } : code (fset.fset0) [interface
              #val #[ DECOMPRESS_NON_CANONICAL ] : decompress_non_canonical_inp → decompress_non_canonical_out
              ] _)) in
          ({ code  '(s_11598 : scalar_t) ←
              ( '(temp_11586 : seq uint8) ←
                  (array_to_seq (s_bytes_11577)) ;;
                 '(temp_11588 : scalar_t) ←
                  (nat_mod_from_byte_seq_le (temp_11586)) ;;
                ret (temp_11588)) ;;
             '(k_11607 : scalar_t) ←
              ( '(temp_11590 : seq uint8) ←
                  (array_concat (r_bytes_11580) (pk_11563)) ;;
                 '(temp_11593 : seq uint8) ←
                  (seq_concat (temp_11590) (msg_11591)) ;;
                 temp_11595 ←
                  (sha512 (temp_11593)) ;;
                 '(temp_11597 : scalar_t) ←
                  (scalar_from_hash (temp_11595)) ;;
                ret (temp_11597)) ;;
             '(sb_11613 : (
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t
                )) ←
              ( temp_11601 ←
                  (point_mul (s_11598) (b_11599)) ;;
                 temp_11603 ←
                  (point_mul_by_cofactor (temp_11601)) ;;
                ret (temp_11603)) ;;
             '(rc_11614 : (
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t
                )) ←
              ( temp_11606 ←
                  (point_mul_by_cofactor (r_11604)) ;;
                ret (temp_11606)) ;;
             '(ka_11615 : (
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t
                )) ←
              ( temp_11610 ←
                  (point_mul (k_11607) (a_11608)) ;;
                 temp_11612 ←
                  (point_mul_by_cofactor (temp_11610)) ;;
                ret (temp_11612)) ;;
             temp_11617 ←
              (point_add (rc_11614) (ka_11615)) ;;
             temp_11619 ←
              (point_eq (sb_11613) (temp_11617)) ;;
            @ret ((result error_t unit_ChoiceEquality)) ((if (
                  temp_11619):bool_ChoiceEquality then (*inline*) (
                  @inl unit_ChoiceEquality error_t (tt)) else (
                  @inr unit_ChoiceEquality error_t (
                    InvalidSignature)))) } : code (fset.fset0) [interface
            #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
            #val #[ DECOMPRESS_NON_CANONICAL ] : decompress_non_canonical_inp → decompress_non_canonical_out ;
            #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
            #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
            #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
            #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
            #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
            #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
            fset.fset0) [interface
          #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
          #val #[ DECOMPRESS_NON_CANONICAL ] : decompress_non_canonical_inp → decompress_non_canonical_out ;
          #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
          #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
          #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
          #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
          #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
          #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
          fset.fset0) [interface
        #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
        #val #[ DECOMPRESS_NON_CANONICAL ] : decompress_non_canonical_inp → decompress_non_canonical_out ;
        #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
        #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
        #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
        #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
        #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
        #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
        fset.fset0) [interface
      #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
      #val #[ DECOMPRESS_NON_CANONICAL ] : decompress_non_canonical_inp → decompress_non_canonical_out ;
      #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
      #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
      #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
      #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
      #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
      #val #[ SHA512 ] : sha512_inp → sha512_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_zcash_verify : package _ _ _ :=
  (seq_link zcash_verify link_rest(
      package_check_canonical_scalar,package_decompress_non_canonical,package_point_add,package_point_eq,package_point_mul,package_point_mul_by_cofactor,package_scalar_from_hash,package_sha512)).
Fail Next Obligation.


Notation "'ietf_cofactored_verify_inp'" := (
  public_key_t '× signature_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactored_verify_out'" := (
  verify_result_t : choice_type) (in custom pack_type at level 2).
Definition IETF_COFACTORED_VERIFY : nat :=
  (11682).
Program Definition ietf_cofactored_verify
   : package (fset.fset0) [interface
  #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
  #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
  #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
  #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
  #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
  #val #[ SHA512 ] : sha512_inp → sha512_out ] [interface
  #val #[ IETF_COFACTORED_VERIFY ] : ietf_cofactored_verify_inp → ietf_cofactored_verify_out
  ] :=
  (
    [package #def #[ IETF_COFACTORED_VERIFY ] (temp_inp : ietf_cofactored_verify_inp) : ietf_cofactored_verify_out { 
    let '(
      pk_11625 , signature_11630 , msg_11653) := temp_inp : public_key_t '× signature_t '× byte_seq in
    #import {sig #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out } as check_canonical_scalar ;;
    let check_canonical_scalar := fun x_0 => check_canonical_scalar (x_0) in
    #import {sig #[ DECOMPRESS ] : decompress_inp → decompress_out } as decompress ;;
    let decompress := fun x_0 => decompress (x_0) in
    #import {sig #[ POINT_ADD ] : point_add_inp → point_add_out } as point_add ;;
    let point_add := fun x_0 x_1 => point_add (x_0,x_1) in
    #import {sig #[ POINT_EQ ] : point_eq_inp → point_eq_out } as point_eq ;;
    let point_eq := fun x_0 x_1 => point_eq (x_0,x_1) in
    #import {sig #[ POINT_MUL ] : point_mul_inp → point_mul_out } as point_mul ;;
    let point_mul := fun x_0 x_1 => point_mul (x_0,x_1) in
    #import {sig #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out } as point_mul_by_cofactor ;;
    let point_mul_by_cofactor := fun x_0 => point_mul_by_cofactor (x_0) in
    #import {sig #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out } as scalar_from_hash ;;
    let scalar_from_hash := fun x_0 => scalar_from_hash (x_0) in
    #import {sig #[ SHA512 ] : sha512_inp → sha512_out } as sha512 ;;
    let sha512 := fun x_0 => sha512 (x_0) in
    ({ code  '(b_11661 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          )) ←
        ( temp_11622 ←
            (decompress (base_v)) ;;
           temp_11624 ←
            (option_unwrap (temp_11622)) ;;
          ret (temp_11624)) ;;
      bnd(ChoiceEqualityMonad.result_bind_code error_t , (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) , _ , fset.fset0) a_11670 ⇠
      (({ code  temp_11627 ←
            (decompress (pk_11625)) ;;
           temp_11629 ←
            (option_ok_or (temp_11627) (InvalidPublickey)) ;;
          @ret _ (temp_11629) } : code (fset.fset0) [interface
          #val #[ DECOMPRESS ] : decompress_inp → decompress_out ] _)) in
      ({ code  '(r_bytes_11642 : compressed_ed_point_t) ←
          ( '(temp_11632 : seq uint8) ←
              (array_to_seq (signature_11630)) ;;
             '(temp_11634 : compressed_ed_point_t) ←
              (array_from_slice (default : uint8) (32) (temp_11632) (usize 0) (
                  usize 32)) ;;
            ret (temp_11634)) ;;
         '(s_bytes_11639 : serialized_scalar_t) ←
          ( '(temp_11636 : seq uint8) ←
              (array_to_seq (signature_11630)) ;;
             '(temp_11638 : serialized_scalar_t) ←
              (array_from_slice (default : uint8) (32) (temp_11636) (usize 32) (
                  usize 32)) ;;
            ret (temp_11638)) ;;
         temp_11641 ←
          (check_canonical_scalar (s_bytes_11639)) ;;
        bnd(
          ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , fset.fset0) 'tt ⇠
        (if negb (temp_11641) : bool_ChoiceEquality
          then (*state*) (({ code bnd(
                ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , fset.fset0) _ ⇠
              (({ code @ret _ (@inr unit_ChoiceEquality error_t (
                      InvalidS)) } : code (fset.fset0) [interface] _)) in
              ({ code @ret ((result error_t unit_ChoiceEquality)) (
                  @inl unit_ChoiceEquality error_t (
                    (tt : unit_ChoiceEquality))) } : code (
                  fset.fset0) [interface] _) } : code (
                fset.fset0) [interface] _))
          else ({ code @ret ((result error_t unit_ChoiceEquality)) (
              @inl unit_ChoiceEquality error_t (
                (tt : unit_ChoiceEquality))) } : code _ _ _) ) in
        ({ code bnd(ChoiceEqualityMonad.result_bind_code error_t , (
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t
            ) , _ , fset.fset0) r_11666 ⇠
          (({ code  temp_11644 ←
                (decompress (r_bytes_11642)) ;;
               temp_11646 ←
                (option_ok_or (temp_11644) (InvalidR)) ;;
              @ret _ (temp_11646) } : code (fset.fset0) [interface
              #val #[ DECOMPRESS ] : decompress_inp → decompress_out ] _)) in
          ({ code  '(s_11660 : scalar_t) ←
              ( '(temp_11648 : seq uint8) ←
                  (array_to_seq (s_bytes_11639)) ;;
                 '(temp_11650 : scalar_t) ←
                  (nat_mod_from_byte_seq_le (temp_11648)) ;;
                ret (temp_11650)) ;;
             '(k_11669 : scalar_t) ←
              ( '(temp_11652 : seq uint8) ←
                  (array_concat (r_bytes_11642) (pk_11625)) ;;
                 '(temp_11655 : seq uint8) ←
                  (seq_concat (temp_11652) (msg_11653)) ;;
                 temp_11657 ←
                  (sha512 (temp_11655)) ;;
                 '(temp_11659 : scalar_t) ←
                  (scalar_from_hash (temp_11657)) ;;
                ret (temp_11659)) ;;
             '(sb_11675 : (
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t
                )) ←
              ( temp_11663 ←
                  (point_mul (s_11660) (b_11661)) ;;
                 temp_11665 ←
                  (point_mul_by_cofactor (temp_11663)) ;;
                ret (temp_11665)) ;;
             '(rc_11676 : (
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t
                )) ←
              ( temp_11668 ←
                  (point_mul_by_cofactor (r_11666)) ;;
                ret (temp_11668)) ;;
             '(ka_11677 : (
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t
                )) ←
              ( temp_11672 ←
                  (point_mul (k_11669) (a_11670)) ;;
                 temp_11674 ←
                  (point_mul_by_cofactor (temp_11672)) ;;
                ret (temp_11674)) ;;
             temp_11679 ←
              (point_add (rc_11676) (ka_11677)) ;;
             temp_11681 ←
              (point_eq (sb_11675) (temp_11679)) ;;
            @ret ((result error_t unit_ChoiceEquality)) ((if (
                  temp_11681):bool_ChoiceEquality then (*inline*) (
                  @inl unit_ChoiceEquality error_t (tt)) else (
                  @inr unit_ChoiceEquality error_t (
                    InvalidSignature)))) } : code (fset.fset0) [interface
            #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
            #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
            #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
            #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
            #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
            #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
            #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
            #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
            fset.fset0) [interface
          #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
          #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
          #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
          #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
          #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
          #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
          #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
          #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
          fset.fset0) [interface
        #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
        #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
        #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
        #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
        #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
        #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
        #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
        #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
        fset.fset0) [interface
      #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
      #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
      #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
      #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
      #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
      #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
      #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
      #val #[ SHA512 ] : sha512_inp → sha512_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_ietf_cofactored_verify : package _ _ _ :=
  (seq_link ietf_cofactored_verify link_rest(
      package_check_canonical_scalar,package_decompress,package_point_add,package_point_eq,package_point_mul,package_point_mul_by_cofactor,package_scalar_from_hash,package_sha512)).
Fail Next Obligation.


Notation "'ietf_cofactorless_verify_inp'" := (
  public_key_t '× signature_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactorless_verify_out'" := (
  verify_result_t : choice_type) (in custom pack_type at level 2).
Definition IETF_COFACTORLESS_VERIFY : nat :=
  (11737).
Program Definition ietf_cofactorless_verify
   : package (fset.fset0) [interface
  #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
  #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
  #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
  #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
  #val #[ SHA512 ] : sha512_inp → sha512_out ] [interface
  #val #[ IETF_COFACTORLESS_VERIFY ] : ietf_cofactorless_verify_inp → ietf_cofactorless_verify_out
  ] :=
  (
    [package #def #[ IETF_COFACTORLESS_VERIFY ] (temp_inp : ietf_cofactorless_verify_inp) : ietf_cofactorless_verify_out { 
    let '(
      pk_11687 , signature_11692 , msg_11715) := temp_inp : public_key_t '× signature_t '× byte_seq in
    #import {sig #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out } as check_canonical_scalar ;;
    let check_canonical_scalar := fun x_0 => check_canonical_scalar (x_0) in
    #import {sig #[ DECOMPRESS ] : decompress_inp → decompress_out } as decompress ;;
    let decompress := fun x_0 => decompress (x_0) in
    #import {sig #[ POINT_ADD ] : point_add_inp → point_add_out } as point_add ;;
    let point_add := fun x_0 x_1 => point_add (x_0,x_1) in
    #import {sig #[ POINT_EQ ] : point_eq_inp → point_eq_out } as point_eq ;;
    let point_eq := fun x_0 x_1 => point_eq (x_0,x_1) in
    #import {sig #[ POINT_MUL ] : point_mul_inp → point_mul_out } as point_mul ;;
    let point_mul := fun x_0 x_1 => point_mul (x_0,x_1) in
    #import {sig #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out } as scalar_from_hash ;;
    let scalar_from_hash := fun x_0 => scalar_from_hash (x_0) in
    #import {sig #[ SHA512 ] : sha512_inp → sha512_out } as sha512 ;;
    let sha512 := fun x_0 => sha512 (x_0) in
    ({ code  '(b_11723 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          )) ←
        ( temp_11684 ←
            (decompress (base_v)) ;;
           temp_11686 ←
            (option_unwrap (temp_11684)) ;;
          ret (temp_11686)) ;;
      bnd(ChoiceEqualityMonad.result_bind_code error_t , (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) , _ , fset.fset0) a_11727 ⇠
      (({ code  temp_11689 ←
            (decompress (pk_11687)) ;;
           temp_11691 ←
            (option_ok_or (temp_11689) (InvalidPublickey)) ;;
          @ret _ (temp_11691) } : code (fset.fset0) [interface
          #val #[ DECOMPRESS ] : decompress_inp → decompress_out ] _)) in
      ({ code  '(r_bytes_11704 : compressed_ed_point_t) ←
          ( '(temp_11694 : seq uint8) ←
              (array_to_seq (signature_11692)) ;;
             '(temp_11696 : compressed_ed_point_t) ←
              (array_from_slice (default : uint8) (32) (temp_11694) (usize 0) (
                  usize 32)) ;;
            ret (temp_11696)) ;;
         '(s_bytes_11701 : serialized_scalar_t) ←
          ( '(temp_11698 : seq uint8) ←
              (array_to_seq (signature_11692)) ;;
             '(temp_11700 : serialized_scalar_t) ←
              (array_from_slice (default : uint8) (32) (temp_11698) (usize 32) (
                  usize 32)) ;;
            ret (temp_11700)) ;;
         temp_11703 ←
          (check_canonical_scalar (s_bytes_11701)) ;;
        bnd(
          ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , fset.fset0) 'tt ⇠
        (if negb (temp_11703) : bool_ChoiceEquality
          then (*state*) (({ code bnd(
                ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , fset.fset0) _ ⇠
              (({ code @ret _ (@inr unit_ChoiceEquality error_t (
                      InvalidS)) } : code (fset.fset0) [interface] _)) in
              ({ code @ret ((result error_t unit_ChoiceEquality)) (
                  @inl unit_ChoiceEquality error_t (
                    (tt : unit_ChoiceEquality))) } : code (
                  fset.fset0) [interface] _) } : code (
                fset.fset0) [interface] _))
          else ({ code @ret ((result error_t unit_ChoiceEquality)) (
              @inl unit_ChoiceEquality error_t (
                (tt : unit_ChoiceEquality))) } : code _ _ _) ) in
        ({ code bnd(ChoiceEqualityMonad.result_bind_code error_t , (
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t
            ) , _ , fset.fset0) r_11731 ⇠
          (({ code  temp_11706 ←
                (decompress (r_bytes_11704)) ;;
               temp_11708 ←
                (option_ok_or (temp_11706) (InvalidR)) ;;
              @ret _ (temp_11708) } : code (fset.fset0) [interface
              #val #[ DECOMPRESS ] : decompress_inp → decompress_out ] _)) in
          ({ code  '(s_11722 : scalar_t) ←
              ( '(temp_11710 : seq uint8) ←
                  (array_to_seq (s_bytes_11701)) ;;
                 '(temp_11712 : scalar_t) ←
                  (nat_mod_from_byte_seq_le (temp_11710)) ;;
                ret (temp_11712)) ;;
             '(k_11726 : scalar_t) ←
              ( '(temp_11714 : seq uint8) ←
                  (array_concat (r_bytes_11704) (pk_11687)) ;;
                 '(temp_11717 : seq uint8) ←
                  (seq_concat (temp_11714) (msg_11715)) ;;
                 temp_11719 ←
                  (sha512 (temp_11717)) ;;
                 '(temp_11721 : scalar_t) ←
                  (scalar_from_hash (temp_11719)) ;;
                ret (temp_11721)) ;;
             '(sb_11730 : (
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t
                )) ←
              ( temp_11725 ←
                  (point_mul (s_11722) (b_11723)) ;;
                ret (temp_11725)) ;;
             '(ka_11732 : (
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t '×
                  ed25519_field_element_t
                )) ←
              ( temp_11729 ←
                  (point_mul (k_11726) (a_11727)) ;;
                ret (temp_11729)) ;;
             temp_11734 ←
              (point_add (r_11731) (ka_11732)) ;;
             temp_11736 ←
              (point_eq (sb_11730) (temp_11734)) ;;
            @ret ((result error_t unit_ChoiceEquality)) ((if (
                  temp_11736):bool_ChoiceEquality then (*inline*) (
                  @inl unit_ChoiceEquality error_t (tt)) else (
                  @inr unit_ChoiceEquality error_t (
                    InvalidSignature)))) } : code (fset.fset0) [interface
            #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
            #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
            #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
            #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
            #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
            #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
            #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
            fset.fset0) [interface
          #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
          #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
          #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
          #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
          #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
          #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
          #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
          fset.fset0) [interface
        #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
        #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
        #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
        #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
        #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
        #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
        #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
        fset.fset0) [interface
      #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
      #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
      #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
      #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
      #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
      #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
      #val #[ SHA512 ] : sha512_inp → sha512_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_ietf_cofactorless_verify : package _ _ _ :=
  (seq_link ietf_cofactorless_verify link_rest(
      package_check_canonical_scalar,package_decompress,package_point_add,package_point_eq,package_point_mul,package_scalar_from_hash,package_sha512)).
Fail Next Obligation.


Notation "'is_identity_inp'" := (
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'is_identity_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition IS_IDENTITY : nat :=
  (11743).
Program Definition is_identity
   : package (fset.fset0) [interface
  #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
  #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out
  ] [interface #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ] :=
  (
    [package #def #[ IS_IDENTITY ] (temp_inp : is_identity_inp) : is_identity_out { 
    let '(p_11738) := temp_inp : ed_point_t in
    #import {sig #[ POINT_EQ ] : point_eq_inp → point_eq_out } as point_eq ;;
    let point_eq := fun x_0 x_1 => point_eq (x_0,x_1) in
    #import {sig #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out } as point_identity ;;
    let point_identity := point_identity tt in
    ({ code  temp_11740 ←
        (point_identity ) ;;
       temp_11742 ←
        (point_eq (p_11738) (temp_11740)) ;;
      @ret (bool_ChoiceEquality) (temp_11742) } : code (fset.fset0) [interface
      #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
      #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_is_identity : package _ _ _ :=
  (seq_link is_identity link_rest(package_point_eq,package_point_identity)).
Fail Next Obligation.


Notation "'alg2_verify_inp'" := (
  public_key_t '× signature_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'alg2_verify_out'" := (
  verify_result_t : choice_type) (in custom pack_type at level 2).
Definition ALG2_VERIFY : nat :=
  (11809).
Program Definition alg2_verify
   : package (fset.fset0) [interface
  #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
  #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
  #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
  #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
  #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
  #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
  #val #[ SHA512 ] : sha512_inp → sha512_out ] [interface
  #val #[ ALG2_VERIFY ] : alg2_verify_inp → alg2_verify_out ] :=
  (
    [package #def #[ ALG2_VERIFY ] (temp_inp : alg2_verify_inp) : alg2_verify_out { 
    let '(
      pk_11748 , signature_11758 , msg_11781) := temp_inp : public_key_t '× signature_t '× byte_seq in
    #import {sig #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out } as check_canonical_scalar ;;
    let check_canonical_scalar := fun x_0 => check_canonical_scalar (x_0) in
    #import {sig #[ DECOMPRESS ] : decompress_inp → decompress_out } as decompress ;;
    let decompress := fun x_0 => decompress (x_0) in
    #import {sig #[ IS_IDENTITY ] : is_identity_inp → is_identity_out } as is_identity ;;
    let is_identity := fun x_0 => is_identity (x_0) in
    #import {sig #[ POINT_ADD ] : point_add_inp → point_add_out } as point_add ;;
    let point_add := fun x_0 x_1 => point_add (x_0,x_1) in
    #import {sig #[ POINT_EQ ] : point_eq_inp → point_eq_out } as point_eq ;;
    let point_eq := fun x_0 x_1 => point_eq (x_0,x_1) in
    #import {sig #[ POINT_MUL ] : point_mul_inp → point_mul_out } as point_mul ;;
    let point_mul := fun x_0 x_1 => point_mul (x_0,x_1) in
    #import {sig #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out } as point_mul_by_cofactor ;;
    let point_mul_by_cofactor := fun x_0 => point_mul_by_cofactor (x_0) in
    #import {sig #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out } as scalar_from_hash ;;
    let scalar_from_hash := fun x_0 => scalar_from_hash (x_0) in
    #import {sig #[ SHA512 ] : sha512_inp → sha512_out } as sha512 ;;
    let sha512 := fun x_0 => sha512 (x_0) in
    ({ code  '(b_11789 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          )) ←
        ( temp_11745 ←
            (decompress (base_v)) ;;
           temp_11747 ←
            (option_unwrap (temp_11745)) ;;
          ret (temp_11747)) ;;
      bnd(ChoiceEqualityMonad.result_bind_code error_t , (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) , _ , fset.fset0) a_11753 ⇠
      (({ code  temp_11750 ←
            (decompress (pk_11748)) ;;
           temp_11752 ←
            (option_ok_or (temp_11750) (InvalidPublickey)) ;;
          @ret _ (temp_11752) } : code (fset.fset0) [interface
          #val #[ DECOMPRESS ] : decompress_inp → decompress_out ] _)) in
      ({ code  temp_11755 ←
          (point_mul_by_cofactor (a_11753)) ;;
         '(temp_11757 : bool_ChoiceEquality) ←
          (is_identity (temp_11755)) ;;
        bnd(
          ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , fset.fset0) 'tt ⇠
        (if temp_11757 : bool_ChoiceEquality
          then (*state*) (({ code bnd(
                ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , fset.fset0) _ ⇠
              (({ code @ret _ (@inr unit_ChoiceEquality error_t (
                      SmallOrderPoint)) } : code (fset.fset0) [interface] _)) in
              ({ code @ret ((result error_t unit_ChoiceEquality)) (
                  @inl unit_ChoiceEquality error_t (
                    (tt : unit_ChoiceEquality))) } : code (
                  fset.fset0) [interface] _) } : code (
                fset.fset0) [interface] _))
          else ({ code @ret ((result error_t unit_ChoiceEquality)) (
              @inl unit_ChoiceEquality error_t (
                (tt : unit_ChoiceEquality))) } : code _ _ _) ) in
        ({ code  '(r_bytes_11770 : compressed_ed_point_t) ←
            ( '(temp_11760 : seq uint8) ←
                (array_to_seq (signature_11758)) ;;
               '(temp_11762 : compressed_ed_point_t) ←
                (array_from_slice (default : uint8) (32) (temp_11760) (
                    usize 0) (usize 32)) ;;
              ret (temp_11762)) ;;
           '(s_bytes_11767 : serialized_scalar_t) ←
            ( '(temp_11764 : seq uint8) ←
                (array_to_seq (signature_11758)) ;;
               '(temp_11766 : serialized_scalar_t) ←
                (array_from_slice (default : uint8) (32) (temp_11764) (
                    usize 32) (usize 32)) ;;
              ret (temp_11766)) ;;
           temp_11769 ←
            (check_canonical_scalar (s_bytes_11767)) ;;
          bnd(
            ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , fset.fset0) 'tt ⇠
          (if negb (temp_11769) : bool_ChoiceEquality
            then (*state*) (({ code bnd(
                  ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , fset.fset0) _ ⇠
                (({ code @ret _ (@inr unit_ChoiceEquality error_t (
                        InvalidS)) } : code (fset.fset0) [interface] _)) in
                ({ code @ret ((result error_t unit_ChoiceEquality)) (
                    @inl unit_ChoiceEquality error_t (
                      (tt : unit_ChoiceEquality))) } : code (
                    fset.fset0) [interface] _) } : code (
                  fset.fset0) [interface] _))
            else ({ code @ret ((result error_t unit_ChoiceEquality)) (
                @inl unit_ChoiceEquality error_t (
                  (tt : unit_ChoiceEquality))) } : code _ _ _) ) in
          ({ code bnd(ChoiceEqualityMonad.result_bind_code error_t , (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) , _ , fset.fset0) r_11794 ⇠
            (({ code  temp_11772 ←
                  (decompress (r_bytes_11770)) ;;
                 temp_11774 ←
                  (option_ok_or (temp_11772) (InvalidR)) ;;
                @ret _ (temp_11774) } : code (fset.fset0) [interface
                #val #[ DECOMPRESS ] : decompress_inp → decompress_out
                ] _)) in
            ({ code  '(s_11788 : scalar_t) ←
                ( '(temp_11776 : seq uint8) ←
                    (array_to_seq (s_bytes_11767)) ;;
                   '(temp_11778 : scalar_t) ←
                    (nat_mod_from_byte_seq_le (temp_11776)) ;;
                  ret (temp_11778)) ;;
               '(k_11797 : scalar_t) ←
                ( '(temp_11780 : seq uint8) ←
                    (array_concat (r_bytes_11770) (pk_11748)) ;;
                   '(temp_11783 : seq uint8) ←
                    (seq_concat (temp_11780) (msg_11781)) ;;
                   temp_11785 ←
                    (sha512 (temp_11783)) ;;
                   '(temp_11787 : scalar_t) ←
                    (scalar_from_hash (temp_11785)) ;;
                  ret (temp_11787)) ;;
               '(sb_11802 : (
                    ed25519_field_element_t '×
                    ed25519_field_element_t '×
                    ed25519_field_element_t '×
                    ed25519_field_element_t
                  )) ←
                ( temp_11791 ←
                    (point_mul (s_11788) (b_11789)) ;;
                   temp_11793 ←
                    (point_mul_by_cofactor (temp_11791)) ;;
                  ret (temp_11793)) ;;
               '(rc_11803 : (
                    ed25519_field_element_t '×
                    ed25519_field_element_t '×
                    ed25519_field_element_t '×
                    ed25519_field_element_t
                  )) ←
                ( temp_11796 ←
                    (point_mul_by_cofactor (r_11794)) ;;
                  ret (temp_11796)) ;;
               '(ka_11804 : (
                    ed25519_field_element_t '×
                    ed25519_field_element_t '×
                    ed25519_field_element_t '×
                    ed25519_field_element_t
                  )) ←
                ( temp_11799 ←
                    (point_mul (k_11797) (a_11753)) ;;
                   temp_11801 ←
                    (point_mul_by_cofactor (temp_11799)) ;;
                  ret (temp_11801)) ;;
               temp_11806 ←
                (point_add (rc_11803) (ka_11804)) ;;
               temp_11808 ←
                (point_eq (sb_11802) (temp_11806)) ;;
              @ret ((result error_t unit_ChoiceEquality)) ((if (
                    temp_11808):bool_ChoiceEquality then (*inline*) (
                    @inl unit_ChoiceEquality error_t (tt)) else (
                    @inr unit_ChoiceEquality error_t (
                      InvalidSignature)))) } : code (fset.fset0) [interface
              #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
              #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
              #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
              #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
              #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
              #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
              #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
              #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
              #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
              fset.fset0) [interface
            #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
            #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
            #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
            #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
            #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
            #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
            #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
            #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
            #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
            fset.fset0) [interface
          #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
          #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
          #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
          #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
          #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
          #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
          #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
          #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
          #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
          fset.fset0) [interface
        #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
        #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
        #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
        #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
        #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
        #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
        #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
        #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
        #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
        fset.fset0) [interface
      #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
      #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
      #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
      #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
      #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
      #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
      #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
      #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
      #val #[ SHA512 ] : sha512_inp → sha512_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_alg2_verify : package _ _ _ :=
  (seq_link alg2_verify link_rest(
      package_check_canonical_scalar,package_decompress,package_is_identity,package_point_add,package_point_eq,package_point_mul,package_point_mul_by_cofactor,package_scalar_from_hash,package_sha512)).
Fail Next Obligation.

Definition batch_entry_t : ChoiceEquality :=
  ((public_key_t '× byte_seq '× signature_t)).
Definition BatchEntry (x : (public_key_t '× byte_seq '× signature_t
    )) : batch_entry_t :=
  ( x).

Definition a_sum_11850_loc : ChoiceEqualityLocation :=
  (((
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) ; 11920%nat)).
Definition s_sum_11848_loc : ChoiceEqualityLocation :=
  ((scalar_t ; 11921%nat)).
Definition r_sum_11849_loc : ChoiceEqualityLocation :=
  (((
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) ; 11922%nat)).
Notation "'zcash_batch_verify_inp'" := (
  seq batch_entry_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'zcash_batch_verify_out'" := (
  verify_result_t : choice_type) (in custom pack_type at level 2).
Definition ZCASH_BATCH_VERIFY : nat :=
  (11923).
Program Definition zcash_batch_verify
   : package (CEfset (
      [s_sum_11848_loc ; r_sum_11849_loc ; a_sum_11850_loc])) [interface
  #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
  #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
  #val #[ DECOMPRESS_NON_CANONICAL ] : decompress_non_canonical_inp → decompress_non_canonical_out ;
  #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
  #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ;
  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
  #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
  #val #[ POINT_NEG ] : point_neg_inp → point_neg_out ;
  #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
  #val #[ SHA512 ] : sha512_inp → sha512_out ] [interface
  #val #[ ZCASH_BATCH_VERIFY ] : zcash_batch_verify_inp → zcash_batch_verify_out
  ] :=
  (
    [package #def #[ ZCASH_BATCH_VERIFY ] (temp_inp : zcash_batch_verify_inp) : zcash_batch_verify_out { 
    let '(
      entries_11813 , entropy_11810) := temp_inp : seq batch_entry_t '× byte_seq in
    #import {sig #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out } as check_canonical_scalar ;;
    let check_canonical_scalar := fun x_0 => check_canonical_scalar (x_0) in
    #import {sig #[ DECOMPRESS ] : decompress_inp → decompress_out } as decompress ;;
    let decompress := fun x_0 => decompress (x_0) in
    #import {sig #[ DECOMPRESS_NON_CANONICAL ] : decompress_non_canonical_inp → decompress_non_canonical_out } as decompress_non_canonical ;;
    let decompress_non_canonical := fun x_0 => decompress_non_canonical (x_0) in
    #import {sig #[ IS_IDENTITY ] : is_identity_inp → is_identity_out } as is_identity ;;
    let is_identity := fun x_0 => is_identity (x_0) in
    #import {sig #[ POINT_ADD ] : point_add_inp → point_add_out } as point_add ;;
    let point_add := fun x_0 x_1 => point_add (x_0,x_1) in
    #import {sig #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out } as point_identity ;;
    let point_identity := point_identity tt in
    #import {sig #[ POINT_MUL ] : point_mul_inp → point_mul_out } as point_mul ;;
    let point_mul := fun x_0 x_1 => point_mul (x_0,x_1) in
    #import {sig #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out } as point_mul_by_cofactor ;;
    let point_mul_by_cofactor := fun x_0 => point_mul_by_cofactor (x_0) in
    #import {sig #[ POINT_NEG ] : point_neg_inp → point_neg_out } as point_neg ;;
    let point_neg := fun x_0 => point_neg (x_0) in
    #import {sig #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out } as scalar_from_hash ;;
    let scalar_from_hash := fun x_0 => scalar_from_hash (x_0) in
    #import {sig #[ SHA512 ] : sha512_inp → sha512_out } as sha512 ;;
    let sha512 := fun x_0 => sha512 (x_0) in
    ({ code  '(temp_11812 : uint_size) ←
        (seq_len (entropy_11810)) ;;
       '(temp_11815 : uint_size) ←
        (seq_len (entries_11813)) ;;
       '(temp_11817 : uint_size) ←
        ((usize 16) .* (temp_11815)) ;;
       '(temp_11819 : bool_ChoiceEquality) ←
        ((temp_11812) <.? (temp_11817)) ;;
      bnd(
        ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , CEfset (
          [s_sum_11848_loc ; r_sum_11849_loc ; a_sum_11850_loc])) 'tt ⇠
      (if temp_11819 : bool_ChoiceEquality
        then (*state*) (({ code bnd(
              ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , fset.fset0) _ ⇠
            (({ code @ret _ (@inr unit_ChoiceEquality error_t (
                    NotEnoughRandomness)) } : code (
                  fset.fset0) [interface] _)) in
            ({ code @ret ((result error_t unit_ChoiceEquality)) (
                @inl unit_ChoiceEquality error_t (
                  (tt : unit_ChoiceEquality))) } : code (
                fset.fset0) [interface] _) } : code (fset.fset0) [interface] _))
        else ({ code @ret ((result error_t unit_ChoiceEquality)) (
            @inl unit_ChoiceEquality error_t (
              (tt : unit_ChoiceEquality))) } : code _ _ _) ) in
      ({ code  '(s_sum_11848 : scalar_t) ←
            ( '(temp_11821 : scalar_t) ←
                (nat_mod_zero ) ;;
              ret (temp_11821)) ;;
          #put s_sum_11848_loc := s_sum_11848 ;;
         '(r_sum_11849 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              )) ←
            ( temp_11823 ←
                (point_identity ) ;;
              ret (temp_11823)) ;;
          #put r_sum_11849_loc := r_sum_11849 ;;
         '(a_sum_11850 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              )) ←
            ( temp_11825 ←
                (point_identity ) ;;
              ret (temp_11825)) ;;
          #put a_sum_11850_loc := a_sum_11850 ;;
         '(temp_11827 : uint_size) ←
          (seq_len (entries_11813)) ;;
        bnd(ChoiceEqualityMonad.result_bind_code error_t , (
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
          ) , _ , CEfset (
            [s_sum_11848_loc ; r_sum_11849_loc ; a_sum_11850_loc])) '(
          s_sum_11848,
          r_sum_11849,
          a_sum_11850
        ) ⇠
        (foldi_bind_code' (usize 0) (temp_11827) (prod_ce(
              s_sum_11848,
              r_sum_11849,
              a_sum_11850
            )) (fun i_11828 '(s_sum_11848, r_sum_11849, a_sum_11850) =>
          ({ code  '(BatchEntry ((pk_11831, msg_11864, signature_11836
                  )) : batch_entry_t) ←
              ( '(temp_11830 : batch_entry_t) ←
                  (seq_index (entries_11813) (i_11828)) ;;
                ret ((temp_11830))) ;;
            bnd(ChoiceEqualityMonad.result_bind_code error_t , (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) , _ , CEfset (
                [s_sum_11848_loc ; r_sum_11849_loc ; a_sum_11850_loc])) a_11896 ⇠
            (({ code  temp_11833 ←
                  (decompress_non_canonical (pk_11831)) ;;
                 temp_11835 ←
                  (option_ok_or (temp_11833) (InvalidPublickey)) ;;
                @ret _ (temp_11835) } : code (CEfset (
                    [s_sum_11848_loc ; r_sum_11849_loc ; a_sum_11850_loc])) [interface
                #val #[ DECOMPRESS_NON_CANONICAL ] : decompress_non_canonical_inp → decompress_non_canonical_out
                ] _)) in
            ({ code  '(r_bytes_11851 : compressed_ed_point_t) ←
                ( '(temp_11838 : seq uint8) ←
                    (array_to_seq (signature_11836)) ;;
                   '(temp_11840 : compressed_ed_point_t) ←
                    (array_from_slice (default : uint8) (32) (temp_11838) (
                        usize 0) (usize 32)) ;;
                  ret (temp_11840)) ;;
               '(s_bytes_11845 : serialized_scalar_t) ←
                ( '(temp_11842 : seq uint8) ←
                    (array_to_seq (signature_11836)) ;;
                   '(temp_11844 : serialized_scalar_t) ←
                    (array_from_slice (default : uint8) (32) (temp_11842) (
                        usize 32) (usize 32)) ;;
                  ret (temp_11844)) ;;
               temp_11847 ←
                (check_canonical_scalar (s_bytes_11845)) ;;
              bnd(
                ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , CEfset (
                  [s_sum_11848_loc ; r_sum_11849_loc ; a_sum_11850_loc])) 'tt ⇠
              (if negb (temp_11847) : bool_ChoiceEquality
                then (*state*) (({ code bnd(
                      ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , CEfset (
                        [s_sum_11848_loc ; r_sum_11849_loc ; a_sum_11850_loc])) _ ⇠
                    (({ code @ret _ (@inr unit_ChoiceEquality error_t (
                            InvalidS)) } : code (CEfset (
                            [s_sum_11848_loc ; r_sum_11849_loc ; a_sum_11850_loc])) [interface] _)) in
                    ({ code @ret ((result error_t unit_ChoiceEquality)) (
                        @inl unit_ChoiceEquality error_t (
                          (tt : unit_ChoiceEquality))) } : code (CEfset (
                          [s_sum_11848_loc ; r_sum_11849_loc ; a_sum_11850_loc])) [interface] _) } : code (
                      CEfset (
                        [s_sum_11848_loc ; r_sum_11849_loc ; a_sum_11850_loc])) [interface] _))
                else ({ code @ret ((result error_t unit_ChoiceEquality)) (
                    @inl unit_ChoiceEquality error_t (
                      (tt : unit_ChoiceEquality))) } : code _ _ _) ) in
              ({ code bnd(ChoiceEqualityMonad.result_bind_code error_t , (
                    ed25519_field_element_t '×
                    ed25519_field_element_t '×
                    ed25519_field_element_t '×
                    ed25519_field_element_t
                  ) , _ , CEfset (
                    [s_sum_11848_loc ; r_sum_11849_loc ; a_sum_11850_loc])) r_11888 ⇠
                (({ code  temp_11853 ←
                      (decompress_non_canonical (r_bytes_11851)) ;;
                     temp_11855 ←
                      (option_ok_or (temp_11853) (InvalidR)) ;;
                    @ret _ (temp_11855) } : code (CEfset (
                        [s_sum_11848_loc ; r_sum_11849_loc ; a_sum_11850_loc])) [interface
                    #val #[ DECOMPRESS_NON_CANONICAL ] : decompress_non_canonical_inp → decompress_non_canonical_out
                    ] _)) in
                ({ code  '(s_11882 : scalar_t) ←
                    ( '(temp_11857 : seq uint8) ←
                        (array_to_seq (s_bytes_11845)) ;;
                       '(temp_11859 : scalar_t) ←
                        (nat_mod_from_byte_seq_le (temp_11857)) ;;
                      ret (temp_11859)) ;;
                   '(c_11893 : scalar_t) ←
                    ( '(temp_11861 : seq uint8) ←
                        (array_to_seq (pk_11831)) ;;
                       '(temp_11863 : seq uint8) ←
                        (array_concat (r_bytes_11851) (temp_11861)) ;;
                       '(temp_11866 : seq uint8) ←
                        (seq_concat (temp_11863) (msg_11864)) ;;
                       temp_11868 ←
                        (sha512 (temp_11866)) ;;
                       '(temp_11870 : scalar_t) ←
                        (scalar_from_hash (temp_11868)) ;;
                      ret (temp_11870)) ;;
                   '(z_11875 : seq uint8) ←
                    ( '(temp_11872 : uint_size) ←
                        ((usize 16) .* (i_11828)) ;;
                       '(temp_11874 : byte_seq) ←
                        (seq_slice (entropy_11810) (temp_11872) (usize 16)) ;;
                      ret (temp_11874)) ;;
                   '(z_11883 : scalar_t) ←
                    ( temp_11877 ←
                        (seq_new_ (default : uint8) (usize 16)) ;;
                       '(temp_11879 : seq uint8) ←
                        (seq_concat (z_11875) (temp_11877)) ;;
                       '(temp_11881 : scalar_t) ←
                        (nat_mod_from_byte_seq_le (temp_11879)) ;;
                      ret (temp_11881)) ;;
                   '(s_sum_11848 : scalar_t) ←
                      (( '(temp_11885 : scalar_t) ←
                            ((s_11882) *% (z_11883)) ;;
                           '(temp_11887 : scalar_t) ←
                            ((s_sum_11848) +% (temp_11885)) ;;
                          ret (temp_11887))) ;;
                    #put s_sum_11848_loc := s_sum_11848 ;;
                  
                   '(r_sum_11849 : (
                          ed25519_field_element_t '×
                          ed25519_field_element_t '×
                          ed25519_field_element_t '×
                          ed25519_field_element_t
                        )) ←
                      (( temp_11890 ←
                            (point_mul (z_11883) (r_11888)) ;;
                           temp_11892 ←
                            (point_add (r_sum_11849) (temp_11890)) ;;
                          ret (temp_11892))) ;;
                    #put r_sum_11849_loc := r_sum_11849 ;;
                  
                   '(a_sum_11850 : (
                          ed25519_field_element_t '×
                          ed25519_field_element_t '×
                          ed25519_field_element_t '×
                          ed25519_field_element_t
                        )) ←
                      (( '(temp_11895 : scalar_t) ←
                            ((z_11883) *% (c_11893)) ;;
                           temp_11898 ←
                            (point_mul (temp_11895) (a_11896)) ;;
                           temp_11900 ←
                            (point_add (a_sum_11850) (temp_11898)) ;;
                          ret (temp_11900))) ;;
                    #put a_sum_11850_loc := a_sum_11850 ;;
                  
                  @ret ((result error_t (
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
                      ))) (@inl (
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
                    ) error_t (prod_ce(s_sum_11848, r_sum_11849, a_sum_11850
                      ))) } : code (CEfset (
                      [s_sum_11848_loc ; r_sum_11849_loc ; a_sum_11850_loc])) [interface
                  #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
                  #val #[ DECOMPRESS_NON_CANONICAL ] : decompress_non_canonical_inp → decompress_non_canonical_out ;
                  #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
                  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
                  #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
                  #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
                  CEfset (
                    [s_sum_11848_loc ; r_sum_11849_loc ; a_sum_11850_loc])) [interface
                #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
                #val #[ DECOMPRESS_NON_CANONICAL ] : decompress_non_canonical_inp → decompress_non_canonical_out ;
                #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
                #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
                #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
                #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
                CEfset (
                  [s_sum_11848_loc ; r_sum_11849_loc ; a_sum_11850_loc])) [interface
              #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
              #val #[ DECOMPRESS_NON_CANONICAL ] : decompress_non_canonical_inp → decompress_non_canonical_out ;
              #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
              #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
              #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
              #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
              CEfset (
                [s_sum_11848_loc ; r_sum_11849_loc ; a_sum_11850_loc])) [interface
            #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
            #val #[ DECOMPRESS_NON_CANONICAL ] : decompress_non_canonical_inp → decompress_non_canonical_out ;
            #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
            #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
            #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
            #val #[ SHA512 ] : sha512_inp → sha512_out ] _))) in
        ({ code  '(b_11905 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              )) ←
            ( temp_11902 ←
                (decompress (base_v)) ;;
               temp_11904 ←
                (option_unwrap (temp_11902)) ;;
              ret (temp_11904)) ;;
           '(sb_11908 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              )) ←
            ( temp_11907 ←
                (point_mul (s_sum_11848) (b_11905)) ;;
              ret (temp_11907)) ;;
           '(check_11917 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              )) ←
            ( temp_11910 ←
                (point_neg (sb_11908)) ;;
               temp_11912 ←
                (point_add (r_sum_11849) (a_sum_11850)) ;;
               temp_11914 ←
                (point_add (temp_11910) (temp_11912)) ;;
               temp_11916 ←
                (point_mul_by_cofactor (temp_11914)) ;;
              ret (temp_11916)) ;;
           '(temp_11919 : bool_ChoiceEquality) ←
            (is_identity (check_11917)) ;;
          @ret ((result error_t unit_ChoiceEquality)) ((if (
                temp_11919):bool_ChoiceEquality then (*inline*) (
                @inl unit_ChoiceEquality error_t (tt)) else (
                @inr unit_ChoiceEquality error_t (
                  InvalidSignature)))) } : code (CEfset (
              [s_sum_11848_loc ; r_sum_11849_loc ; a_sum_11850_loc])) [interface
          #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
          #val #[ DECOMPRESS_NON_CANONICAL ] : decompress_non_canonical_inp → decompress_non_canonical_out ;
          #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
          #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
          #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
          #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (CEfset (
            [s_sum_11848_loc ; r_sum_11849_loc ; a_sum_11850_loc])) [interface
        #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
        #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
        #val #[ DECOMPRESS_NON_CANONICAL ] : decompress_non_canonical_inp → decompress_non_canonical_out ;
        #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
        #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
        #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ;
        #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
        #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
        #val #[ POINT_NEG ] : point_neg_inp → point_neg_out ;
        #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
        #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (CEfset (
          [s_sum_11848_loc ; r_sum_11849_loc ; a_sum_11850_loc])) [interface
      #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
      #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
      #val #[ DECOMPRESS_NON_CANONICAL ] : decompress_non_canonical_inp → decompress_non_canonical_out ;
      #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
      #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
      #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ;
      #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
      #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
      #val #[ POINT_NEG ] : point_neg_inp → point_neg_out ;
      #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
      #val #[ SHA512 ] : sha512_inp → sha512_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_zcash_batch_verify : package _ _ _ :=
  (seq_link zcash_batch_verify link_rest(
      package_check_canonical_scalar,package_decompress,package_decompress_non_canonical,package_is_identity,package_point_add,package_point_identity,package_point_mul,package_point_mul_by_cofactor,package_point_neg,package_scalar_from_hash,package_sha512)).
Fail Next Obligation.

Definition s_sum_11962_loc : ChoiceEqualityLocation :=
  ((scalar_t ; 12034%nat)).
Definition r_sum_11963_loc : ChoiceEqualityLocation :=
  (((
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) ; 12035%nat)).
Definition a_sum_11964_loc : ChoiceEqualityLocation :=
  (((
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) ; 12036%nat)).
Notation "'ietf_cofactored_batch_verify_inp'" := (
  seq batch_entry_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactored_batch_verify_out'" := (
  verify_result_t : choice_type) (in custom pack_type at level 2).
Definition IETF_COFACTORED_BATCH_VERIFY : nat :=
  (12037).
Program Definition ietf_cofactored_batch_verify
   : package (CEfset (
      [s_sum_11962_loc ; r_sum_11963_loc ; a_sum_11964_loc])) [interface
  #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
  #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
  #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
  #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ;
  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
  #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
  #val #[ POINT_NEG ] : point_neg_inp → point_neg_out ;
  #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
  #val #[ SHA512 ] : sha512_inp → sha512_out ] [interface
  #val #[ IETF_COFACTORED_BATCH_VERIFY ] : ietf_cofactored_batch_verify_inp → ietf_cofactored_batch_verify_out
  ] :=
  (
    [package #def #[ IETF_COFACTORED_BATCH_VERIFY ] (temp_inp : ietf_cofactored_batch_verify_inp) : ietf_cofactored_batch_verify_out { 
    let '(
      entries_11927 , entropy_11924) := temp_inp : seq batch_entry_t '× byte_seq in
    #import {sig #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out } as check_canonical_scalar ;;
    let check_canonical_scalar := fun x_0 => check_canonical_scalar (x_0) in
    #import {sig #[ DECOMPRESS ] : decompress_inp → decompress_out } as decompress ;;
    let decompress := fun x_0 => decompress (x_0) in
    #import {sig #[ IS_IDENTITY ] : is_identity_inp → is_identity_out } as is_identity ;;
    let is_identity := fun x_0 => is_identity (x_0) in
    #import {sig #[ POINT_ADD ] : point_add_inp → point_add_out } as point_add ;;
    let point_add := fun x_0 x_1 => point_add (x_0,x_1) in
    #import {sig #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out } as point_identity ;;
    let point_identity := point_identity tt in
    #import {sig #[ POINT_MUL ] : point_mul_inp → point_mul_out } as point_mul ;;
    let point_mul := fun x_0 x_1 => point_mul (x_0,x_1) in
    #import {sig #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out } as point_mul_by_cofactor ;;
    let point_mul_by_cofactor := fun x_0 => point_mul_by_cofactor (x_0) in
    #import {sig #[ POINT_NEG ] : point_neg_inp → point_neg_out } as point_neg ;;
    let point_neg := fun x_0 => point_neg (x_0) in
    #import {sig #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out } as scalar_from_hash ;;
    let scalar_from_hash := fun x_0 => scalar_from_hash (x_0) in
    #import {sig #[ SHA512 ] : sha512_inp → sha512_out } as sha512 ;;
    let sha512 := fun x_0 => sha512 (x_0) in
    ({ code  '(temp_11926 : uint_size) ←
        (seq_len (entropy_11924)) ;;
       '(temp_11929 : uint_size) ←
        (seq_len (entries_11927)) ;;
       '(temp_11931 : uint_size) ←
        ((usize 16) .* (temp_11929)) ;;
       '(temp_11933 : bool_ChoiceEquality) ←
        ((temp_11926) <.? (temp_11931)) ;;
      bnd(
        ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , CEfset (
          [s_sum_11962_loc ; r_sum_11963_loc ; a_sum_11964_loc])) 'tt ⇠
      (if temp_11933 : bool_ChoiceEquality
        then (*state*) (({ code bnd(
              ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , fset.fset0) _ ⇠
            (({ code @ret _ (@inr unit_ChoiceEquality error_t (
                    NotEnoughRandomness)) } : code (
                  fset.fset0) [interface] _)) in
            ({ code @ret ((result error_t unit_ChoiceEquality)) (
                @inl unit_ChoiceEquality error_t (
                  (tt : unit_ChoiceEquality))) } : code (
                fset.fset0) [interface] _) } : code (fset.fset0) [interface] _))
        else ({ code @ret ((result error_t unit_ChoiceEquality)) (
            @inl unit_ChoiceEquality error_t (
              (tt : unit_ChoiceEquality))) } : code _ _ _) ) in
      ({ code  '(s_sum_11962 : scalar_t) ←
            ( '(temp_11935 : scalar_t) ←
                (nat_mod_zero ) ;;
              ret (temp_11935)) ;;
          #put s_sum_11962_loc := s_sum_11962 ;;
         '(r_sum_11963 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              )) ←
            ( temp_11937 ←
                (point_identity ) ;;
              ret (temp_11937)) ;;
          #put r_sum_11963_loc := r_sum_11963 ;;
         '(a_sum_11964 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              )) ←
            ( temp_11939 ←
                (point_identity ) ;;
              ret (temp_11939)) ;;
          #put a_sum_11964_loc := a_sum_11964 ;;
         '(temp_11941 : uint_size) ←
          (seq_len (entries_11927)) ;;
        bnd(ChoiceEqualityMonad.result_bind_code error_t , (
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
          ) , _ , CEfset (
            [s_sum_11962_loc ; r_sum_11963_loc ; a_sum_11964_loc])) '(
          s_sum_11962,
          r_sum_11963,
          a_sum_11964
        ) ⇠
        (foldi_bind_code' (usize 0) (temp_11941) (prod_ce(
              s_sum_11962,
              r_sum_11963,
              a_sum_11964
            )) (fun i_11942 '(s_sum_11962, r_sum_11963, a_sum_11964) =>
          ({ code  '(BatchEntry ((pk_11945, msg_11978, signature_11950
                  )) : batch_entry_t) ←
              ( '(temp_11944 : batch_entry_t) ←
                  (seq_index (entries_11927) (i_11942)) ;;
                ret ((temp_11944))) ;;
            bnd(ChoiceEqualityMonad.result_bind_code error_t , (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) , _ , CEfset (
                [s_sum_11962_loc ; r_sum_11963_loc ; a_sum_11964_loc])) a_12010 ⇠
            (({ code  temp_11947 ←
                  (decompress (pk_11945)) ;;
                 temp_11949 ←
                  (option_ok_or (temp_11947) (InvalidPublickey)) ;;
                @ret _ (temp_11949) } : code (CEfset (
                    [s_sum_11962_loc ; r_sum_11963_loc ; a_sum_11964_loc])) [interface
                #val #[ DECOMPRESS ] : decompress_inp → decompress_out
                ] _)) in
            ({ code  '(r_bytes_11965 : compressed_ed_point_t) ←
                ( '(temp_11952 : seq uint8) ←
                    (array_to_seq (signature_11950)) ;;
                   '(temp_11954 : compressed_ed_point_t) ←
                    (array_from_slice (default : uint8) (32) (temp_11952) (
                        usize 0) (usize 32)) ;;
                  ret (temp_11954)) ;;
               '(s_bytes_11959 : serialized_scalar_t) ←
                ( '(temp_11956 : seq uint8) ←
                    (array_to_seq (signature_11950)) ;;
                   '(temp_11958 : serialized_scalar_t) ←
                    (array_from_slice (default : uint8) (32) (temp_11956) (
                        usize 32) (usize 32)) ;;
                  ret (temp_11958)) ;;
               temp_11961 ←
                (check_canonical_scalar (s_bytes_11959)) ;;
              bnd(
                ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , CEfset (
                  [s_sum_11962_loc ; r_sum_11963_loc ; a_sum_11964_loc])) 'tt ⇠
              (if negb (temp_11961) : bool_ChoiceEquality
                then (*state*) (({ code bnd(
                      ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , CEfset (
                        [s_sum_11962_loc ; r_sum_11963_loc ; a_sum_11964_loc])) _ ⇠
                    (({ code @ret _ (@inr unit_ChoiceEquality error_t (
                            InvalidS)) } : code (CEfset (
                            [s_sum_11962_loc ; r_sum_11963_loc ; a_sum_11964_loc])) [interface] _)) in
                    ({ code @ret ((result error_t unit_ChoiceEquality)) (
                        @inl unit_ChoiceEquality error_t (
                          (tt : unit_ChoiceEquality))) } : code (CEfset (
                          [s_sum_11962_loc ; r_sum_11963_loc ; a_sum_11964_loc])) [interface] _) } : code (
                      CEfset (
                        [s_sum_11962_loc ; r_sum_11963_loc ; a_sum_11964_loc])) [interface] _))
                else ({ code @ret ((result error_t unit_ChoiceEquality)) (
                    @inl unit_ChoiceEquality error_t (
                      (tt : unit_ChoiceEquality))) } : code _ _ _) ) in
              ({ code bnd(ChoiceEqualityMonad.result_bind_code error_t , (
                    ed25519_field_element_t '×
                    ed25519_field_element_t '×
                    ed25519_field_element_t '×
                    ed25519_field_element_t
                  ) , _ , CEfset (
                    [s_sum_11962_loc ; r_sum_11963_loc ; a_sum_11964_loc])) r_12002 ⇠
                (({ code  temp_11967 ←
                      (decompress (r_bytes_11965)) ;;
                     temp_11969 ←
                      (option_ok_or (temp_11967) (InvalidR)) ;;
                    @ret _ (temp_11969) } : code (CEfset (
                        [s_sum_11962_loc ; r_sum_11963_loc ; a_sum_11964_loc])) [interface
                    #val #[ DECOMPRESS ] : decompress_inp → decompress_out
                    ] _)) in
                ({ code  '(s_11996 : scalar_t) ←
                    ( '(temp_11971 : seq uint8) ←
                        (array_to_seq (s_bytes_11959)) ;;
                       '(temp_11973 : scalar_t) ←
                        (nat_mod_from_byte_seq_le (temp_11971)) ;;
                      ret (temp_11973)) ;;
                   '(c_12007 : scalar_t) ←
                    ( '(temp_11975 : seq uint8) ←
                        (array_to_seq (pk_11945)) ;;
                       '(temp_11977 : seq uint8) ←
                        (array_concat (r_bytes_11965) (temp_11975)) ;;
                       '(temp_11980 : seq uint8) ←
                        (seq_concat (temp_11977) (msg_11978)) ;;
                       temp_11982 ←
                        (sha512 (temp_11980)) ;;
                       '(temp_11984 : scalar_t) ←
                        (scalar_from_hash (temp_11982)) ;;
                      ret (temp_11984)) ;;
                   '(z_11989 : seq uint8) ←
                    ( '(temp_11986 : uint_size) ←
                        ((usize 16) .* (i_11942)) ;;
                       '(temp_11988 : byte_seq) ←
                        (seq_slice (entropy_11924) (temp_11986) (usize 16)) ;;
                      ret (temp_11988)) ;;
                   '(z_11997 : scalar_t) ←
                    ( temp_11991 ←
                        (seq_new_ (default : uint8) (usize 16)) ;;
                       '(temp_11993 : seq uint8) ←
                        (seq_concat (z_11989) (temp_11991)) ;;
                       '(temp_11995 : scalar_t) ←
                        (nat_mod_from_byte_seq_le (temp_11993)) ;;
                      ret (temp_11995)) ;;
                   '(s_sum_11962 : scalar_t) ←
                      (( '(temp_11999 : scalar_t) ←
                            ((s_11996) *% (z_11997)) ;;
                           '(temp_12001 : scalar_t) ←
                            ((s_sum_11962) +% (temp_11999)) ;;
                          ret (temp_12001))) ;;
                    #put s_sum_11962_loc := s_sum_11962 ;;
                  
                   '(r_sum_11963 : (
                          ed25519_field_element_t '×
                          ed25519_field_element_t '×
                          ed25519_field_element_t '×
                          ed25519_field_element_t
                        )) ←
                      (( temp_12004 ←
                            (point_mul (z_11997) (r_12002)) ;;
                           temp_12006 ←
                            (point_add (r_sum_11963) (temp_12004)) ;;
                          ret (temp_12006))) ;;
                    #put r_sum_11963_loc := r_sum_11963 ;;
                  
                   '(a_sum_11964 : (
                          ed25519_field_element_t '×
                          ed25519_field_element_t '×
                          ed25519_field_element_t '×
                          ed25519_field_element_t
                        )) ←
                      (( '(temp_12009 : scalar_t) ←
                            ((z_11997) *% (c_12007)) ;;
                           temp_12012 ←
                            (point_mul (temp_12009) (a_12010)) ;;
                           temp_12014 ←
                            (point_add (a_sum_11964) (temp_12012)) ;;
                          ret (temp_12014))) ;;
                    #put a_sum_11964_loc := a_sum_11964 ;;
                  
                  @ret ((result error_t (
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
                      ))) (@inl (
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
                    ) error_t (prod_ce(s_sum_11962, r_sum_11963, a_sum_11964
                      ))) } : code (CEfset (
                      [s_sum_11962_loc ; r_sum_11963_loc ; a_sum_11964_loc])) [interface
                  #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
                  #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
                  #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
                  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
                  #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
                  #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
                  CEfset (
                    [s_sum_11962_loc ; r_sum_11963_loc ; a_sum_11964_loc])) [interface
                #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
                #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
                #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
                #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
                #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
                #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
                CEfset (
                  [s_sum_11962_loc ; r_sum_11963_loc ; a_sum_11964_loc])) [interface
              #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
              #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
              #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
              #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
              #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
              #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
              CEfset (
                [s_sum_11962_loc ; r_sum_11963_loc ; a_sum_11964_loc])) [interface
            #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
            #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
            #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
            #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
            #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
            #val #[ SHA512 ] : sha512_inp → sha512_out ] _))) in
        ({ code  '(b_12019 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              )) ←
            ( temp_12016 ←
                (decompress (base_v)) ;;
               temp_12018 ←
                (option_unwrap (temp_12016)) ;;
              ret (temp_12018)) ;;
           '(sb_12022 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              )) ←
            ( temp_12021 ←
                (point_mul (s_sum_11962) (b_12019)) ;;
              ret (temp_12021)) ;;
           '(check_12031 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              )) ←
            ( temp_12024 ←
                (point_neg (sb_12022)) ;;
               temp_12026 ←
                (point_add (r_sum_11963) (a_sum_11964)) ;;
               temp_12028 ←
                (point_add (temp_12024) (temp_12026)) ;;
               temp_12030 ←
                (point_mul_by_cofactor (temp_12028)) ;;
              ret (temp_12030)) ;;
           '(temp_12033 : bool_ChoiceEquality) ←
            (is_identity (check_12031)) ;;
          @ret ((result error_t unit_ChoiceEquality)) ((if (
                temp_12033):bool_ChoiceEquality then (*inline*) (
                @inl unit_ChoiceEquality error_t (tt)) else (
                @inr unit_ChoiceEquality error_t (
                  InvalidSignature)))) } : code (CEfset (
              [s_sum_11962_loc ; r_sum_11963_loc ; a_sum_11964_loc])) [interface
          #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
          #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
          #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
          #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
          #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
          #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (CEfset (
            [s_sum_11962_loc ; r_sum_11963_loc ; a_sum_11964_loc])) [interface
        #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
        #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
        #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
        #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
        #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ;
        #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
        #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
        #val #[ POINT_NEG ] : point_neg_inp → point_neg_out ;
        #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
        #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (CEfset (
          [s_sum_11962_loc ; r_sum_11963_loc ; a_sum_11964_loc])) [interface
      #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
      #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
      #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
      #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
      #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ;
      #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
      #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
      #val #[ POINT_NEG ] : point_neg_inp → point_neg_out ;
      #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
      #val #[ SHA512 ] : sha512_inp → sha512_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_ietf_cofactored_batch_verify : package _ _ _ :=
  (seq_link ietf_cofactored_batch_verify link_rest(
      package_check_canonical_scalar,package_decompress,package_is_identity,package_point_add,package_point_identity,package_point_mul,package_point_mul_by_cofactor,package_point_neg,package_scalar_from_hash,package_sha512)).
Fail Next Obligation.

Definition s_sum_12076_loc : ChoiceEqualityLocation :=
  ((scalar_t ; 12146%nat)).
Definition r_sum_12077_loc : ChoiceEqualityLocation :=
  (((
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) ; 12147%nat)).
Definition a_sum_12078_loc : ChoiceEqualityLocation :=
  (((
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) ; 12148%nat)).
Notation "'ietf_cofactorless_batch_verify_inp'" := (
  seq batch_entry_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactorless_batch_verify_out'" := (
  verify_result_t : choice_type) (in custom pack_type at level 2).
Definition IETF_COFACTORLESS_BATCH_VERIFY : nat :=
  (12149).
Program Definition ietf_cofactorless_batch_verify
   : package (CEfset (
      [s_sum_12076_loc ; r_sum_12077_loc ; a_sum_12078_loc])) [interface
  #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
  #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
  #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
  #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ;
  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
  #val #[ POINT_NEG ] : point_neg_inp → point_neg_out ;
  #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
  #val #[ SHA512 ] : sha512_inp → sha512_out ] [interface
  #val #[ IETF_COFACTORLESS_BATCH_VERIFY ] : ietf_cofactorless_batch_verify_inp → ietf_cofactorless_batch_verify_out
  ] :=
  (
    [package #def #[ IETF_COFACTORLESS_BATCH_VERIFY ] (temp_inp : ietf_cofactorless_batch_verify_inp) : ietf_cofactorless_batch_verify_out { 
    let '(
      entries_12041 , entropy_12038) := temp_inp : seq batch_entry_t '× byte_seq in
    #import {sig #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out } as check_canonical_scalar ;;
    let check_canonical_scalar := fun x_0 => check_canonical_scalar (x_0) in
    #import {sig #[ DECOMPRESS ] : decompress_inp → decompress_out } as decompress ;;
    let decompress := fun x_0 => decompress (x_0) in
    #import {sig #[ IS_IDENTITY ] : is_identity_inp → is_identity_out } as is_identity ;;
    let is_identity := fun x_0 => is_identity (x_0) in
    #import {sig #[ POINT_ADD ] : point_add_inp → point_add_out } as point_add ;;
    let point_add := fun x_0 x_1 => point_add (x_0,x_1) in
    #import {sig #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out } as point_identity ;;
    let point_identity := point_identity tt in
    #import {sig #[ POINT_MUL ] : point_mul_inp → point_mul_out } as point_mul ;;
    let point_mul := fun x_0 x_1 => point_mul (x_0,x_1) in
    #import {sig #[ POINT_NEG ] : point_neg_inp → point_neg_out } as point_neg ;;
    let point_neg := fun x_0 => point_neg (x_0) in
    #import {sig #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out } as scalar_from_hash ;;
    let scalar_from_hash := fun x_0 => scalar_from_hash (x_0) in
    #import {sig #[ SHA512 ] : sha512_inp → sha512_out } as sha512 ;;
    let sha512 := fun x_0 => sha512 (x_0) in
    ({ code  '(temp_12040 : uint_size) ←
        (seq_len (entropy_12038)) ;;
       '(temp_12043 : uint_size) ←
        (seq_len (entries_12041)) ;;
       '(temp_12045 : uint_size) ←
        ((usize 16) .* (temp_12043)) ;;
       '(temp_12047 : bool_ChoiceEquality) ←
        ((temp_12040) <.? (temp_12045)) ;;
      bnd(
        ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , CEfset (
          [s_sum_12076_loc ; r_sum_12077_loc ; a_sum_12078_loc])) 'tt ⇠
      (if temp_12047 : bool_ChoiceEquality
        then (*state*) (({ code bnd(
              ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , fset.fset0) _ ⇠
            (({ code @ret _ (@inr unit_ChoiceEquality error_t (
                    NotEnoughRandomness)) } : code (
                  fset.fset0) [interface] _)) in
            ({ code @ret ((result error_t unit_ChoiceEquality)) (
                @inl unit_ChoiceEquality error_t (
                  (tt : unit_ChoiceEquality))) } : code (
                fset.fset0) [interface] _) } : code (fset.fset0) [interface] _))
        else ({ code @ret ((result error_t unit_ChoiceEquality)) (
            @inl unit_ChoiceEquality error_t (
              (tt : unit_ChoiceEquality))) } : code _ _ _) ) in
      ({ code  '(s_sum_12076 : scalar_t) ←
            ( '(temp_12049 : scalar_t) ←
                (nat_mod_zero ) ;;
              ret (temp_12049)) ;;
          #put s_sum_12076_loc := s_sum_12076 ;;
         '(r_sum_12077 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              )) ←
            ( temp_12051 ←
                (point_identity ) ;;
              ret (temp_12051)) ;;
          #put r_sum_12077_loc := r_sum_12077 ;;
         '(a_sum_12078 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              )) ←
            ( temp_12053 ←
                (point_identity ) ;;
              ret (temp_12053)) ;;
          #put a_sum_12078_loc := a_sum_12078 ;;
         '(temp_12055 : uint_size) ←
          (seq_len (entries_12041)) ;;
        bnd(ChoiceEqualityMonad.result_bind_code error_t , (
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
          ) , _ , CEfset (
            [s_sum_12076_loc ; r_sum_12077_loc ; a_sum_12078_loc])) '(
          s_sum_12076,
          r_sum_12077,
          a_sum_12078
        ) ⇠
        (foldi_bind_code' (usize 0) (temp_12055) (prod_ce(
              s_sum_12076,
              r_sum_12077,
              a_sum_12078
            )) (fun i_12056 '(s_sum_12076, r_sum_12077, a_sum_12078) =>
          ({ code  '(BatchEntry ((pk_12059, msg_12092, signature_12064
                  )) : batch_entry_t) ←
              ( '(temp_12058 : batch_entry_t) ←
                  (seq_index (entries_12041) (i_12056)) ;;
                ret ((temp_12058))) ;;
            bnd(ChoiceEqualityMonad.result_bind_code error_t , (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) , _ , CEfset (
                [s_sum_12076_loc ; r_sum_12077_loc ; a_sum_12078_loc])) a_12124 ⇠
            (({ code  temp_12061 ←
                  (decompress (pk_12059)) ;;
                 temp_12063 ←
                  (option_ok_or (temp_12061) (InvalidPublickey)) ;;
                @ret _ (temp_12063) } : code (CEfset (
                    [s_sum_12076_loc ; r_sum_12077_loc ; a_sum_12078_loc])) [interface
                #val #[ DECOMPRESS ] : decompress_inp → decompress_out
                ] _)) in
            ({ code  '(r_bytes_12079 : compressed_ed_point_t) ←
                ( '(temp_12066 : seq uint8) ←
                    (array_to_seq (signature_12064)) ;;
                   '(temp_12068 : compressed_ed_point_t) ←
                    (array_from_slice (default : uint8) (32) (temp_12066) (
                        usize 0) (usize 32)) ;;
                  ret (temp_12068)) ;;
               '(s_bytes_12073 : serialized_scalar_t) ←
                ( '(temp_12070 : seq uint8) ←
                    (array_to_seq (signature_12064)) ;;
                   '(temp_12072 : serialized_scalar_t) ←
                    (array_from_slice (default : uint8) (32) (temp_12070) (
                        usize 32) (usize 32)) ;;
                  ret (temp_12072)) ;;
               temp_12075 ←
                (check_canonical_scalar (s_bytes_12073)) ;;
              bnd(
                ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , CEfset (
                  [s_sum_12076_loc ; r_sum_12077_loc ; a_sum_12078_loc])) 'tt ⇠
              (if negb (temp_12075) : bool_ChoiceEquality
                then (*state*) (({ code bnd(
                      ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , CEfset (
                        [s_sum_12076_loc ; r_sum_12077_loc ; a_sum_12078_loc])) _ ⇠
                    (({ code @ret _ (@inr unit_ChoiceEquality error_t (
                            InvalidS)) } : code (CEfset (
                            [s_sum_12076_loc ; r_sum_12077_loc ; a_sum_12078_loc])) [interface] _)) in
                    ({ code @ret ((result error_t unit_ChoiceEquality)) (
                        @inl unit_ChoiceEquality error_t (
                          (tt : unit_ChoiceEquality))) } : code (CEfset (
                          [s_sum_12076_loc ; r_sum_12077_loc ; a_sum_12078_loc])) [interface] _) } : code (
                      CEfset (
                        [s_sum_12076_loc ; r_sum_12077_loc ; a_sum_12078_loc])) [interface] _))
                else ({ code @ret ((result error_t unit_ChoiceEquality)) (
                    @inl unit_ChoiceEquality error_t (
                      (tt : unit_ChoiceEquality))) } : code _ _ _) ) in
              ({ code bnd(ChoiceEqualityMonad.result_bind_code error_t , (
                    ed25519_field_element_t '×
                    ed25519_field_element_t '×
                    ed25519_field_element_t '×
                    ed25519_field_element_t
                  ) , _ , CEfset (
                    [s_sum_12076_loc ; r_sum_12077_loc ; a_sum_12078_loc])) r_12116 ⇠
                (({ code  temp_12081 ←
                      (decompress (r_bytes_12079)) ;;
                     temp_12083 ←
                      (option_ok_or (temp_12081) (InvalidR)) ;;
                    @ret _ (temp_12083) } : code (CEfset (
                        [s_sum_12076_loc ; r_sum_12077_loc ; a_sum_12078_loc])) [interface
                    #val #[ DECOMPRESS ] : decompress_inp → decompress_out
                    ] _)) in
                ({ code  '(s_12110 : scalar_t) ←
                    ( '(temp_12085 : seq uint8) ←
                        (array_to_seq (s_bytes_12073)) ;;
                       '(temp_12087 : scalar_t) ←
                        (nat_mod_from_byte_seq_le (temp_12085)) ;;
                      ret (temp_12087)) ;;
                   '(c_12121 : scalar_t) ←
                    ( '(temp_12089 : seq uint8) ←
                        (array_to_seq (pk_12059)) ;;
                       '(temp_12091 : seq uint8) ←
                        (array_concat (r_bytes_12079) (temp_12089)) ;;
                       '(temp_12094 : seq uint8) ←
                        (seq_concat (temp_12091) (msg_12092)) ;;
                       temp_12096 ←
                        (sha512 (temp_12094)) ;;
                       '(temp_12098 : scalar_t) ←
                        (scalar_from_hash (temp_12096)) ;;
                      ret (temp_12098)) ;;
                   '(z_12103 : seq uint8) ←
                    ( '(temp_12100 : uint_size) ←
                        ((usize 16) .* (i_12056)) ;;
                       '(temp_12102 : byte_seq) ←
                        (seq_slice (entropy_12038) (temp_12100) (usize 16)) ;;
                      ret (temp_12102)) ;;
                   '(z_12111 : scalar_t) ←
                    ( temp_12105 ←
                        (seq_new_ (default : uint8) (usize 16)) ;;
                       '(temp_12107 : seq uint8) ←
                        (seq_concat (z_12103) (temp_12105)) ;;
                       '(temp_12109 : scalar_t) ←
                        (nat_mod_from_byte_seq_le (temp_12107)) ;;
                      ret (temp_12109)) ;;
                   '(s_sum_12076 : scalar_t) ←
                      (( '(temp_12113 : scalar_t) ←
                            ((s_12110) *% (z_12111)) ;;
                           '(temp_12115 : scalar_t) ←
                            ((s_sum_12076) +% (temp_12113)) ;;
                          ret (temp_12115))) ;;
                    #put s_sum_12076_loc := s_sum_12076 ;;
                  
                   '(r_sum_12077 : (
                          ed25519_field_element_t '×
                          ed25519_field_element_t '×
                          ed25519_field_element_t '×
                          ed25519_field_element_t
                        )) ←
                      (( temp_12118 ←
                            (point_mul (z_12111) (r_12116)) ;;
                           temp_12120 ←
                            (point_add (r_sum_12077) (temp_12118)) ;;
                          ret (temp_12120))) ;;
                    #put r_sum_12077_loc := r_sum_12077 ;;
                  
                   '(a_sum_12078 : (
                          ed25519_field_element_t '×
                          ed25519_field_element_t '×
                          ed25519_field_element_t '×
                          ed25519_field_element_t
                        )) ←
                      (( '(temp_12123 : scalar_t) ←
                            ((z_12111) *% (c_12121)) ;;
                           temp_12126 ←
                            (point_mul (temp_12123) (a_12124)) ;;
                           temp_12128 ←
                            (point_add (a_sum_12078) (temp_12126)) ;;
                          ret (temp_12128))) ;;
                    #put a_sum_12078_loc := a_sum_12078 ;;
                  
                  @ret ((result error_t (
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
                      ))) (@inl (
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
                    ) error_t (prod_ce(s_sum_12076, r_sum_12077, a_sum_12078
                      ))) } : code (CEfset (
                      [s_sum_12076_loc ; r_sum_12077_loc ; a_sum_12078_loc])) [interface
                  #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
                  #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
                  #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
                  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
                  #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
                  #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
                  CEfset (
                    [s_sum_12076_loc ; r_sum_12077_loc ; a_sum_12078_loc])) [interface
                #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
                #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
                #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
                #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
                #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
                #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
                CEfset (
                  [s_sum_12076_loc ; r_sum_12077_loc ; a_sum_12078_loc])) [interface
              #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
              #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
              #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
              #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
              #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
              #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
              CEfset (
                [s_sum_12076_loc ; r_sum_12077_loc ; a_sum_12078_loc])) [interface
            #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
            #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
            #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
            #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
            #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
            #val #[ SHA512 ] : sha512_inp → sha512_out ] _))) in
        ({ code  '(b_12133 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              )) ←
            ( temp_12130 ←
                (decompress (base_v)) ;;
               temp_12132 ←
                (option_unwrap (temp_12130)) ;;
              ret (temp_12132)) ;;
           '(sb_12136 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              )) ←
            ( temp_12135 ←
                (point_mul (s_sum_12076) (b_12133)) ;;
              ret (temp_12135)) ;;
           '(check_12143 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              )) ←
            ( temp_12138 ←
                (point_neg (sb_12136)) ;;
               temp_12140 ←
                (point_add (r_sum_12077) (a_sum_12078)) ;;
               temp_12142 ←
                (point_add (temp_12138) (temp_12140)) ;;
              ret (temp_12142)) ;;
           '(temp_12145 : bool_ChoiceEquality) ←
            (is_identity (check_12143)) ;;
          @ret ((result error_t unit_ChoiceEquality)) ((if (
                temp_12145):bool_ChoiceEquality then (*inline*) (
                @inl unit_ChoiceEquality error_t (tt)) else (
                @inr unit_ChoiceEquality error_t (
                  InvalidSignature)))) } : code (CEfset (
              [s_sum_12076_loc ; r_sum_12077_loc ; a_sum_12078_loc])) [interface
          #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
          #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
          #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
          #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
          #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
          #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (CEfset (
            [s_sum_12076_loc ; r_sum_12077_loc ; a_sum_12078_loc])) [interface
        #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
        #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
        #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
        #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
        #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ;
        #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
        #val #[ POINT_NEG ] : point_neg_inp → point_neg_out ;
        #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
        #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (CEfset (
          [s_sum_12076_loc ; r_sum_12077_loc ; a_sum_12078_loc])) [interface
      #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
      #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
      #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
      #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
      #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ;
      #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
      #val #[ POINT_NEG ] : point_neg_inp → point_neg_out ;
      #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
      #val #[ SHA512 ] : sha512_inp → sha512_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_ietf_cofactorless_batch_verify : package _ _ _ :=
  (seq_link ietf_cofactorless_batch_verify link_rest(
      package_check_canonical_scalar,package_decompress,package_is_identity,package_point_add,package_point_identity,package_point_mul,package_point_neg,package_scalar_from_hash,package_sha512)).
Fail Next Obligation.

Definition s_sum_12181_loc : ChoiceEqualityLocation :=
  ((scalar_t ; 12264%nat)).
Definition r_sum_12182_loc : ChoiceEqualityLocation :=
  (((
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) ; 12265%nat)).
Definition a_sum_12183_loc : ChoiceEqualityLocation :=
  (((
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) ; 12266%nat)).
Notation "'alg3_batch_verify_inp'" := (
  seq batch_entry_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'alg3_batch_verify_out'" := (
  verify_result_t : choice_type) (in custom pack_type at level 2).
Definition ALG3_BATCH_VERIFY : nat :=
  (12267).
Program Definition alg3_batch_verify
   : package (CEfset (
      [s_sum_12181_loc ; r_sum_12182_loc ; a_sum_12183_loc])) [interface
  #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
  #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
  #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
  #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ;
  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
  #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
  #val #[ POINT_NEG ] : point_neg_inp → point_neg_out ;
  #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
  #val #[ SHA512 ] : sha512_inp → sha512_out ] [interface
  #val #[ ALG3_BATCH_VERIFY ] : alg3_batch_verify_inp → alg3_batch_verify_out
  ] :=
  (
    [package #def #[ ALG3_BATCH_VERIFY ] (temp_inp : alg3_batch_verify_inp) : alg3_batch_verify_out { 
    let '(
      entries_12153 , entropy_12150) := temp_inp : seq batch_entry_t '× byte_seq in
    #import {sig #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out } as check_canonical_scalar ;;
    let check_canonical_scalar := fun x_0 => check_canonical_scalar (x_0) in
    #import {sig #[ DECOMPRESS ] : decompress_inp → decompress_out } as decompress ;;
    let decompress := fun x_0 => decompress (x_0) in
    #import {sig #[ IS_IDENTITY ] : is_identity_inp → is_identity_out } as is_identity ;;
    let is_identity := fun x_0 => is_identity (x_0) in
    #import {sig #[ POINT_ADD ] : point_add_inp → point_add_out } as point_add ;;
    let point_add := fun x_0 x_1 => point_add (x_0,x_1) in
    #import {sig #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out } as point_identity ;;
    let point_identity := point_identity tt in
    #import {sig #[ POINT_MUL ] : point_mul_inp → point_mul_out } as point_mul ;;
    let point_mul := fun x_0 x_1 => point_mul (x_0,x_1) in
    #import {sig #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out } as point_mul_by_cofactor ;;
    let point_mul_by_cofactor := fun x_0 => point_mul_by_cofactor (x_0) in
    #import {sig #[ POINT_NEG ] : point_neg_inp → point_neg_out } as point_neg ;;
    let point_neg := fun x_0 => point_neg (x_0) in
    #import {sig #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out } as scalar_from_hash ;;
    let scalar_from_hash := fun x_0 => scalar_from_hash (x_0) in
    #import {sig #[ SHA512 ] : sha512_inp → sha512_out } as sha512 ;;
    let sha512 := fun x_0 => sha512 (x_0) in
    ({ code  '(temp_12152 : uint_size) ←
        (seq_len (entropy_12150)) ;;
       '(temp_12155 : uint_size) ←
        (seq_len (entries_12153)) ;;
       '(temp_12157 : uint_size) ←
        ((usize 16) .* (temp_12155)) ;;
       '(temp_12159 : bool_ChoiceEquality) ←
        ((temp_12152) <.? (temp_12157)) ;;
      bnd(
        ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , CEfset (
          [s_sum_12181_loc ; r_sum_12182_loc ; a_sum_12183_loc])) 'tt ⇠
      (if temp_12159 : bool_ChoiceEquality
        then (*state*) (({ code bnd(
              ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , fset.fset0) _ ⇠
            (({ code @ret _ (@inr unit_ChoiceEquality error_t (
                    NotEnoughRandomness)) } : code (
                  fset.fset0) [interface] _)) in
            ({ code @ret ((result error_t unit_ChoiceEquality)) (
                @inl unit_ChoiceEquality error_t (
                  (tt : unit_ChoiceEquality))) } : code (
                fset.fset0) [interface] _) } : code (fset.fset0) [interface] _))
        else ({ code @ret ((result error_t unit_ChoiceEquality)) (
            @inl unit_ChoiceEquality error_t (
              (tt : unit_ChoiceEquality))) } : code _ _ _) ) in
      ({ code  '(s_sum_12181 : scalar_t) ←
            ( '(temp_12161 : scalar_t) ←
                (nat_mod_zero ) ;;
              ret (temp_12161)) ;;
          #put s_sum_12181_loc := s_sum_12181 ;;
         '(r_sum_12182 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              )) ←
            ( temp_12163 ←
                (point_identity ) ;;
              ret (temp_12163)) ;;
          #put r_sum_12182_loc := r_sum_12182 ;;
         '(a_sum_12183 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              )) ←
            ( temp_12165 ←
                (point_identity ) ;;
              ret (temp_12165)) ;;
          #put a_sum_12183_loc := a_sum_12183 ;;
         '(temp_12167 : uint_size) ←
          (seq_len (entries_12153)) ;;
        bnd(ChoiceEqualityMonad.result_bind_code error_t , (
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
          ) , _ , CEfset (
            [s_sum_12181_loc ; r_sum_12182_loc ; a_sum_12183_loc])) '(
          s_sum_12181,
          r_sum_12182,
          a_sum_12183
        ) ⇠
        (foldi_bind_code' (usize 0) (temp_12167) (prod_ce(
              s_sum_12181,
              r_sum_12182,
              a_sum_12183
            )) (fun i_12168 '(s_sum_12181, r_sum_12182, a_sum_12183) =>
          ({ code  '(BatchEntry ((pk_12171, msg_12209, signature_12184
                  )) : batch_entry_t) ←
              ( '(temp_12170 : batch_entry_t) ←
                  (seq_index (entries_12153) (i_12168)) ;;
                ret ((temp_12170))) ;;
            bnd(ChoiceEqualityMonad.result_bind_code error_t , (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) , _ , CEfset (
                [s_sum_12181_loc ; r_sum_12182_loc ; a_sum_12183_loc])) a_12176 ⇠
            (({ code  temp_12173 ←
                  (decompress (pk_12171)) ;;
                 temp_12175 ←
                  (option_ok_or (temp_12173) (InvalidPublickey)) ;;
                @ret _ (temp_12175) } : code (CEfset (
                    [s_sum_12181_loc ; r_sum_12182_loc ; a_sum_12183_loc])) [interface
                #val #[ DECOMPRESS ] : decompress_inp → decompress_out
                ] _)) in
            ({ code  temp_12178 ←
                (point_mul_by_cofactor (a_12176)) ;;
               '(temp_12180 : bool_ChoiceEquality) ←
                (is_identity (temp_12178)) ;;
              bnd(
                ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , CEfset (
                  [s_sum_12181_loc ; r_sum_12182_loc ; a_sum_12183_loc])) 'tt ⇠
              (if temp_12180 : bool_ChoiceEquality
                then (*state*) (({ code bnd(
                      ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , CEfset (
                        [s_sum_12181_loc ; r_sum_12182_loc ; a_sum_12183_loc])) _ ⇠
                    (({ code @ret _ (@inr unit_ChoiceEquality error_t (
                            SmallOrderPoint)) } : code (CEfset (
                            [s_sum_12181_loc ; r_sum_12182_loc ; a_sum_12183_loc])) [interface] _)) in
                    ({ code @ret ((result error_t unit_ChoiceEquality)) (
                        @inl unit_ChoiceEquality error_t (
                          (tt : unit_ChoiceEquality))) } : code (CEfset (
                          [s_sum_12181_loc ; r_sum_12182_loc ; a_sum_12183_loc])) [interface] _) } : code (
                      CEfset (
                        [s_sum_12181_loc ; r_sum_12182_loc ; a_sum_12183_loc])) [interface] _))
                else ({ code @ret ((result error_t unit_ChoiceEquality)) (
                    @inl unit_ChoiceEquality error_t (
                      (tt : unit_ChoiceEquality))) } : code _ _ _) ) in
              ({ code  '(r_bytes_12196 : compressed_ed_point_t) ←
                  ( '(temp_12186 : seq uint8) ←
                      (array_to_seq (signature_12184)) ;;
                     '(temp_12188 : compressed_ed_point_t) ←
                      (array_from_slice (default : uint8) (32) (temp_12186) (
                          usize 0) (usize 32)) ;;
                    ret (temp_12188)) ;;
                 '(s_bytes_12193 : serialized_scalar_t) ←
                  ( '(temp_12190 : seq uint8) ←
                      (array_to_seq (signature_12184)) ;;
                     '(temp_12192 : serialized_scalar_t) ←
                      (array_from_slice (default : uint8) (32) (temp_12190) (
                          usize 32) (usize 32)) ;;
                    ret (temp_12192)) ;;
                 temp_12195 ←
                  (check_canonical_scalar (s_bytes_12193)) ;;
                bnd(
                  ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , CEfset (
                    [s_sum_12181_loc ; r_sum_12182_loc ; a_sum_12183_loc])) 'tt ⇠
                (if negb (temp_12195) : bool_ChoiceEquality
                  then (*state*) (({ code bnd(
                        ChoiceEqualityMonad.result_bind_code error_t , unit_ChoiceEquality , _ , CEfset (
                          [s_sum_12181_loc ; r_sum_12182_loc ; a_sum_12183_loc])) _ ⇠
                      (({ code @ret _ (@inr unit_ChoiceEquality error_t (
                              InvalidS)) } : code (CEfset (
                              [s_sum_12181_loc ; r_sum_12182_loc ; a_sum_12183_loc])) [interface] _)) in
                      ({ code @ret ((result error_t unit_ChoiceEquality)) (
                          @inl unit_ChoiceEquality error_t (
                            (tt : unit_ChoiceEquality))) } : code (CEfset (
                            [s_sum_12181_loc ; r_sum_12182_loc ; a_sum_12183_loc])) [interface] _) } : code (
                        CEfset (
                          [s_sum_12181_loc ; r_sum_12182_loc ; a_sum_12183_loc])) [interface] _))
                  else ({ code @ret ((result error_t unit_ChoiceEquality)) (
                      @inl unit_ChoiceEquality error_t (
                        (tt : unit_ChoiceEquality))) } : code _ _ _) ) in
                ({ code bnd(ChoiceEqualityMonad.result_bind_code error_t , (
                      ed25519_field_element_t '×
                      ed25519_field_element_t '×
                      ed25519_field_element_t '×
                      ed25519_field_element_t
                    ) , _ , CEfset (
                      [s_sum_12181_loc ; r_sum_12182_loc ; a_sum_12183_loc])) r_12233 ⇠
                  (({ code  temp_12198 ←
                        (decompress (r_bytes_12196)) ;;
                       temp_12200 ←
                        (option_ok_or (temp_12198) (InvalidR)) ;;
                      @ret _ (temp_12200) } : code (CEfset (
                          [s_sum_12181_loc ; r_sum_12182_loc ; a_sum_12183_loc])) [interface
                      #val #[ DECOMPRESS ] : decompress_inp → decompress_out
                      ] _)) in
                  ({ code  '(s_12227 : scalar_t) ←
                      ( '(temp_12202 : seq uint8) ←
                          (array_to_seq (s_bytes_12193)) ;;
                         '(temp_12204 : scalar_t) ←
                          (nat_mod_from_byte_seq_le (temp_12202)) ;;
                        ret (temp_12204)) ;;
                     '(c_12238 : scalar_t) ←
                      ( '(temp_12206 : seq uint8) ←
                          (array_to_seq (pk_12171)) ;;
                         '(temp_12208 : seq uint8) ←
                          (array_concat (r_bytes_12196) (temp_12206)) ;;
                         '(temp_12211 : seq uint8) ←
                          (seq_concat (temp_12208) (msg_12209)) ;;
                         temp_12213 ←
                          (sha512 (temp_12211)) ;;
                         '(temp_12215 : scalar_t) ←
                          (scalar_from_hash (temp_12213)) ;;
                        ret (temp_12215)) ;;
                     '(z_12220 : seq uint8) ←
                      ( '(temp_12217 : uint_size) ←
                          ((usize 16) .* (i_12168)) ;;
                         '(temp_12219 : byte_seq) ←
                          (seq_slice (entropy_12150) (temp_12217) (usize 16)) ;;
                        ret (temp_12219)) ;;
                     '(z_12228 : scalar_t) ←
                      ( temp_12222 ←
                          (seq_new_ (default : uint8) (usize 16)) ;;
                         '(temp_12224 : seq uint8) ←
                          (seq_concat (z_12220) (temp_12222)) ;;
                         '(temp_12226 : scalar_t) ←
                          (nat_mod_from_byte_seq_le (temp_12224)) ;;
                        ret (temp_12226)) ;;
                     '(s_sum_12181 : scalar_t) ←
                        (( '(temp_12230 : scalar_t) ←
                              ((s_12227) *% (z_12228)) ;;
                             '(temp_12232 : scalar_t) ←
                              ((s_sum_12181) +% (temp_12230)) ;;
                            ret (temp_12232))) ;;
                      #put s_sum_12181_loc := s_sum_12181 ;;
                    
                     '(r_sum_12182 : (
                            ed25519_field_element_t '×
                            ed25519_field_element_t '×
                            ed25519_field_element_t '×
                            ed25519_field_element_t
                          )) ←
                        (( temp_12235 ←
                              (point_mul (z_12228) (r_12233)) ;;
                             temp_12237 ←
                              (point_add (r_sum_12182) (temp_12235)) ;;
                            ret (temp_12237))) ;;
                      #put r_sum_12182_loc := r_sum_12182 ;;
                    
                     '(a_sum_12183 : (
                            ed25519_field_element_t '×
                            ed25519_field_element_t '×
                            ed25519_field_element_t '×
                            ed25519_field_element_t
                          )) ←
                        (( '(temp_12240 : scalar_t) ←
                              ((z_12228) *% (c_12238)) ;;
                             temp_12242 ←
                              (point_mul (temp_12240) (a_12176)) ;;
                             temp_12244 ←
                              (point_add (a_sum_12183) (temp_12242)) ;;
                            ret (temp_12244))) ;;
                      #put a_sum_12183_loc := a_sum_12183 ;;
                    
                    @ret ((result error_t (
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
                        ))) (@inl (
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
                      ) error_t (prod_ce(s_sum_12181, r_sum_12182, a_sum_12183
                        ))) } : code (CEfset (
                        [s_sum_12181_loc ; r_sum_12182_loc ; a_sum_12183_loc])) [interface
                    #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
                    #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
                    #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
                    #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
                    #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
                    #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
                    #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
                    #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
                    CEfset (
                      [s_sum_12181_loc ; r_sum_12182_loc ; a_sum_12183_loc])) [interface
                  #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
                  #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
                  #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
                  #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
                  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
                  #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
                  #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
                  #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
                  CEfset (
                    [s_sum_12181_loc ; r_sum_12182_loc ; a_sum_12183_loc])) [interface
                #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
                #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
                #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
                #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
                #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
                #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
                #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
                #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
                CEfset (
                  [s_sum_12181_loc ; r_sum_12182_loc ; a_sum_12183_loc])) [interface
              #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
              #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
              #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
              #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
              #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
              #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
              #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
              #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (
              CEfset (
                [s_sum_12181_loc ; r_sum_12182_loc ; a_sum_12183_loc])) [interface
            #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
            #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
            #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
            #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
            #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
            #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
            #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
            #val #[ SHA512 ] : sha512_inp → sha512_out ] _))) in
        ({ code  '(b_12249 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              )) ←
            ( temp_12246 ←
                (decompress (base_v)) ;;
               temp_12248 ←
                (option_unwrap (temp_12246)) ;;
              ret (temp_12248)) ;;
           '(sb_12252 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              )) ←
            ( temp_12251 ←
                (point_mul (s_sum_12181) (b_12249)) ;;
              ret (temp_12251)) ;;
           '(check_12261 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              )) ←
            ( temp_12254 ←
                (point_neg (sb_12252)) ;;
               temp_12256 ←
                (point_add (r_sum_12182) (a_sum_12183)) ;;
               temp_12258 ←
                (point_add (temp_12254) (temp_12256)) ;;
               temp_12260 ←
                (point_mul_by_cofactor (temp_12258)) ;;
              ret (temp_12260)) ;;
           '(temp_12263 : bool_ChoiceEquality) ←
            (is_identity (check_12261)) ;;
          @ret ((result error_t unit_ChoiceEquality)) ((if (
                temp_12263):bool_ChoiceEquality then (*inline*) (
                @inl unit_ChoiceEquality error_t (tt)) else (
                @inr unit_ChoiceEquality error_t (
                  InvalidSignature)))) } : code (CEfset (
              [s_sum_12181_loc ; r_sum_12182_loc ; a_sum_12183_loc])) [interface
          #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
          #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
          #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
          #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
          #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
          #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
          #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
          #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (CEfset (
            [s_sum_12181_loc ; r_sum_12182_loc ; a_sum_12183_loc])) [interface
        #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
        #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
        #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
        #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
        #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ;
        #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
        #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
        #val #[ POINT_NEG ] : point_neg_inp → point_neg_out ;
        #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
        #val #[ SHA512 ] : sha512_inp → sha512_out ] _) } : code (CEfset (
          [s_sum_12181_loc ; r_sum_12182_loc ; a_sum_12183_loc])) [interface
      #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
      #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
      #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
      #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
      #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ;
      #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
      #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
      #val #[ POINT_NEG ] : point_neg_inp → point_neg_out ;
      #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
      #val #[ SHA512 ] : sha512_inp → sha512_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_alg3_batch_verify : package _ _ _ :=
  (seq_link alg3_batch_verify link_rest(
      package_check_canonical_scalar,package_decompress,package_is_identity,package_point_add,package_point_identity,package_point_mul,package_point_mul_by_cofactor,package_point_neg,package_scalar_from_hash,package_sha512)).
Fail Next Obligation.

