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
  2400.
Program Definition scalar_from_hash
  : both_package (fset.fset0) [interface] [(SCALAR_FROM_HASH,(
      scalar_from_hash_inp,scalar_from_hash_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(h_2398) := temp_inp : sha512_digest_t in
    
    ((letb s_2399 : big_scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 h_2398)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          nat_mod_from_byte_seq_le (seq_slice (nat_mod_to_byte_seq_le (
                lift_to_both0 s_2399)) (lift_to_both0 (usize 0)) (
              lift_to_both0 (usize 32))))
        ) : both (fset.fset0) [interface] (scalar_t)))in
  both_package' _ _ (SCALAR_FROM_HASH,(
      scalar_from_hash_inp,scalar_from_hash_out)) temp_package_both.
Fail Next Obligation.


Notation "'sign_inp'" :=(
  secret_key_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sign_inp'" :=(
  secret_key_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'sign_out'" :=(
  signature_t : choice_type) (in custom pack_type at level 2).
Notation "'sign_out'" :=(signature_t : ChoiceEquality) (at level 2).
Definition SIGN : nat :=
  2414.
Program Definition sign
  : both_package (fset.fset0) [interface
  #val #[ COMPRESS ] : compress_inp → compress_out ;
  #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
  #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
  #val #[ SECRET_EXPAND ] : secret_expand_inp → secret_expand_out ;
  #val #[ SHA512 ] : sha512_inp → sha512_out ] [(SIGN,(sign_inp,sign_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(sk_2401 , msg_2407) := temp_inp : secret_key_t '× byte_seq in
    
    let compress := fun x_0 => package_both compress (x_0) in
    let decompress := fun x_0 => package_both decompress (x_0) in
    let point_mul := fun x_0 x_1 => package_both point_mul (x_0,x_1) in
    let scalar_from_hash := fun x_0 => package_both scalar_from_hash (x_0) in
    let secret_expand := fun x_0 => package_both secret_expand (x_0) in
    let sha512 := fun x_0 => package_both sha512 (x_0) in
    ((letb '(a_2402, prefix_2403) : (serialized_scalar_t '× serialized_scalar_t
          ) :=
          secret_expand (lift_to_both0 sk_2401) in
        letb a_2404 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 a_2402)) in
        letb b_2405 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          option_unwrap (decompress (lift_to_both0 base_v)) in
        letb a_p_2406 : compressed_ed_point_t :=
          compress (point_mul (lift_to_both0 a_2404) (lift_to_both0 b_2405)) in
        letb r_2408 : scalar_t :=
          scalar_from_hash (sha512 (array_concat (lift_to_both0 prefix_2403) (
                lift_to_both0 msg_2407))) in
        letb r_p_2409 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          point_mul (lift_to_both0 r_2408) (lift_to_both0 b_2405) in
        letb r_s_2410 : compressed_ed_point_t :=
          compress (lift_to_both0 r_p_2409) in
        letb h_2411 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (
                  lift_to_both0 r_s_2410) (
                  array_to_seq (lift_to_both0 a_p_2406))) (
                lift_to_both0 msg_2407))) in
        letb s_2412 : scalar_t :=
          (lift_to_both0 r_2408) +% ((lift_to_both0 h_2411) *% (
              lift_to_both0 a_2404)) in
        letb s_bytes_2413 : seq uint8 :=
          seq_slice (nat_mod_to_byte_seq_le (lift_to_both0 s_2412)) (
            lift_to_both0 (usize 0)) (lift_to_both0 (usize 32)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_update (
            array_update (array_new_ (default : uint8) (64)) (lift_to_both0 (
                usize 0)) (array_to_seq (lift_to_both0 r_s_2410))) (
            lift_to_both0 (usize 32)) (lift_to_both0 s_bytes_2413))
        ) : both (fset.fset0) [interface
      #val #[ COMPRESS ] : compress_inp → compress_out ;
      #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
      #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
      #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
      #val #[ SECRET_EXPAND ] : secret_expand_inp → secret_expand_out ;
      #val #[ SHA512 ] : sha512_inp → sha512_out ] (signature_t)))in
  both_package' _ _ (SIGN,(sign_inp,sign_out)) temp_package_both.
Fail Next Obligation.


Notation "'zcash_verify_inp'" :=(
  public_key_t '× signature_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'zcash_verify_inp'" :=(
  public_key_t '× signature_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'zcash_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Notation "'zcash_verify_out'" :=(verify_result_t : ChoiceEquality) (at level 2).
Definition ZCASH_VERIFY : nat :=
  2428.
Program Definition zcash_verify
  : both_package (fset.fset0) [interface
  #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
  #val #[ DECOMPRESS_NON_CANONICAL ] : decompress_non_canonical_inp → decompress_non_canonical_out ;
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
  #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
  #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
  #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
  #val #[ SHA512 ] : sha512_inp → sha512_out ] [(ZCASH_VERIFY,(
      zcash_verify_inp,zcash_verify_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      pk_2416 , signature_2418 , msg_2423) := temp_inp : public_key_t '× signature_t '× byte_seq in
    
    let check_canonical_scalar := fun x_0 => package_both check_canonical_scalar (
      x_0) in
    let decompress_non_canonical := fun x_0 => package_both decompress_non_canonical (
      x_0) in
    let point_add := fun x_0 x_1 => package_both point_add (x_0,x_1) in
    let point_eq := fun x_0 x_1 => package_both point_eq (x_0,x_1) in
    let point_mul := fun x_0 x_1 => package_both point_mul (x_0,x_1) in
    let point_mul_by_cofactor := fun x_0 => package_both point_mul_by_cofactor (
      x_0) in
    let scalar_from_hash := fun x_0 => package_both scalar_from_hash (x_0) in
    let sha512 := fun x_0 => package_both sha512 (x_0) in
    ((letb b_2415 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          option_unwrap (decompress_non_canonical (lift_to_both0 base_v)) in
        letbnd(_) a_2417 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          option_ok_or (decompress_non_canonical (lift_to_both0 pk_2416)) (
            InvalidPublickey) in
        letb r_bytes_2419 : compressed_ed_point_t :=
          array_from_slice (default : uint8) (32) (
            array_to_seq (lift_to_both0 signature_2418)) (lift_to_both0 (
              usize 0)) (lift_to_both0 (usize 32)) in
        letb s_bytes_2420 : serialized_scalar_t :=
          array_from_slice (default : uint8) (32) (
            array_to_seq (lift_to_both0 signature_2418)) (lift_to_both0 (
              usize 32)) (lift_to_both0 (usize 32)) in
        letbnd(_) 'tt :=
          if negb (check_canonical_scalar (
              lift_to_both0 s_bytes_2420)) :bool_ChoiceEquality
          then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (I1 := [interface]) (I2 := [interface
          #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
          #val #[ DECOMPRESS_NON_CANONICAL ] : decompress_non_canonical_inp → decompress_non_canonical_out ;
          #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
          #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
          #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
          #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
          #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
          #val #[ SHA512 ] : sha512_inp → sha512_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
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
        letbnd(_) r_2421 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          option_ok_or (decompress_non_canonical (lift_to_both0 r_bytes_2419)) (
            InvalidR) in
        letb s_2422 : scalar_t :=
          nat_mod_from_byte_seq_le (
            array_to_seq (lift_to_both0 s_bytes_2420)) in
        letb k_2424 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (
                  lift_to_both0 r_bytes_2419) (lift_to_both0 pk_2416)) (
                lift_to_both0 msg_2423))) in
        letb sb_2425 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          point_mul_by_cofactor (point_mul (lift_to_both0 s_2422) (
              lift_to_both0 b_2415)) in
        letb rc_2426 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          point_mul_by_cofactor (lift_to_both0 r_2421) in
        letb ka_2427 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          point_mul_by_cofactor (point_mul (lift_to_both0 k_2424) (
              lift_to_both0 a_2417)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) (point_eq (lift_to_both0 sb_2425) (
              point_add (lift_to_both0 rc_2426) (lift_to_both0 ka_2427)))
          then @Ok unit_ChoiceEquality error_t (tt)
          else @Err unit_ChoiceEquality error_t (InvalidSignature))
        ) : both (fset.fset0) [interface
      #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
      #val #[ DECOMPRESS_NON_CANONICAL ] : decompress_non_canonical_inp → decompress_non_canonical_out ;
      #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
      #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
      #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
      #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
      #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
      #val #[ SHA512 ] : sha512_inp → sha512_out ] (verify_result_t)))in
  both_package' _ _ (ZCASH_VERIFY,(
      zcash_verify_inp,zcash_verify_out)) temp_package_both.
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
  2442.
Program Definition ietf_cofactored_verify
  : both_package (fset.fset0) [interface
  #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
  #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
  #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
  #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
  #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
  #val #[ SHA512 ] : sha512_inp → sha512_out ] [(IETF_COFACTORED_VERIFY,(
      ietf_cofactored_verify_inp,ietf_cofactored_verify_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      pk_2430 , signature_2432 , msg_2437) := temp_inp : public_key_t '× signature_t '× byte_seq in
    
    let check_canonical_scalar := fun x_0 => package_both check_canonical_scalar (
      x_0) in
    let decompress := fun x_0 => package_both decompress (x_0) in
    let point_add := fun x_0 x_1 => package_both point_add (x_0,x_1) in
    let point_eq := fun x_0 x_1 => package_both point_eq (x_0,x_1) in
    let point_mul := fun x_0 x_1 => package_both point_mul (x_0,x_1) in
    let point_mul_by_cofactor := fun x_0 => package_both point_mul_by_cofactor (
      x_0) in
    let scalar_from_hash := fun x_0 => package_both scalar_from_hash (x_0) in
    let sha512 := fun x_0 => package_both sha512 (x_0) in
    ((letb b_2429 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          option_unwrap (decompress (lift_to_both0 base_v)) in
        letbnd(_) a_2431 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          option_ok_or (decompress (lift_to_both0 pk_2430)) (
            InvalidPublickey) in
        letb r_bytes_2433 : compressed_ed_point_t :=
          array_from_slice (default : uint8) (32) (
            array_to_seq (lift_to_both0 signature_2432)) (lift_to_both0 (
              usize 0)) (lift_to_both0 (usize 32)) in
        letb s_bytes_2434 : serialized_scalar_t :=
          array_from_slice (default : uint8) (32) (
            array_to_seq (lift_to_both0 signature_2432)) (lift_to_both0 (
              usize 32)) (lift_to_both0 (usize 32)) in
        letbnd(_) 'tt :=
          if negb (check_canonical_scalar (
              lift_to_both0 s_bytes_2434)) :bool_ChoiceEquality
          then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (I1 := [interface]) (I2 := [interface
          #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
          #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
          #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
          #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
          #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
          #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
          #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
          #val #[ SHA512 ] : sha512_inp → sha512_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
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
        letbnd(_) r_2435 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          option_ok_or (decompress (lift_to_both0 r_bytes_2433)) (InvalidR) in
        letb s_2436 : scalar_t :=
          nat_mod_from_byte_seq_le (
            array_to_seq (lift_to_both0 s_bytes_2434)) in
        letb k_2438 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (
                  lift_to_both0 r_bytes_2433) (lift_to_both0 pk_2430)) (
                lift_to_both0 msg_2437))) in
        letb sb_2439 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          point_mul_by_cofactor (point_mul (lift_to_both0 s_2436) (
              lift_to_both0 b_2429)) in
        letb rc_2440 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          point_mul_by_cofactor (lift_to_both0 r_2435) in
        letb ka_2441 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          point_mul_by_cofactor (point_mul (lift_to_both0 k_2438) (
              lift_to_both0 a_2431)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) (point_eq (lift_to_both0 sb_2439) (
              point_add (lift_to_both0 rc_2440) (lift_to_both0 ka_2441)))
          then @Ok unit_ChoiceEquality error_t (tt)
          else @Err unit_ChoiceEquality error_t (InvalidSignature))
        ) : both (fset.fset0) [interface
      #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
      #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
      #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
      #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
      #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
      #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
      #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
      #val #[ SHA512 ] : sha512_inp → sha512_out ] (verify_result_t)))in
  both_package' _ _ (IETF_COFACTORED_VERIFY,(
      ietf_cofactored_verify_inp,ietf_cofactored_verify_out)) temp_package_both.
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
  2455.
Program Definition ietf_cofactorless_verify
  : both_package (fset.fset0) [interface
  #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
  #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
  #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
  #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
  #val #[ SHA512 ] : sha512_inp → sha512_out ] [(IETF_COFACTORLESS_VERIFY,(
      ietf_cofactorless_verify_inp,ietf_cofactorless_verify_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      pk_2444 , signature_2446 , msg_2451) := temp_inp : public_key_t '× signature_t '× byte_seq in
    
    let check_canonical_scalar := fun x_0 => package_both check_canonical_scalar (
      x_0) in
    let decompress := fun x_0 => package_both decompress (x_0) in
    let point_add := fun x_0 x_1 => package_both point_add (x_0,x_1) in
    let point_eq := fun x_0 x_1 => package_both point_eq (x_0,x_1) in
    let point_mul := fun x_0 x_1 => package_both point_mul (x_0,x_1) in
    let scalar_from_hash := fun x_0 => package_both scalar_from_hash (x_0) in
    let sha512 := fun x_0 => package_both sha512 (x_0) in
    ((letb b_2443 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          option_unwrap (decompress (lift_to_both0 base_v)) in
        letbnd(_) a_2445 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          option_ok_or (decompress (lift_to_both0 pk_2444)) (
            InvalidPublickey) in
        letb r_bytes_2447 : compressed_ed_point_t :=
          array_from_slice (default : uint8) (32) (
            array_to_seq (lift_to_both0 signature_2446)) (lift_to_both0 (
              usize 0)) (lift_to_both0 (usize 32)) in
        letb s_bytes_2448 : serialized_scalar_t :=
          array_from_slice (default : uint8) (32) (
            array_to_seq (lift_to_both0 signature_2446)) (lift_to_both0 (
              usize 32)) (lift_to_both0 (usize 32)) in
        letbnd(_) 'tt :=
          if negb (check_canonical_scalar (
              lift_to_both0 s_bytes_2448)) :bool_ChoiceEquality
          then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (I1 := [interface]) (I2 := [interface
          #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
          #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
          #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
          #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
          #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
          #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
          #val #[ SHA512 ] : sha512_inp → sha512_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
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
        letbnd(_) r_2449 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          option_ok_or (decompress (lift_to_both0 r_bytes_2447)) (InvalidR) in
        letb s_2450 : scalar_t :=
          nat_mod_from_byte_seq_le (
            array_to_seq (lift_to_both0 s_bytes_2448)) in
        letb k_2452 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (
                  lift_to_both0 r_bytes_2447) (lift_to_both0 pk_2444)) (
                lift_to_both0 msg_2451))) in
        letb sb_2453 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          point_mul (lift_to_both0 s_2450) (lift_to_both0 b_2443) in
        letb ka_2454 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          point_mul (lift_to_both0 k_2452) (lift_to_both0 a_2445) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) (point_eq (lift_to_both0 sb_2453) (
              point_add (lift_to_both0 r_2449) (lift_to_both0 ka_2454)))
          then @Ok unit_ChoiceEquality error_t (tt)
          else @Err unit_ChoiceEquality error_t (InvalidSignature))
        ) : both (fset.fset0) [interface
      #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
      #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
      #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
      #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
      #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
      #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
      #val #[ SHA512 ] : sha512_inp → sha512_out ] (verify_result_t)))in
  both_package' _ _ (IETF_COFACTORLESS_VERIFY,(
      ietf_cofactorless_verify_inp,ietf_cofactorless_verify_out)) temp_package_both.
Fail Next Obligation.


Notation "'is_identity_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'is_identity_inp'" :=(ed_point_t : ChoiceEquality) (at level 2).
Notation "'is_identity_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'is_identity_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition IS_IDENTITY : nat :=
  2457.
Program Definition is_identity
  : both_package (fset.fset0) [interface
  #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
  #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ] [(
    IS_IDENTITY,(is_identity_inp,is_identity_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_2456) := temp_inp : ed_point_t in
    
    let point_eq := fun x_0 x_1 => package_both point_eq (x_0,x_1) in
    let point_identity := package_both point_identity tt in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (point_eq (
            lift_to_both0 p_2456) (point_identity ))
        ) : both (fset.fset0) [interface
      #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
      #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ] (
        bool_ChoiceEquality)))in
  both_package' _ _ (IS_IDENTITY,(
      is_identity_inp,is_identity_out)) temp_package_both.
Fail Next Obligation.


Notation "'alg2_verify_inp'" :=(
  public_key_t '× signature_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'alg2_verify_inp'" :=(
  public_key_t '× signature_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'alg2_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Notation "'alg2_verify_out'" :=(verify_result_t : ChoiceEquality) (at level 2).
Definition ALG2_VERIFY : nat :=
  2471.
Program Definition alg2_verify
  : both_package (fset.fset0) [interface
  #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
  #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
  #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
  #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
  #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
  #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
  #val #[ SHA512 ] : sha512_inp → sha512_out ] [(ALG2_VERIFY,(
      alg2_verify_inp,alg2_verify_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      pk_2459 , signature_2461 , msg_2466) := temp_inp : public_key_t '× signature_t '× byte_seq in
    
    let check_canonical_scalar := fun x_0 => package_both check_canonical_scalar (
      x_0) in
    let decompress := fun x_0 => package_both decompress (x_0) in
    let is_identity := fun x_0 => package_both is_identity (x_0) in
    let point_add := fun x_0 x_1 => package_both point_add (x_0,x_1) in
    let point_eq := fun x_0 x_1 => package_both point_eq (x_0,x_1) in
    let point_mul := fun x_0 x_1 => package_both point_mul (x_0,x_1) in
    let point_mul_by_cofactor := fun x_0 => package_both point_mul_by_cofactor (
      x_0) in
    let scalar_from_hash := fun x_0 => package_both scalar_from_hash (x_0) in
    let sha512 := fun x_0 => package_both sha512 (x_0) in
    ((letb b_2458 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          option_unwrap (decompress (lift_to_both0 base_v)) in
        letbnd(_) a_2460 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          option_ok_or (decompress (lift_to_both0 pk_2459)) (
            InvalidPublickey) in
        letbnd(_) 'tt :=
          if is_identity (point_mul_by_cofactor (
              lift_to_both0 a_2460)) :bool_ChoiceEquality
          then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (I1 := [interface]) (I2 := [interface
          #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
          #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
          #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
          #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
          #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
          #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
          #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
          #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
          #val #[ SHA512 ] : sha512_inp → sha512_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
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
        letb r_bytes_2462 : compressed_ed_point_t :=
          array_from_slice (default : uint8) (32) (
            array_to_seq (lift_to_both0 signature_2461)) (lift_to_both0 (
              usize 0)) (lift_to_both0 (usize 32)) in
        letb s_bytes_2463 : serialized_scalar_t :=
          array_from_slice (default : uint8) (32) (
            array_to_seq (lift_to_both0 signature_2461)) (lift_to_both0 (
              usize 32)) (lift_to_both0 (usize 32)) in
        letbnd(_) 'tt :=
          if negb (check_canonical_scalar (
              lift_to_both0 s_bytes_2463)) :bool_ChoiceEquality
          then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (I1 := [interface]) (I2 := [interface
          #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
          #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
          #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
          #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
          #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
          #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
          #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
          #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
          #val #[ SHA512 ] : sha512_inp → sha512_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
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
        letbnd(_) r_2464 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          option_ok_or (decompress (lift_to_both0 r_bytes_2462)) (InvalidR) in
        letb s_2465 : scalar_t :=
          nat_mod_from_byte_seq_le (
            array_to_seq (lift_to_both0 s_bytes_2463)) in
        letb k_2467 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (
                  lift_to_both0 r_bytes_2462) (lift_to_both0 pk_2459)) (
                lift_to_both0 msg_2466))) in
        letb sb_2468 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          point_mul_by_cofactor (point_mul (lift_to_both0 s_2465) (
              lift_to_both0 b_2458)) in
        letb rc_2469 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          point_mul_by_cofactor (lift_to_both0 r_2464) in
        letb ka_2470 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          point_mul_by_cofactor (point_mul (lift_to_both0 k_2467) (
              lift_to_both0 a_2460)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) (point_eq (lift_to_both0 sb_2468) (
              point_add (lift_to_both0 rc_2469) (lift_to_both0 ka_2470)))
          then @Ok unit_ChoiceEquality error_t (tt)
          else @Err unit_ChoiceEquality error_t (InvalidSignature))
        ) : both (fset.fset0) [interface
      #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
      #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
      #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
      #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
      #val #[ POINT_EQ ] : point_eq_inp → point_eq_out ;
      #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
      #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
      #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
      #val #[ SHA512 ] : sha512_inp → sha512_out ] (verify_result_t)))in
  both_package' _ _ (ALG2_VERIFY,(
      alg2_verify_inp,alg2_verify_out)) temp_package_both.
Fail Next Obligation.

Definition batch_entry_t : ChoiceEquality :=
  (public_key_t '× byte_seq '× signature_t).
Definition BatchEntry (x : (public_key_t '× byte_seq '× signature_t
    )) : batch_entry_t :=
   x.

Definition s_sum_2472_loc : ChoiceEqualityLocation :=
  (scalar_t ; 2475%nat).
Definition r_sum_2473_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2476%nat).
Definition a_sum_2474_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2477%nat).
Notation "'zcash_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'zcash_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'zcash_batch_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Notation "'zcash_batch_verify_out'" :=(
  verify_result_t : ChoiceEquality) (at level 2).
Definition ZCASH_BATCH_VERIFY : nat :=
  2495.
Program Definition zcash_batch_verify
  : both_package (CEfset (
      [s_sum_2472_loc ; r_sum_2473_loc ; a_sum_2474_loc])) [interface
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
  #val #[ SHA512 ] : sha512_inp → sha512_out ] [(ZCASH_BATCH_VERIFY,(
      zcash_batch_verify_inp,zcash_batch_verify_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      entries_2479 , entropy_2478) := temp_inp : seq batch_entry_t '× byte_seq in
    
    let check_canonical_scalar := fun x_0 => package_both check_canonical_scalar (
      x_0) in
    let decompress := fun x_0 => package_both decompress (x_0) in
    let decompress_non_canonical := fun x_0 => package_both decompress_non_canonical (
      x_0) in
    let is_identity := fun x_0 => package_both is_identity (x_0) in
    let point_add := fun x_0 x_1 => package_both point_add (x_0,x_1) in
    let point_identity := package_both point_identity tt in
    let point_mul := fun x_0 x_1 => package_both point_mul (x_0,x_1) in
    let point_mul_by_cofactor := fun x_0 => package_both point_mul_by_cofactor (
      x_0) in
    let point_neg := fun x_0 => package_both point_neg (x_0) in
    let scalar_from_hash := fun x_0 => package_both scalar_from_hash (x_0) in
    let sha512 := fun x_0 => package_both sha512 (x_0) in
    ((letbnd(_) 'tt :=
          if (seq_len (lift_to_both0 entropy_2478)) <.? ((lift_to_both0 (
                usize 16)) .* (seq_len (
                lift_to_both0 entries_2479))) :bool_ChoiceEquality
          then lift_scope (L1 := fset.fset0) (L2 := CEfset (
            [s_sum_2472_loc ; r_sum_2473_loc ; a_sum_2474_loc])) (I1 := [interface]) (I2 := [interface
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
          #val #[ SHA512 ] : sha512_inp → sha512_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
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
        letbm s_sum_2472 : scalar_t loc( s_sum_2472_loc ) := nat_mod_zero  in
        letbm r_sum_2473 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) loc( r_sum_2473_loc ) :=
          point_identity  in
        letbm a_sum_2474 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) loc( a_sum_2474_loc ) :=
          point_identity  in
        letbnd(_) '(s_sum_2472, r_sum_2473, a_sum_2474) :=
          foldi_bind_both' (lift_to_both0 (usize 0)) (seq_len (
                lift_to_both0 entries_2479)) prod_ce(
              s_sum_2472,
              r_sum_2473,
              a_sum_2474
            ) (L := (CEfset (
                [s_sum_2472_loc ; r_sum_2473_loc ; a_sum_2474_loc]))) (I := (
              [interface
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
              #val #[ SHA512 ] : sha512_inp → sha512_out ])) (fun i_2480 '(
              s_sum_2472,
              r_sum_2473,
              a_sum_2474
            ) =>
            letb BatchEntry ((pk_2481, msg_2482, signature_2483
                )) : batch_entry_t :=
              (seq_index (entries_2479) (lift_to_both0 i_2480)) in
            letbnd(_) a_2484 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress_non_canonical (lift_to_both0 pk_2481)) (
                InvalidPublickey) in
            letb r_bytes_2485 : compressed_ed_point_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2483)) (lift_to_both0 (
                  usize 0)) (lift_to_both0 (usize 32)) in
            letb s_bytes_2486 : serialized_scalar_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2483)) (lift_to_both0 (
                  usize 32)) (lift_to_both0 (usize 32)) in
            letbnd(_) 'tt :=
              if negb (check_canonical_scalar (
                  lift_to_both0 s_bytes_2486)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                [s_sum_2472_loc ; r_sum_2473_loc ; a_sum_2474_loc])) (L2 := CEfset (
                [s_sum_2472_loc ; r_sum_2473_loc ; a_sum_2474_loc])) (I1 := [interface]) (I2 := [interface
              #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
              #val #[ DECOMPRESS_NON_CANONICAL ] : decompress_non_canonical_inp → decompress_non_canonical_out ;
              #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
              #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
              #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
              #val #[ SHA512 ] : sha512_inp → sha512_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
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
            letbnd(_) r_2487 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress_non_canonical (
                  lift_to_both0 r_bytes_2485)) (InvalidR) in
            letb s_2488 : scalar_t :=
              nat_mod_from_byte_seq_le (
                array_to_seq (lift_to_both0 s_bytes_2486)) in
            letb c_2489 : scalar_t :=
              scalar_from_hash (sha512 (seq_concat (array_concat (
                      lift_to_both0 r_bytes_2485) (
                      array_to_seq (lift_to_both0 pk_2481))) (
                    lift_to_both0 msg_2482))) in
            letb z_2490 : seq uint8 :=
              seq_slice (lift_to_both0 entropy_2478) ((lift_to_both0 (
                    usize 16)) .* (lift_to_both0 i_2480)) (lift_to_both0 (
                  usize 16)) in
            letb z_2491 : scalar_t :=
              nat_mod_from_byte_seq_le (seq_concat (lift_to_both0 z_2490) (
                  seq_new_ (default : uint8) (lift_to_both0 (usize 16)))) in
            letbm s_sum_2472 loc( s_sum_2472_loc ) :=
              (lift_to_both0 s_sum_2472) +% ((lift_to_both0 s_2488) *% (
                  lift_to_both0 z_2491)) in
            letbm r_sum_2473 loc( r_sum_2473_loc ) :=
              point_add (lift_to_both0 r_sum_2473) (point_mul (
                  lift_to_both0 z_2491) (lift_to_both0 r_2487)) in
            letbm a_sum_2474 loc( a_sum_2474_loc ) :=
              point_add (lift_to_both0 a_sum_2474) (point_mul ((
                    lift_to_both0 z_2491) *% (lift_to_both0 c_2489)) (
                  lift_to_both0 a_2484)) in
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
                  lift_to_both0 s_sum_2472,
                  lift_to_both0 r_sum_2473,
                  lift_to_both0 a_sum_2474
                )))
            ) in
        letb b_2492 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          option_unwrap (decompress (lift_to_both0 base_v)) in
        letb sb_2493 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          point_mul (lift_to_both0 s_sum_2472) (lift_to_both0 b_2492) in
        letb check_2494 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          point_mul_by_cofactor (point_add (point_neg (lift_to_both0 sb_2493)) (
              point_add (lift_to_both0 r_sum_2473) (
                lift_to_both0 a_sum_2474))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) (is_identity (lift_to_both0 check_2494))
          then @Ok unit_ChoiceEquality error_t (tt)
          else @Err unit_ChoiceEquality error_t (InvalidSignature))
        ) : both (CEfset (
          [s_sum_2472_loc ; r_sum_2473_loc ; a_sum_2474_loc])) [interface
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
      #val #[ SHA512 ] : sha512_inp → sha512_out ] (verify_result_t)))in
  both_package' _ _ (ZCASH_BATCH_VERIFY,(
      zcash_batch_verify_inp,zcash_batch_verify_out)) temp_package_both.
Fail Next Obligation.

Definition a_sum_2498_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2499%nat).
Definition r_sum_2497_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2500%nat).
Definition s_sum_2496_loc : ChoiceEqualityLocation :=
  (scalar_t ; 2501%nat).
Notation "'ietf_cofactored_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactored_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'ietf_cofactored_batch_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactored_batch_verify_out'" :=(
  verify_result_t : ChoiceEquality) (at level 2).
Definition IETF_COFACTORED_BATCH_VERIFY : nat :=
  2519.
Program Definition ietf_cofactored_batch_verify
  : both_package (CEfset (
      [s_sum_2496_loc ; r_sum_2497_loc ; a_sum_2498_loc])) [interface
  #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
  #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
  #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
  #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ;
  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
  #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
  #val #[ POINT_NEG ] : point_neg_inp → point_neg_out ;
  #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
  #val #[ SHA512 ] : sha512_inp → sha512_out ] [(
    IETF_COFACTORED_BATCH_VERIFY,(
      ietf_cofactored_batch_verify_inp,ietf_cofactored_batch_verify_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      entries_2503 , entropy_2502) := temp_inp : seq batch_entry_t '× byte_seq in
    
    let check_canonical_scalar := fun x_0 => package_both check_canonical_scalar (
      x_0) in
    let decompress := fun x_0 => package_both decompress (x_0) in
    let is_identity := fun x_0 => package_both is_identity (x_0) in
    let point_add := fun x_0 x_1 => package_both point_add (x_0,x_1) in
    let point_identity := package_both point_identity tt in
    let point_mul := fun x_0 x_1 => package_both point_mul (x_0,x_1) in
    let point_mul_by_cofactor := fun x_0 => package_both point_mul_by_cofactor (
      x_0) in
    let point_neg := fun x_0 => package_both point_neg (x_0) in
    let scalar_from_hash := fun x_0 => package_both scalar_from_hash (x_0) in
    let sha512 := fun x_0 => package_both sha512 (x_0) in
    ((letbnd(_) 'tt :=
          if (seq_len (lift_to_both0 entropy_2502)) <.? ((lift_to_both0 (
                usize 16)) .* (seq_len (
                lift_to_both0 entries_2503))) :bool_ChoiceEquality
          then lift_scope (L1 := fset.fset0) (L2 := CEfset (
            [s_sum_2496_loc ; r_sum_2497_loc ; a_sum_2498_loc])) (I1 := [interface]) (I2 := [interface
          #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
          #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
          #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
          #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
          #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ;
          #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
          #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
          #val #[ POINT_NEG ] : point_neg_inp → point_neg_out ;
          #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
          #val #[ SHA512 ] : sha512_inp → sha512_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
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
        letbm s_sum_2496 : scalar_t loc( s_sum_2496_loc ) := nat_mod_zero  in
        letbm r_sum_2497 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) loc( r_sum_2497_loc ) :=
          point_identity  in
        letbm a_sum_2498 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) loc( a_sum_2498_loc ) :=
          point_identity  in
        letbnd(_) '(s_sum_2496, r_sum_2497, a_sum_2498) :=
          foldi_bind_both' (lift_to_both0 (usize 0)) (seq_len (
                lift_to_both0 entries_2503)) prod_ce(
              s_sum_2496,
              r_sum_2497,
              a_sum_2498
            ) (L := (CEfset (
                [s_sum_2496_loc ; r_sum_2497_loc ; a_sum_2498_loc]))) (I := (
              [interface
              #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
              #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
              #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
              #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
              #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ;
              #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
              #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
              #val #[ POINT_NEG ] : point_neg_inp → point_neg_out ;
              #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
              #val #[ SHA512 ] : sha512_inp → sha512_out ])) (fun i_2504 '(
              s_sum_2496,
              r_sum_2497,
              a_sum_2498
            ) =>
            letb BatchEntry ((pk_2505, msg_2506, signature_2507
                )) : batch_entry_t :=
              (seq_index (entries_2503) (lift_to_both0 i_2504)) in
            letbnd(_) a_2508 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 pk_2505)) (
                InvalidPublickey) in
            letb r_bytes_2509 : compressed_ed_point_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2507)) (lift_to_both0 (
                  usize 0)) (lift_to_both0 (usize 32)) in
            letb s_bytes_2510 : serialized_scalar_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2507)) (lift_to_both0 (
                  usize 32)) (lift_to_both0 (usize 32)) in
            letbnd(_) 'tt :=
              if negb (check_canonical_scalar (
                  lift_to_both0 s_bytes_2510)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                [s_sum_2496_loc ; r_sum_2497_loc ; a_sum_2498_loc])) (L2 := CEfset (
                [s_sum_2496_loc ; r_sum_2497_loc ; a_sum_2498_loc])) (I1 := [interface]) (I2 := [interface
              #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
              #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
              #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
              #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
              #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
              #val #[ SHA512 ] : sha512_inp → sha512_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
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
            letbnd(_) r_2511 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 r_bytes_2509)) (
                InvalidR) in
            letb s_2512 : scalar_t :=
              nat_mod_from_byte_seq_le (
                array_to_seq (lift_to_both0 s_bytes_2510)) in
            letb c_2513 : scalar_t :=
              scalar_from_hash (sha512 (seq_concat (array_concat (
                      lift_to_both0 r_bytes_2509) (
                      array_to_seq (lift_to_both0 pk_2505))) (
                    lift_to_both0 msg_2506))) in
            letb z_2514 : seq uint8 :=
              seq_slice (lift_to_both0 entropy_2502) ((lift_to_both0 (
                    usize 16)) .* (lift_to_both0 i_2504)) (lift_to_both0 (
                  usize 16)) in
            letb z_2515 : scalar_t :=
              nat_mod_from_byte_seq_le (seq_concat (lift_to_both0 z_2514) (
                  seq_new_ (default : uint8) (lift_to_both0 (usize 16)))) in
            letbm s_sum_2496 loc( s_sum_2496_loc ) :=
              (lift_to_both0 s_sum_2496) +% ((lift_to_both0 s_2512) *% (
                  lift_to_both0 z_2515)) in
            letbm r_sum_2497 loc( r_sum_2497_loc ) :=
              point_add (lift_to_both0 r_sum_2497) (point_mul (
                  lift_to_both0 z_2515) (lift_to_both0 r_2511)) in
            letbm a_sum_2498 loc( a_sum_2498_loc ) :=
              point_add (lift_to_both0 a_sum_2498) (point_mul ((
                    lift_to_both0 z_2515) *% (lift_to_both0 c_2513)) (
                  lift_to_both0 a_2508)) in
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
                  lift_to_both0 s_sum_2496,
                  lift_to_both0 r_sum_2497,
                  lift_to_both0 a_sum_2498
                )))
            ) in
        letb b_2516 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          option_unwrap (decompress (lift_to_both0 base_v)) in
        letb sb_2517 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          point_mul (lift_to_both0 s_sum_2496) (lift_to_both0 b_2516) in
        letb check_2518 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          point_mul_by_cofactor (point_add (point_neg (lift_to_both0 sb_2517)) (
              point_add (lift_to_both0 r_sum_2497) (
                lift_to_both0 a_sum_2498))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) (is_identity (lift_to_both0 check_2518))
          then @Ok unit_ChoiceEquality error_t (tt)
          else @Err unit_ChoiceEquality error_t (InvalidSignature))
        ) : both (CEfset (
          [s_sum_2496_loc ; r_sum_2497_loc ; a_sum_2498_loc])) [interface
      #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
      #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
      #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
      #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
      #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ;
      #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
      #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
      #val #[ POINT_NEG ] : point_neg_inp → point_neg_out ;
      #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
      #val #[ SHA512 ] : sha512_inp → sha512_out ] (verify_result_t)))in
  both_package' _ _ (IETF_COFACTORED_BATCH_VERIFY,(
      ietf_cofactored_batch_verify_inp,ietf_cofactored_batch_verify_out)) temp_package_both.
Fail Next Obligation.

Definition a_sum_2522_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2523%nat).
Definition s_sum_2520_loc : ChoiceEqualityLocation :=
  (scalar_t ; 2524%nat).
Definition r_sum_2521_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2525%nat).
Notation "'ietf_cofactorless_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactorless_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'ietf_cofactorless_batch_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Notation "'ietf_cofactorless_batch_verify_out'" :=(
  verify_result_t : ChoiceEquality) (at level 2).
Definition IETF_COFACTORLESS_BATCH_VERIFY : nat :=
  2543.
Program Definition ietf_cofactorless_batch_verify
  : both_package (CEfset (
      [s_sum_2520_loc ; r_sum_2521_loc ; a_sum_2522_loc])) [interface
  #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
  #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
  #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
  #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ;
  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
  #val #[ POINT_NEG ] : point_neg_inp → point_neg_out ;
  #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
  #val #[ SHA512 ] : sha512_inp → sha512_out ] [(
    IETF_COFACTORLESS_BATCH_VERIFY,(
      ietf_cofactorless_batch_verify_inp,ietf_cofactorless_batch_verify_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      entries_2527 , entropy_2526) := temp_inp : seq batch_entry_t '× byte_seq in
    
    let check_canonical_scalar := fun x_0 => package_both check_canonical_scalar (
      x_0) in
    let decompress := fun x_0 => package_both decompress (x_0) in
    let is_identity := fun x_0 => package_both is_identity (x_0) in
    let point_add := fun x_0 x_1 => package_both point_add (x_0,x_1) in
    let point_identity := package_both point_identity tt in
    let point_mul := fun x_0 x_1 => package_both point_mul (x_0,x_1) in
    let point_neg := fun x_0 => package_both point_neg (x_0) in
    let scalar_from_hash := fun x_0 => package_both scalar_from_hash (x_0) in
    let sha512 := fun x_0 => package_both sha512 (x_0) in
    ((letbnd(_) 'tt :=
          if (seq_len (lift_to_both0 entropy_2526)) <.? ((lift_to_both0 (
                usize 16)) .* (seq_len (
                lift_to_both0 entries_2527))) :bool_ChoiceEquality
          then lift_scope (L1 := fset.fset0) (L2 := CEfset (
            [s_sum_2520_loc ; r_sum_2521_loc ; a_sum_2522_loc])) (I1 := [interface]) (I2 := [interface
          #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
          #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
          #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
          #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
          #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ;
          #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
          #val #[ POINT_NEG ] : point_neg_inp → point_neg_out ;
          #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
          #val #[ SHA512 ] : sha512_inp → sha512_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
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
        letbm s_sum_2520 : scalar_t loc( s_sum_2520_loc ) := nat_mod_zero  in
        letbm r_sum_2521 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) loc( r_sum_2521_loc ) :=
          point_identity  in
        letbm a_sum_2522 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) loc( a_sum_2522_loc ) :=
          point_identity  in
        letbnd(_) '(s_sum_2520, r_sum_2521, a_sum_2522) :=
          foldi_bind_both' (lift_to_both0 (usize 0)) (seq_len (
                lift_to_both0 entries_2527)) prod_ce(
              s_sum_2520,
              r_sum_2521,
              a_sum_2522
            ) (L := (CEfset (
                [s_sum_2520_loc ; r_sum_2521_loc ; a_sum_2522_loc]))) (I := (
              [interface
              #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
              #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
              #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
              #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
              #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ;
              #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
              #val #[ POINT_NEG ] : point_neg_inp → point_neg_out ;
              #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
              #val #[ SHA512 ] : sha512_inp → sha512_out ])) (fun i_2528 '(
              s_sum_2520,
              r_sum_2521,
              a_sum_2522
            ) =>
            letb BatchEntry ((pk_2529, msg_2530, signature_2531
                )) : batch_entry_t :=
              (seq_index (entries_2527) (lift_to_both0 i_2528)) in
            letbnd(_) a_2532 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 pk_2529)) (
                InvalidPublickey) in
            letb r_bytes_2533 : compressed_ed_point_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2531)) (lift_to_both0 (
                  usize 0)) (lift_to_both0 (usize 32)) in
            letb s_bytes_2534 : serialized_scalar_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2531)) (lift_to_both0 (
                  usize 32)) (lift_to_both0 (usize 32)) in
            letbnd(_) 'tt :=
              if negb (check_canonical_scalar (
                  lift_to_both0 s_bytes_2534)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                [s_sum_2520_loc ; r_sum_2521_loc ; a_sum_2522_loc])) (L2 := CEfset (
                [s_sum_2520_loc ; r_sum_2521_loc ; a_sum_2522_loc])) (I1 := [interface]) (I2 := [interface
              #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
              #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
              #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
              #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
              #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
              #val #[ SHA512 ] : sha512_inp → sha512_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
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
            letbnd(_) r_2535 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 r_bytes_2533)) (
                InvalidR) in
            letb s_2536 : scalar_t :=
              nat_mod_from_byte_seq_le (
                array_to_seq (lift_to_both0 s_bytes_2534)) in
            letb c_2537 : scalar_t :=
              scalar_from_hash (sha512 (seq_concat (array_concat (
                      lift_to_both0 r_bytes_2533) (
                      array_to_seq (lift_to_both0 pk_2529))) (
                    lift_to_both0 msg_2530))) in
            letb z_2538 : seq uint8 :=
              seq_slice (lift_to_both0 entropy_2526) ((lift_to_both0 (
                    usize 16)) .* (lift_to_both0 i_2528)) (lift_to_both0 (
                  usize 16)) in
            letb z_2539 : scalar_t :=
              nat_mod_from_byte_seq_le (seq_concat (lift_to_both0 z_2538) (
                  seq_new_ (default : uint8) (lift_to_both0 (usize 16)))) in
            letbm s_sum_2520 loc( s_sum_2520_loc ) :=
              (lift_to_both0 s_sum_2520) +% ((lift_to_both0 s_2536) *% (
                  lift_to_both0 z_2539)) in
            letbm r_sum_2521 loc( r_sum_2521_loc ) :=
              point_add (lift_to_both0 r_sum_2521) (point_mul (
                  lift_to_both0 z_2539) (lift_to_both0 r_2535)) in
            letbm a_sum_2522 loc( a_sum_2522_loc ) :=
              point_add (lift_to_both0 a_sum_2522) (point_mul ((
                    lift_to_both0 z_2539) *% (lift_to_both0 c_2537)) (
                  lift_to_both0 a_2532)) in
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
                  lift_to_both0 s_sum_2520,
                  lift_to_both0 r_sum_2521,
                  lift_to_both0 a_sum_2522
                )))
            ) in
        letb b_2540 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          option_unwrap (decompress (lift_to_both0 base_v)) in
        letb sb_2541 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          point_mul (lift_to_both0 s_sum_2520) (lift_to_both0 b_2540) in
        letb check_2542 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          point_add (point_neg (lift_to_both0 sb_2541)) (point_add (
              lift_to_both0 r_sum_2521) (lift_to_both0 a_sum_2522)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) (is_identity (lift_to_both0 check_2542))
          then @Ok unit_ChoiceEquality error_t (tt)
          else @Err unit_ChoiceEquality error_t (InvalidSignature))
        ) : both (CEfset (
          [s_sum_2520_loc ; r_sum_2521_loc ; a_sum_2522_loc])) [interface
      #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
      #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
      #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
      #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
      #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ;
      #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
      #val #[ POINT_NEG ] : point_neg_inp → point_neg_out ;
      #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
      #val #[ SHA512 ] : sha512_inp → sha512_out ] (verify_result_t)))in
  both_package' _ _ (IETF_COFACTORLESS_BATCH_VERIFY,(
      ietf_cofactorless_batch_verify_inp,ietf_cofactorless_batch_verify_out)) temp_package_both.
Fail Next Obligation.

Definition r_sum_2545_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2547%nat).
Definition s_sum_2544_loc : ChoiceEqualityLocation :=
  (scalar_t ; 2548%nat).
Definition a_sum_2546_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2549%nat).
Notation "'alg3_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'alg3_batch_verify_inp'" :=(
  seq batch_entry_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'alg3_batch_verify_out'" :=(
  verify_result_t : choice_type) (in custom pack_type at level 2).
Notation "'alg3_batch_verify_out'" :=(
  verify_result_t : ChoiceEquality) (at level 2).
Definition ALG3_BATCH_VERIFY : nat :=
  2567.
Program Definition alg3_batch_verify
  : both_package (CEfset (
      [s_sum_2544_loc ; r_sum_2545_loc ; a_sum_2546_loc])) [interface
  #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
  #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
  #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
  #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ;
  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
  #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
  #val #[ POINT_NEG ] : point_neg_inp → point_neg_out ;
  #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
  #val #[ SHA512 ] : sha512_inp → sha512_out ] [(ALG3_BATCH_VERIFY,(
      alg3_batch_verify_inp,alg3_batch_verify_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      entries_2551 , entropy_2550) := temp_inp : seq batch_entry_t '× byte_seq in
    
    let check_canonical_scalar := fun x_0 => package_both check_canonical_scalar (
      x_0) in
    let decompress := fun x_0 => package_both decompress (x_0) in
    let is_identity := fun x_0 => package_both is_identity (x_0) in
    let point_add := fun x_0 x_1 => package_both point_add (x_0,x_1) in
    let point_identity := package_both point_identity tt in
    let point_mul := fun x_0 x_1 => package_both point_mul (x_0,x_1) in
    let point_mul_by_cofactor := fun x_0 => package_both point_mul_by_cofactor (
      x_0) in
    let point_neg := fun x_0 => package_both point_neg (x_0) in
    let scalar_from_hash := fun x_0 => package_both scalar_from_hash (x_0) in
    let sha512 := fun x_0 => package_both sha512 (x_0) in
    ((letbnd(_) 'tt :=
          if (seq_len (lift_to_both0 entropy_2550)) <.? ((lift_to_both0 (
                usize 16)) .* (seq_len (
                lift_to_both0 entries_2551))) :bool_ChoiceEquality
          then lift_scope (L1 := fset.fset0) (L2 := CEfset (
            [s_sum_2544_loc ; r_sum_2545_loc ; a_sum_2546_loc])) (I1 := [interface]) (I2 := [interface
          #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
          #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
          #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
          #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
          #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ;
          #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
          #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
          #val #[ POINT_NEG ] : point_neg_inp → point_neg_out ;
          #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
          #val #[ SHA512 ] : sha512_inp → sha512_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
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
        letbm s_sum_2544 : scalar_t loc( s_sum_2544_loc ) := nat_mod_zero  in
        letbm r_sum_2545 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) loc( r_sum_2545_loc ) :=
          point_identity  in
        letbm a_sum_2546 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) loc( a_sum_2546_loc ) :=
          point_identity  in
        letbnd(_) '(s_sum_2544, r_sum_2545, a_sum_2546) :=
          foldi_bind_both' (lift_to_both0 (usize 0)) (seq_len (
                lift_to_both0 entries_2551)) prod_ce(
              s_sum_2544,
              r_sum_2545,
              a_sum_2546
            ) (L := (CEfset (
                [s_sum_2544_loc ; r_sum_2545_loc ; a_sum_2546_loc]))) (I := (
              [interface
              #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
              #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
              #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
              #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
              #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ;
              #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
              #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
              #val #[ POINT_NEG ] : point_neg_inp → point_neg_out ;
              #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
              #val #[ SHA512 ] : sha512_inp → sha512_out ])) (fun i_2552 '(
              s_sum_2544,
              r_sum_2545,
              a_sum_2546
            ) =>
            letb BatchEntry ((pk_2553, msg_2554, signature_2555
                )) : batch_entry_t :=
              (seq_index (entries_2551) (lift_to_both0 i_2552)) in
            letbnd(_) a_2556 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 pk_2553)) (
                InvalidPublickey) in
            letbnd(_) 'tt :=
              if is_identity (point_mul_by_cofactor (
                  lift_to_both0 a_2556)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                [s_sum_2544_loc ; r_sum_2545_loc ; a_sum_2546_loc])) (L2 := CEfset (
                [s_sum_2544_loc ; r_sum_2545_loc ; a_sum_2546_loc])) (I1 := [interface]) (I2 := [interface
              #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
              #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
              #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
              #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
              #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
              #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
              #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
              #val #[ SHA512 ] : sha512_inp → sha512_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
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
            letb r_bytes_2557 : compressed_ed_point_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2555)) (lift_to_both0 (
                  usize 0)) (lift_to_both0 (usize 32)) in
            letb s_bytes_2558 : serialized_scalar_t :=
              array_from_slice (default : uint8) (32) (
                array_to_seq (lift_to_both0 signature_2555)) (lift_to_both0 (
                  usize 32)) (lift_to_both0 (usize 32)) in
            letbnd(_) 'tt :=
              if negb (check_canonical_scalar (
                  lift_to_both0 s_bytes_2558)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                [s_sum_2544_loc ; r_sum_2545_loc ; a_sum_2546_loc])) (L2 := CEfset (
                [s_sum_2544_loc ; r_sum_2545_loc ; a_sum_2546_loc])) (I1 := [interface]) (I2 := [interface
              #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
              #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
              #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
              #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
              #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
              #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
              #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
              #val #[ SHA512 ] : sha512_inp → sha512_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
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
            letbnd(_) r_2559 : (
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t '×
                ed25519_field_element_t
              ) :=
              option_ok_or (decompress (lift_to_both0 r_bytes_2557)) (
                InvalidR) in
            letb s_2560 : scalar_t :=
              nat_mod_from_byte_seq_le (
                array_to_seq (lift_to_both0 s_bytes_2558)) in
            letb c_2561 : scalar_t :=
              scalar_from_hash (sha512 (seq_concat (array_concat (
                      lift_to_both0 r_bytes_2557) (
                      array_to_seq (lift_to_both0 pk_2553))) (
                    lift_to_both0 msg_2554))) in
            letb z_2562 : seq uint8 :=
              seq_slice (lift_to_both0 entropy_2550) ((lift_to_both0 (
                    usize 16)) .* (lift_to_both0 i_2552)) (lift_to_both0 (
                  usize 16)) in
            letb z_2563 : scalar_t :=
              nat_mod_from_byte_seq_le (seq_concat (lift_to_both0 z_2562) (
                  seq_new_ (default : uint8) (lift_to_both0 (usize 16)))) in
            letbm s_sum_2544 loc( s_sum_2544_loc ) :=
              (lift_to_both0 s_sum_2544) +% ((lift_to_both0 s_2560) *% (
                  lift_to_both0 z_2563)) in
            letbm r_sum_2545 loc( r_sum_2545_loc ) :=
              point_add (lift_to_both0 r_sum_2545) (point_mul (
                  lift_to_both0 z_2563) (lift_to_both0 r_2559)) in
            letbm a_sum_2546 loc( a_sum_2546_loc ) :=
              point_add (lift_to_both0 a_sum_2546) (point_mul ((
                    lift_to_both0 z_2563) *% (lift_to_both0 c_2561)) (
                  lift_to_both0 a_2556)) in
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
                  lift_to_both0 s_sum_2544,
                  lift_to_both0 r_sum_2545,
                  lift_to_both0 a_sum_2546
                )))
            ) in
        letb b_2564 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          option_unwrap (decompress (lift_to_both0 base_v)) in
        letb sb_2565 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          point_mul (lift_to_both0 s_sum_2544) (lift_to_both0 b_2564) in
        letb check_2566 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          point_mul_by_cofactor (point_add (point_neg (lift_to_both0 sb_2565)) (
              point_add (lift_to_both0 r_sum_2545) (
                lift_to_both0 a_sum_2546))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) (is_identity (lift_to_both0 check_2566))
          then @Ok unit_ChoiceEquality error_t (tt)
          else @Err unit_ChoiceEquality error_t (InvalidSignature))
        ) : both (CEfset (
          [s_sum_2544_loc ; r_sum_2545_loc ; a_sum_2546_loc])) [interface
      #val #[ CHECK_CANONICAL_SCALAR ] : check_canonical_scalar_inp → check_canonical_scalar_out ;
      #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
      #val #[ IS_IDENTITY ] : is_identity_inp → is_identity_out ;
      #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
      #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ;
      #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
      #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out ;
      #val #[ POINT_NEG ] : point_neg_inp → point_neg_out ;
      #val #[ SCALAR_FROM_HASH ] : scalar_from_hash_inp → scalar_from_hash_out ;
      #val #[ SHA512 ] : sha512_inp → sha512_out ] (verify_result_t)))in
  both_package' _ _ (ALG3_BATCH_VERIFY,(
      alg3_batch_verify_inp,alg3_batch_verify_out)) temp_package_both.
Fail Next Obligation.

