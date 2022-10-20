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

Definition field_canvas_t := nseq (int8) (usize 32).
Definition ed25519_field_element_t :=
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Definition scalar_canvas_t := nseq (int8) (usize 32).
Definition scalar_t :=
  nat_mod 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed.

Definition big_scalar_canvas_t := nseq (int8) (usize 64).
Definition big_scalar_t :=
  nat_mod 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed.

Definition big_integer_canvas_t := nseq (int8) (usize 32).
Definition big_integer_t :=
  nat_mod 0x8000000000000000000000000000000080000000000000000000000000000000.

Notation "'ed_point_t'" := ((
  ed25519_field_element_t '×
  ed25519_field_element_t '×
  ed25519_field_element_t '×
  ed25519_field_element_t
)) : hacspec_scope.

Definition compressed_ed_point_t := nseq (uint8) (usize 32).

Definition serialized_scalar_t := nseq (uint8) (usize 32).

Definition signature_t := nseq (uint8) (usize 64).

Notation "'public_key_t'" := (compressed_ed_point_t) : hacspec_scope.

Notation "'secret_key_t'" := (serialized_scalar_t) : hacspec_scope.

Definition error_t : ChoiceEquality :=
  unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality.
Definition InvalidPublickey : error_t :=
  inl (inl (inl (inl (inl tt)))).
Definition InvalidSignature : error_t :=
  inl (inl (inl (inl (inr tt)))).
Definition InvalidS : error_t :=
  inl (inl (inl (inr tt))).
Definition InvalidR : error_t :=
  inl (inl (inr tt)).
Definition SmallOrderPoint : error_t :=
  inl (inr tt).
Definition NotEnoughRandomness : error_t :=
  inr tt.

Notation "'verify_result_t'" := ((result error_t unit)) : hacspec_scope.

Definition base_v : compressed_ed_point_t :=
  array_from_list uint8 [
    (secret (@repr U8 88)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8
  ].

Definition constant_p_v : serialized_scalar_t :=
  array_from_list uint8 [
    (secret (@repr U8 237)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 127)) : uint8
  ].

Definition constant_l_v : serialized_scalar_t :=
  array_from_list uint8 [
    (secret (@repr U8 237)) : uint8;
    (secret (@repr U8 211)) : uint8;
    (secret (@repr U8 245)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 26)) : uint8;
    (secret (@repr U8 99)) : uint8;
    (secret (@repr U8 18)) : uint8;
    (secret (@repr U8 88)) : uint8;
    (secret (@repr U8 214)) : uint8;
    (secret (@repr U8 156)) : uint8;
    (secret (@repr U8 247)) : uint8;
    (secret (@repr U8 162)) : uint8;
    (secret (@repr U8 222)) : uint8;
    (secret (@repr U8 249)) : uint8;
    (secret (@repr U8 222)) : uint8;
    (secret (@repr U8 20)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 16)) : uint8
  ].

Definition constant_p3_8_v : serialized_scalar_t :=
  array_from_list uint8 [
    (secret (@repr U8 254)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 15)) : uint8
  ].

Definition constant_p1_4_v : serialized_scalar_t :=
  array_from_list uint8 [
    (secret (@repr U8 251)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 31)) : uint8
  ].

Definition constant_d_v : serialized_scalar_t :=
  array_from_list uint8 [
    (secret (@repr U8 163)) : uint8;
    (secret (@repr U8 120)) : uint8;
    (secret (@repr U8 89)) : uint8;
    (secret (@repr U8 19)) : uint8;
    (secret (@repr U8 202)) : uint8;
    (secret (@repr U8 77)) : uint8;
    (secret (@repr U8 235)) : uint8;
    (secret (@repr U8 117)) : uint8;
    (secret (@repr U8 171)) : uint8;
    (secret (@repr U8 216)) : uint8;
    (secret (@repr U8 65)) : uint8;
    (secret (@repr U8 65)) : uint8;
    (secret (@repr U8 77)) : uint8;
    (secret (@repr U8 10)) : uint8;
    (secret (@repr U8 112)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 152)) : uint8;
    (secret (@repr U8 232)) : uint8;
    (secret (@repr U8 121)) : uint8;
    (secret (@repr U8 119)) : uint8;
    (secret (@repr U8 121)) : uint8;
    (secret (@repr U8 64)) : uint8;
    (secret (@repr U8 199)) : uint8;
    (secret (@repr U8 140)) : uint8;
    (secret (@repr U8 115)) : uint8;
    (secret (@repr U8 254)) : uint8;
    (secret (@repr U8 111)) : uint8;
    (secret (@repr U8 43)) : uint8;
    (secret (@repr U8 238)) : uint8;
    (secret (@repr U8 108)) : uint8;
    (secret (@repr U8 3)) : uint8;
    (secret (@repr U8 82)) : uint8
  ].


Notation "'is_negative_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'is_negative_inp'" :=(
  ed25519_field_element_t : ChoiceEquality) (at level 2).
Notation "'is_negative_out'" :=(
  uint8 : choice_type) (in custom pack_type at level 2).
Notation "'is_negative_out'" :=(uint8 : ChoiceEquality) (at level 2).
Definition IS_NEGATIVE : nat :=
  2569.
Program Definition is_negative
  : both_package (fset.fset0) [interface] [(IS_NEGATIVE,(
      is_negative_inp,is_negative_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_2568) := temp_inp : ed25519_field_element_t in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) (nat_mod_bit (lift_to_both0 x_2568) (
              lift_to_both0 (usize 0)))
          then secret (lift_to_both0 (@repr U8 1))
          else secret (lift_to_both0 (@repr U8 0)))
        ) : both (fset.fset0) [interface] (uint8)))in
  both_package' _ _ (IS_NEGATIVE,(
      is_negative_inp,is_negative_out)) temp_package_both.
Fail Next Obligation.

Definition s_2570_loc : ChoiceEqualityLocation :=
  (byte_seq ; 2571%nat).
Notation "'compress_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'compress_inp'" :=(ed_point_t : ChoiceEquality) (at level 2).
Notation "'compress_out'" :=(
  compressed_ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'compress_out'" :=(
  compressed_ed_point_t : ChoiceEquality) (at level 2).
Definition COMPRESS : nat :=
  2579.
Program Definition compress
  : both_package (CEfset ([s_2570_loc])) [interface
  #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ] [(COMPRESS,(
      compress_inp,compress_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_2572) := temp_inp : ed_point_t in
    
    let is_negative := fun x_0 => package_both is_negative (x_0) in
    ((letb '(x_2573, y_2574, z_2575, _) : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          lift_to_both0 p_2572 in
        letb z_inv_2576 : ed25519_field_element_t :=
          nat_mod_inv (lift_to_both0 z_2575) in
        letb x_2577 : ed25519_field_element_t :=
          (lift_to_both0 x_2573) *% (lift_to_both0 z_inv_2576) in
        letb y_2578 : ed25519_field_element_t :=
          (lift_to_both0 y_2574) *% (lift_to_both0 z_inv_2576) in
        letbm s_2570 : byte_seq loc( s_2570_loc ) :=
          nat_mod_to_byte_seq_le (lift_to_both0 y_2578) in
        letb s_2570 : seq uint8 :=
          seq_upd s_2570 (lift_to_both0 (usize 31)) (is_pure ((seq_index (
                  s_2570) (lift_to_both0 (usize 31))) .^ ((is_negative (
                    lift_to_both0 x_2577)) shift_left (lift_to_both0 (
                    usize 7))))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_slice (
            default : uint8) (32) (lift_to_both0 s_2570) (lift_to_both0 (
              usize 0)) (lift_to_both0 (usize 32)))
        ) : both (CEfset ([s_2570_loc])) [interface
      #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ] (
        compressed_ed_point_t)))in
  both_package' _ _ (COMPRESS,(compress_inp,compress_out)) temp_package_both.
Fail Next Obligation.

Definition result_2580_loc : ChoiceEqualityLocation :=
  ((option (ed25519_field_element_t)) ; 2581%nat).
Notation "'sqrt_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_inp'" :=(ed25519_field_element_t : ChoiceEquality) (at level 2).
Notation "'sqrt_out'" :=((option (
      ed25519_field_element_t)) : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_out'" :=((option (
      ed25519_field_element_t)) : ChoiceEquality) (at level 2).
Definition SQRT : nat :=
  2587.
Program Definition sqrt
  : both_package (CEfset ([result_2580_loc])) [interface
  #val #[ SOME ] : some_inp → some_out ] [(SQRT,(sqrt_inp,sqrt_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(a_2584) := temp_inp : ed25519_field_element_t in
    
    let some := fun x_0 => package_both some (x_0) in
    ((letb p3_8_2582 : ed25519_field_element_t :=
          nat_mod_from_byte_seq_le (
            array_to_seq (lift_to_both0 constant_p3_8_v)) in
        letb p1_4_2583 : ed25519_field_element_t :=
          nat_mod_from_byte_seq_le (
            array_to_seq (lift_to_both0 constant_p1_4_v)) in
        letb x_c_2585 : ed25519_field_element_t :=
          nat_mod_pow_self (lift_to_both0 a_2584) (lift_to_both0 p3_8_2582) in
        letbm result_2580 : (option (
              ed25519_field_element_t)) loc( result_2580_loc ) :=
          @None ed25519_field_element_t in
        letb 'result_2580 :=
          if ((lift_to_both0 x_c_2585) *% (lift_to_both0 x_c_2585)) =.? (
            lift_to_both0 a_2584) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset ([result_2580_loc])) (L2 := CEfset (
            [result_2580_loc])) (I1 := [interface
          #val #[ SOME ] : some_inp → some_out ]) (I2 := [interface
          #val #[ SOME ] : some_inp → some_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm result_2580 loc( result_2580_loc ) :=
              some (lift_to_both0 x_c_2585) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 result_2580)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 result_2580)
           in
        letb 'result_2580 :=
          if ((lift_to_both0 x_c_2585) *% (lift_to_both0 x_c_2585)) =.? ((
              nat_mod_zero ) -% (lift_to_both0 a_2584)) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset ([result_2580_loc])) (L2 := CEfset (
            [result_2580_loc])) (I1 := [interface
          #val #[ SOME ] : some_inp → some_out ]) (I2 := [interface
          #val #[ SOME ] : some_inp → some_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letb x_2586 : ed25519_field_element_t :=
              (nat_mod_pow_self (nat_mod_two ) (lift_to_both0 p1_4_2583)) *% (
                lift_to_both0 x_c_2585) in
            letbm result_2580 loc( result_2580_loc ) :=
              some (lift_to_both0 x_2586) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 result_2580)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 result_2580)
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 result_2580)
        ) : both (CEfset ([result_2580_loc])) [interface
      #val #[ SOME ] : some_inp → some_out ] ((option (
            ed25519_field_element_t)))))in
  both_package' _ _ (SQRT,(sqrt_inp,sqrt_out)) temp_package_both.
Fail Next Obligation.


Notation "'check_canonical_point_inp'" :=(
  compressed_ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'check_canonical_point_inp'" :=(
  compressed_ed_point_t : ChoiceEquality) (at level 2).
Notation "'check_canonical_point_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'check_canonical_point_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition CHECK_CANONICAL_POINT : nat :=
  2590.
Program Definition check_canonical_point
  : both_package (fset.fset0) [interface] [(CHECK_CANONICAL_POINT,(
      check_canonical_point_inp,check_canonical_point_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_2588) := temp_inp : compressed_ed_point_t in
    
    ((letb x_2588 : compressed_ed_point_t :=
          array_upd x_2588 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                  x_2588) (lift_to_both0 (usize 31))) .& (secret (
                  lift_to_both0 (@repr U8 127))))) in
        letb x_2589 : big_integer_t :=
          nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 x_2588)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
            lift_to_both0 x_2589) <.? (nat_mod_from_byte_seq_le (
              array_to_seq (lift_to_both0 constant_p_v))))
        ) : both (fset.fset0) [interface] (bool_ChoiceEquality)))in
  both_package' _ _ (CHECK_CANONICAL_POINT,(
      check_canonical_point_inp,check_canonical_point_out)) temp_package_both.
Fail Next Obligation.

Definition y_s_2591_loc : ChoiceEqualityLocation :=
  (compressed_ed_point_t ; 2593%nat).
Definition x_2592_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 2594%nat).
Notation "'decompress_inp'" :=(
  compressed_ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'decompress_inp'" :=(
  compressed_ed_point_t : ChoiceEquality) (at level 2).
Notation "'decompress_out'" :=((option (
      ed_point_t)) : choice_type) (in custom pack_type at level 2).
Notation "'decompress_out'" :=((option (
      ed_point_t)) : ChoiceEquality) (at level 2).
Definition DECOMPRESS : nat :=
  2605.
Program Definition decompress
  : both_package (CEfset ([y_s_2591_loc ; x_2592_loc])) [interface
  #val #[ SOME ] : some_inp → some_out ;
  #val #[ CHECK_CANONICAL_POINT ] : check_canonical_point_inp → check_canonical_point_out ;
  #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
  #val #[ SQRT ] : sqrt_inp → sqrt_out ] [(DECOMPRESS,(
      decompress_inp,decompress_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(q_2596) := temp_inp : compressed_ed_point_t in
    
    let some := fun x_0 => package_both some (x_0) in
    let check_canonical_point := fun x_0 => package_both check_canonical_point (
      x_0) in
    let is_negative := fun x_0 => package_both is_negative (x_0) in
    let sqrt := fun x_0 => package_both sqrt (x_0) in
    ((letb d_2595 : ed25519_field_element_t :=
          nat_mod_from_byte_seq_le (
            array_to_seq (lift_to_both0 constant_d_v)) in
        letb x_s_2597 : uint8 :=
          ((array_index (q_2596) (lift_to_both0 (usize 31))) .& (secret (
                lift_to_both0 (@repr U8 128)))) shift_right (lift_to_both0 (
              usize 7)) in
        letbm y_s_2591 : compressed_ed_point_t loc( y_s_2591_loc ) :=
          lift_to_both0 q_2596 in
        letb y_s_2591 : compressed_ed_point_t :=
          array_upd y_s_2591 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                  y_s_2591) (lift_to_both0 (usize 31))) .& (secret (
                  lift_to_both0 (@repr U8 127))))) in
        letbnd(_) 'tt :=
          if negb (check_canonical_point (
              lift_to_both0 y_s_2591)) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset ([y_s_2591_loc])) (L2 := CEfset (
            [y_s_2591_loc ; x_2592_loc])) (I1 := [interface]) (I2 := [interface
          #val #[ SOME ] : some_inp → some_out ;
          #val #[ CHECK_CANONICAL_POINT ] : check_canonical_point_inp → check_canonical_point_out ;
          #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
          #val #[ SQRT ] : sqrt_inp → sqrt_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(_) _ : ed_point_t :=
              @None ed_point_t in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              @Some unit_ChoiceEquality (lift_to_both0 (
                  (tt : unit_ChoiceEquality))))
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Some unit_ChoiceEquality (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
           in
        letb y_2598 : ed25519_field_element_t :=
          nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 y_s_2591)) in
        letb z_2599 : ed25519_field_element_t := nat_mod_one  in
        letb yy_2600 : ed25519_field_element_t :=
          (lift_to_both0 y_2598) *% (lift_to_both0 y_2598) in
        letb u_2601 : ed25519_field_element_t :=
          (lift_to_both0 yy_2600) -% (lift_to_both0 z_2599) in
        letb v_2602 : ed25519_field_element_t :=
          ((lift_to_both0 d_2595) *% (lift_to_both0 yy_2600)) +% (
            lift_to_both0 z_2599) in
        letb xx_2603 : ed25519_field_element_t :=
          (lift_to_both0 u_2601) *% (nat_mod_inv (lift_to_both0 v_2602)) in
        letbndm(_) x_2592 : ed25519_field_element_t :=
          sqrt (lift_to_both0 xx_2603) in
        letb x_r_2604 : uint8 := is_negative (lift_to_both0 x_2592) in
        letbnd(_) 'tt :=
          if ((lift_to_both0 x_2592) =.? (nat_mod_zero )) && ((
              uint8_declassify (lift_to_both0 x_s_2597)) =.? (lift_to_both0 (
                @repr U8 1))) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset (
            [y_s_2591_loc ; x_2592_loc])) (L2 := CEfset (
            [y_s_2591_loc ; x_2592_loc])) (I1 := [interface]) (I2 := [interface
          #val #[ SOME ] : some_inp → some_out ;
          #val #[ CHECK_CANONICAL_POINT ] : check_canonical_point_inp → check_canonical_point_out ;
          #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
          #val #[ SQRT ] : sqrt_inp → sqrt_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(_) _ : ed_point_t :=
              @None ed_point_t in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              @Some unit_ChoiceEquality (lift_to_both0 (
                  (tt : unit_ChoiceEquality))))
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Some unit_ChoiceEquality (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
           in
        letb 'x_2592 :=
          if (uint8_declassify (lift_to_both0 x_r_2604)) !=.? (
            uint8_declassify (lift_to_both0 x_s_2597)) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset (
            [y_s_2591_loc ; x_2592_loc])) (L2 := CEfset (
            [y_s_2591_loc ; x_2592_loc])) (I1 := [interface]) (I2 := [interface
          #val #[ SOME ] : some_inp → some_out ;
          #val #[ CHECK_CANONICAL_POINT ] : check_canonical_point_inp → check_canonical_point_out ;
          #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
          #val #[ SQRT ] : sqrt_inp → sqrt_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm x_2592 loc( x_2592_loc ) :=
              (nat_mod_zero ) -% (lift_to_both0 x_2592) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 x_2592)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 x_2592)
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (some (prod_b(
              lift_to_both0 x_2592,
              lift_to_both0 y_2598,
              lift_to_both0 z_2599,
              (lift_to_both0 x_2592) *% (lift_to_both0 y_2598)
            )))
        ) : both (CEfset ([y_s_2591_loc ; x_2592_loc])) [interface
      #val #[ SOME ] : some_inp → some_out ;
      #val #[ CHECK_CANONICAL_POINT ] : check_canonical_point_inp → check_canonical_point_out ;
      #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
      #val #[ SQRT ] : sqrt_inp → sqrt_out ] ((option (ed_point_t)))))in
  both_package' _ _ (DECOMPRESS,(
      decompress_inp,decompress_out)) temp_package_both.
Fail Next Obligation.

Definition y_s_2606_loc : ChoiceEqualityLocation :=
  (compressed_ed_point_t ; 2608%nat).
Definition x_2607_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 2609%nat).
Notation "'decompress_non_canonical_inp'" :=(
  compressed_ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'decompress_non_canonical_inp'" :=(
  compressed_ed_point_t : ChoiceEquality) (at level 2).
Notation "'decompress_non_canonical_out'" :=((option (
      ed_point_t)) : choice_type) (in custom pack_type at level 2).
Notation "'decompress_non_canonical_out'" :=((option (
      ed_point_t)) : ChoiceEquality) (at level 2).
Definition DECOMPRESS_NON_CANONICAL : nat :=
  2620.
Program Definition decompress_non_canonical
  : both_package (CEfset ([y_s_2606_loc ; x_2607_loc])) [interface
  #val #[ SOME ] : some_inp → some_out ;
  #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
  #val #[ SQRT ] : sqrt_inp → sqrt_out ] [(DECOMPRESS_NON_CANONICAL,(
      decompress_non_canonical_inp,decompress_non_canonical_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_2611) := temp_inp : compressed_ed_point_t in
    
    let some := fun x_0 => package_both some (x_0) in
    let is_negative := fun x_0 => package_both is_negative (x_0) in
    let sqrt := fun x_0 => package_both sqrt (x_0) in
    ((letb d_2610 : ed25519_field_element_t :=
          nat_mod_from_byte_seq_le (
            array_to_seq (lift_to_both0 constant_d_v)) in
        letb x_s_2612 : uint8 :=
          ((array_index (p_2611) (lift_to_both0 (usize 31))) .& (secret (
                lift_to_both0 (@repr U8 128)))) shift_right (lift_to_both0 (
              usize 7)) in
        letbm y_s_2606 : compressed_ed_point_t loc( y_s_2606_loc ) :=
          lift_to_both0 p_2611 in
        letb y_s_2606 : compressed_ed_point_t :=
          array_upd y_s_2606 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                  y_s_2606) (lift_to_both0 (usize 31))) .& (secret (
                  lift_to_both0 (@repr U8 127))))) in
        letb y_2613 : ed25519_field_element_t :=
          nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 y_s_2606)) in
        letb z_2614 : ed25519_field_element_t := nat_mod_one  in
        letb yy_2615 : ed25519_field_element_t :=
          (lift_to_both0 y_2613) *% (lift_to_both0 y_2613) in
        letb u_2616 : ed25519_field_element_t :=
          (lift_to_both0 yy_2615) -% (lift_to_both0 z_2614) in
        letb v_2617 : ed25519_field_element_t :=
          ((lift_to_both0 d_2610) *% (lift_to_both0 yy_2615)) +% (
            lift_to_both0 z_2614) in
        letb xx_2618 : ed25519_field_element_t :=
          (lift_to_both0 u_2616) *% (nat_mod_inv (lift_to_both0 v_2617)) in
        letbndm(_) x_2607 : ed25519_field_element_t :=
          sqrt (lift_to_both0 xx_2618) in
        letb x_r_2619 : uint8 := is_negative (lift_to_both0 x_2607) in
        letb 'x_2607 :=
          if (uint8_declassify (lift_to_both0 x_r_2619)) !=.? (
            uint8_declassify (lift_to_both0 x_s_2612)) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset (
            [y_s_2606_loc ; x_2607_loc])) (L2 := CEfset (
            [y_s_2606_loc ; x_2607_loc])) (I1 := [interface]) (I2 := [interface
          #val #[ SOME ] : some_inp → some_out ;
          #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
          #val #[ SQRT ] : sqrt_inp → sqrt_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm x_2607 loc( x_2607_loc ) :=
              (nat_mod_zero ) -% (lift_to_both0 x_2607) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 x_2607)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 x_2607)
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (some (prod_b(
              lift_to_both0 x_2607,
              lift_to_both0 y_2613,
              lift_to_both0 z_2614,
              (lift_to_both0 x_2607) *% (lift_to_both0 y_2613)
            )))
        ) : both (CEfset ([y_s_2606_loc ; x_2607_loc])) [interface
      #val #[ SOME ] : some_inp → some_out ;
      #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
      #val #[ SQRT ] : sqrt_inp → sqrt_out ] ((option (ed_point_t)))))in
  both_package' _ _ (DECOMPRESS_NON_CANONICAL,(
      decompress_non_canonical_inp,decompress_non_canonical_out)) temp_package_both.
Fail Next Obligation.

Definition s_2621_loc : ChoiceEqualityLocation :=
  (byte_seq ; 2622%nat).
Notation "'encode_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'encode_inp'" :=(ed_point_t : ChoiceEquality) (at level 2).
Notation "'encode_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'encode_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition ENCODE : nat :=
  2630.
Program Definition encode
  : both_package (CEfset ([s_2621_loc])) [interface
  #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ] [(ENCODE,(
      encode_inp,encode_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_2623) := temp_inp : ed_point_t in
    
    let is_negative := fun x_0 => package_both is_negative (x_0) in
    ((letb '(x_2624, y_2625, z_2626, _) : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          lift_to_both0 p_2623 in
        letb z_inv_2627 : ed25519_field_element_t :=
          nat_mod_inv (lift_to_both0 z_2626) in
        letb x_2628 : ed25519_field_element_t :=
          (lift_to_both0 x_2624) *% (lift_to_both0 z_inv_2627) in
        letb y_2629 : ed25519_field_element_t :=
          (lift_to_both0 y_2625) *% (lift_to_both0 z_inv_2627) in
        letbm s_2621 : byte_seq loc( s_2621_loc ) :=
          nat_mod_to_byte_seq_le (lift_to_both0 y_2629) in
        letb s_2621 : seq uint8 :=
          seq_upd s_2621 (lift_to_both0 (usize 31)) (is_pure ((seq_index (
                  s_2621) (lift_to_both0 (usize 31))) .^ ((is_negative (
                    lift_to_both0 x_2628)) shift_left (lift_to_both0 (
                    usize 7))))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_2621)
        ) : both (CEfset ([s_2621_loc])) [interface
      #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ] (
        byte_seq)))in
  both_package' _ _ (ENCODE,(encode_inp,encode_out)) temp_package_both.
Fail Next Obligation.


Notation "'decode_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'decode_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'decode_out'" :=((option (
      ed_point_t)) : choice_type) (in custom pack_type at level 2).
Notation "'decode_out'" :=((option (ed_point_t)) : ChoiceEquality) (at level 2).
Definition DECODE : nat :=
  2633.
Program Definition decode
  : both_package (CEfset ([])) [interface
  #val #[ DECOMPRESS ] : decompress_inp → decompress_out ] [(DECODE,(
      decode_inp,decode_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(q_s_2631) := temp_inp : byte_seq in
    
    let decompress := fun x_0 => package_both decompress (x_0) in
    ((letb q_2632 : compressed_ed_point_t :=
          array_from_slice (default : uint8) (32) (lift_to_both0 q_s_2631) (
            lift_to_both0 (usize 0)) (lift_to_both0 (usize 32)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (decompress (
            lift_to_both0 q_2632))
        ) : both (CEfset ([])) [interface
      #val #[ DECOMPRESS ] : decompress_inp → decompress_out ] ((option (
            ed_point_t)))))in
  both_package' _ _ (DECODE,(decode_inp,decode_out)) temp_package_both.
Fail Next Obligation.


Notation "'point_add_inp'" :=(
  ed_point_t '× ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_inp'" :=(
  ed_point_t '× ed_point_t : ChoiceEquality) (at level 2).
Notation "'point_add_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_out'" :=(ed_point_t : ChoiceEquality) (at level 2).
Definition POINT_ADD : nat :=
  2658.
Program Definition point_add
  : both_package (fset.fset0) [interface] [(POINT_ADD,(
      point_add_inp,point_add_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_2636 , q_2641) := temp_inp : ed_point_t '× ed_point_t in
    
    ((letb d_c_2634 : ed25519_field_element_t :=
          nat_mod_from_byte_seq_le (
            array_to_seq (lift_to_both0 constant_d_v)) in
        letb two_2635 : ed25519_field_element_t := nat_mod_two  in
        letb '(x1_2637, y1_2638, z1_2639, t1_2640) : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          lift_to_both0 p_2636 in
        letb '(x2_2642, y2_2643, z2_2644, t2_2645) : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          lift_to_both0 q_2641 in
        letb a_2646 : ed25519_field_element_t :=
          ((lift_to_both0 y1_2638) -% (lift_to_both0 x1_2637)) *% ((
              lift_to_both0 y2_2643) -% (lift_to_both0 x2_2642)) in
        letb b_2647 : ed25519_field_element_t :=
          ((lift_to_both0 y1_2638) +% (lift_to_both0 x1_2637)) *% ((
              lift_to_both0 y2_2643) +% (lift_to_both0 x2_2642)) in
        letb c_2648 : ed25519_field_element_t :=
          (((lift_to_both0 t1_2640) *% (lift_to_both0 two_2635)) *% (
              lift_to_both0 d_c_2634)) *% (lift_to_both0 t2_2645) in
        letb d_2649 : ed25519_field_element_t :=
          ((lift_to_both0 z1_2639) *% (lift_to_both0 two_2635)) *% (
            lift_to_both0 z2_2644) in
        letb e_2650 : ed25519_field_element_t :=
          (lift_to_both0 b_2647) -% (lift_to_both0 a_2646) in
        letb f_2651 : ed25519_field_element_t :=
          (lift_to_both0 d_2649) -% (lift_to_both0 c_2648) in
        letb g_2652 : ed25519_field_element_t :=
          (lift_to_both0 d_2649) +% (lift_to_both0 c_2648) in
        letb h_2653 : ed25519_field_element_t :=
          (lift_to_both0 b_2647) +% (lift_to_both0 a_2646) in
        letb x3_2654 : ed25519_field_element_t :=
          (lift_to_both0 e_2650) *% (lift_to_both0 f_2651) in
        letb y3_2655 : ed25519_field_element_t :=
          (lift_to_both0 g_2652) *% (lift_to_both0 h_2653) in
        letb t3_2656 : ed25519_field_element_t :=
          (lift_to_both0 e_2650) *% (lift_to_both0 h_2653) in
        letb z3_2657 : ed25519_field_element_t :=
          (lift_to_both0 f_2651) *% (lift_to_both0 g_2652) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 x3_2654,
            lift_to_both0 y3_2655,
            lift_to_both0 z3_2657,
            lift_to_both0 t3_2656
          ))
        ) : both (fset.fset0) [interface] (ed_point_t)))in
  both_package' _ _ (POINT_ADD,(point_add_inp,point_add_out)) temp_package_both.
Fail Next Obligation.


Notation "'point_identity_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'point_identity_inp'" :=(
  unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'point_identity_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_identity_out'" :=(ed_point_t : ChoiceEquality) (at level 2).
Definition POINT_IDENTITY : nat :=
  2659.
Program Definition point_identity
  : both_package (fset.fset0) [interface] [(POINT_IDENTITY,(
      point_identity_inp,point_identity_out))] :=
  let temp_package_both := (fun temp_inp => 
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            nat_mod_zero ,
            nat_mod_one ,
            nat_mod_one ,
            nat_mod_zero 
          ))
        ) : both (fset.fset0) [interface] (ed_point_t)))in
  both_package' _ _ (POINT_IDENTITY,(
      point_identity_inp,point_identity_out)) temp_package_both.
Fail Next Obligation.

Definition p_2660_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2662%nat).
Definition q_2661_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2663%nat).
Notation "'point_mul_inp'" :=(
  scalar_t '× ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_inp'" :=(
  scalar_t '× ed_point_t : ChoiceEquality) (at level 2).
Notation "'point_mul_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_out'" :=(ed_point_t : ChoiceEquality) (at level 2).
Definition POINT_MUL : nat :=
  2667.
Program Definition point_mul
  : both_package (CEfset ([p_2660_loc ; q_2661_loc])) [interface
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
  #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ] [(
    POINT_MUL,(point_mul_inp,point_mul_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(s_2666 , p_2664) := temp_inp : scalar_t '× ed_point_t in
    
    let point_add := fun x_0 x_1 => package_both point_add (x_0,x_1) in
    let point_identity := package_both point_identity tt in
    ((letbm p_2660 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) loc( p_2660_loc ) :=
          lift_to_both0 p_2664 in
        letbm q_2661 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) loc( q_2661_loc ) :=
          point_identity  in
        letb '(p_2660, q_2661) :=
          foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                usize 256)) prod_ce(p_2660, q_2661) (L := (CEfset (
                [p_2660_loc ; q_2661_loc]))) (I := ([interface
              #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
              #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out
              ])) (fun i_2665 '(p_2660, q_2661) =>
            letb 'q_2661 :=
              if nat_mod_bit (lift_to_both0 s_2666) (
                lift_to_both0 i_2665) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                [p_2660_loc ; q_2661_loc])) (L2 := CEfset (
                [p_2660_loc ; q_2661_loc])) (I1 := [interface
              #val #[ POINT_ADD ] : point_add_inp → point_add_out
              ]) (I2 := [interface
              #val #[ POINT_ADD ] : point_add_inp → point_add_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm q_2661 loc( q_2661_loc ) :=
                  point_add (lift_to_both0 q_2661) (lift_to_both0 p_2660) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 q_2661)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 q_2661)
               in
            letbm p_2660 loc( p_2660_loc ) :=
              point_add (lift_to_both0 p_2660) (lift_to_both0 p_2660) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 p_2660,
                lift_to_both0 q_2661
              ))
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 q_2661)
        ) : both (CEfset ([p_2660_loc ; q_2661_loc])) [interface
      #val #[ POINT_ADD ] : point_add_inp → point_add_out ;
      #val #[ POINT_IDENTITY ] : point_identity_inp → point_identity_out ] (
        ed_point_t)))in
  both_package' _ _ (POINT_MUL,(point_mul_inp,point_mul_out)) temp_package_both.
Fail Next Obligation.


Notation "'point_mul_by_cofactor_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_by_cofactor_inp'" :=(
  ed_point_t : ChoiceEquality) (at level 2).
Notation "'point_mul_by_cofactor_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_by_cofactor_out'" :=(
  ed_point_t : ChoiceEquality) (at level 2).
Definition POINT_MUL_BY_COFACTOR : nat :=
  2672.
Program Definition point_mul_by_cofactor
  : both_package (fset.fset0) [interface
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ] [(
    POINT_MUL_BY_COFACTOR,(
      point_mul_by_cofactor_inp,point_mul_by_cofactor_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_2668) := temp_inp : ed_point_t in
    
    let point_add := fun x_0 x_1 => package_both point_add (x_0,x_1) in
    ((letb p2_2669 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          point_add (lift_to_both0 p_2668) (lift_to_both0 p_2668) in
        letb p4_2670 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          point_add (lift_to_both0 p2_2669) (lift_to_both0 p2_2669) in
        letb p8_2671 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          point_add (lift_to_both0 p4_2670) (lift_to_both0 p4_2670) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p8_2671)
        ) : both (fset.fset0) [interface
      #val #[ POINT_ADD ] : point_add_inp → point_add_out ] (ed_point_t)))in
  both_package' _ _ (POINT_MUL_BY_COFACTOR,(
      point_mul_by_cofactor_inp,point_mul_by_cofactor_out)) temp_package_both.
Fail Next Obligation.


Notation "'point_neg_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_neg_inp'" :=(ed_point_t : ChoiceEquality) (at level 2).
Notation "'point_neg_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_neg_out'" :=(ed_point_t : ChoiceEquality) (at level 2).
Definition POINT_NEG : nat :=
  2678.
Program Definition point_neg
  : both_package (fset.fset0) [interface] [(POINT_NEG,(
      point_neg_inp,point_neg_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_2673) := temp_inp : ed_point_t in
    
    ((letb '(x_2674, y_2675, z_2676, t_2677) : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          lift_to_both0 p_2673 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            (nat_mod_zero ) -% (lift_to_both0 x_2674),
            lift_to_both0 y_2675,
            lift_to_both0 z_2676,
            (nat_mod_zero ) -% (lift_to_both0 t_2677)
          ))
        ) : both (fset.fset0) [interface] (ed_point_t)))in
  both_package' _ _ (POINT_NEG,(point_neg_inp,point_neg_out)) temp_package_both.
Fail Next Obligation.


Notation "'point_eq_inp'" :=(
  ed_point_t '× ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_eq_inp'" :=(
  ed_point_t '× ed_point_t : ChoiceEquality) (at level 2).
Notation "'point_eq_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'point_eq_out'" :=(bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition POINT_EQ : nat :=
  2687.
Program Definition point_eq
  : both_package (fset.fset0) [interface] [(POINT_EQ,(
      point_eq_inp,point_eq_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_2679 , q_2683) := temp_inp : ed_point_t '× ed_point_t in
    
    ((letb '(x1_2680, y1_2681, z1_2682, _) : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          lift_to_both0 p_2679 in
        letb '(x2_2684, y2_2685, z2_2686, _) : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          lift_to_both0 q_2683 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((((
                lift_to_both0 x1_2680) *% (lift_to_both0 z2_2686)) =.? ((
                lift_to_both0 x2_2684) *% (lift_to_both0 z1_2682))) && (((
                lift_to_both0 y1_2681) *% (lift_to_both0 z2_2686)) =.? ((
                lift_to_both0 y2_2685) *% (lift_to_both0 z1_2682))))
        ) : both (fset.fset0) [interface] (bool_ChoiceEquality)))in
  both_package' _ _ (POINT_EQ,(point_eq_inp,point_eq_out)) temp_package_both.
Fail Next Obligation.


Notation "'point_normalize_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_normalize_inp'" :=(ed_point_t : ChoiceEquality) (at level 2).
Notation "'point_normalize_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_normalize_out'" :=(ed_point_t : ChoiceEquality) (at level 2).
Definition POINT_NORMALIZE : nat :=
  2696.
Program Definition point_normalize
  : both_package (fset.fset0) [interface] [(POINT_NORMALIZE,(
      point_normalize_inp,point_normalize_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(q_2688) := temp_inp : ed_point_t in
    
    ((letb '(qx_2689, qy_2690, qz_2691, _) : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          lift_to_both0 q_2688 in
        letb px_2692 : ed25519_field_element_t :=
          (lift_to_both0 qx_2689) *% (nat_mod_inv (lift_to_both0 qz_2691)) in
        letb py_2693 : ed25519_field_element_t :=
          (lift_to_both0 qy_2690) *% (nat_mod_inv (lift_to_both0 qz_2691)) in
        letb pz_2694 : ed25519_field_element_t := nat_mod_one  in
        letb pt_2695 : ed25519_field_element_t :=
          (lift_to_both0 px_2692) *% (lift_to_both0 py_2693) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 px_2692,
            lift_to_both0 py_2693,
            lift_to_both0 pz_2694,
            lift_to_both0 pt_2695
          ))
        ) : both (fset.fset0) [interface] (ed_point_t)))in
  both_package' _ _ (POINT_NORMALIZE,(
      point_normalize_inp,point_normalize_out)) temp_package_both.
Fail Next Obligation.

Definition s_2697_loc : ChoiceEqualityLocation :=
  (serialized_scalar_t ; 2698%nat).
Notation "'secret_expand_inp'" :=(
  secret_key_t : choice_type) (in custom pack_type at level 2).
Notation "'secret_expand_inp'" :=(secret_key_t : ChoiceEquality) (at level 2).
Notation "'secret_expand_out'" :=((serialized_scalar_t '× serialized_scalar_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'secret_expand_out'" :=((serialized_scalar_t '× serialized_scalar_t
  ) : ChoiceEquality) (at level 2).
Definition SECRET_EXPAND : nat :=
  2702.
Program Definition secret_expand
  : both_package (CEfset ([s_2697_loc])) [interface
  #val #[ SHA512 ] : sha512_inp → sha512_out ] [(SECRET_EXPAND,(
      secret_expand_inp,secret_expand_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(sk_2699) := temp_inp : secret_key_t in
    
    let sha512 := fun x_0 => package_both sha512 (x_0) in
    ((letb h_2700 : sha512_digest_t :=
          sha512 (seq_from_slice (lift_to_both0 sk_2699) (lift_to_both0 (
                usize 0)) (lift_to_both0 (usize 32))) in
        letb h_d_2701 : serialized_scalar_t :=
          array_from_slice (default : uint8) (32) (
            array_to_seq (lift_to_both0 h_2700)) (lift_to_both0 (usize 32)) (
            lift_to_both0 (usize 32)) in
        letbm s_2697 : serialized_scalar_t loc( s_2697_loc ) :=
          array_from_slice (default : uint8) (32) (
            array_to_seq (lift_to_both0 h_2700)) (lift_to_both0 (usize 0)) (
            lift_to_both0 (usize 32)) in
        letb s_2697 : serialized_scalar_t :=
          array_upd s_2697 (lift_to_both0 (usize 0)) (is_pure ((array_index (
                  s_2697) (lift_to_both0 (usize 0))) .& (secret (lift_to_both0 (
                    @repr U8 248))))) in
        letb s_2697 : serialized_scalar_t :=
          array_upd s_2697 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                  s_2697) (lift_to_both0 (usize 31))) .& (secret (
                  lift_to_both0 (@repr U8 127))))) in
        letb s_2697 : serialized_scalar_t :=
          array_upd s_2697 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                  s_2697) (lift_to_both0 (usize 31))) .| (secret (
                  lift_to_both0 (@repr U8 64))))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 s_2697,
            lift_to_both0 h_d_2701
          ))
        ) : both (CEfset ([s_2697_loc])) [interface
      #val #[ SHA512 ] : sha512_inp → sha512_out ] ((
          serialized_scalar_t '×
          serialized_scalar_t
        ))))in
  both_package' _ _ (SECRET_EXPAND,(
      secret_expand_inp,secret_expand_out)) temp_package_both.
Fail Next Obligation.


Notation "'secret_to_public_inp'" :=(
  secret_key_t : choice_type) (in custom pack_type at level 2).
Notation "'secret_to_public_inp'" :=(
  secret_key_t : ChoiceEquality) (at level 2).
Notation "'secret_to_public_out'" :=(
  public_key_t : choice_type) (in custom pack_type at level 2).
Notation "'secret_to_public_out'" :=(
  public_key_t : ChoiceEquality) (at level 2).
Definition SECRET_TO_PUBLIC : nat :=
  2708.
Program Definition secret_to_public
  : both_package (CEfset ([])) [interface
  #val #[ COMPRESS ] : compress_inp → compress_out ;
  #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
  #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
  #val #[ SECRET_EXPAND ] : secret_expand_inp → secret_expand_out ] [(
    SECRET_TO_PUBLIC,(secret_to_public_inp,secret_to_public_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(sk_2703) := temp_inp : secret_key_t in
    
    let compress := fun x_0 => package_both compress (x_0) in
    let decompress := fun x_0 => package_both decompress (x_0) in
    let point_mul := fun x_0 x_1 => package_both point_mul (x_0,x_1) in
    let secret_expand := fun x_0 => package_both secret_expand (x_0) in
    ((letb '(s_2704, _) : (serialized_scalar_t '× serialized_scalar_t) :=
          secret_expand (lift_to_both0 sk_2703) in
        letb base_2705 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          option_unwrap (decompress (lift_to_both0 base_v)) in
        letb ss_2706 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 s_2704)) in
        letb a_2707 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          point_mul (lift_to_both0 ss_2706) (lift_to_both0 base_2705) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (compress (
            lift_to_both0 a_2707))
        ) : both (CEfset ([])) [interface
      #val #[ COMPRESS ] : compress_inp → compress_out ;
      #val #[ DECOMPRESS ] : decompress_inp → decompress_out ;
      #val #[ POINT_MUL ] : point_mul_inp → point_mul_out ;
      #val #[ SECRET_EXPAND ] : secret_expand_inp → secret_expand_out ] (
        public_key_t)))in
  both_package' _ _ (SECRET_TO_PUBLIC,(
      secret_to_public_inp,secret_to_public_out)) temp_package_both.
Fail Next Obligation.


Notation "'check_canonical_scalar_inp'" :=(
  serialized_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'check_canonical_scalar_inp'" :=(
  serialized_scalar_t : ChoiceEquality) (at level 2).
Notation "'check_canonical_scalar_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'check_canonical_scalar_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition CHECK_CANONICAL_SCALAR : nat :=
  2710.
Program Definition check_canonical_scalar
  : both_package (fset.fset0) [interface] [(CHECK_CANONICAL_SCALAR,(
      check_canonical_scalar_inp,check_canonical_scalar_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(s_2709) := temp_inp : serialized_scalar_t in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) ((uint8_declassify ((array_index (
                    s_2709) (lift_to_both0 (usize 31))) .& (secret (
                    lift_to_both0 (@repr U8 224))))) !=.? (lift_to_both0 (
                @repr U8 0)))
          then lift_to_both0 ((false : bool_ChoiceEquality))
          else (nat_mod_from_byte_seq_le (
              array_to_seq (lift_to_both0 s_2709))) <.? (
            nat_mod_from_byte_seq_le (
              array_to_seq (lift_to_both0 constant_l_v))))
        ) : both (fset.fset0) [interface] (bool_ChoiceEquality)))in
  both_package' _ _ (CHECK_CANONICAL_SCALAR,(
      check_canonical_scalar_inp,check_canonical_scalar_out)) temp_package_both.
Fail Next Obligation.

