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


Notation "'ristretto_point_t'" := ((
  field_element_t '×
  field_element_t '×
  field_element_t '×
  field_element_t
)) : hacspec_scope.

Notation "'decode_result_t'" := ((
  result int8 ristretto_point_t)) : hacspec_scope.

Definition ristretto_point_encoded_t := nseq (uint8) (usize 32).

Definition byte_string_t := nseq (uint8) (usize 64).

Definition field_canvas_t := nseq (int8) (usize 32).
Definition field_element_t :=
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Definition scalar_canvas_t := nseq (int8) (usize 32).
Definition scalar_t :=
  nat_mod 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed.

Definition decoding_error_v : int8 :=
  @repr U8 20.


Notation "'p_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'p_inp'" :=(unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'p_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'p_out'" :=(field_element_t : ChoiceEquality) (at level 2).
Definition P : nat :=
  939.
Program Definition p
  : both_package (fset.fset0) [interface] [(P,(p_inp,p_out))] :=
  let temp_package_both := (fun temp_inp => 
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          nat_mod_from_byte_seq_be ([
              secret (lift_to_both0 (@repr U8 127));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 255));
              secret (lift_to_both0 (@repr U8 237))
            ]))
        ) : both (fset.fset0) [interface] (field_element_t)))in
  both_package' _ _ (P,(p_inp,p_out)) temp_package_both.
Fail Next Obligation.


Notation "'d_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'d_inp'" :=(unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'d_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'d_out'" :=(field_element_t : ChoiceEquality) (at level 2).
Definition D : nat :=
  940.
Program Definition d
  : both_package (fset.fset0) [interface] [(D,(d_inp,d_out))] :=
  let temp_package_both := (fun temp_inp => 
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          nat_mod_from_byte_seq_be ([
              secret (lift_to_both0 (@repr U8 82));
              secret (lift_to_both0 (@repr U8 3));
              secret (lift_to_both0 (@repr U8 108));
              secret (lift_to_both0 (@repr U8 238));
              secret (lift_to_both0 (@repr U8 43));
              secret (lift_to_both0 (@repr U8 111));
              secret (lift_to_both0 (@repr U8 254));
              secret (lift_to_both0 (@repr U8 115));
              secret (lift_to_both0 (@repr U8 140));
              secret (lift_to_both0 (@repr U8 199));
              secret (lift_to_both0 (@repr U8 64));
              secret (lift_to_both0 (@repr U8 121));
              secret (lift_to_both0 (@repr U8 119));
              secret (lift_to_both0 (@repr U8 121));
              secret (lift_to_both0 (@repr U8 232));
              secret (lift_to_both0 (@repr U8 152));
              secret (lift_to_both0 (@repr U8 0));
              secret (lift_to_both0 (@repr U8 112));
              secret (lift_to_both0 (@repr U8 10));
              secret (lift_to_both0 (@repr U8 77));
              secret (lift_to_both0 (@repr U8 65));
              secret (lift_to_both0 (@repr U8 65));
              secret (lift_to_both0 (@repr U8 216));
              secret (lift_to_both0 (@repr U8 171));
              secret (lift_to_both0 (@repr U8 117));
              secret (lift_to_both0 (@repr U8 235));
              secret (lift_to_both0 (@repr U8 77));
              secret (lift_to_both0 (@repr U8 202));
              secret (lift_to_both0 (@repr U8 19));
              secret (lift_to_both0 (@repr U8 89));
              secret (lift_to_both0 (@repr U8 120));
              secret (lift_to_both0 (@repr U8 163))
            ]))
        ) : both (fset.fset0) [interface] (field_element_t)))in
  both_package' _ _ (D,(d_inp,d_out)) temp_package_both.
Fail Next Obligation.


Notation "'sqrt_m1_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_m1_inp'" :=(unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'sqrt_m1_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_m1_out'" :=(field_element_t : ChoiceEquality) (at level 2).
Definition SQRT_M1 : nat :=
  941.
Program Definition sqrt_m1
  : both_package (fset.fset0) [interface] [(SQRT_M1,(
      sqrt_m1_inp,sqrt_m1_out))] :=
  let temp_package_both := (fun temp_inp => 
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          nat_mod_from_byte_seq_be ([
              secret (lift_to_both0 (@repr U8 43));
              secret (lift_to_both0 (@repr U8 131));
              secret (lift_to_both0 (@repr U8 36));
              secret (lift_to_both0 (@repr U8 128));
              secret (lift_to_both0 (@repr U8 79));
              secret (lift_to_both0 (@repr U8 193));
              secret (lift_to_both0 (@repr U8 223));
              secret (lift_to_both0 (@repr U8 11));
              secret (lift_to_both0 (@repr U8 43));
              secret (lift_to_both0 (@repr U8 77));
              secret (lift_to_both0 (@repr U8 0));
              secret (lift_to_both0 (@repr U8 153));
              secret (lift_to_both0 (@repr U8 61));
              secret (lift_to_both0 (@repr U8 251));
              secret (lift_to_both0 (@repr U8 215));
              secret (lift_to_both0 (@repr U8 167));
              secret (lift_to_both0 (@repr U8 47));
              secret (lift_to_both0 (@repr U8 67));
              secret (lift_to_both0 (@repr U8 24));
              secret (lift_to_both0 (@repr U8 6));
              secret (lift_to_both0 (@repr U8 173));
              secret (lift_to_both0 (@repr U8 47));
              secret (lift_to_both0 (@repr U8 228));
              secret (lift_to_both0 (@repr U8 120));
              secret (lift_to_both0 (@repr U8 196));
              secret (lift_to_both0 (@repr U8 238));
              secret (lift_to_both0 (@repr U8 27));
              secret (lift_to_both0 (@repr U8 39));
              secret (lift_to_both0 (@repr U8 74));
              secret (lift_to_both0 (@repr U8 14));
              secret (lift_to_both0 (@repr U8 160));
              secret (lift_to_both0 (@repr U8 176))
            ]))
        ) : both (fset.fset0) [interface] (field_element_t)))in
  both_package' _ _ (SQRT_M1,(sqrt_m1_inp,sqrt_m1_out)) temp_package_both.
Fail Next Obligation.


Notation "'invsqrt_a_minus_d_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'invsqrt_a_minus_d_inp'" :=(
  unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'invsqrt_a_minus_d_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'invsqrt_a_minus_d_out'" :=(
  field_element_t : ChoiceEquality) (at level 2).
Definition INVSQRT_A_MINUS_D : nat :=
  942.
Program Definition invsqrt_a_minus_d
  : both_package (fset.fset0) [interface] [(INVSQRT_A_MINUS_D,(
      invsqrt_a_minus_d_inp,invsqrt_a_minus_d_out))] :=
  let temp_package_both := (fun temp_inp => 
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          nat_mod_from_byte_seq_be ([
              secret (lift_to_both0 (@repr U8 120));
              secret (lift_to_both0 (@repr U8 108));
              secret (lift_to_both0 (@repr U8 137));
              secret (lift_to_both0 (@repr U8 5));
              secret (lift_to_both0 (@repr U8 207));
              secret (lift_to_both0 (@repr U8 175));
              secret (lift_to_both0 (@repr U8 252));
              secret (lift_to_both0 (@repr U8 162));
              secret (lift_to_both0 (@repr U8 22));
              secret (lift_to_both0 (@repr U8 194));
              secret (lift_to_both0 (@repr U8 123));
              secret (lift_to_both0 (@repr U8 145));
              secret (lift_to_both0 (@repr U8 254));
              secret (lift_to_both0 (@repr U8 1));
              secret (lift_to_both0 (@repr U8 216));
              secret (lift_to_both0 (@repr U8 64));
              secret (lift_to_both0 (@repr U8 157));
              secret (lift_to_both0 (@repr U8 47));
              secret (lift_to_both0 (@repr U8 22));
              secret (lift_to_both0 (@repr U8 23));
              secret (lift_to_both0 (@repr U8 90));
              secret (lift_to_both0 (@repr U8 65));
              secret (lift_to_both0 (@repr U8 114));
              secret (lift_to_both0 (@repr U8 190));
              secret (lift_to_both0 (@repr U8 153));
              secret (lift_to_both0 (@repr U8 200));
              secret (lift_to_both0 (@repr U8 253));
              secret (lift_to_both0 (@repr U8 170));
              secret (lift_to_both0 (@repr U8 128));
              secret (lift_to_both0 (@repr U8 93));
              secret (lift_to_both0 (@repr U8 64));
              secret (lift_to_both0 (@repr U8 234))
            ]))
        ) : both (fset.fset0) [interface] (field_element_t)))in
  both_package' _ _ (INVSQRT_A_MINUS_D,(
      invsqrt_a_minus_d_inp,invsqrt_a_minus_d_out)) temp_package_both.
Fail Next Obligation.


Notation "'sqrt_ad_minus_one_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_ad_minus_one_inp'" :=(
  unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'sqrt_ad_minus_one_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_ad_minus_one_out'" :=(
  field_element_t : ChoiceEquality) (at level 2).
Definition SQRT_AD_MINUS_ONE : nat :=
  943.
Program Definition sqrt_ad_minus_one
  : both_package (fset.fset0) [interface] [(SQRT_AD_MINUS_ONE,(
      sqrt_ad_minus_one_inp,sqrt_ad_minus_one_out))] :=
  let temp_package_both := (fun temp_inp => 
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          nat_mod_from_byte_seq_be ([
              secret (lift_to_both0 (@repr U8 55));
              secret (lift_to_both0 (@repr U8 105));
              secret (lift_to_both0 (@repr U8 49));
              secret (lift_to_both0 (@repr U8 191));
              secret (lift_to_both0 (@repr U8 43));
              secret (lift_to_both0 (@repr U8 131));
              secret (lift_to_both0 (@repr U8 72));
              secret (lift_to_both0 (@repr U8 172));
              secret (lift_to_both0 (@repr U8 15));
              secret (lift_to_both0 (@repr U8 60));
              secret (lift_to_both0 (@repr U8 252));
              secret (lift_to_both0 (@repr U8 201));
              secret (lift_to_both0 (@repr U8 49));
              secret (lift_to_both0 (@repr U8 245));
              secret (lift_to_both0 (@repr U8 209));
              secret (lift_to_both0 (@repr U8 253));
              secret (lift_to_both0 (@repr U8 175));
              secret (lift_to_both0 (@repr U8 157));
              secret (lift_to_both0 (@repr U8 142));
              secret (lift_to_both0 (@repr U8 12));
              secret (lift_to_both0 (@repr U8 27));
              secret (lift_to_both0 (@repr U8 120));
              secret (lift_to_both0 (@repr U8 84));
              secret (lift_to_both0 (@repr U8 189));
              secret (lift_to_both0 (@repr U8 126));
              secret (lift_to_both0 (@repr U8 151));
              secret (lift_to_both0 (@repr U8 246));
              secret (lift_to_both0 (@repr U8 160));
              secret (lift_to_both0 (@repr U8 73));
              secret (lift_to_both0 (@repr U8 123));
              secret (lift_to_both0 (@repr U8 46));
              secret (lift_to_both0 (@repr U8 27))
            ]))
        ) : both (fset.fset0) [interface] (field_element_t)))in
  both_package' _ _ (SQRT_AD_MINUS_ONE,(
      sqrt_ad_minus_one_inp,sqrt_ad_minus_one_out)) temp_package_both.
Fail Next Obligation.


Notation "'one_minus_d_sq_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'one_minus_d_sq_inp'" :=(
  unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'one_minus_d_sq_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'one_minus_d_sq_out'" :=(
  field_element_t : ChoiceEquality) (at level 2).
Definition ONE_MINUS_D_SQ : nat :=
  944.
Program Definition one_minus_d_sq
  : both_package (fset.fset0) [interface] [(ONE_MINUS_D_SQ,(
      one_minus_d_sq_inp,one_minus_d_sq_out))] :=
  let temp_package_both := (fun temp_inp => 
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          nat_mod_from_byte_seq_be ([
              secret (lift_to_both0 (@repr U8 2));
              secret (lift_to_both0 (@repr U8 144));
              secret (lift_to_both0 (@repr U8 114));
              secret (lift_to_both0 (@repr U8 168));
              secret (lift_to_both0 (@repr U8 178));
              secret (lift_to_both0 (@repr U8 179));
              secret (lift_to_both0 (@repr U8 224));
              secret (lift_to_both0 (@repr U8 215));
              secret (lift_to_both0 (@repr U8 153));
              secret (lift_to_both0 (@repr U8 148));
              secret (lift_to_both0 (@repr U8 171));
              secret (lift_to_both0 (@repr U8 221));
              secret (lift_to_both0 (@repr U8 190));
              secret (lift_to_both0 (@repr U8 112));
              secret (lift_to_both0 (@repr U8 223));
              secret (lift_to_both0 (@repr U8 228));
              secret (lift_to_both0 (@repr U8 44));
              secret (lift_to_both0 (@repr U8 129));
              secret (lift_to_both0 (@repr U8 161));
              secret (lift_to_both0 (@repr U8 56));
              secret (lift_to_both0 (@repr U8 205));
              secret (lift_to_both0 (@repr U8 94));
              secret (lift_to_both0 (@repr U8 53));
              secret (lift_to_both0 (@repr U8 15));
              secret (lift_to_both0 (@repr U8 226));
              secret (lift_to_both0 (@repr U8 124));
              secret (lift_to_both0 (@repr U8 9));
              secret (lift_to_both0 (@repr U8 193));
              secret (lift_to_both0 (@repr U8 148));
              secret (lift_to_both0 (@repr U8 95));
              secret (lift_to_both0 (@repr U8 193));
              secret (lift_to_both0 (@repr U8 118))
            ]))
        ) : both (fset.fset0) [interface] (field_element_t)))in
  both_package' _ _ (ONE_MINUS_D_SQ,(
      one_minus_d_sq_inp,one_minus_d_sq_out)) temp_package_both.
Fail Next Obligation.


Notation "'d_minus_one_sq_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'d_minus_one_sq_inp'" :=(
  unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'d_minus_one_sq_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'d_minus_one_sq_out'" :=(
  field_element_t : ChoiceEquality) (at level 2).
Definition D_MINUS_ONE_SQ : nat :=
  945.
Program Definition d_minus_one_sq
  : both_package (fset.fset0) [interface] [(D_MINUS_ONE_SQ,(
      d_minus_one_sq_inp,d_minus_one_sq_out))] :=
  let temp_package_both := (fun temp_inp => 
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          nat_mod_from_byte_seq_be ([
              secret (lift_to_both0 (@repr U8 89));
              secret (lift_to_both0 (@repr U8 104));
              secret (lift_to_both0 (@repr U8 179));
              secret (lift_to_both0 (@repr U8 122));
              secret (lift_to_both0 (@repr U8 246));
              secret (lift_to_both0 (@repr U8 108));
              secret (lift_to_both0 (@repr U8 34));
              secret (lift_to_both0 (@repr U8 65));
              secret (lift_to_both0 (@repr U8 76));
              secret (lift_to_both0 (@repr U8 220));
              secret (lift_to_both0 (@repr U8 211));
              secret (lift_to_both0 (@repr U8 47));
              secret (lift_to_both0 (@repr U8 82));
              secret (lift_to_both0 (@repr U8 155));
              secret (lift_to_both0 (@repr U8 78));
              secret (lift_to_both0 (@repr U8 235));
              secret (lift_to_both0 (@repr U8 210));
              secret (lift_to_both0 (@repr U8 158));
              secret (lift_to_both0 (@repr U8 74));
              secret (lift_to_both0 (@repr U8 44));
              secret (lift_to_both0 (@repr U8 176));
              secret (lift_to_both0 (@repr U8 30));
              secret (lift_to_both0 (@repr U8 25));
              secret (lift_to_both0 (@repr U8 153));
              secret (lift_to_both0 (@repr U8 49));
              secret (lift_to_both0 (@repr U8 173));
              secret (lift_to_both0 (@repr U8 90));
              secret (lift_to_both0 (@repr U8 170));
              secret (lift_to_both0 (@repr U8 68));
              secret (lift_to_both0 (@repr U8 237));
              secret (lift_to_both0 (@repr U8 77));
              secret (lift_to_both0 (@repr U8 32))
            ]))
        ) : both (fset.fset0) [interface] (field_element_t)))in
  both_package' _ _ (D_MINUS_ONE_SQ,(
      d_minus_one_sq_inp,d_minus_one_sq_out)) temp_package_both.
Fail Next Obligation.


Notation "'base_point_encoded_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'base_point_encoded_inp'" :=(
  unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'base_point_encoded_out'" :=(
  ristretto_point_encoded_t : choice_type) (in custom pack_type at level 2).
Notation "'base_point_encoded_out'" :=(
  ristretto_point_encoded_t : ChoiceEquality) (at level 2).
Definition BASE_POINT_ENCODED : nat :=
  946.
Program Definition base_point_encoded
  : both_package (fset.fset0) [interface] [(BASE_POINT_ENCODED,(
      base_point_encoded_inp,base_point_encoded_out))] :=
  let temp_package_both := (fun temp_inp => 
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (32) ([
              secret (lift_to_both0 (@repr U8 226));
              secret (lift_to_both0 (@repr U8 242));
              secret (lift_to_both0 (@repr U8 174));
              secret (lift_to_both0 (@repr U8 10));
              secret (lift_to_both0 (@repr U8 106));
              secret (lift_to_both0 (@repr U8 188));
              secret (lift_to_both0 (@repr U8 78));
              secret (lift_to_both0 (@repr U8 113));
              secret (lift_to_both0 (@repr U8 168));
              secret (lift_to_both0 (@repr U8 132));
              secret (lift_to_both0 (@repr U8 169));
              secret (lift_to_both0 (@repr U8 97));
              secret (lift_to_both0 (@repr U8 197));
              secret (lift_to_both0 (@repr U8 0));
              secret (lift_to_both0 (@repr U8 81));
              secret (lift_to_both0 (@repr U8 95));
              secret (lift_to_both0 (@repr U8 88));
              secret (lift_to_both0 (@repr U8 227));
              secret (lift_to_both0 (@repr U8 11));
              secret (lift_to_both0 (@repr U8 106));
              secret (lift_to_both0 (@repr U8 165));
              secret (lift_to_both0 (@repr U8 130));
              secret (lift_to_both0 (@repr U8 221));
              secret (lift_to_both0 (@repr U8 141));
              secret (lift_to_both0 (@repr U8 182));
              secret (lift_to_both0 (@repr U8 166));
              secret (lift_to_both0 (@repr U8 89));
              secret (lift_to_both0 (@repr U8 69));
              secret (lift_to_both0 (@repr U8 224));
              secret (lift_to_both0 (@repr U8 141));
              secret (lift_to_both0 (@repr U8 45));
              secret (lift_to_both0 (@repr U8 118))
            ]))
        ) : both (fset.fset0) [interface] (ristretto_point_encoded_t)))in
  both_package' _ _ (BASE_POINT_ENCODED,(
      base_point_encoded_inp,base_point_encoded_out)) temp_package_both.
Fail Next Obligation.


Notation "'base_point_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'base_point_inp'" :=(
  unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'base_point_out'" :=(
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'base_point_out'" :=(ristretto_point_t : ChoiceEquality) (at level 2).
Definition BASE_POINT : nat :=
  947.
Program Definition base_point
  : both_package (fset.fset0) [interface
  #val #[ BASE_POINT_ENCODED ] : base_point_encoded_inp → base_point_encoded_out ;
  #val #[ DECODE ] : decode_inp → decode_out ] [(BASE_POINT,(
      base_point_inp,base_point_out))] :=
  let temp_package_both := (fun temp_inp => 
    
    let base_point_encoded := package_both base_point_encoded tt in
    let decode := fun x_0 => package_both decode (x_0) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (result_unwrap (decode (
              base_point_encoded )))
        ) : both (fset.fset0) [interface
      #val #[ BASE_POINT_ENCODED ] : base_point_encoded_inp → base_point_encoded_out ;
      #val #[ DECODE ] : decode_inp → decode_out ] (ristretto_point_t)))in
  both_package' _ _ (BASE_POINT,(
      base_point_inp,base_point_out)) temp_package_both.
Fail Next Obligation.


Notation "'identity_point_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'identity_point_inp'" :=(
  unit_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'identity_point_out'" :=(
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'identity_point_out'" :=(
  ristretto_point_t : ChoiceEquality) (at level 2).
Definition IDENTITY_POINT : nat :=
  948.
Program Definition identity_point
  : both_package (fset.fset0) [interface #val #[ FE ] : fe_inp → fe_out ] [(
    IDENTITY_POINT,(identity_point_inp,identity_point_out))] :=
  let temp_package_both := (fun temp_inp => 
    
    let fe := fun x_0 => package_both fe (x_0) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            fe (lift_to_both0 (usize 0)),
            fe (lift_to_both0 (usize 1)),
            fe (lift_to_both0 (usize 1)),
            fe (lift_to_both0 (usize 0))
          ))
        ) : both (fset.fset0) [interface #val #[ FE ] : fe_inp → fe_out ] (
        ristretto_point_t)))in
  both_package' _ _ (IDENTITY_POINT,(
      identity_point_inp,identity_point_out)) temp_package_both.
Fail Next Obligation.


Notation "'fe_inp'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'fe_inp'" :=(uint_size : ChoiceEquality) (at level 2).
Notation "'fe_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'fe_out'" :=(field_element_t : ChoiceEquality) (at level 2).
Definition FE : nat :=
  950.
Program Definition fe
  : both_package (fset.fset0) [interface] [(FE,(fe_inp,fe_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_949) := temp_inp : uint_size in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (nat_mod_from_literal (
            0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
            pub_u128 (is_pure (lift_to_both0 x_949))))
        ) : both (fset.fset0) [interface] (field_element_t)))in
  both_package' _ _ (FE,(fe_inp,fe_out)) temp_package_both.
Fail Next Obligation.

Definition res_951_loc : ChoiceEqualityLocation :=
  (bool_ChoiceEquality ; 952%nat).
Notation "'geq_p_inp'" :=(
  seq uint8 : choice_type) (in custom pack_type at level 2).
Notation "'geq_p_inp'" :=(seq uint8 : ChoiceEquality) (at level 2).
Notation "'geq_p_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'geq_p_out'" :=(bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition GEQ_P : nat :=
  958.
Program Definition geq_p
  : both_package (CEfset ([res_951_loc])) [interface] [(GEQ_P,(
      geq_p_inp,geq_p_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_955) := temp_inp : seq uint8 in
    
    ((letb p_seq_953 : seq uint8 :=
          [
            secret (lift_to_both0 (@repr U8 237));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 127))
          ] in
        letbm res_951 : bool_ChoiceEquality loc( res_951_loc ) :=
          lift_to_both0 ((true : bool_ChoiceEquality)) in
        letb res_951 :=
          foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                lift_to_both0 p_seq_953)) res_951 (L := (CEfset (
                [res_951_loc]))) (I := ([interface])) (fun index_954 res_951 =>
            letb x_index_956 : int8 :=
              uint8_declassify (seq_index (x_955) (lift_to_both0 index_954)) in
            letb p_index_957 : int8 :=
              uint8_declassify (seq_index (p_seq_953) (
                  lift_to_both0 index_954)) in
            letb 'res_951 :=
              if (lift_to_both0 x_index_956) !=.? (
                lift_to_both0 p_index_957) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([res_951_loc])) (L2 := CEfset (
                [res_951_loc])) (I1 := [interface]) (I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm res_951 loc( res_951_loc ) :=
                  (lift_to_both0 x_index_956) >.? (lift_to_both0 p_index_957) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 res_951)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 res_951)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 res_951)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 res_951)
        ) : both (CEfset ([res_951_loc])) [interface] (bool_ChoiceEquality)))in
  both_package' _ _ (GEQ_P,(geq_p_inp,geq_p_out)) temp_package_both.
Fail Next Obligation.


Notation "'is_negative_inp'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'is_negative_inp'" :=(field_element_t : ChoiceEquality) (at level 2).
Notation "'is_negative_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'is_negative_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition IS_NEGATIVE : nat :=
  960.
Program Definition is_negative
  : both_package (fset.fset0) [interface #val #[ FE ] : fe_inp → fe_out ] [(
    IS_NEGATIVE,(is_negative_inp,is_negative_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(e_959) := temp_inp : field_element_t in
    
    let fe := fun x_0 => package_both fe (x_0) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
              lift_to_both0 e_959) rem (fe (lift_to_both0 (usize 2)))) =.? (fe (
              lift_to_both0 (usize 1))))
        ) : both (fset.fset0) [interface #val #[ FE ] : fe_inp → fe_out ] (
        bool_ChoiceEquality)))in
  both_package' _ _ (IS_NEGATIVE,(
      is_negative_inp,is_negative_out)) temp_package_both.
Fail Next Obligation.


Notation "'eq_inp'" :=(
  field_element_t '× field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'eq_inp'" :=(
  field_element_t '× field_element_t : ChoiceEquality) (at level 2).
Notation "'eq_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'eq_out'" :=(bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition EQ : nat :=
  963.
Program Definition eq
  : both_package (fset.fset0) [interface] [(EQ,(eq_inp,eq_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(u_961 , v_962) := temp_inp : field_element_t '× field_element_t in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
            lift_to_both0 u_961) =.? (lift_to_both0 v_962))
        ) : both (fset.fset0) [interface] (bool_ChoiceEquality)))in
  both_package' _ _ (EQ,(eq_inp,eq_out)) temp_package_both.
Fail Next Obligation.


Notation "'select_inp'" :=(
  field_element_t '× bool_ChoiceEquality '× field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'select_inp'" :=(
  field_element_t '× bool_ChoiceEquality '× field_element_t : ChoiceEquality) (at level 2).
Notation "'select_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'select_out'" :=(field_element_t : ChoiceEquality) (at level 2).
Definition SELECT : nat :=
  967.
Program Definition select
  : both_package (fset.fset0) [interface] [(SELECT,(select_inp,select_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      u_965 , cond_964 , v_966) := temp_inp : field_element_t '× bool_ChoiceEquality '× field_element_t in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) (lift_to_both0 cond_964)
          then lift_to_both0 u_965
          else lift_to_both0 v_966)
        ) : both (fset.fset0) [interface] (field_element_t)))in
  both_package' _ _ (SELECT,(select_inp,select_out)) temp_package_both.
Fail Next Obligation.


Notation "'neg_fe_inp'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'neg_fe_inp'" :=(field_element_t : ChoiceEquality) (at level 2).
Notation "'neg_fe_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'neg_fe_out'" :=(field_element_t : ChoiceEquality) (at level 2).
Definition NEG_FE : nat :=
  969.
Program Definition neg_fe
  : both_package (fset.fset0) [interface #val #[ FE ] : fe_inp → fe_out ] [(
    NEG_FE,(neg_fe_inp,neg_fe_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(u_968) := temp_inp : field_element_t in
    
    let fe := fun x_0 => package_both fe (x_0) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((fe (lift_to_both0 (
                usize 0))) -% (lift_to_both0 u_968))
        ) : both (fset.fset0) [interface #val #[ FE ] : fe_inp → fe_out ] (
        field_element_t)))in
  both_package' _ _ (NEG_FE,(neg_fe_inp,neg_fe_out)) temp_package_both.
Fail Next Obligation.


Notation "'abs_inp'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'abs_inp'" :=(field_element_t : ChoiceEquality) (at level 2).
Notation "'abs_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'abs_out'" :=(field_element_t : ChoiceEquality) (at level 2).
Definition ABS : nat :=
  971.
Program Definition abs
  : both_package (fset.fset0) [interface
  #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
  #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ;
  #val #[ SELECT ] : select_inp → select_out ] [(ABS,(abs_inp,abs_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(u_970) := temp_inp : field_element_t in
    
    let is_negative := fun x_0 => package_both is_negative (x_0) in
    let neg_fe := fun x_0 => package_both neg_fe (x_0) in
    let select := fun x_0 x_1 x_2 => package_both select (x_0,x_1,x_2) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (select (neg_fe (
              lift_to_both0 u_970)) (is_negative (lift_to_both0 u_970)) (
            lift_to_both0 u_970))
        ) : both (fset.fset0) [interface
      #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
      #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ;
      #val #[ SELECT ] : select_inp → select_out ] (field_element_t)))in
  both_package' _ _ (ABS,(abs_inp,abs_out)) temp_package_both.
Fail Next Obligation.

Definition r_972_loc : ChoiceEqualityLocation :=
  (field_element_t ; 973%nat).
Notation "'sqrt_ratio_m1_inp'" :=(
  field_element_t '× field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_ratio_m1_inp'" :=(
  field_element_t '× field_element_t : ChoiceEquality) (at level 2).
Notation "'sqrt_ratio_m1_out'" :=((bool_ChoiceEquality '× field_element_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_ratio_m1_out'" :=((bool_ChoiceEquality '× field_element_t
  ) : ChoiceEquality) (at level 2).
Definition SQRT_RATIO_M1 : nat :=
  984.
Program Definition sqrt_ratio_m1
  : both_package (CEfset ([r_972_loc])) [interface
  #val #[ P ] : p_inp → p_out ;
  #val #[ SQRT_M1 ] : sqrt_m1_inp → sqrt_m1_out ;
  #val #[ ABS ] : abs_inp → abs_out ; #val #[ EQ ] : eq_inp → eq_out ;
  #val #[ FE ] : fe_inp → fe_out ;
  #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ;
  #val #[ SELECT ] : select_inp → select_out ] [(SQRT_RATIO_M1,(
      sqrt_ratio_m1_inp,sqrt_ratio_m1_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(u_977 , v_974) := temp_inp : field_element_t '× field_element_t in
    
    let p := package_both p tt in
    let sqrt_m1 := package_both sqrt_m1 tt in
    let abs := fun x_0 => package_both abs (x_0) in
    let eq := fun x_0 x_1 => package_both eq (x_0,x_1) in
    let fe := fun x_0 => package_both fe (x_0) in
    let neg_fe := fun x_0 => package_both neg_fe (x_0) in
    let select := fun x_0 x_1 x_2 => package_both select (x_0,x_1,x_2) in
    ((letb v3_975 : field_element_t :=
          (nat_mod_pow (lift_to_both0 v_974) (lift_to_both0 (
                @repr U128 2))) *% (lift_to_both0 v_974) in
        letb v7_976 : field_element_t :=
          (nat_mod_pow (lift_to_both0 v3_975) (lift_to_both0 (
                @repr U128 2))) *% (lift_to_both0 v_974) in
        letbm r_972 : field_element_t loc( r_972_loc ) :=
          ((lift_to_both0 u_977) *% (lift_to_both0 v3_975)) *% (
            nat_mod_pow_felem ((lift_to_both0 u_977) *% (
                lift_to_both0 v7_976)) (((p ) -% (fe (lift_to_both0 (
                      usize 5)))) /% (fe (lift_to_both0 (usize 8))))) in
        letb check_978 : field_element_t :=
          (lift_to_both0 v_974) *% (nat_mod_pow (lift_to_both0 r_972) (
              lift_to_both0 (@repr U128 2))) in
        letb correct_sign_sqrt_979 : bool_ChoiceEquality :=
          eq (lift_to_both0 check_978) (lift_to_both0 u_977) in
        letb flipped_sign_sqrt_980 : bool_ChoiceEquality :=
          eq (lift_to_both0 check_978) (neg_fe (lift_to_both0 u_977)) in
        letb flipped_sign_sqrt_i_981 : bool_ChoiceEquality :=
          eq (lift_to_both0 check_978) ((neg_fe (lift_to_both0 u_977)) *% (
              sqrt_m1 )) in
        letb r_prime_982 : field_element_t :=
          (sqrt_m1 ) *% (lift_to_both0 r_972) in
        letbm r_972 loc( r_972_loc ) :=
          select (lift_to_both0 r_prime_982) ((
              lift_to_both0 flipped_sign_sqrt_980) || (
              lift_to_both0 flipped_sign_sqrt_i_981)) (lift_to_both0 r_972) in
        letbm r_972 loc( r_972_loc ) := abs (lift_to_both0 r_972) in
        letb was_square_983 : bool_ChoiceEquality :=
          (lift_to_both0 correct_sign_sqrt_979) || (
            lift_to_both0 flipped_sign_sqrt_980) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 was_square_983,
            lift_to_both0 r_972
          ))
        ) : both (CEfset ([r_972_loc])) [interface
      #val #[ P ] : p_inp → p_out ;
      #val #[ SQRT_M1 ] : sqrt_m1_inp → sqrt_m1_out ;
      #val #[ ABS ] : abs_inp → abs_out ; #val #[ EQ ] : eq_inp → eq_out ;
      #val #[ FE ] : fe_inp → fe_out ;
      #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ;
      #val #[ SELECT ] : select_inp → select_out ] ((
          bool_ChoiceEquality '×
          field_element_t
        ))))in
  both_package' _ _ (SQRT_RATIO_M1,(
      sqrt_ratio_m1_inp,sqrt_ratio_m1_out)) temp_package_both.
Fail Next Obligation.

Definition s_985_loc : ChoiceEqualityLocation :=
  (field_element_t ; 986%nat).
Notation "'map_inp'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'map_inp'" :=(field_element_t : ChoiceEquality) (at level 2).
Notation "'map_out'" :=(
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'map_out'" :=(ristretto_point_t : ChoiceEquality) (at level 2).
Definition MAP : nat :=
  1001.
Program Definition map
  : both_package (CEfset ([s_985_loc])) [interface
  #val #[ D ] : d_inp → d_out ;
  #val #[ D_MINUS_ONE_SQ ] : d_minus_one_sq_inp → d_minus_one_sq_out ;
  #val #[ ONE_MINUS_D_SQ ] : one_minus_d_sq_inp → one_minus_d_sq_out ;
  #val #[ SQRT_AD_MINUS_ONE ] : sqrt_ad_minus_one_inp → sqrt_ad_minus_one_out ;
  #val #[ SQRT_M1 ] : sqrt_m1_inp → sqrt_m1_out ;
  #val #[ ABS ] : abs_inp → abs_out ; #val #[ FE ] : fe_inp → fe_out ;
  #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ;
  #val #[ SELECT ] : select_inp → select_out ;
  #val #[ SQRT_RATIO_M1 ] : sqrt_ratio_m1_inp → sqrt_ratio_m1_out ] [(MAP,(
      map_inp,map_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(t_989) := temp_inp : field_element_t in
    
    let d := package_both d tt in
    let d_minus_one_sq := package_both d_minus_one_sq tt in
    let one_minus_d_sq := package_both one_minus_d_sq tt in
    let sqrt_ad_minus_one := package_both sqrt_ad_minus_one tt in
    let sqrt_m1 := package_both sqrt_m1 tt in
    let abs := fun x_0 => package_both abs (x_0) in
    let fe := fun x_0 => package_both fe (x_0) in
    let neg_fe := fun x_0 => package_both neg_fe (x_0) in
    let select := fun x_0 x_1 x_2 => package_both select (x_0,x_1,x_2) in
    let sqrt_ratio_m1 := fun x_0 x_1 => package_both sqrt_ratio_m1 (x_0,x_1) in
    ((letb one_987 : field_element_t := fe (lift_to_both0 (usize 1)) in
        letb minus_one_988 : field_element_t :=
          neg_fe (lift_to_both0 one_987) in
        letb r_990 : field_element_t :=
          (sqrt_m1 ) *% (nat_mod_pow (lift_to_both0 t_989) (lift_to_both0 (
                @repr U128 2))) in
        letb u_991 : field_element_t :=
          ((lift_to_both0 r_990) +% (lift_to_both0 one_987)) *% (
            one_minus_d_sq ) in
        letb v_992 : field_element_t :=
          ((lift_to_both0 minus_one_988) -% ((lift_to_both0 r_990) *% (
                d ))) *% ((lift_to_both0 r_990) +% (d )) in
        letb '(was_square_993, s_985) : (bool_ChoiceEquality '× field_element_t
          ) :=
          sqrt_ratio_m1 (lift_to_both0 u_991) (lift_to_both0 v_992) in
        letb s_prime_994 : field_element_t :=
          neg_fe (abs ((lift_to_both0 s_985) *% (lift_to_both0 t_989))) in
        letbm s_985 loc( s_985_loc ) :=
          select (lift_to_both0 s_985) (lift_to_both0 was_square_993) (
            lift_to_both0 s_prime_994) in
        letb c_995 : field_element_t :=
          select (lift_to_both0 minus_one_988) (lift_to_both0 was_square_993) (
            lift_to_both0 r_990) in
        letb n_996 : field_element_t :=
          (((lift_to_both0 c_995) *% ((lift_to_both0 r_990) -% (
                  lift_to_both0 one_987))) *% (d_minus_one_sq )) -% (
            lift_to_both0 v_992) in
        letb w0_997 : field_element_t :=
          ((fe (lift_to_both0 (usize 2))) *% (lift_to_both0 s_985)) *% (
            lift_to_both0 v_992) in
        letb w1_998 : field_element_t :=
          (lift_to_both0 n_996) *% (sqrt_ad_minus_one ) in
        letb w2_999 : field_element_t :=
          (lift_to_both0 one_987) -% (nat_mod_pow (lift_to_both0 s_985) (
              lift_to_both0 (@repr U128 2))) in
        letb w3_1000 : field_element_t :=
          (lift_to_both0 one_987) +% (nat_mod_pow (lift_to_both0 s_985) (
              lift_to_both0 (@repr U128 2))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            (lift_to_both0 w0_997) *% (lift_to_both0 w3_1000),
            (lift_to_both0 w2_999) *% (lift_to_both0 w1_998),
            (lift_to_both0 w1_998) *% (lift_to_both0 w3_1000),
            (lift_to_both0 w0_997) *% (lift_to_both0 w2_999)
          ))
        ) : both (CEfset ([s_985_loc])) [interface
      #val #[ D ] : d_inp → d_out ;
      #val #[ D_MINUS_ONE_SQ ] : d_minus_one_sq_inp → d_minus_one_sq_out ;
      #val #[ ONE_MINUS_D_SQ ] : one_minus_d_sq_inp → one_minus_d_sq_out ;
      #val #[ SQRT_AD_MINUS_ONE ] : sqrt_ad_minus_one_inp → sqrt_ad_minus_one_out ;
      #val #[ SQRT_M1 ] : sqrt_m1_inp → sqrt_m1_out ;
      #val #[ ABS ] : abs_inp → abs_out ; #val #[ FE ] : fe_inp → fe_out ;
      #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ;
      #val #[ SELECT ] : select_inp → select_out ;
      #val #[ SQRT_RATIO_M1 ] : sqrt_ratio_m1_inp → sqrt_ratio_m1_out ] (
        ristretto_point_t)))in
  both_package' _ _ (MAP,(map_inp,map_out)) temp_package_both.
Fail Next Obligation.

Definition r0_bytes_1002_loc : ChoiceEqualityLocation :=
  (seq int8 ; 1004%nat).
Definition r1_bytes_1003_loc : ChoiceEqualityLocation :=
  (seq int8 ; 1005%nat).
Notation "'one_way_map_inp'" :=(
  byte_string_t : choice_type) (in custom pack_type at level 2).
Notation "'one_way_map_inp'" :=(byte_string_t : ChoiceEquality) (at level 2).
Notation "'one_way_map_out'" :=(
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'one_way_map_out'" :=(
  ristretto_point_t : ChoiceEquality) (at level 2).
Definition ONE_WAY_MAP : nat :=
  1013.
Program Definition one_way_map
  : both_package (CEfset ([r0_bytes_1002_loc ; r1_bytes_1003_loc])) [interface
  #val #[ ADD ] : add_inp → add_out ; #val #[ MAP ] : map_inp → map_out ] [(
    ONE_WAY_MAP,(one_way_map_inp,one_way_map_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(b_1006) := temp_inp : byte_string_t in
    
    let add := fun x_0 x_1 => package_both add (x_0,x_1) in
    let map := fun x_0 => package_both map (x_0) in
    ((letb r0_bytes_1007 : seq uint8 :=
          array_slice (lift_to_both0 b_1006) (lift_to_both0 (usize 0)) (
            lift_to_both0 (usize 32)) in
        letb r1_bytes_1008 : seq uint8 :=
          array_slice (lift_to_both0 b_1006) (lift_to_both0 (usize 32)) (
            lift_to_both0 (usize 32)) in
        letbm r0_bytes_1002 : seq int8 loc( r0_bytes_1002_loc ) :=
          seq_declassify (lift_to_both0 r0_bytes_1007) in
        letbm r1_bytes_1003 : seq int8 loc( r1_bytes_1003_loc ) :=
          seq_declassify (lift_to_both0 r1_bytes_1008) in
        letb r0_bytes_1002 : seq int8 :=
          seq_upd r0_bytes_1002 (lift_to_both0 (usize 31)) (is_pure ((
                seq_index (r0_bytes_1002) (lift_to_both0 (usize 31))) .% (
                lift_to_both0 (@repr U8 128)))) in
        letb r1_bytes_1003 : seq int8 :=
          seq_upd r1_bytes_1003 (lift_to_both0 (usize 31)) (is_pure ((
                seq_index (r1_bytes_1003) (lift_to_both0 (usize 31))) .% (
                lift_to_both0 (@repr U8 128)))) in
        letb r0_1009 : field_element_t :=
          nat_mod_from_public_byte_seq_le (lift_to_both0 r0_bytes_1002) in
        letb r1_1010 : field_element_t :=
          nat_mod_from_public_byte_seq_le (lift_to_both0 r1_bytes_1003) in
        letb p1_1011 : (
            field_element_t '×
            field_element_t '×
            field_element_t '×
            field_element_t
          ) :=
          map (lift_to_both0 r0_1009) in
        letb p2_1012 : (
            field_element_t '×
            field_element_t '×
            field_element_t '×
            field_element_t
          ) :=
          map (lift_to_both0 r1_1010) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (add (
            lift_to_both0 p1_1011) (lift_to_both0 p2_1012))
        ) : both (CEfset ([r0_bytes_1002_loc ; r1_bytes_1003_loc])) [interface
      #val #[ ADD ] : add_inp → add_out ; #val #[ MAP ] : map_inp → map_out
      ] (ristretto_point_t)))in
  both_package' _ _ (ONE_WAY_MAP,(
      one_way_map_inp,one_way_map_out)) temp_package_both.
Fail Next Obligation.

Definition y_1014_loc : ChoiceEqualityLocation :=
  (field_element_t ; 1015%nat).
Notation "'encode_inp'" :=(
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'encode_inp'" :=(ristretto_point_t : ChoiceEquality) (at level 2).
Notation "'encode_out'" :=(
  ristretto_point_encoded_t : choice_type) (in custom pack_type at level 2).
Notation "'encode_out'" :=(
  ristretto_point_encoded_t : ChoiceEquality) (at level 2).
Definition ENCODE : nat :=
  1035.
Program Definition encode
  : both_package (CEfset ([y_1014_loc])) [interface
  #val #[ INVSQRT_A_MINUS_D ] : invsqrt_a_minus_d_inp → invsqrt_a_minus_d_out ;
  #val #[ SQRT_M1 ] : sqrt_m1_inp → sqrt_m1_out ;
  #val #[ ABS ] : abs_inp → abs_out ; #val #[ FE ] : fe_inp → fe_out ;
  #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
  #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ;
  #val #[ SELECT ] : select_inp → select_out ;
  #val #[ SQRT_RATIO_M1 ] : sqrt_ratio_m1_inp → sqrt_ratio_m1_out ] [(ENCODE,(
      encode_inp,encode_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(u_1016) := temp_inp : ristretto_point_t in
    
    let invsqrt_a_minus_d := package_both invsqrt_a_minus_d tt in
    let sqrt_m1 := package_both sqrt_m1 tt in
    let abs := fun x_0 => package_both abs (x_0) in
    let fe := fun x_0 => package_both fe (x_0) in
    let is_negative := fun x_0 => package_both is_negative (x_0) in
    let neg_fe := fun x_0 => package_both neg_fe (x_0) in
    let select := fun x_0 x_1 x_2 => package_both select (x_0,x_1,x_2) in
    let sqrt_ratio_m1 := fun x_0 x_1 => package_both sqrt_ratio_m1 (x_0,x_1) in
    ((letb '(x0_1017, y0_1018, z0_1019, t0_1020) : (
            field_element_t '×
            field_element_t '×
            field_element_t '×
            field_element_t
          ) :=
          lift_to_both0 u_1016 in
        letb u1_1021 : field_element_t :=
          ((lift_to_both0 z0_1019) +% (lift_to_both0 y0_1018)) *% ((
              lift_to_both0 z0_1019) -% (lift_to_both0 y0_1018)) in
        letb u2_1022 : field_element_t :=
          (lift_to_both0 x0_1017) *% (lift_to_both0 y0_1018) in
        letb '(_, invsqrt_1023) : (bool_ChoiceEquality '× field_element_t) :=
          sqrt_ratio_m1 (fe (lift_to_both0 (usize 1))) ((
              lift_to_both0 u1_1021) *% (nat_mod_pow (lift_to_both0 u2_1022) (
                lift_to_both0 (@repr U128 2)))) in
        letb den1_1024 : field_element_t :=
          (lift_to_both0 invsqrt_1023) *% (lift_to_both0 u1_1021) in
        letb den2_1025 : field_element_t :=
          (lift_to_both0 invsqrt_1023) *% (lift_to_both0 u2_1022) in
        letb z_inv_1026 : field_element_t :=
          ((lift_to_both0 den1_1024) *% (lift_to_both0 den2_1025)) *% (
            lift_to_both0 t0_1020) in
        letb ix0_1027 : field_element_t :=
          (lift_to_both0 x0_1017) *% (sqrt_m1 ) in
        letb iy0_1028 : field_element_t :=
          (lift_to_both0 y0_1018) *% (sqrt_m1 ) in
        letb enchanted_denominator_1029 : field_element_t :=
          (lift_to_both0 den1_1024) *% (invsqrt_a_minus_d ) in
        letb rotate_1030 : bool_ChoiceEquality :=
          is_negative ((lift_to_both0 t0_1020) *% (lift_to_both0 z_inv_1026)) in
        letb x_1031 : field_element_t :=
          select (lift_to_both0 iy0_1028) (lift_to_both0 rotate_1030) (
            lift_to_both0 x0_1017) in
        letbm y_1014 : field_element_t loc( y_1014_loc ) :=
          select (lift_to_both0 ix0_1027) (lift_to_both0 rotate_1030) (
            lift_to_both0 y0_1018) in
        letb z_1032 : field_element_t := lift_to_both0 z0_1019 in
        letb den_inv_1033 : field_element_t :=
          select (lift_to_both0 enchanted_denominator_1029) (
            lift_to_both0 rotate_1030) (lift_to_both0 den2_1025) in
        letbm y_1014 loc( y_1014_loc ) :=
          select (neg_fe (lift_to_both0 y_1014)) (is_negative ((
                lift_to_both0 x_1031) *% (lift_to_both0 z_inv_1026))) (
            lift_to_both0 y_1014) in
        letb s_1034 : field_element_t :=
          abs ((lift_to_both0 den_inv_1033) *% ((lift_to_both0 z_1032) -% (
                lift_to_both0 y_1014))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_update_start (
            array_new_ (default : uint8) (32)) (nat_mod_to_byte_seq_le (
              lift_to_both0 s_1034)))
        ) : both (CEfset ([y_1014_loc])) [interface
      #val #[ INVSQRT_A_MINUS_D ] : invsqrt_a_minus_d_inp → invsqrt_a_minus_d_out ;
      #val #[ SQRT_M1 ] : sqrt_m1_inp → sqrt_m1_out ;
      #val #[ ABS ] : abs_inp → abs_out ; #val #[ FE ] : fe_inp → fe_out ;
      #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
      #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ;
      #val #[ SELECT ] : select_inp → select_out ;
      #val #[ SQRT_RATIO_M1 ] : sqrt_ratio_m1_inp → sqrt_ratio_m1_out ] (
        ristretto_point_encoded_t)))in
  both_package' _ _ (ENCODE,(encode_inp,encode_out)) temp_package_both.
Fail Next Obligation.

Definition ret_1036_loc : ChoiceEqualityLocation :=
  ((result (int8) (ristretto_point_t)) ; 1037%nat).
Notation "'decode_inp'" :=(
  ristretto_point_encoded_t : choice_type) (in custom pack_type at level 2).
Notation "'decode_inp'" :=(
  ristretto_point_encoded_t : ChoiceEquality) (at level 2).
Notation "'decode_out'" :=(
  decode_result_t : choice_type) (in custom pack_type at level 2).
Notation "'decode_out'" :=(decode_result_t : ChoiceEquality) (at level 2).
Definition DECODE : nat :=
  1053.
Program Definition decode
  : both_package (CEfset ([ret_1036_loc])) [interface
  #val #[ D ] : d_inp → d_out ; #val #[ ABS ] : abs_inp → abs_out ;
  #val #[ FE ] : fe_inp → fe_out ; #val #[ GEQ_P ] : geq_p_inp → geq_p_out ;
  #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
  #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ;
  #val #[ SQRT_RATIO_M1 ] : sqrt_ratio_m1_inp → sqrt_ratio_m1_out ] [(DECODE,(
      decode_inp,decode_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(u_1038) := temp_inp : ristretto_point_encoded_t in
    
    let d := package_both d tt in
    let abs := fun x_0 => package_both abs (x_0) in
    let fe := fun x_0 => package_both fe (x_0) in
    let geq_p := fun x_0 => package_both geq_p (x_0) in
    let is_negative := fun x_0 => package_both is_negative (x_0) in
    let neg_fe := fun x_0 => package_both neg_fe (x_0) in
    let sqrt_ratio_m1 := fun x_0 x_1 => package_both sqrt_ratio_m1 (x_0,x_1) in
    ((letbm ret_1036 : (result (int8) (
              ristretto_point_t)) loc( ret_1036_loc ) :=
          @Err ristretto_point_t int8 (lift_to_both0 decoding_error_v) in
        letb s_1039 : field_element_t :=
          nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 u_1038)) in
        letb 'ret_1036 :=
          if (negb (geq_p (array_to_le_bytes (lift_to_both0 u_1038)))) && (
            negb (is_negative (lift_to_both0 s_1039))) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset ([ret_1036_loc])) (L2 := CEfset (
            [ret_1036_loc])) (I1 := [interface #val #[ D ] : d_inp → d_out ;
          #val #[ ABS ] : abs_inp → abs_out ;
          #val #[ FE ] : fe_inp → fe_out ;
          #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
          #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ;
          #val #[ SQRT_RATIO_M1 ] : sqrt_ratio_m1_inp → sqrt_ratio_m1_out
          ]) (I2 := [interface #val #[ D ] : d_inp → d_out ;
          #val #[ ABS ] : abs_inp → abs_out ;
          #val #[ FE ] : fe_inp → fe_out ;
          #val #[ GEQ_P ] : geq_p_inp → geq_p_out ;
          #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
          #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ;
          #val #[ SQRT_RATIO_M1 ] : sqrt_ratio_m1_inp → sqrt_ratio_m1_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letb one_1040 : field_element_t := fe (lift_to_both0 (usize 1)) in
            letb ss_1041 : field_element_t :=
              nat_mod_pow (lift_to_both0 s_1039) (lift_to_both0 (
                  @repr U128 2)) in
            letb u1_1042 : field_element_t :=
              (lift_to_both0 one_1040) -% (lift_to_both0 ss_1041) in
            letb u2_1043 : field_element_t :=
              (lift_to_both0 one_1040) +% (lift_to_both0 ss_1041) in
            letb u2_sqr_1044 : field_element_t :=
              nat_mod_pow (lift_to_both0 u2_1043) (lift_to_both0 (
                  @repr U128 2)) in
            letb v_1045 : field_element_t :=
              (neg_fe ((d ) *% (nat_mod_pow (lift_to_both0 u1_1042) (
                      lift_to_both0 (@repr U128 2))))) -% (
                lift_to_both0 u2_sqr_1044) in
            letb '(was_square_1046, invsqrt_1047) : (
                bool_ChoiceEquality '×
                field_element_t
              ) :=
              sqrt_ratio_m1 (lift_to_both0 one_1040) ((
                  lift_to_both0 v_1045) *% (lift_to_both0 u2_sqr_1044)) in
            letb den_x_1048 : field_element_t :=
              (lift_to_both0 invsqrt_1047) *% (lift_to_both0 u2_1043) in
            letb den_y_1049 : field_element_t :=
              ((lift_to_both0 invsqrt_1047) *% (lift_to_both0 den_x_1048)) *% (
                lift_to_both0 v_1045) in
            letb x_1050 : field_element_t :=
              abs (((lift_to_both0 s_1039) +% (lift_to_both0 s_1039)) *% (
                  lift_to_both0 den_x_1048)) in
            letb y_1051 : field_element_t :=
              (lift_to_both0 u1_1042) *% (lift_to_both0 den_y_1049) in
            letb t_1052 : field_element_t :=
              (lift_to_both0 x_1050) *% (lift_to_both0 y_1051) in
            letb 'ret_1036 :=
              if negb (((negb (lift_to_both0 was_square_1046)) || (is_negative (
                      lift_to_both0 t_1052))) || ((lift_to_both0 y_1051) =.? (
                    fe (lift_to_both0 (usize 0))))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([ret_1036_loc])) (L2 := CEfset (
                [ret_1036_loc])) (I1 := [interface]) (I2 := [interface
              #val #[ D ] : d_inp → d_out ;
              #val #[ ABS ] : abs_inp → abs_out ;
              #val #[ FE ] : fe_inp → fe_out ;
              #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
              #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ;
              #val #[ SQRT_RATIO_M1 ] : sqrt_ratio_m1_inp → sqrt_ratio_m1_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm ret_1036 loc( ret_1036_loc ) :=
                  @Ok ristretto_point_t int8 (prod_b(
                      lift_to_both0 x_1050,
                      lift_to_both0 y_1051,
                      lift_to_both0 one_1040,
                      lift_to_both0 t_1052
                    )) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 ret_1036)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 ret_1036)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 ret_1036)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 ret_1036)
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 ret_1036)
        ) : both (CEfset ([ret_1036_loc])) [interface
      #val #[ D ] : d_inp → d_out ; #val #[ ABS ] : abs_inp → abs_out ;
      #val #[ FE ] : fe_inp → fe_out ;
      #val #[ GEQ_P ] : geq_p_inp → geq_p_out ;
      #val #[ IS_NEGATIVE ] : is_negative_inp → is_negative_out ;
      #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ;
      #val #[ SQRT_RATIO_M1 ] : sqrt_ratio_m1_inp → sqrt_ratio_m1_out ] (
        decode_result_t)))in
  both_package' _ _ (DECODE,(decode_inp,decode_out)) temp_package_both.
Fail Next Obligation.


Notation "'equals_inp'" :=(
  ristretto_point_t '× ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'equals_inp'" :=(
  ristretto_point_t '× ristretto_point_t : ChoiceEquality) (at level 2).
Notation "'equals_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'equals_out'" :=(bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition EQUALS : nat :=
  1060.
Program Definition equals
  : both_package (fset.fset0) [interface] [(EQUALS,(equals_inp,equals_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      u_1054 , v_1057) := temp_inp : ristretto_point_t '× ristretto_point_t in
    
    ((letb '(x1_1055, y1_1056, _, _) : (
            field_element_t '×
            field_element_t '×
            field_element_t '×
            field_element_t
          ) :=
          lift_to_both0 u_1054 in
        letb '(x2_1058, y2_1059, _, _) : (
            field_element_t '×
            field_element_t '×
            field_element_t '×
            field_element_t
          ) :=
          lift_to_both0 v_1057 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((((
                lift_to_both0 x1_1055) *% (lift_to_both0 y2_1059)) =.? ((
                lift_to_both0 x2_1058) *% (lift_to_both0 y1_1056))) || (((
                lift_to_both0 y1_1056) *% (lift_to_both0 y2_1059)) =.? ((
                lift_to_both0 x1_1055) *% (lift_to_both0 x2_1058))))
        ) : both (fset.fset0) [interface] (bool_ChoiceEquality)))in
  both_package' _ _ (EQUALS,(equals_inp,equals_out)) temp_package_both.
Fail Next Obligation.


Notation "'add_inp'" :=(
  ristretto_point_t '× ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'add_inp'" :=(
  ristretto_point_t '× ristretto_point_t : ChoiceEquality) (at level 2).
Notation "'add_out'" :=(
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'add_out'" :=(ristretto_point_t : ChoiceEquality) (at level 2).
Definition ADD : nat :=
  1083.
Program Definition add
  : both_package (fset.fset0) [interface #val #[ FE ] : fe_inp → fe_out ] [(
    ADD,(add_inp,add_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      u_1061 , v_1066) := temp_inp : ristretto_point_t '× ristretto_point_t in
    
    let fe := fun x_0 => package_both fe (x_0) in
    ((letb '(x1_1062, y1_1063, z1_1064, t1_1065) : (
            field_element_t '×
            field_element_t '×
            field_element_t '×
            field_element_t
          ) :=
          lift_to_both0 u_1061 in
        letb '(x2_1067, y2_1068, z2_1069, t2_1070) : (
            field_element_t '×
            field_element_t '×
            field_element_t '×
            field_element_t
          ) :=
          lift_to_both0 v_1066 in
        letb a_1071 : field_element_t :=
          ((lift_to_both0 y1_1063) -% (lift_to_both0 x1_1062)) *% ((
              lift_to_both0 y2_1068) +% (lift_to_both0 x2_1067)) in
        letb b_1072 : field_element_t :=
          ((lift_to_both0 y1_1063) +% (lift_to_both0 x1_1062)) *% ((
              lift_to_both0 y2_1068) -% (lift_to_both0 x2_1067)) in
        letb c_1073 : field_element_t :=
          ((fe (lift_to_both0 (usize 2))) *% (lift_to_both0 z1_1064)) *% (
            lift_to_both0 t2_1070) in
        letb d_1074 : field_element_t :=
          ((fe (lift_to_both0 (usize 2))) *% (lift_to_both0 t1_1065)) *% (
            lift_to_both0 z2_1069) in
        letb e_1075 : field_element_t :=
          (lift_to_both0 d_1074) +% (lift_to_both0 c_1073) in
        letb f_1076 : field_element_t :=
          (lift_to_both0 b_1072) -% (lift_to_both0 a_1071) in
        letb g_1077 : field_element_t :=
          (lift_to_both0 b_1072) +% (lift_to_both0 a_1071) in
        letb h_1078 : field_element_t :=
          (lift_to_both0 d_1074) -% (lift_to_both0 c_1073) in
        letb x3_1079 : field_element_t :=
          (lift_to_both0 e_1075) *% (lift_to_both0 f_1076) in
        letb y3_1080 : field_element_t :=
          (lift_to_both0 g_1077) *% (lift_to_both0 h_1078) in
        letb t3_1081 : field_element_t :=
          (lift_to_both0 e_1075) *% (lift_to_both0 h_1078) in
        letb z3_1082 : field_element_t :=
          (lift_to_both0 f_1076) *% (lift_to_both0 g_1077) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 x3_1079,
            lift_to_both0 y3_1080,
            lift_to_both0 z3_1082,
            lift_to_both0 t3_1081
          ))
        ) : both (fset.fset0) [interface #val #[ FE ] : fe_inp → fe_out ] (
        ristretto_point_t)))in
  both_package' _ _ (ADD,(add_inp,add_out)) temp_package_both.
Fail Next Obligation.


Notation "'neg_inp'" :=(
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'neg_inp'" :=(ristretto_point_t : ChoiceEquality) (at level 2).
Notation "'neg_out'" :=(
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'neg_out'" :=(ristretto_point_t : ChoiceEquality) (at level 2).
Definition NEG : nat :=
  1089.
Program Definition neg
  : both_package (fset.fset0) [interface
  #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ] [(NEG,(neg_inp,neg_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(u_1084) := temp_inp : ristretto_point_t in
    
    let neg_fe := fun x_0 => package_both neg_fe (x_0) in
    ((letb '(x1_1085, y1_1086, z1_1087, t1_1088) : (
            field_element_t '×
            field_element_t '×
            field_element_t '×
            field_element_t
          ) :=
          lift_to_both0 u_1084 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            neg_fe (lift_to_both0 x1_1085),
            lift_to_both0 y1_1086,
            neg_fe (lift_to_both0 z1_1087),
            lift_to_both0 t1_1088
          ))
        ) : both (fset.fset0) [interface
      #val #[ NEG_FE ] : neg_fe_inp → neg_fe_out ] (ristretto_point_t)))in
  both_package' _ _ (NEG,(neg_inp,neg_out)) temp_package_both.
Fail Next Obligation.


Notation "'sub_inp'" :=(
  ristretto_point_t '× ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'sub_inp'" :=(
  ristretto_point_t '× ristretto_point_t : ChoiceEquality) (at level 2).
Notation "'sub_out'" :=(
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'sub_out'" :=(ristretto_point_t : ChoiceEquality) (at level 2).
Definition SUB : nat :=
  1092.
Program Definition sub
  : both_package (fset.fset0) [interface #val #[ ADD ] : add_inp → add_out ;
  #val #[ NEG ] : neg_inp → neg_out ] [(SUB,(sub_inp,sub_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      u_1090 , v_1091) := temp_inp : ristretto_point_t '× ristretto_point_t in
    
    let add := fun x_0 x_1 => package_both add (x_0,x_1) in
    let neg := fun x_0 => package_both neg (x_0) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (add (
            lift_to_both0 u_1090) (neg (lift_to_both0 v_1091)))
        ) : both (fset.fset0) [interface #val #[ ADD ] : add_inp → add_out ;
      #val #[ NEG ] : neg_inp → neg_out ] (ristretto_point_t)))in
  both_package' _ _ (SUB,(sub_inp,sub_out)) temp_package_both.
Fail Next Obligation.


Notation "'double_inp'" :=(
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'double_inp'" :=(ristretto_point_t : ChoiceEquality) (at level 2).
Notation "'double_out'" :=(
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'double_out'" :=(ristretto_point_t : ChoiceEquality) (at level 2).
Definition DOUBLE : nat :=
  1108.
Program Definition double
  : both_package (fset.fset0) [interface #val #[ FE ] : fe_inp → fe_out ] [(
    DOUBLE,(double_inp,double_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(u_1093) := temp_inp : ristretto_point_t in
    
    let fe := fun x_0 => package_both fe (x_0) in
    ((letb '(x1_1094, y1_1095, z1_1096, _) : (
            field_element_t '×
            field_element_t '×
            field_element_t '×
            field_element_t
          ) :=
          lift_to_both0 u_1093 in
        letb a_1097 : field_element_t :=
          nat_mod_pow (lift_to_both0 x1_1094) (lift_to_both0 (@repr U128 2)) in
        letb b_1098 : field_element_t :=
          nat_mod_pow (lift_to_both0 y1_1095) (lift_to_both0 (@repr U128 2)) in
        letb c_1099 : field_element_t :=
          (fe (lift_to_both0 (usize 2))) *% (nat_mod_pow (
              lift_to_both0 z1_1096) (lift_to_both0 (@repr U128 2))) in
        letb h_1100 : field_element_t :=
          (lift_to_both0 a_1097) +% (lift_to_both0 b_1098) in
        letb e_1101 : field_element_t :=
          (lift_to_both0 h_1100) -% (nat_mod_pow ((lift_to_both0 x1_1094) +% (
                lift_to_both0 y1_1095)) (lift_to_both0 (@repr U128 2))) in
        letb g_1102 : field_element_t :=
          (lift_to_both0 a_1097) -% (lift_to_both0 b_1098) in
        letb f_1103 : field_element_t :=
          (lift_to_both0 c_1099) +% (lift_to_both0 g_1102) in
        letb x2_1104 : field_element_t :=
          (lift_to_both0 e_1101) *% (lift_to_both0 f_1103) in
        letb y2_1105 : field_element_t :=
          (lift_to_both0 g_1102) *% (lift_to_both0 h_1100) in
        letb t2_1106 : field_element_t :=
          (lift_to_both0 e_1101) *% (lift_to_both0 h_1100) in
        letb z2_1107 : field_element_t :=
          (lift_to_both0 f_1103) *% (lift_to_both0 g_1102) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 x2_1104,
            lift_to_both0 y2_1105,
            lift_to_both0 z2_1107,
            lift_to_both0 t2_1106
          ))
        ) : both (fset.fset0) [interface #val #[ FE ] : fe_inp → fe_out ] (
        ristretto_point_t)))in
  both_package' _ _ (DOUBLE,(double_inp,double_out)) temp_package_both.
Fail Next Obligation.

Definition res_1109_loc : ChoiceEqualityLocation :=
  ((field_element_t '× field_element_t '× field_element_t '× field_element_t
    ) ; 1111%nat).
Definition temp_1110_loc : ChoiceEqualityLocation :=
  ((field_element_t '× field_element_t '× field_element_t '× field_element_t
    ) ; 1112%nat).
Notation "'mul_inp'" :=(
  scalar_t '× ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'mul_inp'" :=(
  scalar_t '× ristretto_point_t : ChoiceEquality) (at level 2).
Notation "'mul_out'" :=(
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'mul_out'" :=(ristretto_point_t : ChoiceEquality) (at level 2).
Definition MUL : nat :=
  1116.
Program Definition mul
  : both_package (CEfset ([res_1109_loc ; temp_1110_loc])) [interface
  #val #[ IDENTITY_POINT ] : identity_point_inp → identity_point_out ;
  #val #[ ADD ] : add_inp → add_out ;
  #val #[ DOUBLE ] : double_inp → double_out ] [(MUL,(mul_inp,mul_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(k_1115 , p_1113) := temp_inp : scalar_t '× ristretto_point_t in
    
    let identity_point := package_both identity_point tt in
    let add := fun x_0 x_1 => package_both add (x_0,x_1) in
    let double := fun x_0 => package_both double (x_0) in
    ((letbm res_1109 : (
            field_element_t '×
            field_element_t '×
            field_element_t '×
            field_element_t
          ) loc( res_1109_loc ) :=
          identity_point  in
        letbm temp_1110 : (
            field_element_t '×
            field_element_t '×
            field_element_t '×
            field_element_t
          ) loc( temp_1110_loc ) :=
          lift_to_both0 p_1113 in
        letb '(res_1109, temp_1110) :=
          foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                usize 256)) prod_ce(res_1109, temp_1110) (L := (CEfset (
                [res_1109_loc ; temp_1110_loc]))) (I := ([interface
              #val #[ IDENTITY_POINT ] : identity_point_inp → identity_point_out ;
              #val #[ ADD ] : add_inp → add_out ;
              #val #[ DOUBLE ] : double_inp → double_out ])) (fun i_1114 '(
              res_1109,
              temp_1110
            ) =>
            letb 'res_1109 :=
              if (nat_mod_get_bit (lift_to_both0 k_1115) (
                  lift_to_both0 i_1114)) =.? (nat_mod_from_literal (
                  0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed) (
                  lift_to_both0 (@repr U128 1))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                [res_1109_loc ; temp_1110_loc])) (L2 := CEfset (
                [res_1109_loc ; temp_1110_loc])) (I1 := [interface
              #val #[ ADD ] : add_inp → add_out ]) (I2 := [interface
              #val #[ ADD ] : add_inp → add_out ;
              #val #[ DOUBLE ] : double_inp → double_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm res_1109 loc( res_1109_loc ) :=
                  add (lift_to_both0 res_1109) (lift_to_both0 temp_1110) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 res_1109)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 res_1109)
               in
            letbm temp_1110 loc( temp_1110_loc ) :=
              double (lift_to_both0 temp_1110) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 res_1109,
                lift_to_both0 temp_1110
              ))
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 res_1109)
        ) : both (CEfset ([res_1109_loc ; temp_1110_loc])) [interface
      #val #[ IDENTITY_POINT ] : identity_point_inp → identity_point_out ;
      #val #[ ADD ] : add_inp → add_out ;
      #val #[ DOUBLE ] : double_inp → double_out ] (ristretto_point_t)))in
  both_package' _ _ (MUL,(mul_inp,mul_out)) temp_package_both.
Fail Next Obligation.

