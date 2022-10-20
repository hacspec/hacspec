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


Definition x_3146_loc : ChoiceEqualityLocation :=
  (int64 ; 3149%nat).
Definition r_3148_loc : ChoiceEqualityLocation :=
  (int64 ; 3150%nat).
Definition y_3147_loc : ChoiceEqualityLocation :=
  (int64 ; 3151%nat).
Notation "'xor_inp'" :=(
  int64 '× int64 : choice_type) (in custom pack_type at level 2).
Notation "'xor_inp'" :=(int64 '× int64 : ChoiceEquality) (at level 2).
Notation "'xor_out'" :=(int64 : choice_type) (in custom pack_type at level 2).
Notation "'xor_out'" :=(int64 : ChoiceEquality) (at level 2).
Definition XOR : nat :=
  3157.
Program Definition xor
  : both_package (CEfset (
      [x_3146_loc ; y_3147_loc ; r_3148_loc])) [interface] [(XOR,(
      xor_inp,xor_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_inp_3152 , y_inp_3153) := temp_inp : int64 '× int64 in
    
    ((letbm x_3146 : int64 loc( x_3146_loc ) := lift_to_both0 x_inp_3152 in
        letbm y_3147 : int64 loc( y_3147_loc ) := lift_to_both0 y_inp_3153 in
        letb v_3154 : int64 := lift_to_both0 x_3146 in
        letbm r_3148 : int64 loc( r_3148_loc ) := lift_to_both0 v_3154 in
        letb v1_3155 : int64 := lift_to_both0 r_3148 in
        letb v2_3156 : int64 := lift_to_both0 y_3147 in
        letbm r_3148 loc( r_3148_loc ) :=
          (lift_to_both0 v1_3155) .^ (lift_to_both0 v2_3156) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 r_3148)
        ) : both (CEfset ([x_3146_loc ; y_3147_loc ; r_3148_loc])) [interface] (
        int64)))in
  both_package' _ _ (XOR,(xor_inp,xor_out)) temp_package_both.
Fail Next Obligation.

