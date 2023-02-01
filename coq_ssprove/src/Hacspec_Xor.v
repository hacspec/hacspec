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


Definition x_0_loc : ChoiceEqualityLocation :=
  (int64 ; 3%nat).
Definition y_1_loc : ChoiceEqualityLocation :=
  (int64 ; 4%nat).
Definition r_2_loc : ChoiceEqualityLocation :=
  (int64 ; 5%nat).
Notation "'xor_inp'" :=(
  int64 '× int64 : choice_type) (in custom pack_type at level 2).
Notation "'xor_inp'" :=(int64 '× int64 : ChoiceEquality) (at level 2).
Notation "'xor_out'" :=(int64 : choice_type) (in custom pack_type at level 2).
Notation "'xor_out'" :=(int64 : ChoiceEquality) (at level 2).
Definition XOR : nat :=
  11.
Program Definition xor (x_inp_6 : int64) (y_inp_7 : int64)
  : both (CEfset ([x_0_loc ; y_1_loc ; r_2_loc])) [interface] (int64) :=
  ((letbm x_0 : int64 loc( x_0_loc ) := lift_to_both0 x_inp_6 in
      letbm y_1 : int64 loc( y_1_loc ) := lift_to_both0 y_inp_7 in
      letb v_8 : int64 := lift_to_both0 x_0 in
      letbm r_2 : int64 loc( r_2_loc ) := lift_to_both0 v_8 in
      letb v1_9 : int64 := lift_to_both0 r_2 in
      letb v2_10 : int64 := lift_to_both0 y_1 in
      letbm r_2 loc( r_2_loc ) :=
        (lift_to_both0 v1_9) .^ (lift_to_both0 v2_10) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 r_2)
      ) : both (CEfset ([x_0_loc ; y_1_loc ; r_2_loc])) [interface] (int64)).
Fail Next Obligation.

