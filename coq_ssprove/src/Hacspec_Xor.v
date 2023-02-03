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


Definition x_3412_loc : ChoiceEqualityLocation :=
  (int64 ; 3415%nat).
Definition y_3413_loc : ChoiceEqualityLocation :=
  (int64 ; 3416%nat).
Definition r_3414_loc : ChoiceEqualityLocation :=
  (int64 ; 3417%nat).
Notation "'xor_inp'" :=(
  int64 '× int64 : choice_type) (in custom pack_type at level 2).
Notation "'xor_inp'" :=(int64 '× int64 : ChoiceEquality) (at level 2).
Notation "'xor_out'" :=(int64 : choice_type) (in custom pack_type at level 2).
Notation "'xor_out'" :=(int64 : ChoiceEquality) (at level 2).
Definition XOR : nat :=
  3420.
Program Definition xor (x_inp_3418 : int64) (y_inp_3419 : int64)
  : both (CEfset ([x_3412_loc ; y_3413_loc ; r_3414_loc])) [interface] (
    int64) :=
  ((letbm x_3412 : int64 loc( x_3412_loc ) := lift_to_both0 x_inp_3418 in
      letbm y_3413 : int64 loc( y_3413_loc ) := lift_to_both0 y_inp_3419 in
      letbm r_3414 : int64 loc( r_3414_loc ) :=
        (lift_to_both0 x_3412) .^ (lift_to_both0 y_3413) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 r_3414)
      ) : both (CEfset ([x_3412_loc ; y_3413_loc ; r_3414_loc])) [interface] (
      int64)).
Fail Next Obligation.

