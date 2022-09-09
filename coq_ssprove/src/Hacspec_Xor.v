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
Definition r_1_loc : ChoiceEqualityLocation :=
  ((int64 ; 5%nat)).
Notation "'xor_inp'" := (
  int64 '× int64 : choice_type) (in custom pack_type at level 2).
Notation "'xor_out'" := (int64 : choice_type) (in custom pack_type at level 2).
Definition XOR : nat :=
  (6).
Program Definition xor
   : package (CEfset ([r_1_loc])) [interface] [interface
  #val #[ XOR ] : xor_inp → xor_out ] :=
  ([package #def #[ XOR ] (temp_inp : xor_inp) : xor_out { 
    let '(x_0 , y_2) := temp_inp : int64 '× int64 in
    ({ code  '(r_1 : int64) ←
          (ret (x_0)) ;;
        #put r_1_loc := r_1 ;;
       '(r_1 : int64) ←
          (( temp_4 ←
                ((r_1) .^ (y_2)) ;;
              ret (temp_4))) ;;
        #put r_1_loc := r_1 ;;
      
      @ret (int64) (r_1) } : code (CEfset ([r_1_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_xor : package _ _ _ :=
  (xor).
Fail Next Obligation.

