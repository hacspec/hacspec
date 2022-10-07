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

Definition x_2_loc : ChoiceEqualityLocation :=
  ((int64 ; 10%nat)).
Definition y_5_loc : ChoiceEqualityLocation :=
  ((int64 ; 11%nat)).
Definition r_4_loc : ChoiceEqualityLocation :=
  ((int64 ; 12%nat)).
Notation "'xor_inp'" := (
  int64 '× int64 : choice_type) (in custom pack_type at level 2).
Notation "'xor_out'" := (int64 : choice_type) (in custom pack_type at level 2).
Definition XOR : nat :=
  (13).
Program Definition xor
   : package (CEfset ([x_2_loc ; y_5_loc ; r_4_loc])) [interface] [interface
  #val #[ XOR ] : xor_inp → xor_out ] :=
  ([package #def #[ XOR ] (temp_inp : xor_inp) : xor_out { 
    let '(x_inp_0 , y_inp_1) := temp_inp : int64 '× int64 in
    ({ code  '(x_2 : int64) ←
          (ret (x_inp_0)) ;;
        #put x_2_loc := x_2 ;;
       '(y_5 : int64) ←
          (ret (y_inp_1)) ;;
        #put y_5_loc := y_5 ;;
       '(v_3 : int64) ←
        (ret (x_2)) ;;
       '(r_4 : int64) ←
          (ret (v_3)) ;;
        #put r_4_loc := r_4 ;;
       '(v1_6 : int64) ←
        (ret (r_4)) ;;
       '(v2_7 : int64) ←
        (ret (y_5)) ;;
       '(r_4 : int64) ←
          (( temp_9 ←
                ((v1_6) .^ (v2_7)) ;;
              ret (temp_9))) ;;
        #put r_4_loc := r_4 ;;
      
      @ret (int64) (r_4) } : code (CEfset (
          [x_2_loc ; y_5_loc ; r_4_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_xor : package _ _ _ :=
  (xor).
Fail Next Obligation.

