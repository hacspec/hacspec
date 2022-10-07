(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From CoqWord Require Import ssrZ word.
From Jasmin Require Import word.
Require Import ChoiceEquality.

From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope bool_scope.

Require Import Hacspec_Lib_Comparable.
Require Import Hacspec_Lib_Pre.

Open Scope hacspec_scope.



Definition xor (x_inp_0 : int64) (y_inp_1 : int64) : int64 :=
  let x_2 : int64 :=
    x_inp_0 in 
  let y_3 : int64 :=
    y_inp_1 in 
  let v_4 : int64 :=
    x_2 in 
  let r_5 : int64 :=
    v_4 in 
  let v1_6 : int64 :=
    r_5 in 
  let v2_7 : int64 :=
    y_3 in 
  let r_5 :=
    ((v1_6) .^ (v2_7)) in 
  r_5.
Definition xor_code
  (x_inp_0 : int64)
  (y_inp_1 : int64)
  : code fset.fset0 [interface] (@ct (int64)) :=
  lift_to_code (xor x_inp_0 y_inp_1).

