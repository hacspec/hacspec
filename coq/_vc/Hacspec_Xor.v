(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition xor (x_inp_2781 : int64) (y_inp_2782 : int64)  : int64 :=
  let x_2783 : int64 :=
    x_inp_2781 in 
  let y_2784 : int64 :=
    y_inp_2782 in 
  let r_2785 : int64 :=
    (x_2783) .^ (y_2784) in 
  r_2785.

