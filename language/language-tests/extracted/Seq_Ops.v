(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition foo (x_0 : seq uint8) (y_1 : seq uint8) : seq uint8 :=
  (x_0) seq_add (y_1).

Definition bar (x_2 : seq uint8) (y_3 : seq uint8) : seq uint8 :=
  (x_2) seq_or (y_3).

