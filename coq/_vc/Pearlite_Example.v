(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition ensure_something
  (x_2675 : int8)
  (y_2676 : int8)
  
  `{x_2675 = y_2676}
  : bool :=
  (x_2675) =.? (y_2676).

Theorem ensures_ensure_something : forall result_2677 (x_2675 : int8) (
  y_2676 : int8),
 forall {H_0 : x_2675 = y_2676},
 @ensure_something x_2675 y_2676 H_0 = result_2677 ->
 ~ (result_2677 = false).
 Proof. Admitted.

