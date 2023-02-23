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
  (x_2778 : int8)
  (y_2779 : int8)
  
  `{x_2778 = y_2779}
  : bool :=
  (x_2778) =.? (y_2779).

<<<<<<< ../coq/src/Pearlite_Example.v
Theorem ensures_ensure_something : forall result_2 (x_0 : int8) (y_1 : int8),
 forall {H_0 : x_0 = y_1},
 @ensure_something x_0 y_1 H_0 = result_2 ->
 ~ (result_2 = false).
 Proof. red ; intros. subst. cbn in *. now rewrite (eq_true y_1) in H0. Qed.
=======
Theorem ensures_ensure_something : forall result_2780 (x_2778 : int8) (
  y_2779 : int8),
 forall {H_0 : x_2778 = y_2779},
 @ensure_something x_2778 y_2779 H_0 = result_2780 ->
 ~ (result_2780 = false).
 Proof. Admitted.
>>>>>>> ../coq/src/_temp/Pearlite_Example.v

