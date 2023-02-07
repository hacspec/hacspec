(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
From QuickChick Require Import QuickChick.
Require Import QuickChickLib.
Require Import Hacspec_Lib.

Definition ensure_something (x_0 : int8) (y_1 : int8)  : bool :=
  (x_0) =.? (y_1).

Theorem ensures_ensure_something : forall result_2 (x_0 : int8) (y_1 : int8),
 @ensure_something x_0 y_1 = result_2 ->
 result_2 = true.
 Proof. Admitted.
(*QuickChick (
  forAll g_int8 (fun x_0 : int8 =>forAll g_int8 (fun y_1 : int8 =>ensure_something x_0 y_1))).*)


