(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition foo (x_0 : (option int32)) : bool :=
  match x_0 with | None => false | Some _ => true end.

Definition final_if (a_1 : seq int8) : seq int8 :=
  (if (true):bool then (a_1) else (a_1)).

