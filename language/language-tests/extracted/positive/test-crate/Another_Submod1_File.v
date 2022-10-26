(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Crate.

Inductive res_typ_t :=
| Ok : res_t -> res_typ_t.

Definition some_fun  : int8 :=
  error_value_v.

