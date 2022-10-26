(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Definition error_value_v : int8 :=
  @repr WORDSIZE8 0.

Notation "'res_t'" := ((uint_size × uint_size)) : hacspec_scope.

