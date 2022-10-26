(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition foo (x_0 : (option (option uint32))) : uint32 :=
  let y_1 : (option uint32) :=
    @None uint32 in 
  let z_2 : (option (option uint32)) :=
    @Some (option uint32) (y_1) in 
  match x_0 with
  | None => secret (@repr WORDSIZE32 0) : int32
  | Some x_3 => option_unwrap (x_3)
  end.

