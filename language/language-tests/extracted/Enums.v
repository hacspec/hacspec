(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Inductive foo_t :=
| CaseX : foo_t
| CaseY : (uint8 × seq int32) -> foo_t.

Inductive bar_t :=
| Bar : int32 -> bar_t.

Definition baz (x_0 : foo_t) : bar_t :=
  let z_1 : bar_t :=
    Bar (@repr WORDSIZE32 0) in 
  let 'Bar (z_2) :=
    z_1 in 
  let y_3 : foo_t :=
    match x_0 with
    | CaseX => CaseY ((
        secret (@cast _ uint8 _ (z_2)) : int8,
        seq_new_ (default) (usize 1)
      ))
    | CaseY (a_4, b_5) => CaseY ((
        (a_4) .+ (secret (@repr WORDSIZE8 1) : int8),
        b_5
      ))
    end in 
  match y_3 with
  | CaseX => Bar (@repr WORDSIZE32 0)
  | CaseY (a_6, b_7) => Bar (uint32_declassify (uint32_from_uint8 (a_6)))
  end.

Definition baz_im (x_8 : foo_t) : unit :=
  let z_9 : bar_t :=
    Bar (@repr WORDSIZE32 0) in 
  let 'Bar (z_10) :=
    z_9 in 
  let a_11 : int8 :=
    @cast _ uint8 _ (z_10) in 
  tt.

