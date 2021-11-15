(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Lib.

Definition arr_typ := nseq (int8) (usize 32).

Inductive enum_typ :=
| Empty : enum_typ
| OneArg : arr_typ -> enum_typ
| TwoArg : (arr_typ × int8) -> enum_typ
| ZeroArg : unit -> enum_typ.

Definition eqb_enum_typ (x y : enum_typ) : bool :=
match x with
   | Empty => match y with | Empty=> true | _ => false end
   | OneArg a => match y with | OneArg b => a =.? b | _ => false end
   | TwoArg a => match y with | TwoArg b => a =.? b | _ => false end
   | ZeroArg a => match y with | ZeroArg b => a =.? b | _ => false end
   end.

Definition eqb_leibniz_enum_typ (x y : enum_typ) : eqb_enum_typ x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_enum_typ : EqDec (enum_typ) :=
Build_EqDec (enum_typ) (eqb_enum_typ) (eqb_leibniz_enum_typ).


Inductive map :=
| Map : (public_byte_seq × public_byte_seq) -> map.

Definition eqb_map (x y : map) : bool :=
match x with
   | Map a => match y with | Map b => a =.? b end
   end.

Definition eqb_leibniz_map (x y : map) : eqb_map x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_map : EqDec (map) :=
Build_EqDec (map) (eqb_map) (eqb_leibniz_map).


Inductive tuple_struct_typ :=
| TupleStructTyp : (int64 × enum_typ × map) -> tuple_struct_typ.

Definition eqb_tuple_struct_typ (x y : tuple_struct_typ) : bool :=
match x with
   | TupleStructTyp a => match y with | TupleStructTyp b => a =.? b end
   end.

Definition eqb_leibniz_tuple_struct_typ (x y : tuple_struct_typ) : eqb_tuple_struct_typ x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_tuple_struct_typ : EqDec (tuple_struct_typ) :=
Build_EqDec (tuple_struct_typ) (eqb_tuple_struct_typ) (eqb_leibniz_tuple_struct_typ).


Definition instance  : tuple_struct_typ :=
  TupleStructTyp (
    (
      @repr WORDSIZE64 0,
      ZeroArg (tt),
      Map (
        (
          seq_new_ (@repr WORDSIZE8 0) (usize 0),
          seq_new_ (@repr WORDSIZE8 0) (usize 0)
        ))
    )).

Inductive map_entry :=
| Entry : (int64 × map) -> map_entry.

Definition eqb_map_entry (x y : map_entry) : bool :=
match x with
   | Entry a => match y with | Entry b => a =.? b end
   end.

Definition eqb_leibniz_map_entry (x y : map_entry) : eqb_map_entry x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_map_entry : EqDec (map_entry) :=
Build_EqDec (map_entry) (eqb_map_entry) (eqb_leibniz_map_entry).


Definition map_get_entry (m_0 : map) (entry_1 : arr_typ) : map_entry :=
  let 'Map ((m0_2, m1_3)) :=
    m_0 in 
  let res_4 :=
    Entry (
      (
        @repr WORDSIZE64 0,
        Map (
          (
            seq_concat ((m0_2)) (entry_1),
            seq_concat ((m1_3)) (u64_to_be_bytes (@repr WORDSIZE64 0))
          ))
      )) in 
  let res_4 :=
    foldi (usize 0) ((seq_len ((m0_2))) / (usize 32)) (fun x_5 res_4 =>
      let '(res_4) :=
        if (
          array_from_seq (32) (
            seq_slice ((m0_2)) ((x_5) * (usize 32)) (usize 32))) array_eq (
          entry_1):bool then (
          let res_4 :=
            Entry (
              (
                u64_from_be_bytes (
                  array_from_seq (8) (
                    seq_slice (m1_3) ((x_5) * (usize 8)) (usize 8))),
                Map (((m0_2), (m1_3)))
              )) in 
          (res_4)
        ) else ( (res_4)
        ) in 
      (res_4))
    res_4 in 
  res_4.

Inductive map_update :=
| Update : (int64 × map) -> map_update.

Definition map_update_entry
  (m_6 : map)
  (entry_7 : arr_typ)
  (amount_8 : int64)
  : map_update :=
  let 'Map ((m0_9, m1_10)) :=
    m_6 in 
  let res_11 :=
    Update (
      (
        amount_8,
        Map (
          (
            seq_concat (m0_9) (entry_7),
            seq_concat (m1_10) (u64_to_be_bytes (amount_8))
          ))
      )) in 
  let res_11 :=
    foldi (usize 0) ((seq_len ((m0_9))) / (usize 32)) (fun x_12 res_11 =>
      let '(res_11) :=
        if (
          array_from_seq (32) (
            seq_slice ((m0_9)) ((x_12) * (usize 32)) (usize 32))) array_eq (
          entry_7):bool then (
          let res_11 :=
            Update (
              (
                amount_8,
                Map (
                  (
                    seq_update ((m0_9)) ((x_12) * (usize 32)) (entry_7),
                    seq_update ((m1_10)) ((x_12) * (usize 8)) (
                      u64_to_be_bytes (amount_8))
                  ))
              )) in 
          (res_11)
        ) else ( (res_11)
        ) in 
      (res_11))
    res_11 in 
  res_11.

Definition check_if_max
  (instance_13 : tuple_struct_typ)
  (increase_14 : int64)
  (entry_15 : arr_typ)
  : tuple_struct_typ :=
  let 'TupleStructTyp ((max_16, enum_typ_17, map_18)) :=
    instance_13 in 
  let '(curr_val_19, map_20) :=
    match map_get_entry (map_18) (entry_15) with
    | Entry (curr_val_21, map_22) => (curr_val_21, map_22) end in 
  let '(res_val_23, map_24) :=
    match map_update_entry (map_20) (entry_15) (
      (increase_14) .+ (curr_val_19)) with
    | Update (res_val_25, map_26) => (res_val_25, map_26) end in 
  let enum_typ_27 :=
    match (enum_typ_17) with
    | Empty => ZeroArg (tt)
    | ZeroArg tt => OneArg (entry_15)
    | OneArg add_28 => TwoArg ((add_28, @repr WORDSIZE8 0))
    | TwoArg (add_29, i_30) => TwoArg (
      (add_29, (i_30) .+ (@repr WORDSIZE8 1))) end in 
  let 'tt :=
    if ((enum_typ_27)) =.? (
      TwoArg ((entry_15, @repr WORDSIZE8 100))):bool then ( tt
    ) else ( tt
    ) in 
  let 'tt :=
    if (
      TupleStructTyp (
        ((increase_14) .+ (res_val_23), (enum_typ_27), (map_24)))) =.? (
      TupleStructTyp ((max_16, (enum_typ_27), (map_24)))):bool then ( tt
    ) else ( tt
    ) in 
  (
    if ((max_16) <.? ((increase_14) .+ (res_val_23))):bool then (
      TupleStructTyp (
        ((increase_14) .+ (res_val_23), enum_typ_27, map_24))) else (
      TupleStructTyp ((max_16, enum_typ_27, map_24)))).

Notation "'res_type'" := ((result uint_size unit)) : hacspec_scope.

Definition loop_with_early_return (amount_31 : uint_size) : res_type :=
  let res_32 :=
    Ok (usize 0) in 
  match (
    foldibnd (usize 0) to (usize 100) for res_32>> (fun x_33 res_32 => ifbnd (
      (x_33) + (amount_31)) >.? (usize 200) : bool
    thenbnd (
      match Err (tt)  : result  _ with  | Err a => Err a  | Ok _ => Ok (tt) end)
    else (tt) >> (fun 'tt =>
    let '(res_32) :=
      if (x_33) <.? (usize 50):bool then (
        let res_32 :=
          Ok (x_33) in 
        (res_32)
      ) else ( (res_32)
      ) in 
    Ok ((res_32))))) with
  | Err e => Err e
  | Ok res_32 =>  res_32 end.

