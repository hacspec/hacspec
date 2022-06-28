Global Set Warnings "-ambiguous-paths".
Global Set Warnings "-uniform-inheritance".
Global Set Warnings "-auto-template".
Global Set Warnings "-disj-pattern-notation".
Global Set Warnings "-notation-overridden,-ambiguous-paths".

Require Import Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Sumbool.

From mathcomp Require Import (* choice  *)fintype.

From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset fmap.

Require Import ChoiceEquality.

From CoqWord Require Import ssrZ word.
From Jasmin Require Import word.

From Coq Require Import ZArith List.
Import ListNotations.

(*** Integers *)
Declare Scope hacspec_scope.

Open Scope list_scope.
Open Scope hacspec_scope.
Open Scope nat_scope.
(* Open Scope Z_scope. *)

Require Import Hacspec_Lib_Comparable.

Section IntType.

  Definition int_choice {WS : wsize} := chWord WS.
  Definition int_type {WS : wsize} : Type := WS.-word.
  #[global] Program Instance int {WS : wsize} : ChoiceEquality :=
    {| ct := @int_choice WS ; T := @int_type WS |}.

  Definition unsigned {WS : wsize} (i : @int WS) : Z := wunsigned i.
  Definition signed {WS : wsize} (i: @int WS) : Z := wsigned i.
  Definition repr {WS : wsize} (z : Z) : @int WS := wrepr WS z.

  Definition rol {WS} (u s : @int WS) := wrol u (unsigned s).
  Definition ror {WS} (u s : @int WS) := wror u (unsigned s).

  #[global] Instance int8 : ChoiceEquality := @int U8.
  #[global] Instance int16 : ChoiceEquality := @int U16.
  #[global] Instance int32 : ChoiceEquality := @int U32.
  #[global] Instance int64 : ChoiceEquality := @int U64.
  #[global] Instance int128 : ChoiceEquality := @int U128.

  Definition int_modi {WS : wsize} : @int WS -> @int WS -> @int WS := wmodi.
  Definition int_add {WS : wsize} : @int WS -> @int WS -> @int WS := @add_word WS.
  Definition int_sub {WS : wsize} : @int WS -> @int WS -> @int WS := @sub_word WS.
  Definition int_opp {WS : wsize} : @int WS -> @int WS := @opp_word WS.
  Definition int_mul {WS : wsize} : @int WS -> @int WS -> @int WS := @mul_word WS.
  Definition int_div {WS : wsize} : @int WS -> @int WS -> @int WS := wdiv.
  Definition int_mod {WS : wsize} : @int WS -> @int WS -> @int WS := wmod.
  Definition int_xor {WS : wsize} : @int WS -> @int WS -> @int WS := wxor.
  Definition int_and {WS : wsize} : @int WS -> @int WS -> @int WS := wand.
  Definition int_or {WS : wsize} : @int WS -> @int WS -> @int WS := wor.

  Definition int_not {WS : wsize} : @int WS -> @int WS := wnot.
  
  Definition zero {WS : wsize} : T (@int WS) := @word0 WS.
  Definition one {WS : wsize} : T (@int WS) := @word1 (pred WS).

  Lemma add_zero_l : forall {WS : wsize} n, @int_add WS zero n = n.
  Proof.
    intros.
    apply add0w.
  Defined.

  (* Lemma add_one_l : forall {WS : wsize} n m H1 H2, *)
  (*     n = m -> *)
  (*     mkword n H1 = mkword m H2. *)

  Lemma add_one_l : forall {WS : wsize} n, @int_add WS one (repr n) = repr (Z.succ n).
  Proof.
    intros.

    unfold int_add.
    unfold add_word.

    replace (urepr one) with 1%Z by reflexivity.

    unfold nat_of_wsize.
    fold (wrepr WS (Z.add 1 (@urepr (S (wsize_size_minus_1 WS)) (@repr WS n)))).
    unfold repr.

    rewrite wrepr_add.
    rewrite urepr_word.

    (* Set Printing All. *)
    replace toword with urepr by reflexivity.
    unfold wrepr at 2.
    rewrite ureprK.

    rewrite <- wrepr_add.
    rewrite Z.add_1_l.
    reflexivity.
  Defined.

  Lemma repr0_is_zero : forall {WS : wsize}, @repr WS 0 = zero.
  Proof.
    intros.
    now rewrite wrepr0.
  Qed.

  Lemma add_repr : forall {WS : wsize} (n m : Z), @int_add WS (repr n) (repr m) = (repr (n + m)).
  Proof.
    intros.
    unfold int_add.
    unfold add_word.
    unfold nat_of_wsize.
    fold (wrepr WS (Z.add (@urepr (S (wsize_size_minus_1 WS)) (@repr WS n))
                          (@urepr (S (wsize_size_minus_1 WS)) (@repr WS m)))).

    rewrite wrepr_add.
    replace toword with urepr by reflexivity.
    unfold wrepr at 1 2.
    rewrite ureprK.
    rewrite ureprK.
    rewrite <- wrepr_add.
    reflexivity.
  Qed.


End IntType.

Axiom secret : forall {WS : wsize},  (T (@int WS)) -> (T (@int WS)).

Infix "%%" := int_modi (at level 40, left associativity) : Z_scope.
Infix ".+" := int_add (at level 77) : hacspec_scope.
Infix ".-" := int_sub (at level 77) : hacspec_scope.
Notation "-" := int_opp (at level 77) : hacspec_scope.
Infix ".*" := int_mul (at level 77) : hacspec_scope.
Infix "./" := int_div (at level 77) : hacspec_scope.
Infix ".%" := int_mod (at level 77) : hacspec_scope.
Infix ".^" := int_xor (at level 77) : hacspec_scope.
Infix ".&" := int_and (at level 77) : hacspec_scope.
Infix ".|" := int_or (at level 77) : hacspec_scope.

Notation "'not'" := int_not (at level 77) : hacspec_scope.

(* Infix "==" := (MachineIntegers.eq) (at level 32) : hacspec_scope. *)
(* w1 == w2 -- already defined *)



(* Comparisons, boolean equality, and notation *)

Global Program Instance nat_eqdec : EqDec nat := {
    eqb := Nat.eqb;
    eqb_leibniz := Nat.eqb_eq ;
  }.

Global Instance nat_comparable : Comparable nat := {
    ltb := Nat.ltb;
    leb := Nat.leb;
    gtb a b := Nat.ltb b a;
    geb a b := Nat.leb b a;
  }.

Global Instance N_eqdec : EqDec N := {
    eqb := N.eqb;
    eqb_leibniz := N.eqb_eq ;
  }.

Global Instance N_comparable : Comparable N := {
    ltb := N.ltb;
    leb := N.leb;
    gtb a b := N.ltb b a;
    geb a b := N.leb b a;
  }.

Global Instance Z_eqdec : EqDec Z := {
    eqb := Z.eqb;
    eqb_leibniz := Z.eqb_eq ;
  }.

Global Instance Z_comparable : Comparable Z := {
    ltb := Z.ltb;
    leb := Z.leb;
    gtb a b := Z.ltb b a;
    geb a b := Z.leb b a;
  }.

Lemma int_eqb_eq : forall {WS : wsize} (a b : @int WS), eqtype.eq_op a b = true <-> a = b.
Proof.
  symmetry ; exact (ssrbool.rwP (@eqtype.eqP _ a b)).
Qed.

Global Instance int_eqdec `{WS : wsize}: EqDec (@int WS) := {
    eqb := eqtype.eq_op;
    eqb_leibniz := int_eqb_eq ;
  }.

Global Instance int_comparable `{WS : wsize} : Comparable (@int WS) :=
  eq_dec_lt_Comparable (wlt Unsigned).

Axiom uint8_declassify : int8 -> int8.
Axiom int8_declassify : int8 -> int8.
Axiom uint16_declassify : int16 -> int16.
Axiom int16_declassify : int16 -> int16.
Axiom uint32_declassify : int32 -> int32.
Axiom int32_declassify : int32 -> int32.
Axiom uint64_declassify : int64 -> int64.
Axiom int64_declassify : int64 -> int64.
Axiom uint128_declassify : int128 -> int128.
Axiom int128_declassify : int128 -> int128.

Axiom uint8_classify : int8 -> int8.
Axiom int8_classify : int8 -> int8.
Axiom uint16_classify : int16 -> int16.
Axiom int16_classify : int16 -> int16.
Axiom uint32_classify : int32 -> int32.
Axiom int32_classify : int32 -> int32.
Axiom uint64_classify : int64 -> int64.
Axiom int64_classify : int64 -> int64.
Axiom uint128_classify : int128 -> int128.
Axiom int128_classify : int128 -> int128.


(* CompCert integers' signedness is only interpreted through 'signed' and 'unsigned',
   and not in the representation. Therefore, uints are just names for their respective ints.
 *)

Definition int8_type := @int_type U8.
Definition int16_type := @int_type U16.
Definition int32_type := @int_type U32.
Definition int64_type := @int_type U64.
Definition int128_type := @int_type U128.

Notation uint8 := int8.
Definition uint8_type := @int_type U8.
#[global] Instance uint16 : ChoiceEquality := int16.
Definition uint16_type := @int_type U16.
#[global] Instance uint32 : ChoiceEquality := int32.
Definition uint32_type := @int_type U32.
#[global] Instance uint64 : ChoiceEquality := int64.
Definition uint64_type := @int_type U64.
#[global] Instance uint128 : ChoiceEquality := int128.
Definition uint128_type := @int_type U128.

#[global] Instance uint_size : ChoiceEquality := int32.
Definition uint_size_type := @int_type U32.

#[global] Instance int_size : ChoiceEquality := int32.
Definition int_size_type := @int_type U32.

Axiom declassify_usize_from_uint8 : uint8 -> uint_size.

(* Represents any type that can be converted to uint_size and back *)
Class UInt_sizeable (A : Type) := {
    usize : A -> uint_size;
    from_uint_size : uint_size -> A;
  }.
Arguments usize {_} {_}.
Arguments from_uint_size {_} {_}.

Identity Coercion uint_size_to_int:uint_size_type >-> int_type.

Global Instance nat_uint_sizeable : UInt_sizeable nat := {
    usize n := repr (Z.of_nat n);
    from_uint_size n := Z.to_nat (unsigned n);
  }.

Global Instance N_uint_sizeable : UInt_sizeable N := {
    usize n := repr (Z.of_N n);
    from_uint_size n := Z.to_N (unsigned n);
  }.

Global Instance Z_uint_sizeable : UInt_sizeable Z := {
    usize n := repr n;
    from_uint_size n := unsigned n;
  }.


(* Same, but for int_size *)
Class Int_sizeable (A : Type) := {
    isize : A -> int_size;
    from_int_size : int_size -> A;
  }.

Arguments isize {_} {_}.
Arguments from_int_size {_} {_}.

Global Instance nat_Int_sizeable : Int_sizeable nat := {
    isize n := repr (Z.of_nat n);
    from_int_size n := Z.to_nat (signed n);
  }.

Global Instance N_Int_sizeable : Int_sizeable N := {
    isize n := repr (Z.of_N n);
    from_int_size n := Z.to_N (signed n);
  }.

Global Instance Z_Int_sizeable : Int_sizeable Z := {
    isize n := repr n;
    from_int_size n := signed n;
  }.

(**** Public integers *)

Definition pub_u8 (n : uint_size) : int8 := repr (unsigned n).
Definition pub_i8 (n : uint_size) : int8 := repr (unsigned n).
Definition pub_u16 (n : uint_size) : int16 := repr (unsigned n).
Definition pub_i16 (n : uint_size) : int16 := repr (unsigned n).
Definition pub_u32 (n : uint_size) : int32 := repr (unsigned n).
Definition pub_i32 (n : uint_size) : int32 := repr (unsigned n).
Definition pub_u64 (n : uint_size) : int64 := repr (unsigned n).
Definition pub_i64 (n : uint_size) : int64 := repr (unsigned n).
Definition pub_u128 (n : uint_size) : int128 := repr (unsigned n).
Definition pub_i128 (n : uint_size) : int128 := repr (unsigned n).

(**** Operations *)

(* Should maybe use size of s instead? *)
Definition uint8_rotate_left (u: int8) (s: int8) : int8 := rol u s.

Definition uint8_rotate_right (u: int8) (s: int8) : int8 := ror u s.

Definition uint16_rotate_left (u: int16) (s: int16) : int16 :=
  rol u s.

Definition uint16_rotate_right (u: int16) (s: int16) : int16 :=
  ror u s.

Definition uint32_rotate_left (u: int32) (s: int32) : int32 :=
  rol u s.

Definition uint32_rotate_right (u: int32) (s: int32) : int32 :=
  ror u s.

Definition uint64_rotate_left (u: int64) (s: int64) : int64 :=
  rol u s.

Definition uint64_rotate_right (u: int64) (s: int64) : int64 :=
  ror u s.

Definition uint128_rotate_left (u: int128) (s: int128) : int128 :=
  rol u s.

Definition uint128_rotate_right (u: int128) (s: int128) : int128 :=
  ror u s.

(* should use size u instead of u? *)
Definition usize_shift_right (u: uint_size) (s: int32) : uint_size :=
  (ror u s).
Infix "usize_shift_right" := (usize_shift_right) (at level 77) : hacspec_scope.

(* should use size u instead of u? *)
Definition usize_shift_left (u: uint_size) (s: int32) : uint_size :=
  (rol u s).
Infix "usize_shift_left" := (usize_shift_left) (at level 77) : hacspec_scope.

Definition pub_uint128_wrapping_add (x y: int128) : int128 :=
  x .+ y.

Definition shift_left_ `{WS : wsize} (i : @int WS) (j : uint_size) : @int WS :=
  wshl i (@repr WS (from_uint_size j)).

Definition shift_right_ `{WS : wsize} (i : @int WS) (j : uint_size) : @int WS:=
  wshr i (@repr WS (from_uint_size j)) .

Infix "shift_left" := (shift_left_) (at level 77) : hacspec_scope.
Infix "shift_right" := (shift_right_) (at level 77) : hacspec_scope.

(*** Positive util *)

Section Util.

  Fixpoint binary_representation_pre (n : nat) {struct n}: positive :=
    match n with
    | O => 1
    | S O => 1
    | S n => Pos.succ (binary_representation_pre n)
    end%positive.
  Definition binary_representation (n : nat) `(n <> O) := binary_representation_pre n.

  Theorem positive_is_succs : forall n, forall (H : n <> O) (K : S n <> O),
      @binary_representation (S n) K = Pos.succ (@binary_representation n H).
  Proof. induction n ; [contradiction | reflexivity]. Qed.

  (* Conversion of positive to binary representation *)
  Theorem positive_to_positive_succs : forall p, binary_representation (Pos.to_nat p) (Nat.neq_sym _ _ (Nat.lt_neq _ _ (Pos2Nat.is_pos p))) = p.
  Proof.
    intros p.
    generalize dependent (Nat.neq_sym 0 (Pos.to_nat p) (Nat.lt_neq 0 (Pos.to_nat p) (Pos2Nat.is_pos p))).

    destruct Pos.to_nat eqn:ptno.
    - contradiction.
    - generalize dependent p.
      induction n ; intros.
      + cbn.
        apply Pos2Nat.inj.
        symmetry.
        apply ptno.
      + rewrite positive_is_succs with (H := Nat.neq_succ_0 n).
        rewrite IHn with (p := Pos.of_nat (S n)).
        * rewrite <- Nat2Pos.inj_succ by apply Nat.neq_succ_0.
          rewrite <- ptno.
          apply Pos2Nat.id.
        * apply Nat2Pos.id.
          apply Nat.neq_succ_0.
  Qed.

  (*** Uint size util *)

  (* If a natural number is in bound then a smaller natural number is still in bound *)
  Lemma range_of_nat_succ :
    forall {WS : wsize},
    forall i, (Z.pred 0 < Z.of_nat (S i) < modulus WS)%Z -> (Z.pred 0 < Z.of_nat i < modulus WS)%Z.
  Proof. lia. Qed.

  (* Conversion to equivalent bound *)
  Lemma modulus_range_helper :
    forall {WS : wsize},
    forall i, (Z.pred 0 < i < modulus WS)%Z -> (0 <= i <= wmax_unsigned WS)%Z.
  Proof.
    intros.
    unfold wmax_unsigned.
    unfold wbase.
    unfold nat_of_wsize in H.
    lia.
  Qed.

  Definition unsigned_repr_alt {WS : wsize} (a : Z) `((Z.pred 0 < a < modulus WS)%Z) :
    unsigned (@repr WS a) = a.
  Proof.
    apply wunsigned_repr_small.
    intros.
    unfold wbase.
    unfold nat_of_wsize in H.
    lia.
  Qed.

  Theorem zero_always_modulus {WS : wsize} : (Z.pred 0 < 0 < modulus WS)%Z.
  Proof. easy. Qed.

  (* any uint_size can be represented as a natural number and a bound *)
  (* this is easier for proofs, however less efficient for computation *)
  (* as Z uses a binary representation *)

  Theorem uint_size_as_nat :
    forall (us: uint_size),
      { n : nat |
        us = repr (Z.of_nat n) /\ (Z.pred 0 < Z.of_nat n < @modulus U32)%Z}.
  Proof.
    intros.
    exists (Z.to_nat (unsigned us)).
    rewrite Z2Nat.id by apply (ssrbool.elimT lezP (urepr_ge0 us)).
    split.
    - unfold repr.
      unfold unsigned.
      rewrite wrepr_unsigned.
      reflexivity.
    - pose (wunsigned_range us).
      unfold wbase in a.
      unfold nat_of_wsize.
      cbn in *.
      lia.
  Qed.

  (* destruct uint_size as you would a natural number *)
  Definition destruct_uint_size_as_nat  (a : uint_size) : forall (P : uint_size -> Prop),
    forall (zero_case : P (repr 0)),
    forall (succ_case : forall (n : nat), (Z.pred 0 < Z.of_nat n < @modulus U32)%Z -> P (repr (Z.of_nat n))),
      P a.
  Proof.
    intros.
    destruct (uint_size_as_nat a) as [ n y ] ; destruct y as [ya yb] ; subst.
    destruct n.
    - apply zero_case.
    - apply succ_case.
      apply yb.
  Qed.


  (* induction for uint_size as you would do for a natural number *)
  Definition induction_uint_size_as_nat :
    forall (P : uint_size -> Prop),
      (P (repr 0)) ->
      (forall n,
          (Z.pred 0 < Z.succ (Z.of_nat n) < @modulus U32)%Z ->
          P (repr (Z.of_nat n)) ->
          P (repr (Z.succ (Z.of_nat n)))) ->
      forall (a : uint_size), P a.
  Proof.
    intros P H_zero H_ind a.
    destruct (uint_size_as_nat a) as [ n y ] ; destruct y as [ya yb] ; subst.
    induction n.
    - apply H_zero.
    - rewrite Nat2Z.inj_succ.
      apply H_ind.
      + rewrite <- Nat2Z.inj_succ.
        apply yb.
      + apply IHn.
        lia.
  Qed.

  (* conversion of usize to positive or zero and the respective bound *)
  Theorem uint_size_as_positive :
    forall (us: uint_size),
      { pu : unit + positive |
        match pu with
        | inl u => us = repr Z0
        | inr p => us = repr (Z.pos p) /\ (Z.pred 0 < Z.pos p < @modulus U32)%Z
        end
      }.
  Proof.
    intros.

    destruct us as [val H_].
    pose proof (H := H_).
    apply Bool.andb_true_iff in H as [lt gt].
    apply (ssrbool.elimT lezP) in lt.
    apply (ssrbool.elimT ltzP) in gt.

    destruct val.
    - exists (inl tt). apply word_ext. reflexivity.
    - exists (inr p).
      split.
      + apply word_ext.
        rewrite Zmod_small by (unfold nat_of_wsize in gt ; lia).
        reflexivity.
      + lia.
    - contradiction.
  Defined.

  (* destruction of uint_size as positive *)
  Definition destruct_uint_size_as_positive  (a : uint_size) : forall (P : uint_size -> Prop),
      (P (repr 0)) ->
      (forall b, (Z.pred 0 < Z.pos b < @modulus U32)%Z -> P (repr (Z.pos b))) ->
      P a.
  Proof.
    intros P H_zero H_succ.
    destruct (uint_size_as_positive a) as [ [ _ | b ] y ] ; [ subst | destruct y as [ya yb] ; subst ].
    - apply H_zero.
    - apply H_succ.
      apply yb.
  Qed.

  (* induction of uint_size as positive *)
  Definition induction_uint_size_as_positive :
    forall (P : uint_size -> Prop),
      (P (repr 0)) ->
      (P (repr 1)) ->
      (forall b,
          (Z.pred 0 < Z.succ (Z.pos b) < @modulus U32)%Z ->
          P (repr (Z.pos b)) ->
          P (repr (Z.succ (Z.pos b)))) ->
      forall (a : uint_size), P a.
  Proof.
    intros P H_zero H_one H_ind a.

    destruct (uint_size_as_positive a) as [ [ _ | b ] y ] ; [ subst | destruct y as [ya yb] ; subst ].
    - apply H_zero.
    - pose proof (pos_succ_b := positive_to_positive_succs b)
      ; symmetry in pos_succ_b
      ; rewrite pos_succ_b in *
      ; clear pos_succ_b.

      generalize dependent (Nat.neq_sym 0 (Pos.to_nat b) (Nat.lt_neq 0 (Pos.to_nat b) (Pos2Nat.is_pos b))).

      induction (Pos.to_nat b).
      + contradiction.
      + intros n_neq yb.
        destruct n.
        * apply H_one.
        * rewrite (positive_is_succs _  (Nat.neq_succ_0 n) n_neq) in *.
          rewrite Pos2Z.inj_succ in *.
          apply H_ind.
          -- apply yb.
          -- apply IHn.
             lia.
  Qed.

End Util.

Global Ltac destruct_uint_size_as_nat_named a H_zero H_succ :=
  generalize dependent a ;
  intros a ;
  apply (destruct_uint_size_as_nat a) ; [ pose proof (H_zero := @unsigned_repr_alt U32 0 zero_always_modulus) | let n := fresh in let H := fresh in intros n H ; pose proof (H_succ := @unsigned_repr_alt U32 _ H)] ; intros.

Global Ltac destruct_uint_size_as_nat a :=
  let H_zero := fresh in
  let H_succ := fresh in
  destruct_uint_size_as_nat_named a H_zero H_succ.

Global Ltac induction_uint_size_as_nat var :=
  generalize dependent var ;
  intros var ;
  apply induction_uint_size_as_nat with (a := var) ; [ pose proof (@unsigned_repr_alt U32 0 zero_always_modulus) | let n := fresh in let IH := fresh in intros n IH ; pose proof (@unsigned_repr_alt U32 _ IH)] ; intros.



(*** Loops *)

Open Scope nat_scope.
Fixpoint foldi_
         {acc : Type}
         (fuel : nat)
         (i : uint_size)
         (f : uint_size -> acc -> acc)
         (cur : acc) : acc :=
  match fuel with
  | 0 => cur
  | S n' => foldi_ n' (i .+ one) f (f i cur)
  end.
Close Scope nat_scope.
Definition foldi
           {acc: Type}
           (lo: uint_size)
           (hi: uint_size) (* {lo <= hi} *)
           (init: acc)
           (f: (uint_size) -> acc -> acc) (* {i < hi} *)
  : acc :=
  match Z.sub (unsigned hi) (unsigned lo) with
  | Z0 => init
  | Zneg p => init
  | Zpos p => foldi_ (Pos.to_nat p) lo f init
  end.

(* Fold done using natural numbers for bounds *)
Fixpoint foldi_nat_
         {acc : Type}
         (fuel : nat)
         (i : nat)
         (f : nat -> acc -> acc)
         (cur : acc) : acc :=
  match fuel with
  | O => cur
  | S n' => foldi_nat_ n' (S i) f (f i cur)
  end.


Fixpoint for_loop_
         {acc : Type}
         (fuel : nat)
         (f : nat -> acc -> acc)
         (cur : acc) : acc :=
  match fuel with
  | O => cur
  | S n' => f n' (for_loop_ n' f cur)
  end.

Definition foldi_nat
           {acc: Type}
           (lo: nat)
           (hi: nat) (* {lo <= hi} *)
           (f: nat -> acc -> acc) (* {i < hi} *)
           (init: acc) : acc :=
  match Nat.sub hi lo with
  | O => init
  | S n' => foldi_nat_ (S n') lo f init
  end.

Definition for_loop_range
           {acc: Type}
           (lo: nat)
           (hi: nat) (* {lo <= hi} *)
           (f: nat -> acc -> acc) (* {i < hi} *)
           (init: acc) : acc :=
  match Nat.sub hi lo with
  | O => init
  | S n' => for_loop_ (S n') (fun x => f (x + lo)%nat)  init
  end.

Definition for_loop_usize {acc : Type} (lo hi : uint_size) (f : uint_size -> acc -> acc) init : acc :=
  for_loop_range (from_uint_size lo) (from_uint_size hi) (fun x => f (usize x)) init.


Lemma foldi__move_S :
  forall {acc: Type}
         (fuel : nat)
         (i : uint_size)
         (f : uint_size -> acc -> acc)
         (cur : acc),
    foldi_ fuel (i .+ one) f (f i cur) = foldi_ (S fuel) i f cur.
Proof. reflexivity. Qed.

Lemma foldi__nat_move_S :
  forall {acc: Type}
         (fuel : nat)
         (i : nat)
         (f : nat -> acc -> acc)
         (cur : acc),
    foldi_nat_ fuel (S i) f (f i cur) = foldi_nat_ (S fuel) i f cur.
Proof. reflexivity. Qed.

Lemma foldi__nat_move_S_append :
  forall {acc: Type}
         (fuel : nat)
         (i : nat)
         (f : nat -> acc -> acc)
         (cur : acc),
    f (i + fuel)%nat (foldi_nat_ fuel i f cur) = foldi_nat_ (S fuel) i f cur.
Proof.
  induction fuel ; intros.
  - rewrite <- foldi__nat_move_S.
    unfold foldi_nat_.
    rewrite Nat.add_0_r.
    reflexivity.
  - rewrite <- foldi__nat_move_S.
    rewrite <- foldi__nat_move_S.
    replace (i + S fuel)%nat with (S i + fuel)%nat by lia.
    rewrite IHfuel.
    reflexivity.
Qed.

Theorem foldi_for_loop_eq :
  forall {acc} fuel f (cur : acc),
    foldi_nat_ fuel 0 f cur
    =
      for_loop_ fuel f cur.
Proof.
  induction fuel ; intros.
  - reflexivity.
  - unfold for_loop_ ; fold (@for_loop_ acc).
    rewrite <- foldi__nat_move_S_append.
    rewrite <- IHfuel.
    reflexivity.
Qed.

Lemma foldi__nat_move_to_function :
  forall {acc: ChoiceEquality}
         (fuel : nat)
         (i : nat)
         (f : nat -> acc -> acc)
         (cur : T acc),
    foldi_nat_ fuel i (fun x => f (S x)) (cur) = foldi_nat_ fuel (S i) f cur.
Proof.
  induction fuel ; intros.
  - reflexivity.
  - cbn.
    rewrite IHfuel.
    reflexivity.
Qed.

Lemma foldi__nat_move_to_function_add :
  forall {acc: ChoiceEquality}
         (fuel : nat)
         (i j : nat)
         (f : nat -> T acc ->  acc)
         (cur : T acc),
    foldi_nat_ fuel i (fun x => f (x + j)%nat) (cur) = foldi_nat_ fuel (i + j) f cur.
Proof.
  intros acc fuel i j. generalize dependent i.
  induction j ; intros.
  - rewrite Nat.add_0_r.
    replace (fun x : nat => f (x + 0)%nat) with f.
    reflexivity.
    apply functional_extensionality.
    intros.
    now rewrite Nat.add_0_r.
  - replace (i + S j)%nat with (S i + j)%nat by lia.
    rewrite <- IHj.
    rewrite <- foldi__nat_move_to_function.
    f_equal.
    apply functional_extensionality.
    intros.
    f_equal.
    lia.
Qed.

Theorem foldi_for_loop_range_eq :
  forall {acc : ChoiceEquality} lo hi f (cur : acc),
    foldi_nat lo hi f cur
    =
      for_loop_range lo hi f cur.
Proof.
  unfold foldi_nat.
  unfold for_loop_range.
  intros.

  destruct (hi - lo)%nat.
  - reflexivity.
  - rewrite <- foldi_for_loop_eq.
    (* pose (@foldi__nat_move_to_function acc (S n) 0 f). *)
    (* rewrite <- foldi__nat_move_to_function. *)

    induction lo.
    + f_equal.
      apply functional_extensionality.
      intros.
      now rewrite Nat.add_0_r.
    + replace (fun x : nat => f (x + S lo)%nat) with (fun x : nat => f (S (x + lo))%nat).
      2:{
        apply functional_extensionality.
        intros.
        f_equal.
        lia.
      }

      rewrite (foldi__nat_move_to_function (S n) 0 (fun x => f (x + lo)%nat)).
      rewrite foldi__nat_move_to_function_add.
      reflexivity.
Qed.

(* You can do one iteration of the fold by burning a unit of fuel *)
Lemma foldi__move_S_fuel :
  forall {acc: Type}
         (fuel : nat)
         (i : uint_size)
         (f : uint_size -> acc -> acc)
         (cur : acc),
    (0 <= Z.of_nat fuel <= wmax_unsigned U32)%Z ->
    f ((repr (Z.of_nat fuel)) .+ i) (foldi_ (fuel) i f cur) = foldi_ (S (fuel)) i f cur.
Proof.
  intros acc fuel.
  induction fuel ; intros.
  - cbn.
    replace (repr 0) with (@zero U32) by (rewrite wrepr0 ; reflexivity).
    rewrite add_zero_l.
    reflexivity.
  - do 2 rewrite <- foldi__move_S.
    replace (int_add (repr (Z.of_nat (S fuel))) i)
      with (int_add (repr (Z.of_nat fuel)) (int_add i one)).
    2 : {
      unfold ".+".
      rewrite addwA.
      rewrite addwC.
      rewrite addwA.
      f_equal.

      rewrite Nat2Z.inj_succ.
      unfold repr.
      unfold add_word.
      unfold wrepr.
      f_equal.
      rewrite urepr_word.
      Set Printing Coercions.
      replace (toword one)%Z with 1%Z by reflexivity.
      unfold urepr.
      unfold eqtype.val.
      unfold word_subType.
      unfold toword.
      unfold mkword.
      rewrite Zmod_small.

      rewrite Z.add_1_l.
      reflexivity.

      clear -H.
      unfold modulus.
      unfold two_power_nat.
      cbn in *.
      lia.
    }
    rewrite IHfuel.
    reflexivity.
    lia.
Qed.

(* You can do one iteration of the fold by burning a unit of fuel *)
Lemma foldi__nat_move_S_fuel :
  forall {acc: Type}
         (fuel : nat)
         (i : nat)
         (f : nat -> acc -> acc)
         (cur : acc),
    (0 <= Z.of_nat fuel <= @wmax_unsigned U32)%Z ->
    f (fuel + i)%nat (foldi_nat_ fuel i f cur) = foldi_nat_ (S fuel) i f cur.
Proof.
  induction fuel ; intros.
  - reflexivity.
  - do 2 rewrite <- foldi__nat_move_S.
    replace (S fuel + i)%nat with (fuel + (S i))%nat by (symmetry ; apply plus_Snm_nSm).
    rewrite IHfuel.
    + reflexivity.
    + lia.
Qed.

(* folds and natural number folds compute the same thing *)
Lemma foldi_to_foldi_nat :
  forall {acc: Type}
         (lo: uint_size) (* {lo <= hi} *)
         (hi: uint_size) (* {lo <= hi} *)
         (f: (uint_size) -> acc -> acc) (* {i < hi} *)
         (init: acc),
    (unsigned lo <= unsigned hi)%Z ->
    foldi lo hi init f = foldi_nat (Z.to_nat (unsigned lo)) (Z.to_nat (unsigned hi)) (fun x => f (repr (Z.of_nat x))) init.
Proof.
  intros.

  unfold foldi.
  unfold foldi_nat.

  destruct (uint_size_as_nat hi) as [ hi_n [ hi_eq hi_H ] ] ; subst.
  rewrite (@unsigned_repr_alt U32 _ hi_H) in *.
  rewrite Nat2Z.id.

  destruct (uint_size_as_nat lo) as [ lo_n [ lo_eq lo_H ] ] ; subst.
  rewrite (@unsigned_repr_alt U32 _ lo_H) in *.
  rewrite Nat2Z.id.

  remember (hi_n - lo_n)%nat as n.
  apply f_equal with (f := Z.of_nat) in Heqn.
  rewrite (Nat2Z.inj_sub) in Heqn by (apply Nat2Z.inj_le ; apply H).
  rewrite <- Heqn.

  assert (H_bound : (Z.pred 0 < Z.of_nat n < @modulus U32)%Z) by lia.

  clear Heqn.
  induction n.
  - reflexivity.
  - pose proof (H_max_bound := modulus_range_helper _ (range_of_nat_succ _ H_bound)).
    rewrite <- foldi__nat_move_S_fuel by apply H_max_bound.
    cbn.
    rewrite SuccNat2Pos.id_succ.
    rewrite <- foldi__move_S_fuel by apply H_max_bound.

    destruct n.
    + cbn.
      replace (repr 0) with (@zero U32) by (rewrite wrepr0 ; reflexivity).
      rewrite add_zero_l.
      reflexivity.
    + cbn in *.
      assert (H_bound_pred: (Z.pred 0 < Z.pos (Pos.of_succ_nat n) < @modulus U32)%Z) by lia.
      rewrite <- (IHn H_bound_pred) ; clear IHn.
      f_equal.
      * rewrite add_repr.
        do 2 rewrite Zpos_P_of_succ_nat.
        rewrite Z.add_succ_l.
        rewrite Nat2Z.inj_add.
        reflexivity.
      * rewrite SuccNat2Pos.id_succ.
        rewrite foldi__move_S.
        reflexivity.
Qed.

(* folds can be computed by doing one iteration and incrementing the lower bound *)
Lemma foldi_nat_split_S :
  forall {acc: Type}
         (lo: nat)
         (hi: nat) (* {lo <= hi} *)
         (f: nat -> acc -> acc) (* {i < hi} *)
         (init: acc),
    (lo < hi)%nat ->
    foldi_nat lo hi f init = foldi_nat (S lo) hi f (foldi_nat lo (S lo) f init).
Proof.
  unfold foldi_nat.
  intros.

  assert (succ_sub_diag : forall n, (S n - n = 1)%nat) by lia.
  rewrite (succ_sub_diag lo).

  induction hi ; [ lia | ].
  destruct (S hi =? S lo)%nat eqn:hi_eq_lo.
  - apply Nat.eqb_eq in hi_eq_lo ; rewrite hi_eq_lo in *.
    rewrite (succ_sub_diag lo).
    rewrite Nat.sub_diag.
    reflexivity.
  - apply Nat.eqb_neq in hi_eq_lo.
    apply Nat.lt_gt_cases in hi_eq_lo.
    destruct hi_eq_lo.
    + lia.
    + rewrite (Nat.sub_succ_l (S lo)) by apply (Nat.lt_le_pred _ _ H0).
      rewrite Nat.sub_succ_l by apply (Nat.lt_le_pred _ _ H).
      replace ((S (hi - S lo))) with (hi - lo)%nat by lia.
      reflexivity.
Qed.

(* folds can be split at some valid offset from lower bound *)
Lemma foldi_nat_split_add :
  forall (k : nat),
  forall {acc: Type}
         (lo: nat)
         (hi: nat) (* {lo <= hi} *)
         (f: nat -> acc -> acc) (* {i < hi} *)
         (init: acc),
  forall {guarantee: (lo + k <= hi)%nat},
    foldi_nat lo hi f init = foldi_nat (k + lo) hi f (foldi_nat lo (k + lo) f init).
Proof.
  induction k ; intros.
  - cbn.
    unfold foldi_nat.
    rewrite Nat.sub_diag.
    reflexivity.
  - rewrite foldi_nat_split_S by lia.
    replace (S k + lo)%nat with (k + S lo)%nat by lia.
    specialize (IHk acc (S lo) hi f (foldi_nat lo (S lo) f init)).
    rewrite IHk by lia.
    f_equal.
    rewrite <- foldi_nat_split_S by lia.
    reflexivity.
Qed.

(* folds can be split at some midpoint *)
Lemma foldi_nat_split :
  forall (mid : nat), (* {lo <= mid <= hi} *)
  forall {acc: Type}
         (lo: nat)
         (hi: nat) (* {lo <= hi} *)
         (f: nat -> acc -> acc) (* {i < hi} *)
         (init: acc),
  forall {guarantee: (lo <= mid <= hi)%nat},
    foldi_nat lo hi f init = foldi_nat mid hi f (foldi_nat lo mid f init).
Proof.
  intros.
  assert (mid_is_low_plus_constant : {k : nat | (mid = lo + k)%nat})  by (exists (mid - lo)%nat ; lia).
  destruct mid_is_low_plus_constant ; subst.
  rewrite Nat.add_comm.
  apply foldi_nat_split_add.
  apply guarantee.
Qed.

(* folds can be split at some midpoint *)
Lemma foldi_split :
  forall (mid : uint_size), (* {lo <= mid <= hi} *)
  forall {acc: Type}
         (lo: uint_size)
         (hi: uint_size) (* {lo <= hi} *)
         (f: uint_size -> acc -> acc) (* {i < hi} *)
         (init: acc),
  forall {guarantee: (unsigned lo <= unsigned mid <= unsigned hi)%Z},
    foldi lo hi init f = foldi mid hi (foldi lo mid init f) f.
Proof.
  intros.
  do 3 rewrite foldi_to_foldi_nat by lia.
  apply foldi_nat_split ; lia.
Qed.

(*** Seq *)

Definition nseq_choice (A: ChoiceEquality) (len : nat) : choice_type :=
  match len with
  | O => chUnit (* A *)
  | S n => chMap ('fin (S n)) (ct A)
  end.

Definition nseq_type (A: ChoiceEquality) (len : nat) : Type :=
  match len with
  | 0%nat => unit
  | S n => fmap.FMap.fmap_type (ordinal_ordType len) (T _) (* (Ord.clone (fun x : ssreflect.phantom (Ord.class_of (Ord.sort (ordinal_ordType len))) *)
                              (* (Ord.class (ordinal_ordType len)) => x)) *) (* [ordType of 'I_len] *)
  end.

#[global] Program Instance nseq (A: ChoiceEquality) (len : nat) : ChoiceEquality :=
  {| ct := nseq_choice A len ; T := nseq_type A len |}.
Next Obligation.
  intros.
  unfold nseq_type.
  unfold nseq_choice.
  rewrite <- @ChoiceEq.
  destruct (len) ; reflexivity.
Defined.

Definition seq_choice (A : ChoiceEquality) : choice_type := chMap 'nat (ct A).
Definition seq_type (A : ChoiceEquality) : Type := FMap.fmap_type nat_ordType (T _).
Program Definition seq (A : ChoiceEquality) : ChoiceEquality :=
  {| ct := seq_choice A ; T := seq_type A ; |}.
Next Obligation.
  intros.
  unfold seq_type.
  rewrite <- @ChoiceEq.
  reflexivity.
Defined.

Definition public_byte_seq := seq int8.
Definition byte_seq := seq int8.
Definition list_len := length.

Definition seq_index {A: ChoiceEquality} `{Default (T A)} (s: T (seq A)) (i : uint_size) : T A :=
  match getm s (from_uint_size i) with
  | Some a => a
  | None => default
  end.

Definition seq_len {A: ChoiceEquality} (s: T (seq A)) : T (uint_size) := usize (length s).

Definition seq_to_list (A: ChoiceEquality) (s : T (seq A)) : list (T A).
Proof.
  apply @FMap.fmval in s ; fold chElement in s.
  induction s.
  - apply [].
  - cbn in *.
    destruct a as [_ s0].
    apply (s0 :: IHs).
Defined.

Definition seq_from_list (A : ChoiceEquality) (l : list (T A)) : T (seq A) :=
  fmap_of_seq l.


Definition seq_new_ {A: ChoiceEquality} (init : A) (len: nat) : seq A :=
  fmap_of_seq (repeat init len).

Definition seq_new {A: ChoiceEquality} `{Default A} (len: nat) : seq A :=
  seq_new_ default len.

Definition seq_create {A: ChoiceEquality} `{Default A} (len: nat) : seq A :=
  seq_new len.

Fixpoint list_iter (n : nat) (k : nat) `{(n <= k)%nat} : list { x : nat | (x < k)%nat }.
  destruct n.
  - apply [].
  - apply app.
    + assert (H0: (n <= k)%nat) by lia.
      apply (list_iter n k H0).
    + apply cons.
      * assert (H1: (n < k)%nat) by lia.
        apply (@exist nat (fun x => (x < k)%nat) n H1).
      * apply nil.
Defined.

Definition repr_Z_succ : forall WS z, @repr WS (Z.succ z) = (repr z .+ one).
Proof.
  intros.
  replace one with (@repr WS 1) by (unfold one ; now rewrite word1_zmodE).    
  now rewrite add_repr.
Qed.  

Definition array_from_list
           (A: ChoiceEquality)
           (l: list (T A))
  : T (nseq A (length l)).
Proof.
  destruct l as [ | x xs ].
  - apply tt.
  - pose (l := x :: xs).
    pose proof (seq.foldr (fun (x : (T A) * { x : nat | (x < length l)%nat }) y =>
                             setm
                               (S := (T A))
                               y
                               (fintype.Ordinal (n := length l) (m := proj1_sig (snd x)) (ssrbool.introT ssrnat.ltP (proj2_sig (snd x))))
                               (fst x))
                          emptym
                          (seq.zip l (@list_iter (length l) (length l) (le_n (length l))))).
    rewrite <- ChoiceEq.
    hnf.
    rewrite ChoiceEq.
    apply X.
Defined.

(**** Array manipulation *)


Definition array_new_ {A: ChoiceEquality} (init:T A) (len: nat) : T (nseq A len).
  unfold T.
  unfold nseq.
  rewrite <- (repeat_length init (len)).
  intros.
  apply (@array_from_list A (repeat init len)).
Defined.


Definition array_index {A: ChoiceEquality} `{Default (T A)} {len : nat} (s: T (nseq A len)) {WS} (i: @int WS) : T A.
Proof.
  destruct (Z.to_nat (unsigned i) <? len)%nat eqn:H1.
  (* If i < len, index normally *)
  - apply Nat.ltb_lt in H1.
    destruct len. { lia. }
    rewrite <- ChoiceEq in s.
    cbn in s.
    rewrite -> ChoiceEq in s.
    destruct (@getm _ _ s (fintype.Ordinal (n := S len) (m := Z.to_nat (unsigned i)) (ssrbool.introT ssrnat.ltP H1))) as [f | ].
    + exact f.
    + exact default.

  (* otherwise return default element *)
  - exact default.
Defined.


Definition array_upd {A: ChoiceEquality} {len : nat} (s: T (nseq A len)) {WS} (i: @int WS) (new_v: T A) : T (nseq A len).
Proof.
  destruct (Z.to_nat (unsigned i) <? len)%nat eqn:v.
  (* If i < len, update normally *)
  - apply Nat.ltb_lt in v.
    destruct len. { lia. }
    rewrite <- ChoiceEq in s.
    cbn in s.
    rewrite -> ChoiceEq in s.
    rewrite <- ChoiceEq.
    cbn.
    rewrite -> ChoiceEq.
    apply (setm s (fintype.Ordinal (m := Z.to_nat (unsigned i)) (ssrbool.introT ssrnat.ltP v)) new_v).

  (* exact (VectorDef.replace s (Fin.of_nat_lt H) new_v). *)
  (* otherwise return original array *)
  - exact s.
Defined.

(* Definition array_upd {A: Type} {len : uint_size} (s: lseq A len) (i: uint_size) (new_v: A) : lseq A len := List.upd s i new_v. *)

(* substitutes a sequence (nseq) into an array (nseq), given index interval  *)
Definition update_sub {A : ChoiceEquality} {len slen} `{Default (T A)} (v : T (nseq A len)) (i : nat) (n : nat) (sub : T (nseq A slen)) : T (nseq A len) :=
  let fix rec x acc :=
    match x with
    | 0%nat => acc
    (* | 0 => array_upd acc 0 (array_index sub 0) *)
    | S x => rec x (array_upd acc (usize (i+x)%nat) (array_index sub (usize x)))
    end in
  rec (n - i + 1)%nat v.

(* Sanity check *)
(* Compute (to_list (update_sub [1;2;3;4;5] 0 4 (of_list [9;8;7;6;12]))). *)

Definition array_from_seq
           {a: ChoiceEquality}
           `{Default (T a)}
           (out_len:nat)
           (input: seq_type a)
  : T (nseq a out_len) :=
  let out := array_new_ default out_len in
  update_sub out 0 (out_len - 1) (@array_from_list a (@seq_to_list a input)).

(* Global Coercion array_from_seq : seq_type >-> nseq_type. *)

Definition slice {A} (l : list A) (i j : nat) : list A :=
  if (j <=? i)%nat then [] else firstn (j-i+1) (skipn i l).

Fixpoint array_to_list_helper {A : ChoiceEquality} {n} (f : T (nseq A (S n))) (i : nat) `{(i < S (S n))%nat} : list (T A).
  destruct i as [ | i' ].
  - exact [].
  - refine match getm f (fintype.Ordinal (m := i') _) with
           | None => []
           | Some a => array_to_list_helper A n f i' _ ++ [a]
           end.
    + apply (ssrbool.introT ssrnat.ltP).
      lia.
    + lia.
Defined.

Definition array_to_list {A : ChoiceEquality} {n} (f : T (nseq A n)) : list (T A).
  destruct n.
  - apply [].
  - refine (array_to_list_helper f (S n) (H := _)).
    lia.
Defined.

Definition array_to_seq {A : ChoiceEquality} {n} (f : nseq_type A n) : seq_type _ :=
  seq_from_list _ (array_to_list f).

Definition positive_slice {A : ChoiceEquality} `{Hd: Default (T A)} {n} `{H: Positive n} (l : T (nseq A n)) (i j : nat) `{H1: (i < j)%nat} `{(j - i < length (array_to_list l) - i)%nat} : Positive (length (slice (array_to_list l) i j)).
Proof.
  unfold slice.
  rewrite (proj2 (Nat.leb_gt j i) H1).
  rewrite firstn_length_le.
  - unfold Positive.
    apply (ssrbool.introT ssrnat.ltP).
    lia.
  - rewrite skipn_length.
    apply lt_n_Sm_le.
    lia.
Defined.

Theorem slice_length :
  forall A (l : list A) (i j : nat),
    length (slice l i j) =
      if (j <=? i)%nat then @length A ([]) else length (firstn (j - i + 1) (skipn i l)).
Proof.
  intros.
  unfold slice.
  destruct (j <=? i)%nat.
  - reflexivity.
  - reflexivity.
Qed.

Definition lseq_slice {A : ChoiceEquality} {n} (l : T (nseq A n)) (i j : nat) :
  T (@nseq A (length (slice (array_to_list l) (i) (j)))) :=
  array_from_list _ (slice (array_to_list l) (i) (j)).

Definition seq_sub {a : ChoiceEquality} `{Default (T (a))} (s : (T (seq a))) (start n : nat) :=
  lseq_slice (array_from_seq (from_uint_size (seq_len s)) s) start (start + n)%nat.

Definition array_update_slice
           {a : ChoiceEquality}
           `{Default (T (a))}
           {l : nat}
           (out: (T (nseq a l)))
           (start_out: nat)
           (input: (T (seq a)))
           (start_in: nat)
           (len: nat)
  : (T (nseq a l)) :=
  update_sub out start_out (len) (seq_sub input start_in len).

Definition array_from_slice
           {a: ChoiceEquality}
           `{Default (T a)}
           (default_value: (T a))
           (out_len: nat)
           (input: T (seq a))
           (start: nat)
           (slice_len: nat)
  : T (nseq a out_len) :=
  let out := array_new_ default out_len in
  array_from_seq out_len input.

Definition array_slice
           {a: ChoiceEquality}
           `{Default (T a)}
           (input: T (seq a))
           (start: nat)
           (slice_len: nat)
  : T (nseq a slice_len) :=
  array_from_slice default (slice_len) input (slice_len) (slice_len).

Definition array_from_slice_range
           {a: ChoiceEquality}
           `{Default (T a)}
           (default_value: T a)
           (out_len: nat)
           (input: T (seq a))
           (start_fin: (T uint_size * T uint_size))
  : T (nseq a out_len).
Proof.
  pose (out := array_new_ default_value (out_len)).
  destruct start_fin as [start fin].
  refine (update_sub out 0 ((from_uint_size fin) - (from_uint_size start)) _).

  apply (@lseq_slice a ((from_uint_size fin) - (from_uint_size start)) (array_from_seq ((from_uint_size fin) - (from_uint_size start)) input) (from_uint_size start) (from_uint_size fin)).
Defined.

Definition array_slice_range
           {a: ChoiceEquality}
           `{Default (T a)}
           {len : nat}
           (input: T (nseq a len))
           (start_fin:(T uint_size * T uint_size))
  : T (seq a) :=
  array_to_seq (lseq_slice input (from_uint_size (fst start_fin)) (from_uint_size (snd start_fin))).

Definition array_update
           {a: ChoiceEquality}
           `{Default (T a)}
           {len: nat}
           (s: T (nseq a len))
           (start : nat)
           (start_s: T (seq a))
  : T (nseq a len) :=
  update_sub s start (from_uint_size (seq_len start_s)) (array_from_seq (from_uint_size (seq_len start_s)) (start_s)).

Definition array_update_start
           {a: ChoiceEquality}
           `{Default (T a)}
           {len: nat}
           (s: T (nseq a len))
           (start_s: T (seq a))
  : T (nseq a len) :=
  update_sub s 0 (from_uint_size (seq_len start_s)) (array_from_seq (from_uint_size (seq_len start_s)) start_s).


Definition array_len  {a: ChoiceEquality} {len: nat} (s: T (nseq a len)) : uint_size := usize len.
(* May also come up as 'length' instead of 'len' *)
Definition array_length  {a: ChoiceEquality} {len: nat} (s: T (nseq a len)) : uint_size := usize len.

(**** Seq manipulation *)

Definition seq_slice
           {a: ChoiceEquality}
           `{Default (T a)}
           (s: (T (seq a)))
           (start: nat)
           (len: nat)
  : (seq a) :=
  array_to_seq (lseq_slice (array_from_seq (from_uint_size (seq_len s)) s) start (start + len)).

Definition seq_slice_range
           {a: ChoiceEquality}
           `{Default (T (a))}
           (input: (T (seq a)))
           (start_fin:((T (uint_size)) * (T (uint_size))))
  : (T (seq a)) :=
  seq_slice input (from_uint_size (fst start_fin)) (from_uint_size (snd start_fin)).

(* updating a subsequence in a sequence *)
Definition seq_update
           {a: ChoiceEquality}
           `{Default (T (a))}
           (s: (T (seq a)))
           (start: uint_size)
           (input: (T (seq a)))
  : (T (seq a)) :=
  array_to_seq (update_sub (array_from_seq (from_uint_size (seq_len s)) s) (from_uint_size start) (from_uint_size (seq_len input)) (array_from_seq (from_uint_size (seq_len input)) input)).

(* updating only a single value in a sequence*)
Definition seq_upd
           {a: ChoiceEquality}
           `{Default (T (a))}
           (s: (T (seq a)))
           (start: uint_size)
           (v: (T (a)))
  : (T (seq a)) :=
  seq_update s start (setm emptym 0%nat v).

Definition seq_update_start
           {a: ChoiceEquality}
           `{Default (T (a))}
           (s: (T (seq a)))
           (start_s: (T (seq a)))
  : (T (seq a)) :=
  array_to_seq (update_sub (array_from_seq (from_uint_size (seq_len s)) s) 0 (from_uint_size (seq_len start_s)) (array_from_seq (from_uint_size (seq_len start_s)) start_s)).

Definition seq_update_slice
           {a : ChoiceEquality}
           `{Default (T (a))}
           (out: (T (seq a)))
           (start_out: nat)
           (input: (T (seq a)))
           (start_in: nat)
           (len: nat)
  : (T (seq a))  (* (from_uint_size (seq_len out)) *)
  :=
  array_to_seq (update_sub (array_from_seq (from_uint_size (seq_len out)) out) start_out len (seq_sub input start_in len)).

Definition seq_concat
           {a : ChoiceEquality}
           (s1 :(T (seq a)))
           (s2: (T (seq a)))
  : (T (seq a)) :=
  seq_from_list _ (seq_to_list _ s1 ++ seq_to_list _ s2).

Definition seq_concat_owned
           {a : ChoiceEquality}
           (s1 :(T (seq a)))
           (s2: (T (seq a)))
  : (T (seq a)) := seq_concat s1 s2.

Definition seq_push
           {a : ChoiceEquality}
           (s1 :(T (seq a)))
           (s2: (T (a)))
  : (T (seq a)) :=
  seq_from_list _ ((seq_to_list _ s1) ++ [s2]).

Definition seq_push_owned
           {a : ChoiceEquality}
           (s1 :(T (seq a)))
           (s2: (T (a)))
  : (T (seq a)) := seq_push s1 s2.

Definition seq_from_slice
           {a: ChoiceEquality}
           `{Default (T (a))}
           (input: (T (seq a)))
           (start_fin: ((T (uint_size)) * (T (uint_size))))
  : (T (seq a)) :=
  let out := array_new_ (default) (from_uint_size (seq_len input)) in
  let (start, fin) := start_fin in
  array_to_seq (update_sub out 0 ((from_uint_size fin) - (from_uint_size start)) ((lseq_slice (array_from_seq (from_uint_size (seq_len input)) input) (from_uint_size start) (from_uint_size fin)))).

Definition seq_from_slice_range
           {a: ChoiceEquality}
           `{Default (T (a))}
           (input: (T (seq a)))
           (start_fin: ((T (uint_size)) * (T (uint_size))))
  : (T (seq a)) :=
  let out := array_new_ (default) (from_uint_size (seq_len input)) in
  let (start, fin) := start_fin in
  array_to_seq (update_sub out 0 ((from_uint_size fin) - (from_uint_size start)) ((lseq_slice (array_from_seq (from_uint_size (seq_len input)) input) (from_uint_size start) (from_uint_size fin)))).

Definition seq_from_seq {A} (l : seq A) : seq A := l.

(**** Chunking *)

Definition seq_num_chunks {a: ChoiceEquality} (s: (T (seq a))) (chunk_len: uint_size) : uint_size :=
  ((seq_len s .+ chunk_len .- one) ./ chunk_len)%nat.

Definition seq_chunk_len
           {a: ChoiceEquality}
           (s: (T (seq a)))
           (chunk_len: nat)
           (chunk_num: nat)
  : nat_ChoiceEquality :=
  let idx_start := (chunk_len * chunk_num)%nat in
  if ((from_uint_size (seq_len s)) <.? (idx_start + chunk_len))%nat then
    ((from_uint_size (seq_len s)) - idx_start)%nat
  else
    chunk_len.

(* Definition seq_chunk_same_len_same_chunk_len
  {a: Type}
  (s1 s2: seq a)
  (chunk_len: nat)
  (chunk_num: nat)
  : Lemma
    (requires (LSeq.length s1 := LSeq.length s2 /\ chunk_len * chunk_num <= Seq.length s1))
    (ensures (seq_chunk_len s1 chunk_len chunk_lseq. Admitted. *)

Definition seq_get_chunk
           {a: ChoiceEquality}
           `{Default (T (a))}
           (s: (T (seq a)))
           (chunk_len: uint_size)
           (chunk_num: uint_size)
  : ((T (uint_size '× seq a)))
  :=
  let idx_start := (from_uint_size chunk_len * from_uint_size chunk_num)%nat in
  let out_len := seq_chunk_len s (from_uint_size chunk_len) (from_uint_size chunk_num) in
  (usize out_len, array_to_seq (lseq_slice (array_from_seq (from_uint_size (seq_len s)) s) idx_start (idx_start + seq_chunk_len s (from_uint_size chunk_len) (from_uint_size chunk_num)))).

Definition seq_set_chunk
           {a: ChoiceEquality}
           `{Default (T (a))}
           (s: (T (seq a)))
           (chunk_len: uint_size)
           (chunk_num: uint_size)
           (chunk: (T (seq a)) ) : (T (seq a)) :=
  let idx_start := (from_uint_size chunk_len * from_uint_size chunk_num)%nat in
  let out_len := seq_chunk_len s (from_uint_size chunk_len) (from_uint_size chunk_num) in
  array_to_seq (update_sub (array_from_seq (from_uint_size (seq_len s)) s) idx_start out_len (array_from_seq (from_uint_size (seq_len chunk)) chunk)).


Definition seq_num_exact_chunks {a} (l : (T (seq a))) (chunk_size : (T (uint_size))) : (T (uint_size)) :=
  (repr (Z.of_nat (length l))) ./ chunk_size.

(* Until #84 is fixed this returns an empty sequence if not enough *)
Definition seq_get_exact_chunk {a : ChoiceEquality} `{Default (T (a))} (l : (T (seq a))) (chunk_size chunk_num: (T (uint_size))) : (T (seq a)) :=
  let '(len, chunk) := seq_get_chunk l chunk_size chunk_num in
  if eqtype.eq_op len chunk_size then emptym else chunk.

Definition seq_set_exact_chunk {a : ChoiceEquality} `{H : Default (T (a))} :=
  @seq_set_chunk a H.

Definition seq_get_remainder_chunk {a : ChoiceEquality} `{Default a} (l : seq a) (chunk_size : uint_size) : seq a :=  
  let chunks := seq_num_chunks l chunk_size in
  let last_chunk := if (zero <.? chunks)
                    then (chunks .- one)%nat
                    else zero in
  let (len, chunk) := seq_get_chunk l chunk_size last_chunk in
  if eqtype.eq_op len chunk_size
  then emptym
  else chunk.

Check @fmap.FMap.FMap _ _ [].

Fixpoint list_xor_ {WS} (x y : list (@int WS)) : list (@int WS) :=
  match x, y with
  | (x :: xs), (y :: ys) => (int_xor x y) :: (list_xor_ xs ys) 
  | [] , _ => y
  | _, [] => x
  end.

Definition seq_xor_ {WS} (x y : seq (@int WS)) : seq (@int WS) :=
  seq_from_list _ (list_xor_ (seq_to_list _ x) (seq_to_list _ y)).
Infix "seq_xor" := seq_xor_ (at level 33) : hacspec_scope.

Fixpoint list_truncate {a} (x : list a) (n : nat) : list a := (* uint_size *)
  match x, n with
  | _, O => []
  | [], _ => []
  | (x :: xs), S n' => x :: (list_truncate xs n')
  end.
Definition seq_truncate {a} (x : seq a) (n : nat) : seq a := (* uint_size *)
  seq_from_list _ (list_truncate (seq_to_list _ x) n).
  
(**** Numeric operations *)

(* takes two nseq's and joins them using a function op : a -> a -> a *)
Definition array_join_map
           {a: ChoiceEquality}
           `{Default (T (a))}
           {len: nat}
           (op: (T (a)) -> (T (a)) -> (T (a)))
           (s1: (T (nseq a len)))
           (s2 : (T (nseq a len))) :=
  let out := s1 in
  foldi (usize 0%nat) (usize len) out (fun i out =>
                                         (* let i := from_uint_size i in *)
                                         array_upd out i (op (array_index s1 i) (array_index s2 i))
                                      ).

Infix "array_xor" := (array_join_map int_xor) (at level 33) : hacspec_scope.
Infix "array_add" := (array_join_map int_add) (at level 33) : hacspec_scope.
Infix "array_minus" := (array_join_map int_sub) (at level 33) : hacspec_scope.
Infix "array_mul" := (array_join_map int_mul) (at level 33) : hacspec_scope.
Infix "array_div" := (array_join_map int_div) (at level 33) : hacspec_scope.
Infix "array_or" := (array_join_map int_or) (at level 33) : hacspec_scope.
Infix "array_and" := (array_join_map int_and) (at level 33) : hacspec_scope.

Fixpoint array_eq_
         {a: ChoiceEquality}
         {len: nat}
         (eq: (T (a)) -> (T (a)) -> bool)
         (s1: (T (nseq a len)))
         (s2 : (T (nseq a len)))
         {struct len}
  : bool.
Proof.
  destruct len ; cbn in *.
  - exact  true.
  - destruct (getm s1 (fintype.Ordinal (m := len) (ssrnat.ltnSn _))) as [s | ].
    + destruct (getm s2 (fintype.Ordinal (m := len) (ssrnat.ltnSn _))) as [s0 | ].
      * exact (eq s s0).
      * exact false.
    + exact false.
Defined.

Infix "array_eq" := (array_eq_ eq) (at level 33) : hacspec_scope.
Infix "array_neq" := (fun s1 s2 => negb (array_eq_ eq s1 s2)) (at level 33) : hacspec_scope.


(**** Integers to arrays *)
Axiom uint32_to_le_bytes : int32 -> nseq int8 4.
(* Definition uint32_to_le_bytes (x: uint32) : nseq uint8 4 :=
  LBSeq.uint_to_bytes_le x. *)

Axiom uint32_to_be_bytes : int32 -> nseq int8 4.
(* Definition uint32_to_be_bytes (x: uint32) : nseq uint8 4 :=
  LBSeq.uint_to_bytes_be x *)

Axiom uint32_from_le_bytes : nseq int8 4 -> int32.
(* Definition uint32_from_le_bytes (s: nseq uint8 4) : uint32 :=
  LBSeq.uint_from_bytes_le s *)

Axiom uint32_from_be_bytes : nseq int8 4 -> int32.
(* Definition uint32_from_be_bytes (s: nseq uint8 4) : uint32 :=
  LBSeq.uint_from_bytes_be s *)

Axiom uint64_to_le_bytes : int64 -> nseq int8 8.
(* Definition uint64_to_le_bytes (x: uint64) : nseq uint8 8 :=
  LBSeq.uint_to_bytes_le x *)

Axiom uint64_to_be_bytes : int64 -> nseq int8 8.
(* Definition uint64_to_be_bytes (x: uint64) : nseq uint8 8 :=
  LBSeq.uint_to_bytes_be x *)

Axiom uint64_from_le_bytes : nseq int8 8 -> int64.
(* Definition uint64_from_le_bytes (s: nseq uint8 8) : uint64 :=
  LBSeq.uint_from_bytes_le s *)

Axiom uint64_from_be_bytes : nseq int8 8 -> int64.
(* Definition uint64_from_be_bytes (s: nseq uint8 8) : uint64 :=
  LBSeq.uint_from_bytes_be s *)

Axiom uint128_to_le_bytes : int128 -> nseq int8 16.
(* Definition uint128_to_le_bytes (x: uint128) : nseq uint8 16 :=
  LBSeq.uint_to_bytes_le x *)

Axiom uint128_to_be_bytes : int128 -> nseq int8 16.
(* Definition uint128_to_be_bytes (x: uint128) : nseq uint8 16 :=
  LBSeq.uint_to_bytes_be x *)

Axiom uint128_from_le_bytes : nseq int8 16 -> int128.
(* Definition uint128_from_le_bytes (input: nseq uint8 16) : uint128 :=
  LBSeq.uint_from_bytes_le input *)

Axiom uint128_from_be_bytes : nseq int8 16 -> int128.
(* Definition uint128_from_be_bytes (s: nseq uint8 16) : uint128 :=
  LBSeq.uint_from_bytes_be s *)

Axiom u32_to_le_bytes : int32 -> nseq int8 4.
(* Definition u32_to_le_bytes (x: pub_uint32) : nseq pub_uint8 4 :=
  LBSeq.uint_to_bytes_le x *)

Axiom u32_to_be_bytes : int32 -> nseq int8 4.
(* Definition u32_to_be_bytes (x: pub_uint32) : nseq pub_uint8 4 :=
  LBSeq.uint_to_bytes_be x *)

Axiom u32_from_le_bytes : nseq int8 4 -> int32.
(* Definition u32_from_le_bytes (s: nseq pub_uint8 4) : pub_uint32 :=
  LBSeq.uint_from_bytes_le s *)

Axiom u32_from_be_bytes : nseq int8 4 -> int32.
(* Definition u32_from_be_bytes (s: nseq pub_uint8 4) : pub_uint32 :=
  LBSeq.uint_from_bytes_be s *)

Axiom u64_to_le_bytes : int64 -> nseq int8 8.
(* Definition u64_to_le_bytes (x: int64) : nseq int8 8 :=
  LBSeq.uint_to_bytes_le x *)

Axiom u64_from_le_bytes : nseq int8 8 -> int64.
(* Definition u64_from_le_bytes (s: nseq int8 8) : int64 :=
  LBSeq.uint_from_bytes_le s *)

Axiom u128_to_le_bytes : int128 -> nseq int8 16.
(* Definition u128_to_le_bytes (x: int128) : nseq int8 16 :=
  LBSeq.uint_to_bytes_le x *)

Axiom u128_to_be_bytes : int128 -> nseq int8 16.
(* Definition u128_to_be_bytes (x: int128) : nseq int8 16 :=
  LBSeq.uint_to_bytes_be x *)

Axiom u128_from_le_bytes : nseq int8 16 -> int128.
(* Definition u128_from_le_bytes (input: nseq int8 16) : int128 :=
  LBSeq.uint_from_bytes_le input *)

Axiom u128_from_be_bytes : nseq int8 16 -> int128.
(* Definition u128_from_be_bytes (s: nseq int8 16) : pub_uint128 :=
  LBSeq.uint_from_bytes_be s *)


(*** Nats *)


Definition nat_mod_choice {p : Z} : choice_type := 'fin (S (Init.Nat.pred (Z.to_nat p))).
Definition nat_mod_type {p : Z} : Type := 'I_(S (Init.Nat.pred (Z.to_nat p))).
#[global] Instance nat_mod (p : Z) : ChoiceEquality :=
  {| ct :=  nat_mod_choice ; T :=  @nat_mod_type p ; ChoiceEq := eq_refl |}.
Definition mk_natmod {p} (z : Z) : nat_mod p := @zmodp.inZp (Init.Nat.pred (Z.to_nat p)) (Z.to_nat z).


Definition nat_mod_equal {p} (a b : nat_mod p) : bool :=
  @eqtype.eq_op (ordinal_eqType (S (Init.Nat.pred (Z.to_nat p)))) a b.

Definition nat_mod_equal_reflect {p} {a b} : Bool.reflect (a = b) (@nat_mod_equal p a b) :=
  @eqtype.eqP (ordinal_eqType (S (Init.Nat.pred (Z.to_nat p)))) a b.

Definition nat_mod_zero {p} : nat_mod p := zmodp.Zp0.
Definition nat_mod_one {p} : nat_mod p := zmodp.Zp1.
Definition nat_mod_two {p} : nat_mod p := zmodp.inZp 2.


(* convenience coercions from nat_mod to Z and N *)
(* Coercion Z.of_N : N >-> Z. *)

Definition nat_mod_add {n : Z} (a : nat_mod n) (b : nat_mod n) : nat_mod n := zmodp.Zp_add a b.

Infix "+%" := nat_mod_add (at level 33) : hacspec_scope.

Definition nat_mod_mul {n : Z} (a:nat_mod n) (b:nat_mod n) : nat_mod n := zmodp.Zp_mul a b.
Infix "*%" := nat_mod_mul (at level 33) : hacspec_scope.

Definition nat_mod_sub {n : Z} (a:nat_mod n) (b:nat_mod n) : nat_mod n := zmodp.Zp_add a (zmodp.Zp_opp b).
Infix "-%" := nat_mod_sub (at level 33) : hacspec_scope.

Definition nat_mod_div {n : Z} (a:nat_mod n) (b:nat_mod n) : nat_mod n := zmodp.Zp_mul a (zmodp.Zp_inv b).
Infix "/%" := nat_mod_div (at level 33) : hacspec_scope.

(* A % B = (a * B + r) *)

Definition nat_mod_neg {n : Z} (a:nat_mod n) : nat_mod n := zmodp.Zp_opp a.

Definition nat_mod_inv {n : Z} (a:nat_mod n) : nat_mod n := zmodp.Zp_inv a.

Definition nat_mod_exp_def {p : Z} (a:nat_mod p) (n : nat) : nat_mod p :=
  let fix exp_ (e : nat_mod p) (n : nat) :=
    match n with
    | 0%nat => nat_mod_one
    | S n => nat_mod_mul a (exp_ a n)
    end in
  exp_ a n.

Definition nat_mod_exp {WS} {p} a n := @nat_mod_exp_def p a (Z.to_nat (@unsigned WS n)).
Definition nat_mod_pow {WS} {p} a n := @nat_mod_exp_def p a (Z.to_nat (@unsigned WS n)).
Definition nat_mod_pow_felem {p} a n := @nat_mod_exp_def p a (Z.to_nat (from_uint_size n)).
Definition nat_mod_pow_self {p} a n := @nat_mod_pow_felem p a n.

Close Scope nat_scope.

(* We assume x < m *)
Definition nat_mod_from_secret_literal {m : Z} (x:int128) : nat_mod m := @zmodp.inZp (Init.Nat.pred (Z.to_nat m)) (Z.to_nat (unsigned x)).

Definition nat_mod_from_literal (m : Z) (x:int128) : nat_mod m := nat_mod_from_secret_literal x.

Axiom nat_mod_to_byte_seq_le : forall {n : Z}, nat_mod n -> seq int8.
Axiom nat_mod_to_byte_seq_be : forall {n : Z}, nat_mod n -> seq int8.
Axiom nat_mod_to_public_byte_seq_le : forall (n : Z), nat_mod n -> seq int8.
Axiom nat_mod_to_public_byte_seq_be : forall (n : Z), nat_mod n -> seq int8.

Definition nat_mod_val (p : Z) (a : nat_mod p) : Z := Z.of_nat (nat_of_ord a).

Definition nat_mod_bit {n : Z} (a : nat_mod n) (i : uint_size) : bool_ChoiceEquality :=
  Z.testbit (nat_mod_val _ a) (from_uint_size i).

(* Alias for nat_mod_bit *)
Definition nat_get_mod_bit {p} (a : nat_mod p) := nat_mod_bit a.
Definition nat_mod_get_bit {p} (a : nat_mod p) n :=
  if (nat_mod_bit a n)
  then @nat_mod_one p
  else @nat_mod_zero p.

(*
Definition nat_mod_to_public_byte_seq_le (n: pos)  (len: uint_size) (x: nat_mod_mod n) : lseq pub_uint8 len =
  Definition n' := n % (pow2 (8 * len)) in
  Lib.ByteSequence.nat_mod_to_bytes_le len n'*)

(* Definition nat_to_public_byte_seq_be (n: pos)  (len: uint_size) (x: nat_mod n) : lseq pub_uint8 len =
  Definition n' := n % (pow2 (8 * len)) in
  Lib.ByteSequence.nat_to_bytes_be len n' *)

Axiom array_declassify_eq : forall  {A l}, nseq A l -> nseq A l -> bool_ChoiceEquality.
Axiom array_to_le_uint32s : forall {A l}, nseq A l -> seq uint32.  (* (l/4) *)
Axiom array_to_be_uint32s : forall {l}, nseq uint8 l -> seq uint32.  (* (l/4) *)
Axiom array_to_le_uint64s : forall {A l}, nseq A l -> seq uint64.  (* (l/8) *)
Axiom array_to_be_uint64s : forall {l}, nseq uint8 l -> seq uint64.  (* (l/8) *)
Axiom array_to_le_uint128s : forall {A l}, nseq A l -> seq uint128.  (* (l/16) *)
Axiom array_to_be_uint128s : forall {l}, nseq uint8 l -> seq uint128.  (* (l/16) *)
Axiom array_to_le_bytes : forall {A l}, nseq A l -> seq uint8.
Axiom array_to_be_bytes : forall {A l}, nseq A l -> seq uint8.
Axiom nat_mod_from_byte_seq_le : forall  {A n}, seq A -> nat_mod n.
Axiom most_significant_bit : forall {m}, nat_mod m -> uint_size -> uint_size.


(* We assume 2^x < m *)
Definition nat_mod_pow2 (m : Z) (x : N) : nat_mod m := mk_natmod (Z.pow 2 (Z.of_N x)).


Section Casting.

  (* Type casts, as defined in Section 4.5 in https://arxiv.org/pdf/1106.3448.pdf *)
  Class Cast A B := cast : A -> B.

  Arguments cast {_} _ {_}.

  Notation "' x" := (cast _ x) (at level 20) : hacspec_scope.

  (* Casting to self is always possible *)
  Global Instance cast_self {A} : Cast A A := {
      cast a := a
    }.

  Global Instance cast_transitive {A B C} `{Hab: Cast A B} `{Hbc: Cast B C} : Cast A C := {
      cast a := Hbc (Hab a)
    }.

  Global Instance cast_prod {A B C D} `{Cast A B} `{Cast C D} : Cast (A * C) (B * D) := {
      cast '(a, c) := (cast _ a, cast _ c)
    }.

  Global Instance cast_option {A B} `{Cast A B} : Cast (option A) (option B) := {
      cast a := match a with Some a => Some (cast _ a) | None => None end
    }.

  Global Instance cast_option_b {A B} `{Cast A B} : Cast A (option B) := {
      cast a := Some (cast _ a)
    }.

  (* Global Instances for common types *)

  Global Instance cast_nat_to_N : Cast nat N := {
      cast := N.of_nat
    }.

  Global Instance cast_N_to_Z : Cast N Z := {
      cast := Z.of_N
    }.

  Global Instance cast_Z_to_int {WORDSIZE} : Cast Z (@int WORDSIZE) := {
      cast n := repr n
    }.

  Global Instance cast_natmod_to_Z {p} : Cast (nat_mod p) Z := {
      cast n := nat_mod_val _ n
    }.

  (* Note: should be aware of typeclass resolution with int/uint since they are just aliases of each other currently *)
  Global Instance cast_int8_to_uint32 : Cast int8 uint32 := {
      cast n := repr (unsigned n)
    }.
  Global Instance cast_int8_to_int32 : Cast int8 int32 := {
      cast n := repr (signed n)
    }.

  Global Instance cast_uint8_to_uint32 : Cast uint8 uint32 := {
      cast n := repr (unsigned n)
    }.

  Global Instance cast_int_to_nat `{WS : wsize} : Cast int nat := {
      cast n := Z.to_nat (@signed WS n)
    }.

  Close Scope hacspec_scope.
End Casting.


Global Arguments pair {_ _} & _ _.
(* Global Arguments id {_} & _. *)
Section Coercions.
  (* First, in order to have automatic coercions for tuples, we add bidirectionality hints: *)

  (* Integer coercions *)
  (* We have nat >-> N >-> Z >-> int/int32 *)
  (* and uint >-> Z *)
  (* and N >-> nat *)

  Global Coercion N.to_nat : N >-> nat.
  Global Coercion Z.of_N : N >-> Z.

  (* Global Coercion repr : Z >-> int_type. *)

  Definition Z_to_int `{WS : wsize} (n : Z) : @int_type WS := repr n.
  Global Coercion  Z_to_int : Z >-> int_type.

  Definition Z_to_uint_size (n : Z) : uint_size_type := repr n.
  Global Coercion Z_to_uint_size : Z >-> uint_size_type.
  Definition Z_to_int_size (n : Z) : int_size_type := repr n.
  Global Coercion Z_to_int_size : Z >-> int_size_type.

  Definition N_to_int `{WS : wsize} (n : N) : @int_type WS := repr (Z.of_N n).
  Global Coercion N.of_nat : nat >-> N.
  Global Coercion N_to_int : N >-> int_type.
  Definition N_to_uint_size (n : Z) : uint_size_type := repr n.
  Global Coercion N_to_uint_size : Z >-> uint_size_type.
  Definition nat_to_int `{WS : wsize} (n : nat) : @int_type WS := repr (Z.of_nat n).
  Global Coercion nat_to_int : nat >-> int_type.

  Definition uint_size_to_nat (n : uint_size_type) : nat := from_uint_size n.
  Global Coercion uint_size_to_nat : uint_size_type >-> nat.

  Definition uint_size_to_Z (n : uint_size_type) : Z := from_uint_size n.
  Global Coercion uint_size_to_Z : uint_size_type >-> Z.

  Definition uint32_to_nat (n : uint32_type) : nat := unsigned n.
  Global Coercion uint32_to_nat : uint32_type >-> nat.

  Definition int8_to_nat (n : int8_type) : nat := unsigned n.
  Global Coercion int8_to_nat : int8_type >-> nat.
  Definition int16_to_nat (n : int16_type) : nat := unsigned n.
  Global Coercion int16_to_nat : int16_type >-> nat.
  Definition int32_to_nat (n : int32_type) : nat := unsigned n.
  Global Coercion int32_to_nat : int32_type >-> nat.
  Definition int64_to_nat (n : int64_type) : nat := unsigned n.
  Global Coercion int64_to_nat : int64_type >-> nat.
  Definition int128_to_nat (n : int128_type) : nat := unsigned n.
  Global Coercion int128_to_nat : int128_type >-> nat.

  (* coercions int8 >-> int16 >-> ... int128 *)

  Definition int8_to_int16 (n : int8_type) : int16_type := repr n.
  Global Coercion int8_to_int16 : int8_type >-> int16_type.

  Definition int8_to_int32 (n : int8_type) : int32_type := repr n.
  Global Coercion int8_to_int32 : int8_type >-> int32_type.

  Definition int16_to_int32 (n : int16_type) : int32_type := repr n.
  Global Coercion int16_to_int32 : int16_type >-> int32_type.

  Definition int32_to_int64 (n : int32_type) : int64_type := repr n.
  Global Coercion int32_to_int64 : int32_type >-> int64_type.

  Definition int64_to_int128 (n : int64_type) : int128_type := repr n.
  Global Coercion int64_to_int128 : int64_type >-> int128_type.

  Definition int32_to_int128 (n : int32_type) : int128_type := repr n.
  Global Coercion int32_to_int128 : int32_type >-> int128_type.

  Definition uint_size_to_int64 (n : uint_size_type) : int64_type := repr n.
  Global Coercion uint_size_to_int64 : uint_size_type >-> int64_type.


  (* coercions into nat_mod *)
  Definition Z_in_nat_mod {m : Z} (x:Z) : @nat_mod_type m := @mk_natmod m x.
  (* Global Coercion Z_in_nat_mod : Z >-> nat_mod_type. *)

  Definition int_in_nat_mod {m : Z} `{WS : wsize} (x:@int_type WS) : @nat_mod_type m := mk_natmod (unsigned x).
  Global Coercion int_in_nat_mod : int_type >-> nat_mod_type.

  Definition nat_mod_in_int {m : Z} `{WS : wsize} (x:@nat_mod_type m) : @int_type WS := (repr (nat_mod_val _ x)).
  Global Coercion nat_mod_in_int : nat_mod_type >-> int_type.

  Definition nat_mod_in_Z {m : Z} `{WS : wsize} (x:@nat_mod_type m) : Z := (nat_mod_val _ x).
  Global Coercion nat_mod_in_Z : nat_mod_type >-> Z.

  Definition uint_size_in_nat_mod (n : uint_size_type) : @nat_mod_type 16 := int_in_nat_mod n.
  Global Coercion uint_size_in_nat_mod : uint_size_type >-> nat_mod_type.

End Coercions.


(*** Casting *)

Definition uint128_from_usize (n : uint_size) : int128 := repr n.
Definition uint64_from_usize (n : uint_size) : int64 := repr n.
Definition uint32_from_usize (n : uint_size) : int32 := repr n.
Definition uint16_from_usize (n : uint_size) : int16 := repr n.
Definition uint8_from_usize (n : uint_size) : int8 := repr n.

Definition uint128_from_uint8 (n : int8) : int128 := repr n.
Definition uint64_from_uint8 (n : int8) : int64 := repr n.
Definition uint32_from_uint8 (n : int8) : int32 := repr n.
Definition uint16_from_uint8 (n : int8) : int16 := repr n.
Definition usize_from_uint8 (n : int8) : uint_size := repr n.

Definition uint128_from_uint16 (n : int16) : int128 := repr n.
Definition uint64_from_uint16 (n : int16) : int64 := repr n.
Definition uint32_from_uint16 (n : int16) : int32 := repr n.
Definition uint8_from_uint16 (n : int16) : int8 := repr n.
Definition usize_from_uint16 (n : int16) : uint_size := repr n.

Definition uint128_from_uint32 (n : int32) : int128 := repr n.
Definition uint64_from_uint32 (n : int32) : int64 := repr n.
Definition uint16_from_uint32 (n : int32) : int16 := repr n.
Definition uint8_from_uint32 (n : int32) : int8 := repr n.
Definition usize_from_uint32 (n : int32) : uint_size := repr n.

Definition uint128_from_uint64 (n : int64) : int128 := repr n.
Definition uint32_from_uint64 (n : int64) : int32 := repr n.
Definition uint16_from_uint64 (n : int64) : int16 := repr n.
Definition uint8_from_uint64 (n : int64) : int8 := repr n.
Definition usize_from_uint64 (n : int64) : uint_size := repr n.

Definition uint64_from_uint128 (n : int128) : int64 := repr n.
Definition uint32_from_uint128 (n : int128) : int32 := repr n.
Definition uint16_from_uint128 (n : int128) : int16 := repr n.
Definition uint8_from_uint128 (n : int128) : int8 := repr n.
Definition usize_from_uint128 (n : int128) : uint_size := repr n.


Definition uint8_equal : int8 -> int8 -> bool := eqb.

Theorem nat_mod_eqb_spec : forall {p} (a b : nat_mod p), nat_mod_equal a b = true <-> a = b.
Proof.
  symmetry ; exact (ssrbool.rwP nat_mod_equal_reflect).
Qed.

Global Instance nat_mod_eqdec {p} : EqDec (nat_mod p) := {
    eqb := nat_mod_equal ;
    eqb_leibniz := nat_mod_eqb_spec;
  }.

Global Instance nat_mod_comparable `{p : Z} : Comparable (nat_mod p) := {
    ltb a b := Z.ltb (nat_mod_val p a) (nat_mod_val p b);
    leb a b := if Zeq_bool a b then true else Z.ltb (nat_mod_val p a) (nat_mod_val p b) ;
    gtb a b := Z.ltb (nat_mod_val p b) (nat_mod_val p a);
    geb a b := if Zeq_bool b a then true else Z.ltb (nat_mod_val p b) (nat_mod_val p a) ;
  }.

Fixpoint nat_mod_rem_aux {n : Z} (a:nat_mod n) (b:nat_mod n) (f : nat) {struct f} : nat_mod n :=
  match f with
  | O => a
  | S f' =>
      if geb a b
      then nat_mod_rem_aux (nat_mod_sub a b) b f'
      else a
  end.

Definition nat_mod_rem {n : Z} (a:nat_mod n) (b:nat_mod n) : nat_mod n :=
  if nat_mod_equal b nat_mod_zero
  then nat_mod_one
  else nat_mod_rem_aux a b (S (nat_mod_div a b)).

Infix "rem" := nat_mod_rem (at level 33) : hacspec_scope.

Global Instance bool_eqdec : EqDec bool := {
    eqb := Bool.eqb;
    eqb_leibniz := Bool.eqb_true_iff;
  }.

Global Instance string_eqdec : EqDec String.string := {
    eqb := String.eqb;
    eqb_leibniz := String.eqb_eq ;
  }.

(* Global Instance unit_eqdec : EqDec unit := { *)
(*   eqb := fun _ _ => true ; *)
(*   eqb_leibniz := fun 'tt 'tt => (conj (fun _ => eq_refl) (fun _ => eq_refl)) ; *)
(* }. *)

Fixpoint list_eqdec {A} `{EqDec A} (l1 l2 : list A) : bool :=
  match l1, l2 with
  | x::xs, y::ys => if eqb x y then list_eqdec xs ys else false
  | [], [] => true
  | _,_ => false
  end.

Lemma list_eqdec_refl : forall {A} `{EqDec A} (l1 : list A), list_eqdec l1 l1 = true.
Proof.
  intros ; induction l1 ; cbn ; try rewrite eqb_refl ; easy.
Qed.

Lemma list_eqdec_sound : forall {A} `{EqDec A} (l1 l2 : list A), list_eqdec l1 l2 = true <-> l1 = l2.
Proof.
  intros A H l1.
  induction l1 ; induction l2 ; split ; intros ; simpl in * ; try easy ; try inversion H0.
  - (* inductive case *)
    apply Field_theory.if_true in H0; destruct H0.
    f_equal.
    (* show heads are equal *)
    + apply (proj1 (eqb_leibniz a a0) H0).
    (* show tails are equal using induction hypothesis *)
    + apply IHl1. assumption.
  - rewrite eqb_refl.
    apply list_eqdec_refl.
Qed.

Global Instance List_eqdec {A} `{EqDec A} : EqDec (list A) := {
    eqb := list_eqdec;
    eqb_leibniz := list_eqdec_sound;
  }.

Global Program Instance Dec_eq_prod (A B : Type) `{EqDec A} `{EqDec B} : EqDec (A * B) := {
    eqb '(a0, b0) '(a1, b1) := andb (eqb a0 a1) (eqb b0 b1)
  }.
Next Obligation.
  split ; intros ; destruct x ; destruct y.
  - unfold is_true in H1. 
    symmetry in H1.
    apply Bool.andb_true_eq in H1. destruct H1.
    symmetry in H1. rewrite (eqb_leibniz) in H1.
    symmetry in H2. rewrite (eqb_leibniz) in H2.
    rewrite H1. rewrite H2. reflexivity.
  - inversion_clear H1. now do 2 rewrite eqb_refl.
Defined.

(*** Be Bytes *)


Fixpoint nat_be_range_at_position (k : nat) (z : Z) (n : Z) : list bool :=
  match k with
  | O => []
  | S k' => Z.testbit z (n + k') :: nat_be_range_at_position k' z n
  end.

Fixpoint nat_be_range_to_position_ (z : list bool) (val : Z) : Z :=
  match z with
  | [] => val
  | x :: xs => nat_be_range_to_position_ xs ((if x then 2 ^ List.length xs else 0) + val)
  end.

Definition nat_be_range_to_position (k : nat) (z : list bool) (n : Z) : Z :=
  (nat_be_range_to_position_ z 0 * 2^(k * n)).

Definition nat_be_range (k : nat) (z : Z) (n : nat) : Z :=
  nat_be_range_to_position_ (nat_be_range_at_position k z (n * k)) 0. (* * 2^(k * n) *)

Compute nat_be_range 4 0 300.

Definition u64_to_be_bytes' : int64 -> nseq int8 8 :=
  fun k => array_from_list (int8) [@nat_to_int U8 (nat_be_range 4 k 7) ;
                                   @nat_to_int U8(nat_be_range 4 k 6) ;
                                   @nat_to_int U8 (nat_be_range 4 k 5) ;
                                   @nat_to_int U8 (nat_be_range 4 k 4) ;
                                   @nat_to_int U8 (nat_be_range 4 k 3) ;
                                   @nat_to_int U8 (nat_be_range 4 k 2) ;
                                   @nat_to_int U8 (nat_be_range 4 k 1) ;
                                   @nat_to_int U8 (nat_be_range 4 k 0)].



Definition u64_from_be_bytes_fold_fun (i : int8) (s : nat_ChoiceEquality '× int64) : nat_ChoiceEquality '× int64 :=
  let (n,v) := s in
  (S n, v .+ (@repr U64 ((int8_to_nat i) * 2 ^ (4 * n)))).

Definition u64_from_be_bytes' : nseq int8 8 -> int64 :=
   (fun v => snd (List.fold_right u64_from_be_bytes_fold_fun (0%nat, @repr U64 0) (array_to_list v))).

Definition u64_to_be_bytes : int64 -> nseq int8 8 := u64_to_be_bytes'.
Definition u64_from_be_bytes : nseq int8 8 -> int64 := u64_from_be_bytes'.

(* Definition nat_mod_to_byte_seq_be : forall {n : Z}, nat_mod n -> seq int8 := *)
(*   fun k => VectorDef.of_list . *)

(*** Result *)

#[global] #[refine] Instance result (b a : ChoiceEquality) : ChoiceEquality :=
  {| ct := chSum a b ; T := (a + b)%type |}.
Proof.
  intros.
  cbn.
  do 2 rewrite ChoiceEq.
  reflexivity.
Defined.

Definition Ok {a b : ChoiceEquality} : a -> result b a := @inl a b.
Definition Err {a b : ChoiceEquality} : b -> result b a := @inr a b.

Arguments Ok {_ _}.
Arguments Err {_ _}.

Definition result_unwrap_safe {a b} (x : result b a) `{match x with inl _ => True | inr _ => False end} : a.
  destruct x.
  apply t.
  contradiction.
Defined.
Axiom falso : False. Ltac admit_falso := destruct falso.
Definition result_unwrap {a b} (x : result b a) : a :=
  result_unwrap_safe x (H := ltac:(admit_falso)).

Program Definition option_ChoiceEquality (a : ChoiceEquality) :=
  {| ct := chOption a ; T := option a ; |}.
Next Obligation.
  intros.
  rewrite ChoiceEq.
  reflexivity.
Qed.

(*** TODO: implement or replace *)

(*** Monad / Bind *)

Module ChoiceEqualityMonad.
  Class CEMonad (M : ChoiceEquality -> ChoiceEquality) : Type :=
    {
      bind {A B : ChoiceEquality} (x : M A) (f : A -> M B) : M B ;
      ret {A : ChoiceEquality} (x : A) : M A ;

      (* bind_ret : forall {A B : ChoiceEquality} (x : A) (f : A -> M B), bind (ret x) f = f x ; *)
      (* ret_bind : forall {A : ChoiceEquality} (x : M A) , bind x ret = x ; *)
      (* bind_cong : forall {A B C : ChoiceEquality} (x : M A) (f : A -> M B) (g : B -> M C), *)
      (*   bind (bind x f) g = bind x (fun x => bind (f x) g) ; *)
    }. 
  
  Class CEMonad2 (M : ChoiceEquality -> ChoiceEquality) : Type :=
    {
      unit {A : ChoiceEquality} (x : A) : M A ;
      fmap {A B : ChoiceEquality} (f : A -> B) (x : M A) : M B ;
      join {A : ChoiceEquality} (x : M (M A)) : M A ;
    }.

  #[global] Instance CEMonadToCEMonad2 `{CEMonad} : CEMonad2 M :=
    {|
      unit A := @ret M _ A ;
      fmap A B f x := bind x (fun y => ret (f y)) ;
      join A x := bind x id
    |}.

  #[global] Instance CEMonad2ToCEMonad `{CEMonad2} : CEMonad M :=
    {|
      ret A := @unit M _ A ;
      bind A B x f := join (fmap f x)
    |}.

  Class CEMonad_prod (M M0 : ChoiceEquality -> ChoiceEquality) :=
    { prod : forall A, M0 (M (M0 A)) -> M (M0 A) }.
  
  #[global] Program Instance ComposeProd2 `{CEMonad2} `{CEMonad2} `{@CEMonad_prod M M0} : CEMonad2 (fun x => M (M0 x)) :=
    {|
      unit A x := unit (A := M0 A) (unit x) ;
      fmap A B f x := fmap (A := M0 A) (B := M0 B) (fmap f) x ;
      join A x := join (A := M0 A) (fmap (@prod M M0 _ A) x)
    |}.

  #[global] Instance ComposeProd `{CEMonad} `{CEMonad} `(@CEMonad_prod M M0) : CEMonad (fun x => M (M0 x)) := (@CEMonad2ToCEMonad _ ComposeProd2).
  
  Definition bind_prod `{CEMonad} `{CEMonad} `{@CEMonad_prod M M0}
             {A B} (x : M (M0 A)) (f : A -> M (M0 B))
    : M (M0 B) :=
    (* bind x (fun y => @prod M M0 _ B (bind y (fun y => ret (f y)))). *)
    (@bind (fun x => M (M0 x)) (ComposeProd _) A B x f).


  Class CEMonad_swap (M M0 : ChoiceEquality -> ChoiceEquality) :=
    { swap : forall A, M0 (M A) -> M (M0 A) }.
  
  #[global] Program Instance ComposeSwap2 `{CEMonad2 } `{CEMonad2} `{@CEMonad_swap M M0} : CEMonad2 (fun x => M (M0 x)) :=
    {|
      unit A x := unit (A := M0 A) (unit x) ;
      fmap A B f x := fmap (A := M0 A) (B := M0 B) (fmap f) x ;
      join A x := fmap (join (M := M0)) (join (fmap (@swap M M0 _ (M0 A)) x))
    |}.

  #[global] Instance ComposeSwap `{CEMonad} `{CEMonad} `(@CEMonad_swap M M0) : CEMonad (fun x => M (M0 x)) := (@CEMonad2ToCEMonad _ ComposeSwap2).

  Definition bind_swap `{CEMonad} `{CEMonad} `{@CEMonad_swap M M0}
             A B (x : M (M0 A)) (f : A -> M (M0 B)) : M (M0 B) :=
    (@bind _ (@ComposeSwap M _ M0 _ _) A B x f).
  
  
  Section ResultMonad.
    Definition result_bind {C A B} (r : result C A) (f : A -> result C B) : result C B :=
      match r with
      | inl a => f a
      | inr e => (@Err B C e)
      end.

    Definition result_ret {C A : ChoiceEquality} (a : A) : result C A := Ok a.
    
    Global Instance result_monad {C : ChoiceEquality} : CEMonad (result C) :=
      {|  (* (@result_bind C) (@result_ret C) *)
        bind := (@result_bind C) ;
        ret := (@result_ret C) ;
      |}.
    
    Arguments result_monad {_} &.

    
    
    (* Existing Instance result_monad. *)

    
  End ResultMonad.


  
  Definition option_bind {A B} (r : option A) (f : A -> option B) : option B :=
    match r with
      Some (a) => f a
    | None => None
    end.

  Definition option_ret {A} (a : A) : option A := Some a.

  Global Instance option_monad : CEMonad option_ChoiceEquality :=
    Build_CEMonad option_ChoiceEquality (@option_bind) (@option_ret).

  Definition option_is_none {A} (x : option A) : bool :=
    match x with
    | None => true
    | _ => false
    end.

End ChoiceEqualityMonad.

#[global] Notation "x 'm(' v ')' ⇠ c1 ;; c2" :=
  (ChoiceEqualityMonad.bind (M := v) c1 (fun x => c2))
    (at level 100, c1 at next level, right associativity,
      format "x  'm(' v ')'  ⇠  c1  ;;  '//' c2")
    : hacspec_scope.

#[global] Notation " ' x 'm(' v ')' ⇠ c1 ;; c2" :=
  (ChoiceEqualityMonad.bind (M := v) c1 (fun x => c2))
    (at level 100, c1 at next level, x pattern, right associativity,
      format " ' x  'm(' v ')'  ⇠  c1  ;;  '//' c2")
    : hacspec_scope.

Definition foldi_bind {A : ChoiceEquality} `{ChoiceEqualityMonad.CEMonad} (a : uint_size) (b : uint_size) (f : uint_size -> A -> M A) (init : M A) : M A :=
  @foldi (M A) a b init (fun x y => ChoiceEqualityMonad.bind y (f x)).

(*** Notation *)

Notation "'ifbnd' b 'then' x 'else' y '>>' f" := (if b then f x else f y) (at level 200) : hacspec_scope.
Notation "'ifbnd' b 'thenbnd' x 'else' y '>>' f" := (if b then (ChoiceEqualityMonad.bind x) f else f y) (at level 200) : hacspec_scope.
Notation "'ifbnd' b 'then' x 'elsebnd' y '>>' f" := (if b then f x else (ChoiceEqualityMonad.bind y) f) (at level 200) : hacspec_scope.
Notation "'ifbnd' b 'thenbnd' x 'elsebnd' y '>>' f" := (if b then ChoiceEqualityMonad.bind x f else ChoiceEqualityMonad.bind y f) (at level 200).

Notation "'foldibnd' s 'to' e 'M(' v ')' 'for' z '>>' f" :=
  (Hacspec_Lib_Pre.foldi s e (ChoiceEqualityMonad.ret z) (fun x y => ChoiceEqualityMonad.bind (M := v) y (f x))) (at level 50) : hacspec_scope.

Axiom nat_mod_from_byte_seq_be : forall  {A n}, seq A -> nat_mod n.

(*** Default *)

(* Default instances for common types *)
Global Instance nat_default : Default nat := {
    default := 0%nat
  }.
Global Instance N_default : Default N := {
    default := 0%N
  }.
Global Instance Z_default : Default Z := {
    default := 0%Z
  }.
Global Instance uint_size_default : Default uint_size := {
    default := zero
  }.
Global Instance int_size_default : Default int_size := {
    default := zero
  }.
Global Instance int_default {WS : wsize} : Default (@int WS) := {
    default := repr 0
  }.
Global Instance uint8_default : Default uint8 := _.
Global Instance nat_mod_default {p : Z} : Default (nat_mod p) := {
    default := nat_mod_zero
  }.
Global Instance prod_default {A B : ChoiceEquality} `{Default A} `{Default B} : Default (A '× B) := {
    default := (default, default)
  }.

