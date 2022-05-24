Global Set Warnings "-ambiguous-paths".
Global Set Warnings "-uniform-inheritance".
Global Set Warnings "-auto-template".
Global Set Warnings "-disj-pattern-notation".

From mathcomp Require Import (* choice  *)fintype.

From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset fmap.

(*** Integers *)
From Coq Require Import ZArith List.
Import List.ListNotations.
(* Require Import IntTypes. *)

Require Import Lia.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Sumbool.

Declare Scope hacspec_scope.

From CoqWord Require Import ssrZ word.
From Jasmin Require Import word.

Require Import ChoiceEquality.
Require Import LocationUtility.
Require Import Hacspec_Lib_Comparable.
Require Import Hacspec_Lib_Pre.

Open Scope bool_scope.
Open Scope hacspec_scope.
Open Scope nat_scope.
Open Scope list_scope.

Definition secret : forall {WS : wsize},  (@T (@int WS)) -> both fset.fset0 [interface] (@int WS) := fun {WS} x => lift_to_both (secret x).

(* Definition secret {WS : wsize} (x : @int WS) : *)
(*   both (fset.fset0) (@int WS) := lift_to_both (secret x). *)

Section Uint.
  Definition uint8_declassify (n : int8) : both fset.fset0 [interface] int8 :=
    lift_to_both (uint8_declassify n).
  Definition int8_declassify (n : int8) : both fset.fset0 [interface] int8 :=
    lift_to_both (int8_declassify n).
  Definition uint16_declassify (n : int16) : both fset.fset0 [interface] int16 :=
    lift_to_both (uint16_declassify n).
  Definition int16_declassify (n : int16) : both fset.fset0 [interface] int16 :=
    lift_to_both (int16_declassify n).
  Definition uint32_declassify (n : int32) : both fset.fset0 [interface] int32 :=
    lift_to_both (uint32_declassify n).
  Definition int32_declassify (n : int32) : both fset.fset0 [interface] int32 :=
    lift_to_both (int32_declassify n).
  Definition uint64_declassify (n : int64) : both fset.fset0 [interface] int64 :=
    lift_to_both (uint64_declassify n).
  Definition int64_declassify (n : int64) : both fset.fset0 [interface] int64 :=
    lift_to_both (int64_declassify n).
  Definition uint128_declassify (n : int128) : both fset.fset0 [interface] int128 :=
    lift_to_both (uint128_declassify n).
  Definition int128_declassify (n : int128) : both fset.fset0 [interface] int128 :=
    lift_to_both (int128_declassify n).

  Definition uint8_classify (n : int8) : both fset.fset0 [interface] int8 :=
    lift_to_both (uint8_classify n).
  Definition int8_classify (n : int8) : both fset.fset0 [interface] int8 :=
    lift_to_both (int8_classify n).
  Definition uint16_classify (n : int16) : both fset.fset0 [interface] int16 :=
    lift_to_both (uint16_classify n).
  Definition int16_classify (n : int16) : both fset.fset0 [interface] int16 :=
    lift_to_both (int16_classify n).
  Definition uint32_classify (n : int32) : both fset.fset0 [interface] int32 :=
    lift_to_both (uint32_classify n).
  Definition int32_classify (n : int32) : both fset.fset0 [interface] int32 :=
    lift_to_both (int32_classify n).
  Definition uint64_classify (n : int64) : both fset.fset0 [interface] int64 :=
    lift_to_both (uint64_classify n).
  Definition int64_classify (n : int64) : both fset.fset0 [interface] int64 :=
    lift_to_both (int64_classify n).
  Definition uint128_classify (n : int128) : both fset.fset0 [interface] int128 :=
    lift_to_both (uint128_classify n).
  Definition int128_classify (n : int128) : both fset.fset0 [interface] int128 :=
    lift_to_both (int128_classify n).


  (* CompCert integers' signedness is only interpreted through 'signed' and 'unsigned',
   and not in the representation. Therefore, uints are just names for their respective ints.
   *)

  Definition declassify_usize_from_uint8 (n : uint8) : both fset.fset0 [interface] uint_size :=
    lift_to_both (declassify_usize_from_uint8 n).

(**** Operations *)

(* Should maybe use size of s instead? *)
Definition uint8_rotate_left (u: int8) (s: int8) : int8 := rol u s.
Definition uint8_rotate_right (u: int8) (s: int8) : int8 := ror u s.

Definition uint16_rotate_left (u: int16) (s: int16) : int16 := rol u s.
Definition uint16_rotate_right (u: int16) (s: int16) : int16 := ror u s.

Definition uint32_rotate_left (u: int32) (s: int32) : int32 := rol u s.
Definition uint32_rotate_right (u: int32) (s: int32) : int32 := ror u s.

Definition uint64_rotate_left (u: int64) (s: int64) : int64 := rol u s.
Definition uint64_rotate_right (u: int64) (s: int64) : int64 := ror u s.

Definition uint128_rotate_left (u: int128) (s: int128) : int128 := rol u s.
Definition uint128_rotate_right (u: int128) (s: int128) : int128 := ror u s.

Definition pub_uint128_wrapping_add (x y: int128) : int128 := x .+ y.

End Uint.
  
(*** Loops *)

Section Loops.

  Fixpoint foldi_
           {acc : ChoiceEquality}
           (fuel : nat)
           (i : @T uint_size)
           {L I}
           (f: (@T uint_size) -> @T acc -> code L I (@ct acc))
           (cur : @T acc) {struct fuel} : raw_code (@ct acc) :=
    match fuel with
    | O => ret cur
    | S n' =>
        cur' ← f i cur ;;
        foldi_ n' (i .+ one) f (ct_T cur')
    end.

  Lemma valid_foldi_ :
    forall {acc : ChoiceEquality} L I n i (f : @T uint_size -> @T acc -> code L I (@ct acc)) init,
      ValidCode L I (foldi_ n i f init).
  Proof.
    induction n ; intros ; cbn ; ssprove_valid.
    apply f.
  Qed.
  
  Definition foldi_pre
             {acc: ChoiceEquality}
             (lo: @T uint_size)
             (hi: @T uint_size) (* {lo <= hi} *)
             {I L}
             (f: (@T uint_size) -> @T acc -> code I L (@ct acc)) (* {i < hi} *)
             (* {fset_init : _} *)
             (init: @T acc) : raw_code (@ct acc) :=
    match Z.sub (unsigned hi) (unsigned lo) with
    | Z0 => ret (T_ct init)
    | Zneg p => ret (T_ct init)
    | Zpos p => foldi_ (Pos.to_nat p) lo f init
    end.

  (* Fold done using natural numbers for bounds *)
  Fixpoint foldi_nat_
           {acc : ChoiceEquality}
           (fuel : nat)
           (i : nat)
           (f : nat -> @T acc -> raw_code (@ct acc))
           (cur : @T acc) : raw_code (@ct acc) :=
    match fuel with
    | O => ret (T_ct cur)
    | S n' =>
        cur' ← f i cur ;;
        foldi_nat_ n' (S i) f (ct_T cur')
    end.
  Definition foldi_nat
             {acc: ChoiceEquality}
             (lo: nat)
             (hi: nat) (* {lo <= hi} *)
             (f: nat -> @T acc -> raw_code (@ct acc)) (* {i < hi} *)
             (init: @T acc) : raw_code (@ct acc) :=
    match Nat.sub hi lo with
    | O => ret (T_ct init)
    | S n' => foldi_nat_ (S n') lo f init
    end.

  Lemma foldi__move_S :
    forall {acc: ChoiceEquality}
      (fuel : nat)
      (i : @T uint_size)
      {L I}
      (f : @T uint_size -> @T acc -> code L I (@ct acc))
      (cur : @T acc),
      (cur' ← f i cur ;; foldi_ fuel (i .+ one) f (ct_T cur')) = foldi_ (S fuel) i f cur.
  Proof. reflexivity. Qed.

  Lemma foldi__nat_move_S :
    forall {acc: ChoiceEquality}
      (fuel : nat)
      (i : nat)
      (f : nat -> @T acc -> raw_code (@ct acc))
      (cur : @T acc),
      (cur' ← f i cur ;; foldi_nat_ fuel (S i) f (ct_T cur')) = foldi_nat_ (S fuel) i f cur.
  Proof. reflexivity. Qed.

  Lemma foldi__nat_move_S_append :
    forall {acc: ChoiceEquality}
      (fuel : nat)
      (i : nat)
      (f : nat -> @T acc -> raw_code (@ct acc))
      (cur : @T acc),
      (cur' ← foldi_nat_ fuel i f (cur) ;; f (i + fuel) (ct_T cur')) = foldi_nat_ (S fuel) i f cur.
  Proof.
    (* Set Printing Coercions. *)
    induction fuel ; intros.
    - rewrite <- foldi__nat_move_S.
      unfold foldi_nat_.
      replace (fun cur' => ret (T_ct (ct_T cur'))) with (fun cur' => @ret acc cur').
      2: {
        apply functional_extensionality.
        intros. now rewrite T_ct_id.
      }
      rewrite bind_ret.
      unfold bind at 1.
      rewrite ct_T_id.
      rewrite Nat.add_0_r.
      reflexivity.
    - rewrite <- foldi__nat_move_S.      
      rewrite <- foldi__nat_move_S.      
      rewrite bind_assoc.
      f_equal.
      apply functional_extensionality.
      intros.
      replace (i + S fuel) with (S i + fuel) by lia.
      rewrite IHfuel.
      reflexivity.
  Qed.

  Lemma foldi__nat_move_to_function :
    forall {acc: ChoiceEquality}
      (fuel : nat)
      (i : nat)
      (f : nat -> @T acc -> raw_code (@ct acc))
      (cur : @T acc),
      foldi_nat_ fuel i (fun x => f (S x)) (cur) = foldi_nat_ fuel (S i) f cur.
  Proof.
    induction fuel ; intros.
    - reflexivity.
    - cbn.
      f_equal.
      apply functional_extensionality.
      intros.
      rewrite IHfuel.
      reflexivity.
  Qed.
  
  Lemma foldi__nat_move_to_function_add :
    forall {acc: ChoiceEquality}
      (fuel : nat)
      (i j : nat)
      (f : nat -> @T acc -> raw_code (@ct acc))
      (cur : @T acc),
      foldi_nat_ fuel i (fun x => f (x + j)) (cur) = foldi_nat_ fuel (i + j) f cur.
  Proof.
    intros acc fuel i j. generalize dependent i.
    induction j ; intros.
    - rewrite Nat.add_0_r.
      replace (fun x : nat => f (x + 0)) with f.
      reflexivity.
      apply functional_extensionality.
      intros.
      now rewrite Nat.add_0_r.
    - replace (i + S j) with (S i + j) by lia.
      rewrite <- IHj.
      rewrite <- foldi__nat_move_to_function.
      f_equal.
      apply functional_extensionality.
      intros.
      f_equal.
      lia.            
  Qed.      
  
  Lemma raw_code_type_from_choice_type_id :
    forall (acc : ChoiceEquality) (x : raw_code (@ct acc)),
      (cur' ← x ;;
       ret (T_ct (ct_T cur')))
      =
        x.
  Proof.
    intros.
    rewrite @bind_cong with (v := x) (g := @ret (@ct acc)).
    rewrite bind_ret.
    reflexivity.
    reflexivity.

    apply functional_extensionality.
    intros.

    rewrite T_ct_id.
    reflexivity.  
  Qed.
  
  (* You can do one iteration of the fold by burning a unit of fuel *)
  Lemma foldi__move_S_fuel :
    forall {acc: ChoiceEquality}
      (fuel : nat)
      (i : @T uint_size)
      {L I}
      (f : @T uint_size -> @T acc -> code L I (@ct acc))
      (cur : @T acc),
      (0 <= Z.of_nat fuel <= @wmax_unsigned U32)%Z ->
      (cur' ← foldi_ fuel i f cur ;;
       f ((repr (Z.of_nat fuel)) .+ i) (ct_T cur')
      ) = foldi_ (S (fuel)) i f cur.
  Proof.
    intros acc fuel.
    induction fuel ; intros.
    - cbn.
      replace (repr 0) with (@zero U32) by (apply word_ext ; reflexivity).
      unfold ".+".
      rewrite add0w.
      
      rewrite ct_T_id.
      rewrite raw_code_type_from_choice_type_id.
      reflexivity.
    - unfold foldi_.
      fold (@foldi_ acc fuel).
      rewrite bind_assoc.

      f_equal.
      apply functional_extensionality.
      intros.

      specialize (IHfuel (i .+ one) L I f (ct_T x)).

      replace ((repr (Z.of_nat (S fuel))) .+ i)
        with ((repr (Z.of_nat fuel)) .+ (i .+ one)).
      2 : {
        unfold ".+".
        rewrite <- addwC.
        rewrite <- addwA.
        rewrite addwC.
        f_equal.
        apply word_ext.
        rewrite Z.add_1_l.
        rewrite Nat2Z.inj_succ.
        f_equal.
        f_equal.
        apply Zmod_small.
        unfold wmax_unsigned in H.
        unfold wbase in H.
        lia.
      }

      rewrite IHfuel.
      reflexivity.    
      lia.
  Qed.

  (* You can do one iteration of the fold by burning a unit of fuel *)
  Lemma foldi__nat_move_S_fuel :
    forall {acc: ChoiceEquality}
      (fuel : nat)
      (i : nat)
      (f : nat -> @T acc -> raw_code (@ct acc))
      (cur : @T acc),
      (0 <= Z.of_nat fuel <= @wmax_unsigned U32)%Z ->
      (cur' ← foldi_nat_ fuel i f cur ;; f (fuel + i)%nat (ct_T cur')) = foldi_nat_ (S fuel) i f cur.
  Proof.
    induction fuel ; intros.
    - cbn.
      rewrite ct_T_id.
      rewrite raw_code_type_from_choice_type_id.
      reflexivity.
    - unfold foldi_nat_.
      fold (@foldi_nat_ acc fuel).
      rewrite bind_assoc.
      f_equal.
      apply functional_extensionality.
      intros.
      replace (S fuel + i)%nat with (fuel + (S i))%nat by (symmetry ; apply plus_Snm_nSm).
      rewrite IHfuel.
      + reflexivity.
      + lia.
  Qed.

  (* folds and natural number folds compute the same thing *)
  Lemma foldi_to_foldi_nat :
    forall {acc: ChoiceEquality}
      (lo: @T uint_size) (* {lo <= hi} *)
      (hi: @T uint_size) (* {lo <= hi} *)
      {L I}
      (f: (@T uint_size) -> @T acc -> code L I (@ct acc)) (* {i < hi} *)
      (init: @T acc),
      (unsigned lo <= unsigned hi)%Z ->
      foldi_pre lo hi f init = foldi_nat (Z.to_nat (unsigned lo)) (Z.to_nat (unsigned hi)) (fun x => f (repr (Z.of_nat x))) init.
  Proof.
    intros.

    unfold foldi_pre.
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
        replace (repr 0) with (@zero U32) by (apply word_ext ; reflexivity).
        unfold int_add.
        rewrite add0w.
        reflexivity.
      + assert (H_bound_pred: (Z.pred 0 < Z.pos (Pos.of_succ_nat n) < @modulus U32)%Z) by lia.
        rewrite <- (IHn H_bound_pred) ; clear IHn.
        f_equal.
        * cbn in *.
          rewrite foldi__move_S.
          f_equal.
          lia.
        * apply functional_extensionality.
          intros.

          enough ((@int_add U32 (@repr U32 (Z.of_nat (S n))) (@repr U32 (Z.of_nat lo_n))) = (@repr U32 (Z.of_nat (Init.Nat.add (S n) lo_n)))).
          rewrite H0. reflexivity.
          (* f_equal. *)
          
          apply word_ext.

          replace (urepr (repr (Z.of_nat (S n)))) with (@unsigned U32 (repr (Z.of_nat (S n)))) by reflexivity.
          replace (urepr (repr (Z.of_nat lo_n))) with (@unsigned U32 (repr (Z.of_nat lo_n))) by reflexivity.

          do 2 rewrite unsigned_repr_alt by lia.
          rewrite Nat2Z.inj_add.
          reflexivity.        
  Qed.

  Lemma foldi_nat_to_foldi :
    forall {acc: ChoiceEquality}
      (lo: nat) (* {lo <= hi} *)
      (hi: nat) (* {lo <= hi} *)
      {L I}
      (f: nat -> @T acc -> code L I (@ct acc)) (* {i < hi} *)
      (init: @T acc),
      (lo <= hi) ->
      (Z.of_nat hi < @modulus U32)%Z ->
      (forall x, f x = f (from_uint_size (repr (Z.of_nat x)))) ->
      foldi_nat lo hi f init =
        foldi_pre (usize lo) (usize hi) (fun x => f (from_uint_size x)) init.
  Proof.
    intros.
    rewrite foldi_to_foldi_nat.
    2: {
      unfold nat_uint_sizable.
      unfold usize.

      do 2 rewrite wunsigned_repr.
      rewrite Zmod_small by (split ; [ lia | apply Z.le_lt_trans with (m := Z.of_nat hi) ; try apply inj_le ; assumption ]).
      rewrite Zmod_small by (split ; try easy ; lia).
      lia.
    }

    unfold nat_uint_sizable.
    unfold usize.

    do 2 rewrite wunsigned_repr.
    rewrite Zmod_small by (split ; [ lia | apply Z.le_lt_trans with (m := Z.of_nat hi) ; try apply inj_le ; assumption ]).
    rewrite Zmod_small by (split ; try easy ; lia).
    do 2 rewrite Nat2Z.id.
    
    f_equal.
    apply functional_extensionality. intros.    
    rewrite <- H1.
    reflexivity.    
  Qed.
        
  (* folds can be computed by doing one iteration and incrementing the lower bound *)
  Lemma foldi_nat_split_S :
    forall {acc: ChoiceEquality}
      (lo: nat)
      (hi: nat) (* {lo <= hi} *)
      (f: nat -> @T acc -> raw_code (@ct acc)) (* {i < hi} *)
      (init: @T acc),
      (lo < hi)%nat ->
      foldi_nat lo hi f init = (cur' ← foldi_nat lo (S lo) f init ;; foldi_nat (S lo) hi f (ct_T cur')).
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

      (* unfold foldi_nat_. *)
      rewrite raw_code_type_from_choice_type_id.
      reflexivity.
    - apply Nat.eqb_neq in hi_eq_lo.
      apply Nat.lt_gt_cases in hi_eq_lo.
      destruct hi_eq_lo.
      + lia.
      + rewrite (Nat.sub_succ_l (S lo)) by apply (Nat.lt_le_pred _ _ H0).
        rewrite Nat.sub_succ_l by apply (Nat.lt_le_pred _ _ H).
        replace ((S (hi - S lo))) with (hi - lo)%nat by lia.

        unfold foldi_nat_.
        fold (@foldi_nat_ acc).
        rewrite raw_code_type_from_choice_type_id.
        reflexivity.
  Qed.

  (* folds can be split at some valid offset from lower bound *)
  Lemma foldi_nat_split_add :
    forall (k : nat),
    forall {acc: ChoiceEquality}
      (lo: nat)
      (hi: nat) (* {lo <= hi} *)
      (f: nat -> @T acc -> raw_code (@ct acc)) (* {i < hi} *)
      (init: @T acc),
    forall {guarantee: (lo + k <= hi)%nat},
      foldi_nat lo hi f init = (cur' ← foldi_nat lo (k + lo) f init ;; foldi_nat (k + lo) hi f (ct_T cur')).
  Proof.
    induction k ; intros.
    - cbn.
      unfold foldi_nat.
      rewrite Nat.sub_diag.
      cbn.
      rewrite ct_T_id.
      reflexivity.
    - rewrite foldi_nat_split_S by lia.
      replace (S k + lo)%nat with (k + S lo)%nat by lia.
      specialize (IHk acc (S lo) hi f).

      rewrite bind_cong with (v := foldi_nat lo (S lo) (fun (x : nat) (x0 : @T acc) => f x x0) init) (g := fun v => (cur' ← foldi_nat (S lo) (k + S lo) (fun (x : nat) (x0 : @T acc) => f x x0) (ct_T v) ;;
                                                                                                             foldi_nat (k + S lo) hi (fun (x : nat) (x0 : @T acc) => f x x0)
                                                                                                                       (ct_T cur'))).

      rewrite <- bind_assoc.
      f_equal.
      
      rewrite <- foldi_nat_split_S by lia.
      reflexivity.
      
      reflexivity.

      apply functional_extensionality. intros. rewrite IHk by lia. reflexivity.
  Qed.

  (* folds can be split at some midpoint *)
  Lemma foldi_nat_split :
    forall (mid : nat), (* {lo <= mid <= hi} *)
    forall {acc: ChoiceEquality}
      (lo: nat)
      (hi: nat) (* {lo <= hi} *)
      (f: nat -> @T acc -> raw_code (@ct acc)) (* {i < hi} *)
      (init: @T acc),
    forall {guarantee: (lo <= mid <= hi)%nat},
      foldi_nat lo hi f init = (cur' ← foldi_nat lo mid f init ;; foldi_nat mid hi f (ct_T cur')).
  Proof.
    intros.
    assert (mid_is_low_plus_constant : {k : nat | (mid = lo + k)%nat})  by (exists (mid - lo)%nat ; lia).  
    destruct mid_is_low_plus_constant ; subst.
    rewrite Nat.add_comm.
    pose foldi_nat_split_add.
    apply foldi_nat_split_add.
    apply guarantee.
  Qed.

  (* folds can be split at some midpoint *)
  Lemma foldi_split :
    forall (mid : @T uint_size), (* {lo <= mid <= hi} *)
    forall {acc: ChoiceEquality}
      (lo: @T uint_size)
      (hi: @T uint_size) (* {lo <= hi} *)
      {L I}
      (f: @T uint_size -> @T acc -> code L I (@ct acc)) (* {i < hi} *)
      (init: @T acc),
    forall {guarantee: (unsigned lo <= unsigned mid <= unsigned hi)%Z},
      foldi_pre lo hi f init = (cur' ← foldi_pre lo mid f init ;; foldi_pre mid hi f (ct_T cur')).
  Proof.
    intros.
    rewrite foldi_to_foldi_nat by lia.
    rewrite foldi_to_foldi_nat by lia.

    pose @foldi_to_foldi_nat.
    
    rewrite bind_cong with (v := foldi_nat (Z.to_nat (unsigned lo)) (Z.to_nat (unsigned mid))
                                           (fun x : nat => f (repr (Z.of_nat x))) init) (g := fun init => foldi_nat (Z.to_nat (unsigned mid)) (Z.to_nat (unsigned hi))
                                                                                                            (fun x : nat => f (repr (Z.of_nat x))) (ct_T init)). 

    apply foldi_nat_split ; lia.
    reflexivity.
    apply functional_extensionality.
    intros.
    
    rewrite foldi_to_foldi_nat by lia.
    reflexivity.
  Qed.


  Lemma valid_foldi_pre :
    forall {acc : ChoiceEquality} (lo hi : int_type) {L : {fset Location}} {I : Interface} (f : int_type -> T -> code L I ct),
      forall init : T,
        ValidCode L I (foldi_pre lo hi f init).
  Proof.
    intros.
    unfold foldi_pre.
    destruct (unsigned hi - unsigned lo)%Z.
    - ssprove_valid.
    - apply valid_foldi_.
    - ssprove_valid.
  Qed.

  Definition foldi
             {acc: ChoiceEquality}
             (lo: @T uint_size)
             (hi: @T uint_size) (* {lo <= hi} *)
             {L}
             {I}
             (f: (@T uint_size) -> @T acc -> code L I (@ct acc))
             (init: @T acc)
    :
    code L I (@ct acc) :=
    {| prog := foldi_pre lo hi f init;
                     prog_valid := @valid_foldi_pre acc lo hi L I f init |}.

  (* Global Arguments foldi {_} _ _ {_} {_} {_} _ _ {_} {_}. *)

  Lemma valid_remove_back :
    forall x xs I {ct} c,
      ValidCode (fset xs) I c ->
      @ValidCode (fset (xs ++ [x])) I ct c.
  Proof.
    intros.
    apply (@valid_injectLocations) with (L1 := fset xs).
    - (* replace (x :: xs) with (seq.cat [x] xs) by reflexivity. *)
      rewrite fset_cat.
      apply fsubsetUl.    
    - apply H.
  Qed.  

  Lemma list_constructor : forall {A : Type} (x : A) (xs : list A) (l : list A) (H : (x :: xs) = l), (l <> []).
  Proof.
    intros.
    subst.
    easy.
  Qed.

  Definition pop_back {A : Type} (l : list A) :=
    match (rev l) with
    | [] => []
    | (x :: xs) => rev xs ++ [x]
    end.

  Theorem pop_back_ignore_front : forall {A} (a : A) (l : list A), pop_back (a :: l) = a :: pop_back l.
  Proof.
    intros.
    induction l ; intros.
    - reflexivity.
    - unfold pop_back.
      destruct (rev (a :: a0 :: l)) eqn:orev.
      { apply f_equal with (f := @rev A) in orev.
        rewrite (rev_involutive) in orev.
        discriminate orev.
      }
      cbn in orev.

      destruct (rev (a0 :: l)) eqn:orev2.
      { apply f_equal with (f := @rev A) in orev2.
        rewrite (rev_involutive) in orev2.
        discriminate orev2.
      }
      cbn in orev2.
      rewrite orev2 in orev ; clear orev2.

      inversion_clear orev.
      rewrite rev_unit.
      reflexivity.
  Qed.
  
  Theorem pop_back_is_id : forall {A} (l : list A), l = pop_back l.
  Proof.
    intros.
    induction l.
    - reflexivity.
    - destruct l.
      + reflexivity.
      + rewrite pop_back_ignore_front.
        rewrite <- IHl.
        reflexivity.
  Qed.

  Ltac valid_remove_back' :=
    match goal with
    | _ : _ |- (ValidCode (fset (?l)) _ _) =>
        rewrite (@pop_back_is_id _ l)
    end ;
    apply valid_remove_back.


  Lemma valid_remove_front :
    forall x xs I {ct} c,
      ValidCode (fset xs) I c ->
      @ValidCode (fset (x :: xs)) I ct c.
  Proof.
    intros.
    apply (@valid_injectLocations) with (L1 := fset xs).
    - replace (x :: xs) with (seq.cat [x] xs) by reflexivity.
      rewrite fset_cat.
      apply fsubsetUr.    
    - apply H.
  Qed.

  Lemma valid_subset :
    forall xs ys I {ct} c,
      List.incl (xs) (ys) ->
      ValidCode (fset xs) I c ->
      @ValidCode (fset ys) I ct c.
  Proof.
    intros.
    apply (@valid_injectLocations) with (L1 := fset xs).
    - apply list_incl_fsubset.
      apply -> list_incl_remove_fset.
      apply H.      
    - apply H0.
  Qed.

Theorem for_loop_unfold :
  forall c n,
  for_loop (fun m : nat => c m) (S n) =
    (c 0 ;; for_loop (fun m : nat => c (S m)) (n) ).
  cbn.
  induction n ; intros.
  - reflexivity.
  - unfold for_loop ; fold for_loop.
    cbn.
    rewrite IHn.
    rewrite bind_assoc.
    reflexivity.
Qed.    

End Loops.

(*** Seq *)

Section Seqs.

  (**** Unsafe functions *)

  Definition seq_new_ {A: ChoiceEquality} (init : A) (len: nat) : both fset.fset0 [interface] (seq A) :=
    lift_to_both (seq_new_ init len).

  Definition seq_new {A: ChoiceEquality} `{Default A} (len: nat) : both fset.fset0 [interface] (seq A) :=
    lift_to_both (seq_new len).

  Definition seq_len {A: ChoiceEquality} (s: @T (seq A)) : both fset.fset0 [interface] (uint_size) := lift_to_both (seq_len s).

(**** Array manipulation *)
Definition array_new_ {A: ChoiceEquality} (init:@T A) (len: nat) :
  both fset.fset0 [interface] ((nseq A len)) :=
  lift_to_both (array_new_ init len).

Definition array_index {A: ChoiceEquality} `{Default (@T A)} {len : nat} (s: @T (nseq A len)) (i: nat) : both fset.fset0 [interface] (A) :=
  lift_to_both (array_index s i).

Definition array_upd {A: ChoiceEquality} {len : nat} (s: @T (nseq A len)) (i: nat) (new_v: @T A) : both fset.fset0 [interface] ((nseq A len)) :=
  lift_to_both (array_upd s i new_v).

(* substitutes a sequence (seq) into an array (nseq), given index interval  *)
(* Axiom update_sub : forall {A len }, nseq A len -> nat -> nat -> seq A -> t A len. *)
Definition update_sub {A : ChoiceEquality} {len slen} `{Default (@T A)} (v : @T (nseq A len)) (i : nat) (n : nat) (sub : @T (nseq A slen)) : both fset.fset0 [interface] ((nseq A len)) :=
  lift_to_both (update_sub v i n sub).

Instance array_from_seq   {a: ChoiceEquality}
 `{Default (@T a)}
  (out_len:nat)
  (input: @T (seq a)) 
  : both fset.fset0 [interface] (nseq a out_len) :=
  lift_to_both (array_from_seq out_len input). (*  : @T (nseq a out_len) *)

Instance array_to_seq {A : ChoiceEquality} {n} (f : nseq_type A n) : both fset.fset0 [interface] (seq _) := @lift_to_both (seq A) _ _ (array_to_seq f).

Definition array_from_slice
  {a: ChoiceEquality}
 `{Default (@T a)}
  (default_value: (@T a))
  (out_len: nat)
  (input: @T (seq a))
  (start: uint_size)
  (slice_len: uint_size)  : both fset.fset0 [interface] ((nseq a out_len)) :=
  lift_to_both (array_from_slice default_value out_len input (from_uint_size start) (from_uint_size slice_len)).

Definition array_slice
  {a: ChoiceEquality}
 `{Default (@T a)}
  (input: @T (seq a))
  (start: nat)
  (slice_len: nat)
  : both fset.fset0 [interface] ((nseq a slice_len)) :=
  lift_to_both (array_slice input start slice_len).

Definition array_from_slice_range
  {a: ChoiceEquality}
 `{Default (@T a)}
  (default_value: @T a)
  (out_len: nat)
  (input: @T (seq a))
  (start_fin: (@T uint_size * @T uint_size))
  : both fset.fset0 [interface] ((nseq a out_len)) :=
  lift_to_both (array_from_slice_range default_value out_len input start_fin).

Definition array_slice_range
  {a: ChoiceEquality}
 `{Default (@T a)}
  {len : nat}
  (input: @T (nseq a len))
  (start_fin:(@T uint_size * @T uint_size))
    : both fset.fset0 [interface] ((seq a)) :=
  lift_to_both (array_slice_range input start_fin).

Definition array_update
  {a: ChoiceEquality}
 `{Default (@T a)}
  {len: nat}
  (s: @T (nseq a len))
  (start : nat)
  (start_s: @T (seq a))
  : both fset.fset0 [interface] ((nseq a len)) :=
    lift_to_both (array_update s start start_s).

Definition array_update_start
  {a: ChoiceEquality}
 `{Default (@T a)}
  {len: nat}
  (s: @T (nseq a len))
  (start_s: @T (seq a))
    : both fset.fset0 [interface] ((nseq a len)) :=
    lift_to_both (array_update_start s start_s).

Definition array_len_pre  {a: ChoiceEquality} {len: nat} (s: @T (nseq a len)) := len.
(* May also come up as 'length' instead of 'len' *)
Definition array_length_pre  {a: ChoiceEquality} {len: nat} (s: @T (nseq a len)) := len.

(**** Seq manipulation *)


Definition seq_slice
  {a: ChoiceEquality}
 `{Default (@T a)}
  (s: (@T (seq a)))
  (start: nat)
  (len: nat)
    : both fset.fset0 [interface] ((nseq a _)) :=
  lift_to_both (seq_slice s start len).

Definition seq_slice_range
  {a: ChoiceEquality}
 `{Default (@T (a))}
  (input: (@T (seq a)))
  (start_fin:((@T (uint_size)) * (@T (uint_size))))
    : both fset.fset0 [interface] ((nseq a _)) :=
  lift_to_both (seq_slice_range input start_fin).

(* updating a subsequence in a sequence *)
Definition seq_update
  {a: ChoiceEquality}
 `{Default (@T (a))}
  (s: (@T (seq a)))
  (start: nat)
  (input: (@T (seq a)))
  : both fset.fset0 [interface] ((seq a)) :=
  lift_to_both (seq_update s start input).

(* updating only a single value in a sequence*)
Definition seq_upd
  {a: ChoiceEquality}
 `{Default (@T (a))}
  (s: (@T (seq a)))
  (start: nat)
  (v: (@T (a)))
  : both fset.fset0 [interface] ((seq a)) :=
  lift_to_both (seq_upd s start v).

Definition seq_update_start
  {a: ChoiceEquality}
 `{Default (@T (a))}
  (s: (@T (seq a)))
  (start_s: (@T (seq a)))
    : both fset.fset0 [interface] ((seq a)) :=
    lift_to_both (seq_update_start s start_s).

Definition array_update_slice
  {a : ChoiceEquality}
 `{Default (@T (a))}
  {l : nat}
  (out: (@T (seq a)))
  (start_out: nat)
  (input: (@T (seq a)))
  (start_in: nat)
  (len: nat)
  : both fset.fset0 [interface] ((nseq a _)) :=
  lift_to_both (array_update_slice (l := l) out start_out input start_in len).
  
Definition seq_update_slice
  {a : ChoiceEquality}
 `{Default (@T (a))}
  (out: (@T (seq a)))
  (start_out: nat)
  (input: (@T (seq a)))
  (start_in: nat)
  (len: nat)
    : both fset.fset0 [interface] ((nseq a _)) :=
  lift_to_both (seq_update_slice out start_out input start_in len).

Definition seq_concat
  {a : ChoiceEquality}
  (s1 :(@T (seq a)))
  (s2: (@T (seq a)))
  : both fset.fset0 [interface] ((seq a)) :=
   lift_to_both (seq_concat s1 s2).

Definition seq_push_pre
  {a : ChoiceEquality}
  (s1 :(@T (seq a)))
  (s2: (@T (a)))
  : both fset.fset0 [interface] ((seq a)) :=
  lift_to_both (seq_push s1 s2).

Definition seq_from_slice_range
  {a: ChoiceEquality}
 `{Default (@T (a))}
  (input: (@T (seq a)))
  (start_fin: ((@T (uint_size)) * (@T (uint_size))))
  : both fset.fset0 [interface] ((seq a)) :=
  lift_to_both (seq_from_slice_range input start_fin).

Definition seq_from_seq {A} (l : @T (seq A)) : both fset.fset0 [interface] (seq A) :=
  lift_to_both (seq_from_seq l).

(**** Chunking *)

Definition seq_num_chunks {a: ChoiceEquality} (s: (@T (seq a))) (chunk_len: nat) : both fset.fset0 [interface] (uint_size) :=
  lift_to_both (usize (seq_num_chunks s chunk_len)).

Definition seq_chunk_len
  {a: ChoiceEquality}
  (s: (@T (seq a)))
  (chunk_len: nat)
  (chunk_num: nat)
    : both fset.fset0 [interface] ((nat_ChoiceEquality)) :=
  lift_to_both (seq_chunk_len s chunk_len chunk_num).
  
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
  `{Default (@T (a))}
  (s: (@T (seq a)))
  (chunk_len: nat)
  (chunk_num: nat)
  : both fset.fset0 [interface] (((uint_size '× seq a))) :=
  lift_to_both (seq_get_chunk s chunk_len chunk_num).

Definition seq_set_chunk
  {a: ChoiceEquality}
 `{Default (@T (a))}
  (s: (@T (seq a)))
  (chunk_len: nat)
  (chunk_num: nat)
  (chunk: (@T (seq a)) ) : both fset.fset0 [interface] ((seq a)) :=
  lift_to_both (seq_set_chunk s chunk_len chunk_num chunk).


Definition seq_num_exact_chunks {a} (l : (@T (seq a))) (chunk_size : (@T (uint_size))) : (both fset.fset0 [interface] uint_size) :=
  lift_to_both (seq_num_exact_chunks l chunk_size).


(* Until #84 is fixed this returns an empty sequence if not enough *)
Definition seq_get_exact_chunk {a : ChoiceEquality} `{Default (@T (a))} (l : (@T (seq a))) (chunk_size chunk_num: (@T (uint_size))) :
  both fset.fset0 [interface] ((seq a)) :=
  lift_to_both (seq_get_exact_chunk l chunk_size chunk_num).

Definition seq_set_exact_chunk {a : ChoiceEquality} `{H : Default (@T (a))} :=
  @seq_set_chunk a H.

Definition seq_get_remainder_chunk {a : ChoiceEquality} `{Default (@T (a))} (l : @T (seq a)) (chunk_size : @T (uint_size)) : both fset.fset0 [interface] ((seq a)) :=
  lift_to_both (seq_get_remainder_chunk l chunk_size).

(**** Numeric operations *)

(* takes two nseq's and joins them using a function op : a -> a -> a *)
Definition array_join_map
  {a: ChoiceEquality}
 `{Default (@T (a))}
  {len: nat}
  (op: (@T (a)) -> (@T (a)) -> (@T (a)))
  (s1: (@T (nseq a len)))
  (s2 : (@T (nseq a len))) : both fset.fset0 [interface] ((nseq a len)) :=
  lift_to_both (array_join_map op s1 s2).
  
(* Infix "array_xor" := (array_join_map xor) (at level 33) : hacspec_scope. *)
(* Infix "array_add" := (array_join_map add) (at level 33) : hacspec_scope. *)
(* Infix "array_minus" := (array_join_map sub) (at level 33) : hacspec_scope. *)
(* Infix "array_mul" := (array_join_map mul) (at level 33) : hacspec_scope. *)
(* Infix "array_div" := (array_join_map divs) (at level 33) : hacspec_scope. *)
(* Infix "array_or" := (array_join_map or) (at level 33) : hacspec_scope. *)
(* Infix "array_and" := (array_join_map and) (at level 33) : hacspec_scope. *)


Fixpoint array_eq_
  {a: ChoiceEquality}
  {len: nat}
  (eq: (@T (a)) -> (@T (a)) -> bool)
  (s1: (@T (nseq a len)))
  (s2 : (@T (nseq a len)))
  {struct len}
  : bool.
Proof.
  destruct len ; cbn in *.
  - exact  true.
  - destruct (getm s1 (fintype.Ordinal (m := len) (ssrnat.ltnSn _))) as [s | _].
    + destruct (getm s2 (fintype.Ordinal (m := len) (ssrnat.ltnSn _))) as [s0 | _].
      * exact (eq s s0).
      * exact false.
    + exact false.
Defined.

End Seqs.


Infix "array_eq" := (array_eq_ eq) (at level 33) : hacspec_scope.
Infix "array_neq" := (fun s1 s2 => negb (array_eq_ eq s1 s2)) (at level 33) : hacspec_scope.


(**** Integers to arrays *)
Definition uint32_to_le_bytes (n : @T int32) : both fset.fset0 [interface] ((nseq int8 4)) := lift_to_both (uint32_to_le_bytes n).
Definition uint32_to_be_bytes (n : @T int32) : both fset.fset0 [interface] ((nseq int8 4)) := lift_to_both (uint32_to_be_bytes n).
Definition uint32_from_le_bytes (n : @T (nseq int8 4)) : both fset.fset0 [interface] ((int32)) := lift_to_both (uint32_from_le_bytes n).
Definition uint32_from_be_bytes (n : @T (nseq int8 4)) : both fset.fset0 [interface] ((int32)) := lift_to_both (uint32_from_be_bytes n).
Definition uint64_to_le_bytes (n : @T int64) : both fset.fset0 [interface] ((nseq int8 8)) := lift_to_both (uint64_to_le_bytes n).
Definition uint64_to_be_bytes (n : @T int64) : both fset.fset0 [interface] ((nseq int8 8)) := lift_to_both (uint64_to_be_bytes n).
Definition uint64_from_le_bytes (n : @T (nseq int8 8)) : both fset.fset0 [interface] ((int64)) := lift_to_both (uint64_from_le_bytes n).
Definition uint64_from_be_bytes (n : @T (nseq int8 8)) : both fset.fset0 [interface] ((int64)) := lift_to_both (uint64_from_be_bytes n).
Definition uint128_to_le_bytes (n : @T int128) : both fset.fset0 [interface] ((nseq int8 16)) := lift_to_both (uint128_to_le_bytes n).
Definition uint128_to_be_bytes (n : @T int128) : both fset.fset0 [interface] ((nseq int8 16)) := lift_to_both (uint128_to_be_bytes n).
Definition uint128_from_le_bytes (n : @T (nseq int8 16)) : both fset.fset0 [interface] (int128) := lift_to_both (uint128_from_le_bytes n).
Definition uint128_from_be_bytes (n : @T (nseq int8 16)) : both fset.fset0 [interface] ((int128)) := lift_to_both (uint128_from_be_bytes n).
Definition u32_to_le_bytes (n : @T int32) : both fset.fset0 [interface] ((nseq int8 4)) := lift_to_both (u32_to_le_bytes n).
Definition u32_to_be_bytes (n : @T int32) : both fset.fset0 [interface] ((nseq int8 4)) := lift_to_both (u32_to_be_bytes n).
Definition u32_from_le_bytes (n : @T (nseq int8 4)) : both fset.fset0 [interface] ((int32)) := lift_to_both (u32_from_le_bytes n).
Definition u32_from_be_bytes (n : @T (nseq int8 4)) : both fset.fset0 [interface] ((int32)) := lift_to_both (u32_from_be_bytes n).
Definition u64_to_le_bytes (n : @T int64) : both fset.fset0 [interface] ((nseq int8 8)) := lift_to_both (u64_to_le_bytes n).
Definition u64_from_le_bytes (n : @T (nseq int8 8)) : both fset.fset0 [interface] ((int64)) := lift_to_both (u64_from_le_bytes n).
Definition u128_to_le_bytes (n : @T int128) : both fset.fset0 [interface] ((nseq int8 16)) := lift_to_both (u128_to_le_bytes n).
Definition u128_to_be_bytes (n : @T int128) : both fset.fset0 [interface] ((nseq int8 16)) := lift_to_both (u128_to_be_bytes n).
Definition u128_from_le_bytes (n : @T (nseq int8 16)) : both fset.fset0 [interface] ((int128)) := lift_to_both (u128_from_le_bytes n).
Definition u128_from_be_bytes (n : @T (nseq int8 16)) : both fset.fset0 [interface] ((int128)) := lift_to_both (u128_from_be_bytes n).

(*** Nats *)


Section Todosection.

Definition nat_mod_equal {p} (a b : nat_mod p) : bool :=
  @eqtype.eq_op (ordinal_eqType (S (Init.Nat.pred (Z.to_nat p)))) a b.

Definition nat_mod_equal_reflect {p} {a b} : Bool.reflect (a = b) (@nat_mod_equal p a b) :=
  @eqtype.eqP (ordinal_eqType (S (Init.Nat.pred (Z.to_nat p)))) a b.
      
Definition nat_mod_zero_pre {p} : nat_mod p := zmodp.Zp0.
Definition nat_mod_one_pre {p} : nat_mod p := zmodp.Zp1.
Definition nat_mod_two_pre {p} : nat_mod p := zmodp.inZp 2.

Definition nat_mod_zero {p} : both fset.fset0 [interface] ((nat_mod p)) := lift_to_both (nat_mod_zero_pre).
Definition nat_mod_one {p} : both fset.fset0 [interface] ((nat_mod p)) := lift_to_both (nat_mod_one_pre).
Definition nat_mod_two {p} : both fset.fset0 [interface] ((nat_mod p)) := lift_to_both (nat_mod_two_pre).


(* convenience coercions from nat_mod to Z and N *)
(* Coercion Z.of_N : N >-> Z. *)


Definition nat_mod_add_pre {n : Z} (a : nat_mod n) (b : nat_mod n) : nat_mod n := zmodp.Zp_add a b.

Definition nat_mod_mul_pre {n : Z} (a:nat_mod n) (b:nat_mod n) : nat_mod n := zmodp.Zp_mul a b.

Definition nat_mod_sub_pre {n : Z} (a:nat_mod n) (b:nat_mod n) : nat_mod n := zmodp.Zp_add a (zmodp.Zp_opp b).

Definition nat_mod_div_pre {n : Z} (a:nat_mod n) (b:nat_mod n) : nat_mod n :=
  zmodp.Zp_mul a (zmodp.Zp_inv b).

(* A % B = (a * B + r) *)

(* TODO: MachineIntegers implementation *)
(* Definition nat_mod_neg {n : Z} (a:nat_mod n) : nat_mod n := GZnZ.opp n a. *)

(* Definition nat_mod_inv {n : Z} (a:nat_mod n) : nat_mod n := GZnZ.inv n a. *)

Definition nat_mod_exp_def_pre {p : Z} (a:nat_mod p) (n : nat) : nat_mod p :=
  let fix exp_ (e : nat_mod p) (n : nat) :=
    match n with
    | 0%nat => nat_mod_one_pre
    | S n => nat_mod_mul_pre a (exp_ a n)
    end in
  exp_ a n.

Definition nat_mod_exp_pre {WS} {p} a n := @nat_mod_exp_def_pre p a (Z.to_nat (@unsigned WS n)).
Definition nat_mod_pow_pre {WS} {p} a n := @nat_mod_exp_def_pre p a (Z.to_nat (@unsigned WS n)).
Definition nat_mod_pow_self_pre {p} a n := @nat_mod_exp_def_pre p a (Z.to_nat (from_uint_size n)).

Close Scope nat_scope.

(* We assume x < m *)

(* Definition nat_mod_from_secret_literal_pre {m : Z} (x:int128) : nat_mod m := *)
(*   @zmodp.inZp (Init.Nat.pred (Z.to_nat m)) (Z.to_nat (unsigned x)). *)

Definition nat_mod_from_secret_literal {m : Z} (x:int128) : both fset.fset0 [interface] (nat_mod m) :=
 lift_to_both (@nat_mod_from_secret_literal m x).  

Definition nat_mod_from_literal (m : Z) (x:int128) : both fset.fset0 [interface] ((nat_mod m)) := nat_mod_from_secret_literal x.

Definition nat_mod_to_byte_seq_le {n : Z} (m : nat_mod n) : both fset.fset0 [interface] (seq int8) := lift_to_both (nat_mod_to_byte_seq_le m).
Definition nat_mod_to_byte_seq_be {n : Z} (m : nat_mod n) : both fset.fset0 [interface] (seq int8) := lift_to_both (nat_mod_to_byte_seq_be m).
Definition nat_mod_to_public_byte_seq_le (n : Z) (m : nat_mod n) : both fset.fset0 [interface] (seq int8) := lift_to_both (nat_mod_to_public_byte_seq_le n m).
Definition nat_mod_to_public_byte_seq_be (n : Z) (m : nat_mod n) : both fset.fset0 [interface] (seq int8) := lift_to_both (nat_mod_to_public_byte_seq_be n m).

Definition nat_mod_bit_pre {n : Z} (a : nat_mod n) (i : uint_size) : bool :=
  Z.testbit (Z.of_nat (nat_of_ord a)) (from_uint_size i).

(* Alias for nat_mod_bit *)
Definition nat_get_mod_bit_pre {p} (a : nat_mod p) := nat_mod_bit_pre a.
Definition nat_mod_get_bit {p} (a : nat_mod p) n :=
  if (nat_mod_bit_pre a n)
  then @nat_mod_one p
  else @nat_mod_zero p.

(*
Definition nat_mod_to_public_byte_seq_le (n: pos)  (len: uint_size) (x: nat_mod_mod n) : lseq pub_uint8 len =
  Definition n' := n % (pow2 (8 * len)) in
  Lib.ByteSequence.nat_mod_to_bytes_le len n'*)

(* Definition nat_to_public_byte_seq_be (n: pos)  (len: uint_size) (x: nat_mod n) : lseq pub_uint8 len =
  Definition n' := n % (pow2 (8 * len)) in
  Lib.ByteSequence.nat_to_bytes_be len n' *)

Axiom array_declassify_eq : forall  {A l}, nseq A l -> nseq A l -> both fset.fset0 [interface] bool_ChoiceEquality.
Axiom array_to_le_uint32s : forall {A l}, nseq A l -> both fset.fset0 [interface] (nseq uint32 l).
Axiom array_to_be_uint32s : forall {l}, nseq uint8 l -> both fset.fset0 [interface] (nseq uint32 (l/4)).
Axiom array_to_le_bytes : forall {A l}, nseq A l -> both fset.fset0 [interface] (seq uint8).
Axiom array_to_be_bytes : forall {A l}, nseq A l -> both fset.fset0 [interface] (seq uint8).
Axiom nat_mod_from_byte_seq_le : forall  {A n}, seq A -> both fset.fset0 [interface] (nat_mod n).
Axiom most_significant_bit : forall {m}, nat_mod m -> uint_size -> both fset.fset0 [interface] (uint_size).


(* We assume 2^x < m *)

Definition nat_mod_pow2 (m : Z) (x : N) : both fset.fset0 [interface] ((nat_mod m)) :=
  lift_to_both (nat_mod_pow2 m x).

End Todosection.

Infix "+%" := nat_mod_add_pre (at level 33) : hacspec_scope.
Infix "*%" := nat_mod_mul_pre (at level 33) : hacspec_scope.
Infix "-%" := nat_mod_sub_pre (at level 33) : hacspec_scope.
Infix "/%" := nat_mod_div_pre (at level 33) : hacspec_scope.

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

  Global Instance cast_Z_to_int {wsize} : Cast Z (@int wsize) := {
    cast n := repr n
  }.

  Global Instance cast_natmod_to_Z {p} : Cast (nat_mod p) Z := {
    cast n := Z.of_nat (nat_of_ord n)
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


(*** Casting *)

Section TodoSection2.

Definition uint128_from_usize (n : uint_size) : int128 := repr (unsigned n).
Definition uint64_from_usize (n : uint_size) : int64 := repr (unsigned n).
Definition uint32_from_usize (n : uint_size) : int32 := repr (unsigned n).
Definition uint16_from_usize (n : uint_size) : int16 := repr (unsigned n).
Definition uint8_from_usize (n : uint_size) : int8 := repr (unsigned n).

Definition uint128_from_uint8 (n : int8) : int128 := repr (unsigned n).
Definition uint64_from_uint8 (n : int8) : int64 := repr (unsigned n).
Definition uint32_from_uint8 (n : int8) : int32 := repr (unsigned n).
Definition uint16_from_uint8 (n : int8) : int16 := repr (unsigned n).
Definition usize_from_uint8 (n : int8) : uint_size := repr (unsigned n).

Definition uint128_from_uint16 (n : int16) : int128 := repr (unsigned n).
Definition uint64_from_uint16 (n : int16) : int64 := repr (unsigned n).
Definition uint32_from_uint16 (n : int16) : int32 := repr (unsigned n).
Definition uint8_from_uint16 (n : int16) : int8 := repr (unsigned n).
Definition usize_from_uint16 (n : int16) : uint_size := repr (unsigned n).

Definition uint128_from_uint32 (n : int32) : int128 := repr (unsigned n).
Definition uint64_from_uint32 (n : int32) : int64 := repr (unsigned n).
Definition uint16_from_uint32 (n : int32) : int16 := repr (unsigned n).
Definition uint8_from_uint32 (n : int32) : int8 := repr (unsigned n).
Definition usize_from_uint32 (n : int32) : uint_size := repr (unsigned n).

Definition uint128_from_uint64 (n : int64) : int128 := repr (unsigned n).
Definition uint32_from_uint64 (n : int64) : int32 := repr (unsigned n).
Definition uint16_from_uint64 (n : int64) : int16 := repr (unsigned n).
Definition uint8_from_uint64 (n : int64) : int8 := repr (unsigned n).
Definition usize_from_uint64 (n : int64) : uint_size := repr (unsigned n).

Definition uint64_from_uint128 (n : int128) : int64 := repr (unsigned n).
Definition uint32_from_uint128 (n : int128) : int32 := repr (unsigned n).
Definition uint16_from_uint128 (n : int128) : int16 := repr (unsigned n).
Definition uint8_from_uint128 (n : int128) : int8 := repr (unsigned n).
Definition usize_from_uint128 (n : int128) : uint_size := repr (unsigned n).


(* Comparisons, boolean equality, and notation *)

Global Instance int_eqdec `{WS : wsize}: EqDec (@int WS) := {
  eqb := eqtype.eq_op ;
  eqb_leibniz := int_eqb_eq ;
}.

Global Instance int_comparable `{WS : wsize} : Comparable (@int WS) :=
    eq_dec_lt_Comparable (wlt Unsigned).
  
Definition uint8_equal : int8 -> int8 -> bool := eqb.

(* Definition nat_mod_val (p : Z) (a : nat_mod p) : Z := nat_of_ord a. *)

Theorem nat_mod_eqb_spec : forall {p} (a b : nat_mod p),
    nat_mod_equal a b = true <-> a = b.
Proof.
  symmetry ; apply (ssrbool.rwP nat_mod_equal_reflect).
Qed.

Global Instance nat_mod_eqdec {p} : EqDec (nat_mod p) := {
  eqb a b := nat_mod_equal a b;
  eqb_leibniz := nat_mod_eqb_spec;
}.

Global Instance nat_mod_comparable `{p : Z} : Comparable (nat_mod p) :=
  eq_dec_lt_Comparable (@order.Order.lt order.Order.OrdinalOrder.ord_display (order.Order.OrdinalOrder.porderType _)).

Fixpoint nat_mod_rem_aux {n : Z} (a:nat_mod n) (b:nat_mod n) (f : nat) {struct f} : nat_mod n :=
  match f with
  | O => a
  | S f' =>
      if geb a b
      then nat_mod_rem_aux (nat_mod_sub_pre a b) b f'
      else a
  end.


(* Infix "rem" := nat_mod_rem (at level 33) : hacspec_scope. *)

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

Lemma vector_eqb_sound : forall {A : Type} {n : nat} `{EqDec A} (v1 v2 : VectorDef.t A n), Vector.eqb _ eqb v1 v2 = true <-> v1 = v2.
Proof.
  intros.
  apply Vector.eqb_eq.
  intros.
  apply eqb_leibniz.
Qed.

Global Program Instance Vector_eqdec {A n} `{EqDec A}: EqDec (VectorDef.t A n) := {
  eqb := Vector.eqb _ eqb;
  eqb_leibniz := vector_eqb_sound;
}.

Global Program Instance Dec_eq_prod (A B : Type) `{EqDec A} `{EqDec B} : EqDec (A * B) := {
  eqb '(a0, b0) '(a1, b1) := andb (eqb a0 a1) (eqb b0 b1)
}.
Next Obligation.
  split ; intros ; destruct x ; destruct y.
  - symmetry in H1.
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

(* Definition u64_to_be_bytes' : int64 -> nseq int8 8 := *)
(*   fun k => array_from_list (int8) [@nat_to_int wsize8 (nat_be_range 4 k 7) ; *)
(*                                @nat_to_int wsize8 (nat_be_range 4 k 6) ; *)
(*                                @nat_to_int wsize8 (nat_be_range 4 k 5) ; *)
(*                                @nat_to_int wsize8 (nat_be_range 4 k 4) ; *)
(*                                @nat_to_int wsize8 (nat_be_range 4 k 3) ; *)
(*                                @nat_to_int wsize8 (nat_be_range 4 k 2) ; *)
(*                                @nat_to_int wsize8 (nat_be_range 4 k 1) ; *)
(*                                @nat_to_int wsize8 (nat_be_range 4 k 0)]. *)

(* Definition u64_from_be_bytes_fold_fun (i : int8) (s : nat '× int64) : nat '× int64 := *)
(*   let (n,v) := s in *)
(*   (S n, v .+ (@repr wsize64 ((int8_to_nat i) * 2 ^ (4 * n)))). *)

(* Definition u64_from_be_bytes' : nseq int8 8 -> int64 := *)
(*   (fun v => snd (VectorDef.fold_right u64_from_be_bytes_fold_fun v (0, @repr wsize64 0))). *)

(* Definition u64_to_be_bytes : int64 -> nseq int8 8 := u64_to_be_bytes'. *)
(* Definition u64_from_be_bytes : nseq int8 8 -> int64 := u64_from_be_bytes'. *)

(* Definition nat_mod_to_byte_seq_be : forall {n : Z}, nat_mod n -> seq int8 := *)
(*   fun k => VectorDef.of_list . *)

End TodoSection2.


(*** Monad / Bind *)

Definition result_unwrap {a b} (x : result a b) : both fset.fset0 [interface] (a) :=
  lift_to_both (result_unwrap x).
Definition result_unwrap_safe {a b} (x : result a b) `{match x with @Ok_type _ _ _ => True | @Err_type _ _ _ => False end} : both fset.fset0 [interface] (a) :=
  lift_to_both (result_unwrap_safe x (H := H)).

Module ChoiceEqualityMonad.
  
  (* Class bind_through_code {M} (mon : ChoiceEqualityMonad.CEMonad M) := *)
  (*   { *)
  (*     bind_code : forall {A B} {L1 L2 : list Location} `{is_true (incl_sort_compute _ L1 L2)} {I} (y : code (fset L1) I (M A)) (f : A -> code (fset L2) I (M B)) , code (fset L2) I (M B) *)
  (*   }. *)


  (* Global Program Instance result_bind_code {C} : bind_through_code (@ChoiceEqualityMonad.result_monad C) := *)
  (*   {| *)
  (*     bind_code A B L1 L2 H I y f := *)
  (*     {code *)
  (*        z ← y ;; *)
  (*        match ct_T z with *)
  (*        | @Ok_type _ _ a => f a *)
  (*        | @Err_type _ _ b => (@mkprog (fset L2) I _ (pkg_core_definition.ret (Err b)) (valid_ret (fset L2) I (Err b))) *)
  (*        end} *)
  (*   |}. *)
  (* Next Obligation. *)
  (*   intros. *)
  (*   apply valid_bind. *)
  (*   - apply (@valid_injectLocations_b I _ (fset L1) (fset L2) y). *)
  (*     apply (list_incl_remove_fset L1 L2).       *)
  (*     apply (proj2 (list_incl_compute L1 L2) H). *)
  (*     apply y. *)
  (*   - intros. *)
  (*     destruct ct_T. *)
  (*     + apply (f t). *)
  (*     + apply valid_ret.       *)
  (* Qed. *)
  
End ChoiceEqualityMonad.  

(*** Notation *)

(* Program Definition if_bind_code {A : ChoiceEquality} `{mnd : ChoiceEqualityMonad.CEMonad} `{@ChoiceEqualityMonad.bind_through_code _ mnd} (b : bool_ChoiceEquality) {Lx Ly L2 : list Location}  `{it1 : is_true (incl_sort_compute _ Lx L2)} `{it2 : is_true (incl_sort_compute _ Ly L2)} {I} (x : code (fset Lx) I (M A)) (y : code (fset Ly) I (M A)) (f : A -> code (fset L2) I (@ct (M A))) : code (fset L2) I (@ct (M A)) := *)
(*   if b *)
(*   then ChoiceEqualityMonad.bind_code (L1 := Lx) (is_true0 := it1) x f *)
(*   else ChoiceEqualityMonad.bind_code (L1 := Ly) (is_true0 := it2) y f. *)

(* Definition foldi_bind_code {A : ChoiceEquality} `{mnd : ChoiceEqualityMonad.CEMonad} `{@ChoiceEqualityMonad.bind_through_code _ mnd} (a : uint_size) (b : uint_size) {L1 L2 : list Location} `{is_true (incl_sort_compute _ L1 L2)} {I}  (init : M A) (f : uint_size -> A -> code (fset L2) I (@ct (M A))) : code (fset L2) I (@ct (M A)) := *)
(*   foldi a b (fun x y => ChoiceEqualityMonad.bind_code (L1 := L1) (is_true0 := is_true0) (lift_to_both y) (f x)) init. *)

(* Global Notation "'foldibnd' s 'to' e 'for' z '>>' f" := (foldi_bind_code s e (Ok z) f) (at level 50). *)

(* Global Notation "'ifbnd' b 'then' x 'else' y '>>' f" := (if b then f x else f y) (at level 200). *)
(* Global Notation "'ifbnd' b 'thenbnd' x 'else' y '>>' f" := (if b then (ChoiceEqualityMonad.bind_code x) f else f y) (at level 200). *)
(* Global Notation "'ifbnd' b 'then' x 'elsebnd' y '>>' f" := (if b then f x else (ChoiceEqualityMonad.bind_code y) f) (at level 200). *)
(* Global Notation "'ifbnd' b 'thenbnd' x 'elsebnd' y '>>' f" := (if b then ChoiceEqualityMonad.bind x f else ChoiceEqualityMonad.bind y f) (at level 200). *)

Section TodoSection3.
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
Canonical int8_default : Default uint8 := @int_default U8.

Global Instance nat_mod_default {p : Z} : Default (nat_mod p) := {
  default := nat_mod_zero_pre
}.
Global Instance prod_default {A B} `{Default A} `{Default B} : Default (prod A B) := {
  default := (default, default)
}.

End TodoSection3.

Infix "=.?" := eqb (at level 40) : hacspec_scope.
Infix "!=.?" := (fun a b => negb (eqb a b)) (at level 40) : hacspec_scope.
Infix "<.?" := ltb (at level 42) : hacspec_scope.
Infix "<=.?" := leb (at level 42) : hacspec_scope.
Infix ">.?" := gtb (at level 42) : hacspec_scope.
Infix ">=.?" := geb (at level 42) : hacspec_scope.

Lemma foldi_nat_both :
  forall {A : ChoiceEquality} {L : {fset Location}} {I} (lo hi : nat)
    (b : nat -> A -> both L I A)
    (* (f_state : nat -> A -> raw_code A) *)
    (* (f_pure : nat -> A -> A) *)
    (v : A),
    (* (lo <= hi)%nat -> *)
  ⊢ ⦃ true_precond ⦄
      @foldi_nat _ lo hi (fun n v => @is_state _ _ _ (b n v)) v
  ≈
  lift_to_both (L := L) (I := [interface]) (Hacspec_Lib_Pre.foldi_nat lo hi (fun n v => @is_pure _ _ _ (b n v)) v)
  ⦃ pre_to_post true_precond ⦄.
Proof.
  intros.
  unfold prog, lift_to_both.

  unfold foldi_nat.
  unfold Hacspec_Lib_Pre.foldi_nat.

    destruct (_ - lo).
  { apply r_ret ; intros ; subst. 
    split.
    - easy.
    - easy.
  }
  
  generalize dependent lo.
  clear.
  generalize dependent v.
      
  induction n ; intros.
  - cbn.
    unfold repr.
    
    replace (fun cur' : choice.Choice.sort (chElement (@ct A)) =>
               @ret (chElement (@ct A)) (@T_ct A (@ct_T A cur'))) with (@ret (chElement (@ct A))) by (apply functional_extensionality ; intros ; now rewrite T_ct_id).
    rewrite bind_ret.
    apply (@code_eq_proof_statement).
    
  - rewrite <- foldi__nat_move_S.
    rewrite <- Hacspec_Lib_Pre.foldi__nat_move_S.

    pose @r_bind_trans_both.
    specialize r with (b := (b lo v)).

    rewrite <- (ct_T_id is_pure).
                            
    specialize r with (g := fun temp => @ret (chElement (@ct A))
       (@T_ct A
          (@Hacspec_Lib_Pre.foldi_nat_ (@T A) (S n) (S lo)
             (fun (n0 : nat) (v0 : @T A) => @is_pure L I A (b n0 v0))
             (ct_T temp)))).
    apply r.
    intros.
    apply IHn.
Qed.

Lemma foldi_both :
  forall {A : ChoiceEquality} {L I} lo hi
    (b : uint_size -> A -> both L I A)
     v,
    (unsigned lo <= unsigned hi)%Z ->
  ⊢ ⦃ true_precond ⦄
     @foldi _ lo hi L I (fun x y => @is_state _ _ _ (b x y))  v
  ≈
     lift_to_both (L := L) (I := I) (Hacspec_Lib_Pre.foldi lo hi (fun x y => @is_pure _ _ _ (b x y)) v)
  ⦃ pre_to_post true_precond ⦄. (* fun '(a, _) '(b, _) => a = b *)
Proof.
  intros.
  unfold foldi.
  unfold prog.
  rewrite foldi_to_foldi_nat by apply H.

  unfold lift_to_both.
  rewrite Hacspec_Lib_Pre.foldi_to_foldi_nat by apply H.

  eapply (foldi_nat_both).
Qed.

(* Class both L I (A : ChoiceEquality) := *)
(*   { *)
(*     is_pure : A ; *)
(*     is_state : code L I (@ct A) ; *)
(*     code_eq_proof_statement : *)
(*     ⊢ ⦃ true_precond ⦄ *)
(*           is_state ≈ lift_to_code (L := L) (I := I) (is_pure) *)
(*       ⦃ pre_to_post true_precond ⦄ *)
(*   }. *)
(* Coercion is_pure : both >-> T. *)
(* Coercion is_state : both >-> code. *)

Lemma foldi_as_both :
  forall {A : ChoiceEquality} {L I} lo hi
    (state : uint_size -> A -> code L I (@ct A))
    (pure : uint_size -> A -> @T A)
     v,
    (unsigned lo <= unsigned hi)%Z ->
    (forall x y,
    ⊢ ⦃ true_precond ⦄ 
        state x y ≈ lift_to_code (L := L) (I := I) (pure x y)
    ⦃ pre_to_post true_precond ⦄) ->
  ⊢ ⦃ true_precond ⦄
     @foldi _ lo hi L I state v
  ≈
     lift_to_both (L := L) (I := I) (Hacspec_Lib_Pre.foldi lo hi pure v)
  ⦃ pre_to_post true_precond ⦄. 
Proof.
  intros.
  apply foldi_both with (b := fun x y => Build_both L I A (pure x y) (state x y) (H0 x y)).
  apply H.
Qed.

(*** For loop again *)

(* SSProve for loop is inclusive upperbound, while hacspec is exclusive upperbound *)
Definition for_loop_range
  (lo: nat)
  (hi: nat)
  (f : nat -> raw_code 'unit) : raw_code 'unit :=
  match hi - lo with
  | O => @ret 'unit tt
  | S i => for_loop (fun n => f (n + lo)) i
  end.

Definition ChoiceEqualityLocation := ∑ (t : ChoiceEquality), nat.
Definition CE_loc_to_loc (x : ChoiceEqualityLocation) : Location :=
  let (k, n) := x in
  (@ct k; n).
Definition CE_loc_to_CE (x : ChoiceEqualityLocation) : ChoiceEquality :=
  let (k, n) := x in
  k.
Coercion CE_loc_to_loc : ChoiceEqualityLocation >-> Location.
Coercion CE_loc_to_CE : ChoiceEqualityLocation >-> ChoiceEquality.

Fixpoint list_types_ (l : list ChoiceEquality) (init : ChoiceEquality) : ChoiceEquality  :=
  match l with
  | (t :: ts) => list_types_ ts t '× init
  | [] => init
  end.

Fixpoint list_types (l : list ChoiceEquality) : ChoiceEquality :=
  match l with
  | [] => unit_ChoiceEquality
  | (t :: ts) => list_types_ ts t
  end.

Program Fixpoint vars_to_tuple (vars : list (∑ (t : ChoiceEquality), t)) {measure (length vars)} : list_types (seq.map (fun '(x ; y) => x) vars)  :=
  match vars with
  | [] => @ct_T unit_ChoiceEquality tt
  | (x :: xs) =>
      match xs with
      | [] => _
      | (s :: xs) => (vars_to_tuple (s :: xs) , _)
      end
  end.

Fixpoint for_loop_return_ (ℓ : list ChoiceEqualityLocation) (vars : list (∑ (t : ChoiceEquality), t)) : raw_code (list_types (seq.cat (seq.map (fun '(x ; y) => x) vars) (seq.map (fun '(x ; y) => x) ℓ) )).
  (* Set Printing Implicit. *)
  destruct ℓ as [ | l ls ].
  - rewrite seq.cats0.
    pose (ret (vars_to_tuple vars)).
    replace (fun pat : ∑ t : ChoiceEquality, @T t => _) with
      (fun pat : @sigT ChoiceEquality
       (fun t : ChoiceEquality => @T t) =>
         match pat return ChoiceEquality with
         | @existT _ _ x _ => x
         end)
      in r by (apply functional_extensionality ; now intros []).
    apply r.
  - apply (getr l).
    intros x.
    destruct l.
    cbn in x.
    pose (for_loop_return_ ls (vars ++ [(_ ; ct_T x)])).
    rewrite seq.map_cat in r.
    cbn in r.
    rewrite <- seq.catA in r.
    cbn in r.
    apply r.
Defined.    
Definition for_loop_return (ℓ : list ChoiceEqualityLocation) : raw_code (list_types (seq.map (fun '(x ; y) => x) ℓ)) := for_loop_return_ ℓ [].

Definition for_loop_locations
           (lo: nat)
           (hi: nat)
           (ℓ : list ChoiceEqualityLocation)
           (f : nat -> raw_code 'unit) :=
  match hi - lo with
  | O => @ret 'unit tt
  | S i => for_loop (fun n => f (n + lo)) i
  end  ;; for_loop_return ℓ.

Theorem empty_put {B} ℓ v (k h : raw_code B) :
  ⊢ ⦃ true_precond ⦄ k ≈ h ⦃ pre_to_post true_precond ⦄ ->
  ⊢ ⦃ true_precond ⦄ #put ℓ := v ;; k ≈ h ⦃ pre_to_post true_precond ⦄.
Proof.
  intros.
  step_code.
  eapply rpre_weaken_rule.
  apply H.
  intros.
  reflexivity.
Qed.  

Theorem forget_precond {B} (x y : raw_code B) P Q :
  ⊢ ⦃ true_precond ⦄ x ≈ y ⦃ Q ⦄ -> 
  ⊢ ⦃ P ⦄ x ≈ y ⦃ Q ⦄. 
Proof.
  intros.
  eapply rpre_weaken_rule.
  apply H.
  intros.
  reflexivity.
Qed.

Ltac ssprove_valid' :=
  repeat ((apply valid_bind ; [apply valid_scheme ; apply prog_valid | intros])
          || (apply valid_bind ; [valid_program | intros])
          (* || (apply ChoiceEqualityMonad.bind_code)  *)
          || (apply valid_putr ; [ cbn ; ssprove_valid_location | ])
          || (apply valid_getr ; [ cbn ; ssprove_valid_location | intros])
          || match goal with
            | [ |- context[match ?x with | true => _ | false => _ end] ] =>
                destruct x
            end
          || match goal with
            | [ |- context[match ?x with | Ok_type _ => _ | Err_type _ => _ end] ] =>
                destruct x
            end
          || match goal with
            | [ |- context[let _ := ct_T ?x in _] ] =>
                destruct ct_T
            end
          || apply valid_ret
          (* || (match goal with *)
          (*    | [ |- context [ValidCode (fset ?xs) _ (@prog _ _ _ (@foldi _ ?lo ?hi (fset ?xs) _ ?f ?v))] ] => *)
          (*        apply valid_foldi_pre *)
          (*    end) *)
          || (match goal with
             | [ |- context [ValidCode (fset ?ys) _ (@prog _ _ _ (@foldi _ ?lo ?hi (fset ?xs) _ ?f ?v))] ] =>
                 eapply (valid_subset xs ys) ; [ | apply valid_foldi_pre ] ; incl_compute
             end)
             ).

Check path.merge_sort_rec.

Theorem length_merge_sort_pop : forall {A} leb (l1 : list (list A)) (l2 : list A),
    length (path.merge_sort_pop leb l2 l1) = length (seq.cat (seq.flatten l1) l2).
Proof.
  intros.
  generalize dependent l2.
  induction l1 ; intros.
  - cbn.
    reflexivity.
  - cbn.
    rewrite IHl1.
    rewrite seq.size_cat.    
    rewrite seq.size_cat.
    rewrite seq.size_cat.        
    rewrite path.size_merge.    
    rewrite seq.size_cat.    
    rewrite ssrnat.addnA.    
    f_equal.
    rewrite ssrnat.addnC.
    reflexivity.
Qed.

Theorem length_sort_even : forall {A} leb a x (l1 : list (list A)) (l2 : list A),
    length (path.merge_sort_rec leb l1 (a :: x :: l2)) =
    length (path.merge_sort_rec leb
        (path.merge_sort_push leb (if leb a x then [a; x] else [x; a]) l1) l2).
Proof.
  reflexivity.
Qed.

Theorem length_sort_is_length' : forall {A} leb (l1 : list (list A)),
    length (path.merge_sort_rec leb l1 []) = length (seq.flatten l1).
Proof.
  destruct l1.
  + cbn.
    reflexivity.
  + cbn.
    rewrite length_merge_sort_pop.
    rewrite seq.size_cat.
    rewrite seq.size_cat.
    rewrite path.size_merge.
    rewrite seq.cats0.
    rewrite ssrnat.addnC.
    reflexivity.
Qed.

(* Theorem length_sort_is_length'' : forall {A} leb (l1 : list (list A)) (l2 : list A), *)
(*     length (path.merge_sort_rec leb l1 l2) = length (seq.cat (seq.flatten l1) l2 ) \/ *)
(*     (forall x, length (path.merge_sort_rec leb l1 (x :: l2)) = S (length (seq.cat l2 (seq.flatten l1)))). *)
(* Proof. *)
(*   intros. *)
(*   generalize dependent l1. *)
(*   induction l2. *)
(*   - intros. left. *)
(*     rewrite length_sort_is_length'. *)
(*     rewrite seq.cats0. *)
(*     reflexivity. *)
(*   - intros. *)
(*     cbn. *)
(*     right. intros. *)
(*     specialize (IHl2 (path.merge_sort_push leb [x; a] l1)). *)
(*     destruct IHl2. *)
(* Admitted. *)
    
(* Theorem length_sort_is_length : forall {A} leb (l1 : list (list A)) (l2 : list A), *)
(*     length (path.merge_sort_rec leb l1 l2) = length (seq.cat l2 (seq.flatten l1)). *)
(* Proof. *)
(*   intros. *)
(* Admitted. *)
  
(* Theorem fset_sort_cons : *)
(*   forall leb (l1 l2 : list Location)  (a : Location), *)
(*     path.sort leb l1 = path.sort leb l2 <-> *)
(*     path.sort leb (a :: l1) = path.sort leb (a :: l2). *)
(* Proof. *)
(*   unfold path.sort. *)
(*   set (n := []). *)
(*   generalize dependent n. *)

(*   assert (forall {A} {l1 l2 : list A}, l1 = l2 -> length l1 = length l2). *)
(*   { intros. apply f_equal with (f := @length _) in H. apply H. } *)
(* Admitted. *)


(* Theorem fset_sort_is_list_in : *)
(*   forall leb (l1 l2 : list Location), *)
(*     (forall a, List.In a l1 <-> List.In a l2) <-> *)
(*     path.sort leb (@seq.undup loc_eqType l1) = path.sort leb (@seq.undup loc_eqType l2). *)
(* Proof. *)
(*   induction l1 ; intros. *)
(*   - destruct l2. *)
(*     + split ; intros. *)
(*       * reflexivity. *)
(*       * reflexivity. *)
(*     + split ; intros. *)
(*       * specialize (H l). *)
(*         exfalso. *)
(*         apply H. *)
(*         left. *)
(*         reflexivity. *)
(*       * apply f_equal with (f := @length _) in H. *)
(*         do 2 rewrite path.size_sort in H. *)
(*         admit. *)
(*   - split. intros. *)
(* Admitted. *)

(* Theorem fset_any_sort : *)
(*   forall leb (l : list Location), *)
(*     (fset (path.sort leb l)) = (fset l). *)
(* Proof.   *)
(* Admitted.   *)
  
Ltac ssprove_valid'_2 :=
  destruct_choice_type_prod
  ; ssprove_valid'
  ; ssprove_valid_program
  ; ssprove_valid_location.
