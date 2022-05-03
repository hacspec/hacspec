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

Require Import ChoiceEquality.

Require Import Lia.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Sumbool.

Declare Scope hacspec_scope.

From CoqWord Require Import ssrZ word.
From Jasmin Require Import word.

Require Import Hacspec_Lib_Comparable.
Require Import Hacspec_Lib_Pre.

Open Scope bool_scope.
Open Scope hacspec_scope.
Open Scope nat_scope.
Open Scope list_scope.

Definition secret : forall {WS : wsize},  (@T (@int WS)) -> code fset.fset0 [interface] (@ct (@int WS)) := fun {WS} x => lift_to_code (secret x).

Section Uint.
  

Definition uint8_declassify (n : int8) : code fset.fset0 [interface] int8 := lift_to_code (uint8_declassify n).
Definition int8_declassify (n : int8) : code fset.fset0 [interface] int8 := lift_to_code (int8_declassify n).
Definition uint16_declassify (n : int16) : code fset.fset0 [interface] int16 := lift_to_code (uint16_declassify n).
Definition int16_declassify (n : int16) : code fset.fset0 [interface] int16 := lift_to_code (int16_declassify n).
Definition uint32_declassify (n : int32) : code fset.fset0 [interface] int32 := lift_to_code (uint32_declassify n).
Definition int32_declassify (n : int32) : code fset.fset0 [interface] int32 := lift_to_code (int32_declassify n).
Definition uint64_declassify (n : int64) : code fset.fset0 [interface] int64 := lift_to_code (uint64_declassify n).
Definition int64_declassify (n : int64) : code fset.fset0 [interface] int64 := lift_to_code (int64_declassify n).
Definition uint128_declassify (n : int128) : code fset.fset0 [interface] int128 := lift_to_code (uint128_declassify n).
Definition int128_declassify (n : int128) : code fset.fset0 [interface] int128 := lift_to_code (int128_declassify n).

Definition uint8_classify (n : int8) : code fset.fset0 [interface] int8 := lift_to_code (uint8_classify n).
Definition int8_classify (n : int8) : code fset.fset0 [interface] int8 := lift_to_code (int8_classify n).
Definition uint16_classify (n : int16) : code fset.fset0 [interface] int16 := lift_to_code (uint16_classify n).
Definition int16_classify (n : int16) : code fset.fset0 [interface] int16 := lift_to_code (int16_classify n).
Definition uint32_classify (n : int32) : code fset.fset0 [interface] int32 := lift_to_code (uint32_classify n).
Definition int32_classify (n : int32) : code fset.fset0 [interface] int32 := lift_to_code (int32_classify n).
Definition uint64_classify (n : int64) : code fset.fset0 [interface] int64 := lift_to_code (uint64_classify n).
Definition int64_classify (n : int64) : code fset.fset0 [interface] int64 := lift_to_code (int64_classify n).
Definition uint128_classify (n : int128) : code fset.fset0 [interface] int128 := lift_to_code (uint128_classify n).
Definition int128_classify (n : int128) : code fset.fset0 [interface] int128 := lift_to_code (int128_classify n).


(* CompCert integers' signedness is only interpreted through 'signed' and 'unsigned',
   and not in the representation. Therefore, uints are just names for their respective ints.
*)

Definition declassify_usize_from_uint8 (n : uint8) : code fset.fset0 [interface] uint_size := lift_to_code (declassify_usize_from_uint8 n).

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
           (f: (@T uint_size) -> @T acc -> raw_code (@ct acc))
           (cur : @T acc) {struct fuel} : raw_code (@ct acc) :=    
    match fuel with
    | O => pkg_core_definition.ret (T_ct cur)
    | S n' =>
        cur' ← f i cur ;;
        foldi_ n' (i .+ one) f (ct_T cur')
    end.

  Lemma valid_foldi_ :
    forall {acc : ChoiceEquality} L I n i (f : @T uint_size -> @T acc -> raw_code (@ct acc)) init,
      (forall i v, ValidCode L I (f i v)) ->
      ValidCode L I (foldi_ n i f init).
  Proof.
    induction n ; intros.
    - cbn.
      ssprove_valid.
    - cbn.
      ssprove_valid.
  Qed.
  
  Definition foldi_pre
             {acc: ChoiceEquality}
             (lo: @T uint_size)
             (hi: @T uint_size) (* {lo <= hi} *)
             (f: (@T uint_size) -> @T acc -> raw_code (@ct acc)) (* {i < hi} *)
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
      (f : @T uint_size -> @T acc -> raw_code (@ct acc))
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
    Set Printing Coercions.
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
      (f : @T uint_size -> @T acc -> raw_code (@ct acc))
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

      specialize (IHfuel (i .+ one) f (ct_T x)).

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
      (f: (@T uint_size) -> @T acc -> raw_code (@ct acc)) (* {i < hi} *)
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
          f_equal.
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
      (f: nat -> @T acc -> raw_code (@ct acc)) (* {i < hi} *)
      (init: @T acc),
      (lo <= hi) ->
      (Z.of_nat hi < @modulus U32)%Z ->
      f = (fun x => f (from_uint_size (repr (Z.of_nat x)))) ->
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
    apply H1.      
    
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
      (f: @T uint_size -> @T acc -> raw_code (@ct acc)) (* {i < hi} *)
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
      (forall (i : int_type) (v : T), ValidCode L I (f i v)) ->
      forall init : T,
        ValidCode L I (foldi_pre lo hi f init).
  Proof.
    intros.
    unfold foldi_pre.
    destruct (unsigned hi - unsigned lo)%Z.
    - ssprove_valid.
    - apply valid_foldi_.
      assumption.
    - ssprove_valid.
  Qed.

  Definition foldi
             {acc: ChoiceEquality}
             (lo: @T uint_size)
             (hi: @T uint_size) (* {lo <= hi} *)
             {L}
             {I}
             (f: (@T uint_size) -> @T acc -> code L I (@ct acc)) (* {i < hi} *)
             (* `[is_subset : is_true (fsubset L1 L0)] *)
             (* `[forall i v, ValidCode L1 I (f i v)] *)
             (init: @T acc)
    :
    code L I (@ct acc) :=
    {| prog := (foldi_pre lo hi f init);
      prog_valid := valid_foldi_pre _ _ _ _ _ |}.

  Definition valid_foldi L I ce := fun lo hi d f => @prog_valid L I (@ct ce) (@foldi ce lo hi L I d f).

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

  (* Lemma valid_foldi_subset : *)
  (*   forall {acc : ChoiceEquality} L1 L2 I lo hi (f : @T uint_size -> @T acc -> code L1 [interface] (@ct acc)) init, *)
  (*     fset.fsubset L1 L2 = true -> *)
  (*     (forall i v, ValidCode L1 I (f i v)) -> *)
  (*     ValidCode L2 I (foldi_pre lo hi f init). *)
  (* Proof. *)
  (*   intros. *)
  (*   apply (@valid_injectLocations) with (L1 := L1). *)
  (*   - apply H. *)
  (*   - apply valid_foldi, H0. *)
  (* Qed.   *)

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

Lemma for_loop_equality : forall fuel f,
    for_loop f fuel  =
    foldi_nat_ (S fuel) 0 (fun x _ => f x) tt.
Proof.
  intros.

  replace f with (fun x => f (x + 0)) at 1.
  2: {
    apply functional_extensionality.
    intros.
    now rewrite Nat.add_0_r.
  }

  generalize dependent 0.
  induction fuel ; intros n.
  - unfold for_loop.
    unfold foldi_nat_.
    now rewrite bind_ret.
  - rewrite for_loop_unfold.
    rewrite <- foldi__nat_move_S.
    f_equal.
    apply functional_extensionality.
    intros cur'.
    destruct cur'.    
    rewrite <- IHfuel.
    f_equal.
    apply functional_extensionality.
    intros.
    f_equal.
    lia.
Qed.    
    
Definition for_loop_range
  (lo: nat)
  (hi: nat)
  (f : nat -> raw_code 'unit) : raw_code 'unit :=
  for_loop (fun n => f (n + lo)) ((hi - lo) - 1).

Definition for_loop_usize (lo hi : uint_size) {L I} (c : uint_size -> code L I 'unit) : raw_code 'unit :=
  for_loop_range (from_uint_size lo) (from_uint_size hi) (fun n => prog (c (usize n))).

Lemma for_loop_range_eq :
  forall lo hi f,
    for_loop_range lo hi f
    =
      (t ← f lo ;;
       foldi_nat (S lo) hi (fun x _ => f x) t).
Proof.
  intros.
  unfold for_loop_range.
  rewrite for_loop_equality.
  unfold foldi_nat.

  replace (hi - S lo) with (hi - lo - 1) by lia.
  
  destruct (hi - lo - 1).
  { cbn.
    rewrite bind_ret.
    reflexivity. }

  set (f' := (fun (x : nat) (_ : T) => f x)).
  replace (f lo) with (f' lo tt) by reflexivity.
  pose foldi__nat_move_S. rewrite e. clear e.

  replace lo with (0 + lo) at 1 by lia.
  rewrite <- foldi__nat_move_to_function_add.
  reflexivity.
Qed.    


Lemma foldi_nat_consume_ret_tt :
  forall {acc : ChoiceEquality} lo hi f (v : acc),
  (@foldi_nat acc lo hi (fun x a => f x tt ;; ret a) v)
  =
  (@foldi_nat unit_ChoiceEquality lo hi f tt ;; ret v).
Proof.
  intros.
  unfold foldi_nat.
  destruct (hi - lo).
  - reflexivity.
  - generalize dependent lo.
    induction n ; intros.
    + cbn.
      rewrite bind_assoc.
      rewrite bind_assoc.
      unfold bind at 2.
      rewrite T_ct_id.
      reflexivity.
    + rewrite <- foldi__nat_move_S.
      rewrite bind_assoc.
      rewrite <- foldi__nat_move_S.
      rewrite bind_assoc.
      f_equal.
      apply functional_extensionality.
      intros [].
      unfold bind at 1.
      rewrite ct_T_id.     
      now rewrite IHn.
Qed.            

(* Lemma foldi_nat_tt_is_ignore : *)
(*   forall {acc : ChoiceEquality} lo hi f (v : acc), *)
(*     (@foldi_nat unit_ChoiceEquality lo hi f tt) *)
(*   = *)
(*   (@foldi_nat acc lo hi (fun x _ => f x tt) v). *)

Lemma foldi_nat_consume_ret :
  forall {acc A : ChoiceEquality} lo hi f (a : acc) (v : A),
    (@foldi_nat (acc '× A) lo hi (fun x a => t ← f x (fst a) ;; @ret (acc '× A) (t, snd a)) (a , v))
  =
  (x ← @foldi_nat acc lo hi f a ;; @ret (acc '× A) (x, v)).
Proof.
Admitted.

Lemma foldi_nat_is_loop :
  forall {acc A : ChoiceEquality} lo hi f (k : A),
  (for_loop_range lo hi (f k) ;; ret k)
    =
  (t ← f k lo ;; foldi_nat (S lo) hi (fun (x0 : nat) (a : T) => f k x0 ;; ret (T_ct a)) k).
Proof.
  intros.

  rewrite for_loop_range_eq.
  rewrite bind_assoc.
  
  f_equal.
  apply functional_extensionality.
  intros [].

  rewrite <- (foldi_nat_consume_ret_tt (S lo) hi _ k).
  reflexivity.  
Qed.
          
(* Theorem for_loop_nat_equality (lo hi : nat) c : *)
(*   ⊢ ⦃ fun '(s₀, s₁) => s₀ = s₁ ⦄ *)
(*      for_loop_range lo hi c tt *)
(*      ≈ *)
(*      foldi_nat (lo) (hi) c (tt)    *)
(*   ⦃ eq ⦄. *)
(* Proof. *)
(*   Set Printing Coercions. *)

(*   unfold for_loop_range. *)
      
(*   unfold prog.   *)
(*   unfold foldi_nat. *)
  
(*   destruct (hi - lo) eqn:hi_lo. *)
(*   - (* apply Nat.sub_0_le in hi_lo. *) *)
(*     (* apply Nat.leb_le in hi_lo. *) *)

(*     (* unfold nat_comparable. *) *)
(*     (* unfold leb. *) *)
(*     (* rewrite hi_lo. *) *)

(*     cbn. *)
(*     rewrite bind_assoc. *)
(*     unfold bind at 2. *)
    
    
(*     unfold for_loop. *)
(*     unfold foldi_nat. *)

(*     apply rreflexivity_rule. *)
(*   - replace (hi <=.? lo) with false by (rewrite leb_correct_conv by (replace hi with (S n + lo) ; lia) ; reflexivity). *)
(*     clear hi_lo. *)

(*     replace (S n - 1) with n by lia.  *)
(*     rewrite <- foldi__nat_move_S. *)

(*     generalize dependent lo. *)
(*     (* generalize dependent P. *) *)
(*     induction n ; intros. *)
(*     + unfold for_loop. *)
(*       rewrite Nat.add_0_l. *)
(*       unfold foldi_nat_. *)
(*       rewrite bind_ret. *)
(*       unfold bind at 1. *)
(*       rewrite bind_assoc. *)
(*       unfold bind at 2. *)
(*       rewrite ct_T_id. *)
      
(*       apply rreflexivity_rule. *)
(*     + rewrite for_loop_unfold. *)
(*       eapply r_bind. *)
(*       apply rreflexivity_rule. *)
(*       intros. *)
(*       eapply rpre_weaken_rule.       *)
(*       apply IHn. *)
(*       intros. *)
(*       inversion H ; subst. *)
(*       reflexivity. *)
(* Qed.     *)

(* Theorem for_loop_nat_equality_better {acc : ChoiceEquality} (lo hi : nat) (c : nat -> acc -> raw_code acc) (v : acc) : *)
(*   ⊢ ⦃ fun '(s₀, s₁) => s₀ = s₁ ⦄ *)
(*       i ← ret v ;; *)
(*   for_loop_range (fun x => (i ← c x (ct_T i) ;; @ret 'unit tt)) lo hi ;; *)
(*   ret i *)
(*      ≈ *)
(*      foldi_nat (lo) (hi) c v    *)
(*      ⦃ eq ⦄. *)
(* Proof. *)
(*   unfold bind at 1. *)
(*   rewrite ct_T_id. *)

(*   unfold for_loop_range. *)
      
(*   unfold prog.   *)
(*   unfold foldi_nat. *)
  
(*   destruct (hi - lo) eqn:hi_lo. *)
(*   - apply Nat.sub_0_le in hi_lo. *)
(*     apply Nat.leb_le in hi_lo. *)
(*     unfold nat_comparable. *)
(*     unfold leb. *)
(*     rewrite hi_lo. *)

(*     apply r_ret. intros ; subst ; reflexivity. *)
(*   - replace (hi <=.? lo) with false by (rewrite leb_correct_conv by (replace hi with (S n + lo) ; lia) ; reflexivity). *)
(*     clear hi_lo. *)

(*     replace (S n - 1) with n by lia.  *)
(*     rewrite <- foldi__nat_move_S. *)

(*     generalize dependent lo. *)
(*     (* generalize dependent P. *) *)
(*     induction n ; intros. *)
(*     + unfold for_loop. *)
(*       rewrite Nat.add_0_l. *)
(*       unfold foldi_nat_. *)
(*       rewrite bind_assoc. *)
(*       unfold bind at 2. *)
(*       (* unfold bind at 2. *) *)
(*       replace (fun cur' : choice.Choice.sort (chElement ct) => ret (T_ct (ct_T cur'))) *)
(*         with *)
(*         (fun cur' : choice.Choice.sort (chElement ct) => ret cur'). *)
(*       rewrite bind_ret. *)
(*       apply rreflexivity_rule. *)
(*     + rewrite for_loop_unfold. *)
(*       eapply r_bind. *)
(*       apply rreflexivity_rule. *)
(*       intros. *)
(*       eapply rpre_weaken_rule.       *)
(*       apply IHn. *)
(*       intros. *)
(*       inversion H ; subst. *)
(*       reflexivity. *)

    
(*   pose for_loop_nat_equality. *)
  

(* Theorem for_loop_equality (lo hi : uint_size) {H : (unsigned lo <= unsigned hi)%Z} {L I} (c : uint_size -> code L I 'unit) : *)
(*   ⊢ ⦃ fun '(s₀, s₁) => s₀ = s₁ ⦄ *)
(*      for_loop_usize lo hi c *)
(*      ≈ *)
(*      foldi (lo) (hi) (fun x a => c x) (tt)    *)
(*   ⦃ eq ⦄. *)
(* Proof. *)
(*   unfold for_loop_usize. *)
(*   unfold prog. *)
(*   unfold foldi. *)
(*   rewrite foldi_to_foldi_nat. *)
(*   apply for_loop_nat_equality. *)
(*   apply H. *)
(* Qed. *)

End Loops.

(*** Seq *)

Section Seqs.

  (**** Unsafe functions *)

  Definition seq_new_ {A: ChoiceEquality} (init : A) (len: nat) : code fset.fset0 [interface] (seq A) :=
    lift_to_code (seq_new_ init len).

  Definition seq_new {A: ChoiceEquality} `{Default A} (len: nat) : code fset.fset0 [interface] (seq A) :=
    lift_to_code (seq_new len).

  Definition seq_len {A: ChoiceEquality} (s: @T (seq A)) : code fset.fset0 [interface] (@ct uint_size) := lift_to_code (seq_len s).

(**** Array manipulation *)
Definition array_new_ {A: ChoiceEquality} (init:@T A) (len: nat) :
  code fset.fset0 [interface] (@ct (nseq A len)) :=
  lift_to_code (array_new_ init len).

Definition array_index {A: ChoiceEquality} `{Default (@T A)} {len : nat} (s: @T (nseq A len)) (i: nat) : code fset.fset0 [interface] (@ct A) :=
  lift_to_code (array_index s i).

Definition array_upd {A: ChoiceEquality} {len : nat} (s: @T (nseq A len)) (i: nat) (new_v: @T A) : code fset.fset0 [interface] (@ct (nseq A len)) :=
  lift_to_code (array_upd s i new_v).

(* substitutes a sequence (seq) into an array (nseq), given index interval  *)
(* Axiom update_sub : forall {A len }, nseq A len -> nat -> nat -> seq A -> t A len. *)
Definition update_sub {A : ChoiceEquality} {len slen} `{Default (@T A)} (v : @T (nseq A len)) (i : nat) (n : nat) (sub : @T (nseq A slen)) : code fset.fset0 [interface] (@ct (nseq A len)) :=
  lift_to_code (update_sub v i n sub).

Definition array_from_seq   {a: ChoiceEquality}
 `{Default (@T a)}
  (out_len:nat)
  (input: @T (seq a)) 
  : code fset.fset0 [interface] (@ct (nseq a out_len)) :=
  lift_to_code (array_from_seq out_len input : @T (nseq a out_len)).

Definition array_to_seq {A : ChoiceEquality} {n} (f : nseq_type A n) : code fset.fset0 [interface] (@ct (seq _)) := @lift_to_code (seq A) _ _ (array_to_seq f).

Definition array_from_slice
  {a: ChoiceEquality}
 `{Default (@T a)}
  (default_value: (@T a))
  (out_len: nat)
  (input: @T (seq a))
  (start: nat)
  (slice_len: nat)  : code fset.fset0 [interface] (@ct (nseq a out_len)) :=
  lift_to_code (array_from_slice default_value out_len input start slice_len).

Definition array_slice
  {a: ChoiceEquality}
 `{Default (@T a)}
  (input: @T (seq a))
  (start: nat)
  (slice_len: nat)
  : code fset.fset0 [interface] (@ct (nseq a slice_len)) :=
  lift_to_code (array_slice input start slice_len).

Definition array_from_slice_range
  {a: ChoiceEquality}
 `{Default (@T a)}
  (default_value: @T a)
  (out_len: nat)
  (input: @T (seq a))
  (start_fin: (@T uint_size * @T uint_size))
  : code fset.fset0 [interface] (@ct (nseq a out_len)) :=
  lift_to_code (array_from_slice_range default_value out_len input start_fin).

Definition array_slice_range
  {a: ChoiceEquality}
 `{Default (@T a)}
  {len : nat}
  (input: @T (nseq a len))
  (start_fin:(@T uint_size * @T uint_size))
    : code fset.fset0 [interface] (@ct (seq a)) :=
  lift_to_code (array_slice_range input start_fin).

Definition array_update
  {a: ChoiceEquality}
 `{Default (@T a)}
  {len: nat}
  (s: @T (nseq a len))
  (start : nat)
  (start_s: @T (seq a))
  : code fset.fset0 [interface] (@ct (nseq a len)) :=
    lift_to_code (array_update s start start_s).

Definition array_update_start
  {a: ChoiceEquality}
 `{Default (@T a)}
  {len: nat}
  (s: @T (nseq a len))
  (start_s: @T (seq a))
    : code fset.fset0 [interface] (@ct (nseq a len)) :=
    lift_to_code (array_update_start s start_s).

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
    : code fset.fset0 [interface] (@ct (nseq a _)) :=
  lift_to_code (seq_slice s start len).

Definition seq_slice_range
  {a: ChoiceEquality}
 `{Default (@T (a))}
  (input: (@T (seq a)))
  (start_fin:((@T (uint_size)) * (@T (uint_size))))
    : code fset.fset0 [interface] (@ct (nseq a _)) :=
  lift_to_code (seq_slice_range input start_fin).

(* updating a subsequence in a sequence *)
Definition seq_update
  {a: ChoiceEquality}
 `{Default (@T (a))}
  (s: (@T (seq a)))
  (start: nat)
  (input: (@T (seq a)))
  : code fset.fset0 [interface] (@ct (seq a)) :=
  lift_to_code (seq_update s start input).

(* updating only a single value in a sequence*)
Definition seq_upd
  {a: ChoiceEquality}
 `{Default (@T (a))}
  (s: (@T (seq a)))
  (start: nat)
  (v: (@T (a)))
  : code fset.fset0 [interface] (@ct (seq a)) :=
  lift_to_code (seq_upd s start v).

Definition seq_update_start
  {a: ChoiceEquality}
 `{Default (@T (a))}
  (s: (@T (seq a)))
  (start_s: (@T (seq a)))
    : code fset.fset0 [interface] (@ct (seq a)) :=
    lift_to_code (seq_update_start s start_s).

Definition array_update_slice
  {a : ChoiceEquality}
 `{Default (@T (a))}
  {l : nat}
  (out: (@T (seq a)))
  (start_out: nat)
  (input: (@T (seq a)))
  (start_in: nat)
  (len: nat)
  : code fset.fset0 [interface] (@ct (nseq a _)) :=
  lift_to_code (array_update_slice (l := l) out start_out input start_in len).
  
Definition seq_update_slice
  {a : ChoiceEquality}
 `{Default (@T (a))}
  (out: (@T (seq a)))
  (start_out: nat)
  (input: (@T (seq a)))
  (start_in: nat)
  (len: nat)
    : code fset.fset0 [interface] (@ct (nseq a _)) :=
  lift_to_code (seq_update_slice out start_out input start_in len).

Definition seq_concat
  {a : ChoiceEquality}
  (s1 :(@T (seq a)))
  (s2: (@T (seq a)))
  : code fset.fset0 [interface] (@ct (seq a)) :=
   lift_to_code (seq_concat s1 s2).

Definition seq_push_pre
  {a : ChoiceEquality}
  (s1 :(@T (seq a)))
  (s2: (@T (a)))
  : code fset.fset0 [interface] (@ct (seq a)) :=
  lift_to_code (seq_push s1 s2).

Definition seq_from_slice_range
  {a: ChoiceEquality}
 `{Default (@T (a))}
  (input: (@T (seq a)))
  (start_fin: ((@T (uint_size)) * (@T (uint_size))))
  : code fset.fset0 [interface] (@ct (seq a)) :=
  lift_to_code (seq_from_slice_range input start_fin).

Definition seq_from_seq {A} (l : @T (seq A)) : code fset.fset0 [interface] (_) := lift_to_code (seq_from_seq l).

(**** Chunking *)

Definition seq_num_chunks {a: ChoiceEquality} (s: (@T (seq a))) (chunk_len: nat) : code fset.fset0 [interface] (@ct uint_size) :=
  lift_to_code (usize (seq_num_chunks s chunk_len)).

Definition seq_chunk_len
  {a: ChoiceEquality}
  (s: (@T (seq a)))
  (chunk_len: nat)
  (chunk_num: nat)
    : code fset.fset0 [interface] (@ct (nat_ChoiceEquality)) :=
  lift_to_code (seq_chunk_len s chunk_len chunk_num).
  
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
  : code fset.fset0 [interface] ((@ct (uint_size '× seq a))) :=
  lift_to_code (seq_get_chunk s chunk_len chunk_num).

Definition seq_set_chunk
  {a: ChoiceEquality}
 `{Default (@T (a))}
  (s: (@T (seq a)))
  (chunk_len: nat)
  (chunk_num: nat)
  (chunk: (@T (seq a)) ) : code fset.fset0 [interface] (@ct (seq a)) :=
  lift_to_code (seq_set_chunk s chunk_len chunk_num chunk).


Definition seq_num_exact_chunks {a} (l : (@T (seq a))) (chunk_size : (@T (uint_size))) : (code fset.fset0 [interface] _) :=
  lift_to_code (seq_num_exact_chunks l chunk_size).


(* Until #84 is fixed this returns an empty sequence if not enough *)
Definition seq_get_exact_chunk {a : ChoiceEquality} `{Default (@T (a))} (l : (@T (seq a))) (chunk_size chunk_num: (@T (uint_size))) :
  code fset.fset0 [interface] (@ct (seq a)) :=
  lift_to_code (seq_get_exact_chunk l chunk_size chunk_num).

Definition seq_set_exact_chunk {a : ChoiceEquality} `{H : Default (@T (a))} :=
  @seq_set_chunk a H.

Definition seq_get_remainder_chunk {a : ChoiceEquality} `{Default (@T (a))} (l : @T (seq a)) (chunk_size : @T (uint_size)) : code fset.fset0 [interface] (@ct (seq a)) :=
  lift_to_code (seq_get_remainder_chunk l chunk_size).

(**** Numeric operations *)

(* takes two nseq's and joins them using a function op : a -> a -> a *)
Definition array_join_map
  {a: ChoiceEquality}
 `{Default (@T (a))}
  {len: nat}
  (op: (@T (a)) -> (@T (a)) -> (@T (a)))
  (s1: (@T (nseq a len)))
  (s2 : (@T (nseq a len))) : code fset.fset0 [interface] (@ct (nseq a len)) :=
  lift_to_code (array_join_map op s1 s2).
  
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
Axiom uint32_to_le_bytes : @T int32 -> code fset.fset0 [interface] (@ct (nseq int8 4)).
(* Definition uint32_to_le_bytes (x: uint32) : nseq uint8 4 :=
  LBSeq.uint_to_bytes_le x. *)

Axiom uint32_to_be_bytes : @T int32 -> code fset.fset0 [interface] (@ct (nseq int8 4)).
(* Definition uint32_to_be_bytes (x: uint32) : nseq uint8 4 :=
  LBSeq.uint_to_bytes_be x *)

Axiom uint32_from_le_bytes : @T (nseq int8 4) -> code fset.fset0 [interface] (@ct (int32)).
(* Definition uint32_from_le_bytes (s: nseq uint8 4) : uint32 :=
  LBSeq.uint_from_bytes_le s *)

Axiom uint32_from_be_bytes : @T (nseq int8 4) -> code fset.fset0 [interface] (@ct (int32)).
(* Definition uint32_from_be_bytes (s: nseq uint8 4) : uint32 :=
  LBSeq.uint_from_bytes_be s *)

Axiom uint64_to_le_bytes : @T int64 -> code fset.fset0 [interface] (@ct (nseq int8 8)).
(* Definition uint64_to_le_bytes (x: uint64) : nseq uint8 8 :=
  LBSeq.uint_to_bytes_le x *)

Axiom uint64_to_be_bytes : @T int64 -> code fset.fset0 [interface] (@ct (nseq int8 8)).
(* Definition uint64_to_be_bytes (x: uint64) : nseq uint8 8 :=
  LBSeq.uint_to_bytes_be x *)

Axiom uint64_from_le_bytes : @T (nseq int8 8) -> code fset.fset0 [interface] (@ct (int64)).
(* Definition uint64_from_le_bytes (s: nseq uint8 8) : uint64 :=
  LBSeq.uint_from_bytes_le s *)

Axiom uint64_from_be_bytes : @T (nseq int8 8) -> code fset.fset0 [interface] (@ct (int64)).
(* Definition uint64_from_be_bytes (s: nseq uint8 8) : uint64 :=
  LBSeq.uint_from_bytes_be s *)

Axiom uint128_to_le_bytes : @T int128 -> code fset.fset0 [interface] (@ct (nseq int8 16)).
(* Definition uint128_to_le_bytes (x: uint128) : nseq uint8 16 :=
  LBSeq.uint_to_bytes_le x *)

Axiom uint128_to_be_bytes : @T int128 -> code fset.fset0 [interface] (@ct (nseq int8 16)).
(* Definition uint128_to_be_bytes (x: uint128) : nseq uint8 16 :=
  LBSeq.uint_to_bytes_be x *)

Definition uint128_from_le_bytes (n : @T (nseq int8 16)) : code fset.fset0 [interface] (@ct (int128)) := lift_to_code (uint128_from_le_bytes n).
(* Definition uint128_from_le_bytes (input: nseq uint8 16) : uint128 :=
  LBSeq.uint_from_bytes_le input *)

Axiom uint128_from_be_bytes : @T (nseq int8 16) -> code fset.fset0 [interface] (@ct (int128)).
(* Definition uint128_from_be_bytes (s: nseq uint8 16) : uint128 :=
  LBSeq.uint_from_bytes_be s *)

Axiom u32_to_le_bytes : @T int32 -> code fset.fset0 [interface] (@ct (nseq int8 4)).
(* Definition u32_to_le_bytes (x: pub_uint32) : nseq pub_uint8 4 :=
  LBSeq.uint_to_bytes_le x *)

Axiom u32_to_be_bytes : @T int32 -> code fset.fset0 [interface] (@ct (nseq int8 4)).
(* Definition u32_to_be_bytes (x: pub_uint32) : nseq pub_uint8 4 :=
  LBSeq.uint_to_bytes_be x *)

Axiom u32_from_le_bytes : @T (nseq int8 4) -> code fset.fset0 [interface] (@ct (int32)).
(* Definition u32_from_le_bytes (s: nseq pub_uint8 4) : pub_uint32 :=
  LBSeq.uint_from_bytes_le s *)

Axiom u32_from_be_bytes : @T (nseq int8 4) -> code fset.fset0 [interface] (@ct (int32)).
(* Definition u32_from_be_bytes (s: nseq pub_uint8 4) : pub_uint32 :=
  LBSeq.uint_from_bytes_be s *)

Axiom u64_to_le_bytes : @T int64 -> code fset.fset0 [interface] (@ct (nseq int8 8)).
(* Definition u64_to_le_bytes (x: int64) : nseq int8 8 :=
  LBSeq.uint_to_bytes_le x *)

Axiom u64_from_le_bytes : @T (nseq int8 8) -> code fset.fset0 [interface] (@ct (int64)).
(* Definition u64_from_le_bytes (s: nseq int8 8) : int64 :=
  LBSeq.uint_from_bytes_le s *)

Axiom u128_to_le_bytes : @T int128 -> code fset.fset0 [interface] (@ct (nseq int8 16)).
(* Definition u128_to_le_bytes (x: int128) : nseq int8 16 :=
  LBSeq.uint_to_bytes_le x *)

Axiom u128_to_be_bytes : @T int128 -> code fset.fset0 [interface] (@ct (nseq int8 16)).
(* Definition u128_to_be_bytes (x: int128) : nseq int8 16 :=
  LBSeq.uint_to_bytes_be x *)

Axiom u128_from_le_bytes : @T (nseq int8 16) -> code fset.fset0 [interface] (@ct (int128)).
(* Definition u128_from_le_bytes (input: nseq int8 16) : int128 :=
  LBSeq.uint_from_bytes_le input *)

Axiom u128_from_be_bytes : @T (nseq int8 16) -> code fset.fset0 [interface] (@ct (int128)).
(* Definition u128_from_be_bytes (s: nseq int8 16) : pub_uint128 :=
  LBSeq.uint_from_bytes_be s *)


(*** Nats *)


Section Todosection.

Definition nat_mod_equal {p} (a b : nat_mod p) : bool :=
  @eqtype.eq_op (ordinal_eqType (S (Init.Nat.pred (Z.to_nat p)))) a b.

Definition nat_mod_equal_reflect {p} {a b} : Bool.reflect (a = b) (@nat_mod_equal p a b) :=
  @eqtype.eqP (ordinal_eqType (S (Init.Nat.pred (Z.to_nat p)))) a b.
      
Definition nat_mod_zero_pre {p} : nat_mod p := zmodp.Zp0.
Definition nat_mod_one_pre {p} : nat_mod p := zmodp.Zp1.
Definition nat_mod_two_pre {p} : nat_mod p := zmodp.inZp 2.

Definition nat_mod_zero {p} : code fset.fset0 [interface] (@ct (nat_mod p)) := lift_to_code (nat_mod_zero_pre).
Definition nat_mod_one {p} : code fset.fset0 [interface] (@ct (nat_mod p)) := lift_to_code (nat_mod_one_pre).
Definition nat_mod_two {p} : code fset.fset0 [interface] (@ct (nat_mod p)) := lift_to_code (nat_mod_two_pre).


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

Definition nat_mod_from_secret_literal {m : Z} (x:int128) : code fset.fset0 [interface] (@ct (nat_mod m)) :=
 lift_to_code (@nat_mod_from_secret_literal m x).  

Definition nat_mod_from_literal (m : Z) (x:int128) : code fset.fset0 [interface] (@ct (nat_mod m)) := nat_mod_from_secret_literal x.

Axiom nat_mod_to_byte_seq_le : forall {n : Z}, nat_mod n -> code fset.fset0 [interface] (seq int8).
Axiom nat_mod_to_byte_seq_be : forall {n : Z}, nat_mod n -> code fset.fset0 [interface] (seq int8).
Axiom nat_mod_to_public_byte_seq_le : forall (n : Z), nat_mod n -> code fset.fset0 [interface] (seq int8).
Axiom nat_mod_to_public_byte_seq_be : forall (n : Z), nat_mod n -> code fset.fset0 [interface] (seq int8).

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

Axiom array_declassify_eq : forall  {A l}, nseq A l -> nseq A l -> code fset.fset0 [interface] 'bool.
Axiom array_to_le_uint32s : forall {A l}, nseq A l -> code fset.fset0 [interface] (nseq uint32 l).
Axiom array_to_be_uint32s : forall {l}, nseq uint8 l -> code fset.fset0 [interface] (nseq uint32 (l/4)).
Axiom array_to_le_bytes : forall {A l}, nseq A l -> code fset.fset0 [interface] (seq uint8).
Axiom array_to_be_bytes : forall {A l}, nseq A l -> code fset.fset0 [interface] (seq uint8).
Axiom nat_mod_from_byte_seq_le : forall  {A n}, seq A -> code fset.fset0 [interface] (nat_mod n).
Axiom most_significant_bit : forall {m}, nat_mod m -> uint_size -> code fset.fset0 [interface] (uint_size).


(* We assume 2^x < m *)

Definition nat_mod_pow2 (m : Z) (x : N) : code fset.fset0 [interface] (@ct (nat_mod m)) :=
  lift_to_code (nat_mod_pow2 m x).

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

Instance eq_dec_lt_Comparable {A : Type} `{EqDec A} (ltb : A -> A -> bool) : Comparable A := {
    ltb := ltb;
    leb a b := if eqb a b then true else ltb a b ;
    gtb a b := ltb b a;
    geb a b := if eqb a b then true else ltb b a;
  }.

Instance eq_dec_le_Comparable {A : Type} `{EqDec A} (leb : A -> A -> bool) : Comparable A := {
    ltb a b := if eqb a b then false else leb a b;
    leb := leb ;
    gtb a b := if eqb a b then false else leb b a;
    geb a b := leb b a;
  }.

Theorem eqb_refl : forall {A} {H : EqDec A} (x : A), @eqb A H x x = true.
Proof.
  intros.
  now rewrite eqb_leibniz.
Qed.


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

Lemma int_eqb_eq : forall {WS : wsize} (a b : @int WS),
    eqtype.eq_op a b = true <-> a = b.
Proof.
  symmetry ; exact (ssrbool.rwP (@eqtype.eqP _ a b)).
Qed.

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

(*** Location *)

Section Location.
    Fixpoint Inb {A : Type} `{EqDec A} (a:A) (l:list A) : bool :=
    match l with
    | nil => false
    | cons b m => (eqb b a) || Inb a m
    end.
  

  Definition location_eqb (ℓ ℓ' : Location) :=
    (eqb (ssrfun.tagged ℓ) (ssrfun.tagged ℓ')).
  (* (@eqtype.eq_op *)
  (* (@eqtype.tag_eqType choice_type_eqType *)
  (*                     (fun _ : choice_type => ssrnat.nat_eqType)) ℓ ℓ'). *)

  Axiom location_is_types : (forall l1 l2 : Location ,
                                is_true (eqb (ssrfun.tagged l1) (ssrfun.tagged l2)) ->
                                is_true (eqtype.eq_op (ssrfun.tag l1) (ssrfun.tag l2))).

  Definition location_eqbP : forall (l1 l2 : Location),
      @eqb nat _ (ssrfun.tagged l1) (ssrfun.tagged l2)
      = (@eqtype.eq_op
           (@eqtype.tag_eqType choice_type_eqType
                               (fun _ : choice_type => ssrnat.nat_eqType)) l1 l2).
  Proof.
    intros.
    symmetry.
    pose (location_is_types l1 l2).
    destruct l1, l2.
    unfold location_eqb.
    cbn.
    unfold eqtype.tag_eq.
    unfold eqtype.tagged_as, ssrfun.tagged , ssrfun.tag , ".π1" , ".π2" in *.

    destruct ((n =? n0)%nat) eqn:b.
    - rewrite i by assumption.        
      destruct eqtype.eqP.
      + cbn.
        unfold eq_rect_r , eq_rect ; destruct eq_sym.      
        assumption.
      + rewrite eqtype.eq_refl.
        reflexivity.
    - destruct eqtype.eqP.
      + cbn.
        unfold eq_rect_r , eq_rect ; destruct eq_sym.
        assumption.
      + rewrite eqtype.eq_refl.
        reflexivity.
  Qed.

  Lemma location_eqb_sound : forall ℓ ℓ' : Location, is_true (location_eqb ℓ ℓ') <-> ℓ = ℓ'.
  Proof.
    intros.
    unfold is_true.
    replace (location_eqb ℓ ℓ' = true) with (true = location_eqb ℓ ℓ') by
      (rewrite boolp.propeqE ; split ; symmetry ; assumption).
    unfold location_eqb. rewrite location_eqbP.
    split.
    - symmetry ; apply lookup_hpv_r_obligation_1 ; assumption.
    - intros ; subst. cbn. symmetry. rewrite eqtype.tag_eqE. apply eqtype.eq_refl.
  Qed.

  Global Program Instance location_eqdec: EqDec (Location) := {
      eqb := location_eqb;
      eqb_leibniz := location_eqb_sound;
    }.

  Definition location_ltb : Location -> Location -> bool :=
    (fun l1 l2 : Location =>
       let (_, n1) := l1 in
       let (_, n2) := l2 in
       ltb n1 n2).

  Global Instance location_comparable : Comparable (Location) :=
    eq_dec_lt_Comparable location_ltb.

  Definition le_is_ord_leq : forall s s0 : nat_ordType,
      eqtype.eq_op s s0 = false -> ltb s s0 = (s <= s0)%ord.
  Proof.
    intros s s0.
    unfold ltb , nat_comparable , Nat.ltb.
    intros e.
    
    generalize dependent s.
    induction s0 ; intros.
    * destruct s ; easy.
    * destruct s. reflexivity.
      (* unfold Nat.leb ; fold Nat.leb. *)
      cbn.
      cbn in IHs0.
      rewrite IHs0.
      reflexivity.
      assumption.
  Qed.
Theorem is_true_split_or : forall a b, is_true (a || b) = (is_true a \/ is_true b).
Proof.
  intros.
  rewrite boolp.propeqE.
  symmetry.
  apply (ssrbool.rwP ssrbool.orP).
Qed.  
Theorem is_true_split_and : forall a b, is_true (a && b) = (is_true a /\ is_true b).
Proof.
  intros.
  rewrite boolp.propeqE.
  symmetry.
  apply (ssrbool.rwP ssrbool.andP).
Qed.  
  
  

    
Theorem LocsSubset : (forall {A} (L1 L2 : list A) (a : A),
     List.incl L1 L2 ->
     List.In a L1 ->
     List.In a L2).
  intros.
  induction L1 as [ | a0 L ] ; cbn in *.
  - contradiction.
  - destruct (List.incl_cons_inv H).
    destruct H0.
    + subst.
      assumption.
    + apply IHL ; assumption.
Qed.
Theorem in_bool_iff : forall {A : Type} `{EqDec A} (a:A) (l:list A), is_true (Inb a l) <-> List.In a l.
  induction l ; cbn.
  - rewrite boolp.falseE.
    reflexivity.
  - cbn.
    rewrite is_true_split_or.    
    apply ZifyClasses.or_morph.
    apply eqb_leibniz.
    apply IHl.
Qed.

Theorem loc_compute_b :
  (forall l : (@sigT choice_type (fun _ : choice_type => nat)),
    forall n : list (@sigT choice_type (fun _ : choice_type => nat)),
      Inb l n = ssrbool.in_mem l (@ssrbool.mem _
          (seq.seq_predType
             (Ord.eqType
                (@tag_ordType choice_type_ordType (fun _ : choice_type => nat_ordType))))
          n)).
  intros.
  cbn.
  unfold ssrbool.in_mem.
  unfold ssrbool.pred_of_mem.
  unfold ssrbool.mem ; cbn.
  
  induction n.
  - cbn.
    reflexivity.
  - cbn.
    unfold "||".
    rewrite eqtype.tag_eqE ; rewrite eqtype.eq_sym ; rewrite <- eqtype.tag_eqE.
    rewrite IHn.
    rewrite location_eqbP.
    reflexivity.
Qed.

Theorem loc_compute : (forall l : (@sigT choice_type (fun _ : choice_type => nat)), forall n : list (@sigT choice_type (fun _ : choice_type => nat)), List.In l n <-> is_true (ssrbool.in_mem l (@ssrbool.mem _
          (seq.seq_predType
             (Ord.eqType
                (@tag_ordType choice_type_ordType (fun _ : choice_type => nat_ordType))))
          n))).
  intros.
  rewrite <- loc_compute_b.
  symmetry.
  apply in_bool_iff.
Qed.

Lemma valid_injectLocations_b :
  forall (import : Interface) (A : choice.Choice.type)
    (L1 L2 : {fset tag_ordType (I:=choice_type_ordType) (fun _ : choice_type => nat_ordType)})
    (v : raw_code A),
    List.incl L1 L2 -> ValidCode L1 import v -> ValidCode L2 import v.
Proof.
    intros A L1 L2 v h incl p.
    induction p.
    all:
      try solve [ constructor ; eauto ].
    all: apply loc_compute in H 
    ; constructor ; [ | eauto ]
    ; apply loc_compute
    ; eapply LocsSubset
    ; eauto.
Qed.

Theorem in_bool_eq : forall {A : Type} `{EqDec A} (a:A) (l:list A), is_true (Inb a l) = List.In a l.
  intros.
  rewrite boolp.propeqE. apply in_bool_iff.
Qed.

  Definition incl_sort_compute A `{EqDec A} (l1 l2 : list A) : bool.
  Proof.
    induction l1.
    - exact true.
    - exact (andb (Inb a l2) (IHl1)).      
  Defined.

  Definition incl_fset_sort_compute (l1 l2 : {fset Location}) : bool.
  Proof.
    destruct l1 as [l1].
    induction l1.
    - exact true.
    - assert (is_true (path.sorted Ord.lt l1)).
      {
        pose (path.drop_sorted).
        specialize i0 with (n := 1) (s := a :: l1).
        rewrite seq.drop1 in i0.
        unfold seq.behead in i0.
        apply i0.
        apply i.
      }
      exact (andb (Inb a l2) (IHl1 H)).      
  Defined.

  Theorem in_remove_fset : forall a (l : list Location), List.In a l <-> List.In a (fset l).
  Proof.
    intros.
    do 2 rewrite loc_compute.
    unfold fset ; rewrite ssreflect.locked_withE.
    cbn.
    rewrite (@path.mem_sort (Ord.eqType
                (@tag_ordType choice_type_ordType (fun _ : choice_type => nat_ordType))) (tag_leq (I:=choice_type_ordType) (T_:=fun _ : choice_type => nat_ordType)) (@seq.undup
                (Ord.eqType
                   (@tag_ordType choice_type_ordType (fun _ : choice_type => nat_ordType)))
                l)).
    
    generalize dependent a.
    induction l ; intros.
    + easy.
    + cbn.

      rewrite (@seq.in_cons (Ord.eqType
                               (@tag_ordType choice_type_ordType (fun _ : choice_type => nat_ordType))) a l).
      rewrite is_true_split_or.

      match goal with
      | [ |- context[match ?x with | true => _ | false => _ end] ] =>
          destruct x eqn:so
      end.
      * rewrite <- IHl.
        split.
        -- intros [].
           ++ apply Couplings.reflection_nonsense in H.
              subst.
              apply so.
           ++ apply H.
        -- intros.
           right.
           apply H.
      * split.
        -- intros [].
           ++ apply Couplings.reflection_nonsense in H.
              subst.
              apply seq.mem_head.
           ++ apply seq.mem_drop with (n0 := 1%nat).
              cbn.
              rewrite seq.drop0.
              apply IHl.
              apply H.
        -- intros.
           destruct (eqtype.eq_op) eqn:so2.
           ++ left.
              reflexivity.
           ++ right.
              unfold ssrbool.in_mem in H.
              unfold ssrbool.pred_of_mem in H.
              unfold ssrbool.mem in H.
              cbn in H.
              cbn in so2.
              rewrite so2 in H.
              cbn in H.

              apply IHl.
              apply H.
  Qed.

  Theorem list_incl_remove_fset {A} `{EqDec A} : forall (l1 l2 : list Location), List.incl l1 l2 <-> List.incl (fset l1) (fset l2).
  Proof.
    pose in_bool_eq.
    pose loc_compute_b.
    
    intros. (* [l1] [l2]. *)
    pose (@incl_sort_compute A H).

    cbn in *.
    
    induction l1.
    - rewrite <- fset0E. easy.
    - cbn.
      unfold incl.
      cbn.
      split.
      + intros.
        rewrite <- in_remove_fset.
        rewrite <- in_remove_fset in H1.
        apply H0.
        apply H1.
      + intros.        
        rewrite -> in_remove_fset.
        apply H0.
        rewrite <- in_remove_fset.
        apply H1.
Qed.        

  Theorem list_incl_compute {A} `{EqDec A} : forall (l1 l2 : list Location), List.incl l1 l2 <-> is_true (incl_sort_compute _ l1 l2).
    induction l1.
    - split ; intros.
      reflexivity.
      apply incl_nil_l.
    - intros.
      
      assert (forall A (a : A) l1 l2, List.incl (a :: l1) l2 <-> (List.In a l2 /\ List.incl l1 l2)).
      {
        split.
        - pose List.incl_cons_inv.
          apply List.incl_cons_inv.
        - intros [].
          apply List.incl_cons ; assumption.          
      }

      rewrite H0.

      cbn.
      rewrite is_true_split_and.
      rewrite in_bool_eq.

      apply and_iff_compat_l.
      apply IHl1.
  Qed.        

  (* Theorem forall l1 l2, incl_sort_compute <-> list_incl_compute  *)

End Location.

(*** Monad / Bind *)

Definition result_unwrap {a b} (x : result a b) : code fset.fset0 [interface] (a) :=
  lift_to_code (result_unwrap x).
Definition result_unwrap_safe {a b} (x : result a b) `{match x with @Ok_type _ _ _ => True | @Err_type _ _ _ => False end} : code fset.fset0 [interface] (a) :=
  lift_to_code (result_unwrap_safe x (H := H)).

Module ChoiceEqualityMonad.
  
  Class bind_through_code {M} (mon : ChoiceEqualityMonad.CEMonad M) :=
    {
      bind_code : forall {A B} {L1 L2 : list Location} `{is_true (incl_sort_compute _ L1 L2)} {I} (y : code (fset L1) I (M A)) (f : A -> code (fset L2) I (M B)) , code (fset L2) I (M B)
    }.


  Global Program Instance result_bind_code {C} : bind_through_code (@ChoiceEqualityMonad.result_monad C) :=
    {|
      bind_code A B L1 L2 H I y f :=
      {code
         z ← y ;;
         match ct_T z with
         | @Ok_type _ _ a => f a
         | @Err_type _ _ b => (@mkprog (fset L2) I _ (pkg_core_definition.ret (Err b)) (valid_ret (fset L2) I (Err b)))
         end}
    |}.
  Next Obligation.
    intros.
    apply valid_bind.
    - apply (@valid_injectLocations_b I _ (fset L1) (fset L2) y).
      apply (list_incl_remove_fset L1 L2).      
      apply (proj2 (list_incl_compute L1 L2) H).
      apply y.
    - intros.
      destruct ct_T.
      + apply (f t).
      + apply valid_ret.      
  Qed.
  
End ChoiceEqualityMonad.  

(*** Notation *)

Program Definition if_bind_code {A : ChoiceEquality} `{mnd : ChoiceEqualityMonad.CEMonad} `{@ChoiceEqualityMonad.bind_through_code _ mnd} (b : bool_ChoiceEquality) {Lx Ly L2 : list Location}  `{it1 : is_true (incl_sort_compute _ Lx L2)} `{it2 : is_true (incl_sort_compute _ Ly L2)} {I} (x : code (fset Lx) I (M A)) (y : code (fset Ly) I (M A)) (f : A -> code (fset L2) I (@ct (M A))) : code (fset L2) I (@ct (M A)) :=
  if b
  then ChoiceEqualityMonad.bind_code (L1 := Lx) (is_true0 := it1) x f
  else ChoiceEqualityMonad.bind_code (L1 := Ly) (is_true0 := it2) y f.

Definition foldi_bind_code {A : ChoiceEquality} `{mnd : ChoiceEqualityMonad.CEMonad} `{@ChoiceEqualityMonad.bind_through_code _ mnd} (a : uint_size) (b : uint_size) {L1 L2 : list Location} `{is_true (incl_sort_compute _ L1 L2)} {I}  (init : M A) (f : uint_size -> A -> code (fset L2) I (@ct (M A))) : code (fset L2) I (@ct (M A)) :=
  foldi a b (fun x y => ChoiceEqualityMonad.bind_code (L1 := L1) (is_true0 := is_true0) (lift_to_code y) (f x)) init.

Global Notation "'foldibnd' s 'to' e 'for' z '>>' f" := (foldi_bind_code s e (Ok z) f) (at level 50).

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

(* Ltac ssprove_valid_location := *)
(*   try repeat (try (apply eqtype.predU1l ; reflexivity) ; try apply eqtype.predU1r). *)

Ltac ssprove_valid_location :=
  repeat
    (try reflexivity ;
     try (rewrite fset_cons ;
          apply (ssrbool.introT (fsetU1P _ _ _)) ;
          try (left ; reflexivity) ;
          right)).


Ltac ssprove_valid_program :=
  try (apply prog_valid) ;
  try (apply valid_scheme ; apply prog_valid).

Ltac destruct_choice_type_prod :=
  try match goal with
  | H : choice.Choice.sort (chElement (loc_type ?p)) |- _ =>
      unfold p in H ;
      unfold loc_type in H ;
      unfold "_ .π1" in H
  end ;
  try match goal with
  | H : @T (prod_ChoiceEquality _ _) |- _ =>
      destruct H
  end ;
  try repeat match goal with
  | H : choice.Choice.sort
         (chElement
            (@ct
               (prod_ChoiceEquality _ _))) |- _ =>
      destruct H
  end ;
  repeat match goal with
         | H : prod _ _ |- _ => destruct H
         end.

Ltac ssprove_valid_2 :=
  (* destruct_choice_type_prod ; *)
  ssprove_valid ;
  ssprove_valid_program ;
  ssprove_valid_location.

Check ct.

Theorem single_mem : forall m, 
Datatypes.is_true
    (@ssrbool.in_mem
       (Ord.sort (@tag_ordType choice_type_ordType (fun _ : choice_type => nat_ordType)))
       m
       (@ssrbool.mem
          (Ord.sort
             (@tag_ordType choice_type_ordType (fun _ : choice_type => nat_ordType)))
          (fset_predType
             (@tag_ordType choice_type_ordType (fun _ : choice_type => nat_ordType)))
          (@fset (@tag_ordType choice_type_ordType (fun _ : choice_type => nat_ordType))
             (@cons (@sigT choice_type (fun _ : choice_type => nat)) m
                    (@nil (@sigT choice_type (fun _ : choice_type => nat))))))).
Proof.
  intros.
  rewrite <- (@fset1E (@tag_ordType choice_type_ordType (fun _ : choice_type => nat_ordType))).
  rewrite (ssrbool.introT (fset1P _ _)) ; reflexivity.
Qed.
  
(* Notation "ct( x , y , .. , z )" := (pair_ChoiceEquality .. (pair_ChoiceEquality x y) .. z) : hacspec_scope. *)



(* Locate "=.?". *)

(* Definition le_is_ord_leq2 : forall (s s0 : Location), *)
(*     eqb (ssrfun.tagged s) (ssrfun.tagged s0) = false ->  *)
(*     eqtype.eq_op (ssrfun.tag s) (ssrfun.tag s0) = false -> *)
(*     s <.? s0 = (s <= s0)%ord. *)
(* Proof. *)
(*   intros s s0. *)
(*   unfold "<.?" , location_comparable , eq_dec_lt_Comparable , location_ltb , "<?". *)
(*   unfold eqtype.tagged_as, ssrfun.tagged , ssrfun.tag , ".π1" , ".π2". *)
(*   intros e H. *)
(*   destruct s , s0. *)

(*   replace (((x; n) <= (x0; n0))%ord) with (x < x0)%ord. *)
(*   2 : {     *)
(*     cbn. *)
(*     unfold tag_leq. *)
(*     cbn. *)
(*     cbn in H. *)
(*     replace (choice_type_test x x0) with false by apply H. *)
(*     cbn. *)
(*     rewrite Bool.orb_false_r. *)
(*     reflexivity. *)
(*   }   *)

  
  
(*   replace (eqtype.eq_op (ssrfun.tag (x; n)) (ssrfun.tag (x0; n0))) with false. *)
  
(*   rewrite le_is_ord_leq by apply e. *)

  
  
(*   generalize dependent n. *)
(*   induction n0 ; intros. *)
(*   * destruct s ; easy. *)
(*   * destruct s. reflexivity. *)
(*     (* unfold Nat.leb ; fold Nat.leb. *) *)
(*     cbn. *)
(*     cbn in IHs0. *)
(*     rewrite IHs0. *)
(*     reflexivity. *)
(*     assumption. *)
(* Qed. *)

Definition location_lebP : (tag_leq (I:=choice_type_ordType) (T_:=fun _ : choice_type => nat_ordType)) = leb.
Proof.
  symmetry.
  do 2 (apply functional_extensionality ; intro).
  unfold tag_leq.
  unfold "<=.?".
  unfold location_comparable.
  unfold eq_dec_lt_Comparable.
  destruct (@eqb Location _ x x0) eqn:x_eq_x0.
  - cbn in x_eq_x0.
    rewrite location_is_types by apply x_eq_x0.    
    unfold eqtype.tagged_as.
    destruct eqtype.eqP.
    + rewrite (Couplings.reflection_nonsense _ (ssrfun.tagged x) (ssrfun.tagged x0) x_eq_x0).
      unfold eq_rect_r , eq_rect ; destruct eq_sym.
      rewrite Ord.leqxx.
      rewrite Bool.orb_true_r.
      reflexivity. 
    + exfalso.
      apply n.
      apply Couplings.reflection_nonsense.
      apply (location_is_types x x0 x_eq_x0).
  - unfold location_ltb.
    pose (location_eqbP x x0).
    destruct x , x0.
    cbn in x_eq_x0.
    cbn in e.
    rewrite x_eq_x0 in e.
    symmetry in e.
    unfold eqtype.tag_eq in e.
    unfold eqtype.tagged_as, ssrfun.tagged , ssrfun.tag , ".π1" , ".π2" in e.
    
    unfold eqtype.tagged_as, ssrfun.tagged , ssrfun.tag , ".π1" , ".π2".
    destruct eqtype.eqP.
    + subst.
      unfold eq_rect_r , eq_rect in * ; destruct eq_sym.
      rewrite choice_type_refl in e.
      rewrite Bool.andb_true_l in e.

      rewrite Ord.ltxx.
      
      rewrite Bool.orb_false_l.
      rewrite Bool.andb_true_l.

      apply le_is_ord_leq.
      assumption.
    + exfalso.
      admit.
Admitted.



Ltac ssprove_valid_location' :=
  apply loc_compute ; repeat (try (left ; reflexivity) ; right) ; try reflexivity.

Fixpoint uniqb {A} `{EqDec A} (s : list A) :=
  match s with
  | cons x s' => andb (negb (Inb x s')) (uniqb s')
  | _ => true
  end.

Theorem uniq_is_bool : forall (l : list (tag_ordType (I:=choice_type_ordType) (fun _ : choice_type => nat_ordType))), seq.uniq l = uniqb l.
Proof.
  cbn ; intros.
  induction l.
  - reflexivity.
  - cbn.
    f_equal.
    + f_equal.
      rewrite loc_compute_b.
      reflexivity.
    + exact IHl.
Qed.        
    
Theorem simplify_fset : forall l,
    is_true
    (path.sorted leb l) ->
    is_true (uniqb l) ->
    (@FSet.fsval (@tag_ordType choice_type_ordType (fun _ : choice_type => nat_ordType))
       (@fset _
              l)) = (l).
  intros l is_sorted  is_unique.
  unfold fset ; rewrite ssreflect.locked_withE.
  cbn.
  rewrite <- uniq_is_bool in is_unique.
  rewrite seq.undup_id by assumption.
  rewrite path.sorted_sort.
  - reflexivity.
  - destruct (tag_leqP (I:=choice_type_ordType) (fun _ : choice_type => nat_ordType)) as [ _ trans _ _ ].
    apply trans.
  - rewrite location_lebP.
    assumption.  
Qed.

Theorem simplify_sorted_fset : forall l,
    is_true (uniqb l) ->
    (@FSet.fsval (@tag_ordType choice_type_ordType (fun _ : choice_type => nat_ordType))
       (@fset _  (path.sort (leb : Location -> Location -> bool) l))) = (path.sort (leb : Location -> Location -> bool) l).
Proof.
  intros.
  apply simplify_fset.
  apply path.sort_sorted ; pose location_lebP ; cbn ; cbn in e ; rewrite <- e ; apply Ord.leq_total.
  rewrite <- uniq_is_bool.
  rewrite path.sort_uniq.
  rewrite uniq_is_bool.
  apply H.
Qed.
  
Theorem tag_leq_simplify :
  forall (a b : Location),
    is_true (ssrfun.tag a <= ssrfun.tag b)%ord ->
    is_true (ssrfun.tagged a <= ssrfun.tagged b)%ord ->
    is_true (tag_leq (I:=choice_type_ordType) (T_:=fun _ : choice_type => nat_ordType) a b).
Proof.
  intros [] [].
  
  unfold tag_leq.
  unfold eqtype.tagged_as, ssrfun.tagged , ssrfun.tag , ".π1" , ".π2".

  intro.
  rewrite Ord.leq_eqVlt in H.
  rewrite is_true_split_or in H.
  destruct H.
  - apply Couplings.reflection_nonsense in H ; subst.
    
    rewrite Ord.ltxx.
    rewrite Bool.orb_false_l.
    rewrite eqtype.eq_refl.
    rewrite Bool.andb_true_l.
    
    destruct eqtype.eqP.
    + unfold eq_rect_r , eq_rect ; destruct eq_sym.
      trivial.
    + contradiction.
  - rewrite H ; clear H.
    reflexivity.    
Qed.
  
Theorem tag_leq_inverse :
  forall a b,
    tag_leq (I:=choice_type_ordType) (T_:=fun _ : choice_type => nat_ordType) a b
    =
      negb (tag_leq (I:=choice_type_ordType) (T_:=fun _ : choice_type => nat_ordType)
                    b a) ||
           eqtype.eq_op (ssrfun.tag a) (ssrfun.tag b) &&
        eqtype.eq_op (ssrfun.tagged a) (ssrfun.tagged b).
Proof.
  intros [a b] [c d].
  unfold tag_leq.
  
  rewrite Bool.negb_orb.
  rewrite Bool.negb_andb.
  rewrite Bool.andb_orb_distrib_r.

  unfold eqtype.tagged_as.
  unfold ssrfun.tagged , ssrfun.tag , ".π1" , ".π2".
  rewrite <- Bool.orb_assoc.
  
  f_equal.
  - rewrite <- Bool.negb_orb.    
    rewrite <- Bool.orb_comm.
    rewrite <- Ord.leq_eqVlt.
    rewrite <- Ord.ltNge.
    reflexivity.
  - destruct (eqtype.eq_op a c) eqn:a_eq_c.
    + apply Couplings.reflection_nonsense in a_eq_c.
      subst.
      do 2 rewrite Bool.andb_true_l.

      destruct eqtype.eqP. 2: contradiction.
      
      unfold eq_rect_r , eq_rect.
      destruct eq_sym.

      rewrite Ord.leq_eqVlt.
      rewrite Bool.orb_comm.

      f_equal.
      rewrite <- Ord.ltNge.
      rewrite Ord.ltxx.
      reflexivity.
    + do 2 rewrite Bool.andb_false_l.
      rewrite Bool.orb_false_r.
      symmetry.

      destruct eqtype.eqP.
      { subst. rewrite eqtype.eq_refl in a_eq_c. discriminate a_eq_c. }

      rewrite Ord.eq_leq by reflexivity.
      rewrite Bool.andb_false_r.
      reflexivity.
Qed.

Ltac incl_compute :=
  now (apply list_incl_compute ; cbn ; reflexivity).

(* Ltac incl_b_compute := *)
(*   let H := fresh in *)
(*   intro H ; *)
(*   repeat rewrite is_true_split_or in H ; *)
(*   decompose [and or] H ; clear H ; *)
(*   [ repeat rewrite is_true_split_or ; *)
(*     repeat (try (left ; assumption) ; right) *)
(*   | discriminate ]. *)

(* Ltac incl_compute := *)
(*   now (unfold List.incl ; intros [] ; repeat rewrite <- in_bool_eq ; unfold Inb ; incl_b_compute). *)

(* Lemma valid_inject_loc_b : *)
(*   forall (import : Interface) (A : choiceType) *)
(*     (L1 L2 : {fset tag_ordType (I:=choice_type_ordType) (fun _ : choice_type => nat_ordType)}) *)
(*     (v : raw_code A), *)
(*     List.incl (path.sort leb L1) (path.sort leb L2). *)
(* Proof. *)
(*   intros. *)
(*   rewrite simplify_sorted_fset by reflexivity. *)
(*   eapply (valid_injectLocations_b) with (L1 := L1). *)
(*   [ rewrite simplify_sorted_fset by reflexivity  *)
(*     ; rewrite simplify_sorted_fset by reflexivity *)
(*     ; cbn   *)
(*     ; incl_compute *)
(*   | .. ]    . *)
(* Qed. *)

(* eapply (valid_injectLocations_b) with (L1 := _) ; *)

Ltac valid_sorted_incl :=
  rewrite simplify_sorted_fset by reflexivity 
    ; rewrite simplify_sorted_fset by reflexivity
    ; cbn  
    ; incl_compute.

Ltac valid_program :=
  (* match goal with *)
  (* | |- (ValidCode _ _ (@prog _ _ _ (?program))) => apply program *)
  (* end. *)
  match goal with
  | |- (ValidCode _ _ (@prog _ _ _ ?program)) =>
      pose program ;
      match goal with
      | H : (code ?fset _ _) |- _ =>          
          eapply (valid_injectLocations_b) with (L1 := fset) ;
          [ | apply program ]
      end           
  end ; valid_sorted_incl .

Ltac ssprove_valid' :=
  repeat (valid_program
          || (apply valid_bind ; [apply valid_scheme ; apply prog_valid | intros])
          || (apply valid_bind ; [ | intros ; ssprove_valid' ])
          || (apply ChoiceEqualityMonad.bind_code) 
          || (apply valid_putr ; [ cbn ; ssprove_valid_location | ])
          || (apply valid_getr ; [ cbn ; ssprove_valid_location | intros])
          (* || (apply valid_foldi ; intros) *)
          || (unfold for_loop_usize, for_loop_range ;
             (* match goal with *)
            (* | [ |- context[match ?x with | true => _ | false => _ end] ] => *)
                (* destruct x ; [ |  *)apply valid_for_loop ; intros (* ] *)
            (* end *)
             )
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
          || apply valid_ret).

Ltac ssprove_valid'_2 :=
  destruct_choice_type_prod ;
  ssprove_valid' ;
  ssprove_valid_program ;
  ssprove_valid_location.

Definition heap_ignore_post fset {A} : postcond A A :=
  fun '(a, h₀) '(b, h₁) => a = b /\ heap_ignore fset (h₀ , h₁).

Class both fset (A : ChoiceEquality) :=
  {
    is_pure : A ;
    is_state : code fset [interface] (@ct A) ;
    code_eq_proof_statement : ⊢ ⦃ (fun '(h0, h1) => heap_ignore fset (h0, h1)) ⦄  is_state ≈ lift_to_code (L := fset.fset0) (I := [interface]) (is_pure) ⦃ heap_ignore_post fset ⦄
  }.
Coercion is_pure : both >-> T.
Coercion is_state : both >-> code.

(* Class CodeEqProofStatement  {fset} {A : ChoiceEquality} `(b : @both fset A) := *)
(*   code_eq_proof_statement : ⊢ ⦃ (fun '(h0, h1) => heap_ignore fset (h0, h1)) ⦄  is_state ≈ lift_to_code (L := fset.fset0) (I := [interface]) (is_pure) ⦃ heap_ignore_post fset ⦄. *)

Theorem bind_both {A B : ChoiceEquality} {fset}  `{b : @both fset A} (* `{code_bind : @CodeEqProofStatement fset A b } *)
    (k : choice.Choice.sort A -> raw_code B) :
    (forall a₀ a₁ : choice.Choice.sort A, ⊢ ⦃ fun '(s₀, s₁) => heap_ignore_post fset (a₀, s₀) (a₁, s₁) ⦄ k a₀ ≈ k a₁ ⦃ heap_ignore_post fset ⦄) ->
    ⊢ ⦃ (fun '(h₀, h₁) => heap_ignore fset (h₀ , h₁)) ⦄
        (@bind A B is_state k)
        ≈
        (@bind A B (lift_to_code (L := fset.fset0) (I := [interface]) is_pure) k)
    ⦃ heap_ignore_post fset ⦄.
Proof. exact (r_bind (is_state) ((lift_to_code (L := fset.fset0) (I := [interface]) is_pure)) k k (heap_ignore fset) (heap_ignore_post fset) (heap_ignore_post fset) code_eq_proof_statement). Qed.

Ltac bind_both_function :=
  match goal with
  | [ |- context [ ⊢ ⦃ ?P ⦄ (@bind _ _ (_ (_ ?code_fun) ) ?k) ≈ _ ⦃ ?Q ⦄ ]] =>
      apply (@bind_both _ _ _ Q (code_eq_proof_statement code_fun) k)
  end.
     (* match goal with *)
  (* | [ |- context [ ⊢ ⦃ ?P ⦄ (@bind _ _ (_ (?proj_fun ?code_fun) ) ?k) ≈ _ ⦃ ?Q ⦄ ]] => *)
  (*     apply (r_bind  (proj_fun code_fun) (prog (lift_to_code (L := fset.fset0) (I := [interface]) code_fun)) k k P (fun '(a, _) '(b, _) => a = b) Q) ; [apply code_eq_proof_statement | intros ..] *)
  (* end. *)

Theorem bind_rewrite : forall (A B : ChoiceEquality) x f, @bind A B (ret x) f = f x.
Proof ltac:(reflexivity).

Ltac clear_bind :=
  rewrite bind_rewrite
  ||
  bind_both_function.

Ltac progress_step_code :=
  match goal with
  | [ |- context [ ⊢ ⦃ _ ⦄ (#put ?l := ?x ;; (getr ?l ?a)) ≈ _ ⦃ _ ⦄ ]] =>
      apply (r_transL (#put l := x ;; a x )) ;
      [ apply (r_put_get _ l x a) | ]
  end
  ||
  match goal with
  | [ |- context [ ⊢ ⦃ _ ⦄ (#put ?l := ?x ;; (putr ?l ?y ?a)) ≈ _ ⦃ _ ⦄ ]] =>
      apply (r_transL (#put l := y ;; a )) ;
      [ apply contract_put | ]
  end
  ||
  match goal with
  | [ |- context [ ⊢ ⦃ _ ⦄ (#put ?l := ?x ;; ?a) ≈ ?b ⦃ _ ⦄ ]] =>
      apply (r_put_lhs l x a b (* (fun '(h0, h1) => heap_ignore fset (h0, h1)) *))
  end
  ||
  apply r_ret.

Ltac step_code :=
  repeat (clear_bind || progress_step_code).

Lemma foldi_both :
  forall {A : ChoiceEquality} {L} lo hi
    (f_state : uint_size -> A -> code L [interface] A)
    (f_pure : uint_size -> A -> A) v,
    (unsigned lo <= unsigned hi)%Z ->
    forall (P : precond), (forall x, P (x , x)) ->
    (forall (i : uint_size) (v : A),
        ⊢ ⦃ fun '(s₀, s₁) => P (s₀, s₁) /\ s₀ = s₁ ⦄
            f_state i v
          ≈
            ret (f_pure i v)
          ⦃ eq ⦄) ->
  ⊢ ⦃ fun '(s₀, s₁) => s₀ = s₁ ⦄
     @foldi _ lo hi L [interface] f_state v 
  ≈
     lift_to_code (L := L) (I := [interface]) (Hacspec_Lib_Pre.foldi lo hi f_pure v) 
  ⦃ eq ⦄. (* fun '(a, _) '(b, _) => a = b *)
Proof.
  intros.
  unfold foldi.
  unfold prog.
  rewrite foldi_to_foldi_nat by apply H.

  unfold lift_to_code.
  rewrite Hacspec_Lib_Pre.foldi_to_foldi_nat by apply H.

  unfold foldi_nat.  
  unfold Hacspec_Lib_Pre.foldi_nat.

  set (r := Z.to_nat (unsigned lo)).
  destruct (_ - r) ; [ apply r_ret ; intros ; subst ; reflexivity | ].

  generalize dependent r.
  clear -H0 H1.
  generalize dependent v.
  
  induction n ; intros.
  - cbn.
    unfold repr.
    
    replace (fun cur' : choice.Choice.sort (chElement (@ct A)) =>
               @ret (chElement (@ct A)) (@T_ct A (@ct_T A cur'))) with (@ret (chElement (@ct A))) by (apply functional_extensionality ; intros ; now rewrite T_ct_id).
    rewrite bind_ret.
    eapply rpre_weaken_rule.
    apply H1. intros ; subst ; split ; easy.
  - rewrite <- foldi__nat_move_S.
    rewrite <- Hacspec_Lib_Pre.foldi__nat_move_S.

    replace (ret
       (T_ct
          (Hacspec_Lib_Pre.foldi_nat_ (S n) (S r)
                                      (fun x : nat => f_pure (repr (Z.of_nat x))) (f_pure (repr (Z.of_nat r)) v)))) with
      (pu ← lift_to_code (L := L) (I := [interface]) (f_pure (repr (Z.of_nat r)) v) ;;
        ret
       (T_ct
          (Hacspec_Lib_Pre.foldi_nat_ (S n) (S r)
                                      (fun x : nat => f_pure (repr (Z.of_nat x))) (ct_T pu)))).

    pose (@r_bind).
    eapply (@r_bind) with (mid := eq).    
    eapply rpre_weaken_rule.
    apply H1. intros ; subst ; split ; easy.
    intros.
    specialize IHn with (v := (ct_T a₁)) (r := S r).
    apply (r_transR _ (foldi_nat_ (S n) (S r)
       (fun (x : nat) (x0 : T) => prog (f_state (repr (Z.of_nat x)) x0)) 
       (ct_T a₁))).
    apply IHn.
    apply rpre_hypothesis_rule.
    intros ; inversion H ; subst.
    eapply rpre_weaken_rule.    
    apply @rreflexivity_rule.
    intros sa sb [].
    cbn in *.
    subst.
    reflexivity.

    unfold prog.
    unfold lift_to_code.
    rewrite bind_rewrite.
    rewrite ct_T_id.
    reflexivity.
Qed.

Ltac heap_ignore_remove_ignore :=
  match goal with
  | H : heap_ignore ?L ( ?a , ?b ) |- _ =>
      match goal with
      | [ |- context[ heap_ignore L ( ?c , b ) ] ] =>
          intros ℓ H_mem
          ; specialize (H ℓ H_mem)
          ; match goal with
            | [ |- context[ get_heap (set_heap ?x ?ℓ' ?v) ℓ = get_heap _ ℓ ] ] =>
                destruct (@eqtype.eq_op (@eqtype.tag_eqType choice_type_eqType
             (fun _ : choice_type => ssrnat.nat_eqType)) ℓ ℓ') eqn:ℓ_eq_ℓ'
                ; [ exfalso
                    ; apply (ssrbool.elimT eqtype.eqP) in ℓ_eq_ℓ' ; subst
                    ; apply (ssrbool.elimT ssrbool.negP) in H_mem
                    ; apply H_mem
                    ; clear H_mem
                    ; apply loc_compute
                    ; unfold eqtype.val
                    ; rewrite simplify_sorted_fset
                    ; repeat (reflexivity || (left ; reflexivity) || right)
                  | rewrite <- (get_heap_set_heap a ℓ ℓ' v) ;
                    [ assumption
                    | rewrite ℓ_eq_ℓ' ; reflexivity 
                    ]
                ]     
            end
      end
  end .

Ltac both_bind :=
  match goal with
  | [ |- context[ (?x : both ?L ?T) ] ] =>  
      match goal with
      | [ |- context[ (bind ?f ?v) ] ] =>
          eapply (r_transR (bind (@is_state _ _ x) v) (bind (lift_to_code (@is_pure _ _ x)) v)) ;
          [ 
          | eapply r_bind ; [ apply x | ]
          ]
      end
  end.


Ltac remove_T_ct :=
  match goal with
  | [ |- context[ T_ct ?x ] ] =>  
      replace (T_ct x) with x by reflexivity
  | H : _ |- context[ T_ct ?x ] =>  
      replace (T_ct x) with x in H by reflexivity
  end.
