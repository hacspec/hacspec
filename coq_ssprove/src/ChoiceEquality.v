From Coq Require Import ZArith List.
From Crypt Require Import choice_type Package.
Import PackageNotation.
From Crypt Require Import pkg_interpreter.
From extructures Require Import ord fset fmap.
Require Import Hacspec_Lib_Comparable.

Require Import LocationUtility.
Require Import Coq.Logic.FunctionalExtensionality.

(* Set Printing Universes. *)

Monomorphic Class ChoiceEquality := {
    T : Type@{choice.Choice.type.u0} ;
    ct : choice_type ;
    ChoiceEq : @eq Type@{choice.Choice.type.u0} (choice.Choice.sort (chElement ct)) T ;
  }.
(* Monomorphic Class ChoiceEquality@{a} := { *)
(*     T : Type@{a} ; *)
(*     ct : choice_type ; *)
(*     ChoiceEq : @eq Type@{a} (choice.Choice.sort (chElement ct)) T ; *)
(*   }. *)
Print ChoiceEquality.


Global Coercion T : ChoiceEquality >-> Sortclass.
Global Coercion ct : ChoiceEquality >-> choice_type.

Definition ct_T {ce : ChoiceEquality} (x : choice.Choice.sort (@ct ce)) : @T ce :=
  eq_rect (choice.Choice.sort (chElement (@ct ce))) id x (@T ce) ChoiceEq.

Definition T_ct {ce : ChoiceEquality} (x : @T ce) : choice.Choice.sort (@ct ce) :=
  eq_rect_r id x ChoiceEq.

Theorem ct_T_id : forall {ce : ChoiceEquality} t, ct_T (T_ct t) = t.
Proof (fun ce => rew_opp_r id (@ChoiceEq ce)). 

Theorem T_ct_id : forall {ce : ChoiceEquality} t, T_ct (ct_T t) = t.
Proof (fun ce => rew_opp_l id (@ChoiceEq ce)).

Global Coercion ct_T : choice.Choice.sort >-> T.
Global Coercion T_ct : T >-> choice.Choice.sort.

Lemma ChoiceEquality_ct_EqP : forall ce1 ce2, ce1 = ce2 <-> @ct ce1 = @ct ce2.
Proof.
  split ; intros.
  - rewrite H.
    reflexivity.
  - destruct ce1 as [T1 ct1 CE1].
    destruct ce2 as [T2 ct2 CE2].
    cbn in *.
    subst.
    reflexivity.
Qed.
    
Definition ChoiceEquality_leq (t1 t2 : ChoiceEquality) :=
    choice_type_leq t1 t2.

Lemma ChoiceEquality_leqP : Ord.axioms ChoiceEquality_leq.
Proof.
  unfold ChoiceEquality_leq.
  destruct choice_type_leqP.
  split.
  - intros ?. apply H.
  - intros ? ? ? ? ?. apply (H0 y x z) ; assumption.
  - intros ? ? ?.
    apply ChoiceEquality_ct_EqP.
    apply H1. assumption.
  - intros ? ?. apply H2.
Qed.

(* Locate OrdMixin. *)
(* Definition ChoiceEquality_ordMixin := OrdMixin ChoiceEquality_leqP. *)
(* Canonical ChoiceEquality_ordType : Ord.type. *)
(* Proof. *)
(*   pose ChoiceEquality. *)
(*   Set Printing Universes. *)
(*   pose ChoiceEquality_ordMixin. *)
(*   pose (@Ord.pack T0). *)  
(*   Constrait (extructures.ord. < Hacspec.ChoiceEquality.a). *)  
(*   specialize (t T0). *)  
(*   pose (OrdType ChoiceEquality ChoiceEquality_ordMixin). *)  
(* (* Constraint ChoiceEquality.a < {extructures.ord.93}. *) *)  
(*   Eval hnf in OrdType ChoiceEquality ChoiceEquality_ordMixin. *)

Program Instance prod_ChoiceEquality (a b : ChoiceEquality) : ChoiceEquality :=
  {| T := (@T a) * (@T b) ; ct := (@ct a) × (@ct b); |}.
Next Obligation.
  intros.
  do 2 rewrite ChoiceEq.
  reflexivity.
Defined.

Notation "A '× B" := (prod_ChoiceEquality A B) (at level 79, left associativity) : hacspec_scope.

Open Scope hacspec_scope.

Definition fst_CE {A B} (p : A '× B) : A := let '(f,s) := p in f.
Definition snd_CE {A B} (p : A '× B) : B := let '(f,s) := p in s.  

(* Notation "A '× B" := (prod A B) (at level 79, left associativity) : hacspec_scope. *)

Instance nat_ChoiceEquality : ChoiceEquality := {| T := nat ; ct := 'nat ; ChoiceEq := ltac:(reflexivity) |}.
Instance bool_ChoiceEquality : ChoiceEquality := {| T := bool ; ct := 'bool ; ChoiceEq := ltac:(reflexivity) |}.
Instance unit_ChoiceEquality : ChoiceEquality := {| T := unit ; ct := 'unit ; ChoiceEq := ltac:(reflexivity) |}.

Definition lift_to_code {ce : ChoiceEquality} {L I} (x : @T ce) : code L I (@ct ce) :=
  {code ret (T_ct x)}.

Definition evaluate_code {ce : ChoiceEquality} {L I} (x : code L I (@ct ce)) `{match Run sampler x 0 with Some _ => True | _ => False end} : @T ce.
Proof.
  destruct (Run sampler x 0).
  apply (ct_T s).
  contradiction.
Defined.


Definition pre_to_post (P : precond) {A} : postcond A A :=
  fun '(a, h₀) '(b, h₁) => a = b /\ P (h₀ , h₁).  

Definition true_precond : precond := fun _ => True.

Class both L I (A : ChoiceEquality) :=
  {
    is_pure : A ;
    is_state : code L I (@ct A) ;
    code_eq_proof_statement :
    ⊢ ⦃ true_precond ⦄
          is_state ≈ lift_to_code (L := L) (I := I) (is_pure)
      ⦃ pre_to_post true_precond ⦄
  }.
Coercion is_pure : both >-> T.
Coercion is_state : both >-> code.

Program Definition lift_to_both {ce : ChoiceEquality} {L I} (x : @T ce) : both L I ce :=
  {| is_pure := x ; is_state := @lift_to_code ce L I x |}.
Next Obligation. intros. apply r_ret. intros. split ; reflexivity. Qed.



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
      unfold projT1 in H
  end ;
  repeat match goal with
  | H : @T (prod_ChoiceEquality _ _) |- _ =>
      destruct H
  end ;
  repeat match goal with
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


Ltac ssprove_valid_location' :=
  apply loc_compute ; repeat (try (left ; reflexivity) ; right) ; try reflexivity.

(* Fixpoint uniqb {A} `{EqDec A} (s : list A) := *)
(*   match s with *)
(*   | cons x s' => andb (negb (Inb x s')) (uniqb s') *)
(*   | _ => true *)
(*   end. *)

(* Theorem uniq_is_bool : forall (l : list (tag_ordType (I:=choice_type_ordType) (fun _ : choice_type => nat_ordType))), seq.uniq l = uniqb l. *)
(* Proof. *)
(*   cbn ; intros. *)
(*   induction l. *)
(*   - reflexivity. *)
(*   - cbn. *)
(*     f_equal. *)
(*     + f_equal. *)
(*       rewrite loc_compute_b. *)
(*       reflexivity. *)
(*     + exact IHl. *)
(* Qed.         *)
    
(* Theorem simplify_fset : forall l, *)
(*     is_true *)
(*     (path.sorted leb l) -> *)
(*     is_true (uniqb l) -> *)
(*     (@FSet.fsval (@tag_ordType choice_type_ordType (fun _ : choice_type => nat_ordType)) *)
(*        (@fset _ *)
(*               l)) = (l). *)
(*   intros l is_sorted  is_unique. *)
(*   unfold fset ; rewrite ssreflect.locked_withE. *)
(*   cbn. *)
(*   rewrite <- uniq_is_bool in is_unique. *)
(*   rewrite seq.undup_id by assumption. *)
(*   rewrite path.sorted_sort. *)
(*   - reflexivity. *)
(*   - destruct (tag_leqP (I:=choice_type_ordType) (fun _ : choice_type => nat_ordType)) as [ _ trans _ _ ]. *)
(*     apply trans. *)
(*   - rewrite location_lebP. *)
(*     assumption.   *)
(* Qed. *)

(* Theorem simplify_sorted_fset : forall l, *)
(*     is_true (uniqb l) -> *)
(*     (FSet.fsval (fset (path.sort (leb : Location -> Location -> bool) l))) *)
(*     = (path.sort (leb : Location -> Location -> bool) l). *)
(* Proof. *)
(*   intros. *)
(*   apply simplify_fset. *)
(*   apply path.sort_sorted ; pose location_lebP ; cbn ; cbn in e ; rewrite <- e ; apply Ord.leq_total. *)
(*   rewrite <- uniq_is_bool. *)
(*   rewrite path.sort_uniq. *)
(*   rewrite uniq_is_bool. *)
(*   apply H. *)
(* Qed. *)
  
Theorem tag_leq_simplify :
  forall (a b : Location),
    is_true (ssrfun.tag a <= ssrfun.tag b)%ord ->
    is_true (ssrfun.tagged a <= ssrfun.tagged b)%ord ->
    is_true (tag_leq (I:=choice_type_ordType) (T_:=fun _ : choice_type => nat_ordType) a b).
Proof.
  intros [] [].
  
  unfold tag_leq.
  unfold eqtype.tagged_as, ssrfun.tagged , ssrfun.tag , projT1 , projT2.

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
      (negb (tag_leq (I:=choice_type_ordType) (T_:=fun _ : choice_type => nat_ordType)
                    b a) ||
           eqtype.eq_op (ssrfun.tag a) (ssrfun.tag b) &&
        eqtype.eq_op (ssrfun.tagged a) (ssrfun.tagged b))%bool.
Proof.
  intros [a b] [c d].
  unfold tag_leq.
  
  rewrite Bool.negb_orb.
  rewrite Bool.negb_andb.
  rewrite Bool.andb_orb_distrib_r.

  unfold eqtype.tagged_as.
  unfold ssrfun.tagged , ssrfun.tag , projT1 , projT2.
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

(* rewrite list_incl_sort with (leb := location_ltb_simple) ;  *)
Ltac incl_compute :=
  now (apply list_incl_expand ; (now repeat (split ; [ repeat ((left ; reflexivity) || (right)) | ]))).
  (* now (apply list_incl_compute ; cbn ; repeat rewrite ssrnat.eqnE ; repeat rewrite eqtype.eq_refl ; repeat rewrite choice_type_test_refl ; cbn ; reflexivity). *)

(* Ltac valid_sorted_incl := *)
(*   rewrite simplify_sorted_fset by reflexivity  *)
(*   ; rewrite simplify_sorted_fset by reflexivity *)
(*   ; apply list_incl_sort_order_ignorant_compute with (leb1 := location_ltb_simple) *)
(*   ; cbn *)
(*   ; incl_compute. *)

Ltac valid_program :=
  apply prog_valid
  || (apply valid_scheme ; apply prog_valid)
  || (eapply (valid_injectLocations_b) ; [ | apply prog_valid ] ; apply -> list_incl_remove_fset ; incl_compute).


Definition heap_ignore_post fset {A} : postcond A A :=
  pre_to_post (heap_ignore fset).

Theorem heap_ignore_refl :
  forall {fset} h, heap_ignore fset (h, h).
Proof.
  intros fset h ℓ ?.
  reflexivity.
Qed.

Theorem heap_ignore_post_refl :
  forall {fset A} (x : A * heap), heap_ignore_post fset x x.
Proof.
  intros fset A [].
  split. reflexivity.
  apply heap_ignore_refl.
Qed.

Lemma heap_ignore_weaken :
  forall fset fset', is_true (fsubset fset fset') ->
  forall x, heap_ignore fset x -> heap_ignore fset' x.
Proof.
  intros.
  destruct x as [h h0].
  pose (INV'_heap_ignore fset fset' fset0).
  rewrite fsetU0 in i.
  unfold INV' in i.
  specialize (i H h h0).
  destruct i as [? _].
  intros l ?.
  specialize (H1 H0 l H2 ltac:(easy)).
  rewrite H1.
  reflexivity.
Qed.

Lemma rpost_heap_ignore_weaken :
  forall {A} fset fset', is_true (fsubset fset fset') ->
  forall (x y : raw_code A),
    ⊢ ⦃ (fun '(h0, h1) => heap_ignore fset (h0, h1)) ⦄
        x ≈ y
      ⦃ heap_ignore_post fset ⦄ ->
    ⊢ ⦃ (fun '(h0, h1) => heap_ignore fset (h0, h1)) ⦄
        x ≈ y
        ⦃ heap_ignore_post fset' ⦄.
Proof.
  intros.
  (* eapply rpre_weaken_rule. *)
  eapply rpost_weaken_rule.
  apply H0.

  intros [] [] []. subst.
  split. reflexivity.
  apply (heap_ignore_weaken fset) ; assumption.
Qed.


Lemma rpre_heap_ignore_weaken :
  forall {A} fset fset', is_true (fsubset fset fset') ->
  forall (x y : raw_code A),
    ⊢ ⦃ (fun '(h0, h1) => heap_ignore fset' (h0, h1)) ⦄
        x ≈ y
      ⦃ heap_ignore_post fset ⦄ ->
    ⊢ ⦃ (fun '(h0, h1) => heap_ignore fset (h0, h1)) ⦄
        x ≈ y
        ⦃ heap_ignore_post fset ⦄.
Proof.
  intros.
  eapply rpre_weaken_rule.
  (* eapply rpost_weaken_rule. *)
  apply H0.

  intros. cbn.
  apply (heap_ignore_weaken fset fset') ; assumption.
Qed.

(* Theorem bind_both {A B : ChoiceEquality} {fset' fset : {fset Location}}  `{b : @both fset A} *)
(*         (k : choice.Choice.sort A -> raw_code B) : *)
(*   List.incl fset fset' -> *)
(*   forall fset_head fset_tail, *)
(*     ⊢ ⦃ (fun '(h₀, h₁) => heap_ignore (fset_head :|: fset' :|: fset_tail) (h₀ , h₁)) ⦄ *)
(*         (@bind A B is_state k) *)
(*         ≈ *)
(*         (@bind A B (lift_to_code (L := fset) (I := [interface]) is_pure) k) *)
(*     ⦃ heap_ignore_post (fset_head :|: fset' :|: fset_tail) ⦄. *)
(* Proof. *)
(*   intros f_subset fset_head fset_tail. *)
(*   apply list_incl_fsubset in f_subset. *)


(*   assert (subset_eq : fset' = fset :|: (fset' :\: fset)). *)
(*   { *)
(*     apply (ssrbool.elimT fsetUidPr) in f_subset. *)
(*     rewrite fsetUDr. *)
(*     rewrite f_subset. *)
(*     rewrite fsetDv. *)
(*     rewrite fsetD0. *)
(*     reflexivity. *)
(*   } *)

(*   rewrite subset_eq. *)
(*   rewrite (fsetUC fset (fset' :\: fset)).     *)
(*   rewrite fsetUA.   *)
    
(*   eapply (r_bind (is_state) ((lift_to_code (L := fset) (I := [interface]) is_pure)) k k). *)

(*   apply code_eq_proof_statement. *)

(*   (* intros. *) *)

(*   exists fset_head, fset_tail. *)
(*   split. *)
(*   - intros. *)
  
  
(*   apply rpre_hypothesis_rule. *)
(*   intros ? ? []. *)
(*   subst. *)

(*   eapply rpost_weaken_rule. *)
(*   - eapply rpre_weaken_rule. *)
(*     + apply rreflexivity_rule. *)
(*     + intros ? ? []. subst. *)
(*       admit. *)
(*   - intros [] [] ?. *)
(*     inversion_clear H. *)
(*     apply heap_ignore_post_refl. *)
(* Admitted. *)

(* Ltac bind_both_function := *)
(*   match goal with *)
(*   | [ |- context [ ⊢ ⦃ ?P ⦄ (@bind _ _ (_ (_ ?code_fun) ) ?k) ≈ _ ⦃ ?Q ⦄ ]] => *)
(*       apply (@bind_both _ _ _ Q (code_eq_proof_statement code_fun) k) *)
(*   end. *)

Theorem bind_rewrite : forall A B x f, @bind A B (ret x) f = f x.
Proof.
  intros.
  unfold bind.
  reflexivity.
Qed.
(* Proof ltac:(unfold bind ; reflexivity). *)

Ltac clear_bind :=
  rewrite bind_rewrite
  (* || *)
  (* bind_both_function *).

Theorem r_bind_eq : forall {B C : ChoiceEquality} (y : B) (g : choice.Choice.sort B  -> raw_code C), (temp ← ret y ;; g temp) = g y.
Proof. reflexivity. Qed.

Theorem r_bind_trans :
  forall {B C : ChoiceEquality}
    (f g : choice.Choice.sort B -> raw_code C) (x : raw_code B) (y : B),
  forall (P P_mid : precond) (Q : postcond (choice.Choice.sort C) (choice.Choice.sort C)),
  forall (H_x_is_y : ⊢ ⦃ P ⦄ x ≈ ret (T_ct y) ⦃ pre_to_post P_mid ⦄),
    (forall a, ⊢ ⦃ P_mid ⦄ f a  ≈ g a ⦃ Q ⦄) ->
    ⊢ ⦃ P ⦄ temp ← x ;; f temp ≈ g (T_ct y) ⦃ Q ⦄.
Proof.
  intros.
  (* apply list_incl_fsubset in H_incl. *)

  replace (g y) with (temp ← ret y ;; g temp) by reflexivity.

  (* destruct H_P_Q as [fset_head [fset_tail [H_P [H_P_mid H_Q]]]]. *)
  (* cbn in fset_head , fset_tail.  *)

  (* set (P_mid := fun _ _ => _) in H_x_is_y. *)
  
  eapply r_bind with (mid := pre_to_post P_mid).
  apply H_x_is_y.

  intros.
  eapply rpre_hypothesis_rule.
  intros ? ? []. subst.
  eapply rpre_weaken_rule.
  2: { intros ? ? []. subst. apply H1. }
  clear H1.

  apply H.
Qed.

Lemma heap_ignore_remove_set_heap :
  forall {fset} {s₀ s₁ : heap} {ℓ v},
  is_true (ssrbool.in_mem ℓ (ssrbool.mem fset)) ->
  heap_ignore (fset) (s₀, s₁) ->
  heap_ignore (fset) (set_heap s₀ ℓ v, s₁).
Proof.
  intros.
  unfold heap_ignore.
  intros.
  unfold heap_ignore in H0.  
  specialize (H0 ℓ0 ltac:(assumption)).
  rewrite <- H0.
  rewrite <- get_heap_set_heap.
  reflexivity.

  destruct (@eqtype.eq_op
          (@eqtype.tag_eqType choice_type_eqType
                              (fun _ : choice_type => ssrnat.nat_eqType)) ℓ0 ℓ) eqn:ℓ_eq.
  - apply (ssrbool.elimT eqtype.eqP) in ℓ_eq.
    subst.
    exfalso.
    apply (ssrbool.elimT ssrbool.negP) in H.
    + apply H.
    + assumption.
  - reflexivity.
Qed.

Lemma isolate_mem_section :
  forall (fset : {fset Location}) ℓ  fset_head fset_tail,
    is_true (ssrbool.in_mem ℓ (ssrbool.mem fset)) ->
    is_true (ssrbool.in_mem ℓ (ssrbool.mem (fset_head :|: fset :|: fset_tail))).
Proof.
  intros.
  apply loc_compute. apply in_split_fset_cat ; left ; apply in_split_fset_cat ; right.
  apply loc_compute. apply H.
Qed.  
  
Ltac solve_heap_ignore_remove_set_heap :=
  apply (heap_ignore_remove_set_heap) ; [ apply isolate_mem_section ; apply loc_compute ; apply -> in_remove_fset ; cbn ; repeat (left ; reflexivity || right || reflexivity) | assumption ].

Theorem r_bind_trans_both : forall {B C : ChoiceEquality} {L I} {f g : choice.Choice.sort B -> raw_code C} (b : both L I B),
  forall (P : precond) (Q : postcond _ _),
    (forall a, ⊢ ⦃ true_precond ⦄ f a  ≈ g a ⦃ Q ⦄) -> 
    ⊢ ⦃ P ⦄ temp ← @is_state L I B b ;; f temp ≈ g (is_pure) ⦃ Q ⦄.
Proof.
  intros.
  eapply r_bind_trans with (P_mid := true_precond).

  eapply rpre_weaken_rule.    
  apply code_eq_proof_statement.
  reflexivity.

  intros.
  apply H.
Qed.

Ltac solve_post_from_pre :=
  let H := fresh in
  intros ? ? H
  ; split
  ; [reflexivity | ]
  ; ( assumption
      || (apply restore_set_lhs in H
         ; [ assumption
           | intros ? ?
             ; solve_heap_ignore_remove_set_heap ] )).

Corollary better_r_put_lhs : forall {A B : choice.Choice.type} (ℓ : Location)
       (v : choice.Choice.sort (Value (projT1 ℓ))) (r₀ : raw_code A) 
       (r₁ : raw_code B) (pre : precond)
       (post : postcond (choice.Choice.sort A) (choice.Choice.sort B)),
     ⊢ ⦃ set_lhs ℓ v pre ⦄ r₀ ≈ r₁ ⦃ post ⦄ ->
     ⊢ ⦃ pre ⦄ #put ℓ := v ;; r₀ ≈ r₁ ⦃ post ⦄.
Proof.
  intros.
  replace (pre) with (fun '(x, y) => pre (x, y)).
  apply r_put_lhs.
  apply H.
  apply functional_extensionality.
  intros [].
  reflexivity.
Qed.

Corollary better_r_get_remind_lhs : forall {A B : choice.Choice.type} (ℓ : Location)
       (v : choice.Choice.sort (Value (projT1 ℓ)))
       (r₀ : choice.Choice.sort (Value (projT1 ℓ)) -> raw_code A) (r₁ : raw_code B)
       (pre : precond) (post : postcond (choice.Choice.sort A) (choice.Choice.sort B)),
     Remembers_lhs ℓ v pre ->
     ⊢ ⦃ pre ⦄ r₀ v ≈ r₁ ⦃ post ⦄ ->
     ⊢ ⦃ pre ⦄ x ← get ℓ ;; r₀ x ≈ r₁ ⦃ post ⦄.
Proof.
  intros.
  replace (pre) with (fun '(x, y) => pre (x, y)) in *.
  eapply r_get_remind_lhs.
  apply H.
  apply H0.
  apply functional_extensionality.
  intros [].
  reflexivity.
Qed.

Lemma isolate_mem_sectiongetr_set_lhs : 
  forall {A B} ℓ v pre post (a : _ -> raw_code A) (b : raw_code B),
  ⊢ ⦃ set_lhs ℓ v pre ⦄
     a v
  ≈
     b
  ⦃ post ⦄ ->
  ⊢ ⦃ set_lhs ℓ v pre ⦄
     x ← get ℓ ;;
     a x
  ≈
     b
  ⦃ post ⦄.
Proof.
  clear.
  intros.

  eapply better_r_get_remind_lhs.
  unfold Remembers_lhs.
  intros ? ? [? []]. subst.
  unfold rem_lhs.
  rewrite get_set_heap_eq.
  reflexivity.
  apply H.
Qed.

Ltac progress_step_code :=    
  match goal with
  | [ |- context [ prog (@is_state ?L ?I _ ?x) : both _ _ _ ] ] =>
      match goal with
      | [ |- context [ ⊢ ⦃ _ ⦄ _ ≈ ?os ⦃ _ ⦄ ] ] =>
          let Hx := fresh in
          set (Hx := x)
          ; try replace (@is_pure _ _ _ _) with (@is_pure _ _ _ Hx) by reflexivity
          ; subst Hx
          ; let H := fresh in
            set (H := os)
            ; pattern (@is_pure L I _ x) in H
            ; set (Hx := x) in *
            ; subst H
            ; apply (@r_bind_trans_both) with (b := Hx)
            ; intros
      end
  end
  || match goal with
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
      apply (better_r_put_lhs l x a b (* (fun '(h0, h1) => heap_ignore fset (h0, h1)) *))
  end
  ||
  rewrite bind_ret
  ||
  apply r_ret.

Ltac step_code :=
  repeat (clear_bind || progress_step_code) ; try (intros ; split ; reflexivity).

(* Ltac heap_ignore_remove_ignore := *)
(*   match goal with *)
(*   | H : heap_ignore ?L ( ?a , ?b ) |- _ => *)
(*       match goal with *)
(*       | [ |- context[ heap_ignore L ( ?c , b ) ] ] => *)
(*           intros ℓ H_mem *)
(*           ; specialize (H ℓ H_mem) *)
(*           ; match goal with *)
(*             | [ |- context[ get_heap (set_heap ?x ?ℓ' ?v) ℓ = get_heap _ ℓ ] ] => *)
(*                 destruct (@eqtype.eq_op (@eqtype.tag_eqType choice_type_eqType *)
(*              (fun _ : choice_type => ssrnat.nat_eqType)) ℓ ℓ') eqn:ℓ_eq_ℓ' *)
(*                 ; [ exfalso *)
(*                     ; apply (ssrbool.elimT eqtype.eqP) in ℓ_eq_ℓ' ; subst *)
(*                     ; apply (ssrbool.elimT ssrbool.negP) in H_mem *)
(*                     ; apply H_mem *)
(*                     ; clear H_mem *)
(*                     ; apply loc_compute *)
(*                     ; unfold eqtype.val *)
(*                     ; rewrite simplify_sorted_fset *)
(*                     ; repeat (reflexivity || (left ; reflexivity) || right) *)
(*                   | rewrite <- (get_heap_set_heap a ℓ ℓ' v) ; *)
(*                     [ assumption *)
(*                     | rewrite ℓ_eq_ℓ' ; reflexivity  *)
(*                     ] *)
(*                 ]      *)
(*             end *)
(*       end *)
(*   end . *)

(* Ltac both_bind := *)
(*   match goal with *)
(*   | [ |- context[ (?x : both ?L ?T) ] ] =>   *)
(*       match goal with *)
(*       | [ |- context[ (bind ?f ?v) ] ] => *)
(*           eapply (r_transR (bind (@is_state _ _ x) v) (bind (lift_to_code (@is_pure _ _ x)) v)) ; *)
(*           [  *)
(*           | eapply r_bind ; [ apply x | ] *)
(*           ] *)
(*       end *)
(*   end. *)


Ltac remove_T_ct :=
  match goal with
  | [ |- context[ T_ct ?x ] ] =>  
      replace (T_ct x) with x by reflexivity
  | H : _ |- context[ T_ct ?x ] =>  
      replace (T_ct x) with x in H by reflexivity
  end.



