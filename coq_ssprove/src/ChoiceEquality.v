From Coq Require Import ZArith List.
From Crypt Require Import choice_type Package.
Import PackageNotation.
From Crypt Require Import pkg_interpreter.
From extructures Require Import ord fset fmap.
Require Import Hacspec_Lib_Comparable.

Require Import LocationUtility.
Require Import Coq.Logic.FunctionalExtensionality.

Import RulesStateProb.
Import RulesStateProb.RSemanticNotation.
Open Scope rsemantic_scope.

(******************************************************************************)
(*   This file defines a class ChoiceEquality, which defines an equality      *)
(* between choice_type and coq types. We also define types both and           *)
(* both_package, which is stateful code/package and a pure value, combined    *)
(* with a proof of equality between the two.                                  *)
(******************************************************************************)

Monomorphic Class ChoiceEquality := {
    T : Type@{choice.Choice.type.u0} ;
    ct : choice_type ;
    ChoiceEq : @eq Type@{choice.Choice.type.u0} (choice.Choice.sort (chElement ct)) T ;
  }.

Arguments T ChoiceEquality : clear implicits.
Arguments ct ChoiceEquality : clear implicits.
Arguments ChoiceEq ChoiceEquality : clear implicits.

Global Coercion T : ChoiceEquality >-> Sortclass.
Global Coercion ct : ChoiceEquality >-> choice_type.

Definition ct_T {ce : ChoiceEquality} (x : choice.Choice.sort (ct ce)) : T ce :=
  eq_rect (choice.Choice.sort (chElement (ct ce))) id x (T ce) (ChoiceEq _).

Definition T_ct {ce : ChoiceEquality} (x : T ce) : choice.Choice.sort (ct ce) :=
  eq_rect_r id x (ChoiceEq _).

Theorem ct_T_id : forall {ce : ChoiceEquality} t, ct_T (T_ct t) = t.
Proof (fun ce => rew_opp_r id (ChoiceEq ce)).

Theorem T_ct_id : forall {ce : ChoiceEquality} t, T_ct (ct_T t) = t.
Proof (fun ce => rew_opp_l id (ChoiceEq ce)).

Global Coercion ct_T : choice.Choice.sort >-> T.
Global Coercion T_ct : T >-> choice.Choice.sort.


Lemma ChoiceEquality_ct_EqP : forall ce1 ce2, ce1 = ce2 <-> ct ce1 = ct ce2.
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

Program Instance prod_ChoiceEquality (a b : ChoiceEquality) : ChoiceEquality :=
  {| T := (@T a) * (@T b) ; ct := (@ct a) × (@ct b); |}.
Next Obligation.
  intros.
  do 2 rewrite ChoiceEq.
  reflexivity.
Defined.

Notation "A '× B" := (prod_ChoiceEquality A B) (at level 79, left associativity) : hacspec_scope.

Notation "prod_ce( a , b )" := ((a , b) : prod_ChoiceEquality _ _) : hacspec_scope.
Notation "prod_ce( a , b , .. , c )" := ((.. ((a , b) : prod_ChoiceEquality _ _) .. , c) : prod_ChoiceEquality _ _) : hacspec_scope.

Program Instance sum_ChoiceEquality (a b : ChoiceEquality) : ChoiceEquality :=
  {| T := (@T a) + (@T b) ; ct := (@ct a) ∐ (@ct b); |}.
Next Obligation.
  intros.
  do 2 rewrite ChoiceEq.
  reflexivity.
Defined.

Notation "A '+ B" := (sum_ChoiceEquality A B) (at level 79, left associativity) : hacspec_scope.

Open Scope hacspec_scope.

Definition fst_CE {A B} (p : A '× B) : A := let '(f,s) := p in f.
Definition snd_CE {A B} (p : A '× B) : B := let '(f,s) := p in s.


Theorem T_ct_id_prod : forall {ceA ceB : ChoiceEquality} a b, @T_ct (prod_ChoiceEquality ceA ceB) (@ct_T ceA a , @ct_T ceB b) = (a , b).
Proof. now intros [? ? []] [? ? []]. Qed.

Theorem T_ct_prod_propegate : forall {ceA ceB : ChoiceEquality} a b, @T_ct (prod_ChoiceEquality ceA ceB) (a , b) = (T_ct a , T_ct b).
Proof. now intros [? ? []] [? ? []]. Qed.

Theorem ct_T_prod_propegate : forall {ceA ceB : ChoiceEquality} a b,
    @ct_T (prod_ChoiceEquality ceA ceB) (a , b) = (ct_T a , ct_T b).
Proof. now intros [? ? []] [? ? []]. Qed.

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
Definition pre_to_post_ret (P : precond) {A} v : postcond A A :=
  fun '(a, h₀) '(b, h₁) => (a = b /\ b = v) /\ P (h₀ , h₁).

Definition true_precond : precond := fun _ => True.

Class both L I (A : ChoiceEquality) :=
  {
    is_pure : A ;
    is_state : code L I (@ct A) ;
    code_eq_proof_statement :
    ⊢ ⦃ true_precond ⦄
          is_state ≈ lift_to_code (L := L) (I := I) (is_pure)
      ⦃ pre_to_post_ret true_precond (T_ct is_pure) ⦄
  }.

Arguments is_pure {_} {_} {_} both.
Arguments is_state {_} {_} {_} both.
Arguments code_eq_proof_statement {_} {_} {_} both.

Coercion is_pure : both >-> T.
Coercion is_state : both >-> code.

Definition opsigCE := ident * (ChoiceEquality * ChoiceEquality).
Definition InterfaceCE := list opsigCE.

Definition opsigCE_opsig := (fun '(i, (s, t)) => (i : ident, (ct s, ct t))).
Definition IfToCEIf (x : InterfaceCE) : Interface := fset (map opsigCE_opsig x).

Lemma helper :
  forall (o : opsigCE),
    choice.Choice.sort (fst (snd o)) = choice.Choice.sort (src (opsigCE_opsig o)).
Proof. now intros [? []]. Qed.

Lemma pack_helper :
  forall {E : InterfaceCE} {o} (H : In o E),
    is_true
   (ssrbool.in_mem (opsigCE_opsig o)
      (ssrbool.mem (IfToCEIf E))).
Proof.
  intros.
  apply (ssrbool.introT (xseq.InP _ _)).
  unfold IfToCEIf.
  apply -> (in_remove_fset (T:=opsig_ordType)).
  apply in_map.
  apply H.
Defined.

Class both_package L I (E : InterfaceCE) :=
  {
    pack_pure : forall o, List.In o E -> fst (snd o) -> snd (snd o) ;
    pack_state : package L I (IfToCEIf E) ;
    pack_eq_proof_statement : forall i s t (H : In (i,(s,t)) E), forall (v : s),
      forall f, (pack pack_state) i = Some
    (existT
       (fun S0 : choice_type => {T0 : choice_type & choice.Choice.sort S0 -> raw_code T0})
       s (existT (fun T0 : choice_type => choice.Choice.sort s -> raw_code T0) t f)) ->
      ⊢ ⦃ true_precond ⦄
          f v
          ≈ lift_to_code (L := L) (I := I) (pack_pure (i,(s,t)) H v)
      ⦃ pre_to_post_ret true_precond (T_ct (pack_pure (i,(s,t)) H v)) ⦄
  }.

Arguments pack_pure {_} {_} {_} {_} {_} {_} both_package.
Arguments pack_state {_} {_} {_} both_package.

Coercion pack_pure : both_package >-> Funclass.
Coercion pack_state : both_package >-> package.

Instance package_both {L I} {x y z} (pkg : both_package L I ((x, (y, z)) :: nil)) (args : y)
  : both L I (z).
Proof.
  destruct pkg as [pure state eq_proof].
  pose (o := (x, (y, z)) : opsigCE).
  Check pack_eq_proof_statement.
  refine {| is_pure := pure o (List.in_eq _ _) args ;
           is_state := {code get_op_default state (opsigCE_opsig o) (args) #with valid_get_op_default _ _ _ state (opsigCE_opsig o) (args) _ (pack_helper (List.in_eq _ _)) } |}.
  apply eq_proof.
  cbn.
  destruct (from_valid_package _ _ _ _ (pack_valid state) (opsigCE_opsig o) (pack_helper (List.in_eq _ _))) as [? []].
  rewrite H.
  apply f_equal.
  apply f_equal.
  apply f_equal.
  unfold get_op_default.
  cbn.
  rewrite H.
  destruct choice_type_eqP ; [ | contradiction ].
  destruct choice_type_eqP ; [ | contradiction ].
  rewrite pkg_composition.cast_fun_K.
  reflexivity.
Defined.

Program Instance both_package' L I o (bf : T (fst (snd o)) -> both L I (snd (snd o)))
  : both_package L I (o :: nil) :=
  {|
    pack_pure := fun o0 H => ltac:((assert (o = o0) by now destruct H) ; subst ; apply bf ; apply X) ;
    pack_state := (mkpackage (mkfmap ((fst o, pkg_composition.mkdef _ _ (fun x => bf (ct_T x))) :: nil)) (valid_package1 L I (fst o) (fst (snd o)) (snd (snd o)) (fun x => bf (ct_T x)) (fun x => prog_valid (is_state (bf (ct_T x)))))) ;
    pack_eq_proof_statement := _
  |}.
Next Obligation.
  intros.
  destruct H ; [ subst | contradiction ].
  cbn in H0.
  rewrite (ssrbool.introT ssrnat.eqnP eq_refl) in H0.
  inversion H0.
  do 2 apply Eqdep.EqdepTheory.inj_pair2 in H1.
  subst.
  cbn.
  rewrite ct_T_id.
  apply bf.
Defined.

Program Definition lift_to_both {ce : ChoiceEquality} {L I} (x : @T ce) : both L I ce :=
  {| is_pure := x ; is_state := @lift_to_code ce L I x |}.
Next Obligation. intros. apply r_ret. intros. easy. Qed.

Definition both0 (A : ChoiceEquality) := both fset.fset0 [interface] A.
Definition lift_to_both0 {ce : ChoiceEquality} (x : T ce) : both fset.fset0 [interface] ce := lift_to_both x.

Definition lift_code_scope {L1 L2 : {fset Location}} {I1 I2 : {fset opsig}} {A} (c : code L1 I1 A) `{H_loc_incl : List.incl L1 L2} `{H_opsig_incl : List.incl I1 I2} : code L2 I2 A :=
  {code (prog c) #with
    (@valid_injectMap L2 A I1 I2 _ (proj2 (opsig_list_incl_fsubset _ _) H_opsig_incl) (@valid_injectLocations I1 A L1 L2 _ (proj2 (loc_list_incl_fsubset _ _) H_loc_incl) (prog_valid c))) }.

Definition lift_scope {L1 L2 : {fset Location}} {I1 I2 : {fset opsig}} {A} (b : both L1 I1 A) `{H_loc_incl : List.incl L1 L2} `{H_opsig_incl : List.incl I1 I2} : both L2 I2 A :=
  {|
    is_pure := is_pure b ;
    is_state := lift_code_scope (H_loc_incl := H_loc_incl) (H_opsig_incl := H_opsig_incl) (is_state b) ;
    code_eq_proof_statement := code_eq_proof_statement b
  |}.
Definition lift_scopeI
  {L1 L2 : {fset Location}} {I : {fset opsig}} {A} (b : both L1 I A) `{H_loc_incl : List.incl L1 L2} : both L2 I A :=
  {|
    is_pure := is_pure b ;
    is_state := lift_code_scope (H_loc_incl := H_loc_incl) (H_opsig_incl := incl_refl _) (is_state b) ;
    code_eq_proof_statement := code_eq_proof_statement b
  |}.

Definition lift_scope0 {L I} {A} (b : both fset.fset0 [interface] A) : both L I A :=
  lift_scope (H_loc_incl := incl_nil_l _) (H_opsig_incl := ltac:(rewrite <- fset0E ; apply incl_nil_l)) b.

Instance both_comparable {A : ChoiceEquality} `{Comparable A} {L I} : Comparable (both L I A) :=
  {|
    ltb x y := ltb (is_pure x) (is_pure y) ;
    leb x y := leb (is_pure x) (is_pure y) ;
    gtb x y := gtb (is_pure x) (is_pure y) ;
    geb x y := geb (is_pure x) (is_pure y)
  |}.

Theorem forget_precond {B} (x y : raw_code B) P Q :
  ⊢ ⦃ true_precond ⦄ x ≈ y ⦃ Q ⦄ ->
  ⊢ ⦃ P ⦄ x ≈ y ⦃ Q ⦄.
Proof.
  intros.
  now apply (rpre_weaken_rule _ _ _ H).
Qed.

Program Instance prod_both {ceA ceB : ChoiceEquality} {L1 L2 : {fset _}} {I1 I2 : {fset _}} (a : both L1 I1 ceA) (b : both L2 I2 ceB) : both (L1 :|: L2) (I1 :|: I2) (ceA '× ceB) :=
  {|
    is_pure := (is_pure a , is_pure b) ;
    is_state :=
    {code
       x ← a ;;
       y ← b ;;
       @ret (prod_ChoiceEquality _ _) (x , y)
    }
  |}.
Next Obligation.
  intros.
  ssprove_valid.
  apply valid_injectLocations with (L1 := L1). apply fsubsetUl.
  apply @valid_injectMap with (I1 := I1). apply fsubsetUl.
  apply (is_state a).

  apply valid_injectLocations with (L1 := L2). apply fsubsetUr.
  apply @valid_injectMap with (I1 := I2). apply fsubsetUr.
  apply (is_state b).
Defined.
Next Obligation.
  intros.
  rewrite (T_ct_prod_propegate).

  set (r := ret _).
  pattern (T_ct (is_pure a)) in r.
  set (g := fun _ => _) in r.
  subst r.
  replace (g a) with (bind (ret a) g) by reflexivity.
  subst g. hnf.

  eapply r_bind ; [ apply (code_eq_proof_statement a) | ].
  intros.
  apply rpre_hypothesis_rule.
  intros ? ? [[] []]. subst.
  apply forget_precond.

  set (r := ret _).
  pattern (T_ct (is_pure b)) in r.
  set (g := fun _ => _) in r.
  subst r.
  replace (g b) with (bind (ret b) g) by reflexivity.
  subst g. hnf.

  eapply r_bind ; [ apply (code_eq_proof_statement b) | ].
  intros.
  apply rpre_hypothesis_rule.
  intros ? ? [[] []]. subst.
  apply forget_precond.

  apply r_ret.
  intros ? ? []. easy.
Defined.
Notation "prod_b( a , b )" := (prod_both a b) : hacspec_scope.
Notation "prod_b( a , b , .. , c )" := (prod_both .. (prod_both a b) .. c) : hacspec_scope.

Ltac ssprove_valid_fset T :=
  apply (fset_compute (T:=T)) ; try apply -> (in_remove_fset (T:=T)) ; repeat (try (left ; reflexivity) ; right) ; try reflexivity.

Ltac ssprove_valid_location := ssprove_valid_fset loc_ordType.
Ltac ssprove_valid_opsig := ssprove_valid_fset opsig_ordType.

Ltac ssprove_valid_program :=
  try (apply prog_valid) ;
  try (apply valid_scheme ; try rewrite <- fset.fset0E ; apply prog_valid).

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
         end ;
  cbv zeta.

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

Ltac loc_incl_compute :=
  now (try apply -> loc_list_incl_remove_fset ; apply loc_list_incl_expand ; (now repeat (split ; [ repeat ((left ; reflexivity) || (right)) | ]))).

Ltac opsig_incl_compute :=
  now (try apply -> opsig_list_incl_remove_fset ; apply opsig_list_incl_expand ; (now repeat (split ; [ repeat ((left ; reflexivity) || (right)) | ]))).

Lemma valid_subset_fset :
  forall xs ys I {ct} c,
    List.incl (xs) (ys) ->
    ValidCode (fset xs) I c ->
    @ValidCode (fset ys) I ct c.
Proof.
  intros.
  apply (valid_injectLocations) with (L1 := fset xs).
  - apply loc_list_incl_fsubset.
    apply -> loc_list_incl_remove_fset.
    apply H.
  - apply H0.
Qed.

Lemma valid_subset :
  forall (xs ys : {fset Location}) I {ct} c,
    List.incl (xs) (ys) ->
    ValidCode (xs) I c ->
    @ValidCode (ys) I ct c.
Proof.
  intros.
  apply (valid_injectLocations) with (L1 := xs).
  - apply loc_list_incl_fsubset.
    apply H.
  - apply H0.
Qed.

Ltac valid_program :=
  apply prog_valid
  || (apply valid_scheme ; try rewrite <- fset.fset0E ; apply prog_valid)
  || (eapply (valid_subset_fset) ; [ | apply prog_valid ] ; loc_incl_compute).


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
  apply H0.
  intros. cbn.
  apply (heap_ignore_weaken fset fset') ; assumption.
Qed.

Theorem bind_rewrite : forall A B x f, @bind A B (ret x) f = f x.
Proof.
  intros.
  unfold bind.
  reflexivity.
Qed.

Theorem r_bind_eq : forall {B C : ChoiceEquality} (y : B) (g : choice.Choice.sort B  -> raw_code C), (temp ← ret y ;; g temp) = g y.
Proof. reflexivity. Qed.

Theorem r_bind_trans :
  forall {B C : ChoiceEquality}
     (f : choice.Choice.sort B -> raw_code C)
    (g : B -> raw_code C) (x : raw_code B) (y : B),
  forall (P P_mid : precond) (Q : postcond (choice.Choice.sort C) (choice.Choice.sort C)),
  forall (H_x_is_y : ⊢ ⦃ P ⦄ x  ≈ ret y ⦃ pre_to_post_ret P_mid (T_ct y) ⦄),
    (⊢ ⦃ P_mid ⦄ f (T_ct y)  ≈ g y ⦃ Q ⦄) ->
    ⊢ ⦃ P ⦄ temp ← x ;; f temp ≈ g y ⦃ Q ⦄.
Proof.
  intros.
  rewrite <- (ct_T_id y).
  replace (g (ct_T (T_ct y))) with (temp ← ret (T_ct y) ;; g (ct_T temp)) by reflexivity.

  pose @r_bind.
  specialize r with (f₀ := f) (f₁ := fun x => g (ct_T x)).
  specialize r with (m₀ := x) (m₁ := (ret (T_ct y))).
  specialize r with (pre := P) (mid := pre_to_post_ret P_mid (T_ct y) ) (post := Q).
  apply r ; clear r.

  - apply H_x_is_y.
  - intros.
    eapply rpre_hypothesis_rule.
    intros ? ? [[] ?]. subst.
    eapply rpre_weaken_rule.
    cbn in H2.
    subst.
    rewrite ct_T_id.
    apply H.
    intros ? ? []. subst. apply H2.
Qed.

Theorem r_bind_trans' :
  forall {B C : ChoiceEquality}
     (f : choice.Choice.sort B -> raw_code C)
    (g : B -> raw_code C) (x : raw_code B) (y : B),
  forall (P : precond) (Q : postcond (choice.Choice.sort C) (choice.Choice.sort C)),
  forall (H_x_is_y : ⊨ repr x ≈ repr (ret (T_ct y)) [{retW (T_ct y, T_ct y)}]),
    (⊢ ⦃ P ⦄ f (T_ct y)  ≈ g y ⦃ Q ⦄) ->
    ⊢ ⦃ P ⦄ temp ← x ;; f temp ≈ g y ⦃ Q ⦄.
Proof.
  intros.

  rewrite <- (ct_T_id y).

  replace (g (ct_T (T_ct y))) with (temp ← ret (T_ct y) ;; g (ct_T temp)) by reflexivity.

  pose @r_bind.
  specialize r with (f₀ := f) (f₁ := fun x => g (ct_T x)).
  specialize r with (m₀ := x) (m₁ := (ret (T_ct y))).
  specialize r with (pre := P) (mid := fun s0 s1 => pre_to_post P s0 s1 /\ fst s1 = T_ct y) (post := Q).
  apply r ; clear r.

  - eapply from_sem_jdg.
    eapply (RulesStateProb.weaken_rule (retW (T_ct y , T_ct y))).
    + apply H_x_is_y.
    + unfold retW.
      intros [] X [? πa1a2] ; cbn in X.
      specialize (fun x => πa1a2 (x, s) (T_ct y, s0)).

      unfold proj1_sig.

      unfold RulesStateProb.WrelSt.
      unfold θ.
      unfold StateTransformingLaxMorph.rlmm_codomain ; simpl.

      apply πa1a2.
      split.
      cbn.
      split.
      reflexivity.
      2: { reflexivity. }
      apply H0.
  - intros.
    eapply rpre_hypothesis_rule.
    intros ? ? [[] ?]. subst.
    eapply rpre_weaken_rule.
    2: { intros ? ? []. subst. apply H1. }
    clear H1.
    cbn in H2.
    subst.
    rewrite ct_T_id.
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
  apply fset_compute. apply in_split_fset_cat ; left ; apply in_split_fset_cat ; right.
  apply fset_compute. apply H.
Qed.

Ltac solve_heap_ignore_remove_set_heap :=
  apply (heap_ignore_remove_set_heap) ; [ apply isolate_mem_section ; apply fset_compute ; apply -> in_remove_fset ; cbn ; repeat (left ; reflexivity || right || reflexivity) | assumption ].

Theorem r_bind_trans_both : forall {B C : ChoiceEquality} {L I} {f : choice.Choice.sort B -> raw_code C} {g : B -> raw_code C} (b : both L I B),
  forall (P : precond) (Q : postcond _ _),
    (⊢ ⦃ true_precond ⦄ f (T_ct (is_pure b))  ≈ g (is_pure b) ⦃ Q ⦄) ->
    ⊢ ⦃ P ⦄ temp ← is_state b ;; f temp ≈ g (is_pure b) ⦃ Q ⦄.
Proof.
  intros.
  apply r_bind_trans with (P_mid := true_precond).

  eapply rpre_weaken_rule.
  apply code_eq_proof_statement.
  reflexivity.

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

Corollary better_r :
  forall {A B : choice.Choice.type}
    (r₀ : raw_code A)
    (r₁ : raw_code B) (pre : precond)
    (post : postcond (choice.Choice.sort A) (choice.Choice.sort B)),
    ⊢ ⦃ fun '(s₀, s₁) => pre (s₀, s₁) ⦄ r₀ ≈ r₁ ⦃ post ⦄ <->
      ⊢ ⦃ pre ⦄ r₀ ≈ r₁ ⦃ post ⦄.
Proof.
  split ; intros ; (eapply rpre_hypothesis_rule ; intros ; eapply rpre_weaken_rule ; [ apply H | intros ? ? [] ; subst ; easy ]).
Qed.

Corollary better_r_put_lhs : forall {A B : choice.Choice.type} (ℓ : Location)
       (v : choice.Choice.sort (Value (projT1 ℓ))) (r₀ : raw_code A)
       (r₁ : raw_code B) (pre : precond)
       (post : postcond (choice.Choice.sort A) (choice.Choice.sort B)),
     ⊢ ⦃ set_lhs ℓ v pre ⦄ r₀ ≈ r₁ ⦃ post ⦄ ->
     ⊢ ⦃ pre ⦄ #put ℓ := v ;; r₀ ≈ r₁ ⦃ post ⦄.
Proof.
  intros ; now apply better_r, r_put_lhs, better_r.
Qed.

Corollary better_r_put_get : forall (A : choice.Choice.type) (ℓ : Location) (v : choice.Choice.sort ℓ) (r : choice.Choice.sort ℓ -> raw_code A) rhs (pre : precond) (post : postcond (choice.Choice.sort A) (choice.Choice.sort A)),
    ⊢ ⦃ pre ⦄
     #put ℓ := v ;;
     r v ≈ rhs ⦃ post ⦄ ->
    ⊢ ⦃ pre ⦄
        #put ℓ := v ;;
        x ← get ℓ ;;
        r x ≈ rhs ⦃ post ⦄.
Proof.
  intros.
  apply (r_transL (#put ℓ := v ;; r v )).
  apply r_put_get.
  apply H.
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
  apply better_r.
  eapply r_get_remind_lhs.
  apply H.
  apply better_r.
  apply H0.
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

Ltac remove_T_ct :=
  progress match goal with
  | [ |- context[ T_ct ?x ] ] =>
      replace (T_ct x) with x by reflexivity
  end.

Ltac pattern_both Hx Hf Hg :=
  (match goal with
   | [ |- context [ prog (@is_state ?L ?I _ ?x) : both _ _ _ ] ] =>
       set (Hx := x)
       ; try replace (@is_pure _ _ _ _) with (@is_pure _ _ _ Hx) by reflexivity
       ; match goal with
         | [ |- context [ ⊢ ⦃ _ ⦄ bind _ ?fb ≈ ?os ⦃ _ ⦄ ] ] =>
             let H := fresh in
             set (H := os)
             ; pattern (@is_pure L I _ Hx) in H
             ; subst H
             ; set (Hf := fb)
             ; match goal with
               | [ |- context [ ⊢ ⦃ _ ⦄ _ ≈ ?gb _ ⦃ _ ⦄ ] ] =>
                   set (Hg := gb)
               end
         end
   end).

Ltac pattern_both_fresh :=
  let x := fresh in
  let y := fresh in
  let z := fresh in
  pattern_both x y z.

Ltac match_bind_trans_both :=
  let Hx := fresh in
  let Hf := fresh in
  let Hg := fresh in
  repeat remove_T_ct
  ; pattern_both Hx Hf Hg
  ; apply (@r_bind_trans_both) with (b := Hx) (f := Hf) (g := Hg)
  ; intros ; try remove_T_ct ; subst Hf ; subst Hg ; subst Hx ; hnf.
