Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
     fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool
     ssrnum eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

Require Import List.
Set Warnings "-notation-overridden".
From Jasmin Require Import expr.
Set Warnings "notation-overridden".
From Jasmin Require Import x86_instr_decl x86_extra.
From JasminSSProve Require Import jasmin_translate.
From Crypt Require Import Prelude Package.

Import ListNotations.
Local Open Scope string.

Set Bullet Behavior "Strict Subproofs".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.
Require Import micromega.Lia.
From mathcomp.word Require Import word ssrZ.
From JasminSSProve Require Import aes_jazz jasmin_utils.
From JasminSSProve Require Import aes_utils.
Import JasminNotation JasminCodeNotation.
Import PackageNotation.

From Hacspec Require Import Hacspec_Aes_Jazz ChoiceEquality Hacspec_Lib Hacspec_Lib_Pre Hacspec_Lib_Comparable.
Open Scope hacspec_scope.

#[global] Hint Resolve preceq_I preceq_O preceq_refl : preceq.

From Hacspec Require Import Hacspec_Lib.

From mathcomp Require Import zify_ssreflect zify_algebra zify.
Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Section Hacspec.

(*** Helper definitions *)

  (* NB: this redefines neq_loc_auto, which helps some tactics, since checking for inequality by computation is not feasible for translated variables *)
  Ltac neq_loc_auto ::= solve [ eapply injective_translate_var3; auto | eapply injective_translate_var2; auto ].

  Ltac destruct_pre :=
    repeat
      match goal with
      | [ H : set_lhs _ _ _ _ |- _ ] =>
          let sn := fresh in
          let Hsn := fresh in
          destruct H as [sn [Hsn]]
      | [ H : set_rhs _ _ _ _ |- _ ] =>
          let sn := fresh in
          let Hsn := fresh in
          destruct H as [sn [Hsn]]
      | [ H : _ /\ _ |- _ ] =>
          let H1 := fresh in
          let H2 := fresh in
          destruct H as [H1 H2]
      | [ H : (_ ⋊ _) _ |- _ ] =>
          let H1 := fresh in
          let H2 := fresh in
          destruct H as [H1 H2]
      | [ H : exists _, _ |- _ ] =>
          let o := fresh in
          destruct H as [o]
      end; simpl in *; subst.


  Lemma det_jkey id0 rcon rkey temp2 : deterministic (JKEY_COMBINE id0 rcon rkey temp2).
  Proof.
    unfold translate_call, translate_call_body.
    Opaque translate_call.
    simpl.

    repeat (apply deterministic_put || (apply deterministic_get ; intros) || apply deterministic_ret).
    Transparent translate_call.
  Defined.


  Lemma det_key_combine rcon rkey temp2 : deterministic (is_state (key_combine rcon rkey temp2)).
  Proof.
    repeat (apply deterministic_put || (apply deterministic_get ; intros) || apply deterministic_ret).
  Defined.

  Lemma unfold_det_run : forall {A : choiceType} c [h : @deterministic A c] s, @det_run A c h s = match h with
                                                                                             | deterministic_ret x => (x, s)
                                                                                             | deterministic_get ℓ k hk => det_run (k (get_heap s ℓ)) (h := hk _) s
                                                                                             | deterministic_put ℓ v k hk => det_run k (h := hk) (set_heap s ℓ v)
                                                                                             end.
  Proof. destruct h ; reflexivity. Qed.

  Ltac bind_jazz_hac :=
    match goal with
    | [ |- context [ ⊢ ⦃ ?P ⦄ putr ?l ?jazz ?f ≈ _ ⦃ ?Q ⦄ ] ] =>
        eapply (@r_bind _ _ _ _ (ret jazz) _ (fun x => putr l x f) _ _ (fun '(v0, h0) '(v1, h1) => v0 = v1 /\ P (h0, h1)) _) ; [ try rewrite !zero_extend_u | intros ]
    end.

  Ltac remove_get_in_lhs :=
    eapply better_r_get_remind_lhs ;
    unfold Remembers_lhs , rem_lhs ;
    [ intros ? ? ? ;
      destruct_pre ;
      repeat (rewrite get_set_heap_neq ; [ | apply injective_translate_var3 ; reflexivity ]) ;
      rewrite get_set_heap_eq ;
      reflexivity | ].

  Theorem shiftr_bounds : forall x y z,
      (0 <= y)%Z ->
      (0 <= x < modulus (z+Z.to_nat y))%Z ->
      (0 <= Z.shiftr x y < modulus z)%Z.
  Proof.
    intros.
    rewrite Z.shiftr_div_pow2.
    2:{ cbn. lia. }
    assert (modulus (z + Z.to_nat y) / 2 ^ y = modulus z)%Z.
    {
      unfold modulus.
      rewrite two_power_nat_correct.
      rewrite two_power_nat_correct.
      rewrite Zpower_nat_Z.
      rewrite Zpower_nat_Z.
      rewrite Nat2Z.inj_add.
      rewrite Z2Nat.id ; [ | assumption].

      rewrite <- Z.pow_sub_r ; [ now rewrite Z.add_simpl_r | lia | ].
      split. assumption.
      lia.
    }
    split.
    - apply Z_div_nonneg_nonneg ; lia.
    - apply (Z.div_lt_upper_bound).
      lia.
      eapply Z.lt_le_trans.
      apply H0.
      rewrite Z.mul_comm.
      unfold modulus.
      rewrite two_power_nat_correct.
      rewrite two_power_nat_correct.
      rewrite Zpower_nat_Z.
      rewrite Zpower_nat_Z.
      rewrite <- Z.pow_add_r.
      cbn.
      rewrite Nat2Z.inj_add.
      rewrite Z2Nat.id.
      lia.
      cbn. lia.
      cbn. lia.
      cbn. lia.
  Qed.

  Theorem shiftl_bounds : forall x (y z : nat),
      (y <= z)%Z ->
      (0 <= x < modulus (z - y))%Z ->
      (0 <= Z.shiftl x y < modulus z)%Z.
  Proof.
    intros.
    rewrite Z.shiftl_mul_pow2.
    2:{ cbn. lia. }
    assert (modulus (z - y) * 2 ^ y = modulus z)%Z.
    {
      unfold modulus.
      rewrite two_power_nat_correct.
      rewrite two_power_nat_correct.
      rewrite Zpower_nat_Z.
      rewrite Zpower_nat_Z.
      rewrite <- Z.pow_add_r ; [ | lia | cbn ; lia ].
      f_equal.
      rewrite Nat2Z.inj_sub.
      rewrite Z.sub_simpl_r.
      reflexivity.
      apply Nat2Z.inj_le.
      apply H.
    }
    split.
    - apply Z.mul_nonneg_nonneg ; lia.
    - rewrite <- H1.
      rewrite <- (Z.mul_lt_mono_pos_r).
      lia.
      cbn.
      lia.
  Qed.

  Theorem shiftr_smaller : forall x y n,
      (0 <= y)%Z ->
      (0 <= x < modulus (n + Z.to_nat y))%Z ->
      Z.shiftr x y = (Z.shiftr x y mod modulus n)%Z.
  Proof.
    intros.
    rewrite Zmod_small.
    2:{
      apply shiftr_bounds.
      - apply H.
      - apply H0.
    }
    reflexivity.
  Qed.

  Notation JVSHUFPS i rkey temp1 temp2 := (trc VSHUFPS i [('word U128 ; rkey) ; ('word U128 ; temp1) ; ('word U128 ; temp2)]).

  Lemma modulus_gt0_Z :
    forall n, (0 < modulus n)%Z.
  Proof. easy. Qed.

  Lemma modulus_ge0_Z :
    forall n, (0 <= modulus n)%Z.
  Proof. easy. Qed.

  Lemma isword_Z : forall n k, (0 <= @toword n k < modulus n)%Z.
  Proof.
    apply (fun n k => ssrbool.elimT (iswordZP n (toword k)) (@isword_word n k)).
  Qed.

  Lemma lt_add_right : forall n m p, (0 < p)%Z -> (n < m)%Z -> (n < m + p)%Z.
  Proof.
    intros.
    eapply Z.lt_trans.
    apply H0.
    lia.
  Qed.

  Lemma le_add_right : forall n m p, (0 <= p)%Z -> (n <= m)%Z -> (n <= m + p)%Z.
  Proof.
    intros.
    eapply Z.le_trans.
    apply H0.
    lia.
  Qed.

  Lemma modulusDZ : forall n m p, (n <= modulus (m + p)%nat)%Z = (n <= modulus m * modulus p)%Z .
  Proof.
    intros.
    rewrite modulusD.
    rewrite mulZE.
    reflexivity.
  Qed.

  Lemma modulus_add_r : forall n m p, (0 <= n < modulus m)%Z -> (0 <= n < modulus (m + p)%nat)%Z.
  Proof.
    intros.
    destruct n as [ | n | ] ; [ easy | | easy ].
    rewrite modulusD.
    rewrite <- mulZE.
    split. easy.
    induction p.
    - rewrite Z.mul_1_r.
      apply H.
    - rewrite modulusS.
      rewrite GRing.Theory.mulr2n.
      rewrite <- addZE.
      eapply Z.lt_trans.
      apply IHp.
      apply Zmult_lt_compat_l.
      easy.
      apply Z.lt_add_pos_r.
      easy.
  Qed.

  Lemma small_modulus_smaller : forall n m p, (0 <= n)%Z -> (0 < m <= p)%Z -> (0 <= n mod m < p)%Z.
  Proof.
    intros.
    split. apply Z_mod_nonneg_nonneg. apply H. apply Z.lt_le_incl. apply H0.
    eapply Z.lt_le_trans.
    apply Z.mod_pos_bound.
    lia.
    apply H0.
  Qed.

  Lemma mod_mod_larger : forall n m p, (0 <= n)%Z -> (0 < m <= p)%Z -> (n mod m mod p = n mod m)%Z.
  Proof.
    intros.
    rewrite Zmod_small.
    reflexivity.
    apply small_modulus_smaller.
    apply H.
    apply H0.
  Qed.

  Lemma mod_mod_divisable : forall n m p, (0 < p)%Z -> (exists k, m = k * p /\ 0 < k)%Z -> (n mod m mod p = n mod p)%Z.
  Proof.
    intros.
    destruct H0 as [ ? [] ].
    subst.
    now apply mod_pq_mod_q.
  Qed.


  Lemma Z_shiftl_mod_modulus_S : forall n (m p : nat),
      (Z.shiftl n (Z.of_nat m.+1) mod modulus (p.+1) = 2 * (Z.shiftl n (Z.of_nat m) mod modulus p))%Z.
  Proof.
    intros.
    rewrite <- Zmult_mod_distr_l.

    f_equal.
    {
      rewrite Z.shiftl_mul_pow2.
      rewrite Nat2Z.inj_succ.
      rewrite Z.pow_succ_r.
      rewrite Z.mul_comm.
      rewrite <- Z.mul_assoc.
      rewrite <- (Z.mul_comm n).
      rewrite <- Z.shiftl_mul_pow2.
      reflexivity.

      lia.
      lia.
      lia.
    }
  Qed.

  Lemma Z_shiftl_mod_modulus_add : forall n (m p k : nat),
      (Z.shiftl n (Z.of_nat (m + k)) mod modulus (p + k) = modulus k * (Z.shiftl n (Z.of_nat m) mod modulus p))%Z.
  Proof.
    intros.
    induction k.
    - rewrite !addn0.
      rewrite Z.mul_1_l.
      reflexivity.
    - rewrite !addnS.
      rewrite Z_shiftl_mod_modulus_S.
      rewrite IHk.
      rewrite Z.mul_assoc.
      reflexivity.
  Qed.

  Lemma subn_diag : forall p m, m <= p -> p = p - m + m.
  Proof.
    intros.
    pose subn_eq0.
    pose (@subnA p m m (leqnn m) H).
    epose (addKn m 0).
    setoid_rewrite addn0 in e1.
    setoid_rewrite e1 in e0.
    now rewrite (subn0 p) in e0.
  Qed.

  Lemma Z_shiftl_mod_modulus : forall n (m p k : nat), (m <= p) -> (Z.shiftl n (Z.of_nat m) mod modulus p = modulus m * (n mod modulus (p - m)))%Z.
  Proof.
    intros.
    replace p with (p - m + m) at 1 by now rewrite <- (subn_diag p m H).
    replace (m) with (0 + m) at 1 by reflexivity.
    apply Z_shiftl_mod_modulus_add.
  Qed.

  Ltac solve_lower_bounds :=
    (simple apply Z.mul_nonneg_nonneg || simple apply Zle_0_pos || simple apply Z_mod_nonneg_nonneg || simple apply Nat2Z.is_nonneg || simple apply modulus_ge0_Z || simple apply (fun x y => proj2 (Z.shiftr_nonneg x y)) || simple apply (fun x y => proj2 (Z.shiftl_nonneg x y)) || simple apply word_geZ0 || (apply Z.lor_nonneg ; solve_upper_bound))
      with
      solve_upper_bound :=
      ((split ; [ repeat solve_lower_bounds | ]) || (apply small_modulus_smaller ; now repeat solve_lower_bounds) || (rewrite <- (Z.mul_lt_mono_pos_l) ; [ | easy]) || apply isword_Z || (apply shiftr_bounds ; repeat solve_lower_bounds) || apply modulus_add_r || rewrite Z.shiftr_0_r || lia).

  Lemma shift_left_4_byte_ok :
    (forall i (a : 'word U32),
        i < 4 ->
        (0 <= Z.shiftl (wunsigned a) (Z.of_nat (i * 32)) <
           modulus (wsize_size_minus_1 U128).+1)%Z).
  Proof.
    clear.
    destruct a.
    unfold wunsigned, urepr, val, word_subType, word.toword.
    apply (ssrbool.elimT (iswordZP _ _)) in i0.
    split. apply Z.shiftl_nonneg. lia.
    destruct i0.
    rewrite Z.shiftl_mul_pow2 ; [ | lia].
    eapply Z.lt_le_trans.
    rewrite <- (@Z.mul_lt_mono_pos_r (2 ^ Z.of_nat _) toword) ; [ | lia ].
    apply H1.
    destruct i as [ | [ | [ | [ | []] ]] ] ; easy.
  Qed.

  Lemma num_smaller_if_modulus_le : (forall {WS} (x : 'word WS) z, (modulus WS <= z)%Z -> (0 <= x < z)%Z).
  Proof.
    cbn.
    intros.
    split.
    - apply isword_Z.
    - eapply Z.lt_le_trans ; [ apply isword_Z | apply H ].
  Qed.

  Lemma Z_lor_pow2 : (forall (x y : Z) (k : nat), (0 <= x < 2 ^ k)%Z -> (0 <= y < 2 ^ k)%Z -> (0 <= Z.lor x y < 2 ^ k)%Z).
  Proof.
    clear.
    intros.

    split.
    apply Z.lor_nonneg ; easy.
    destruct x as [ | x | x ].
    - apply H0.
    - destruct y as [ | y | y ].
      + apply H.
      + destruct H as [_ ?].
        destruct H0 as [_ ?].
        apply Z.log2_lt_pow2 in H ; [ | easy ].
        apply Z.log2_lt_pow2 in H0 ; [ | easy ].
        apply Z.log2_lt_pow2 ; [ easy | ].
        rewrite (Z.log2_lor) ; [ | easy | easy ].
        apply Z.max_lub_lt ; easy.
      + easy.
    - easy.
  Qed.

  Definition pdisj (P : precond) (s_id : p_id) (rhs : {fset Location}) :=
    (forall h1 h2 l a v s_id', l = translate_var s_id' v -> (s_id ⪯ s_id') -> (P (h1, h2) -> P (set_heap h1 l a, h2))) /\
      (forall h1 h2 l a, l \in rhs -> (P (h1, h2) -> P (h1, set_heap h2 l a))).

  Ltac solve_in :=
    repeat match goal with
           | |- is_true (?v \in fset1 ?v :|: _) => apply/fsetU1P; left; auto
           | |- is_true (_ \in fsetU _ _) => apply/fsetU1P; right
           end.

  Ltac pdisj_apply h :=
    lazymatch goal with
    | |- ?pre (set_heap _ _ _, set_heap _ _ _) => eapply h; [ solve_in | pdisj_apply h ]
    | |- ?pre (set_heap _ _ _, _) =>
        eapply h ; [ reflexivity | auto with preceq | pdisj_apply h ]
    | |- _ => try assumption
    end.


  Ltac bind_jazz_bind :=
    match goal with
    | [ |- context [ ⊢ ⦃ ?P ⦄ putr ?l ?y ?g ≈ bind ?a ?f ⦃ ?Q ⦄ ] ] =>
        let yv := fresh in
        let gv := fresh in
        let av := fresh in
        let fv := fresh in
        set l
        ; set (yv := y)
        ; set (gv := g)
        ; set (av := a)
        ; set (fv := f)
        ; apply (r_bind (ret yv) (av) (fun x => putr l x gv) fv P (fun '(v0, h0) '(v1, h1) => v0 = v1 /\ P (h0, h1)) Q) ; [ | intros ]
        ; subst yv gv av fv ; hnf
    end.

  Theorem rpre_hypothesis_rule' :
    ∀ {A₀ A₁ : _} {p₀ : raw_code A₀} {p₁ : raw_code A₁}
      (pre : precond) post,
      (∀ s₀ s₁,
          pre (s₀, s₁) → ⊢ ⦃ λ '(s₀', s₁'), s₀' = s₀ ∧ s₁' = s₁ ⦄ p₀ ≈ p₁ ⦃ post ⦄
      ) →
      ⊢ ⦃ pre ⦄ p₀ ≈ p₁ ⦃ post ⦄.
  Proof.
    intros A₀ A₁ p₀ p₁ pre post h.
    eapply rpre_hypothesis_rule.
    intros s0 s1 H. eapply rpre_weaken_rule.
    eapply h.
    eassumption.
    easy.
  Qed.

  Theorem rpre_weak_hypothesis_rule' :
    ∀ {A₀ A₁ : _} {p₀ : raw_code A₀} {p₁ : raw_code A₁}
      (pre : precond) post,
      (∀ s₀ s₁,
          pre (s₀, s₁) → ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄ p₀ ≈ p₁ ⦃ post ⦄
      ) →
      ⊢ ⦃ pre ⦄ p₀ ≈ p₁ ⦃ post ⦄.
  Proof.
    intros A₀ A₁ p₀ p₁ pre post h.
    eapply rpre_hypothesis_rule'.
    intros. eapply rpre_weaken_rule.
    eapply h. eassumption.
    intros s0' s1' [H0 H1].
    subst.
    assumption.
  Qed.

  Theorem modulus_exact : forall {WS : wsize.wsize} (x : 'word WS), (0 <= x < modulus WS)%Z.
  Proof.
    intros.
    destruct x.
    cbn.
    apply (ssrbool.elimT (iswordZP _ _)) in i.
    apply i.
  Qed.

  Theorem modulus_smaller : forall (WS : wsize.wsize) (m : nat) {x : 'word WS}, (WS <= m)%Z -> (0 <= x < modulus m)%Z.
  Proof.
    intros.
    destruct x.
    cbn.
    apply (ssrbool.elimT (iswordZP _ _)) in i.
    split.
    - easy.
    - eapply Z.lt_le_trans.
      apply i.
      rewrite modulusZE.
      rewrite modulusZE.
      apply (Z.pow_le_mono_r 2).
      reflexivity.
      apply H.
  Qed.

  Ltac match_pattern_and_bind_repr p :=
    unfold let_both at 1, is_state at 1, prog ;
    match goal with
    | [ |- context [ ⊢ ⦃ ?P ⦄ ?x ≈ _ ⦃ ?Q ⦄ ] ] =>
        let Hx := fresh in
        set (Hx := x) ;
        pattern p in Hx ;
        subst Hx ;

        (* Match bind and apply *)
        match goal with
        | [ |- context [ ⊢ ⦃ ?P ⦄ _ ≈ bind ?a ?f ⦃ ?Q ⦄ ] ] =>
            let av := fresh in
            let fv := fresh in
            set (av := a)
            ; set (fv := f)
            ; eapply (r_bind (ret p) av _ fv P (fun '(v0, h0) '(v1, h1) => v0 = repr v1 /\ P (h0, h1)) Q)
            ; subst av fv ; hnf ; [ | intros ; apply rpre_hypothesis_rule' ; intros ? ? [] ; apply rpre_weaken_rule with (pre := fun '(s₀, s₁) => P (s₀, s₁))
              ]
        end
    end.

  Ltac match_pattern_and_bind p :=
    unfold let_both at 1, is_state at 1, prog ;
    match goal with
    | [ |- context [ ⊢ ⦃ ?P ⦄ ?x ≈ _ ⦃ ?Q ⦄ ] ] =>
        let Hx := fresh in
        set (Hx := x) ;
        pattern p in Hx ;
        subst Hx ;

        (* Match bind and apply *)
        match goal with
        | [ |- context [ ⊢ ⦃ ?P ⦄ _ ≈ bind ?a ?f ⦃ ?Q ⦄ ] ] =>
            let av := fresh in
            let fv := fresh in
            set (av := a)
            ; set (fv := f)
            ; eapply (r_bind (ret p) av _ fv P (fun '(v0, h0) '(v1, h1) => v0 = v1 /\ P (h0, h1)) Q)
            ; subst av fv ; hnf ; [ | intros ; apply rpre_hypothesis_rule' ; intros ? ? [] ; apply rpre_weaken_rule with (pre := fun '(s₀, s₁) => P (s₀, s₁))
              ]
        end
    end.

  Definition unfold_translate_for : forall v j d id0 id' y,
      (translate_for v [seq (1 + Z.of_nat i)%Z | i <- iota j (S d)] id0 y id') =
      (translate_write_var id0 v (@existT choice_type (fun t : choice_type => Choice.sort (chElement t)) chInt (Z.of_nat (j.+1))) ;;
      (snd (y id')) ;;
      translate_for v [seq (1 + Z.of_nat i)%Z | i <- iota (S j) d] id0 y (fst (y id'))).
  Proof.
    intros.
    assert (forall j n, [seq (1 + Z.of_nat i)%Z | i <- iota j (S n)] =
                     ((1 + Z.of_nat j)%Z :: [seq (1 + Z.of_nat i)%Z | i <- iota (S j) n])) by reflexivity.
    rewrite H.
    unfold translate_for ; fold translate_for.
    destruct (y id').
    replace (totce (translate_value (values.Vint (1 + Z.of_nat j))))
      with (@existT choice_type (fun t : choice_type => Choice.sort (chElement t)) chInt (Z.of_nat (j.+1))).
    2:{
      cbn.
      repeat (cbn ; rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; rewrite coerce_to_choice_type_K).
      rewrite Zpos_P_of_succ_nat.
      unfold Z.succ.
      rewrite Z.add_comm.
      reflexivity.
    }
    reflexivity.
  Qed.

  Theorem loop_eq :
    forall {acc : ChoiceEquality} v d (j : nat) id0 s_id id' y I L (y0 : @int U32 -> acc -> code L I acc) (pre : _ -> _ -> precond) (inv : _ -> _ -> precond) c,
      (0 < d) ->
      (id0 ≺ s_id) ->
      (forall id, id ⪯ id' id) ->
      (forall k c s_id,
          (id0 ≺ s_id) ->
          j <= k < j + d ->
          ⊢ ⦃ set_lhs
                (translate_var id0 (v_var v))
                (@truncate_el chInt (vtype (v_var v)) (S k))
                (fun '(h0, h1) => (inv k c) (h0, h1) /\ (pre k c) (h0, h1)) ⦄
          y s_id
              ≈ y0 (repr (Pos.of_succ_nat k)) c
              ⦃ λ '(_, h0) '(v1, h1), (inv (S k) (ct_T v1) (h0, h1)) /\ (pre (S k) (ct_T v1)) (h0, h1) ⦄) ->
      (forall k c s_id, (id0 ≺ s_id) ->
          pdisj (pre k c) s_id fset0) ->
      ⊢ ⦃ fun '(h0, h1) => inv j c (h0, h1) /\ (pre j c) (h0, h1) ⦄
          (translate_for v
                         [seq (1 + Z.of_nat i)%Z | i <- iota j d] id0 (fun id => (id' id, y id)) s_id) ≈
          (foldi_ (I := I) (L := L) (d) (repr (S j)) y0 c )
     ⦃ fun '(v0, h0) '(v1, h1) => (inv (j + d) (ct_T v1) (h0, h1)) /\ (pre (j + d) (ct_T v1)) (h0, h1) ⦄ .
  Proof.
    intros.
    generalize dependent j.
    generalize dependent c.
    generalize dependent s_id.
    induction d ; intros.
    discriminate.

    destruct d.
    - rewrite unfold_translate_for.
      simpl.
      apply better_r_put_lhs.
      setoid_rewrite T_ct_id.
      eapply r_bind.
      {
        apply H2.
        apply H0.
        lia.
      }
      {
        intros.
        apply r_ret.
        intros. rewrite addn1. apply H4.
      }
    - rewrite <- foldi__move_S.
      rewrite unfold_translate_for.

      apply better_r_put_lhs.
      setoid_rewrite bind_rewrite.
      apply r_bind with (mid := λ '(_, h0) '(v1, h1), (inv (j.+1) (ct_T v1) ((h0, h1)) /\ (pre (j.+1) (ct_T v1) (h0, h1)))).

      2:{
        intros.
        replace (Hacspec_Lib_Pre.int_add (repr j.+1) _)
          with
          (@repr U32 j.+2).
        2:{
          simpl.
          cbn.
          unfold Hacspec_Lib_Pre.int_add, add_word.
          rewrite mkwordK.
          cbn.
          apply word_ext.
          rewrite Zplus_mod.
          rewrite Zmod_mod.
          rewrite <- Zplus_mod.
          f_equal.
          now zify.
        }

        assert (id0 ≺ id' s_id).
        {
          split.
          - etransitivity.
            apply H0.
            apply H1.
          - red ; intros.
            clear -H0 H1 H4.
            subst.
            pose (prec_precneq (id' s_id) (s_id)).
            apply n.
            apply H0.
            apply H1.
        }

        apply better_r.
        unfold ".1".
        rewrite <- addSnnS.
        apply (IHd ltac:(easy) (id' s_id) H4).
        {
          intros.
          apply H2.
          apply H5.
          lia.
        }
      }
      unfold ".2".
      apply H2.
      apply H0.
      lia.
  Qed.

  Theorem loop_eq_simpl :
    forall {acc : ChoiceEquality} v d (j : nat) id0 s_id id' y I L (y0 : @int U32 -> acc -> code L I acc) (pre : _ -> _ -> precond) c,
      (0 < d) ->
      (id0 ≺ s_id) ->
      (forall id, id ⪯ id' id) ->
      (forall k c s_id,
          (id0 ≺ s_id) ->
          j <= k < j + d ->
          ⊢ ⦃ set_lhs
                (translate_var id0 (v_var v))
                (@truncate_el chInt (vtype (v_var v)) (S k))
                (pre k c) ⦄
          y s_id
              ≈ y0 (repr (Pos.of_succ_nat k)) c
              ⦃ λ '(_, h0) '(v1, h1), (pre (S k) (ct_T v1)) (h0, h1) ⦄) ->
      (forall k c s_id, (id0 ≺ s_id) ->
          pdisj (pre k c) s_id fset0) ->
      ⊢ ⦃ (pre j c) ⦄
          (translate_for v
                         [seq (1 + Z.of_nat i)%Z | i <- iota j d] id0 (fun id => (id' id, y id)) s_id) ≈
          (foldi_ (I := I) (L := L) (d) (repr (S j)) y0 c )
     ⦃ fun '(v0, h0) '(v1, h1) => (pre (j + d) (ct_T v1)) (h0, h1) ⦄ .
  Proof.
    intros.
    generalize dependent j.
    generalize dependent c.
    generalize dependent s_id.
    induction d ; intros.
    discriminate.

    destruct d.
    - rewrite unfold_translate_for.
      simpl.
      apply better_r_put_lhs.
      setoid_rewrite T_ct_id.
      eapply r_bind.
      {
        apply H2.
        apply H0.
        lia.
      }
      {
        intros.
        apply r_ret.
        intros. rewrite <- addSnnS. setoid_rewrite Nat.add_0_r. apply H4.
      }
    - rewrite <- foldi__move_S.
      rewrite unfold_translate_for.

      apply better_r_put_lhs.
      setoid_rewrite bind_rewrite.
      apply r_bind with (mid := λ '(_, h0) '(v1, h1), (pre (S j) (ct_T v1) (h0, h1))).

      2:{
        intros.
        replace (Hacspec_Lib_Pre.int_add (repr j.+1) _)
          with
          (@repr U32 j.+2).
        2:{
          simpl.
          cbn.
          unfold Hacspec_Lib_Pre.int_add, add_word.
          rewrite mkwordK.
          cbn.
          apply word_ext.
          rewrite Zplus_mod.
          rewrite Zmod_mod.
          rewrite <- Zplus_mod.
          f_equal.
          now zify.
        }

        apply better_r.
        unfold ".1".
        rewrite <- addSnnS.
        eapply (IHd (ltac:(easy)) (id' s_id) ).
        {
          eapply prec_preceq_trans.
          apply H0.
          apply H1.
        }
        {
          intros.
          apply H2.
          apply H4.
          lia.
        }
      }
      unfold ".2".
      apply H2.
      apply H0.
      lia.
  Qed.

  Lemma nat_to_be_range_is_subword : forall {WS : wsize.wsize} {WS_inp : wsize.wsize} (n : @int WS_inp) i `{H_WS : WS <= WS_inp} , (@repr WS (nat_be_range WS (toword n) i) = word.subword (i * WS) WS n).
  Proof.
    intros.
    apply word_ext.
    cbn.
    unfold nat_be_range.
    replace (_ ^ WS)%Z with (modulus WS)%Z by (destruct WS ; reflexivity).
    replace (modulus WS_inp) with (modulus (WS_inp - WS) * modulus WS)%Z by (destruct WS , WS_inp ; easy).
    rewrite mod_pq_mod_q ; [ | easy | easy ].
    rewrite !Zmod_mod.
    f_equal.
    rewrite <- Z.shiftr_div_pow2 ; [  | lia ].
    rewrite Nat2Z.inj_mul.
    f_equal. now zify.
  Qed.

  (*** Equality proofs *)

  Lemma rebuild_128_eq :
    forall (v0 v1 v2 v3 : 'word U32) ,
      make_vec _ [v0 ; v1 ; v2 ; v3] = is_pure (rebuild_u128 v0 v1 v2 v3).
  Proof.
    intros.
    simpl.
    unfold "shift_left".
    unfold Hacspec_Lib_Pre.shift_left_.
    unfold is_pure.
    unfold ".|".
    unfold Hacspec_Lib_Pre.int_or.
    unfold lift3_both ; simpl.

    unfold make_vec.
    unfold wcat_r.

    apply word_ext.

    rewrite Z.shiftl_0_l.
    rewrite Z.lor_0_r.
    rewrite !Z.shiftl_lor.
    simpl int_to_Z.
    rewrite !Z.shiftl_shiftl ; try easy.
    simpl (_ + _)%Z.

    unfold wshl, lsl.
    setoid_rewrite wunsigned_repr.
    rewrite Zmod_small.
    rewrite Zmod_small.
    rewrite mod_mod_larger.
    rewrite Zmod_small.
    rewrite Zmod_small.
    rewrite mod_mod_larger.
    rewrite Zmod_small.
    rewrite Zmod_small.
    rewrite mod_mod_larger.
    rewrite Zmod_small.
    rewrite Zmod_small.
    unfold word.wor, wor, toword, mkword.
    rewrite Zmod_small.
    rewrite Zmod_small.
    rewrite Zmod_small.
    reflexivity.

    all: try apply shiftl_bounds.
    all: try now apply (@num_smaller_if_modulus_le U32).
    all: try easy.
    repeat (rewrite modulusZE ; apply Z_lor_pow2 ; rewrite <- modulusZE).
    all: try now apply (@num_smaller_if_modulus_le U32).
    1: replace 32%Z with (int_to_Z 32) by reflexivity.
    2: replace 64%Z with (int_to_Z 64) by reflexivity.
    3: replace 96%Z with (int_to_Z 96) by reflexivity.
    all: apply shiftl_bounds ; [ easy | ].
    all: try now apply (@num_smaller_if_modulus_le U32).
  Qed.

  Lemma rebuild_32_eq :
    forall (v0 v1 v2 v3 : 'word U8) ,
      make_vec _ [v0 ; v1 ; v2 ; v3] = is_pure (rebuild_u32 v0 v1 v2 v3).
  Proof.
    intros.
    simpl.
    unfold "shift_left".
    unfold Hacspec_Lib_Pre.shift_left_.
    unfold is_pure.
    unfold ".|".
    unfold Hacspec_Lib_Pre.int_or.
    unfold lift3_both ; simpl.

    unfold make_vec.
    unfold wcat_r.

    apply word_ext.

    rewrite Z.shiftl_0_l.
    rewrite Z.lor_0_r.
    rewrite !Z.shiftl_lor.
    simpl int_to_Z.
    rewrite !Z.shiftl_shiftl ; try easy.
    simpl (_ + _)%Z.

    unfold wshl, lsl.
    setoid_rewrite wunsigned_repr.
    rewrite Zmod_small.
    rewrite Zmod_small.
    rewrite mod_mod_larger.
    rewrite Zmod_small.
    rewrite Zmod_small.
    rewrite mod_mod_larger.
    rewrite Zmod_small.
    rewrite Zmod_small.
    rewrite mod_mod_larger.
    rewrite Zmod_small.
    rewrite Zmod_small.
    unfold word.wor, wor, toword, mkword.
    rewrite Zmod_small.
    rewrite Zmod_small.
    rewrite Zmod_small.
    reflexivity.

    all: try apply shiftl_bounds.
    all: try now apply (@num_smaller_if_modulus_le U8).
    all: try easy.
    repeat (rewrite modulusZE ; apply Z_lor_pow2 ; rewrite <- modulusZE).
    all: try now apply (@num_smaller_if_modulus_le U8).
    1: replace 8%Z with (int_to_Z 8) by reflexivity.
    2: replace 16%Z with (int_to_Z 16) by reflexivity.
    3: replace 24%Z with (int_to_Z 24) by reflexivity.
    all: apply shiftl_bounds ; [ easy | ].
    all: try now apply (@num_smaller_if_modulus_le U8).
  Qed.

  Lemma index_32_eq :
    forall (v : 'word U128) (i : nat),
      i < 4 ->
      word.subword (i * U32) U32 v = is_pure (index_u32 v (repr (Z.of_nat i))).
  Proof.
    intros.
    unfold word.subword.
    unfold index_u32.
    simpl.
    unfold "shift_left", Hacspec_Lib_Pre.shift_left_.
    unfold "shift_right", Hacspec_Lib_Pre.shift_right_.
    unfold ".%", Hacspec_Lib_Pre.int_mod.
    unfold ".*", Hacspec_Lib_Pre.int_mul.
    unfold is_pure.
    unfold lift3_both ; simpl.
    unfold wshl, lsl.
    unfold wshr, lsr.
    unfold wmod, mul_word.
    apply word_ext.
    simpl.
    cbn.

    rewrite Z2Nat.id.
    rewrite (Zmod_small (Z.of_nat i)).
    rewrite (Zmod_small ( (Z.of_nat i) * _)).
    rewrite (Zmod_small ( (Z.of_nat i) * _)).
    rewrite (mod_mod_larger _ 4294967296).
    rewrite (Zmod_mod _ (modulus U32)).
    f_equal.
    f_equal.
    all: try now do 4 (destruct i as [ | i ] ; [ easy | ]).
    repeat solve_lower_bounds.
  Qed.


  Lemma index_8_eq :
    forall (v : 'word U32) (i : nat),
      i < 4 ->
      word.subword (i * U8) U8 v = is_pure (index_u8 v (repr (Z.of_nat i))).
  Proof.
    intros.
    unfold word.subword.
    unfold index_u32.
    simpl.
    unfold "shift_left", Hacspec_Lib_Pre.shift_left_.
    unfold "shift_right", Hacspec_Lib_Pre.shift_right_.
    unfold ".%", Hacspec_Lib_Pre.int_mod.
    unfold ".*", Hacspec_Lib_Pre.int_mul.
    unfold is_pure.
    unfold lift3_both ; simpl.
    unfold wshl, lsl.
    unfold wshr, lsr.
    unfold wmod, mul_word.
    apply word_ext.
    simpl.
    cbn.

    rewrite Z2Nat.id.
    rewrite (Zmod_small (Z.of_nat i)).
    rewrite (Zmod_small ( (Z.of_nat i) * _)).
    rewrite (Zmod_small ( (Z.of_nat i) * _)).
    rewrite (mod_mod_larger _ 256).
    rewrite (Zmod_mod _ (modulus U8)).
    f_equal.
    f_equal.
    all: try now do 4 (destruct i as [ | i ] ; [ easy | ]).
    repeat solve_lower_bounds.
  Qed.

  Lemma wpshufd1_eq :
    forall (rkey : 'word U128)  (i : nat) (n : 'word U8),
      i < 4 ->
      wpshufd1 rkey n i =
        is_pure (vpshufd1 rkey n (Hacspec_Lib_Pre.repr i)).
  Proof.
    Opaque Z.mul.
    clear.
    intros.
    unfold vpshufd1.
    unfold wpshufd1.

    Opaque index_u32.
    unfold is_pure at 1, lift_scope ; simpl.
    rewrite (index_32_eq _ 0).
    f_equal.
    f_equal.
    unfold Hacspec_Lib_Pre.int_mod.
    unfold Hacspec_Lib_Pre.shift_right_.
    unfold Hacspec_Lib_Pre.int_mul.
    unfold lift3_both ; simpl.
    apply word_ext.
    simpl.
    f_equal.
    f_equal.
    f_equal.
    f_equal.
    rewrite Zmod_small.
    unfold mul_word.
    unfold unsigned, wunsigned.
    rewrite !mkwordK.
    rewrite (Zmod_small _ (modulus U32)).
    rewrite (Zmod_small _ (modulus U32)).
    rewrite (Zmod_small _ (modulus U32)).
    rewrite (Zmod_small _ (modulus U32)).
    rewrite (Zmod_small _ (modulus U32)).
    f_equal.
    cbn.
    replace (4 mod _)%Z with (modulus 2)%Z by reflexivity.
    rewrite Z2Nat.id.
    symmetry.
    rewrite (Zmod_small _ (modulus nat7.+1)).
    symmetry.
    f_equal.
    f_equal.
    f_equal.
    all: try now do 4 (destruct i as [ | i ] ; [ easy | ]).
    apply small_modulus_smaller.
    now repeat solve_lower_bounds.
    easy.

    split ; [ cbn ; now repeat solve_lower_bounds | ].
    replace (modulus U32)%Z with (32 * modulus (U32 - 5))%Z by reflexivity.
    apply Zmult_lt_compat_l. easy.
    apply small_modulus_smaller.
    cbn ; now repeat solve_lower_bounds.
    easy.

    apply small_modulus_smaller.
    cbn ; now repeat solve_lower_bounds.
    easy.

    apply (@num_smaller_if_modulus_le U32).
    easy.
  Qed.

  Lemma wpshufd1_eq_state :
    forall {H} (rkey : 'word U128) (n : 'word U8) (i : nat),
      i < 4 ->
      ⊢ ⦃ H ⦄
          ret (wpshufd1 rkey n i) ≈
          is_state (vpshufd1 rkey n (Hacspec_Lib_Pre.repr i))
          ⦃ λ '(v0, h0) '(v1, h1), v0 = v1 ∧ H (h0, h1) ⦄.
  Proof.
    intros.
    rewrite (wpshufd1_eq _ i n) ; [ | apply H0 ].
    now apply r_ret.
  Qed.

  Ltac match_wpshufd1_vpshufd1 i :=
    (let w := fresh in
     let y := fresh in
     let b := fresh in
     set (w := wpshufd1 _ _ i) ;
     set (y := fun _ : Hacspec_Lib_Pre.int32 => _) ;
     set (b := vpshufd1 _ _ _);
     let k := fresh in
     let l := fresh in
     match goal with
     | [ |- context [ ⊢ ⦃ ?P ⦄ ?lhs ≈ _ ⦃ _ ⦄ ] ] => set (k := P) ; set (l := lhs)
     end ;
     pattern (w) in l ;
     subst l ;
     apply (@r_bind _ _ _ _ (ret w) (prog (is_state b)) _ y _ (fun '(v0, h0) '(v1, h1) => v0 = v1 /\ k (h0, h1))) ; subst w y b ; hnf).

  Ltac solve_wpshufd1_vpshufd1 i :=
    match_wpshufd1_vpshufd1 i ; [now apply wpshufd1_eq_state | intros ].

  Lemma wpshufd_128_eq_state :
    forall {H} (rkey : 'word U128) (n : nat),
      ⊢ ⦃ H ⦄
          ret (wpshufd_128 rkey n) ≈
          is_state (vpshufd rkey (repr n))
          ⦃ λ '(v0, h0) '(v1, h1), v0 = v1 ∧ H (h0, h1) ⦄.
  Proof.
    intros.
    unfold wpshufd_128.
    unfold wpshufd_128.
    unfold iota.
    unfold map.

    setoid_rewrite rebuild_128_eq.
    unfold vpshufd.

    solve_wpshufd1_vpshufd1 0.
    solve_wpshufd1_vpshufd1 1.
    solve_wpshufd1_vpshufd1 2.
    solve_wpshufd1_vpshufd1 3.

    apply r_ret.
    intros ? ? [? [? [? []]]].
    subst.
    subst H4.
    split ; [ clear | assumption ].
    reflexivity.
  Qed.

  Lemma wshufps_128_eq_state :
    forall {H} (a b : 'word U128) (n : nat),
      ⊢ ⦃ H ⦄
          ret (wshufps_128 (wrepr U8 n) a b) ≈
          is_state (vshufps a b (Hacspec_Lib_Pre.repr n))
          ⦃ λ '(v0, h0) '(v1, h1), v0 = v1 ∧ H (h0, h1) ⦄.
  Proof.
    intros.
    unfold wshufps_128.
    unfold vshufps.
    unfold iota.
    unfold map.
    unfold vpshufd.

    solve_wpshufd1_vpshufd1 0.
    solve_wpshufd1_vpshufd1 1.
    solve_wpshufd1_vpshufd1 2.
    solve_wpshufd1_vpshufd1 3.

    rewrite rebuild_128_eq.

    intros.
    apply r_ret.
    intros ? ? [? [? [? []]]].
    subst.
    subst H4.
    split ; [ clear | assumption ].
    reflexivity.
  Qed.

  Lemma key_combined_eq id0 rcon rkey temp2 (pre : precond) :
    (pdisj pre id0 fset0) ->
    ⊢ ⦃ pre ⦄
        JKEY_COMBINE id0 rcon rkey temp2
        ≈
        is_state (key_combine rcon rkey temp2)
        ⦃ fun '(v0, h0) '(v1, h1) =>
            (exists o1 o2, v0 = [('word U128 ; o1) ; ('word U128 ; o2)]
                      /\ (o1, o2) = v1) /\ pre (h0, h1) ⦄.
  Proof.
    intros H_pdisj.
    set (JKEY_COMBINE _ _ _ _).
    unfold JKEY_COMBINE in r.
    unfold get_translated_static_fun in r.
    simpl in r.
    unfold translate_call, translate_call_body in r |- *.
    Opaque translate_call.
    simpl in r.

    subst r.
    rewrite !zero_extend_u.
    unfold key_combine.

    apply better_r_put_lhs.
    apply better_r_put_lhs.
    apply better_r_put_lhs.
    remove_get_in_lhs.
    bind_jazz_hac ; [ shelve | ].
    do 5 (apply better_r_put_lhs ; do 2 remove_get_in_lhs ; bind_jazz_hac ; [shelve | ]).
    apply better_r_put_lhs ; do 2 remove_get_in_lhs ; apply r_ret.

    intros.
    split.
    {
      destruct_pre.
      eexists.
      eexists.
      split ; [ reflexivity | ].
      cbn.
      rewrite !zero_extend_u.
      reflexivity.
    }
    {
      destruct_pre.
      pdisj_apply H_pdisj.
    }

    Unshelve.
    {
      unfold tr_app_sopn_tuple.
      unfold sopn_sem.
      unfold sopn.get_instr_desc.

      set (chCanonical _).
      cbn in s.
      subst s.

      set (tr_app_sopn _ _ _ _).
      cbn in y.
      subst y.
      hnf.

      replace (toword _) with (255)%Z by (cbn ; rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; now rewrite coerce_to_choice_type_K).

      replace (truncate_chWord U128 _) with rkey by (simpl ; now rewrite zero_extend_u).

      apply (wpshufd_128_eq_state rkey 255).
    }
    {
      unfold tr_app_sopn_tuple.
      unfold sopn_sem.
      unfold sopn.get_instr_desc.

      set (totce _) at 2.
      cbn in t.
      unfold totce in t.

      set (chCanonical _).
      cbn in s.
      subst s.

      set (tr_app_sopn _ _ _ _).
      cbn in y.
      subst y.
      hnf.

      unfold totce.
      subst t.
      unfold ".π2".

      unfold lift2_vec.

      unfold map2.
      unfold split_vec.
      unfold map.
      unfold iota.

      set (nat_of_wsize U128 %/ nat_of_wsize U128 +
             nat_of_wsize U128 %% nat_of_wsize U128).
      cbn in n.
      subst n.
      hnf.

      replace (word.subword _ _ _) with temp2.
      2:{
        destruct temp2.
        cbn.
        apply word_ext.
        cbn.
        rewrite !Zmod_mod.
        rewrite Zmod_small.
        reflexivity.
        apply (ssrbool.elimT (iswordZP _ _)).
        apply i.
      }
      replace (word.subword _ _ _) with rcon.
      2:{
        destruct rcon.
        cbn.
        apply word_ext.
        cbn.
        rewrite !Zmod_mod.
        rewrite Zmod_small.
        reflexivity.
        apply (ssrbool.elimT (iswordZP _ _)).
        apply i.
      }

      replace (truncate_chWord _ _) with (wrepr U8 16) by now do 2 (cbn ; rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; rewrite coerce_to_choice_type_K).

      unfold make_vec.
      unfold wcat_r.
      rewrite Z.shiftl_0_l.
      rewrite Z.lor_0_r.

      unfold mkword.

      epose (wshufps_128_eq_state temp2 rcon 16).
      unfold lift_scope.
      unfold is_state at 1.
      unfold lift_code_scope.
      unfold prog.

      rewrite <- bind_ret.
      set (ret _).
      pattern (wshufps_128 (wrepr U8 16) temp2 rcon) in r0.
      subst r0.

      eapply (@r_bind _ _ _ _ (ret (wshufps_128 (wrepr U8 16) temp2 rcon))).
      apply r.
      intros.
      apply r_ret.
      intros ? ? [].
      subst.
      split.
      destruct a₁0. cbn. unfold wrepr. cbn. apply word_ext.
      rewrite Zmod_small.
      reflexivity.
      apply (ssrbool.elimT (iswordZP _ _)).
      apply i.
      apply H0.
    }
    {
      cbn.
      apply r_ret.
      intros.
      split.
      reflexivity.
      apply H.
    }
    {

      unfold tr_app_sopn_tuple.
      unfold sopn_sem.
      unfold sopn.get_instr_desc.

      set (totce _) at 2.
      cbn in t.
      unfold totce in t.

      set (chCanonical _).
      cbn in s.
      subst s.

      set (tr_app_sopn _ _ _ _).
      cbn in y.
      subst y.
      hnf.

      unfold totce.
      subst t.
      unfold ".π2".

      unfold lift2_vec.

      unfold map2.
      unfold split_vec.
      unfold map.
      unfold iota.

      set (nat_of_wsize U128 %/ nat_of_wsize U128 +
             nat_of_wsize U128 %% nat_of_wsize U128).
      cbn in n.
      subst n.
      hnf.

      replace (word.subword _ _ _) with a₁0.
      2:{
        destruct a₁0.
        cbn.
        apply word_ext.
        cbn.
        rewrite !Zmod_mod.
        rewrite Zmod_small.
        reflexivity.
        apply (ssrbool.elimT (iswordZP _ _)).
        apply i.
      }
      replace (word.subword _ _ _) with a₁1.
      2:{
        destruct a₁1.
        cbn.
        apply word_ext.
        cbn.
        rewrite !Zmod_mod.
        rewrite Zmod_small.
        reflexivity.
        apply (ssrbool.elimT (iswordZP _ _)).
        apply i.
      }

      replace (truncate_chWord _ _) with (wrepr U8 140) by now repeat (cbn ; rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; rewrite coerce_to_choice_type_K).

      rewrite <- bind_ret.
      set (ret _).
      pattern (wshufps_128 (wrepr U8 140) a₁0 a₁1) in r.
      subst r.
      eapply (@r_bind _ _ _ _ (ret (wshufps_128 (wrepr U8 140) a₁0 a₁1))).
      apply (wshufps_128_eq_state a₁0 a₁1 140).

      intros.
      apply r_ret.
      intros ? ? [].
      subst.
      split.
      unfold make_vec.
      cbn.
      rewrite Z.lor_0_r.
      destruct a₁2. cbn. unfold wrepr. cbn. apply word_ext.
      rewrite Zmod_small.
      cbn.
      reflexivity.
      apply (ssrbool.elimT (iswordZP _ _)).
      apply i.
      apply H0.
    }
    {
      apply r_ret.
      solve_post_from_pre.
    }
    {
      apply r_ret.
      solve_post_from_pre.
    }
    (* Cleanup *)
    Transparent translate_call.
  Qed.

  Lemma sbox_eq :
    (forall n i, (i < 4)%nat ->
    is_pure (array_index sbox_v
             (index_u8 (lift_to_both0 n) (lift_to_both0 (usize i)))) = waes.Sbox (word.subword (i * U8) U8 n)).
  Proof.
    intros.
    rewrite index_8_eq ; [ | apply H ].

    destruct (is_pure (index_u8 _ _)).
    destruct toword.
    - reflexivity.
    - (* SLOW! *) (* admit. *)
      do 8 (destruct p ; [ | | reflexivity ]) ; exfalso ; destruct p ; discriminate i0.
    - easy.
  (* Admitted. *) Qed.

  Lemma SubWord_eq (n : int32) :
    waes.SubWord n = is_pure (subword n).
  Proof.
    intros.
    unfold waes.SubWord.
    unfold split_vec.
    replace (U32 %/ U8 + U32 %% U8) with 4 by reflexivity.

    unfold map.
    unfold iota.
    rewrite rebuild_32_eq.

    unfold subword.
    do 4 (rewrite <- sbox_eq ; [ | easy ]).

    easy.
  Qed.

  Lemma keygen_assist_eq id0 (v1 : 'word U128) (v2 : 'word U8) (pre : precond) :
    (pdisj pre id0 fset0) ->
    ⊢ ⦃ pre ⦄
        ret (waes.wAESKEYGENASSIST v1 v2)
        ≈
        prog (is_state (aeskeygenassist v1 v2))
        ⦃ fun '(v0, h0) '(v1, h1) => (v0 = v1) /\ pre (h0, h1) ⦄.
  Proof.
    intros.

    unfold waes.wAESKEYGENASSIST.

    rewrite rebuild_128_eq.

    unfold aeskeygenassist.

    match_pattern_and_bind_repr (@word.subword (wsize_size_minus_1 U128).+1 (1 * U32) U32 v1).
    {
      apply r_ret.
      intros.
      rewrite index_32_eq ; [ | easy ].
      split. setoid_rewrite wrepr_unsigned. reflexivity. assumption.
    }

    match_pattern_and_bind_repr (@word.subword (wsize_size_minus_1 U128).+1 (3 * U32) U32 v1).
    {
      apply r_ret.
      intros.
      rewrite index_32_eq ; [ | easy ].
      split ; [ setoid_rewrite wrepr_unsigned | ] ; easy.
    }

    match_pattern_and_bind (waes.SubWord a₀).
    {
      subst.
      replace (is_pure (lift_to_both0 _)) with (@repr U32 a₁).
      2:{
        pose (isword_Z _ a₁).
        destruct a₁.
        apply word_ext.
        now rewrite Zmod_small.
      }
      rewrite (SubWord_eq (repr a₁)).
      apply r_ret ; easy.
    }

    match_pattern_and_bind (word.wxor (waes.RotWord a₀1) (zero_extend U32 (sz':=U8) v2)).
    {
      subst.

      unfold waes.RotWord.
      rewrite rebuild_32_eq.
      rewrite !index_8_eq ; try lia.
      unfold rotword.

      apply r_ret.
      intros.
      split.
      - reflexivity.
      - apply H0.
    }

    match_pattern_and_bind (waes.SubWord a₀0).
    {
      subst.
      replace (is_pure (lift_to_both0 _)) with (@repr U32 a₁0).
      2:{
        pose (isword_Z _ a₁0).
        destruct a₁0.
        apply word_ext.
        now rewrite Zmod_small.
      }
      rewrite (SubWord_eq (repr a₁0)).
      apply r_ret ; easy.
    }

    match_pattern_and_bind (word.wxor (waes.RotWord a₀3) (zero_extend U32 (sz':=U8) v2)).
    {
      subst.

      unfold waes.RotWord.
      rewrite rebuild_32_eq.
      rewrite !index_8_eq ; try lia.
      unfold rotword.

      apply r_ret.
      intros.
      split.
      - reflexivity.
      - apply H0.
    }

    subst.
    apply r_ret.
    intros.
    subst.
    all: try (intros ? ? [] ; subst ; assumption).
    easy.
  Qed.

  Lemma key_expand_eq id0 rcon rkey temp2  (pre : precond) :
    (pdisj pre id0 fset0) ->
    ⊢ ⦃ pre ⦄
        JKEY_EXPAND id0 rcon rkey temp2
        ≈
        key_expand (wrepr U8 rcon) rkey temp2
        ⦃ fun '(v0, h0) '(v1, h1) =>
            (exists o1 o2, v0 = [('word U128 ; o1) ; ('word U128 ; o2)]
                      /\ (o1, o2) = v1)  /\ pre (h0, h1) ⦄.
  Proof.
    intros H_pdisj.
    set (JKEY_EXPAND _ _ _ _).
    unfold translate_call, translate_call_body in r |- *.
    Opaque translate_call.
    unfold JKEY_EXPAND in r.
    cbn in r.
    subst r.
    rewrite !zero_extend_u.

    apply better_r_put_lhs.
    apply better_r_put_lhs.
    apply better_r_put_lhs.

    do 2 remove_get_in_lhs.
    bind_jazz_hac ; [shelve | ].

    eapply rpre_weak_hypothesis_rule'.
    intros ? ? [? H].

    apply better_r_put_lhs.
    do 3 remove_get_in_lhs.

    rewrite bind_assoc.
    rewrite bind_assoc.
    rewrite <- bind_ret.
    match goal with
    | [ |- context [ ⊢ ⦃ ?pre ⦄ _ ≈ _ ⦃ _ ⦄ ] ] => set (P := pre)
    end.
    apply r_bind with (mid := λ '(v0, h0) '(v1, h1),
                         (∃ o1 o2 : 'word U128,
                             v0 = [('word U128; o1) ; ('word U128; o2)] ∧ (o1, o2) = v1) /\ P (h0, h1)).
    2:{
      intros.
      subst P.
      destruct a₁0.
      destruct a₀0 as [ | ? [] ] ; simpl ; repeat apply better_r_put_lhs ; repeat remove_get_in_lhs ; apply r_ret ; intros ; destruct_pre ; try easy.
      split.
      eexists.
      eexists.
      split.
      reflexivity.
      rewrite !zero_extend_u.
      inversion H25.
      subst.
      inversion H24.
      subst.
      cbn.
      now rewrite !zero_extend_u.

      pdisj_apply H_pdisj.
    }

    subst.
    subst P.

    intros.
    apply (key_combined_eq (id0~1)%positive rkey a₁ temp2).

    split.
    - intros.
      subst.
      repeat destruct H.
      subst.
      cbn in H2.
      subst.
      unfold set_lhs.

      subst.
      destruct_pre.
      repeat (cbn ; rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; rewrite coerce_to_choice_type_K).
      eexists.
      split.
      split ; [ reflexivity | ].
      eexists.
      split ; [ | reflexivity ].
      eexists.
      split ; [ | reflexivity ].
      exists (set_heap H9 (translate_var s_id' v) a).
      split ; [ | reflexivity ].
      pdisj_apply H_pdisj.
      etransitivity.
      apply fresh2_weak.
      assumption.

      rewrite ![set_heap _ (translate_var s_id' v) a]set_heap_commut
      ; (reflexivity ||
           (apply injective_translate_var2 ;
            red ;
            intros ;
            subst ;
            now apply (precneq_I s_id'))).

      Unshelve.
      {

        (* Keygen assist *)

        unfold tr_app_sopn_tuple.
        unfold sopn_sem.
        unfold sopn.get_instr_desc.


        Opaque aeskeygenassist.
        repeat (cbn ; rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; rewrite coerce_to_choice_type_K).
        Transparent aeskeygenassist.
        apply (keygen_assist_eq (id0~1)%positive ).

        split.
        - intros.
          subst.
          destruct_pre.
          unfold set_lhs.
          eexists.
          eexists.
          eexists.
          split.
          exists (set_heap H5 (translate_var s_id' v) a).
          split.
          pdisj_apply H_pdisj.

          etransitivity.
          apply fresh2_weak.
          apply H0.
          reflexivity.
          reflexivity.

          rewrite ![set_heap _ (translate_var s_id' v) a]set_heap_commut ;
            (reflexivity ||
               (apply injective_translate_var2 ;
                red ;
                intros ;
                subst ;
                now apply (precneq_I s_id'))).
        - intros.
          subst.
          destruct_pre.
          unfold set_lhs.
          eexists.
          split ; [ | reflexivity ].
          eexists.
          split ; [ | reflexivity ].
          eexists.
          split ; [ | reflexivity ].
          eapply H_pdisj.
          apply H.
          apply H6.
      }

    - easy.
      Transparent translate_call.
  Qed.

  Lemma rcon_eq id0 (j : nat) (pre : precond) :
    (pdisj pre id0 fset0) ->
    (0 <= j < 10)%nat ->
    ⊢ ⦃ pre ⦄
        JRCON id0 (Z.pos (Pos.of_succ_nat j))
        ≈
        is_state (array_index (rcon_v) (@repr U32 (S j)))
        ⦃ fun '(v0, h0) '(v1, h1) =>
            (exists o1, v0 = [('int; o1)] /\ repr o1 = v1)  /\ pre (h0, h1) ⦄.
  Proof.
    intros.
    unfold JRCON.
    unfold get_translated_static_fun.
    simpl.
    apply better_r_put_lhs.
    remove_get_in_lhs.
    fold @bind.
    rewrite !coerce_to_choice_type_K.
    repeat setoid_rewrite coerce_to_choice_type_K.
    cbn.
    rewrite !array_from_list_helper_equation_2.
    simpl.
    rewrite Hacspec_Lib_Pre.array_index_equation_2.
    simpl.
    cbn.
    unfold array_index_clause_2.
    unfold array_index_clause_2_clause_1.
    simpl.

    (* SLOW! *) (* admit. *)
    do 10 (destruct j as [ | j ] ; [ simpl ; repeat (remove_get_in_lhs ; simpl) ; apply better_r_put_lhs ; remove_get_in_lhs ; apply r_ret ; intros ; destruct_pre ; split ; [ eexists ; split ; [ | reflexivity] ; f_equal ; unfold totce ; repeat (cbn ; rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; rewrite coerce_to_choice_type_K) ; reflexivity | eapply H ; [ reflexivity | reflexivity | ] ; eapply H ; [ reflexivity | reflexivity | ] ; apply H5 ] | ]).
    exfalso.
    lia.
  (* Admitted. *) Qed.

  Ltac split_post :=
    repeat
      match goal with
      | |- (_ ⋊ _) _ => split
      | |- _ /\ _ => split
      | |- set_lhs _ _ _ _ => eexists
      | |- set_rhs _ _ _ _ => eexists
      end.

  Definition seq_to_arr (X : seq uint128) : FMap.fmap_type Z_ordType U8.-word :=
    let l0 := (unzip2 X) in
    mkfmap (zip (ziota 0 (size l0)) (seq.foldr (fun x y => y ++ (split_vec U8 x)) [] l0)).

  Definition seq_upd_from_arr (X : seq uint128) (v : 'array) : FMap.fmap_type Z_ordType U8.-word :=
    let l0 := (seq_to_list int128 X) in
    foldr (fun kv m => (chArray_set m AAscale kv.1 kv.2)) v (rev (zip (ziota 0 (Z.of_nat (size l0))) (l0))).

  Lemma seq_udp_from_arr_push : forall a b c,
      (seq_upd_from_arr (Hacspec_Lib_Pre.seq_push a b) c)
      =
        (chArray_set (seq_upd_from_arr a c) AAscale (Z.of_nat (size (seq_to_list int128 a))) b).
  Proof.
    intros.
    unfold seq_upd_from_arr.
    simpl.

    rewrite seq_push_list_app.
    rewrite size_cat.
    rewrite Nat2Z.inj_add.
    rewrite Z.add_1_r.
    rewrite ziotaS_cat.
    rewrite !Z.add_0_l.

    rewrite zip_cat.
    rewrite rev_cat.

    unfold zip at 1.
    unfold rev at 1, catrev.
    rewrite foldr_cat.

    unfold foldr at 1.
    reflexivity.
    rewrite size_ziota.
    rewrite Nat2Z.id.
    reflexivity.

    lia.
  Qed.

  Ltac solve_var_neq :=
    ((now apply injective_translate_var3) ||
             (apply injective_translate_var2 ; red ; intros ; subst)).
  Ltac eexists_set_heap :=
    eexists ; split ; [ |
    match goal with
    | [ |- context [
              set_heap _ _ ?d
              = set_heap _ _ ?d
      ] ] =>
        reflexivity
    end ||
        match goal with
        | [ |- context [
                  set_heap ?a ?b ?c
                  = set_heap _ _ ?e
          ] ] =>
            rewrite [set_heap a b c]set_heap_commut ; [ reflexivity |
            solve_var_neq ]
        end].

  Ltac solve_in_fset :=
    rewrite in_fset ; repeat (reflexivity || (rewrite mem_head) || (now rewrite Bool.orb_true_r) || (now rewrite Bool.orb_true_l) || rewrite in_cons ; simpl).

  Ltac remove_get_set_heap :=
    match goal with
    | [ |- context [ get_heap (set_heap _ ?a _) ?a ] ] =>
        rewrite get_set_heap_eq
    end ||
        rewrite get_set_heap_neq.

  Notation rkeys_loc := (CE_loc_to_loc rkeys_65_loc).
  Notation temp2_loc := (CE_loc_to_loc temp2_67_loc).
  Notation rkey_loc := (CE_loc_to_loc key_66_loc).
  Lemma keys_expand_eq id0 rkey  (pre : precond) :
    (pdisj pre id0 (fset ([rkeys_loc ; temp2_loc ; rkey_loc ]))) ->
    ⊢ ⦃ pre ⦄
        JKEYS_EXPAND id0 rkey
        ≈
        is_state (keys_expand rkey)
        ⦃ fun '(v0, h0) '(v1, h1) =>
            (exists o1, v0 = [('array; o1)]
                   /\ (forall k, k <= 10 -> ((chArray_get U128 o1 k (wsize_size U128))
    = is_pure (seq_index (A := @int U128) v1 (lift_to_both0 (repr k))))))  /\ pre (h0, h1) ⦄.
  Proof.
    intros H_pdisj.
    set (JKEYS_EXPAND _ _).
    unfold translate_call, translate_call_body in r |- *.
    Opaque translate_call.
    unfold JKEY_EXPAND in r.
    unfold get_translated_static_fun, JAES_ROUNDS, get_translated_static_fun, translate_prog_static, translate_funs_static, translate_call_body in r.
    simpl in r.
    subst r.
    rewrite !zero_extend_u.

    apply better_r_put_lhs.
    remove_get_in_lhs.
    apply better_r. eapply r_get_remember_lhs. intros.


    unfold keys_expand.

    unfold let_mut_both at 1, is_state at 1, is_state at 1, is_state at 1.
    Opaque is_state. Opaque is_pure.
    match goal with
    | [ |- context [ ⊢ ⦃ ?P ⦄ ?lhs ≈ ?rhs ⦃ ?Q ⦄ ] ] =>
        simpl rhs
    end.
    Transparent is_state. Transparent is_pure.

    rewrite bind_rewrite.
    setoid_rewrite bind_rewrite.
    apply better_r_put_get_rhs.
    apply better_r_put_rhs.

    apply better_r_put_get_rhs.
    apply better_r_put_rhs.

    unfold let_mut_both at 1, is_state at 1, is_state at 1, is_state at 1.
    Opaque is_state. Opaque is_pure.
    match goal with
    | [ |- context [ ⊢ ⦃ ?P ⦄ ?lhs ≈ ?rhs ⦃ ?Q ⦄ ] ] =>
        simpl rhs
    end.
    Transparent is_state. Transparent is_pure.

    set (Hacspec_Lib_Pre.seq_new_ _ _).

    rewrite !zero_extend_u.
    rewrite !coerce_to_choice_type_K.

    rewrite bind_rewrite.

    apply better_r_put_get_rhs.
    apply better_r_put_rhs.

    rewrite bind_rewrite.

    apply better_r_put_get_rhs.
    apply better_r_put_rhs.

    set (temp2 := repr 0) at 1 2.

    unfold let_both at 1, is_state at 1, prog.
    apply better_r_put_lhs.

    set (tr_app_sopn_tuple _ _ _).
    cbn in s.
    assert (s = temp2) by now apply word_ext.
    generalize dependent s.
    intros.
    subst.

    apply better_r_put_lhs.


    unfold let_mut_both at 1, is_state at 1, is_state at 1, is_state at 1.
    Opaque is_state. Opaque is_pure.
    match goal with
    | [ |- context [ ⊢ ⦃ ?P ⦄ ?lhs ≈ ?rhs ⦃ ?Q ⦄ ] ] =>
        simpl rhs
    end.
    Transparent is_state. Transparent is_pure.

    rewrite bind_assoc.

    set (set_lhs _ _ _).
    set (rkeys := Hacspec_Lib_Pre.seq_push _ _) in *.
    pose (p0 := (λ (n : nat) '(rkeys, rkey, temp2) '(h0, h1),
          set_lhs (translate_var id0 {| vtype := sword U128; vname := "temp2.336" |}) temp2
            (set_lhs (translate_var id0 {| vtype := sarr 176; vname := "rkeys.335" |}) (seq_upd_from_arr rkeys x)
               (set_rhs rkeys_loc rkeys
                  (set_rhs temp2_loc temp2
                     (set_rhs rkey_loc rkey
                        (
                           (λ '(s₀, s₁),
                              (set_lhs (translate_var id0 {| vtype := sword U128; vname := "key.334" |}) rkey pre)
                                (s₀, s₁))))))) (h0, h1)) : nat -> key_list_t * 'word U128 * int → precond).

    apply rpre_weaken_rule with (pre := (λ '(h0, h1), (p0 0 (rkeys, rkey, temp2)) (h0, h1))).
    2:{
      intros.
      subst p.
      subst p0.

      destruct_pre.
      eexists_set_heap.
      eexists ; split.
      2:{
        remove_get_set_heap.
        subst rkeys.
        unfold seq_upd_from_arr.
        simpl.
        reflexivity.

        solve_var_neq.
      }
      eexists ; split.
      2:{
        rewrite set_heap_commut.
        reflexivity.
        easy.
      }
      eexists ; split.
      2:{
        reflexivity.
      }
      eexists ; split.
      2:{
        reflexivity.
      }
      eexists ; split.
      2:{
        reflexivity.
      }
      eapply H_pdisj.
      solve_in_fset.
      assumption.
    }
    subst p.

    pose (P := fun (n : nat) (v0 : key_list_t * 'word U128 * @int U128) => fun '(h0, h1) => pre (h0, h1) /\ (forall i, i <= n -> (chArray_get U128
             (get_heap h0
                (translate_var id0
                   {| vtype := sarr 176; vname := "rkeys.335" |})) i
             (wsize_size U128)) = Hacspec_Lib_Pre.seq_index (fst (fst v0)) (repr (Z.of_nat i))) /\ size (Hacspec_Lib_Pre.seq_to_list _ (fst (fst v0))) = n.+1).

    apply rpre_weaken_rule with (pre := (λ '(h0, h1), (P 0 (rkeys, rkey, temp2) (h0, h1)) /\ (p0 0 (rkeys, rkey, temp2)) (h0, h1))).
    2:{
      subst P.
      hnf.
      intros ? ? ?.
      split ; [ | apply H ].
      repeat split.
      - subst p0.
        hnf in H.
        destruct_pre.
        pdisj_apply H_pdisj.
        + rewrite in_fset.
          now rewrite mem_head.
        + rewrite in_fset.
          rewrite in_cons ; simpl.
          now rewrite mem_head.
        + rewrite in_fset.
          rewrite in_cons ; simpl.
          rewrite in_cons ; simpl.
          rewrite mem_head.
          now rewrite Bool.orb_true_r.
      - intros.
        simpl.
        subst p0.
        hnf in H.
        destruct_pre.
        repeat (rewrite get_set_heap_neq ; [ | apply injective_translate_var3 ; reflexivity ]) ;
      rewrite get_set_heap_eq.
        repeat (rewrite get_set_heap_neq ; [ | apply injective_translate_var3 ; reflexivity ]).
        intros.
        destruct i ; [ | easy ].
        simpl.
        rewrite chArray_get_set_eq.
        reflexivity.
    }


    eapply (r_bind) with (mid := (λ '(v0, h0) '(v1, h1), P 10 v1 (h0, h1) /\ (p0 10 v1) (h0, h1))).
    2:{
      intros.
      subst P.
      destruct a₁.
      destruct s.
      rewrite ct_T_prod_propegate.
      rewrite ct_T_prod_propegate.
      subst p0.
      hnf.

      rewrite bind_rewrite.

      eapply rpre_weak_hypothesis_rule'.
      intros ? ? [].

      destruct H.
      eapply better_r_get_remind_lhs with (v := seq_upd_from_arr s x).
      unfold Remembers_lhs , rem_lhs ;
        [ intros ? ? ? ;
          destruct_pre ;
          repeat (rewrite get_set_heap_neq ; [ | apply injective_translate_var3 ; reflexivity ]) ;
          rewrite get_set_heap_eq ].
      reflexivity.

      apply r_ret.
      intros.
      destruct_pre.
      split.
      - eexists.
        split.
        reflexivity.
        intros.

        simpl.
        rewrite !coerce_to_choice_type_K.
        rewrite <- H15.
        repeat (rewrite get_set_heap_neq ; [ | apply injective_translate_var3 ; reflexivity ]).
        rewrite get_set_heap_eq.
        reflexivity.
        assumption.
      - pdisj_apply H_pdisj.
        + rewrite in_fset.
          now rewrite mem_head.
        + rewrite in_fset.
          rewrite in_cons ; simpl.
          now rewrite mem_head.
        + rewrite in_fset.
          rewrite in_cons ; simpl.
          rewrite in_cons ; simpl.
          rewrite mem_head.
          now rewrite Bool.orb_true_r.

    }
    {
      intros.

      set (fun (_ : p_id) => _).
      set (fun (_ : int_type) (_ : _ * _ * _) => _).

      rewrite !coerce_typed_code_K.
      rewrite bind_rewrite.
      rewrite bind_rewrite.

      unfold foldi_both', foldi_both, lift_scope, is_state at 1, lift_code_scope, prog, is_state at 1, foldi.
      unfold foldi_pre ; replace (unsigned _ - unsigned _)%Z with 10%Z by reflexivity.
      replace (Z.to_nat (11 - 1)) with 10 by reflexivity.
      replace (Pos.to_nat 10) with 10 by reflexivity.

      apply (@loop_eq (seq int128 '× int '× int) _ 10 0 _ _ _ _ _ _ _ p0 P).
      { easy. }
      { apply prec_I. }
      { intros. etransitivity. apply prec_O. apply prec_O. }
      {
        intros.

        subst P.
        subst y.
        subst y0.
        hnf.

        remove_get_in_lhs.
        rewrite bind_assoc.
        destruct c as [? []].
        destruct t0 as [].

        set (set_lhs _ _ _).
        eapply r_bind with (mid := λ '(v0, h0) '(v1, h1),
                              (∃ o1 : (λ i : choice_type_choiceType, i) 'int,
                                  v0 = [('int; o1)] ∧ repr o1 = v1) ∧
                                p (h0, h1)) ; subst p.
        {
          set [ _ ].

          replace (translate_call ssprove_jasmin_prog 12%positive
                                  static_funs (s_id~1)%positive l)
            with
            (get_translated_static_fun ssprove_jasmin_prog 12%positive
                                       static_funs (s_id~1)%positive l).
          2:{
            Transparent translate_call.
            simpl.
            cbn.
            repeat (cbn ; rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; rewrite coerce_to_choice_type_K).
            reflexivity.
            Opaque translate_call.
          }
          subst l.
          replace (totce _)
            with (@existT choice_type (fun t : choice_type => Choice.sort (chElement t)) chInt (Pos.of_succ_nat k)).
          2:{
            cbn.
            repeat (cbn ; rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; rewrite coerce_to_choice_type_K).
            unfold totce.
            rewrite Zpos_P_of_succ_nat.
            reflexivity.
          }
          apply (rcon_eq (s_id~1)%positive k).

          shelve.
          easy.
        }

        intros.
        apply rpre_hypothesis_rule.
        intros.
        destruct H1.
        destruct H1.
        destruct H1.
        eapply rpre_weaken_rule.
        2:{
          intros ? ? []. subst.
          apply H2.
        }
        clear H2.
        rewrite H1.
        rewrite <- H3.
        clear H1 H3.
        apply better_r_put_lhs.
        remove_get_in_lhs.
        subst p0.
        remove_get_in_lhs.
        remove_get_in_lhs. fold @bind.

        rewrite bind_assoc.
        set (set_lhs _ _ _).
        eapply r_bind with (mid := λ '(v0, h0) '(v1, h1),
                              (∃ o1 o2 : 'word U128,
                                  v0 = [('word U128; o1); ('word U128; o2)] ∧ (o1, o2) = v1)
                              ∧ p (h0, h1)).
        {

          pose (key_expand_eq (s_id~0~1)%positive x0 t1  (mkWord (nbits:=U128) (toword:=toword) i)  p).
          unfold JKEY_EXPAND in r.

          replace (translate_call _ _ _ _ _)
            with
            (get_translated_static_fun ssprove_jasmin_prog 11%positive
                                       static_funs (s_id~0~1)%positive [('int; x0); ('word U128; t1); ('word U128; (mkWord (nbits:=U128) (toword:=toword) i))]).
          2:{
            Transparent translate_call.
            simpl.
            cbn.
            repeat (cbn ; rewrite <- !coerce_to_choice_type_clause_1_equation_1; rewrite <- coerce_to_choice_type_equation_1; rewrite coerce_to_choice_type_K).
            rewrite !zero_extend_u.
            reflexivity.
            Opaque translate_call.
          }
          unfold lift_to_both0.

          unfold is_pure.
          unfold lift_to_both.
          unfold repr.
          apply r.

          shelve.

        }

        intros.
        apply rpre_hypothesis_rule.
        intros.
        destruct H1.
        destruct H1.
        destruct H1.
        eapply rpre_weaken_rule.
        2:{
          intros ? ? []. subst.
          apply H2.
        }
        clear H2.
        destruct H1.
        destruct a₁0.
        rewrite ct_T_prod_propegate.
        simpl.
        inversion H2.
        subst.
        clear H2.

        apply better_r_put_lhs ; fold @bind.
        apply better_r_put_lhs ; fold @bind.
        simpl in p.
        subst p.
        rewrite !coerce_to_choice_type_K.
        remove_get_in_lhs.
        apply better_r_get_remind_lhs with (v := seq_upd_from_arr t0 x).
        unfold Remembers_lhs , rem_lhs ;
          [ intros ? ? ? ;
            destruct_pre ;
            repeat (rewrite get_set_heap_neq ; [ | apply injective_translate_var3 ; reflexivity ]) ;
            rewrite get_set_heap_eq ].
        reflexivity.
        remove_get_in_lhs.

        rewrite !coerce_to_choice_type_K.
        rewrite !zero_extend_u.
        apply better_r_put_lhs.

        apply better_r_put_get_rhs.
        apply better_r_put_rhs.
        apply better_r_put_get_rhs.
        apply better_r_put_rhs.
        apply better_r_put_get_rhs.
        apply better_r_put_rhs.

        apply r_ret.
        intros.
        shelve.
      }
      shelve.

      Unshelve.
      {
        split ; [ | discriminate].
        intros.
        destruct_pre.
        eexists_set_heap.
        2:{
          apply (precneq_I s_id).
          etransitivity.
          apply H2.
          apply H.
        }

        repeat split.
        {
          pdisj_apply H_pdisj.
          etransitivity.
          apply H.
          etransitivity.
          apply preceq_I.
          apply H2.
        }
        {
          intros.
          rewrite <- H6.
          rewrite get_set_heap_neq.
          reflexivity.
          solve_var_neq.

          apply (precneq_I s_id).
          etransitivity.
          apply H2.
          apply H.

          apply H1.
        }
        {
          easy.
        }
        {
          destruct_pre.
          eexists_set_heap.
          eexists_set_heap.
          eexists_set_heap.
          eexists_set_heap.
          eexists_set_heap.
          eexists_set_heap.

          pdisj_apply H_pdisj.
          etransitivity.
          apply H.
          etransitivity.
          apply preceq_I.
          apply H2.
          all: try (apply (precneq_I s_id) ; etransitivity ; [ apply H2 | apply H ]).
        }
      }
      {
        split.
        intros.
        subst p.
        destruct_pre.
        destruct_pre.
        eexists_set_heap.
        eexists_set_heap.
        repeat split.
        {
          pdisj_apply H_pdisj.
          all: try solve_in_fset.

          etransitivity.
          apply H.
          etransitivity.
          apply preceq_O.
          etransitivity.
          apply preceq_I.
          apply H2.
        }
        {
          intros.
          rewrite <- H8.
          rewrite get_set_heap_neq.
          reflexivity.
          solve_var_neq.
          (apply (precneq_O s_id) ; etransitivity ; [apply preceq_I | etransitivity ; [ apply H2 | apply H ] ]).
          apply H1.
        }
        {
          assumption.
        }
        {
          destruct_pre.
          eexists_set_heap.
          eexists_set_heap.
          eexists_set_heap.
          eexists_set_heap.
          eexists_set_heap.
          eexists_set_heap.
          pdisj_apply H_pdisj.
          etransitivity.
          apply H.
          etransitivity.
          apply preceq_O.
          etransitivity.
          apply preceq_I.
          apply H2.

          all: (apply (precneq_O s_id) ; etransitivity ; [apply preceq_I | etransitivity ; [ apply H2 | apply H ] ]).
        }
        {
          (apply (precneq_O s_id) ; etransitivity ; [apply preceq_I | etransitivity ; [ apply H2 | apply H ] ]).
        }
        {
          (apply (precneq_O s_id) ; etransitivity ; [apply preceq_I | etransitivity ; [ apply H2 | apply H ] ]).
        }
        {
          discriminate.
        }
      }
      {
        destruct_pre.
        repeat split.
        {
          pdisj_apply H_pdisj ; solve_in_fset.
        }
        {
          intros.

          remove_get_set_heap.


          destruct (Nat.eq_dec i0 k.+1).
          + subst.
            unfold Hacspec_Lib_Pre.seq_index.
            simpl.
            unfold Hacspec_Lib_Pre.seq_push.
            unfold seq_index_nat.
            rewrite setmE.
            replace (Z.to_nat _) with (k.+1).
            2:{
              cbn.
              rewrite Zmod_small.
              setoid_rewrite SuccNat2Pos.id_succ.
              reflexivity.
              do 10 (destruct k ; [ easy | ]) ; discriminate.
            }
            replace (seq_len_nat t0) with k.+1.
            2:{
              rewrite <- H33.
              pose seq_to_list_size.
              rewrite (@seq_to_list_size int128).
              reflexivity.
            }
            rewrite eqtype.eq_refl.
            now rewrite chArray_get_set_eq.
          + assert (i0 <= k) by lia.
            specialize (H18 i0 H2).

            assert (forall (A : ChoiceEquality) (H_default : Default A) t (s : A) i, (0 <= Z.of_nat i < modulus (wsize_size_minus_1 U32).+1)%Z -> i < size (Hacspec_Lib_Pre.seq_to_list _ t) -> Hacspec_Lib_Pre.seq_index (Hacspec_Lib_Pre.seq_push t s) (repr (Z.of_nat i)) = Hacspec_Lib_Pre.seq_index t (repr (Z.of_nat i))).
            {
              clear ; intros.
              unfold Hacspec_Lib_Pre.seq_index.
              unfold Hacspec_Lib_Pre.seq_index_nat.
              unfold Hacspec_Lib_Pre.seq_push.
              rewrite setmE.
              rewrite eqtype.eq_sym.
              rewrite gtn_eqF.
              2:{
                simpl.
                setoid_rewrite wunsigned_repr.
                rewrite Zmod_small.
                rewrite Nat2Z.id.
                rewrite seq_to_list_size in H0.
                apply H0.
                apply H.
              }
              reflexivity.
            }

            rewrite H3.
            2:{
              split. lia.
              apply Z.lt_le_trans with (m := Z.of_nat 10).
              2: easy.
              apply inj_lt.
              lia.
            }
            2:{
              now rewrite H33.
            }
            rewrite <- H18.

            rewrite chArray_get_set_neq.

            remove_get_set_heap.
            remove_get_set_heap.

            reflexivity.

            { solve_var_neq. }
            { lia. }
        }
        {
          rewrite seq_push_list_app.
          rewrite size_cat.
          rewrite H33.
          now rewrite addn1.
        }
        {
          rewrite !zero_extend_u.
          destruct_pre.
          eexists_set_heap.
          eexists ; split.
          2:{
            rewrite seq_udp_from_arr_push.
            rewrite H33.
            simpl.
            reflexivity.
          }
          eexists ; split.
          2:{
            reflexivity.
          }
          eexists ; split.
          2:{
            reflexivity.
          }
          eexists ; split.
          2:{
            reflexivity.
          }
          eexists ; split.
          2:{
            reflexivity.
          }
          pdisj_apply H_pdisj ; solve_in_fset.
        }
      }
      {
        intros.
        destruct c as [[]].
        destruct_pre.
        subst p0.
        hnf.
        repeat split.
        {
          intros.
          subst.
          destruct_pre.
          eexists ; split.
          2:{
            rewrite set_heap_commut.
            reflexivity.
            apply injective_translate_var2.
            red ; intros.
            subst.
            eapply prec_precneq.
            apply H.
            apply H1.
          }
          eexists ; split.
          2:{
            rewrite set_heap_commut.
            reflexivity.
            apply injective_translate_var2.
            red ; intros.
            subst.
            eapply prec_precneq.
            apply H.
            apply H1.
          }
          eexists ; split.
          2:{
            reflexivity.
          }
          eexists ; split.
          2:{
            reflexivity.
          }
          eexists ; split.
          2:{
            reflexivity.
          }
          eexists ; split.
          2:{
            rewrite set_heap_commut.
            reflexivity.
            apply injective_translate_var2.
            red ; intros.
            subst.
            eapply prec_precneq.
            apply H.
            apply H1.
          }
          pdisj_apply H_pdisj.
          etransitivity.
          apply H.
          apply H1.
        }
        {
          discriminate.
        }
      }
    }
  Qed.

  Lemma shift_rows_eq id0 (state : 'word U128) (pre : precond) :
    (pdisj pre id0 fset0) ->
    ⊢ ⦃ pre ⦄ ret (waes.ShiftRows state) ≈
      prog (is_state (shiftrows state))
      ⦃ λ '(v0, h0) '(v1, h1), v0 = v1 ∧ pre (h0, h1) ⦄.
    intros.
    unfold waes.ShiftRows.
    unfold waes.to_matrix.
    unfold waes.to_state.
    rewrite rebuild_32_eq.
    rewrite rebuild_32_eq.
    rewrite rebuild_32_eq.
    rewrite rebuild_32_eq.
    rewrite rebuild_128_eq.
    unfold shiftrows.
    rewrite !index_32_eq.
    rewrite !index_8_eq.

    set (rebuild_u32 _ _ _ _).
    set (rebuild_u32 _ _ _ _).
    set (rebuild_u32 _ _ _ _).
    set (rebuild_u32 _ _ _ _).

    apply r_ret.
    {
      intros.
      split.
      - reflexivity.
      - easy.
    }

    all: lia.
  Qed.

  Lemma sub_bytes_eq id0 (state : 'word U128) (pre : precond) :
    (pdisj pre id0 fset0) ->
  ⊢ ⦃ λ '(s₀0, s₁0), pre (s₀0, s₁0) ⦄ ret (waes.SubBytes state) ≈
     prog (is_state (subbytes (state)))
     ⦃ λ '(v0, h0) '(v1, h1), v0 = v1 ∧ pre (h0, h1) ⦄.
  Proof.
    intros.
    unfold waes.SubBytes.
    unfold subbytes.

    simpl map.
    rewrite rebuild_128_eq.

    rewrite !SubWord_eq.
    rewrite !index_32_eq.
    apply r_ret ; easy.

    all: lia.
  Qed.

  Lemma mix_columns_eq id0 (state : 'word U128) (pre : precond) :
    (pdisj pre id0 fset0) ->
  ⊢ ⦃ λ '(s₀0, s₁0), pre (s₀0, s₁0) ⦄ ret (waes.MixColumns state) ≈
     prog (is_state (mixcolumns (state)))
     ⦃ λ '(v0, h0) '(v1, h1), v0 = v1 ∧ pre (h0, h1) ⦄.
  Proof.
    (* Mix Columns is not defined in jasmin,
       so we admit the equality *)
  Admitted.

  Lemma aes_enc_eq id0 state key (pre : precond) :
    (pdisj pre id0 fset0) ->
    ⊢ ⦃ pre ⦄
        ret (waes.wAESENC state key)
        ≈
        prog (is_state (aesenc state key))
        ⦃ fun '(v0, h0) '(v1, h1) => (v0 = v1)  /\ pre (h0, h1) ⦄.
  Proof.
    intros.
    unfold waes.wAESENC.
    unfold aesenc.

    match_pattern_and_bind (waes.ShiftRows state).
    {
      Set Printing Coercions.
      unfold lift_to_both0.
      unfold lift_to_both.
      unfold is_pure.
      unfold lift_scope.
      unfold is_state at 1.
      unfold lift_code_scope.

      apply (shift_rows_eq id0).
      apply H.
    }

    subst.

    match_pattern_and_bind (waes.SubBytes a₁).
    {
      unfold lift_to_both0.
      unfold lift_to_both.
      unfold is_pure.
      unfold lift_scope.
      unfold is_state at 1.
      unfold lift_code_scope.

      apply (sub_bytes_eq id0).
      apply H.
    }

    subst.

    match_pattern_and_bind (waes.MixColumns a₁0).
    {
      unfold lift_to_both0.
      unfold lift_to_both.
      unfold is_pure.
      unfold lift_scope.
      unfold is_state at 1.
      unfold lift_code_scope.

      apply (mix_columns_eq id0).
      apply H.
    }

    subst.

    all: try (intros ? ? [] ; subst ; assumption).

    apply r_ret.
    intros.
    split.
    - reflexivity.
    - assumption.
  Qed.

  Lemma aes_enc_last_eq id0 state key (pre : precond) :
    (pdisj pre id0 fset0) ->
    ⊢ ⦃ pre ⦄
        ret (waes.wAESENCLAST state key)
        ≈
        prog (is_state (aesenclast state key))
        ⦃ fun '(v0, h0) '(v1, h1) => (v0 = v1)  /\ pre (h0, h1) ⦄.
  Proof.
    intros.
    unfold waes.wAESENCLAST.
    unfold aesenclast.

    match_pattern_and_bind (waes.ShiftRows state).
    {
      unfold lift_to_both0.
      unfold lift_to_both.
      unfold is_pure.
      unfold lift_scope.
      unfold is_state at 1.
      unfold lift_code_scope.

      apply (shift_rows_eq id0).
      apply H.
    }

    subst.

    match_pattern_and_bind (waes.SubBytes a₁).
    {
      unfold lift_to_both0.
      unfold lift_to_both.
      unfold is_pure.
      unfold lift_scope.
      unfold is_state at 1.
      unfold lift_code_scope.

      apply (sub_bytes_eq id0).
      apply H.
    }

    subst.

    all: try (intros ? ? [] ; subst ; assumption).
    apply r_ret.
    intros.
    split.
    - reflexivity.
    - assumption.
  Qed.


  Notation state_loc := (CE_loc_to_loc state_120_loc).
  Lemma addroundkey_eq id0 (rkeys : 'array) (rkeys' : seq int128) m  (pre : precond) :
    (pdisj pre id0 (fset [ state_loc ])) ->
    (forall k, k <= 10 -> ((chArray_get U128 rkeys k (wsize_size U128))
    = is_pure (seq_index rkeys' (lift_to_both0 (repr k))))) ->
    ⊢ ⦃ pre ⦄
        JAES_ROUNDS id0 rkeys m
        ≈
        is_state (aes_rounds rkeys' m)
        ⦃ fun '(v0, h0) '(v1, h1) => (exists o1, v0 = [('word U128; o1)] /\ o1 = v1)  /\ pre (h0, h1) ⦄.
  Proof.
    intros H_pdisj rkeys_ext.
    set (JAES_ROUNDS _ _ _).
    unfold JAES_ROUNDS in r.
    Transparent translate_call.
    unfold get_translated_static_fun in r.
    simpl in r.
    unfold translate_call_body in r.
    Opaque translate_call.
    simpl in r.
    subst r.
    rewrite !zero_extend_u.

    apply better_r, r_put_lhs, better_r.
    apply better_r, r_put_lhs, better_r.
    remove_get_in_lhs.
    apply better_r, r_put_lhs, better_r.
    remove_get_in_lhs.
    remove_get_in_lhs.
    rewrite !zero_extend_u.

    unfold aes_rounds.

    rewrite !coerce_to_choice_type_K.

    unfold lift_to_both0 at 1.

    unfold let_mut_both at 1, is_state at 1, is_state at 1, is_state at 1.
    Opaque is_state. Opaque is_pure.
    simpl. Transparent is_state. Transparent is_pure.

    rewrite (rkeys_ext 0) ; [ | lia ].

    bind_jazz_bind.
    {
      (* xor *)
      apply r_ret.
      intros.
      split.
      reflexivity.
      assumption.
    }

    apply rpre_hypothesis_rule'.
    intros ? ? [].
    subst.
    eapply rpre_weaken_rule.
    2:{
      intros ? ? []. subst.
      apply H0.
    }
    clear H0.

    apply better_r_put_lhs.
    apply better_r_put_get_rhs.
    apply better_r_put_rhs.

    rewrite bind_assoc.
    rewrite bind_assoc.
    rewrite <- bind_assoc.

    eapply r_bind.
    {
      set (fun (_ : p_id) => _).
      set (fun (_ : int_type) (_ : _) => _).

      rewrite !coerce_typed_code_K.
      rewrite bind_rewrite.
      rewrite bind_rewrite.

      unfold foldi_both', foldi_both, lift_scope, is_state at 1, lift_code_scope, prog, is_state at 1, foldi.
      unfold foldi_pre ; replace (unsigned _ - unsigned _)%Z with 9%Z by reflexivity.
      replace (Z.to_nat (10 - 1)) with 9 by reflexivity.
      replace (Pos.to_nat 9) with 9 by reflexivity.

      set (y1 :=
      fun H : int =>
        set_rhs state_loc H
          (set_lhs
             (translate_var id0
                {| vtype := sword U128; vname := "state.327" |}) H
                (set_lhs
                   (translate_var id0
                      {| vtype := sword U128; vname := "in.326" |}) m
                   (set_lhs
                      (translate_var id0
                         {| vtype := sarr 176; vname := "rkeys.325" |})
                      rkeys pre)))).
      eapply rpre_weaken_rule with (pre := y1 a₁).
      2:{
        intros.
        subst y1 ; hnf.
        destruct_pre.
        eexists_set_heap.
        eexists ; split.
        2:{
          rewrite set_heap_contract.
          reflexivity.
        }
        eexists_set_heap.
        eexists_set_heap.
        assumption.
      }

      apply (@loop_eq_simpl int _ 9 0 _ _ _ _ _ _ _ (fun _ => y1) a₁) ; subst y1 ; hnf.
      { easy. }
      { apply prec_I. }
      { reflexivity. }
      {
        intros.
        remove_get_in_lhs.
        remove_get_in_lhs.
        remove_get_in_lhs.

        (* AES Enc loop *)
        bind_jazz_hac.
        - unfold sopn_sem.
          unfold sopn.get_instr_desc.
          unfold asm_op_instr.
          unfold asm_opI.
          unfold arch_extra.get_instr_desc.
          unfold semi.
          unfold instr_desc.
          unfold instr_desc_op.
          unfold _asm_op_decl.
          unfold _asm.
          unfold x86_extra.
          unfold x86.x86.
          unfold x86_op_decl.
          unfold x86_instr_desc.
          unfold id_semi.
          unfold Ox86_AESENC_instr.
          unfold mk_instr_aes2.
          unfold ".1".
          unfold x86_AESENC.
          unfold tr_app_sopn_tuple.
          unfold encode_tuple.
          unfold jasmin_translate.encode.
          unfold w_ty.
          unfold map.
          unfold lchtuple.
          unfold chCanonical.
          unfold w2_ty.
          unfold tr_app_sopn.
          unfold embed_tuple.
          unfold embed_ot.
          unfold unembed.
          simpl set_lhs.
          unfold truncate_el.
          unfold totce.
          unfold ".π2".

          rewrite !coerce_to_choice_type_K.

          set (truncate_chWord _ _).
          set (truncate_chWord _ _).
          cbn in s0.
          cbn in s.
          subst s0.
          subst s.
          rewrite !zero_extend_u.

          unfold seq_index.
          unfold lift_to_both0.
          unfold lift_to_both at 2.
          unfold is_pure at 2.
          unfold lift_to_both at 2.
          unfold is_pure at 2.
          pose (rkeys_ext (S k)).
          simpl in e.
          rewrite <- e ; [ | lia ].
          clear e.

          apply (aes_enc_eq s_id c (chArray_get U128 rkeys (Pos.of_succ_nat k) (wsize_size U128))).

          (* pdisj *)
          {
            simpl.
            split.

            {
              intros.
              destruct_pre.
              eexists ; split.
              2:{
                rewrite set_heap_commut.
                reflexivity.
                solve_var_neq.
                eapply prec_precneq.
                apply H.
                apply H2.
              }.

              eexists_set_heap.
              eexists_set_heap.
              eexists_set_heap.
              eexists_set_heap.

              pdisj_apply H_pdisj.

              etransitivity.
              apply H.
              apply H2.

              {
                eapply prec_precneq.
                apply H.
                apply H2.
              }

              {
                eapply prec_precneq.
                apply H.
                apply H2.
              }

              {
                eapply prec_precneq.
                apply H.
                apply H2.
              }
            }
            {
              intros.
              destruct_pre.
              discriminate.
            }
          }
        - apply better_r_put_get_rhs.
          apply better_r_put_rhs.
          apply better_r_put_lhs.

          apply r_ret.
          intros.
          destruct_pre.
          eexists ; split.
          2:{
            reflexivity.
          }
          eexists ; split.
          2:{
            reflexivity.
          }
          eexists ; split.
          2:{
            rewrite [set_heap (set_heap (set_heap H15 _ _) _ _) _ _]set_heap_commut.
            rewrite set_heap_commut.
            reflexivity.
            solve_var_neq.
            solve_var_neq.
          }
          eexists ; split.
          2:{
            rewrite [set_heap (set_heap H15 _ _) _ _]set_heap_commut.
            rewrite [set_heap (set_heap (set_heap H15 _ _) _ _) _ _]set_heap_commut.
            reflexivity.
            solve_var_neq.
            solve_var_neq.
          }
          pdisj_apply H_pdisj.
          solve_in_fset.
      }
      (* pdisj *)
      {
        intros.
        split.
        {
          intros.
          destruct_pre.
          eexists_set_heap.
          eexists_set_heap.
          eexists_set_heap.
          eexists_set_heap.
          pdisj_apply H_pdisj.
          {
            etransitivity.
            apply H.
            apply H1.
          }
          {
            eapply prec_precneq.
            apply H.
            apply H1.
          }
          {
            eapply prec_precneq.
            apply H.
            apply H1.
          }
          {
            eapply prec_precneq.
            apply H.
            apply H1.
          }
        }
        {
          discriminate.
        }
      }
    }

    intros.
    hnf.
    remove_get_in_lhs.
    remove_get_in_lhs.
    rewrite <- bind_ret.
    bind_jazz_hac.
    {
       (* AES Enc last *)

      unfold sopn_sem.
      unfold sopn.get_instr_desc.
      unfold asm_op_instr.
      unfold asm_opI.
      unfold arch_extra.get_instr_desc.
      unfold semi.
      unfold instr_desc.
      unfold instr_desc_op.
      unfold _asm_op_decl.
      unfold _asm.
      unfold x86_extra.
      unfold x86.x86.
      unfold x86_op_decl.
      unfold x86_instr_desc.
      unfold id_semi.
      unfold Ox86_AESENCLAST_instr.
      unfold mk_instr_aes2.
      unfold ".1".
      unfold x86_AESENCLAST.
      unfold tr_app_sopn_tuple.
      unfold encode_tuple.
      unfold jasmin_translate.encode.
      unfold w_ty.
      unfold map.
      unfold lchtuple.
      unfold chCanonical.
      unfold w2_ty.
      unfold tr_app_sopn.
      unfold embed_tuple.
      unfold embed_ot.
      unfold unembed.
      unfold truncate_el.
      unfold totce.
      unfold ".π2".

      rewrite !coerce_to_choice_type_K.
      set (truncate_chWord _ _).
      set (truncate_chWord _ _).
      cbn in s0.
      cbn in s.
      subst s0.
      subst s.
      rewrite !zero_extend_u.

      unfold seq_index.
      unfold lift_to_both0.
      unfold lift_to_both.
      unfold is_pure.
      pose (rkeys_ext 10).
      simpl in e.
      rewrite <- e ; [ | lia ].
      clear e.

      apply (aes_enc_last_eq id0~1 a₁0 (chArray_get U128 rkeys 10 (wsize_size U128))).

      (* pdisj *)
      {
        split.
        {
          intros.
          destruct_pre.
          eexists ; split.
          2:{
            reflexivity.
          }
          eexists ; split.
          2:{
            rewrite set_heap_commut.
            reflexivity.
            solve_var_neq.
            eapply precneq_I.
            apply H0.
          }
          eexists_set_heap.
          eexists_set_heap.
          pdisj_apply H_pdisj.

          etransitivity.
          apply preceq_I.
          apply H0.

          {
            eapply precneq_I.
            apply H0.
          }
          {
            eapply precneq_I.
            apply H0.
          }
        }
        {
          intros.
          destruct_pre.
          discriminate.
        }
      }
    }

    apply better_r_put_lhs.
    remove_get_in_lhs.

    apply r_ret.

    intros.

    destruct_pre.
    split.
    - eexists.
      split.
      + reflexivity.
      + setoid_rewrite zero_extend_u.
        reflexivity.
    - pdisj_apply H_pdisj.
      rewrite in_fset.
      now rewrite mem_head.
  Qed.

  Lemma aes_eq id0 key m  (pre : precond) :
    (pdisj pre id0 (fset [state_loc ; rkeys_loc; temp2_loc; rkey_loc])) ->
    ⊢ ⦃ pre ⦄
        JAES id0 key m
        ≈
        is_state (aes key m)
        ⦃ fun '(v0, h0) '(v1, h1) => (exists o1, v0 = [('word U128; o1)] /\ o1 = v1)  /\ pre (h0, h1) ⦄.
  Proof.
    intros H_pdisj.
    set (JAES _ _ _).
    unfold JAES_ROUNDS in r.
    unfold get_translated_static_fun, JAES_ROUNDS, get_translated_static_fun, translate_prog_static, translate_funs_static, translate_call_body in r.
    Opaque translate_call.
    simpl in r.
    subst r.
    rewrite !zero_extend_u.

    unfold aes.

    apply better_r_put_lhs.
    apply better_r_put_lhs.
    remove_get_in_lhs.

    rewrite bind_assoc.
    rewrite bind_assoc.

    eapply r_bind.
    apply keys_expand_eq.

    split.
    {
      intros.
      destruct_pre.
      unfold set_lhs.
      eexists (set_heap (set_heap H4 ($$"key.314") _) (translate_var s_id' v) a).
      split.
      2:{
        rewrite set_heap_commut.
        f_equal.
        f_equal.
        apply f_equal.
        reflexivity.
        apply injective_translate_var2.
        red ; intros.
        subst.
        now apply (precneq_I s_id').
      }
      exists (set_heap H4 (translate_var s_id' v) a).
      split.
      2:{
        rewrite set_heap_commut.
        reflexivity.
        apply injective_translate_var2.
        red ; intros.
        subst.
        now apply (precneq_I s_id').
      }
      pdisj_apply H_pdisj.
      etransitivity.
      apply preceq_I.
      apply H0.
    }
    {
      intros.
      destruct_pre.
      eexists.
      split ; [ | reflexivity ].
      eexists.
      split ; [ | reflexivity ].
      apply H_pdisj.

      rewrite in_fset.
      rewrite in_fset in H.
      rewrite in_cons ; simpl.
      rewrite H.
      now rewrite Bool.orb_true_r.
      apply H4.
    }

    intros.
    apply rpre_hypothesis_rule.
    intros ? ? [].
    eapply rpre_weaken_rule.
    2:{
      intros ? ? []. subst.
      apply H0.
    }
    clear H0.
    destruct H.
    destruct H.
    subst.
    apply better_r_put_lhs.
    remove_get_in_lhs. fold @bind.
    remove_get_in_lhs.

    rewrite bind_assoc.
    rewrite bind_assoc.

    rewrite <- bind_ret.
    eapply r_bind.

    apply addroundkey_eq.
    {
      split.
      - intros.
        destruct_pre.
        eexists.
        split.
        2:{
          rewrite ![set_heap _ (translate_var s_id' v) a]set_heap_commut
          ; (reflexivity ||
               (apply injective_translate_var2 ;
                red ; intros ; subst ;
                apply (precneq_O s_id') ;
                etransitivity ; [apply preceq_I | apply H1])).
        }
        eexists.
        split ; [ | reflexivity ].
        eexists.
        split ; [ | reflexivity ].
        pdisj_apply H_pdisj.
        etransitivity.
        apply preceq_O.
        etransitivity.
        apply preceq_I.
        apply H1.
      - intros.
        destruct_pre.
        eexists.
        split ; [| reflexivity ].
        eexists.
        split ; [ | reflexivity ].
        eexists.
        split ; [ | reflexivity ].
        eapply H_pdisj.

        rewrite in_fset.
        rewrite in_cons ; simpl.
        rewrite in_cons ; simpl.
        rewrite in_fset in H.
        rewrite in_cons in H ; simpl.
        rewrite Bool.orb_false_r in H.
        rewrite orbA.
        rewrite H.
        now rewrite Bool.orb_true_l.
        apply H7.
    }
    {
      intros.
      rewrite !coerce_to_choice_type_K.
      specialize (H0 k H).
      rewrite H0.
      reflexivity.
    }

    intros.
    apply rpre_hypothesis_rule.
    intros ? ? [].
    eapply rpre_weaken_rule.
    2:{
      intros ? ? []. subst.
      apply H1.
    }
    clear H1.
    destruct H.
    destruct H.
    subst.
    apply better_r_put_lhs.
    rewrite bind_rewrite.
    remove_get_in_lhs.
    apply r_ret.

    intros.
    destruct_pre.
    split.
    eexists.
    split ; [reflexivity | ].
    rewrite !zero_extend_u.
    setoid_rewrite zero_extend_u.
    reflexivity.
    pdisj_apply H_pdisj.
  Qed.

End Hacspec.
