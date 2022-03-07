(** This file was automatically generated using Hacspec **)
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From CoqWord Require Import ssrZ word.
From Jasmin Require Import word.
Require Import ChoiceEquality.

From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope bool_scope.

Require Import Hacspec_Lib_Comparable.
Require Import Hacspec_Lib_Pre.
Require Import Hacspec_Lib.

Open Scope hacspec_scope.


Obligation Tactic :=
(intros ; do 2 ssprove_valid'_2) ||
(try (Tactics.program_simpl; fail); simpl). (* Old Obligation Tactic *)

Require Import Hacspec_Lib.

Definition poly_key_t := nseq (uint8) (usize 32).

Definition blocksize_v : (uint_size) :=
  ((usize 16)).

Definition poly_block_t := nseq (uint8) (usize 16).

Definition poly1305_tag_t := nseq (uint8) (usize 16).

Notation "'sub_block_t'" := (byte_seq) : hacspec_scope.

Notation "'block_index_t'" := (uint_size) : hacspec_scope.

Definition field_canvas_t := nseq (int8) (17).
Definition field_element_t := nat_mod 0x03fffffffffffffffffffffffffffffffb.

Notation "'poly_state_t'" := ((
  field_element_t '×
  field_element_t '×
  poly_key_t
)) : hacspec_scope.

Import Hacspec_Lib_Pre.
Definition poly1305_encode_r_pure (b_0 : poly_block_t) : field_element_t :=
  let n_4 : uint128 :=
    uint128_from_le_bytes (array_from_seq (16) (array_to_seq (b_0))) in 
  let n_4 :=
    (n_4) .& (secret (
        @repr U128 21267647620597763993911028882763415551) : int128) in 
  nat_mod_from_secret_literal (n_4).

Import Hacspec_Lib.
Definition n_4_loc : Location :=
  (uint128 : choice_type ; 7%nat).
Program Definition poly1305_encode_r_state
  (b_0 : poly_block_t)
  : code (fset (path.sort leb [ n_4_loc])) [interface] (@ct (
      field_element_t)) :=
  (({code  temp_1 ←
        (array_to_seq (b_0)) ;;
      let temp_1 : seq uint8 :=
        (temp_1) in
       temp_2 ←
        (array_from_seq (16) (temp_1)) ;;
       temp_3 ←
        (uint128_from_le_bytes (temp_2)) ;;
      #put n_4_loc := 
        (temp_3) ;;
      n_4 ← get n_4_loc ;;
      let n_4 : uint128 :=
        (n_4) in
       temp_5 ←
        (secret (@repr U128 21267647620597763993911028882763415551)) ;;
      let temp_5 : int128 :=
        (temp_5) in
      n_4 ← get n_4_loc ;;
      
      #put n_4_loc := 
        ((n_4) .& (temp_5)) ;;
      n_4 ← get n_4_loc ;;
      
       temp_6 ←
        (nat_mod_from_secret_literal (n_4)) ;;
      @pkg_core_definition.ret (field_element_t) ( (temp_6)) } : code (fset (
          path.sort leb [ n_4_loc])) [interface] _)).
Fail Next Obligation.

Program Instance poly1305_encode_r
  (b_0 : poly_block_t)
  : both (fset (path.sort leb [ n_4_loc])) field_element_t :=
  {|
  is_pure := poly1305_encode_r_pure(b_0 : poly_block_t);
  is_state := poly1305_encode_r_state(b_0 : poly_block_t);
  |}.
Next Obligation.
  intros.
  unfold poly1305_encode_r_state.
  unfold poly1305_encode_r_pure.
  unfold lift_to_code.
  unfold prog.

  unfold array_to_seq.
  unfold array_from_seq.
  unfold uint128_from_le_bytes.
  unfold secret.
  unfold nat_mod_from_secret_literal.

  unfold lift_to_code.
  
  step_code.
  reflexivity.
Qed.

Import Hacspec_Lib_Pre.
Definition poly1305_encode_block_pure (b_8 : poly_block_t) : field_element_t :=
  let n_12 : uint128 :=
    uint128_from_le_bytes (array_from_seq (16) (array_to_seq (b_8))) in 
  let f_14 : field_element_t :=
    nat_mod_from_secret_literal (n_12) in 
  (f_14) +% (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (
      usize 128) : field_element_t).

Import Hacspec_Lib.

Program Definition poly1305_encode_block_state
  (b_8 : poly_block_t)
  : code (fset.fset0) [interface] (@ct (field_element_t)) :=
  (({code  temp_9 ←
        (array_to_seq (b_8)) ;;
      let temp_9 : seq uint8 :=
        (temp_9) in
       temp_10 ←
        (array_from_seq (16) (temp_9)) ;;
       temp_11 ←
        (uint128_from_le_bytes (temp_10)) ;;
      let n_12 : uint128 :=
        (temp_11) in
       temp_13 ←
        (nat_mod_from_secret_literal (n_12)) ;;
      let f_14 : field_element_t :=
        (temp_13) in
       temp_15 ←
        (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (usize 128)) ;;
      let temp_15 : field_element_t :=
        (temp_15) in
      @pkg_core_definition.ret (field_element_t) ( ((f_14) +% (
          temp_15))) } : code (fset.fset0) [interface] _)).
Fail Next Obligation.

Program Instance  poly1305_encode_block
  (b_8 : poly_block_t)
  : both (fset.fset0) field_element_t :=
  {|
  is_pure := poly1305_encode_block_pure(b_8 : poly_block_t);
  is_state := poly1305_encode_block_state(b_8 : poly_block_t);
  |}.
Next Obligation.
  unfold poly1305_encode_block_state.
  unfold poly1305_encode_block_pure.
  unfold lift_to_code.
  unfold prog.

  unfold array_to_seq.
  unfold array_from_seq.
  unfold uint128_from_le_bytes.
  unfold nat_mod_from_secret_literal.
  unfold nat_mod_pow2.

  unfold lift_to_code.
  
  step_code.
  reflexivity.
Qed.

Import Hacspec_Lib_Pre.
Definition poly1305_encode_last_pure
  (pad_len_23 : block_index_t)
  (b_16 : sub_block_t)
  : field_element_t :=
  let n_20 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default) (16) (b_16) (usize 0) (
        seq_len (b_16))) in 
  let f_22 : field_element_t :=
    nat_mod_from_secret_literal (n_20) in 
  (f_22) +% (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) ((usize 8) .* (
        pad_len_23)) : field_element_t).

Import Hacspec_Lib.

Program Definition poly1305_encode_last_state
  (pad_len_23 : block_index_t)
  (b_16 : sub_block_t)
  : code (fset.fset0) [interface] (@ct (field_element_t)) :=
  (({code  temp_17 ←
        (seq_len (b_16)) ;;
       temp_18 ←
        (array_from_slice (default) (16) (b_16) (usize 0) (temp_17)) ;;
       temp_19 ←
        (uint128_from_le_bytes (temp_18)) ;;
      let n_20 : uint128 :=
        (temp_19) in
       temp_21 ←
        (nat_mod_from_secret_literal (n_20)) ;;
      let f_22 : field_element_t :=
        (temp_21) in
       temp_24 ←
        (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) ((usize 8) .* (
              pad_len_23))) ;;
      let temp_24 : field_element_t :=
        (temp_24) in
      @pkg_core_definition.ret (field_element_t) ( ((f_22) +% (
          temp_24))) } : code (fset.fset0) [interface] _)).
Fail Next Obligation.

Program Instance  poly1305_encode_last
  (pad_len_23 : block_index_t)
  (b_16 : sub_block_t)
  : both (fset.fset0) field_element_t :=
  {|
  is_pure := poly1305_encode_last_pure(pad_len_23 : block_index_t)
  (b_16 : sub_block_t);
  is_state := poly1305_encode_last_state(pad_len_23 : block_index_t)
  (b_16 : sub_block_t);
  |}.
Next Obligation.
  unfold poly1305_encode_last_state.
  unfold poly1305_encode_last_pure.
  unfold lift_to_code.
  unfold prog.

  unfold array_to_seq.
  unfold array_from_seq.
  unfold uint128_from_le_bytes.
  unfold nat_mod_from_secret_literal.
  unfold nat_mod_pow2.

  unfold lift_to_code.
  
  step_code.
  reflexivity.
Qed.

Import Hacspec_Lib_Pre.
Definition poly1305_init_pure (k_25 : poly_key_t) : poly_state_t :=
  let r_30 : field_element_t :=
    poly1305_encode_r (array_from_slice (default) (16) (array_to_seq (k_25)) (
        usize 0) (usize 16)) in 
  (nat_mod_zero , r_30, k_25).

Import Hacspec_Lib.

Program Definition poly1305_init_state
  (k_25 : poly_key_t)
  : code (fset (path.sort leb [ n_4_loc])) [interface] (@ct (poly_state_t)) :=
  (({code  temp_26 ←
        (array_to_seq (k_25)) ;;
      let temp_26 : seq uint8 :=
        (temp_26) in
       temp_27 ←
        (array_from_slice (default) (16) (temp_26) (usize 0) (usize 16)) ;;
       temp_28 ←
        (poly1305_encode_r (temp_27)) ;;
      let r_30 : field_element_t :=
        (temp_28) in
       temp_29 ←
        (nat_mod_zero ) ;;
      @pkg_core_definition.ret ((
          field_element_t '×
          field_element_t '×
          poly_key_t
        )) ( ((temp_29, r_30, k_25))) } : code (fset (
          path.sort leb [ n_4_loc])) [interface] _)).
Fail Next Obligation.



Program Instance  poly1305_init
  (k_25 : poly_key_t)
  : both (fset (path.sort leb [ n_4_loc])) poly_state_t :=
  {|
  is_pure := poly1305_init_pure(k_25 : poly_key_t);
  is_state := poly1305_init_state(k_25 : poly_key_t);
  |}.
Next Obligation.
  unfold poly1305_init_state.
  unfold poly1305_init_pure.
  unfold lift_to_code.
  unfold prog.

  unfold array_to_seq.
  unfold array_from_slice.
  unfold nat_mod_zero.
  unfold lift_to_code.
  step_code.

  unfold poly1305_encode_r.
  unfold is_pure.
  unfold is_state.

  assert (forall (A : ChoiceEquality) k (v : raw_code A) `(@both fset.fset0 A),
               ⊢ ⦃ fun '(h₀, h₁) => h₀ = h₁ ⦄
                 temp ← lift_to_code (L := fset.fset0) (I := [interface]) is_pure ;;
                 k temp
                   ≈
                 v 
                 ⦃ fun '(a, _) '(b, _) => a = b ⦄
               ->
         ⊢ ⦃ fun '(h₀, h₁) => h₀ = h₁ ⦄
                 temp ← is_state ;;
                 k temp
                   ≈
                 v 
             ⦃ fun '(a, _) '(b, _) => a = b ⦄).
  {
    intros.
    destruct H. cbn in *.

    pose (@rrewrite_eqDistrL A A (fun '(h₀, h₁) => h₀ = h₁) (fun '(a, _) '(b, _) => a = b) (k is_pure)).
    apply r.
    apply H0.

    assert (forall {A} (K₀ K₁ : raw_code A),
               ⊢ ⦃ fun '(h₀, h₁) => h₀ = h₁ ⦄ K₀ ≈ K₁ ⦃ fun '(a, _) '(b, _) => a = b ⦄ ->
               forall s₀ s₁,
                 (fun '(h₀, h₁) => h₀ = h₁) (s₀, s₁) ->
                 RulesStateProb.θ_dens (RulesStateProb.θ0  (pkg_semantics.repr K₀) s₀) =
                   RulesStateProb.θ_dens (RulesStateProb.θ0 (pkg_semantics.repr K₁) s₁)).
    {
      clear ; intros.    
      eapply to_sem_jdg in H.

      apply SubDistr.distr_ext.
      
      unfold ssrfun.eqfun.
      intros [x y].
      rewrite distr.pr_pred1.
      rewrite distr.pr_pred1.
      simpl in *.

      unfold ssrbool.PredOfSimpl.coerce.
      unfold ssrfun.fun_of_simpl.
      unfold eqtype.pred1.
      simpl.

      (* unfold eqtype.eq_op. *)
      (* simpl. *)
      
      pose (@RulesStateProb.Pr_eq A A heap_choiceType heap_choiceType).    
      specialize e with (Ψ := fun '(h₀, h₁) => h₀ = h₁).
      specialize e with (ϕ := fun '(a, _) '(b, _) => a = b).
      apply e ; clear e.

      apply H.
      apply H0.

      
      
      intros [] []. intros ; subst.
      split ; intros.
      apply Couplings.reflection_nonsense in H0.      
      inversion H0 ; subst.
      reflexivity.
    }
    
    intros.
    simpl.
    apply (H A _ _ (fun '(h₀, h₁) => h₀ = h₁) ).
    reflexivity.

    
    specialize (e (fun x0 : choice.Choice.sort A * heap =>
     @eqtype.eq_op
       (choice.Choice.eqType
          (ChoiceAsOrd.F_choice_prod_obj
             {| Base.nfst := A; Base.nsnd := heap_choiceType |})) x0 
       (x, y)) (fun x0 : choice.Choice.sort A * heap =>
     @eqtype.eq_op
       (choice.Choice.eqType
          (ChoiceAsOrd.F_choice_prod_obj
             {| Base.nfst := A; Base.nsnd := heap_choiceType |})) x0 
       (x, y))).
    specialize (e (pkg_semantics.repr K₀) (pkg_semantics.repr K₁) H).
    specialize (e s₀ s₁ H0).

    
    enough (forall x y : choice.Choice.sort A * choice.Choice.sort heap_choiceType,
       x = y ->
       is_true
         ((fun _ : choice.Choice.sort A * choice.Choice.sort heap_choiceType => false) x) <->
       is_true
         ((fun _ : choice.Choice.sort A * choice.Choice.sort heap_choiceType => true) y)).
    specialize (e H1). clear H1.
    simpl in e.
    simpl.

    
    
    apply e.
    
    specialize (e s₀ s₁ H0).
    cbn in e.
    
    specialize e with (Ψ := ψ).
    
  eapply coupling_eq. all: eauto.

    pose (@rcoupling_eq A (k is_pure) ((temp ← is_state ;;
                                            k temp)) ).
    
    
    
    apply (r_transL (k is_pure)).

    
    apply (r_transL (k is_pure)).
    2: apply H0.
   clear H0.

    apply (@r_bind A A A A (ret is_pure) (is_state) k k (fun '(s₀, s₁) => s₀ = s₁) (fun '(a, _) '(b, _) => b = a) eq).
    apply rsymmetry.
    apply rsym_pre. intros ; subst ; reflexivity.
    apply code_eq_proof_statement.

    intros.
    apply (rpre_hypothesis_rule).
    intros.
    subst.    
    pose (@rpre_weaken_rule A A (k a₀) (k a₀) (fun '(h₀, h₁) => h₀ = h₁) (fun s : heap * heap => fst s = s₀ /\ snd s = s₁)).
    apply r.
    apply (@rreflexivity_rule A (k a₀)).

    intros.
    destruct H0.
    subst.
    reflexivity.
    
    apply (rpre
    
    pose (@rpost_conclusion_rule).

    
    
    
    (* rewrite bind_rewrite. *)

    (* rewrite !repr_bind. *)
    apply from_sem_jdg. eapply to_sem_jdg in code_eq_proof_statement.
    pose @rbind_rule.
    eapply RulesStateProb.bind_rule_pp.
    
    destruct is_state as [ [] ].
    - pose (@rpost_conclusion_rule A A A (fun '(s₀, s₁) => s₀ = s₁) (ret is_pure) (ret x)).
      apply (rpost_conclusion_rule) in code_eq_proof_statement.
      
      rewrite bind_rewrite.
      
  }
  unfold poly1305_encode_r_state.
  unfold poly1305_encode_r_pure.
  unfold lift_to_code.
  unfold prog.

  unfold array_to_seq.
  unfold array_from_seq.
  unfold uint128_from_le_bytes.
  unfold secret.
  unfold nat_mod_from_secret_literal.

  unfold lift_to_code.
  
  unfold bind.

  step_code.
  reflexivity.
  
  rewrite bind_assoc.
  
  step_code.

  
  replace (fun temp_28 => (temp_29 ← ret nat_mod_zero_pre ;;
            ret (temp_29, temp_28, k_25)))
    with (fun temp_28 => ret (ct_T (nat_mod_zero_pre, temp_28, k_25)) ).
  pose (@bind_rewrite _ _ (@nat_mod_zero_pre 1361129467683753853853498429727072845819)).
  rewrite ( (zmodp.Zp0).
  
  apply rpost_conclusion_rule.
  
  unfold lift_to_code.
  step_code.
    match goal with
    | [ |- context [ ⊢ ⦃ ?P ⦄ (@bind _ _ (_ (_ ?code_fun) ) ?bound_code) ≈ _ ⦃ ?post ⦄ ]] =>
        let H := fresh in
        pose (H := @bind_both) ;
        specialize (H) with (k := bound_code) (Q := post) (code_bind := code_fun)
    end.
    unfold lift_to_code in H.
    unfold prog in H.
    rewrite bind_rewrite in H.
    

    
    unfold nat_mod_zero.
    unfold lift_to_code.

    rel_jdg_replace_sem.
    
    rewrite bind_ret.
    
    rewrite <- bind_assocax.
    rewrite <- bind_assoc.
    rewrite <- bind_assoc.
    
    apply H.
  step_code.
  match goal with
  | [ |- context [ ⊢ ⦃ ?P ⦄ (@bind _ _ (_ (?proj_fun ?code_fun) ) ?k) ≈ _ ⦃ ?Q ⦄ ]] =>
      apply (@bind_both _ _ _ Q (poly1305_encode_r _) k)
  end.

  (* eapply (bind_both). *)
  
  intros.
  step_code.
a
  (* pose (t := poly1305_encode_r_eq). *)
  (* unfold code_eq_proof_statement in t. *)

  remember (Hacspec_Lib_Pre.array_from_slice _ _ _ _ _).
  (* bind_both_function. *)
  step_code.
  step_code.
  intros ; subst.
  reflexivity.
Qed.
  
Import Hacspec_Lib_Pre.
Definition poly1305_update_block_pure
  (b_32 : poly_block_t)
  (st_31 : poly_state_t)
  : poly_state_t :=
  let '(acc_34, r_35, k_36) :=
    st_31 in 
  (((poly1305_encode_block (b_32)) +% (acc_34)) *% (r_35), r_35, k_36).

Import Hacspec_Lib.

Program Definition poly1305_update_block_state
  (b_32 : poly_block_t)
  (st_31 : poly_state_t)
  : code (fset.fset0) [interface] (@ct (poly_state_t)) :=
  (({code let '(acc_34, r_35, k_36) :=
        (st_31) : (field_element_t '× field_element_t '× poly_key_t) in
       temp_33 ←
        (poly1305_encode_block (b_32)) ;;
      @pkg_core_definition.ret ((
          field_element_t '×
          field_element_t '×
          poly_key_t
        )) ( ((((temp_33) +% (acc_34)) *% (r_35), r_35, k_36))) } : code (
        fset.fset0) [interface] _)).
Fail Next Obligation.

Definition poly1305_update_block
  (b_32 : poly_block_t)
  (st_31 : poly_state_t)
  : both (fset.fset0) poly_state_t :=
  {|
  is_pure := poly1305_update_block_pure(b_32 : poly_block_t)
  (st_31 : poly_state_t);
  is_state := poly1305_update_block_state(b_32 : poly_block_t)
  (st_31 : poly_state_t);
  |}.

Theorem poly1305_update_block_eq :
forall (b_32 : poly_block_t)
(st_31 : poly_state_t),
code_eq_proof_statement (poly1305_update_block(b_32 : poly_block_t)
  (st_31 : poly_state_t)).
Proof. Admitted.

Import Hacspec_Lib_Pre.
Definition poly1305_update_blocks_pure
  (m_38 : byte_seq)
  (st_37 : poly_state_t)
  : poly_state_t :=
  let st_45 : (field_element_t '× field_element_t '× poly_key_t) :=
    st_37 in 
  let n_blocks_40 : uint_size :=
    (seq_len (m_38)) ./ (blocksize_v) in 
  let st_45 :=
    foldi (usize 0) (n_blocks_40) (fun i_41 st_45 =>
      let block_44 : poly_block_t :=
        array_from_seq (16) (seq_get_exact_chunk (m_38) (blocksize_v) (
            i_41)) in 
      let st_45 :=
        poly1305_update_block (block_44) (st_45) in 
      (st_45))
    st_45 in 
  st_45.

Import Hacspec_Lib.
Definition st_45_loc : Location :=
  ((field_element_t '× field_element_t '× poly_key_t) : choice_type ; 47%nat).
Program Definition poly1305_update_blocks_state
  (m_38 : byte_seq)
  (st_37 : poly_state_t)
  : code (fset (path.sort leb [ st_45_loc])) [interface] (@ct (poly_state_t)) :=
  (({code #put st_45_loc := 
        (st_37) ;;
      st_45 ← get st_45_loc ;;
      let st_45 : (field_element_t '× field_element_t '× poly_key_t) :=
        (st_45) in
       temp_39 ←
        (seq_len (m_38)) ;;
      let n_blocks_40 : uint_size :=
        ((temp_39) ./ (blocksize_v)) in
       st_45 ←
        (foldi (usize 0) (n_blocks_40) (fun i_41 (st_45 : _) =>
            ({code  temp_42 ←
                (seq_get_exact_chunk (m_38) (blocksize_v) (i_41)) ;;
               temp_43 ←
                (array_from_seq (16) (temp_42)) ;;
              let block_44 : poly_block_t :=
                (temp_43) in
               temp_46 ←
                (poly1305_update_block (block_44) (st_45)) ;;
              st_45 ← get st_45_loc ;;
              
              #put st_45_loc := 
                (temp_46) ;;
              st_45 ← get st_45_loc ;;
              
              @pkg_core_definition.ret (_) ( ((st_45))) } : code (fset (
                  path.sort leb [ st_45_loc])) [interface] _))
          st_45) ;;
      
      @pkg_core_definition.ret ((
          field_element_t '×
          field_element_t '×
          poly_key_t
        )) ( (st_45)) } : code (fset (
          path.sort leb [ st_45_loc])) [interface] _)).
Fail Next Obligation.

Definition poly1305_update_blocks
  (m_38 : byte_seq)
  (st_37 : poly_state_t)
  : both (fset (path.sort leb [ st_45_loc])) poly_state_t :=
  {|
  is_pure := poly1305_update_blocks_pure(m_38 : byte_seq)
  (st_37 : poly_state_t);
  is_state := poly1305_update_blocks_state(m_38 : byte_seq)
  (st_37 : poly_state_t);
  |}.

Theorem poly1305_update_blocks_eq :
forall (m_38 : byte_seq)
(st_37 : poly_state_t),
code_eq_proof_statement (poly1305_update_blocks(m_38 : byte_seq)
  (st_37 : poly_state_t)).
Proof. Admitted.

Import Hacspec_Lib_Pre.
Definition poly1305_update_last_pure
  (pad_len_52 : uint_size)
  (b_50 : sub_block_t)
  (st_48 : poly_state_t)
  : poly_state_t :=
  let st_49 : (field_element_t '× field_element_t '× poly_key_t) :=
    st_48 in 
  let '(st_49) :=
    if (seq_len (b_50)) !=.? (usize 0):bool then (let '(acc_54, r_55, k_56) :=
        st_49 in 
      let st_49 :=
        (
          ((poly1305_encode_last (pad_len_52) (b_50)) +% (acc_54)) *% (r_55),
          r_55,
          k_56
        ) in 
      (st_49)) else ((st_49)) in 
  st_49.

Import Hacspec_Lib.
Definition st_49_loc : Location :=
  ((field_element_t '× field_element_t '× poly_key_t) : choice_type ; 57%nat).
Program Definition poly1305_update_last_state
  (pad_len_52 : uint_size)
  (b_50 : sub_block_t)
  (st_48 : poly_state_t)
  : code (fset (path.sort leb [ st_49_loc])) [interface] (@ct (poly_state_t)) :=
  (({code #put st_49_loc := 
        (st_48) ;;
      st_49 ← get st_49_loc ;;
      let st_49 : (field_element_t '× field_element_t '× poly_key_t) :=
        (st_49) in
       temp_51 ←
        (seq_len (b_50)) ;;
       '(st_49) ←
        (if (temp_51) !=.? (usize 0):bool_ChoiceEquality then (({code let '(
                  acc_54,
                  r_55,
                  k_56
                ) :=
                (st_49) : (field_element_t '× field_element_t '× poly_key_t
              ) in
               temp_53 ←
                (poly1305_encode_last (pad_len_52) (b_50)) ;;
              st_49 ← get st_49_loc ;;
              
              #put st_49_loc := 
                ((((temp_53) +% (acc_54)) *% (r_55), r_55, k_56)) ;;
              st_49 ← get st_49_loc ;;
              
              @pkg_core_definition.ret (_) ( ((st_49))) } : code (fset (
                  path.sort leb [ st_49_loc])) [interface] _)) else (
            @pkg_core_definition.ret (_) ( ((st_49))))) ;;
      
      @pkg_core_definition.ret ((
          field_element_t '×
          field_element_t '×
          poly_key_t
        )) ( (st_49)) } : code (fset (
          path.sort leb [ st_49_loc])) [interface] _)).
Fail Next Obligation.

Definition poly1305_update_last
  (pad_len_52 : uint_size)
  (b_50 : sub_block_t)
  (st_48 : poly_state_t)
  : both (fset (path.sort leb [ st_49_loc])) poly_state_t :=
  {|
  is_pure := poly1305_update_last_pure(pad_len_52 : uint_size)
  (b_50 : sub_block_t)
  (st_48 : poly_state_t);
  is_state := poly1305_update_last_state(pad_len_52 : uint_size)
  (b_50 : sub_block_t)
  (st_48 : poly_state_t);
  |}.

Theorem poly1305_update_last_eq :
forall (pad_len_52 : uint_size)
(b_50 : sub_block_t)
(st_48 : poly_state_t),
code_eq_proof_statement (poly1305_update_last(pad_len_52 : uint_size)
  (b_50 : sub_block_t)
  (st_48 : poly_state_t)).
Proof. Admitted.

Import Hacspec_Lib_Pre.
Definition poly1305_update_pure
  (m_58 : byte_seq)
  (st_59 : poly_state_t)
  : poly_state_t :=
  let st_64 : (field_element_t '× field_element_t '× poly_key_t) :=
    poly1305_update_blocks (m_58) (st_59) in 
  let last_62 : seq uint8 :=
    seq_get_remainder_chunk (m_58) (blocksize_v) in 
  poly1305_update_last (seq_len (last_62)) (last_62) (st_64).

Import Hacspec_Lib.

Program Definition poly1305_update_state
  (m_58 : byte_seq)
  (st_59 : poly_state_t)
  : code (fset (path.sort leb [ st_45_loc ; st_49_loc])) [interface] (@ct (
      poly_state_t)) :=
  (({code  temp_60 ←
        (poly1305_update_blocks (m_58) (st_59)) ;;
      let st_64 : (field_element_t '× field_element_t '× poly_key_t) :=
        (temp_60) in
       temp_61 ←
        (seq_get_remainder_chunk (m_58) (blocksize_v)) ;;
      let last_62 : seq uint8 :=
        (temp_61) in
       temp_63 ←
        (seq_len (last_62)) ;;
       temp_65 ←
        (poly1305_update_last (temp_63) (last_62) (st_64)) ;;
      @pkg_core_definition.ret (poly_state_t) ( (temp_65)) } : code (fset (
          path.sort leb [ st_45_loc ; st_49_loc])) [interface] _)).
Fail Next Obligation.

Definition poly1305_update
  (m_58 : byte_seq)
  (st_59 : poly_state_t)
  : both (fset (path.sort leb [ st_45_loc ; st_49_loc])) poly_state_t :=
  {|
  is_pure := poly1305_update_pure(m_58 : byte_seq)
  (st_59 : poly_state_t);
  is_state := poly1305_update_state(m_58 : byte_seq)
  (st_59 : poly_state_t);
  |}.

Theorem poly1305_update_eq :
forall (m_58 : byte_seq)
(st_59 : poly_state_t),
code_eq_proof_statement (poly1305_update(m_58 : byte_seq)
  (st_59 : poly_state_t)).
Proof. Admitted.

Import Hacspec_Lib_Pre.
Definition poly1305_finish_pure (st_66 : poly_state_t) : poly1305_tag_t :=
  let '(acc_71, _, k_67) :=
    st_66 in 
  let n_77 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default) (16) (
        array_to_seq (k_67)) (usize 16) (usize 16)) in 
  let aby_73 : seq uint8 :=
    nat_mod_to_byte_seq_le (acc_71) in 
  let a_76 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default) (16) (aby_73) (usize 0) (
        usize 16)) in 
  array_from_seq (16) (array_to_seq (uint128_to_le_bytes ((a_76) .+ (n_77)))).

Import Hacspec_Lib.

Program Definition poly1305_finish_state
  (st_66 : poly_state_t)
  : code (fset.fset0) [interface] (@ct (poly1305_tag_t)) :=
  (({code let '(acc_71, _, k_67) :=
        (st_66) : (field_element_t '× field_element_t '× poly_key_t) in
       temp_68 ←
        (array_to_seq (k_67)) ;;
      let temp_68 : seq uint8 :=
        (temp_68) in
       temp_69 ←
        (array_from_slice (default) (16) (temp_68) (usize 16) (usize 16)) ;;
       temp_70 ←
        (uint128_from_le_bytes (temp_69)) ;;
      let n_77 : uint128 :=
        (temp_70) in
       temp_72 ←
        (nat_mod_to_byte_seq_le (acc_71)) ;;
      let aby_73 : seq uint8 :=
        (temp_72) in
       temp_74 ←
        (array_from_slice (default) (16) (aby_73) (usize 0) (usize 16)) ;;
       temp_75 ←
        (uint128_from_le_bytes (temp_74)) ;;
      let a_76 : uint128 :=
        (temp_75) in
       temp_78 ←
        (uint128_to_le_bytes ((a_76) .+ (n_77))) ;;
       temp_79 ←
        (array_to_seq (temp_78)) ;;
      let temp_79 : seq uint8 :=
        (temp_79) in
       temp_80 ←
        (array_from_seq (16) (temp_79)) ;;
      @pkg_core_definition.ret (poly1305_tag_t) ( (temp_80)) } : code (
        fset.fset0) [interface] _)).
Fail Next Obligation.

Definition poly1305_finish
  (st_66 : poly_state_t)
  : both (fset.fset0) poly1305_tag_t :=
  {|
  is_pure := poly1305_finish_pure(st_66 : poly_state_t);
  is_state := poly1305_finish_state(st_66 : poly_state_t);
  |}.

Theorem poly1305_finish_eq :
forall (st_66 : poly_state_t),
code_eq_proof_statement (poly1305_finish(st_66 : poly_state_t)).
Proof. Admitted.

Import Hacspec_Lib_Pre.
Definition poly1305_pure
  (m_83 : byte_seq)
  (key_81 : poly_key_t)
  : poly1305_tag_t :=
  let st_84 : (field_element_t '× field_element_t '× poly_key_t) :=
    poly1305_init (key_81) in 
  let st_84 :=
    poly1305_update (m_83) (st_84) in 
  poly1305_finish (st_84).

Import Hacspec_Lib.
Definition st_84_loc : Location :=
  ((field_element_t '× field_element_t '× poly_key_t) : choice_type ; 87%nat).
Program Definition poly1305_state
  (m_83 : byte_seq)
  (key_81 : poly_key_t)
  : code (fset (
      path.sort leb [ n_4_loc ; st_49_loc ; st_45_loc ; st_84_loc])) [interface] (
    @ct (poly1305_tag_t)) :=
  (({code  temp_82 ←
        (poly1305_init (key_81)) ;;
      #put st_84_loc := 
        (temp_82) ;;
      st_84 ← get st_84_loc ;;
      let st_84 : (field_element_t '× field_element_t '× poly_key_t) :=
        (st_84) in
       temp_85 ←
        (poly1305_update (m_83) (st_84)) ;;
      st_84 ← get st_84_loc ;;
      
      #put st_84_loc := 
        (temp_85) ;;
      st_84 ← get st_84_loc ;;
      
       temp_86 ←
        (poly1305_finish (st_84)) ;;
      @pkg_core_definition.ret (poly1305_tag_t) ( (temp_86)) } : code (fset (
          path.sort leb [ n_4_loc ; st_49_loc ; st_45_loc ; st_84_loc])) [interface] _)).
Fail Next Obligation.

Definition poly1305
  (m_83 : byte_seq)
  (key_81 : poly_key_t)
  : both (fset (
      path.sort leb [ n_4_loc ; st_49_loc ; st_45_loc ; st_84_loc])) poly1305_tag_t :=
  {|
  is_pure := poly1305_pure(m_83 : byte_seq)
  (key_81 : poly_key_t);
  is_state := poly1305_state(m_83 : byte_seq)
  (key_81 : poly_key_t);
  |}.

Theorem poly1305_eq :
forall (m_83 : byte_seq)
(key_81 : poly_key_t),
code_eq_proof_statement (poly1305(m_83 : byte_seq) (key_81 : poly_key_t)).
Proof. Admitted.

