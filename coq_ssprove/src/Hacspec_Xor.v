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

Definition xor_pure (x_0 : int64) (y_1 : int64) : int64 :=
  let r_2 : int64 :=
    x_0 in 
  let r_2 :=
    (r_2) .^ (y_1) in 
  r_2.
Definition xor_code
  (x_0 : int64)
  (y_1 : int64)
  : code fset.fset0 [interface] (@ct int64) :=
  {code pkg_core_definition.ret (T_ct (xor_pure x_0 y_1))}.


Definition r_1_loc : Location :=
  (int64 : choice_type ; 3%nat).
Program Definition xor
  (x_0 : int64)
  (y_2 : int64)
  : code (fset (path.sort leb [ r_1_loc])) [interface] (@ct (int64)) :=
  (({code #put r_1_loc := 
        (x_0) ;;
      r_1 ← get r_1_loc ;;
      (* let r_1 : int64 := *)
      (*   (r_1) in *)
      (* r_1 ← get r_1_loc ;; *)
      
      #put r_1_loc := 
        ((r_1) .^ (y_2)) ;;
      r_1 ← get r_1_loc ;;
      
      @pkg_core_definition.ret (int64) ( (r_1)) } : code (fset (
          path.sort leb [ r_1_loc])) [interface] _)).
Fail Next Obligation.

From Equations Require Import Equations. (* FunctionalExtensionality *)

Theorem encode_equality :
  forall (x y : (S nat63).-word) , ⊢ ⦃ (fun '(h₀, h₁) => h₀ = h₁) ⦄  xor x y ≈ xor_code x y ⦃ fun '(a, _) '(b, _) => a = b ⦄.
Proof.

  
  
  Set Printing Coercion.
  Set Printing Implicit.

  Locate " ⊢ ⦃ _ ⦄  _ ≈ _ ⦃ _ ⦄ ".
  Check rel_jdg.
  intros.
  cbn.
  
  repeat match goal with
  | [ |- context [ ⊢ ⦃ _ ⦄ (#put ?l := ?x ;; (getr ?l ?a)) ≈ _ ⦃ _ ⦄ ]] =>
      apply (r_transL (#put l := x ;; a x )) ;
      [ apply (r_put_get _ l x (fun _ => _)) | ]
  end
  ||
  match goal with
  | [ |- context [ ⊢ ⦃ _ ⦄ (#put ?l := ?x ;; (putr ?l ?y ?a)) ≈ _ ⦃ _ ⦄ ]] =>
      apply (r_transL (#put l := y ;; a )) ;
      [ apply contract_put | ]
  end.
  
  match goal with
  | [ |- context [ ⊢ ⦃ _ ⦄ (#put ?l := ?x ;; (getr ?l ?a)) ≈ _ ⦃ _ ⦄ ]] =>
      apply (r_transL (#put l := x ;; a x )) ;
      [ apply (r_put_get _ l x (fun _ => _)) | ]
  end.

  apply (r_put_lhs r_1_loc (@mkWord (S nat63) (Z.lxor x y) (@wxor_subproof (S nat63) x y)) (ret _) (ret _) (fun '(h₀, h₁) => h₀ = h₁)).
  apply r_ret.

  intros.
  reflexivity.
Qed.

Ltac ch_nat_compute :=
  let k := fresh in
  let e := fresh in
  match goal with
  | [ |- context[match nat_ch (ch_nat ?l ?v) _ with | Some _ => _ | None => None end] ] =>
      pose (ch_nat_ch l v) as k ;
      generalize dependent k ;
      destruct (ch_nat l v) eqn:e ; [clear e ; intros k | exfalso .. ]
  end.

From Equations Require Import Equations.
Theorem interpret_equality :
  forall x y seed , Run sampler (xor_code x y) seed = Run sampler (xor x y) seed.
Proof.
  Set Printing Coercions.
  
  intros.
    
  unfold xor_code.
  unfold xor.
  
  unfold prog.

  unfold Run.

  assert (forall (A B : ChoiceEquality) x f, @bind A B (ret x) f = f x) by reflexivity.
  
  unfold Run_aux ; fold (@Run_aux sampler).

  unfold new_state.
  rewrite eqtype.eq_refl.
  
  ch_nat_compute.
  2: { cbn in H1. simp ch_nat in H1. discriminate. }
  rewrite H0.

  ch_nat_compute.
  2: { cbn in H2. simp ch_nat in H2. discriminate. }
  rewrite H1.

  reflexivity.
Qed.
  
