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

From Equations Require Import Equations.

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

Definition n_4_loc : Location :=
  (uint128 : choice_type ; 7%nat).
Program Definition poly1305_encode_r
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

Import Hacspec_Lib_Pre.
Definition poly1305_encode_r_pure (b_0 : poly_block_t) : field_element_t :=
  let n_1 : uint128 :=
    uint128_from_le_bytes (array_from_seq (16) (array_to_seq (b_0))) in 
  let n_1 :=
    (n_1) .& (secret (
        @repr U128 21267647620597763993911028882763415551) : int128) in 
  nat_mod_from_secret_literal (n_1).
Definition poly1305_encode_r_code
           (b_0 : poly_block_t)
  : code fset.fset0 [interface] (@ct field_element_t) :=
  lift_to_code (poly1305_encode_r_pure b_0).

Ltac unfold_T_ct :=
  unfold T_ct , eq_rect_r , eq_rect , ChoiceEq ;
  repeat
    (unfold int128
     || unfold uint8, int8
     || unfold nat_mod
     || unfold nseq, Hacspec_Lib_Pre.nseq_obligation_1 , eq_ind , ChoiceEq
     || unfold seq, Hacspec_Lib_Pre.seq_obligation_1, eq_ind, ChoiceEq
     || unfold int, Hacspec_Lib_Pre.int_obligation_1) ;
  unfold eq_sym.

Hint Unfold poly1305_encode_r : Hacspec_hint.
Hint Transparent poly1305_encode_r.
Transparent poly1305_encode_r.
Import Hacspec_Lib.
Theorem encode_equality :
  forall b , ⊢ ⦃ (fun '(h₀, h₁) => h₀ = h₁) ⦄  poly1305_encode_r b ≈ poly1305_encode_r_code b ⦃ fun '(a, _) '(b, _) => a = b ⦄.
  Set Printing Coercions.
  intros.

  unfold poly1305_encode_r.
  unfold poly1305_encode_r_code.
  unfold poly1305_encode_r_pure.
  unfold lift_to_code.
  unfold prog.

  unfold array_to_seq.
  unfold lift_to_code.

  unfold array_from_seq.
  unfold lift_to_code.

  unfold uint128_from_le_bytes.
  unfold lift_to_code.
  
  unfold secret.
  unfold lift_to_code.
  
  unfold nat_mod_from_secret_literal.
  unfold lift_to_code.

  step_code.
  
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

Theorem encode_equality :
  forall b n, 
    Run sampler (poly1305_encode_r_code b true) n =
    Run sampler (poly1305_encode_r b) n.
Proof.
  Set Printing Coercions.
  intros.
  
  assert (forall (A B : ChoiceEquality) x f, @bind A B (ret x) f = f x) by reflexivity.

  
  unfold poly1305_encode_r_code.
  unfold poly1305_encode_r.
  unfold poly1305_encode_r_pure.

  unfold Run.
  unfold lift_to_code.
  unfold prog.

  unfold Run_aux at 1.
  
  assert (forall (A B : ChoiceEquality) x f, @bind A B (ret x) f = f x) by reflexivity.
  unfold array_to_seq.
  unfold lift_to_code.
  rewrite H.

  unfold array_from_seq.
  unfold lift_to_code.
  rewrite H.    

  unfold uint128_from_le_bytes.
  unfold lift_to_code.
  rewrite H.
  
  unfold Run_aux ; fold (@Run_aux sampler).

  unfold new_state.
  rewrite eqtype.eq_refl.

  unfold_T_ct.
  unfold field_element_t.
  unfold_T_ct.
    
  ch_nat_compute.
  2: {
    destruct (Hacspec_Lib_Pre.uint128_from_le_bytes _) in H1.
    cbn in H1.
    simp ch_nat in H1.
    discriminate.
  }.  
  rewrite H0.
  
  unfold secret.
  unfold lift_to_code.
  rewrite H.

  unfold Run_aux ; fold (@Run_aux sampler).

  rewrite eqtype.eq_refl.
  rewrite H0.

  unfold new_state.
  rewrite eqtype.eq_refl.

  unfold_T_ct.

  ch_nat_compute.
  2: {
    destruct (_ .& _) in H2.
    cbn in H2.
    simp ch_nat in H2.
    discriminate.    
  }
  rewrite H1.
  
  unfold nat_mod_from_secret_literal.
  unfold lift_to_code.
  
  rewrite bind_ret with (v := ret _). 
  unfold Run_aux ; fold (@Run_aux sampler).

  unfold_T_ct.

  reflexivity.
Qed.  
  
  
    
  

Theorem encode_equality :
  forall b , prog (poly1305_encode_r_code b) = prog (poly1305_encode_r b).
Proof.  
  Set Printing Coercions.
  intros.
  unfold poly1305_encode_r_code.

  assert (forall A x, @prog _ _ _ (@lift_to_code A
                        fset.fset0
                        [interface] x) = ret (T_ct x)) by reflexivity.
  
  unfold poly1305_encode_r_code.
  unfold poly1305_encode_r.
  unfold poly1305_encode_r_pure.

  
  unfold lift_to_code.
  unfold prog.
    
  assert (forall (A B : ChoiceEquality) x f, @bind A B (ret x) f = f x) by reflexivity.

  rewrite <- (@bind_ret _ (ret (T_ct _))).

  Check bind_morphism _ _ _.
  rewrite bind_morphism.
  
  assert (bind_def : forall (A B : ChoiceEquality) (f : A -> B) (x : A) t,
             (@bind B B (ret (T_ct (f x))) (@ret B))
             =
               (@bind A B (ret x) (fun v => @bind B B (ret (T_ct (f v))) (@ret B)))).
  
  
  
  rewrite bind_assoc.
  
  assert (bind_def : forall (A B : ChoiceEquality) (f : A -> B) (x : A) t,
             (@bind _ _ (ret (T_ct (f x))) t)
             =
               (@bind A B (ret (T_ct x)) (fun v => @bind _ _ (ret (T_ct (f (ct_T v)))) t))).
  {
    clear ; intros.
    cbn.
    rewrite ct_T_id.
    reflexivity.
    Show Proof.
  }
  rewrite bind_def.



  fold (@nat_mod_from_secret_literal 1361129467683753853853498429727072845819).
  fold (nat_mod_from_secret_literal).

  
  assert (bind_def2 : forall (A C B : ChoiceEquality) (f : A -> C -> B) (x : A) (y : C) t,
             (@bind _ _ (ret (T_ct (f x y))) t)
             =
               (@bind A B (ret (T_ct x)) (fun v =>
               (@bind C B (ret (T_ct y)) (fun u =>
                  @bind _ _ (ret (T_ct (f (ct_T v) (ct_T u)))) t))))).
  {
    clear ; intros.
    cbn.
    rewrite ct_T_id.
    rewrite ct_T_id.
    reflexivity.
  }

  rewrite bind_def2.
  
  
  specialize (bind_def).
  
  
    with (f := (fun x => T_ct (Hacspec_Lib_Pre.nat_mod_from_secret_literal x))).
  
  specialize bind_def with (f := @Hacspec_Lib_Pre.nat_mod_from_secret_literal 0x03fffffffffffffffffffffffffffffffb) (g := Hacspec_Lib_Pre.uint128_from_le_bytes) (x := (Hacspec_Lib_Pre.array_from_seq 16 (Hacspec_Lib_Pre.array_to_seq b))
          .& Hacspec_Lib_Pre.secret (repr 21267647620597763993911028882763415551)).
  
  rewrite bind_def.
  
  
  rewrite -> bind_assoc.
  
  rewrite <- H0.
  
  assert (forall (A B : ChoiceEquality) x f,
             ret (T_ct (f x)) =
             @bind A B (ret (T_ct (f x))) (fun y => ret (T_ct _))) by reflexivity.
  rewrite <- H0.

  
  rewrite <- H.

  replace (ret
         (T_ct
            (Hacspec_Lib_Pre.nat_mod_from_secret_literal
               (Hacspec_Lib_Pre.uint128_from_le_bytes
                  (Hacspec_Lib_Pre.array_from_seq 16 (Hacspec_Lib_Pre.array_to_seq b))
                  .& Hacspec_Lib_Pre.secret (repr 21267647620597763993911028882763415551))))).
  replace (ret
         (T_ct
            (Hacspec_Lib_Pre.nat_mod_from_secret_literal
               (Hacspec_Lib_Pre.uint128_from_le_bytes
                  (Hacspec_Lib_Pre.array_from_seq 16 (Hacspec_Lib_Pre.array_to_seq b))
                .& Hacspec_Lib_Pre.secret (repr 21267647620597763993911028882763415551)))))
  
  rewrite bind_assoc.
  
  unfold array_to_seq.
  unfold lift_to_code.
  rewrite H.

  unfold array_from_seq.
  unfold lift_to_code.
  rewrite H.    

  unfold uint128_from_le_bytes.
  unfold lift_to_code.
  rewrite H.
  
  rewrite put_get_id_none.

  unfold secret ; unfold lift_to_code ; rewrite H.
  
  replace (
      n_4 ← get n_4_loc ;;
      #put n_4_loc := n_4 .& T_ct (secret_pure (repr 21267647620597763993911028882763415551)) ;;
                      n_0 ← get n_4_loc ;;
                      temp_6 ← prog (@nat_mod_from_secret_literal 0x03fffffffffffffffffffffffffffffffb n_0) ;;
                      ret temp_6)
    with
    (n_4 ← get n_4_loc ;;
   temp_6 ← prog (@nat_mod_from_secret_literal 0x03fffffffffffffffffffffffffffffffb (n_4 .& T_ct (secret_pure (repr 21267647620597763993911028882763415551)))) ;;
   ret temp_6).
  2: {
    f_equal.
    apply functional_extensionality.
  
  
  
  

  unfold uint128_from_le_bytes.
  unfold lift_to_code.
  rewrite H.
  
  assert (forall B l x f, (#put l := x ;; n ← get l ;; f n) = (@bind (loc_type l) B (ret x) f)).
  clear ; intros.
  cbn.
  
  
  
  pose (fun v => r_put_get uint8 n_4_loc v).
  assert putr
  
  Check putr.
  Locate " #put _ := _ ;; _".
  
  unfold uint128_from_le_bytes.
  unfold lift_to_code.
  rewrite H.
  
  rewrite <- bind_assoc.  

  
  rewrite H.
  
  unfold bind in r.
  
  
  assert (forall x f, bind x f = f (T_ct x)).
  

  unfold prog.
  unfold array_to_seq.
  unfold lift_to_code.

  unfold array_from_seq.
  unfold lift_to_code.

  

  rewrite <- bind_assoc.  
  rewrite <- bind_assoc.

  
  
  erewrite (@bind_cong _ _ (ret (T_ct (Hacspec_Lib_Pre.array_to_seq b : seq uint8))) _
                       (fun x => ret (T_ct (Hacspec_Lib_Pre.array_from_seq 16 (x : seq_type uint8) : nseq uint8 16)))).
  2: {
    Set Printing All.
  }.
  
  assert (forall (A B C : ChoiceEquality) (f : @T A -> @T C) (g : @T C -> @T B) y,

             

             
             (@bind (@ct C) (@ct B) (ret (T_ct (f y))) (fun x => ret (T_ct (g (ct_T x))))) =
               (@bind (@ct A) (@ct B) (ret y) (fun x => g (f x)))) by reflexivity.
  
  rewrite <- bind_assoc.
  rewrite (H _ _ _ T_ct).
  
  
  pose (@bind_cong _ _ (ret (T_ct (Hacspec_Lib_Pre.array_to_seq b : seq uint8))) (ret (T_ct (Hacspec_Lib_Pre.array_to_seq b : seq uint8)))
                   (fun x => ret (T_ct (Hacspec_Lib_Pre.array_from_seq 16 (x : seq_type uint8) : nseq uint8 16)))).
  erewrite e.

  
  intros.
  
  rewrite @bind_cong with (v := x) (g := @ret (@ct acc)).
  rewrite bind_ret.
  reflexivity.
  reflexivity.
  
  apply functional_extensionality.
  intros.
  
  rewrite T_ct_id.
  reflexivity.  

  
  Locate raw_code_type_from_choice_type_id.
  rewrite raw_code_type_from_choice_type_id.
  rewrite bind_ret.
  
  
  unfold array_from_seq.
  unfold lift_to_code.

  
  rewrite <- bind_assoc.

  
  assert (x ← prog y ;; prog (g x) = prog (g y)).
  
  rewrite <- bind_assoc.
  rewrite bind_assoc.

  unfold array_to_seq.
  unfold lift_to_code.

  (* unfold bind. *)

  unfold bind.
  
  replace (x ← ret (T_ct (Hacspec_Lib_Pre.array_to_seq b)) ;;
             prog (array_from_seq 16 x)) with (prog (array_from_seq 16 (T_ct (Hacspec_Lib_Pre.array_to_seq b)))).
  
  (* assert ((x ← ret (T_ct (Hacspec_Lib_Pre.array_to_seq b : seq uint8)) ;; *)
  (*          prog (array_from_seq 16 x)) = *)
  (*   (prog (array_from_seq 16 (Hacspec_Lib_Pre.array_to_seq b)))). *)
  
  rewrite bind_ret.  
  
  replace ((x ← prog (array_to_seq b) ;;
            prog (array_from_seq 16 x))) with
    
  
  rewrite <- bind_assoc.

  replace ((x ← prog (array_to_seq b) ;;
             prog (array_from_seq 16 x))) with (array_to_seq b).
  
  unfold bind at 0.
  
  replace (prog (array_to_seq b)) with

  unfold prog.
  
  
  (* replace (ret *)
  (*   (T_ct *)
  (*      (Hacspec_Lib_Pre.nat_mod_from_secret_literal *)
  (*         (Hacspec_Lib_Pre.uint128_from_le_bytes *)
  (*            (Hacspec_Lib_Pre.array_from_seq 16 (Hacspec_Lib_Pre.array_to_seq b)) *)
  (*          .& Hacspec_Lib_Pre.secret (repr 21267647620597763993911028882763415551))))) with *)
  (* ((fun a => ret *)
  (*   (T_ct *)
  (*      (Hacspec_Lib_Pre.nat_mod_from_secret_literal *)
  (*         (Hacspec_Lib_Pre.uint128_from_le_bytes *)
  (*            (Hacspec_Lib_Pre.array_from_seq 16 a) *)
  (*          .& Hacspec_Lib_Pre.secret (repr 21267647620597763993911028882763415551))))) (Hacspec_Lib_Pre.array_to_seq b)). *)

  assert (forall f, @bind _ (nseq _ 16) (array_to_seq b) f = f (Hacspec_Lib_Pre.array_to_seq b)).
  intros.
  cbn.
  reflexivity.
  
  cbn.
  unfold poly1305_encode_r_pure.
  rewrite bind_ret.

Program Definition poly1305_encode_block
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


Program Definition poly1305_encode_last
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


Program Definition poly1305_init
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


Program Definition poly1305_update_block
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

Definition st_45_loc : Location :=
  ((field_element_t '× field_element_t '× poly_key_t) : choice_type ; 47%nat).
Program Definition poly1305_update_blocks
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

Definition st_49_loc : Location :=
  ((field_element_t '× field_element_t '× poly_key_t) : choice_type ; 57%nat).
Program Definition poly1305_update_last
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


Program Definition poly1305_update
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


Program Definition poly1305_finish
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

Definition st_84_loc : Location :=
  ((field_element_t '× field_element_t '× poly_key_t) : choice_type ; 87%nat).
Program Definition poly1305
  (m_83 : byte_seq)
  (key_81 : poly_key_t)
  : code (fset (
      path.sort leb [ st_45_loc ; st_49_loc ; n_4_loc ; st_84_loc])) [interface] (
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
          path.sort leb [ st_45_loc ; st_49_loc ; n_4_loc ; st_84_loc])) [interface] _)).
Fail Next Obligation.

