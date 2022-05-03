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



Definition poly_key_t := nseq (uint8) (usize 32).

Definition blocksize_v : uint_size :=
  usize 16.

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
Definition poly1305_encode_r_pure (b_2 : poly_block_t) : field_element_t :=
  let n_0 : uint128 :=
    uint128_from_le_bytes (array_from_seq (16) (array_to_seq (b_2))) in 
  let n_0 :=
    (n_0) .& (secret (
        @repr U128 21267647620597763993911028882763415551) : int128) in 
  nat_mod_from_secret_literal (n_0).
Definition poly1305_encode_r_pure_code
  (b_2 : poly_block_t)
  : code fset.fset0 [interface] (@ct field_element_t) :=
  {code pkg_core_definition.ret (T_ct (poly1305_encode_r_pure b_2))}.

Import Hacspec_Lib.
Definition n_0_loc : Location :=
  (uint128 : choice_type ; 8%nat).
Program Definition poly1305_encode_r_state
  (b_2 : poly_block_t)
  : code (fset (path.sort leb [ n_0_loc])) [interface] (@ct (
      field_element_t)) :=
  (({code  temp_3 ←
        (array_to_seq (b_2)) ;;
      let temp_3 : seq uint8 :=
        (temp_3) in
       temp_4 ←
        (array_from_seq (16) (temp_3)) ;;
       temp_5 ←
        (uint128_from_le_bytes (temp_4)) ;;
      #put n_0_loc := 
        (temp_5) ;;
      n_0 ← get n_0_loc ;;
      let n_0 : uint128 :=
        (n_0) in
       temp_6 ←
        (secret (@repr U128 21267647620597763993911028882763415551)) ;;
      let temp_6 : int128 :=
        (temp_6) in
      n_0 ← get n_0_loc ;;
      
      #put n_0_loc := 
        ((n_0) .& (temp_6)) ;;
      n_0 ← get n_0_loc ;;
      
       temp_7 ←
        (nat_mod_from_secret_literal (n_0)) ;;
      @pkg_core_definition.ret (field_element_t) ( (temp_7)) } : code (fset (
          path.sort leb [ n_0_loc])) [interface] _)).
Fail Next Obligation.

Program Definition poly1305_encode_r
  (b_2 : poly_block_t)
  : both (fset (path.sort leb [ n_0_loc])) field_element_t :=
  {|
  is_pure := poly1305_encode_r_pure(b_2 : poly_block_t);
  is_state := poly1305_encode_r_state(b_2 : poly_block_t);
  |}.
Next Obligation.
  unfold poly1305_encode_r_pure.
  unfold poly1305_encode_r_state.
  unfold is_pure.
  unfold is_state.

  unfold prog.

  unfold array_to_seq.
  unfold array_from_seq.
  unfold uint128_from_le_bytes.
  unfold secret.
  unfold nat_mod_from_secret_literal.

  unfold lift_to_code.

  step_code.
  intros.

  split ; [reflexivity | ].
  destruct H.
  decompose [and or] H ; clear H ; subst.
  
  heap_ignore_remove_ignore.
Qed.

Import Hacspec_Lib_Pre.
Definition poly1305_encode_block_pure (b_9 : poly_block_t) : field_element_t :=
  let n_10 : uint128 :=
    uint128_from_le_bytes (array_from_seq (16) (array_to_seq (b_9))) in 
  let f_11 : field_element_t :=
    nat_mod_from_secret_literal (n_10) in 
  (f_11) +% (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (
      usize 128) : field_element_t).
Definition poly1305_encode_block_pure_code
  (b_9 : poly_block_t)
  : code fset.fset0 [interface] (@ct field_element_t) :=
  {code pkg_core_definition.ret (T_ct (poly1305_encode_block_pure b_9))}.

Import Hacspec_Lib.

Program Definition poly1305_encode_block_state
  (b_9 : poly_block_t)
  : code (fset.fset0) [interface] (@ct (field_element_t)) :=
  (({code  temp_12 ←
        (array_to_seq (b_9)) ;;
      let temp_12 : seq uint8 :=
        (temp_12) in
       temp_13 ←
        (array_from_seq (16) (temp_12)) ;;
       temp_14 ←
        (uint128_from_le_bytes (temp_13)) ;;
      let n_10 : uint128 :=
        (temp_14) in
       temp_15 ←
        (nat_mod_from_secret_literal (n_10)) ;;
      let f_11 : field_element_t :=
        (temp_15) in
       temp_16 ←
        (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (usize 128)) ;;
      let temp_16 : field_element_t :=
        (temp_16) in
      @pkg_core_definition.ret (field_element_t) ( ((f_11) +% (
          temp_16))) } : code (fset.fset0) [interface] _)).
Fail Next Obligation.

Program Definition poly1305_encode_block
  (b_9 : poly_block_t)
  : both (fset.fset0) field_element_t :=
  {|
  is_pure := poly1305_encode_block_pure(b_9 : poly_block_t);
  is_state := poly1305_encode_block_state(b_9 : poly_block_t);
  |}.
Next Obligation.
  unfold poly1305_encode_block_pure.
  unfold poly1305_encode_block_state.

  unfold prog.

  unfold array_to_seq.
  unfold array_from_seq.
  unfold uint128_from_le_bytes.
  unfold nat_mod_from_secret_literal.
  unfold nat_mod_pow2.

  unfold lift_to_code.

  step_code.
  split ; easy.
Qed.

Import Hacspec_Lib_Pre.
Definition poly1305_encode_last_pure
  (pad_len_17 : block_index_t)
  (b_18 : sub_block_t)
  : field_element_t :=
  let n_19 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default) (16) (b_18) (usize 0) (
        seq_len (b_18))) in 
  let f_20 : field_element_t :=
    nat_mod_from_secret_literal (n_19) in 
  (f_20) +% (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) ((usize 8) .* (
        pad_len_17)) : field_element_t).
Definition poly1305_encode_last_pure_code
  (pad_len_17 : block_index_t)
  (b_18 : sub_block_t)
  : code fset.fset0 [interface] (@ct field_element_t) :=
  {code pkg_core_definition.ret (T_ct (poly1305_encode_last_pure pad_len_17
    b_18))}.

Import Hacspec_Lib.

Program Definition poly1305_encode_last_state
  (pad_len_17 : block_index_t)
  (b_18 : sub_block_t)
  : code (fset.fset0) [interface] (@ct (field_element_t)) :=
  (({code  temp_21 ←
        (seq_len (b_18)) ;;
       temp_22 ←
        (array_from_slice (default) (16) (b_18) (usize 0) (temp_21)) ;;
       temp_23 ←
        (uint128_from_le_bytes (temp_22)) ;;
      let n_19 : uint128 :=
        (temp_23) in
       temp_24 ←
        (nat_mod_from_secret_literal (n_19)) ;;
      let f_20 : field_element_t :=
        (temp_24) in
       temp_25 ←
        (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) ((usize 8) .* (
              pad_len_17))) ;;
      let temp_25 : field_element_t :=
        (temp_25) in
      @pkg_core_definition.ret (field_element_t) ( ((f_20) +% (
          temp_25))) } : code (fset.fset0) [interface] _)).
Fail Next Obligation.

Program Definition poly1305_encode_last
  (pad_len_17 : block_index_t)
  (b_18 : sub_block_t)
  : both (fset.fset0) field_element_t :=
  {|
  is_pure := poly1305_encode_last_pure(pad_len_17 : block_index_t)
  (b_18 : sub_block_t);
  is_state := poly1305_encode_last_state(pad_len_17 : block_index_t)
  (b_18 : sub_block_t);
  |}.
Next Obligation.
  unfold poly1305_encode_last_pure.
  unfold poly1305_encode_last_state.

  unfold prog.

  unfold seq_len.
  unfold array_from_slice.
  unfold uint128_from_le_bytes.
  unfold nat_mod_from_secret_literal.
  unfold nat_mod_pow2.

  unfold lift_to_code.

  step_code.
  split ; easy.
Qed.

Import Hacspec_Lib_Pre.
Definition poly1305_init_pure (k_26 : poly_key_t) : poly_state_t :=
  let r_27 : field_element_t :=
    poly1305_encode_r (array_from_slice (default) (16) (array_to_seq (k_26)) (
        usize 0) (usize 16)) in 
  (nat_mod_zero , r_27, k_26).
Definition poly1305_init_pure_code
  (k_26 : poly_key_t)
  : code fset.fset0 [interface] (@ct poly_state_t) :=
  {code pkg_core_definition.ret (T_ct (poly1305_init_pure k_26))}.

Import Hacspec_Lib.

Program Definition poly1305_init_state
  (k_26 : poly_key_t)
  : code (fset (path.sort leb [ n_0_loc])) [interface] (@ct (poly_state_t)) :=
  (({code  temp_28 ←
        (array_to_seq (k_26)) ;;
      let temp_28 : seq uint8 :=
        (temp_28) in
       temp_29 ←
        (array_from_slice (default) (16) (temp_28) (usize 0) (usize 16)) ;;
       temp_30 ←
        (poly1305_encode_r (temp_29)) ;;
      let r_27 : field_element_t :=
        (temp_30) in
       temp_31 ←
        (nat_mod_zero ) ;;
      @pkg_core_definition.ret ((
          field_element_t '×
          field_element_t '×
          poly_key_t
        )) ( ((temp_31, r_27, k_26))) } : code (fset (
          path.sort leb [ n_0_loc])) [interface] _)).
Fail Next Obligation.

Program Definition poly1305_init
  (k_26 : poly_key_t)
  : both (fset (path.sort leb [ n_0_loc])) poly_state_t :=
  {|
  is_pure := poly1305_init_pure(k_26 : poly_key_t);
  is_state := poly1305_init_state(k_26 : poly_key_t);
  |}.
Next Obligation.
  unfold poly1305_init_pure.
  unfold poly1305_init_state.

  unfold prog.

  unfold array_to_seq.
  unfold array_from_slice.
  unfold nat_mod_zero.

  unfold lift_to_code.

  step_code.
  both_bind.
    
  apply r_ret.
  intros ; subst.
  reflexivity.

  intros.
  step_code.
  intros ? ? [] ; subst.
  split ; easy.
Qed.

Import Hacspec_Lib_Pre.
Definition poly1305_update_block_pure
  (b_32 : poly_block_t)
  (st_33 : poly_state_t)
  : poly_state_t :=
  let '(acc_34, r_35, k_36) :=
    st_33 in 
  (((poly1305_encode_block (b_32)) +% (acc_34)) *% (r_35), r_35, k_36).
Definition poly1305_update_block_pure_code
  (b_32 : poly_block_t)
  (st_33 : poly_state_t)
  : code fset.fset0 [interface] (@ct poly_state_t) :=
  {code pkg_core_definition.ret (T_ct (poly1305_update_block_pure b_32 st_33))}.

Import Hacspec_Lib.

Program Definition poly1305_update_block_state
  (b_32 : poly_block_t)
  (st_33 : poly_state_t)
  : code (fset.fset0) [interface] (@ct (poly_state_t)) :=
  (({code let '(acc_34, r_35, k_36) :=
        (st_33) : (field_element_t '× field_element_t '× poly_key_t) in
       temp_37 ←
        (poly1305_encode_block (b_32)) ;;
      @pkg_core_definition.ret ((
          field_element_t '×
          field_element_t '×
          poly_key_t
        )) ( ((((temp_37) +% (acc_34)) *% (r_35), r_35, k_36))) } : code (
        fset.fset0) [interface] _)).
Fail Next Obligation.

Program Definition poly1305_update_block
  (b_32 : poly_block_t)
  (st_33 : poly_state_t)
  : both (fset.fset0) poly_state_t :=
  {|
  is_pure := poly1305_update_block_pure(b_32 : poly_block_t)
  (st_33 : poly_state_t);
  is_state := poly1305_update_block_state(b_32 : poly_block_t)
  (st_33 : poly_state_t);
  |}.
Next Obligation.
unfold poly1305_update_block_pure.
unfold poly1305_update_block_state.
unfold is_pure.
unfold is_state.

unfold prog.

both_bind.

step_code.
intros ; subst.
reflexivity.

intros.
step_code.
intros ? ? [] ; subst.
split ; easy.
Qed.

Import Hacspec_Lib_Pre.
Definition poly1305_update_blocks_pure
  (m_40 : byte_seq)
  (st_41 : poly_state_t)
  : poly_state_t :=
  let st_38 : (field_element_t '× field_element_t '× poly_key_t) :=
    st_41 in 
  let n_blocks_42 : uint_size :=
    (seq_len (m_40)) ./ (blocksize_v) in 
  let st_38 :=
    foldi (usize 0) (n_blocks_42) (fun i_43 st_38 =>
      let block_44 : poly_block_t :=
        array_from_seq (16) (seq_get_exact_chunk (m_40) (blocksize_v) (
            i_43)) in 
      let st_38 :=
        poly1305_update_block (block_44) (st_38) in 
      (st_38))
    st_38 in 
  st_38.
Definition poly1305_update_blocks_pure_code
  (m_40 : byte_seq)
  (st_41 : poly_state_t)
  : code fset.fset0 [interface] (@ct poly_state_t) :=
  {code pkg_core_definition.ret (T_ct (poly1305_update_blocks_pure m_40
    st_41))}.

Import Hacspec_Lib.
Definition st_38_loc : Location :=
  ((field_element_t '× field_element_t '× poly_key_t) : choice_type ; 49%nat).
Program Definition poly1305_update_blocks_state
  (m_40 : byte_seq)
  (st_41 : poly_state_t)
  : code (fset (path.sort leb [ st_38_loc])) [interface] (@ct (poly_state_t)) :=
  (({code #put st_38_loc := 
        (st_41) ;;
      st_38 ← get st_38_loc ;;
      let st_38 : (field_element_t '× field_element_t '× poly_key_t) :=
        (st_38) in
       temp_45 ←
        (seq_len (m_40)) ;;
      let n_blocks_42 : uint_size :=
        ((temp_45) ./ (blocksize_v)) in
      for_loop_usize (usize 0) (n_blocks_42) (fun i_43 =>
        ({code  temp_46 ←
            (seq_get_exact_chunk (m_40) (blocksize_v) (i_43)) ;;
           temp_47 ←
            (array_from_seq (16) (temp_46 : seq int8)) ;;
          let block_44 : poly_block_t :=
            (temp_47) in
           temp_48 ←
            (poly1305_update_block (block_44) (st_38)) ;;
          st_38 ← get st_38_loc ;;
          
          #put st_38_loc := 
            (temp_48) ;;
          st_38 ← get st_38_loc ;;
          
          @pkg_core_definition.ret (unit_ChoiceEquality) ( (tt)) } : code (
            fset (path.sort leb [ st_38_loc])) [interface] _)) ;;
      @pkg_core_definition.ret ((
          field_element_t '×
          field_element_t '×
          poly_key_t
        )) ( (st_38)) } : code (fset (
                                    path.sort leb [ st_38_loc])) [interface] _)).
Fail Next Obligation.

Program Definition poly1305_update_blocks
  (m_40 : byte_seq)
  (st_41 : poly_state_t)
  : both (fset (path.sort leb [ st_38_loc])) poly_state_t :=
  {|
  is_pure := poly1305_update_blocks_pure(m_40 : byte_seq)
  (st_41 : poly_state_t);
  is_state := poly1305_update_blocks_state(m_40 : byte_seq)
  (st_41 : poly_state_t);
  |}.
Next Obligation.
unfold poly1305_update_blocks_pure.
unfold poly1305_update_blocks_state.
unfold is_pure.
unfold is_state.

unfold prog.

unfold seq_len.
unfold lift_to_code.

step_code.


enough (unsigned (usize 0%nat) <=
          unsigned (Hacspec_Lib_Pre.seq_len m_40 ./ blocksize_v))%Z.

unfold for_loop_usize.
replace (from_uint_size (usize 0)) with 0 by reflexivity.

set (f := fun n : nat => _).
set (k := (_ , _)).
pose (foldi_nat_is_loop 0 (from_uint_size (Hacspec_Lib_Pre.seq_len m_40 ./ blocksize_v)) (fun (_ : poly_state_t) => f) k).
hnf in e.

Set Printing Coercions.

set (tct := T_ct _) in *.
replace tct with k in e by reflexivity. 
remove_T_ct.
rewrite e.
  
pose @Build_both.
epose (fun x y => @Build_both _ _ (d x y) (c x)) .


both_bind.

unfold c at 1.

unfold poly1305_update_block.
unfold poly1305_update_block_state.
unfold poly1305_update_block_pure.
destruct st_41 as [[]].

unfold poly1305_encode_block.
unfold is_pure.
unfold is_state.
unfold poly1305_encode_block_state.
unfold poly1305_encode_block_pure.

unfold prog.
unfold seq_get_exact_chunk.
unfold array_from_seq.
unfold array_to_seq.
unfold uint128_from_le_bytes.
unfold nat_mod_from_secret_literal.
unfold nat_mod_pow2.

unfold lift_to_code.

step_code.



apply r_restore_lhs.
intros.
subst.

apply r_get_remember_lhs. intros.
apply r_put_lhs.
apply r_get_remember_lhs. intros.
fold (@bind 'unit).
step_code.


set (lo := S (from_uint_size _)).
set (hi := (from_uint_size (_ ./ _))).
set (f := fun _ _ => _ ).
set (v := (@pair (@T (prod_ChoiceEquality field_element_t field_element_t))
                (@T poly_key_t) (@pair (@T field_element_t) (@T field_element_t) t t0) t1) : poly_state_t).

replace (foldi_nat lo hi f tt ;; ret _) with (foldi_nat lo hi (fun (x : nat) (a : poly_state_t) => f x tt ;; ret a) v) by apply (@foldi_nat_consume_ret (prod_ChoiceEquality _ _) lo hi f v).

(* replace (S (from_uint_size (usize 0))) with (from_uint_size (usize (S 0))) in lo. *)
pose (foldi_to_foldi_nat (usize (S 0)) (Hacspec_Lib_Pre.seq_len m_40 ./ blocksize_v)).

rewrite foldi_nat_to_foldi.

epose (@foldi
       (prod_ChoiceEquality (prod_ChoiceEquality field_element_t field_element_t)
                            poly_key_t) (@usize nat nat_uint_sizable lo) (@usize nat nat_uint_sizable hi)
       _ _
       (fun (x1 : @T uint_size)
          (a : @T
                 (prod_ChoiceEquality
                    (prod_ChoiceEquality field_element_t field_element_t) poly_key_t)) =>
        {code (@bind (chElement (@ct unit_ChoiceEquality))
          (chElement
             (@ct
                (prod_ChoiceEquality (prod_ChoiceEquality field_element_t field_element_t)
                   poly_key_t))) (f (@from_uint_size nat nat_uint_sizable x1) tt)
          (fun _ : choice.Choice.sort (chElement (@ct unit_ChoiceEquality)) =>
           @ret
             (chElement
                (@ct
                   (prod_ChoiceEquality
                      (prod_ChoiceEquality field_element_t field_element_t) poly_key_t)))
             (@T_ct
                (prod_ChoiceEquality (prod_ChoiceEquality field_element_t field_element_t)
                                     poly_key_t) a)))}) v).

replace (@foldi_pre
       (prod_ChoiceEquality (prod_ChoiceEquality field_element_t field_element_t)
          poly_key_t) (@usize nat nat_uint_sizable lo) (@usize nat nat_uint_sizable hi)
       (fun (x1 : @T uint_size)
          (a : @T
                 (prod_ChoiceEquality
                    (prod_ChoiceEquality field_element_t field_element_t) poly_key_t)) =>
        @bind (chElement (@ct unit_ChoiceEquality))
          (chElement
             (@ct
                (prod_ChoiceEquality (prod_ChoiceEquality field_element_t field_element_t)
                   poly_key_t))) (f (@from_uint_size nat nat_uint_sizable x1) tt)
          (fun _ : choice.Choice.sort (chElement (@ct unit_ChoiceEquality)) =>
           @ret
             (chElement
                (@ct
                   (prod_ChoiceEquality
                      (prod_ChoiceEquality field_element_t field_element_t) poly_key_t)))
             (@T_ct
                (prod_ChoiceEquality (prod_ChoiceEquality field_element_t field_element_t)
                   poly_key_t) a))) v) with (prog c0).
unfold c0.

unfold prog.
(* eapply rpre_weaken_rule. *)

set (f_state := (fun (x1 : block_index_t) (a : poly_state_t) =>
        {code f (from_uint_size x1) tt ;;
        ret a })).

set (f_pure := (fun (i_43 : block_index_t) => _)).

unfold hi in *. clear hi. set (hi := (Hacspec_Lib_Pre.seq_len m_40 ./ blocksize_v)).
unfold lo in *. clear lo.
unfold nat_uint_sizable.
unfold usize at 3.
unfold from_uint_size at 3.

set (lo := usize 0%Z).
set (P := _ ⋊ _).
assert (forall x , P (x , x)).
clear.
intros.
unfold P.
unfold set_lhs.
hnf.
esplit.
exists (set_heap x1 st_38_loc v).
split.
hnf.
split.
exists x1.
split.
reflexivity.
reflexivity.

hnf.
rewrite get_set_heap_eq.

exists x1.
cbn.

pose (@foldi_both _ _ lo (hi) f_state f_pure v H P).

Set Printing Coercions.

pose @r_transR.
specialize r0 with (P := P).
              (set_lhs st_38_loc v (fun '(h₀, h₁) => h₀ = h₁) ⋊ rem_lhs st_38_loc x)). 
                                                                                  (c₁' := ret (Hacspec_Lib_Pre.foldi lo hi f_pure v)).

(((T_ct
              (Hacspec_Lib_Pre.nat_mod_from_secret_literal
                 (T_ct
                    (Hacspec_Lib_Pre.uint128_from_le_bytes
                       (T_ct
                          (Hacspec_Lib_Pre.array_from_seq 16
                             (T_ct
                                (Hacspec_Lib_Pre.array_to_seq
                                   (T_ct
                                      (Hacspec_Lib_Pre.array_from_seq 16
                                         (T_ct
                                            (Hacspec_Lib_Pre.seq_get_exact_chunk m_40
                                               blocksize_v
                                               (usize (from_uint_size (repr (Z.of_nat 0))))))))))))))) +%
            T_ct
              (Hacspec_Lib_Pre.nat_mod_pow2 1361129467683753853853498429727072845819
                 (N.of_nat (uint_size_to_nat (Z_to_uint_size (toword (usize 128))))))) +%
           t) *% t0, t0, t1)

  eapply r_transR.
apply r.
assumption.
intros.
unfold f_state.
unfold f_pure.
unfold prog.
unfold f.
unfold c.


unfold poly1305_update_block.
unfold poly1305_update_block_state.
unfold poly1305_update_block_pure.
(* destruct st_41 as [[]]. *)

unfold poly1305_encode_block.
unfold is_pure.
unfold is_state.
unfold poly1305_encode_block_state.
unfold poly1305_encode_block_pure.

unfold prog.
unfold seq_get_exact_chunk.
unfold array_from_seq.
unfold array_to_seq.
unfold uint128_from_le_bytes.
unfold nat_mod_from_secret_literal.
unfold nat_mod_pow2.

unfold lift_to_code.

step_code.




unfold lo.
unfold hi.
unfold nat_uint_sizable.
unfold from_uint_size.
unfold usize.





rewrite  Z2Nat.id.
rewrite Nat2Z.id.

eapply r.

Print foldi.
rewrite <- foldi_to_foldi_nat.

apply foldi_both.


  

Set Printing All.

rewrite <- e.
rewrite <- foldi_nat_consume_ret.




(@bind (chElement chUnit)
       (chElement
          (@ct
             (prod_ChoiceEquality (prod_ChoiceEquality field_element_t field_element_t)
                poly_key_t))) (@foldi_nat unit_ChoiceEquality lo hi f tt)
       (fun _ : choice.Choice.sort (chElement chUnit) =>
        @ret
          (chElement
             (@ct
                (prod_ChoiceEquality (prod_ChoiceEquality field_element_t field_element_t)
                   poly_key_t)))
          (@pair (@T (prod_ChoiceEquality field_element_t field_element_t))
                 (@T poly_key_t) t2 t3)))

(@bind (chElement chUnit)
          (chElement
             (@ct
                (prod_ChoiceEquality (prod_ChoiceEquality field_element_t field_element_t)
                   poly_key_t))) (@foldi_nat unit_ChoiceEquality lo hi f tt)
          (fun _ : choice.Choice.sort (chElement (@ct unit_ChoiceEquality)) =>
           @ret
             (chElement
                (@ct
                   (prod_ChoiceEquality
                      (prod_ChoiceEquality field_element_t field_element_t) poly_key_t)))
             (@T_ct
                (prod_ChoiceEquality (prod_ChoiceEquality field_element_t field_element_t)
                   poly_key_t)
                (@pair (@T (prod_ChoiceEquality field_element_t field_element_t))
                   (@T poly_key_t) t2 t3))))

set (v := (t, t0, t1) ).


rewrite <- foldi_nat_consume_ret.


apply rreflexivity_rule.

reflexivity.


fold bind.

Check r_get_remind_lhs.
apply r_get_remind_lhs.

apply r_restore_lhs.
intros. subst.  admit. 


rewrite <- bind_assoc.
unfold bind at 1.



replace (S
          (from_uint_size (Hacspec_Lib_Pre.seq_len m_40 ./ blocksize_v) -
             from_uint_size (usize 0) - 1)) with
  (S (from_uint_size ((Hacspec_Lib_Pre.seq_len m_40 ./ blocksize_v) .- repr 1) -
      from_uint_size (usize 0))).

pose (foldi_nat (usize 0) ((Hacspec_Lib_Pre.seq_len m_40 ./ blocksize_v) - 1)).
remember r.

inversion Heqr0.
unfold r in Heqr0.
unfold foldi_nat in r.
destruct ((Hacspec_Lib_Pre.seq_len m_40 ./ blocksize_v) - 1 - usize 0) eqn:ro in r.


replace 



fold foldi_nat.

rewrite <- foldi__nat_move_S_append.
unfold c.
unfold prog.
unfold seq_get_exact_chunk.
unfold array_from_seq.

rewrite forc;




eapply (r_transL
          (foldi_nat_
       (S
          (from_uint_size (Hacspec_Lib_Pre.seq_len m_40 ./ blocksize_v) -
           from_uint_size (usize 0) - 1)) 0
       (fun (x : nat) (_ : unit_ChoiceEquality) =>
        c (usize (x + from_uint_size (usize 0)))) tt ;; ret st_41)) .
eapply r_bind.
apply rsymmetry.
apply rsym_pre. intros ; subst ; reflexivity.
eapply rpost_weaken_rule.
rewrite for_loop_equality.
reflexivity.


apply for_loop_equality. apply H.
intros. subst. destruct a₁. reflexivity.
intros. apply r_ret. intros. inversion H0. subst. reflexivity.
Set Printing Coercions.

eapply (r_transL
          (lift_to_code (Hacspec_Lib_Pre.foldi (usize 0) (Hacspec_Lib_Pre.seq_len m_40 ./ blocksize_v) (fun i_43 st_38 : T =>
              let (is_pure, _) :=
                poly1305_update_block
                  (Hacspec_Lib_Pre.array_from_seq 16
                     (Hacspec_Lib_Pre.seq_get_exact_chunk m_40 blocksize_v i_43)) st_38 in
              is_pure) _) ;; ret st_41)).
eapply r_bind.
apply rsymmetry.
apply rsym_pre. intros ; subst ; reflexivity.
eapply rpost_weaken_rule.
pose @foldi_both.
apply foldi_both.
intros [h₀  h₁]. apply (h₀ = h₁).
apply H.
intros.





(* unfold prog. *)
(* unfold foldi. *)

(* assert (forall lo hi {L I} f v (H : (unsigned lo <= unsigned hi)%Z), *)
(*            (foldi lo hi (fun x _ => f x) tt ;; ret v) = *)
(*            (foldi lo hi (L := L) (I := I) (fun x v => {code f x ;; ret v}) (ct_T v)) *)
(*        ). *)
(* clear. *)
(* intros. *)
(* unfold prog. *)
(* unfold foldi. *)
(* rewrite foldi_to_foldi_nat by apply H. *)
(* rewrite foldi_to_foldi_nat by apply H. *)
(* unfold prog. *)
(* unfold foldi_nat. *)
(* destruct (Z.to_nat (unsigned hi) - Z.to_nat (unsigned lo)) ; [ reflexivity | .. ]. *)
(* rewrite <- foldi__nat_move_S. *)
(* rewrite <- foldi__nat_move_S. *)
(* f_equal. *)
(* induction n. *)
(* - cbn. *)
(*   rewrite bind_ret. *)

apply 

unfold prog.
unfold foldi.
rewrite foldi_to_foldi_nat.

  

pose (foldi_both (usize 0) (Hacspec_Lib_Pre.seq_len m_40 ./ blocksize_v) (fun (x : block_index_t) (_ : unit_ChoiceEquality) => c x)).

apply H.

unfold nat_uint_sizable in r.
unfold usize in r.
rewrite unsigned_repr_alt in r.




specialize r with ()
apply r.

unfold for_loop_usize.
unfold for_loop_range.

unfold prog.

unfold poly1305_update_block.
unfold poly1305_update_block_pure.
unfold poly1305_update_block_state.
unfold is_pure.
unfold is_state.
destruct st_41 as [[]].

unfold poly1305_encode_block.
unfold poly1305_encode_block_pure.
unfold poly1305_encode_block_state.
unfold is_pure.
unfold is_state.
unfold prog.

unfold seq_get_exact_chunk.
unfold array_from_seq.

unfold array_to_seq.
unfold array_from_seq.
unfold uint128_from_le_bytes.
unfold nat_mod_from_secret_literal.
unfold nat_mod_pow2.

unfold lift_to_code.


unfold from_uint_size.
unfold nat_uint_sizable.
unfold usize.
Set Printing Coercions.

rewrite unsigned_repr_alt.
rewrite Nat2Z.id.
rewrite Nat.sub_0_r.

unfold for_loop.
destruct (Z.to_nat (unsigned (T_ct (Hacspec_Lib_Pre.seq_len m_40) ./ blocksize_v))).





repeat rewrite unsigned_repr_alt.


rewrite unsigned_repr.

apply (for_loop_rule (fun i => fun '(s₀, s₁) => set_lhs st_38_loc st_41 (fun '(h₀, h₁) => h₀ = h₁) (s₀, s₁))).

unfold poly1305_update_block.
unfold poly1305_update_block_pure.
unfold poly1305_update_block_state.
unfold is_pure.
unfold is_state.

unfold prog.

destruct st_38 as [[]].

unfold poly1305_encode_block.
unfold poly1305_encode_block_pure.
unfold poly1305_encode_block_state.
unfold is_pure.
unfold is_state.
unfold prog.

unfold seq_get_exact_chunk.
unfold array_from_seq.



unfold array_to_seq.
  unfold array_from_seq.
  unfold uint128_from_le_bytes.
  unfold nat_mod_from_secret_literal.
  unfold nat_mod_pow2.

  unfold lift_to_code.

Admitted.

Import Hacspec_Lib_Pre.
Definition poly1305_update_last_pure
  (pad_len_52 : uint_size)
  (b_53 : sub_block_t)
  (st_54 : poly_state_t)
  : poly_state_t :=
  let st_50 : (field_element_t '× field_element_t '× poly_key_t) :=
    st_54 in 
  let '(st_50) :=
    if (seq_len (b_53)) !=.? (usize 0):bool then (let '(acc_55, r_56, k_57) :=
        st_50 in 
      let st_50 :=
        (
          ((poly1305_encode_last (pad_len_52) (b_53)) +% (acc_55)) *% (r_56),
          r_56,
          k_57
        ) in 
      (st_50)) else ((st_50)) in 
  st_50.
Definition poly1305_update_last_pure_code
  (pad_len_52 : uint_size)
  (b_53 : sub_block_t)
  (st_54 : poly_state_t)
  : code fset.fset0 [interface] (@ct poly_state_t) :=
  {code pkg_core_definition.ret (T_ct (poly1305_update_last_pure pad_len_52
    b_53
    st_54))}.

Import Hacspec_Lib.
Definition st_50_loc : Location :=
  ((field_element_t '× field_element_t '× poly_key_t) : choice_type ; 60%nat).
Program Definition poly1305_update_last_state
  (pad_len_52 : uint_size)
  (b_53 : sub_block_t)
  (st_54 : poly_state_t)
  : code (fset (path.sort leb [ st_50_loc])) [interface] (@ct (poly_state_t)) :=
  (({code #put st_50_loc := 
        (st_54) ;;
      st_50 ← get st_50_loc ;;
      let st_50 : (field_element_t '× field_element_t '× poly_key_t) :=
        (st_50) in
       temp_58 ←
        (seq_len (b_53)) ;;
       '(st_50) ←
        (if (temp_58) !=.? (usize 0):bool_ChoiceEquality then (({code let '(
                  acc_55,
                  r_56,
                  k_57
                ) :=
                (st_50) : (field_element_t '× field_element_t '× poly_key_t
              ) in
               temp_59 ←
                (poly1305_encode_last (pad_len_52) (b_53)) ;;
              st_50 ← get st_50_loc ;;
              
              #put st_50_loc := 
                ((((temp_59) +% (acc_55)) *% (r_56), r_56, k_57)) ;;
              st_50 ← get st_50_loc ;;
              
              @pkg_core_definition.ret (_) ( ((st_50))) } : code (fset (
                  path.sort leb [ st_50_loc])) [interface] _)) else (
            @pkg_core_definition.ret (_) ( ((st_50))))) ;;
      
      @pkg_core_definition.ret ((
          field_element_t '×
          field_element_t '×
          poly_key_t
        )) ( (st_50)) } : code (fset (
          path.sort leb [ st_50_loc])) [interface] _)).
Fail Next Obligation.

Definition poly1305_update_last
  (pad_len_52 : uint_size)
  (b_53 : sub_block_t)
  (st_54 : poly_state_t)
  : both (fset (path.sort leb [ st_50_loc])) poly_state_t :=
  {|
  is_pure := poly1305_update_last_pure(pad_len_52 : uint_size)
  (b_53 : sub_block_t)
  (st_54 : poly_state_t);
  is_state := poly1305_update_last_state(pad_len_52 : uint_size)
  (b_53 : sub_block_t)
  (st_54 : poly_state_t);
  |}.

Instance poly1305_update_last_eq :
forall (pad_len_52 : uint_size)
(b_53 : sub_block_t)
(st_54 : poly_state_t),
CodeEqProofStatement (poly1305_update_last(pad_len_52 : uint_size)
  (b_53 : sub_block_t)
  (st_54 : poly_state_t)).
Proof.
intros.
unfold CodeEqProofStatement.

unfold poly1305_update_last.
unfold poly1305_update_last_pure.
unfold poly1305_update_last_state.
unfold is_pure.
unfold is_state.

unfold prog.
Admitted.

Import Hacspec_Lib_Pre.
Definition poly1305_update_pure
  (m_61 : byte_seq)
  (st_62 : poly_state_t)
  : poly_state_t :=
  let st_63 : (field_element_t '× field_element_t '× poly_key_t) :=
    poly1305_update_blocks (m_61) (st_62) in 
  let last_64 : seq uint8 :=
    seq_get_remainder_chunk (m_61) (blocksize_v) in 
  poly1305_update_last (seq_len (last_64)) (last_64) (st_63).
Definition poly1305_update_pure_code
  (m_61 : byte_seq)
  (st_62 : poly_state_t)
  : code fset.fset0 [interface] (@ct poly_state_t) :=
  {code pkg_core_definition.ret (T_ct (poly1305_update_pure m_61 st_62))}.

Import Hacspec_Lib.

Program Definition poly1305_update_state
  (m_61 : byte_seq)
  (st_62 : poly_state_t)
  : code (fset (path.sort leb [ st_38_loc ; st_50_loc])) [interface] (@ct (
      poly_state_t)) :=
  (({code  temp_65 ←
        (poly1305_update_blocks (m_61) (st_62)) ;;
      let st_63 : (field_element_t '× field_element_t '× poly_key_t) :=
        (temp_65) in
       temp_66 ←
        (seq_get_remainder_chunk (m_61) (blocksize_v)) ;;
      let last_64 : seq uint8 :=
        (temp_66) in
       temp_67 ←
        (seq_len (last_64)) ;;
       temp_68 ←
        (poly1305_update_last (temp_67) (last_64) (st_63)) ;;
      @pkg_core_definition.ret (poly_state_t) ( (temp_68)) } : code (fset (
          path.sort leb [ st_38_loc ; st_50_loc])) [interface] _)).
Fail Next Obligation.

Definition poly1305_update
  (m_61 : byte_seq)
  (st_62 : poly_state_t)
  : both (fset (path.sort leb [ st_38_loc ; st_50_loc])) poly_state_t :=
  {|
  is_pure := poly1305_update_pure(m_61 : byte_seq)
  (st_62 : poly_state_t);
  is_state := poly1305_update_state(m_61 : byte_seq)
  (st_62 : poly_state_t);
  |}.

Instance poly1305_update_eq :
forall (m_61 : byte_seq)
(st_62 : poly_state_t),
CodeEqProofStatement (poly1305_update(m_61 : byte_seq) (st_62 : poly_state_t)).
Proof.
intros.
unfold CodeEqProofStatement.

unfold poly1305_update.
unfold poly1305_update_pure.
unfold poly1305_update_state.
unfold is_pure.
unfold is_state.

unfold prog.
Admitted.

Import Hacspec_Lib_Pre.
Definition poly1305_finish_pure (st_69 : poly_state_t) : poly1305_tag_t :=
  let '(acc_70, _, k_71) :=
    st_69 in 
  let n_72 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default) (16) (
        array_to_seq (k_71)) (usize 16) (usize 16)) in 
  let aby_73 : seq uint8 :=
    nat_mod_to_byte_seq_le (acc_70) in 
  let a_74 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default) (16) (aby_73) (usize 0) (
        usize 16)) in 
  array_from_seq (16) (array_to_seq (uint128_to_le_bytes ((a_74) .+ (n_72)))).
Definition poly1305_finish_pure_code
  (st_69 : poly_state_t)
  : code fset.fset0 [interface] (@ct poly1305_tag_t) :=
  {code pkg_core_definition.ret (T_ct (poly1305_finish_pure st_69))}.

Import Hacspec_Lib.

Program Definition poly1305_finish_state
  (st_69 : poly_state_t)
  : code (fset.fset0) [interface] (@ct (poly1305_tag_t)) :=
  (({code let '(acc_70, _, k_71) :=
        (st_69) : (field_element_t '× field_element_t '× poly_key_t) in
       temp_75 ←
        (array_to_seq (k_71)) ;;
      let temp_75 : seq uint8 :=
        (temp_75) in
       temp_76 ←
        (array_from_slice (default) (16) (temp_75) (usize 16) (usize 16)) ;;
       temp_77 ←
        (uint128_from_le_bytes (temp_76)) ;;
      let n_72 : uint128 :=
        (temp_77) in
       temp_78 ←
        (nat_mod_to_byte_seq_le (acc_70)) ;;
      let aby_73 : seq uint8 :=
        (temp_78) in
       temp_79 ←
        (array_from_slice (default) (16) (aby_73) (usize 0) (usize 16)) ;;
       temp_80 ←
        (uint128_from_le_bytes (temp_79)) ;;
      let a_74 : uint128 :=
        (temp_80) in
       temp_81 ←
        (uint128_to_le_bytes ((a_74) .+ (n_72))) ;;
       temp_82 ←
        (array_to_seq (temp_81)) ;;
      let temp_82 : seq uint8 :=
        (temp_82) in
       temp_83 ←
        (array_from_seq (16) (temp_82)) ;;
      @pkg_core_definition.ret (poly1305_tag_t) ( (temp_83)) } : code (
        fset.fset0) [interface] _)).
Fail Next Obligation.

Definition poly1305_finish
  (st_69 : poly_state_t)
  : both (fset.fset0) poly1305_tag_t :=
  {|
  is_pure := poly1305_finish_pure(st_69 : poly_state_t);
  is_state := poly1305_finish_state(st_69 : poly_state_t);
  |}.

Instance poly1305_finish_eq :
forall (st_69 : poly_state_t),
CodeEqProofStatement (poly1305_finish(st_69 : poly_state_t)).
Proof.
intros.
unfold CodeEqProofStatement.

unfold poly1305_finish.
unfold poly1305_finish_pure.
unfold poly1305_finish_state.
unfold is_pure.
unfold is_state.

unfold prog.
Admitted.

Import Hacspec_Lib_Pre.
Definition poly1305_pure
  (m_86 : byte_seq)
  (key_87 : poly_key_t)
  : poly1305_tag_t :=
  let st_84 : (field_element_t '× field_element_t '× poly_key_t) :=
    poly1305_init (key_87) in 
  let st_84 :=
    poly1305_update (m_86) (st_84) in 
  poly1305_finish (st_84).
Definition poly1305_pure_code
  (m_86 : byte_seq)
  (key_87 : poly_key_t)
  : code fset.fset0 [interface] (@ct poly1305_tag_t) :=
  {code pkg_core_definition.ret (T_ct (poly1305_pure m_86 key_87))}.

Import Hacspec_Lib.
Definition st_84_loc : Location :=
  ((field_element_t '× field_element_t '× poly_key_t) : choice_type ; 91%nat).
Program Definition poly1305_state
  (m_86 : byte_seq)
  (key_87 : poly_key_t)
  : code (fset (
      path.sort leb [ st_50_loc ; n_0_loc ; st_84_loc ; st_38_loc])) [interface] (
    @ct (poly1305_tag_t)) :=
  (({code  temp_88 ←
        (poly1305_init (key_87)) ;;
      #put st_84_loc := 
        (temp_88) ;;
      st_84 ← get st_84_loc ;;
      let st_84 : (field_element_t '× field_element_t '× poly_key_t) :=
        (st_84) in
       temp_89 ←
        (poly1305_update (m_86) (st_84)) ;;
      st_84 ← get st_84_loc ;;
      
      #put st_84_loc := 
        (temp_89) ;;
      st_84 ← get st_84_loc ;;
      
       temp_90 ←
        (poly1305_finish (st_84)) ;;
      @pkg_core_definition.ret (poly1305_tag_t) ( (temp_90)) } : code (fset (
          path.sort leb [ st_50_loc ; n_0_loc ; st_84_loc ; st_38_loc])) [interface] _)).
Fail Next Obligation.

Definition poly1305
  (m_86 : byte_seq)
  (key_87 : poly_key_t)
  : both (fset (
      path.sort leb [ st_50_loc ; n_0_loc ; st_84_loc ; st_38_loc])) poly1305_tag_t :=
  {|
  is_pure := poly1305_pure(m_86 : byte_seq)
  (key_87 : poly_key_t);
  is_state := poly1305_state(m_86 : byte_seq)
  (key_87 : poly_key_t);
  |}.

Instance poly1305_eq :
forall (m_86 : byte_seq)
(key_87 : poly_key_t),
CodeEqProofStatement (poly1305(m_86 : byte_seq) (key_87 : poly_key_t)).
Proof.
intros.
unfold CodeEqProofStatement.

unfold poly1305.
unfold poly1305_pure.
unfold poly1305_state.
unfold is_pure.
unfold is_state.

unfold prog.
Admitted.

