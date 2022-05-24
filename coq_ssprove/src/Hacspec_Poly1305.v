(** This file was automatically generated using Hacspec **)
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From CoqWord Require Import ssrZ word.
From Jasmin Require Import word.

From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope bool_scope.


Require Import ChoiceEquality.
Require Import LocationUtility.
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

Definition n_0_loc : Location :=
  (uint128 : choice_type ; 8%nat).
Program Definition poly1305_encode_r_state
  (b_2 : poly_block_t)
  : code (fset ([ n_0_loc])) [interface] (@ct (field_element_t)) :=
  (({| prog :=  temp_3 ←
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
      #put n_0_loc := 
        ((n_0) .& (temp_6)) ;;
      n_0 ← get n_0_loc ;;
      
       temp_7 ←
        (nat_mod_from_secret_literal (n_0)) ;;
      @pkg_core_definition.ret (field_element_t) ( (
        temp_7)) ; prog_valid := ltac:(ssprove_valid'_2) |}: code (fset (
          [ n_0_loc])) [interface] _)).
Fail Next Obligation.

Program Definition poly1305_encode_r
  (b_2 : poly_block_t)
  : both (fset ([ n_0_loc])) [interface] field_element_t :=
  {|
  is_pure := poly1305_encode_r_pure (b_2 : poly_block_t);
  is_state := poly1305_encode_r_state (b_2 : poly_block_t);
  |}.
Next Obligation.
intros.
unfold poly1305_encode_r_pure.
unfold poly1305_encode_r_state.

unfold prog.
step_code.
Qed.

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


Program Definition poly1305_encode_block_state
  (b_9 : poly_block_t)
  : code (fset.fset0) [interface] (@ct (field_element_t)) :=
  (({| prog :=  temp_12 ←
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
          temp_16))) ; prog_valid := ltac:(ssprove_valid'_2) |}: code (
        fset.fset0) [interface] _)).
Fail Next Obligation.

Program Definition poly1305_encode_block
  (b_9 : poly_block_t)
  : both (fset.fset0) [interface] field_element_t :=
  {|
  is_pure := poly1305_encode_block_pure (b_9 : poly_block_t);
  is_state := poly1305_encode_block_state (b_9 : poly_block_t);
  |}.
Next Obligation.
intros.
unfold poly1305_encode_block_pure.
unfold poly1305_encode_block_state.

unfold prog.
step_code.
Qed.

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


Program Definition poly1305_encode_last_state
  (pad_len_17 : block_index_t)
  (b_18 : sub_block_t)
  : code (fset.fset0) [interface] (@ct (field_element_t)) :=
  (({| prog :=  temp_21 ←
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
          temp_25))) ; prog_valid := ltac:(ssprove_valid'_2) |}: code (
        fset.fset0) [interface] _)).
Fail Next Obligation.

Program Definition poly1305_encode_last
  (pad_len_17 : block_index_t)
  (b_18 : sub_block_t)
  : both (fset.fset0) [interface] field_element_t :=
  {|
  is_pure := poly1305_encode_last_pure (pad_len_17 : block_index_t)
  (b_18 : sub_block_t);
  is_state := poly1305_encode_last_state (pad_len_17 : block_index_t)
  (b_18 : sub_block_t);
  |}.
Next Obligation.
intros.
unfold poly1305_encode_last_pure.
unfold poly1305_encode_last_state.

unfold prog.
step_code.
Qed.

Definition poly1305_init_pure (k_26 : poly_key_t) : poly_state_t :=
  let r_27 : field_element_t :=
    poly1305_encode_r (array_from_slice (default) (16) (array_to_seq (k_26)) (
        usize 0) (usize 16)) in 
  (nat_mod_zero , r_27, k_26).
Definition poly1305_init_pure_code
  (k_26 : poly_key_t)
  : code fset.fset0 [interface] (@ct poly_state_t) :=
  {code pkg_core_definition.ret (T_ct (poly1305_init_pure k_26))}.


Program Definition poly1305_init_state
  (k_26 : poly_key_t)
  : code (fset ([ n_0_loc])) [interface] (@ct (poly_state_t)) :=
  (({| prog :=  temp_28 ←
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
        )) ( ((temp_31, r_27, k_26
        ))) ; prog_valid := ltac:(ssprove_valid'_2) |}: code (fset (
          [ n_0_loc])) [interface] _)).
Fail Next Obligation.

Program Definition poly1305_init
  (k_26 : poly_key_t)
  : both (fset ([ n_0_loc])) [interface] poly_state_t :=
  {|
  is_pure := poly1305_init_pure (k_26 : poly_key_t);
  is_state := poly1305_init_state (k_26 : poly_key_t);
  |}.
Next Obligation.
intros.
unfold poly1305_init_pure.
unfold poly1305_init_state.

unfold prog.
Admitted.

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


Program Definition poly1305_update_block_state
  (b_32 : poly_block_t)
  (st_33 : poly_state_t)
  : code (fset.fset0) [interface] (@ct (poly_state_t)) :=
  (({| prog := let '(acc_34, r_35, k_36) :=
        (st_33) : (field_element_t '× field_element_t '× poly_key_t) in
       temp_37 ←
        (poly1305_encode_block (b_32)) ;;
      @pkg_core_definition.ret ((
          field_element_t '×
          field_element_t '×
          poly_key_t
        )) ( ((((temp_37) +% (acc_34)) *% (r_35), r_35, k_36
        ))) ; prog_valid := ltac:(ssprove_valid'_2) |}: code (
        fset.fset0) [interface] _)).
Fail Next Obligation.

Program Definition poly1305_update_block
  (b_32 : poly_block_t)
  (st_33 : poly_state_t)
  : both (fset.fset0) [interface] poly_state_t :=
  {|
  is_pure := poly1305_update_block_pure (b_32 : poly_block_t)
  (st_33 : poly_state_t);
  is_state := poly1305_update_block_state (b_32 : poly_block_t)
  (st_33 : poly_state_t);
  |}.
Next Obligation.
intros.
unfold poly1305_update_block_pure.
unfold poly1305_update_block_state.

unfold prog.
step_code.
Qed.

Definition poly1305_update_blocks_pure
  (m_40 : byte_seq)
  (st_41 : poly_state_t)
  : poly_state_t :=
  let st_38 : (field_element_t '× field_element_t '× poly_key_t) :=
    st_41 in 
  let n_blocks_42 : uint_size :=
    (seq_len (m_40)) ./ (blocksize_v) in 
  let st_38 :=
    Hacspec_Lib_Pre.foldi (usize 0) (n_blocks_42) (fun i_43 st_38 =>
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

Definition st_38_loc : Location :=
  ((field_element_t '× field_element_t '× poly_key_t) : choice_type ; 49%nat).
Program Definition poly1305_update_blocks_state
  (m_40 : byte_seq)
  (st_41 : poly_state_t)
  : code (fset ([ st_38_loc])) [interface] (@ct (poly_state_t)) :=
  (({| prog := #put st_38_loc := 
        (st_41) ;;
      st_38 ← get st_38_loc ;;
      let st_38 : (field_element_t '× field_element_t '× poly_key_t) :=
        (st_38) in
       temp_45 ←
        (seq_len (m_40)) ;;
      let n_blocks_42 : uint_size :=
        ((temp_45) ./ (blocksize_v)) in
       st_38 ←
        (foldi (usize 0) (n_blocks_42) (fun i_43 (st_38 : _) =>
            ({| prog :=  temp_46 ←
                (seq_get_exact_chunk (m_40) (blocksize_v) (i_43)) ;;
               temp_47 ←
                (array_from_seq (16) (temp_46 : seq int8)) ;;
              let block_44 : poly_block_t :=
                (temp_47) in
               temp_48 ←
                (poly1305_update_block (block_44) (st_38)) ;;
              #put st_38_loc := 
                (temp_48) ;;
              st_38 ← get st_38_loc ;;
              
              @pkg_core_definition.ret (_) ( ((st_38
                ))) ; prog_valid := ltac:(ssprove_valid'_2) |}: code (fset (
                  [ st_38_loc])) [interface] _)) st_38) ;;
      
      @pkg_core_definition.ret ((
          field_element_t '×
          field_element_t '×
          poly_key_t
        )) ( (st_38)) ; prog_valid := ltac:(ssprove_valid'_2) |}: code (fset (
          [ st_38_loc])) [interface] _)).
Fail Next Obligation.

Program Definition poly1305_update_blocks
  (m_40 : byte_seq)
  (st_41 : poly_state_t)
  : both (fset ([ st_38_loc])) [interface] poly_state_t :=
  {|
  is_pure := poly1305_update_blocks_pure (m_40 : byte_seq)
  (st_41 : poly_state_t);
  is_state := poly1305_update_blocks_state (m_40 : byte_seq)
  (st_41 : poly_state_t);
  |}.
Next Obligation.
intros.
unfold poly1305_update_blocks_pure.
unfold poly1305_update_blocks_state.

unfold prog.

step_code.

apply foldi_as_both.
set (hi := (a ./ blocksize_v)).
destruct_uint_size_as_nat hi.
- reflexivity.
- rewrite H2.  
  apply Nat2Z.is_nonneg.

intros.

step_code.
Qed.

Definition poly1305_update_last_pure
  (pad_len_52 : uint_size)
  (b_53 : sub_block_t)
  (st_54 : poly_state_t)
  : poly_state_t :=
  let st_50 : (field_element_t '× field_element_t '× poly_key_t) :=
    st_54 in 
  let '(st_50) :=
    if (seq_len (b_53) : T) !=.? (usize 0):bool then (let '(acc_55, r_56, k_57) :=
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

Definition st_50_loc : Location :=
  ((field_element_t '× field_element_t '× poly_key_t) : choice_type ; 60%nat).
Program Definition poly1305_update_last_state
  (pad_len_52 : uint_size)
  (b_53 : sub_block_t)
  (st_54 : poly_state_t)
  : code (fset ([ st_50_loc])) [interface] (@ct (poly_state_t)) :=
  (({| prog := #put st_50_loc := 
        (st_54) ;;
      st_50 ← get st_50_loc ;;
      let st_50 : (field_element_t '× field_element_t '× poly_key_t) :=
        (st_50) in
       temp_58 ←
        (seq_len (b_53)) ;;
       '(st_50) ←
        (if (temp_58) !=.? (usize 0):bool_ChoiceEquality then ((
              {| prog := let '(acc_55, r_56, k_57) :=
                (st_50) : (field_element_t '× field_element_t '× poly_key_t
              ) in
               temp_59 ←
                (poly1305_encode_last (pad_len_52) (b_53)) ;;
              #put st_50_loc := 
                ((((temp_59) +% (acc_55)) *% (r_56), r_56, k_57)) ;;
              st_50 ← get st_50_loc ;;
              
              @pkg_core_definition.ret (_) ( ((st_50
                ))) ; prog_valid := ltac:(ssprove_valid'_2) |}: code (fset (
                  [ st_50_loc])) [interface] _)) else (
            @pkg_core_definition.ret (_) ( ((st_50))))) ;;
      
      @pkg_core_definition.ret ((
          field_element_t '×
          field_element_t '×
          poly_key_t
        )) ( (st_50)) ; prog_valid := ltac:(ssprove_valid'_2) |}: code (fset (
          [ st_50_loc])) [interface] _)).
Fail Next Obligation.

Program Definition poly1305_update_last
  (pad_len_52 : uint_size)
  (b_53 : sub_block_t)
  (st_54 : poly_state_t)
  : both (fset ([ st_50_loc])) [interface] poly_state_t :=
  {|
  is_pure := poly1305_update_last_pure (pad_len_52 : uint_size)
  (b_53 : sub_block_t)
  (st_54 : poly_state_t);
  is_state := poly1305_update_last_state (pad_len_52 : uint_size)
  (b_53 : sub_block_t)
  (st_54 : poly_state_t);
  |}.
Next Obligation.
intros.
unfold poly1305_update_last_pure.
unfold poly1305_update_last_state.

unfold prog.
step_code.
destruct negb.
- step_code.
- step_code.
Qed.

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


Program Definition poly1305_update_state
  (m_61 : byte_seq)
  (st_62 : poly_state_t)
  : code (fset ([ st_50_loc ; st_38_loc])) [interface] (@ct (poly_state_t)) :=
  (({| prog :=  temp_65 ←
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
      @pkg_core_definition.ret (poly_state_t) ( (
        temp_68)) ; prog_valid := ltac:(ssprove_valid'_2) |}: code (fset (
          [ st_50_loc ; st_38_loc])) [interface] _)).
Fail Next Obligation.

Program Definition poly1305_update
  (m_61 : byte_seq)
  (st_62 : poly_state_t)
  : both (fset ([ st_50_loc ; st_38_loc])) [interface] poly_state_t :=
  {|
  is_pure := poly1305_update_pure (m_61 : byte_seq)
  (st_62 : poly_state_t);
  is_state := poly1305_update_state (m_61 : byte_seq)
  (st_62 : poly_state_t);
  |}.
Next Obligation.
intros.
unfold poly1305_update_pure.
unfold poly1305_update_state.

unfold prog.
step_code.
Qed.

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
  array_from_seq (16) (array_to_seq (uint128_to_le_bytes ((a_74) .+ (n_72)) : nseq _ _)).
Definition poly1305_finish_pure_code
  (st_69 : poly_state_t)
  : code fset.fset0 [interface] (@ct poly1305_tag_t) :=
  {code pkg_core_definition.ret (T_ct (poly1305_finish_pure st_69))}.


Program Definition poly1305_finish_state
  (st_69 : poly_state_t)
  : code (fset.fset0) [interface] (@ct (poly1305_tag_t)) :=
  (({| prog := let '(acc_70, _, k_71) :=
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
        (array_to_seq (temp_81 : nseq int8 16 )) ;;
      let temp_82 : seq uint8 :=
        (temp_82) in
       temp_83 ←
        (array_from_seq (16) (temp_82)) ;;
      @pkg_core_definition.ret (poly1305_tag_t) ( (
        temp_83)) ; prog_valid := ltac:(ssprove_valid'_2) |}: code (
        fset.fset0) [interface] _)).
Fail Next Obligation.

Program Definition poly1305_finish
  (st_69 : poly_state_t)
  : both (fset.fset0) [interface] poly1305_tag_t :=
  {|
  is_pure := poly1305_finish_pure (st_69 : poly_state_t);
  is_state := poly1305_finish_state (st_69 : poly_state_t);
  |}.
Next Obligation.
intros.
unfold poly1305_finish_pure.
unfold poly1305_finish_state.

unfold prog.
step_code.
Qed.

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

Definition st_84_loc : Location :=
  ((field_element_t '× field_element_t '× poly_key_t) : choice_type ; 91%nat).
Program Definition poly1305_state
  (m_86 : byte_seq)
  (key_87 : poly_key_t)
  : code (fset ([ st_50_loc ; n_0_loc ; st_84_loc ; st_38_loc])) [interface] (
    @ct (poly1305_tag_t)) :=
  (({| prog :=  temp_88 ←
        (poly1305_init (key_87)) ;;
      #put st_84_loc := 
        (temp_88) ;;
      st_84 ← get st_84_loc ;;
      let st_84 : (field_element_t '× field_element_t '× poly_key_t) :=
        (st_84) in
       temp_89 ←
        (poly1305_update (m_86) (st_84)) ;;
      #put st_84_loc := 
        (temp_89) ;;
      st_84 ← get st_84_loc ;;
      
       temp_90 ←
        (poly1305_finish (st_84)) ;;
      @pkg_core_definition.ret (poly1305_tag_t) ( (
        temp_90)) ; prog_valid := ltac:(ssprove_valid'_2) |}: code (fset (
          [ st_50_loc ; n_0_loc ; st_84_loc ; st_38_loc])) [interface] _)).
Fail Next Obligation.

Program Definition poly1305
  (m_86 : byte_seq)
  (key_87 : poly_key_t)
  : both (fset (
      [ st_50_loc ; n_0_loc ; st_84_loc ; st_38_loc])) [interface] poly1305_tag_t :=
  {|
  is_pure := poly1305_pure (m_86 : byte_seq)
  (key_87 : poly_key_t);
  is_state := poly1305_state (m_86 : byte_seq)
  (key_87 : poly_key_t);
  |}.
Next Obligation.
intros.
unfold poly1305_pure.
unfold poly1305_state.

unfold prog.
step_code.
Qed.

