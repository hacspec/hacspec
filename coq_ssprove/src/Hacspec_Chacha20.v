(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
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

Obligation Tactic := try timeout 8 solve_ssprove_obligations.


Definition state_t := nseq (uint32) (usize 16).

Definition state_idx_t :=
  nat_mod (usize 16).
Definition uint_size_in_state_idx_t(n : uint_size) : state_idx_t := int_in_nat_mod n.
Coercion uint_size_in_state_idx_t : uint_size >-> state_idx_t.

Definition constants_t := nseq (uint32) (usize 4).

Definition constants_idx_t :=
  nat_mod (usize 4).
Definition uint_size_in_constants_idx_t(n : uint_size) : constants_idx_t := int_in_nat_mod n.
Coercion uint_size_in_constants_idx_t : uint_size >-> constants_idx_t.

Definition block_t := nseq (uint8) (usize 64).

Definition cha_cha_iv_t := nseq (uint8) (usize 12).

Definition cha_cha_key_t := nseq (uint8) (usize 32).

Definition chacha20_line_pure
  (a_2 : state_idx_t)
  (b_3 : state_idx_t)
  (d_4 : state_idx_t)
  (s_5 : uint_size)
  (m_6 : state_t)
  : state_t :=
  let state_0 : state_t :=
    m_6 in 
  let state_0 :=
    array_upd state_0 (a_2) (((array_index (state_0) (a_2)) .+ (array_index (
            state_0) (b_3)))) in 
  let state_0 :=
    array_upd state_0 (d_4) (((array_index (state_0) (d_4)) .^ (array_index (
            state_0) (a_2)))) in 
  let state_0 :=
    array_upd state_0 (d_4) (uint32_rotate_left (array_index (state_0) (d_4)) (
        s_5)) in 
  state_0.
Definition chacha20_line_pure_code
  (a_2 : state_idx_t)
  (b_3 : state_idx_t)
  (d_4 : state_idx_t)
  (s_5 : uint_size)
  (m_6 : state_t)
  : code fset.fset0 [interface] (@ct state_t) :=
  lift_to_code (chacha20_line_pure a_2 b_3 d_4 s_5 m_6).

Definition state_0_loc : ChoiceEqualityLocation :=
  ((state_t ; 23%nat)).
Program Definition chacha20_line_state
  (a_2 : state_idx_t)
  (b_3 : state_idx_t)
  (d_4 : state_idx_t)
  (s_5 : uint_size)
  (m_6 : state_t) : code (CEfset ([state_0_loc])) [interface] (@ct (state_t)) :=
  (({ code  '(state_0 : state_t) ←
          (ret (m_6)) ;;
        #put state_0_loc := state_0 ;;
       '(state_0 : state_t) ←
        ( temp_8 ←
            (array_index (state_0) (a_2)) ;;
           temp_10 ←
            (array_index (state_0) (b_3)) ;;
           '(temp_12 : uint32) ←
            ((temp_8) .+ (temp_10)) ;;
          ret (array_upd state_0 (a_2) (temp_12))) ;;
      
       '(state_0 : state_t) ←
        ( temp_14 ←
            (array_index (state_0) (d_4)) ;;
           temp_16 ←
            (array_index (state_0) (a_2)) ;;
           temp_18 ←
            ((temp_14) .^ (temp_16)) ;;
          ret (array_upd state_0 (d_4) (temp_18))) ;;
      
       '(state_0 : state_t) ←
        ( temp_20 ←
            (array_index (state_0) (d_4)) ;;
           temp_22 ←
            (uint32_rotate_left (temp_20) (s_5)) ;;
          ret (array_upd state_0 (d_4) (temp_22))) ;;
      
      @ret (state_t) (state_0) } : code (CEfset (
          [state_0_loc])) [interface] _)).
Fail Next Obligation.

Program Definition chacha20_line
  (a_2 : state_idx_t)
  (b_3 : state_idx_t)
  (d_4 : state_idx_t)
  (s_5 : uint_size)
  (m_6 : state_t)
  : both (CEfset ([state_0_loc])) [interface] (state_t) :=
  letbm state_0 : state_t loc( state_0_loc ) := lift_to_both0 m_6 in
  letb state_0 : state_t :=
    array_upd state_0 (lift_to_both0 a_2) (is_pure ((array_index (state_0) (
            lift_to_both0 a_2)) .+ (array_index (state_0) (
            lift_to_both0 b_3)))) in
  letb state_0 : state_t :=
    array_upd state_0 (lift_to_both0 d_4) (is_pure ((array_index (state_0) (
            lift_to_both0 d_4)) .^ (array_index (state_0) (
            lift_to_both0 a_2)))) in
  letb state_0 : state_t :=
    array_upd state_0 (lift_to_both0 d_4) (is_pure (uint32_rotate_left (
          array_index (state_0) (lift_to_both0 d_4)) (lift_to_both0 s_5))) in
  lift_scope (H_incl := _) (lift_to_both0 state_0)
  .
Fail Next Obligation.

Definition chacha20_quarter_round_pure
  (a_24 : state_idx_t)
  (b_25 : state_idx_t)
  (c_26 : state_idx_t)
  (d_27 : state_idx_t)
  (state_28 : state_t)
  : state_t :=
  let state_29 : state_t :=
    chacha20_line (a_24) (b_25) (d_27) (usize 16) (state_28) in 
  let state_30 : state_t :=
    chacha20_line (c_26) (d_27) (b_25) (usize 12) (state_29) in 
  let state_31 : state_t :=
    chacha20_line (a_24) (b_25) (d_27) (usize 8) (state_30) in 
  chacha20_line (c_26) (d_27) (b_25) (usize 7) (state_31).
Definition chacha20_quarter_round_pure_code
  (a_24 : state_idx_t)
  (b_25 : state_idx_t)
  (c_26 : state_idx_t)
  (d_27 : state_idx_t)
  (state_28 : state_t)
  : code fset.fset0 [interface] (@ct state_t) :=
  lift_to_code (chacha20_quarter_round_pure a_24 b_25 c_26 d_27 state_28).


Program Definition chacha20_quarter_round_state
  (a_24 : state_idx_t)
  (b_25 : state_idx_t)
  (c_26 : state_idx_t)
  (d_27 : state_idx_t)
  (state_28 : state_t) : code (CEfset ([state_0_loc])) [interface] (@ct (
      state_t)) :=
  (({ code  '(state_29 : state_t) ←
        ( '(temp_33 : state_t) ←
            (chacha20_line (a_24) (b_25) (d_27) (usize 16) (state_28)) ;;
          ret (temp_33)) ;;
       '(state_30 : state_t) ←
        ( '(temp_35 : state_t) ←
            (chacha20_line (c_26) (d_27) (b_25) (usize 12) (state_29)) ;;
          ret (temp_35)) ;;
       '(state_31 : state_t) ←
        ( '(temp_37 : state_t) ←
            (chacha20_line (a_24) (b_25) (d_27) (usize 8) (state_30)) ;;
          ret (temp_37)) ;;
       '(temp_39 : state_t) ←
        (chacha20_line (c_26) (d_27) (b_25) (usize 7) (state_31)) ;;
      @ret (state_t) (temp_39) } : code (CEfset (
          [state_0_loc])) [interface] _)).
Fail Next Obligation.

Program Definition chacha20_quarter_round
  (a_24 : state_idx_t)
  (b_25 : state_idx_t)
  (c_26 : state_idx_t)
  (d_27 : state_idx_t)
  (state_28 : state_t)
  : both (CEfset ([state_0_loc])) [interface] (state_t) :=
  letb state_29 : state_t :=
    chacha20_line (lift_to_both0 a_24) (lift_to_both0 b_25) (
      lift_to_both0 d_27) (lift_to_both0 (usize 16)) (lift_to_both0 state_28) in
  letb state_30 : state_t :=
    chacha20_line (lift_to_both0 c_26) (lift_to_both0 d_27) (
      lift_to_both0 b_25) (lift_to_both0 (usize 12)) (lift_to_both0 state_29) in
  letb state_31 : state_t :=
    chacha20_line (lift_to_both0 a_24) (lift_to_both0 b_25) (
      lift_to_both0 d_27) (lift_to_both0 (usize 8)) (lift_to_both0 state_30) in
  lift_scope (H_incl := _) (chacha20_line (lift_to_both0 c_26) (
      lift_to_both0 d_27) (lift_to_both0 b_25) (lift_to_both0 (usize 7)) (
      lift_to_both0 state_31))
  .
Fail Next Obligation.

Definition chacha20_double_round_pure (state_40 : state_t) : state_t :=
  let state_41 : state_t :=
    chacha20_quarter_round (usize 0) (usize 4) (usize 8) (usize 12) (
      state_40) in 
  let state_42 : state_t :=
    chacha20_quarter_round (usize 1) (usize 5) (usize 9) (usize 13) (
      state_41) in 
  let state_43 : state_t :=
    chacha20_quarter_round (usize 2) (usize 6) (usize 10) (usize 14) (
      state_42) in 
  let state_44 : state_t :=
    chacha20_quarter_round (usize 3) (usize 7) (usize 11) (usize 15) (
      state_43) in 
  let state_45 : state_t :=
    chacha20_quarter_round (usize 0) (usize 5) (usize 10) (usize 15) (
      state_44) in 
  let state_46 : state_t :=
    chacha20_quarter_round (usize 1) (usize 6) (usize 11) (usize 12) (
      state_45) in 
  let state_47 : state_t :=
    chacha20_quarter_round (usize 2) (usize 7) (usize 8) (usize 13) (
      state_46) in 
  chacha20_quarter_round (usize 3) (usize 4) (usize 9) (usize 14) (state_47).
Definition chacha20_double_round_pure_code
  (state_40 : state_t)
  : code fset.fset0 [interface] (@ct state_t) :=
  lift_to_code (chacha20_double_round_pure state_40).


Program Definition chacha20_double_round_state
  (state_40 : state_t) : code (CEfset ([state_0_loc])) [interface] (@ct (
      state_t)) :=
  (({ code  '(state_41 : state_t) ←
        ( '(temp_49 : state_t) ←
            (chacha20_quarter_round (usize 0) (usize 4) (usize 8) (usize 12) (
                state_40)) ;;
          ret (temp_49)) ;;
       '(state_42 : state_t) ←
        ( '(temp_51 : state_t) ←
            (chacha20_quarter_round (usize 1) (usize 5) (usize 9) (usize 13) (
                state_41)) ;;
          ret (temp_51)) ;;
       '(state_43 : state_t) ←
        ( '(temp_53 : state_t) ←
            (chacha20_quarter_round (usize 2) (usize 6) (usize 10) (usize 14) (
                state_42)) ;;
          ret (temp_53)) ;;
       '(state_44 : state_t) ←
        ( '(temp_55 : state_t) ←
            (chacha20_quarter_round (usize 3) (usize 7) (usize 11) (usize 15) (
                state_43)) ;;
          ret (temp_55)) ;;
       '(state_45 : state_t) ←
        ( '(temp_57 : state_t) ←
            (chacha20_quarter_round (usize 0) (usize 5) (usize 10) (usize 15) (
                state_44)) ;;
          ret (temp_57)) ;;
       '(state_46 : state_t) ←
        ( '(temp_59 : state_t) ←
            (chacha20_quarter_round (usize 1) (usize 6) (usize 11) (usize 12) (
                state_45)) ;;
          ret (temp_59)) ;;
       '(state_47 : state_t) ←
        ( '(temp_61 : state_t) ←
            (chacha20_quarter_round (usize 2) (usize 7) (usize 8) (usize 13) (
                state_46)) ;;
          ret (temp_61)) ;;
       '(temp_63 : state_t) ←
        (chacha20_quarter_round (usize 3) (usize 4) (usize 9) (usize 14) (
            state_47)) ;;
      @ret (state_t) (temp_63) } : code (CEfset (
          [state_0_loc])) [interface] _)).
Fail Next Obligation.

Program Definition chacha20_double_round
  (state_40 : state_t)
  : both (CEfset ([state_0_loc])) [interface] (state_t) :=
  letb state_41 : state_t :=
    chacha20_quarter_round (lift_to_both0 (usize 0)) (lift_to_both0 (usize 4)) (
      lift_to_both0 (usize 8)) (lift_to_both0 (usize 12)) (
      lift_to_both0 state_40) in
  letb state_42 : state_t :=
    chacha20_quarter_round (lift_to_both0 (usize 1)) (lift_to_both0 (usize 5)) (
      lift_to_both0 (usize 9)) (lift_to_both0 (usize 13)) (
      lift_to_both0 state_41) in
  letb state_43 : state_t :=
    chacha20_quarter_round (lift_to_both0 (usize 2)) (lift_to_both0 (usize 6)) (
      lift_to_both0 (usize 10)) (lift_to_both0 (usize 14)) (
      lift_to_both0 state_42) in
  letb state_44 : state_t :=
    chacha20_quarter_round (lift_to_both0 (usize 3)) (lift_to_both0 (usize 7)) (
      lift_to_both0 (usize 11)) (lift_to_both0 (usize 15)) (
      lift_to_both0 state_43) in
  letb state_45 : state_t :=
    chacha20_quarter_round (lift_to_both0 (usize 0)) (lift_to_both0 (usize 5)) (
      lift_to_both0 (usize 10)) (lift_to_both0 (usize 15)) (
      lift_to_both0 state_44) in
  letb state_46 : state_t :=
    chacha20_quarter_round (lift_to_both0 (usize 1)) (lift_to_both0 (usize 6)) (
      lift_to_both0 (usize 11)) (lift_to_both0 (usize 12)) (
      lift_to_both0 state_45) in
  letb state_47 : state_t :=
    chacha20_quarter_round (lift_to_both0 (usize 2)) (lift_to_both0 (usize 7)) (
      lift_to_both0 (usize 8)) (lift_to_both0 (usize 13)) (
      lift_to_both0 state_46) in
  lift_scope (H_incl := _) (chacha20_quarter_round (lift_to_both0 (usize 3)) (
      lift_to_both0 (usize 4)) (lift_to_both0 (usize 9)) (lift_to_both0 (
        usize 14)) (lift_to_both0 state_47))
  .
Fail Next Obligation.

Definition chacha20_rounds_pure (state_66 : state_t) : state_t :=
  let st_64 : state_t :=
    state_66 in 
  let st_64 :=
    Hacspec_Lib_Pre.foldi (usize 0) (usize 10) st_64
      (fun i_67 st_64 =>
      let st_64 :=
        chacha20_double_round (st_64) in 
      (st_64)) in 
  st_64.
Definition chacha20_rounds_pure_code
  (state_66 : state_t)
  : code fset.fset0 [interface] (@ct state_t) :=
  lift_to_code (chacha20_rounds_pure state_66).

Definition st_64_loc : ChoiceEqualityLocation :=
  ((state_t ; 70%nat)).
Program Definition chacha20_rounds_state
  (state_66 : state_t) : code (CEfset ([state_0_loc ; st_64_loc])) [interface] (
    @ct (state_t)) :=
  (({ code  '(st_64 : state_t) ←
          (ret (state_66)) ;;
        #put st_64_loc := st_64 ;;
       '(st_64 : (state_t)) ←
        (foldi (usize 0) (usize 10) st_64 (fun i_67 st_64 =>
            ({ code  '(st_64 : state_t) ←
                  (( '(temp_69 : state_t) ←
                        (chacha20_double_round (st_64)) ;;
                      ret (temp_69))) ;;
                #put st_64_loc := st_64 ;;
              
              @ret ((state_t)) (st_64) } : code (CEfset (
                  [state_0_loc ; st_64_loc])) [interface] _))) ;;
      
      @ret (state_t) (st_64) } : code (CEfset (
          [state_0_loc ; st_64_loc])) [interface] _)).
Fail Next Obligation.

Program Definition chacha20_rounds
  (state_66 : state_t)
  : both (CEfset ([state_0_loc ; st_64_loc])) [interface] (state_t) :=
  letbm st_64 : state_t loc( st_64_loc ) := lift_to_both0 state_66 in
  letb st_64 :=
    foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
          usize 10)) st_64 (L := (CEfset (
          [state_0_loc ; st_64_loc]))) (fun i_67 st_64 =>
      letbm st_64 loc( st_64_loc ) :=
        chacha20_double_round (lift_to_both0 st_64) in
      lift_scope (H_incl := _) (lift_to_both0 st_64)
      ) in
  lift_scope (H_incl := _) (lift_to_both0 st_64)
  .
Fail Next Obligation.

Definition chacha20_core_pure (ctr_73 : uint32) (st0_74 : state_t) : state_t :=
  let state_71 : state_t :=
    st0_74 in 
  let state_71 :=
    array_upd state_71 (usize 12) (((array_index (state_71) (usize 12)) .+ (
          ctr_73))) in 
  let k_75 : state_t :=
    chacha20_rounds (state_71) in 
  ((k_75) array_add (state_71)).
Definition chacha20_core_pure_code
  (ctr_73 : uint32)
  (st0_74 : state_t)
  : code fset.fset0 [interface] (@ct state_t) :=
  lift_to_code (chacha20_core_pure ctr_73 st0_74).

Definition state_71_loc : ChoiceEqualityLocation :=
  ((state_t ; 84%nat)).
Program Definition chacha20_core_state
  (ctr_73 : uint32)
  (st0_74 : state_t) : code (CEfset (
      [state_0_loc ; st_64_loc ; state_71_loc])) [interface] (@ct (state_t)) :=
  (({ code  '(state_71 : state_t) ←
          (ret (st0_74)) ;;
        #put state_71_loc := state_71 ;;
       '(state_71 : state_t) ←
        ( temp_77 ←
            (array_index (state_71) (usize 12)) ;;
           '(temp_79 : uint32) ←
            ((temp_77) .+ (ctr_73)) ;;
          ret (array_upd state_71 (usize 12) (temp_79))) ;;
      
       '(k_75 : state_t) ←
        ( '(temp_81 : state_t) ←
            (chacha20_rounds (state_71)) ;;
          ret (temp_81)) ;;
       '(temp_83 : state_t) ←
        ((k_75) array_add (state_71)) ;;
      @ret (state_t) (temp_83) } : code (CEfset (
          [state_0_loc ; st_64_loc ; state_71_loc])) [interface] _)).
Fail Next Obligation.

Program Definition chacha20_core
  (ctr_73 : uint32)
  (st0_74 : state_t)
  : both (CEfset ([state_0_loc ; st_64_loc ; state_71_loc])) [interface] (
    state_t) :=
  letbm state_71 : state_t loc( state_71_loc ) := lift_to_both0 st0_74 in
  letb state_71 : state_t :=
    array_upd state_71 (lift_to_both0 (usize 12)) (is_pure ((array_index (
            state_71) (lift_to_both0 (usize 12))) .+ (lift_to_both0 ctr_73))) in
  letb k_75 : state_t := chacha20_rounds (lift_to_both0 state_71) in
  lift_scope (H_incl := _) ((lift_to_both0 k_75) array_add (
      lift_to_both0 state_71))
  .
Fail Next Obligation.

Definition chacha20_constants_init_pure  : constants_t :=
  let constants_85 : constants_t :=
    array_new_ (default : uint32) (4) in 
  let constants_85 :=
    array_upd constants_85 (usize 0) (secret (@repr U32 1634760805)) in 
  let constants_85 :=
    array_upd constants_85 (usize 1) (secret (@repr U32 857760878)) in 
  let constants_85 :=
    array_upd constants_85 (usize 2) (secret (@repr U32 2036477234)) in 
  let constants_85 :=
    array_upd constants_85 (usize 3) (secret (@repr U32 1797285236)) in 
  constants_85.
Definition chacha20_constants_init_pure_code
  
  : code fset.fset0 [interface] (@ct constants_t) :=
  lift_to_code (chacha20_constants_init_pure ).

Definition constants_85_loc : ChoiceEqualityLocation :=
  ((constants_t ; 97%nat)).
Program Definition chacha20_constants_init_state
   : code (CEfset ([constants_85_loc])) [interface] (@ct (constants_t)) :=
  (({ code  '(constants_85 : constants_t) ←
          ( '(temp_88 : constants_t) ←
              (array_new_ (default : uint32) (4)) ;;
            ret (temp_88)) ;;
        #put constants_85_loc := constants_85 ;;
       '(constants_85 : constants_t) ←
        ( '(temp_90 : int32) ←
            (secret (@repr U32 1634760805)) ;;
          ret (array_upd constants_85 (usize 0) (temp_90))) ;;
      
       '(constants_85 : constants_t) ←
        ( '(temp_92 : int32) ←
            (secret (@repr U32 857760878)) ;;
          ret (array_upd constants_85 (usize 1) (temp_92))) ;;
      
       '(constants_85 : constants_t) ←
        ( '(temp_94 : int32) ←
            (secret (@repr U32 2036477234)) ;;
          ret (array_upd constants_85 (usize 2) (temp_94))) ;;
      
       '(constants_85 : constants_t) ←
        ( '(temp_96 : int32) ←
            (secret (@repr U32 1797285236)) ;;
          ret (array_upd constants_85 (usize 3) (temp_96))) ;;
      
      @ret (constants_t) (constants_85) } : code (CEfset (
          [constants_85_loc])) [interface] _)).
Fail Next Obligation.

Program Definition chacha20_constants_init
  
  : both (CEfset ([constants_85_loc])) [interface] (constants_t) :=
  letbm constants_85 : constants_t loc( constants_85_loc ) :=
    array_new_ (default : uint32) (4) in
  letb constants_85 : constants_t :=
    array_upd constants_85 (lift_to_both0 (usize 0)) (is_pure (secret (
          lift_to_both0 (@repr U32 1634760805)))) in
  letb constants_85 : constants_t :=
    array_upd constants_85 (lift_to_both0 (usize 1)) (is_pure (secret (
          lift_to_both0 (@repr U32 857760878)))) in
  letb constants_85 : constants_t :=
    array_upd constants_85 (lift_to_both0 (usize 2)) (is_pure (secret (
          lift_to_both0 (@repr U32 2036477234)))) in
  letb constants_85 : constants_t :=
    array_upd constants_85 (lift_to_both0 (usize 3)) (is_pure (secret (
          lift_to_both0 (@repr U32 1797285236)))) in
  lift_scope (H_incl := _) (lift_to_both0 constants_85)
  .
Fail Next Obligation.

Definition chacha20_init_pure
  (key_100 : cha_cha_key_t)
  (iv_101 : cha_cha_iv_t)
  (ctr_102 : uint32)
  : state_t :=
  let st_98 : state_t :=
    array_new_ (default : uint32) (16) in 
  let st_98 :=
    array_update (st_98) (usize 0) (array_to_seq (chacha20_constants_init )) in 
  let st_98 :=
    array_update (st_98) (usize 4) (array_to_le_uint32s (key_100)) in 
  let st_98 :=
    array_upd st_98 (usize 12) (ctr_102) in 
  let st_98 :=
    array_update (st_98) (usize 13) (array_to_le_uint32s (iv_101)) in 
  st_98.
Definition chacha20_init_pure_code
  (key_100 : cha_cha_key_t)
  (iv_101 : cha_cha_iv_t)
  (ctr_102 : uint32)
  : code fset.fset0 [interface] (@ct state_t) :=
  lift_to_code (chacha20_init_pure key_100 iv_101 ctr_102).

Definition st_98_loc : ChoiceEqualityLocation :=
  ((state_t ; 119%nat)).
Program Definition chacha20_init_state
  (key_100 : cha_cha_key_t)
  (iv_101 : cha_cha_iv_t)
  (ctr_102 : uint32) : code (CEfset (
      [constants_85_loc ; st_98_loc])) [interface] (@ct (state_t)) :=
  (({ code  '(st_98 : state_t) ←
          ( '(temp_104 : state_t) ←
              (array_new_ (default : uint32) (16)) ;;
            ret (temp_104)) ;;
        #put st_98_loc := st_98 ;;
       '(st_98 : state_t) ←
          (( '(temp_106 : constants_t) ←
                (chacha20_constants_init ) ;;
               '(temp_108 : seq uint32) ←
                (array_to_seq (temp_106)) ;;
               '(temp_110 : state_t) ←
                (array_update (st_98) (usize 0) (temp_108)) ;;
              ret (temp_110))) ;;
        #put st_98_loc := st_98 ;;
      
       '(st_98 : state_t) ←
          (( temp_112 ←
                (array_to_le_uint32s (key_100)) ;;
               '(temp_114 : state_t) ←
                (array_update (st_98) (usize 4) (temp_112)) ;;
              ret (temp_114))) ;;
        #put st_98_loc := st_98 ;;
      
       '(st_98 : state_t) ←
        (ret (array_upd st_98 (usize 12) (ctr_102))) ;;
      
       '(st_98 : state_t) ←
          (( temp_116 ←
                (array_to_le_uint32s (iv_101)) ;;
               '(temp_118 : state_t) ←
                (array_update (st_98) (usize 13) (temp_116)) ;;
              ret (temp_118))) ;;
        #put st_98_loc := st_98 ;;
      
      @ret (state_t) (st_98) } : code (CEfset (
          [constants_85_loc ; st_98_loc])) [interface] _)).
Fail Next Obligation.

Program Definition chacha20_init
  (key_100 : cha_cha_key_t)
  (iv_101 : cha_cha_iv_t)
  (ctr_102 : uint32)
  : both (CEfset ([constants_85_loc ; st_98_loc])) [interface] (state_t) :=
  letbm st_98 : state_t loc( st_98_loc ) :=
    array_new_ (default : uint32) (16) in
  letbm st_98 loc( st_98_loc ) :=
    array_update (lift_to_both0 st_98) (lift_to_both0 (usize 0)) (
      array_to_seq (chacha20_constants_init )) in
  letbm st_98 loc( st_98_loc ) :=
    array_update (lift_to_both0 st_98) (lift_to_both0 (usize 4)) (
      array_to_le_uint32s (lift_to_both0 key_100)) in
  letb st_98 : state_t :=
    array_upd st_98 (lift_to_both0 (usize 12)) (is_pure (
        lift_to_both0 ctr_102)) in
  letbm st_98 loc( st_98_loc ) :=
    array_update (lift_to_both0 st_98) (lift_to_both0 (usize 13)) (
      array_to_le_uint32s (lift_to_both0 iv_101)) in
  lift_scope (H_incl := _) (lift_to_both0 st_98)
  .
Fail Next Obligation.

Definition chacha20_key_block_pure (state_120 : state_t) : block_t :=
  let state_121 : state_t :=
    chacha20_core (secret (@repr U32 0)) (state_120) in 
  array_from_seq (64) (array_to_le_bytes (state_121)).
Definition chacha20_key_block_pure_code
  (state_120 : state_t)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (chacha20_key_block_pure state_120).


Program Definition chacha20_key_block_state
  (state_120 : state_t) : code (CEfset (
      [state_0_loc ; st_64_loc ; state_71_loc])) [interface] (@ct (block_t)) :=
  (({ code  '(state_121 : state_t) ←
        ( '(temp_123 : int32) ←
            (secret (@repr U32 0)) ;;
           '(temp_125 : state_t) ←
            (chacha20_core (temp_123) (state_120)) ;;
          ret (temp_125)) ;;
       temp_127 ←
        (array_to_le_bytes (state_121)) ;;
       '(temp_129 : block_t) ←
        (array_from_seq (64) (temp_127)) ;;
      @ret (block_t) (temp_129) } : code (CEfset (
          [state_0_loc ; st_64_loc ; state_71_loc])) [interface] _)).
Fail Next Obligation.

Program Definition chacha20_key_block
  (state_120 : state_t)
  : both (CEfset ([state_0_loc ; st_64_loc ; state_71_loc])) [interface] (
    block_t) :=
  letb state_121 : state_t :=
    chacha20_core (secret (lift_to_both0 (@repr U32 0))) (
      lift_to_both0 state_120) in
  lift_scope (H_incl := _) (array_from_seq (64) (array_to_le_bytes (
        lift_to_both0 state_121)))
  .
Fail Next Obligation.

Definition chacha20_key_block0_pure
  (key_130 : cha_cha_key_t)
  (iv_131 : cha_cha_iv_t)
  : block_t :=
  let state_132 : state_t :=
    chacha20_init (key_130) (iv_131) (secret (@repr U32 0)) in 
  chacha20_key_block (state_132).
Definition chacha20_key_block0_pure_code
  (key_130 : cha_cha_key_t)
  (iv_131 : cha_cha_iv_t)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (chacha20_key_block0_pure key_130 iv_131).


Program Definition chacha20_key_block0_state
  (key_130 : cha_cha_key_t)
  (iv_131 : cha_cha_iv_t) : code (CEfset (
      [state_0_loc ; st_64_loc ; state_71_loc ; constants_85_loc ; st_98_loc])) [interface] (
    @ct (block_t)) :=
  (({ code  '(state_132 : state_t) ←
        ( '(temp_134 : int32) ←
            (secret (@repr U32 0)) ;;
           '(temp_136 : state_t) ←
            (chacha20_init (key_130) (iv_131) (temp_134)) ;;
          ret (temp_136)) ;;
       '(temp_138 : block_t) ←
        (chacha20_key_block (state_132)) ;;
      @ret (block_t) (temp_138) } : code (CEfset (
          [state_0_loc ; st_64_loc ; state_71_loc ; constants_85_loc ; st_98_loc])) [interface] _)).
Fail Next Obligation.

Program Definition chacha20_key_block0
  (key_130 : cha_cha_key_t)
  (iv_131 : cha_cha_iv_t)
  : both (CEfset (
      [state_0_loc ; st_64_loc ; state_71_loc ; constants_85_loc ; st_98_loc])) [interface] (
    block_t) :=
  letb state_132 : state_t :=
    chacha20_init (lift_to_both0 key_130) (lift_to_both0 iv_131) (secret (
        lift_to_both0 (@repr U32 0))) in
  lift_scope (H_incl := _) (chacha20_key_block (lift_to_both0 state_132))
  .
Fail Next Obligation.

Definition chacha20_encrypt_block_pure
  (st0_139 : state_t)
  (ctr_140 : uint32)
  (plain_141 : block_t)
  : block_t :=
  let st_142 : state_t :=
    chacha20_core (ctr_140) (st0_139) in 
  let pl_143 : state_t :=
    array_from_seq (16) (array_to_le_uint32s (plain_141)) in 
  let st_144 : state_t :=
    ((pl_143) array_xor (st_142)) in 
  array_from_seq (64) (array_to_le_bytes (st_144)).
Definition chacha20_encrypt_block_pure_code
  (st0_139 : state_t)
  (ctr_140 : uint32)
  (plain_141 : block_t)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (chacha20_encrypt_block_pure st0_139 ctr_140 plain_141).


Program Definition chacha20_encrypt_block_state
  (st0_139 : state_t)
  (ctr_140 : uint32)
  (plain_141 : block_t) : code (CEfset (
      [state_0_loc ; st_64_loc ; state_71_loc])) [interface] (@ct (block_t)) :=
  (({ code  '(st_142 : state_t) ←
        ( '(temp_146 : state_t) ←
            (chacha20_core (ctr_140) (st0_139)) ;;
          ret (temp_146)) ;;
       '(pl_143 : state_t) ←
        ( temp_148 ←
            (array_to_le_uint32s (plain_141)) ;;
           '(temp_150 : state_t) ←
            (array_from_seq (16) (temp_148)) ;;
          ret (temp_150)) ;;
       '(st_144 : state_t) ←
        ( temp_152 ←
            ((pl_143) array_xor (st_142)) ;;
          ret (temp_152)) ;;
       temp_154 ←
        (array_to_le_bytes (st_144)) ;;
       '(temp_156 : block_t) ←
        (array_from_seq (64) (temp_154)) ;;
      @ret (block_t) (temp_156) } : code (CEfset (
          [state_0_loc ; st_64_loc ; state_71_loc])) [interface] _)).
Fail Next Obligation.

Program Definition chacha20_encrypt_block
  (st0_139 : state_t)
  (ctr_140 : uint32)
  (plain_141 : block_t)
  : both (CEfset ([state_0_loc ; st_64_loc ; state_71_loc])) [interface] (
    block_t) :=
  letb st_142 : state_t :=
    chacha20_core (lift_to_both0 ctr_140) (lift_to_both0 st0_139) in
  letb pl_143 : state_t :=
    array_from_seq (16) (array_to_le_uint32s (lift_to_both0 plain_141)) in
  letb st_144 : state_t :=
    (lift_to_both0 pl_143) array_xor (lift_to_both0 st_142) in
  lift_scope (H_incl := _) (array_from_seq (64) (array_to_le_bytes (
        lift_to_both0 st_144)))
  .
Fail Next Obligation.

Definition chacha20_encrypt_last_pure
  (st0_159 : state_t)
  (ctr_160 : uint32)
  (plain_161 : byte_seq)
  : byte_seq :=
  let b_157 : block_t :=
    array_new_ (default : uint8) (64) in 
  let b_157 :=
    array_update (b_157) (usize 0) (plain_161) in 
  let b_157 :=
    chacha20_encrypt_block (st0_159) (ctr_160) (b_157) in 
  array_slice (b_157) (usize 0) (seq_len (plain_161)).
Definition chacha20_encrypt_last_pure_code
  (st0_159 : state_t)
  (ctr_160 : uint32)
  (plain_161 : byte_seq)
  : code fset.fset0 [interface] (@ct byte_seq) :=
  lift_to_code (chacha20_encrypt_last_pure st0_159 ctr_160 plain_161).

Definition b_157_loc : ChoiceEqualityLocation :=
  ((block_t ; 172%nat)).
Program Definition chacha20_encrypt_last_state
  (st0_159 : state_t)
  (ctr_160 : uint32)
  (plain_161 : byte_seq) : code (CEfset (
      [state_0_loc ; st_64_loc ; state_71_loc ; b_157_loc])) [interface] (@ct (
      byte_seq)) :=
  (({ code  '(b_157 : block_t) ←
          ( '(temp_163 : block_t) ←
              (array_new_ (default : uint8) (64)) ;;
            ret (temp_163)) ;;
        #put b_157_loc := b_157 ;;
       '(b_157 : block_t) ←
          (( '(temp_165 : block_t) ←
                (array_update (b_157) (usize 0) (plain_161)) ;;
              ret (temp_165))) ;;
        #put b_157_loc := b_157 ;;
      
       '(b_157 : block_t) ←
          (( '(temp_167 : block_t) ←
                (chacha20_encrypt_block (st0_159) (ctr_160) (b_157)) ;;
              ret (temp_167))) ;;
        #put b_157_loc := b_157 ;;
      
       '(temp_169 : uint_size) ←
        (seq_len (plain_161)) ;;
       '(temp_171 : seq uint8) ←
        (array_slice (b_157) (usize 0) (temp_169)) ;;
      @ret (seq uint8) (temp_171) } : code (CEfset (
          [state_0_loc ; st_64_loc ; state_71_loc ; b_157_loc])) [interface] _)).
Fail Next Obligation.

Program Definition chacha20_encrypt_last
  (st0_159 : state_t)
  (ctr_160 : uint32)
  (plain_161 : byte_seq)
  : both (CEfset (
      [state_0_loc ; st_64_loc ; state_71_loc ; b_157_loc])) [interface] (
    byte_seq) :=
  letbm b_157 : block_t loc( b_157_loc ) := array_new_ (default : uint8) (64) in
  letbm b_157 loc( b_157_loc ) :=
    array_update (lift_to_both0 b_157) (lift_to_both0 (usize 0)) (
      lift_to_both0 plain_161) in
  letbm b_157 loc( b_157_loc ) :=
    chacha20_encrypt_block (lift_to_both0 st0_159) (lift_to_both0 ctr_160) (
      lift_to_both0 b_157) in
  lift_scope (H_incl := _) (array_slice (lift_to_both0 b_157) (lift_to_both0 (
        usize 0)) (seq_len (lift_to_both0 plain_161)))
  .
Fail Next Obligation.

Definition chacha20_update_pure
  (st0_175 : state_t)
  (m_176 : byte_seq)
  : byte_seq :=
  let blocks_out_173 : seq uint8 :=
    seq_new_ (default : uint8) (seq_len (m_176)) in 
  let n_blocks_177 : uint_size :=
    seq_num_exact_chunks (m_176) (usize 64) in 
  let blocks_out_173 :=
    Hacspec_Lib_Pre.foldi (usize 0) (n_blocks_177) blocks_out_173
      (fun i_178 blocks_out_173 =>
      let msg_block_179 : seq uint8 :=
        seq_get_exact_chunk (m_176) (usize 64) (i_178) in 
      let b_180 : block_t :=
        chacha20_encrypt_block (st0_175) (secret (pub_u32 (i_178))) (
          array_from_seq (64) (msg_block_179)) in 
      let blocks_out_173 :=
        seq_set_exact_chunk (blocks_out_173) (usize 64) (i_178) (
          array_to_seq (b_180)) in 
      (blocks_out_173)) in 
  let last_block_181 : seq uint8 :=
    seq_get_remainder_chunk (m_176) (usize 64) in 
  let '(blocks_out_173) :=
    ((if (((seq_len (last_block_181)) !=.? (usize 0))):bool_ChoiceEquality
        then (let b_182 : seq uint8 :=
            chacha20_encrypt_last (st0_175) (secret (pub_u32 (n_blocks_177))) (
              last_block_181) in 
          let blocks_out_173 :=
            seq_set_chunk (blocks_out_173) (usize 64) (n_blocks_177) (b_182) in 
          (blocks_out_173))
        else ((blocks_out_173))) : T _) in 
  blocks_out_173.
Definition chacha20_update_pure_code
  (st0_175 : state_t)
  (m_176 : byte_seq)
  : code fset.fset0 [interface] (@ct byte_seq) :=
  lift_to_code (chacha20_update_pure st0_175 m_176).

Definition blocks_out_173_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 213%nat)).
Program Definition chacha20_update_state
  (st0_175 : state_t)
  (m_176 : byte_seq) : code (CEfset (
      [state_0_loc ; st_64_loc ; state_71_loc ; b_157_loc ; blocks_out_173_loc])) [interface] (
    @ct (byte_seq)) :=
  (({ code  '(blocks_out_173 : seq uint8) ←
          ( '(temp_184 : uint_size) ←
              (seq_len (m_176)) ;;
             temp_186 ←
              (seq_new_ (default : uint8) (temp_184)) ;;
            ret (temp_186)) ;;
        #put blocks_out_173_loc := blocks_out_173 ;;
       '(n_blocks_177 : uint_size) ←
        ( '(temp_188 : uint_size) ←
            (seq_num_exact_chunks (m_176) (usize 64)) ;;
          ret (temp_188)) ;;
       '(blocks_out_173 : (seq uint8)) ←
        (foldi (usize 0) (
              n_blocks_177) blocks_out_173 (fun i_178 blocks_out_173 =>
            ({ code  '(msg_block_179 : seq uint8) ←
                ( '(temp_190 : byte_seq) ←
                    (seq_get_exact_chunk (m_176) (usize 64) (i_178)) ;;
                  ret (temp_190)) ;;
               '(b_180 : block_t) ←
                ( '(temp_192 : int32) ←
                    (secret (pub_u32 (i_178))) ;;
                   '(temp_194 : block_t) ←
                    (array_from_seq (64) (msg_block_179)) ;;
                   '(temp_196 : block_t) ←
                    (chacha20_encrypt_block (st0_175) (temp_192) (temp_194)) ;;
                  ret (temp_196)) ;;
               '(blocks_out_173 : seq uint8) ←
                  (( '(temp_198 : seq uint8) ←
                        (array_to_seq (b_180)) ;;
                       '(temp_200 : seq uint8) ←
                        (seq_set_exact_chunk (blocks_out_173) (usize 64) (
                            i_178) (temp_198)) ;;
                      ret (temp_200))) ;;
                #put blocks_out_173_loc := blocks_out_173 ;;
              
              @ret ((seq uint8)) (blocks_out_173) } : code (CEfset (
                  [state_0_loc ; st_64_loc ; state_71_loc ; blocks_out_173_loc])) [interface] _))) ;;
      
       '(last_block_181 : seq uint8) ←
        ( '(temp_202 : byte_seq) ←
            (seq_get_remainder_chunk (m_176) (usize 64)) ;;
          ret (temp_202)) ;;
       '(temp_204 : uint_size) ←
        (seq_len (last_block_181)) ;;
       '(temp_206 : bool_ChoiceEquality) ←
        ((temp_204) !=.? (usize 0)) ;;
       '(blocks_out_173 : (seq uint8)) ←
        (if temp_206:bool_ChoiceEquality
          then (({ code  '(b_182 : seq uint8) ←
                ( '(temp_208 : int32) ←
                    (secret (pub_u32 (n_blocks_177))) ;;
                   '(temp_210 : byte_seq) ←
                    (chacha20_encrypt_last (st0_175) (temp_208) (
                        last_block_181)) ;;
                  ret (temp_210)) ;;
               '(blocks_out_173 : seq uint8) ←
                  (( '(temp_212 : seq uint8) ←
                        (seq_set_chunk (blocks_out_173) (usize 64) (
                            n_blocks_177) (b_182)) ;;
                      ret (temp_212))) ;;
                #put blocks_out_173_loc := blocks_out_173 ;;
              
              @ret ((seq uint8)) (blocks_out_173) } : code (CEfset (
                  [state_0_loc ; st_64_loc ; state_71_loc ; b_157_loc ; blocks_out_173_loc])) [interface] _))
          else @ret ((seq uint8)) (blocks_out_173)) ;;
      
      @ret (seq uint8) (blocks_out_173) } : code (CEfset (
          [state_0_loc ; st_64_loc ; state_71_loc ; b_157_loc ; blocks_out_173_loc])) [interface] _)).
Fail Next Obligation.

Program Definition chacha20_update
  (st0_175 : state_t)
  (m_176 : byte_seq)
  : both (CEfset (
      [state_0_loc ; st_64_loc ; state_71_loc ; b_157_loc ; blocks_out_173_loc])) [interface] (
    byte_seq) :=
  letbm blocks_out_173 : seq uint8 loc( blocks_out_173_loc ) :=
    seq_new_ (default : uint8) (seq_len (lift_to_both0 m_176)) in
  letb n_blocks_177 : uint_size :=
    seq_num_exact_chunks (lift_to_both0 m_176) (lift_to_both0 (usize 64)) in
  letb blocks_out_173 :=
    foldi_both' (lift_to_both0 (usize 0)) (
        lift_to_both0 n_blocks_177) blocks_out_173 (L := (CEfset (
          [state_0_loc ; st_64_loc ; state_71_loc ; b_157_loc ; blocks_out_173_loc]))) (fun i_178 blocks_out_173 =>
      letb msg_block_179 : seq uint8 :=
        seq_get_exact_chunk (lift_to_both0 m_176) (lift_to_both0 (usize 64)) (
          lift_to_both0 i_178) in
      letb b_180 : block_t :=
        chacha20_encrypt_block (lift_to_both0 st0_175) (secret (pub_u32 (
              is_pure (lift_to_both0 i_178)))) (array_from_seq (64) (
            lift_to_both0 msg_block_179)) in
      letbm blocks_out_173 loc( blocks_out_173_loc ) :=
        seq_set_exact_chunk (lift_to_both0 blocks_out_173) (lift_to_both0 (
            usize 64)) (lift_to_both0 i_178) (
          array_to_seq (lift_to_both0 b_180)) in
      lift_scope (H_incl := _) (lift_to_both0 blocks_out_173)
      ) in
  letb last_block_181 : seq uint8 :=
    seq_get_remainder_chunk (lift_to_both0 m_176) (lift_to_both0 (usize 64)) in
  letb 'blocks_out_173 :=
    if (seq_len (lift_to_both0 last_block_181)) !=.? (lift_to_both0 (
        usize 0)) :bool_ChoiceEquality
    then lift_scope (L1 := CEfset (
      [state_0_loc ; st_64_loc ; state_71_loc ; b_157_loc ; blocks_out_173_loc])) (L2 := CEfset (
      [state_0_loc ; st_64_loc ; state_71_loc ; b_157_loc ; blocks_out_173_loc])) (H_incl := _) (
      letb b_182 : seq uint8 :=
        chacha20_encrypt_last (lift_to_both0 st0_175) (secret (pub_u32 (
              is_pure (lift_to_both0 n_blocks_177)))) (
          lift_to_both0 last_block_181) in
      letbm blocks_out_173 loc( blocks_out_173_loc ) :=
        seq_set_chunk (lift_to_both0 blocks_out_173) (lift_to_both0 (
            usize 64)) (lift_to_both0 n_blocks_177) (lift_to_both0 b_182) in
      lift_scope (H_incl := _) (lift_to_both0 blocks_out_173)
      )
    else lift_scope (H_incl := _) (lift_to_both0 blocks_out_173)
     in
  lift_scope (H_incl := _) (lift_to_both0 blocks_out_173)
  .
Fail Next Obligation.

Definition chacha20_pure
  (key_214 : cha_cha_key_t)
  (iv_215 : cha_cha_iv_t)
  (ctr_216 : int32)
  (m_217 : byte_seq)
  : byte_seq :=
  let state_218 : state_t :=
    chacha20_init (key_214) (iv_215) (secret (ctr_216)) in 
  chacha20_update (state_218) (m_217).
Definition chacha20_pure_code
  (key_214 : cha_cha_key_t)
  (iv_215 : cha_cha_iv_t)
  (ctr_216 : int32)
  (m_217 : byte_seq)
  : code fset.fset0 [interface] (@ct byte_seq) :=
  lift_to_code (chacha20_pure key_214 iv_215 ctr_216 m_217).


Program Definition chacha20_state
  (key_214 : cha_cha_key_t)
  (iv_215 : cha_cha_iv_t)
  (ctr_216 : int32)
  (m_217 : byte_seq) : code (CEfset (
      [state_0_loc ; st_64_loc ; state_71_loc ; constants_85_loc ; st_98_loc ; b_157_loc ; blocks_out_173_loc])) [interface] (
    @ct (byte_seq)) :=
  (({ code  '(state_218 : state_t) ←
        ( '(temp_220 : int32) ←
            (secret (ctr_216)) ;;
           '(temp_222 : state_t) ←
            (chacha20_init (key_214) (iv_215) (temp_220)) ;;
          ret (temp_222)) ;;
       '(temp_224 : byte_seq) ←
        (chacha20_update (state_218) (m_217)) ;;
      @ret (byte_seq) (temp_224) } : code (CEfset (
          [state_0_loc ; st_64_loc ; state_71_loc ; constants_85_loc ; st_98_loc ; b_157_loc ; blocks_out_173_loc])) [interface] _)).
Fail Next Obligation.

Program Definition chacha20
  (key_214 : cha_cha_key_t)
  (iv_215 : cha_cha_iv_t)
  (ctr_216 : int32)
  (m_217 : byte_seq)
  : both (CEfset (
      [state_0_loc ; st_64_loc ; state_71_loc ; constants_85_loc ; st_98_loc ; b_157_loc ; blocks_out_173_loc])) [interface] (
    byte_seq) :=
  letb state_218 : state_t :=
    chacha20_init (lift_to_both0 key_214) (lift_to_both0 iv_215) (secret (
        lift_to_both0 ctr_216)) in
  lift_scope (H_incl := _) (chacha20_update (lift_to_both0 state_218) (
      lift_to_both0 m_217))
  .
Fail Next Obligation.

