(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp.word Require Import ssrZ word.
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
  (a_941 : state_idx_t)
  (b_942 : state_idx_t)
  (d_943 : state_idx_t)
  (s_944 : uint_size)
  (m_945 : state_t)
  : state_t :=
  let state_939 : state_t :=
    m_945 in 
  let state_939 :=
    array_upd state_939 (a_941) (((array_index (state_939) (a_941)) .+ (
          array_index (state_939) (b_942)))) in 
  let state_939 :=
    array_upd state_939 (d_943) (((array_index (state_939) (d_943)) .^ (
          array_index (state_939) (a_941)))) in 
  let state_939 :=
    array_upd state_939 (d_943) (uint32_rotate_left (array_index (state_939) (
          d_943)) (s_944)) in 
  state_939.
Definition chacha20_line_pure_code
  (a_941 : state_idx_t)
  (b_942 : state_idx_t)
  (d_943 : state_idx_t)
  (s_944 : uint_size)
  (m_945 : state_t)
  : code fset.fset0 [interface] (@ct (state_t)) :=
  lift_to_code (chacha20_line_pure a_941 b_942 d_943 s_944 m_945).

Definition state_939_loc : ChoiceEqualityLocation :=
  ((state_t ; 962%nat)).
Notation "'chacha20_line_state_inp'" := (
  state_idx_t '× state_idx_t '× state_idx_t '× uint_size '× state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_line_state_out'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_LINE_STATE : nat :=
  (963).
Program Definition chacha20_line_state
   : package (CEfset ([state_939_loc])) [interface] [interface
  #val #[ CHACHA20_LINE_STATE ] : chacha20_line_state_inp → chacha20_line_state_out
  ] :=
  (
    [package #def #[ CHACHA20_LINE_STATE ] (temp_inp : chacha20_line_state_inp) : chacha20_line_state_out { 
    let '(
      a_941 , b_942 , d_943 , s_944 , m_945) := temp_inp : state_idx_t '× state_idx_t '× state_idx_t '× uint_size '× state_t in
    ({ code  '(state_939 : state_t) ←
          (ret (m_945)) ;;
        #put state_939_loc := state_939 ;;
       '(state_939 : state_t) ←
        ( temp_947 ←
            (array_index (state_939) (a_941)) ;;
           temp_949 ←
            (array_index (state_939) (b_942)) ;;
           '(temp_951 : uint32) ←
            ((temp_947) .+ (temp_949)) ;;
          ret (array_upd state_939 (a_941) (temp_951))) ;;
      
       '(state_939 : state_t) ←
        ( temp_953 ←
            (array_index (state_939) (d_943)) ;;
           temp_955 ←
            (array_index (state_939) (a_941)) ;;
           temp_957 ←
            ((temp_953) .^ (temp_955)) ;;
          ret (array_upd state_939 (d_943) (temp_957))) ;;
      
       '(state_939 : state_t) ←
        ( temp_959 ←
            (array_index (state_939) (d_943)) ;;
           temp_961 ←
            (uint32_rotate_left (temp_959) (s_944)) ;;
          ret (array_upd state_939 (d_943) (temp_961))) ;;
      
      @ret (state_t) (state_939) } : code (CEfset (
          [state_939_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_chacha20_line_state : package _ _ _ :=
  (chacha20_line_state).
Fail Next Obligation.

Notation "'chacha20_line_inp'" :=(
  state_idx_t '× state_idx_t '× state_idx_t '× uint_size '× state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_line_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_LINE : nat :=
  (964).
Program Definition chacha20_line
  (a_941 : state_idx_t)
  (b_942 : state_idx_t)
  (d_943 : state_idx_t)
  (s_944 : uint_size)
  (m_945 : state_t)
  :both (CEfset ([state_939_loc])) [interface] (state_t) :=
  letbm state_939 : state_t loc( state_939_loc ) := lift_to_both0 m_945 in
  letb state_939 : state_t :=
    array_upd state_939 (lift_to_both0 a_941) (is_pure ((array_index (
            state_939) (lift_to_both0 a_941)) .+ (array_index (state_939) (
            lift_to_both0 b_942)))) in
  letb state_939 : state_t :=
    array_upd state_939 (lift_to_both0 d_943) (is_pure ((array_index (
            state_939) (lift_to_both0 d_943)) .^ (array_index (state_939) (
            lift_to_both0 a_941)))) in
  letb state_939 : state_t :=
    array_upd state_939 (lift_to_both0 d_943) (is_pure (uint32_rotate_left (
          array_index (state_939) (lift_to_both0 d_943)) (
          lift_to_both0 s_944))) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 state_939)
  .
Fail Next Obligation.

Definition chacha20_quarter_round_pure
  (a_965 : state_idx_t)
  (b_966 : state_idx_t)
  (c_967 : state_idx_t)
  (d_968 : state_idx_t)
  (state_969 : state_t)
  : state_t :=
  let state_970 : state_t :=
    chacha20_line (a_965) (b_966) (d_968) (usize 16) (state_969) in 
  let state_971 : state_t :=
    chacha20_line (c_967) (d_968) (b_966) (usize 12) (state_970) in 
  let state_972 : state_t :=
    chacha20_line (a_965) (b_966) (d_968) (usize 8) (state_971) in 
  chacha20_line (c_967) (d_968) (b_966) (usize 7) (state_972).
Definition chacha20_quarter_round_pure_code
  (a_965 : state_idx_t)
  (b_966 : state_idx_t)
  (c_967 : state_idx_t)
  (d_968 : state_idx_t)
  (state_969 : state_t)
  : code fset.fset0 [interface] (@ct (state_t)) :=
  lift_to_code (chacha20_quarter_round_pure a_965 b_966 c_967 d_968 state_969).


Notation "'chacha20_quarter_round_state_inp'" := (
  state_idx_t '× state_idx_t '× state_idx_t '× state_idx_t '× state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_quarter_round_state_out'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_QUARTER_ROUND_STATE : nat :=
  (981).
Program Definition chacha20_quarter_round_state
   : package (CEfset ([])) [interface
  #val #[ CHACHA20_LINE_STATE ] : chacha20_line_state_inp → chacha20_line_state_out
  ] [interface
  #val #[ CHACHA20_QUARTER_ROUND_STATE ] : chacha20_quarter_round_state_inp → chacha20_quarter_round_state_out
  ] :=
  (
    [package #def #[ CHACHA20_QUARTER_ROUND_STATE ] (temp_inp : chacha20_quarter_round_state_inp) : chacha20_quarter_round_state_out { 
    let '(
      a_965 , b_966 , c_967 , d_968 , state_969) := temp_inp : state_idx_t '× state_idx_t '× state_idx_t '× state_idx_t '× state_t in
    #import {sig #[ CHACHA20_LINE_STATE ] : chacha20_line_state_inp → chacha20_line_state_out } as chacha20_line_state ;;
    let chacha20_line_state := fun x_0 x_1 x_2 x_3 x_4 => chacha20_line_state (
      x_0,x_1,x_2,x_3,x_4) in
    ({ code  '(state_970 : state_t) ←
        ( temp_974 ←
            (chacha20_line (a_965) (b_966) (d_968) (usize 16) (state_969)) ;;
          ret (temp_974)) ;;
       '(state_971 : state_t) ←
        ( temp_976 ←
            (chacha20_line (c_967) (d_968) (b_966) (usize 12) (state_970)) ;;
          ret (temp_976)) ;;
       '(state_972 : state_t) ←
        ( temp_978 ←
            (chacha20_line (a_965) (b_966) (d_968) (usize 8) (state_971)) ;;
          ret (temp_978)) ;;
       temp_980 ←
        (chacha20_line (c_967) (d_968) (b_966) (usize 7) (state_972)) ;;
      @ret (state_t) (temp_980) } : code (CEfset ([])) [interface
      #val #[ CHACHA20_LINE_STATE ] : chacha20_line_state_inp → chacha20_line_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_chacha20_quarter_round_state : package _ _ _ :=
  (seq_link chacha20_quarter_round_state link_rest(
      package_chacha20_line_state)).
Fail Next Obligation.

Notation "'chacha20_quarter_round_inp'" :=(
  state_idx_t '× state_idx_t '× state_idx_t '× state_idx_t '× state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_quarter_round_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_QUARTER_ROUND : nat :=
  (982).
Program Definition chacha20_quarter_round
  (a_965 : state_idx_t)
  (b_966 : state_idx_t)
  (c_967 : state_idx_t)
  (d_968 : state_idx_t)
  (state_969 : state_t)
  :both (CEfset ([])) [interface
  #val #[ CHACHA20_LINE ] : chacha20_line_inp → chacha20_line_out ] (
    state_t) :=
  #import {sig #[ CHACHA20_LINE ] : chacha20_line_inp → chacha20_line_out } as chacha20_line ;;
  let chacha20_line := fun x_0 x_1 x_2 x_3 x_4 => chacha20_line (
    x_0,x_1,x_2,x_3,x_4) in
  letb state_970 : state_t :=
    chacha20_line (lift_to_both0 a_965) (lift_to_both0 b_966) (
      lift_to_both0 d_968) (lift_to_both0 (usize 16)) (
      lift_to_both0 state_969) in
  letb state_971 : state_t :=
    chacha20_line (lift_to_both0 c_967) (lift_to_both0 d_968) (
      lift_to_both0 b_966) (lift_to_both0 (usize 12)) (
      lift_to_both0 state_970) in
  letb state_972 : state_t :=
    chacha20_line (lift_to_both0 a_965) (lift_to_both0 b_966) (
      lift_to_both0 d_968) (lift_to_both0 (usize 8)) (
      lift_to_both0 state_971) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (chacha20_line (
      lift_to_both0 c_967) (lift_to_both0 d_968) (lift_to_both0 b_966) (
      lift_to_both0 (usize 7)) (lift_to_both0 state_972))
  .
Fail Next Obligation.

Definition chacha20_double_round_pure (state_983 : state_t) : state_t :=
  let state_984 : state_t :=
    chacha20_quarter_round (usize 0) (usize 4) (usize 8) (usize 12) (
      state_983) in 
  let state_985 : state_t :=
    chacha20_quarter_round (usize 1) (usize 5) (usize 9) (usize 13) (
      state_984) in 
  let state_986 : state_t :=
    chacha20_quarter_round (usize 2) (usize 6) (usize 10) (usize 14) (
      state_985) in 
  let state_987 : state_t :=
    chacha20_quarter_round (usize 3) (usize 7) (usize 11) (usize 15) (
      state_986) in 
  let state_988 : state_t :=
    chacha20_quarter_round (usize 0) (usize 5) (usize 10) (usize 15) (
      state_987) in 
  let state_989 : state_t :=
    chacha20_quarter_round (usize 1) (usize 6) (usize 11) (usize 12) (
      state_988) in 
  let state_990 : state_t :=
    chacha20_quarter_round (usize 2) (usize 7) (usize 8) (usize 13) (
      state_989) in 
  chacha20_quarter_round (usize 3) (usize 4) (usize 9) (usize 14) (state_990).
Definition chacha20_double_round_pure_code
  (state_983 : state_t)
  : code fset.fset0 [interface] (@ct (state_t)) :=
  lift_to_code (chacha20_double_round_pure state_983).


Notation "'chacha20_double_round_state_inp'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_double_round_state_out'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_DOUBLE_ROUND_STATE : nat :=
  (1007).
Program Definition chacha20_double_round_state
   : package (CEfset ([])) [interface
  #val #[ CHACHA20_QUARTER_ROUND_STATE ] : chacha20_quarter_round_state_inp → chacha20_quarter_round_state_out
  ] [interface
  #val #[ CHACHA20_DOUBLE_ROUND_STATE ] : chacha20_double_round_state_inp → chacha20_double_round_state_out
  ] :=
  (
    [package #def #[ CHACHA20_DOUBLE_ROUND_STATE ] (temp_inp : chacha20_double_round_state_inp) : chacha20_double_round_state_out { 
    let '(state_983) := temp_inp : state_t in
    #import {sig #[ CHACHA20_QUARTER_ROUND_STATE ] : chacha20_quarter_round_state_inp → chacha20_quarter_round_state_out } as chacha20_quarter_round_state ;;
    let chacha20_quarter_round_state := fun x_0 x_1 x_2 x_3 x_4 => chacha20_quarter_round_state (
      x_0,x_1,x_2,x_3,x_4) in
    ({ code  '(state_984 : state_t) ←
        ( temp_992 ←
            (chacha20_quarter_round (usize 0) (usize 4) (usize 8) (usize 12) (
                state_983)) ;;
          ret (temp_992)) ;;
       '(state_985 : state_t) ←
        ( temp_994 ←
            (chacha20_quarter_round (usize 1) (usize 5) (usize 9) (usize 13) (
                state_984)) ;;
          ret (temp_994)) ;;
       '(state_986 : state_t) ←
        ( temp_996 ←
            (chacha20_quarter_round (usize 2) (usize 6) (usize 10) (usize 14) (
                state_985)) ;;
          ret (temp_996)) ;;
       '(state_987 : state_t) ←
        ( temp_998 ←
            (chacha20_quarter_round (usize 3) (usize 7) (usize 11) (usize 15) (
                state_986)) ;;
          ret (temp_998)) ;;
       '(state_988 : state_t) ←
        ( temp_1000 ←
            (chacha20_quarter_round (usize 0) (usize 5) (usize 10) (usize 15) (
                state_987)) ;;
          ret (temp_1000)) ;;
       '(state_989 : state_t) ←
        ( temp_1002 ←
            (chacha20_quarter_round (usize 1) (usize 6) (usize 11) (usize 12) (
                state_988)) ;;
          ret (temp_1002)) ;;
       '(state_990 : state_t) ←
        ( temp_1004 ←
            (chacha20_quarter_round (usize 2) (usize 7) (usize 8) (usize 13) (
                state_989)) ;;
          ret (temp_1004)) ;;
       temp_1006 ←
        (chacha20_quarter_round (usize 3) (usize 4) (usize 9) (usize 14) (
            state_990)) ;;
      @ret (state_t) (temp_1006) } : code (CEfset ([])) [interface
      #val #[ CHACHA20_QUARTER_ROUND_STATE ] : chacha20_quarter_round_state_inp → chacha20_quarter_round_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_chacha20_double_round_state : package _ _ _ :=
  (seq_link chacha20_double_round_state link_rest(
      package_chacha20_quarter_round_state)).
Fail Next Obligation.

Notation "'chacha20_double_round_inp'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_double_round_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_DOUBLE_ROUND : nat :=
  (1008).
Program Definition chacha20_double_round
  (state_983 : state_t)
  :both (CEfset ([])) [interface
  #val #[ CHACHA20_QUARTER_ROUND ] : chacha20_quarter_round_inp → chacha20_quarter_round_out
  ] (state_t) :=
  #import {sig #[ CHACHA20_QUARTER_ROUND ] : chacha20_quarter_round_inp → chacha20_quarter_round_out } as chacha20_quarter_round ;;
  let chacha20_quarter_round := fun x_0 x_1 x_2 x_3 x_4 => chacha20_quarter_round (
    x_0,x_1,x_2,x_3,x_4) in
  letb state_984 : state_t :=
    chacha20_quarter_round (lift_to_both0 (usize 0)) (lift_to_both0 (usize 4)) (
      lift_to_both0 (usize 8)) (lift_to_both0 (usize 12)) (
      lift_to_both0 state_983) in
  letb state_985 : state_t :=
    chacha20_quarter_round (lift_to_both0 (usize 1)) (lift_to_both0 (usize 5)) (
      lift_to_both0 (usize 9)) (lift_to_both0 (usize 13)) (
      lift_to_both0 state_984) in
  letb state_986 : state_t :=
    chacha20_quarter_round (lift_to_both0 (usize 2)) (lift_to_both0 (usize 6)) (
      lift_to_both0 (usize 10)) (lift_to_both0 (usize 14)) (
      lift_to_both0 state_985) in
  letb state_987 : state_t :=
    chacha20_quarter_round (lift_to_both0 (usize 3)) (lift_to_both0 (usize 7)) (
      lift_to_both0 (usize 11)) (lift_to_both0 (usize 15)) (
      lift_to_both0 state_986) in
  letb state_988 : state_t :=
    chacha20_quarter_round (lift_to_both0 (usize 0)) (lift_to_both0 (usize 5)) (
      lift_to_both0 (usize 10)) (lift_to_both0 (usize 15)) (
      lift_to_both0 state_987) in
  letb state_989 : state_t :=
    chacha20_quarter_round (lift_to_both0 (usize 1)) (lift_to_both0 (usize 6)) (
      lift_to_both0 (usize 11)) (lift_to_both0 (usize 12)) (
      lift_to_both0 state_988) in
  letb state_990 : state_t :=
    chacha20_quarter_round (lift_to_both0 (usize 2)) (lift_to_both0 (usize 7)) (
      lift_to_both0 (usize 8)) (lift_to_both0 (usize 13)) (
      lift_to_both0 state_989) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (chacha20_quarter_round (
      lift_to_both0 (usize 3)) (lift_to_both0 (usize 4)) (lift_to_both0 (
        usize 9)) (lift_to_both0 (usize 14)) (lift_to_both0 state_990))
  .
Fail Next Obligation.

Definition chacha20_rounds_pure (state_1011 : state_t) : state_t :=
  let st_1009 : state_t :=
    state_1011 in 
  let st_1009 :=
    Hacspec_Lib_Pre.foldi (usize 0) (usize 10) st_1009
      (fun i_1012 st_1009 =>
      let st_1009 :=
        chacha20_double_round (st_1009) in 
      (st_1009)) in 
  st_1009.
Definition chacha20_rounds_pure_code
  (state_1011 : state_t)
  : code fset.fset0 [interface] (@ct (state_t)) :=
  lift_to_code (chacha20_rounds_pure state_1011).

Definition st_1009_loc : ChoiceEqualityLocation :=
  ((state_t ; 1015%nat)).
Notation "'chacha20_rounds_state_inp'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_rounds_state_out'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_ROUNDS_STATE : nat :=
  (1016).
Program Definition chacha20_rounds_state
   : package (CEfset ([st_1009_loc])) [interface
  #val #[ CHACHA20_DOUBLE_ROUND_STATE ] : chacha20_double_round_state_inp → chacha20_double_round_state_out
  ] [interface
  #val #[ CHACHA20_ROUNDS_STATE ] : chacha20_rounds_state_inp → chacha20_rounds_state_out
  ] :=
  (
    [package #def #[ CHACHA20_ROUNDS_STATE ] (temp_inp : chacha20_rounds_state_inp) : chacha20_rounds_state_out { 
    let '(state_1011) := temp_inp : state_t in
    #import {sig #[ CHACHA20_DOUBLE_ROUND_STATE ] : chacha20_double_round_state_inp → chacha20_double_round_state_out } as chacha20_double_round_state ;;
    let chacha20_double_round_state := fun x_0 => chacha20_double_round_state (
      x_0) in
    ({ code  '(st_1009 : state_t) ←
          (ret (state_1011)) ;;
        #put st_1009_loc := st_1009 ;;
       '(st_1009 : (state_t)) ←
        (foldi' (usize 0) (usize 10) st_1009 (L2 := CEfset ([st_1009_loc])) (
              I2 := [interface
              #val #[ CHACHA20_DOUBLE_ROUND_STATE ] : chacha20_double_round_state_inp → chacha20_double_round_state_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_1012 st_1009 =>
            ({ code  '(st_1009 : state_t) ←
                  (( temp_1014 ←
                        (chacha20_double_round (st_1009)) ;;
                      ret (temp_1014))) ;;
                #put st_1009_loc := st_1009 ;;
              
              @ret ((state_t)) (st_1009) } : code (CEfset (
                  [st_1009_loc])) [interface] _))) ;;
      
      @ret (state_t) (st_1009) } : code (CEfset ([st_1009_loc])) [interface
      #val #[ CHACHA20_DOUBLE_ROUND_STATE ] : chacha20_double_round_state_inp → chacha20_double_round_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_chacha20_rounds_state : package _ _ _ :=
  (seq_link chacha20_rounds_state link_rest(
      package_chacha20_double_round_state)).
Fail Next Obligation.

Notation "'chacha20_rounds_inp'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_rounds_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_ROUNDS : nat :=
  (1017).
Program Definition chacha20_rounds
  (state_1011 : state_t)
  :both (CEfset ([st_1009_loc])) [interface
  #val #[ CHACHA20_DOUBLE_ROUND ] : chacha20_double_round_inp → chacha20_double_round_out
  ] (state_t) :=
  #import {sig #[ CHACHA20_DOUBLE_ROUND ] : chacha20_double_round_inp → chacha20_double_round_out } as chacha20_double_round ;;
  let chacha20_double_round := fun x_0 => chacha20_double_round (x_0) in
  letbm st_1009 : state_t loc( st_1009_loc ) := lift_to_both0 state_1011 in
  letb st_1009 :=
    foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
          usize 10)) st_1009 (L := (CEfset ([st_1009_loc]))) (I := ([interface
        #val #[ CHACHA20_DOUBLE_ROUND ] : chacha20_double_round_inp → chacha20_double_round_out
        ])) (fun i_1012 st_1009 =>
      letbm st_1009 loc( st_1009_loc ) :=
        chacha20_double_round (lift_to_both0 st_1009) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 st_1009)
      ) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 st_1009)
  .
Fail Next Obligation.

Definition chacha20_core_pure
  (ctr_1020 : uint32)
  (st0_1021 : state_t)
  : state_t :=
  let state_1018 : state_t :=
    st0_1021 in 
  let state_1018 :=
    array_upd state_1018 (usize 12) (((array_index (state_1018) (usize 12)) .+ (
          ctr_1020))) in 
  let k_1022 : state_t :=
    chacha20_rounds (state_1018) in 
  ((k_1022) array_add (state_1018)).
Definition chacha20_core_pure_code
  (ctr_1020 : uint32)
  (st0_1021 : state_t)
  : code fset.fset0 [interface] (@ct (state_t)) :=
  lift_to_code (chacha20_core_pure ctr_1020 st0_1021).

Definition state_1018_loc : ChoiceEqualityLocation :=
  ((state_t ; 1031%nat)).
Notation "'chacha20_core_state_inp'" := (
  uint32 '× state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_core_state_out'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_CORE_STATE : nat :=
  (1032).
Program Definition chacha20_core_state
   : package (CEfset ([state_1018_loc])) [interface
  #val #[ CHACHA20_ROUNDS_STATE ] : chacha20_rounds_state_inp → chacha20_rounds_state_out
  ] [interface
  #val #[ CHACHA20_CORE_STATE ] : chacha20_core_state_inp → chacha20_core_state_out
  ] :=
  (
    [package #def #[ CHACHA20_CORE_STATE ] (temp_inp : chacha20_core_state_inp) : chacha20_core_state_out { 
    let '(ctr_1020 , st0_1021) := temp_inp : uint32 '× state_t in
    #import {sig #[ CHACHA20_ROUNDS_STATE ] : chacha20_rounds_state_inp → chacha20_rounds_state_out } as chacha20_rounds_state ;;
    let chacha20_rounds_state := fun x_0 => chacha20_rounds_state (x_0) in
    ({ code  '(state_1018 : state_t) ←
          (ret (st0_1021)) ;;
        #put state_1018_loc := state_1018 ;;
       '(state_1018 : state_t) ←
        ( temp_1024 ←
            (array_index (state_1018) (usize 12)) ;;
           '(temp_1026 : uint32) ←
            ((temp_1024) .+ (ctr_1020)) ;;
          ret (array_upd state_1018 (usize 12) (temp_1026))) ;;
      
       '(k_1022 : state_t) ←
        ( temp_1028 ←
            (chacha20_rounds (state_1018)) ;;
          ret (temp_1028)) ;;
       '(temp_1030 : state_t) ←
        ((k_1022) array_add (state_1018)) ;;
      @ret (state_t) (temp_1030) } : code (CEfset ([state_1018_loc])) [interface
      #val #[ CHACHA20_ROUNDS_STATE ] : chacha20_rounds_state_inp → chacha20_rounds_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_chacha20_core_state : package _ _ _ :=
  (seq_link chacha20_core_state link_rest(package_chacha20_rounds_state)).
Fail Next Obligation.

Notation "'chacha20_core_inp'" :=(
  uint32 '× state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_core_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_CORE : nat :=
  (1033).
Program Definition chacha20_core
  (ctr_1020 : uint32)
  (st0_1021 : state_t)
  :both (CEfset ([state_1018_loc])) [interface
  #val #[ CHACHA20_ROUNDS ] : chacha20_rounds_inp → chacha20_rounds_out ] (
    state_t) :=
  #import {sig #[ CHACHA20_ROUNDS ] : chacha20_rounds_inp → chacha20_rounds_out } as chacha20_rounds ;;
  let chacha20_rounds := fun x_0 => chacha20_rounds (x_0) in
  letbm state_1018 : state_t loc( state_1018_loc ) := lift_to_both0 st0_1021 in
  letb state_1018 : state_t :=
    array_upd state_1018 (lift_to_both0 (usize 12)) (is_pure ((array_index (
            state_1018) (lift_to_both0 (usize 12))) .+ (
          lift_to_both0 ctr_1020))) in
  letb k_1022 : state_t := chacha20_rounds (lift_to_both0 state_1018) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
      lift_to_both0 k_1022) array_add (lift_to_both0 state_1018))
  .
Fail Next Obligation.

Definition chacha20_constants_init_pure  : constants_t :=
  let constants_1034 : constants_t :=
    array_new_ (default : uint32) (4) in 
  let constants_1034 :=
    array_upd constants_1034 (usize 0) (secret (@repr U32 1634760805)) in 
  let constants_1034 :=
    array_upd constants_1034 (usize 1) (secret (@repr U32 857760878)) in 
  let constants_1034 :=
    array_upd constants_1034 (usize 2) (secret (@repr U32 2036477234)) in 
  let constants_1034 :=
    array_upd constants_1034 (usize 3) (secret (@repr U32 1797285236)) in 
  constants_1034.
Definition chacha20_constants_init_pure_code
  
  : code fset.fset0 [interface] (@ct (constants_t)) :=
  lift_to_code (chacha20_constants_init_pure ).

Definition constants_1034_loc : ChoiceEqualityLocation :=
  ((constants_t ; 1046%nat)).
Notation "'chacha20_constants_init_state_inp'" := (
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_constants_init_state_out'" := (
  constants_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_CONSTANTS_INIT_STATE : nat :=
  (1047).
Program Definition chacha20_constants_init_state
   : package (CEfset ([constants_1034_loc])) [interface] [interface
  #val #[ CHACHA20_CONSTANTS_INIT_STATE ] : chacha20_constants_init_state_inp → chacha20_constants_init_state_out
  ] :=
  (
    [package #def #[ CHACHA20_CONSTANTS_INIT_STATE ] (temp_inp : chacha20_constants_init_state_inp) : chacha20_constants_init_state_out { 
    ({ code  '(constants_1034 : constants_t) ←
          ( '(temp_1037 : constants_t) ←
              (array_new_ (default : uint32) (4)) ;;
            ret (temp_1037)) ;;
        #put constants_1034_loc := constants_1034 ;;
       '(constants_1034 : constants_t) ←
        ( '(temp_1039 : int32) ←
            (secret (@repr U32 1634760805)) ;;
          ret (array_upd constants_1034 (usize 0) (temp_1039))) ;;
      
       '(constants_1034 : constants_t) ←
        ( '(temp_1041 : int32) ←
            (secret (@repr U32 857760878)) ;;
          ret (array_upd constants_1034 (usize 1) (temp_1041))) ;;
      
       '(constants_1034 : constants_t) ←
        ( '(temp_1043 : int32) ←
            (secret (@repr U32 2036477234)) ;;
          ret (array_upd constants_1034 (usize 2) (temp_1043))) ;;
      
       '(constants_1034 : constants_t) ←
        ( '(temp_1045 : int32) ←
            (secret (@repr U32 1797285236)) ;;
          ret (array_upd constants_1034 (usize 3) (temp_1045))) ;;
      
      @ret (constants_t) (constants_1034) } : code (CEfset (
          [constants_1034_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_chacha20_constants_init_state : package _ _ _ :=
  (chacha20_constants_init_state).
Fail Next Obligation.

Notation "'chacha20_constants_init_inp'" :=(
   : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_constants_init_out'" :=(
  constants_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_CONSTANTS_INIT : nat :=
  (1048).
Program Definition chacha20_constants_init
  
  :both (CEfset ([constants_1034_loc])) [interface] (constants_t) :=
  letbm constants_1034 : constants_t loc( constants_1034_loc ) :=
    array_new_ (default : uint32) (4) in
  letb constants_1034 : constants_t :=
    array_upd constants_1034 (lift_to_both0 (usize 0)) (is_pure (secret (
          lift_to_both0 (@repr U32 1634760805)))) in
  letb constants_1034 : constants_t :=
    array_upd constants_1034 (lift_to_both0 (usize 1)) (is_pure (secret (
          lift_to_both0 (@repr U32 857760878)))) in
  letb constants_1034 : constants_t :=
    array_upd constants_1034 (lift_to_both0 (usize 2)) (is_pure (secret (
          lift_to_both0 (@repr U32 2036477234)))) in
  letb constants_1034 : constants_t :=
    array_upd constants_1034 (lift_to_both0 (usize 3)) (is_pure (secret (
          lift_to_both0 (@repr U32 1797285236)))) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
    lift_to_both0 constants_1034)
  .
Fail Next Obligation.

Definition chacha20_init_pure
  (key_1051 : cha_cha_key_t)
  (iv_1052 : cha_cha_iv_t)
  (ctr_1053 : uint32)
  : state_t :=
  let st_1049 : state_t :=
    array_new_ (default : uint32) (16) in 
  let st_1049 :=
    array_update (st_1049) (usize 0) (
      array_to_seq (chacha20_constants_init )) in 
  let st_1049 :=
    array_update (st_1049) (usize 4) (array_to_le_uint32s (key_1051)) in 
  let st_1049 :=
    array_upd st_1049 (usize 12) (ctr_1053) in 
  let st_1049 :=
    array_update (st_1049) (usize 13) (array_to_le_uint32s (iv_1052)) in 
  st_1049.
Definition chacha20_init_pure_code
  (key_1051 : cha_cha_key_t)
  (iv_1052 : cha_cha_iv_t)
  (ctr_1053 : uint32)
  : code fset.fset0 [interface] (@ct (state_t)) :=
  lift_to_code (chacha20_init_pure key_1051 iv_1052 ctr_1053).

Definition st_1049_loc : ChoiceEqualityLocation :=
  ((state_t ; 1070%nat)).
Notation "'chacha20_init_state_inp'" := (
  cha_cha_key_t '× cha_cha_iv_t '× uint32 : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_init_state_out'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_INIT_STATE : nat :=
  (1071).
Program Definition chacha20_init_state
   : package (CEfset ([st_1049_loc])) [interface
  #val #[ CHACHA20_CONSTANTS_INIT_STATE ] : chacha20_constants_init_state_inp → chacha20_constants_init_state_out
  ] [interface
  #val #[ CHACHA20_INIT_STATE ] : chacha20_init_state_inp → chacha20_init_state_out
  ] :=
  (
    [package #def #[ CHACHA20_INIT_STATE ] (temp_inp : chacha20_init_state_inp) : chacha20_init_state_out { 
    let '(
      key_1051 , iv_1052 , ctr_1053) := temp_inp : cha_cha_key_t '× cha_cha_iv_t '× uint32 in
    #import {sig #[ CHACHA20_CONSTANTS_INIT_STATE ] : chacha20_constants_init_state_inp → chacha20_constants_init_state_out } as chacha20_constants_init_state ;;
    let chacha20_constants_init_state := chacha20_constants_init_state tt in
    ({ code  '(st_1049 : state_t) ←
          ( '(temp_1055 : state_t) ←
              (array_new_ (default : uint32) (16)) ;;
            ret (temp_1055)) ;;
        #put st_1049_loc := st_1049 ;;
       '(st_1049 : state_t) ←
          (( temp_1057 ←
                (chacha20_constants_init ) ;;
               '(temp_1059 : seq uint32) ←
                (array_to_seq (temp_1057)) ;;
               '(temp_1061 : state_t) ←
                (array_update (st_1049) (usize 0) (temp_1059)) ;;
              ret (temp_1061))) ;;
        #put st_1049_loc := st_1049 ;;
      
       '(st_1049 : state_t) ←
          (( temp_1063 ←
                (array_to_le_uint32s (key_1051)) ;;
               '(temp_1065 : state_t) ←
                (array_update (st_1049) (usize 4) (temp_1063)) ;;
              ret (temp_1065))) ;;
        #put st_1049_loc := st_1049 ;;
      
       '(st_1049 : state_t) ←
        (ret (array_upd st_1049 (usize 12) (ctr_1053))) ;;
      
       '(st_1049 : state_t) ←
          (( temp_1067 ←
                (array_to_le_uint32s (iv_1052)) ;;
               '(temp_1069 : state_t) ←
                (array_update (st_1049) (usize 13) (temp_1067)) ;;
              ret (temp_1069))) ;;
        #put st_1049_loc := st_1049 ;;
      
      @ret (state_t) (st_1049) } : code (CEfset ([st_1049_loc])) [interface
      #val #[ CHACHA20_CONSTANTS_INIT_STATE ] : chacha20_constants_init_state_inp → chacha20_constants_init_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_chacha20_init_state : package _ _ _ :=
  (seq_link chacha20_init_state link_rest(
      package_chacha20_constants_init_state)).
Fail Next Obligation.

Notation "'chacha20_init_inp'" :=(
  cha_cha_key_t '× cha_cha_iv_t '× uint32 : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_init_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_INIT : nat :=
  (1072).
Program Definition chacha20_init
  (key_1051 : cha_cha_key_t)
  (iv_1052 : cha_cha_iv_t)
  (ctr_1053 : uint32)
  :both (CEfset ([st_1049_loc])) [interface
  #val #[ CHACHA20_CONSTANTS_INIT ] : chacha20_constants_init_inp → chacha20_constants_init_out
  ] (state_t) :=
  #import {sig #[ CHACHA20_CONSTANTS_INIT ] : chacha20_constants_init_inp → chacha20_constants_init_out } as chacha20_constants_init ;;
  let chacha20_constants_init := chacha20_constants_init tt in
  letbm st_1049 : state_t loc( st_1049_loc ) :=
    array_new_ (default : uint32) (16) in
  letbm st_1049 loc( st_1049_loc ) :=
    array_update (lift_to_both0 st_1049) (lift_to_both0 (usize 0)) (
      array_to_seq (chacha20_constants_init )) in
  letbm st_1049 loc( st_1049_loc ) :=
    array_update (lift_to_both0 st_1049) (lift_to_both0 (usize 4)) (
      array_to_le_uint32s (lift_to_both0 key_1051)) in
  letb st_1049 : state_t :=
    array_upd st_1049 (lift_to_both0 (usize 12)) (is_pure (
        lift_to_both0 ctr_1053)) in
  letbm st_1049 loc( st_1049_loc ) :=
    array_update (lift_to_both0 st_1049) (lift_to_both0 (usize 13)) (
      array_to_le_uint32s (lift_to_both0 iv_1052)) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 st_1049)
  .
Fail Next Obligation.

Definition chacha20_key_block_pure (state_1073 : state_t) : block_t :=
  let state_1074 : state_t :=
    chacha20_core (secret (@repr U32 0)) (state_1073) in 
  array_from_seq (64) (array_to_le_bytes (state_1074)).
Definition chacha20_key_block_pure_code
  (state_1073 : state_t)
  : code fset.fset0 [interface] (@ct (block_t)) :=
  lift_to_code (chacha20_key_block_pure state_1073).


Notation "'chacha20_key_block_state_inp'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_key_block_state_out'" := (
  block_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_KEY_BLOCK_STATE : nat :=
  (1083).
Program Definition chacha20_key_block_state
   : package (CEfset ([])) [interface
  #val #[ CHACHA20_CORE_STATE ] : chacha20_core_state_inp → chacha20_core_state_out
  ] [interface
  #val #[ CHACHA20_KEY_BLOCK_STATE ] : chacha20_key_block_state_inp → chacha20_key_block_state_out
  ] :=
  (
    [package #def #[ CHACHA20_KEY_BLOCK_STATE ] (temp_inp : chacha20_key_block_state_inp) : chacha20_key_block_state_out { 
    let '(state_1073) := temp_inp : state_t in
    #import {sig #[ CHACHA20_CORE_STATE ] : chacha20_core_state_inp → chacha20_core_state_out } as chacha20_core_state ;;
    let chacha20_core_state := fun x_0 x_1 => chacha20_core_state (x_0,x_1) in
    ({ code  '(state_1074 : state_t) ←
        ( '(temp_1076 : int32) ←
            (secret (@repr U32 0)) ;;
           temp_1078 ←
            (chacha20_core (temp_1076) (state_1073)) ;;
          ret (temp_1078)) ;;
       temp_1080 ←
        (array_to_le_bytes (state_1074)) ;;
       '(temp_1082 : block_t) ←
        (array_from_seq (64) (temp_1080)) ;;
      @ret (block_t) (temp_1082) } : code (CEfset ([])) [interface
      #val #[ CHACHA20_CORE_STATE ] : chacha20_core_state_inp → chacha20_core_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_chacha20_key_block_state : package _ _ _ :=
  (seq_link chacha20_key_block_state link_rest(package_chacha20_core_state)).
Fail Next Obligation.

Notation "'chacha20_key_block_inp'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_key_block_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_KEY_BLOCK : nat :=
  (1084).
Program Definition chacha20_key_block
  (state_1073 : state_t)
  :both (CEfset ([])) [interface
  #val #[ CHACHA20_CORE ] : chacha20_core_inp → chacha20_core_out ] (
    block_t) :=
  #import {sig #[ CHACHA20_CORE ] : chacha20_core_inp → chacha20_core_out } as chacha20_core ;;
  let chacha20_core := fun x_0 x_1 => chacha20_core (x_0,x_1) in
  letb state_1074 : state_t :=
    chacha20_core (secret (lift_to_both0 (@repr U32 0))) (
      lift_to_both0 state_1073) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (64) (
      array_to_le_bytes (lift_to_both0 state_1074)))
  .
Fail Next Obligation.

Definition chacha20_key_block0_pure
  (key_1085 : cha_cha_key_t)
  (iv_1086 : cha_cha_iv_t)
  : block_t :=
  let state_1087 : state_t :=
    chacha20_init (key_1085) (iv_1086) (secret (@repr U32 0)) in 
  chacha20_key_block (state_1087).
Definition chacha20_key_block0_pure_code
  (key_1085 : cha_cha_key_t)
  (iv_1086 : cha_cha_iv_t)
  : code fset.fset0 [interface] (@ct (block_t)) :=
  lift_to_code (chacha20_key_block0_pure key_1085 iv_1086).


Notation "'chacha20_key_block0_state_inp'" := (
  cha_cha_key_t '× cha_cha_iv_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_key_block0_state_out'" := (
  block_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_KEY_BLOCK0_STATE : nat :=
  (1094).
Program Definition chacha20_key_block0_state
   : package (CEfset ([])) [interface
  #val #[ CHACHA20_INIT_STATE ] : chacha20_init_state_inp → chacha20_init_state_out ;
  #val #[ CHACHA20_KEY_BLOCK_STATE ] : chacha20_key_block_state_inp → chacha20_key_block_state_out
  ] [interface
  #val #[ CHACHA20_KEY_BLOCK0_STATE ] : chacha20_key_block0_state_inp → chacha20_key_block0_state_out
  ] :=
  (
    [package #def #[ CHACHA20_KEY_BLOCK0_STATE ] (temp_inp : chacha20_key_block0_state_inp) : chacha20_key_block0_state_out { 
    let '(key_1085 , iv_1086) := temp_inp : cha_cha_key_t '× cha_cha_iv_t in
    #import {sig #[ CHACHA20_INIT_STATE ] : chacha20_init_state_inp → chacha20_init_state_out } as chacha20_init_state ;;
    let chacha20_init_state := fun x_0 x_1 x_2 => chacha20_init_state (
      x_0,x_1,x_2) in
    #import {sig #[ CHACHA20_KEY_BLOCK_STATE ] : chacha20_key_block_state_inp → chacha20_key_block_state_out } as chacha20_key_block_state ;;
    let chacha20_key_block_state := fun x_0 => chacha20_key_block_state (x_0) in
    ({ code  '(state_1087 : state_t) ←
        ( '(temp_1089 : int32) ←
            (secret (@repr U32 0)) ;;
           temp_1091 ←
            (chacha20_init (key_1085) (iv_1086) (temp_1089)) ;;
          ret (temp_1091)) ;;
       temp_1093 ←
        (chacha20_key_block (state_1087)) ;;
      @ret (block_t) (temp_1093) } : code (CEfset ([])) [interface
      #val #[ CHACHA20_INIT_STATE ] : chacha20_init_state_inp → chacha20_init_state_out ;
      #val #[ CHACHA20_KEY_BLOCK_STATE ] : chacha20_key_block_state_inp → chacha20_key_block_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_chacha20_key_block0_state : package _ _ _ :=
  (seq_link chacha20_key_block0_state link_rest(
      package_chacha20_init_state,package_chacha20_key_block_state)).
Fail Next Obligation.

Notation "'chacha20_key_block0_inp'" :=(
  cha_cha_key_t '× cha_cha_iv_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_key_block0_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_KEY_BLOCK0 : nat :=
  (1095).
Program Definition chacha20_key_block0
  (key_1085 : cha_cha_key_t)
  (iv_1086 : cha_cha_iv_t)
  :both (CEfset ([])) [interface
  #val #[ CHACHA20_INIT ] : chacha20_init_inp → chacha20_init_out ;
  #val #[ CHACHA20_KEY_BLOCK ] : chacha20_key_block_inp → chacha20_key_block_out
  ] (block_t) :=
  #import {sig #[ CHACHA20_INIT ] : chacha20_init_inp → chacha20_init_out } as chacha20_init ;;
  let chacha20_init := fun x_0 x_1 x_2 => chacha20_init (x_0,x_1,x_2) in
  #import {sig #[ CHACHA20_KEY_BLOCK ] : chacha20_key_block_inp → chacha20_key_block_out } as chacha20_key_block ;;
  let chacha20_key_block := fun x_0 => chacha20_key_block (x_0) in
  letb state_1087 : state_t :=
    chacha20_init (lift_to_both0 key_1085) (lift_to_both0 iv_1086) (secret (
        lift_to_both0 (@repr U32 0))) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (chacha20_key_block (
      lift_to_both0 state_1087))
  .
Fail Next Obligation.

Definition chacha20_encrypt_block_pure
  (st0_1096 : state_t)
  (ctr_1097 : uint32)
  (plain_1098 : block_t)
  : block_t :=
  let st_1099 : state_t :=
    chacha20_core (ctr_1097) (st0_1096) in 
  let pl_1100 : state_t :=
    array_from_seq (16) (array_to_le_uint32s (plain_1098)) in 
  let st_1101 : state_t :=
    ((pl_1100) array_xor (st_1099)) in 
  array_from_seq (64) (array_to_le_bytes (st_1101)).
Definition chacha20_encrypt_block_pure_code
  (st0_1096 : state_t)
  (ctr_1097 : uint32)
  (plain_1098 : block_t)
  : code fset.fset0 [interface] (@ct (block_t)) :=
  lift_to_code (chacha20_encrypt_block_pure st0_1096 ctr_1097 plain_1098).


Notation "'chacha20_encrypt_block_state_inp'" := (
  state_t '× uint32 '× block_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_encrypt_block_state_out'" := (
  block_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_ENCRYPT_BLOCK_STATE : nat :=
  (1114).
Program Definition chacha20_encrypt_block_state
   : package (CEfset ([])) [interface
  #val #[ CHACHA20_CORE_STATE ] : chacha20_core_state_inp → chacha20_core_state_out
  ] [interface
  #val #[ CHACHA20_ENCRYPT_BLOCK_STATE ] : chacha20_encrypt_block_state_inp → chacha20_encrypt_block_state_out
  ] :=
  (
    [package #def #[ CHACHA20_ENCRYPT_BLOCK_STATE ] (temp_inp : chacha20_encrypt_block_state_inp) : chacha20_encrypt_block_state_out { 
    let '(
      st0_1096 , ctr_1097 , plain_1098) := temp_inp : state_t '× uint32 '× block_t in
    #import {sig #[ CHACHA20_CORE_STATE ] : chacha20_core_state_inp → chacha20_core_state_out } as chacha20_core_state ;;
    let chacha20_core_state := fun x_0 x_1 => chacha20_core_state (x_0,x_1) in
    ({ code  '(st_1099 : state_t) ←
        ( temp_1103 ←
            (chacha20_core (ctr_1097) (st0_1096)) ;;
          ret (temp_1103)) ;;
       '(pl_1100 : state_t) ←
        ( temp_1105 ←
            (array_to_le_uint32s (plain_1098)) ;;
           '(temp_1107 : state_t) ←
            (array_from_seq (16) (temp_1105)) ;;
          ret (temp_1107)) ;;
       '(st_1101 : state_t) ←
        ( temp_1109 ←
            ((pl_1100) array_xor (st_1099)) ;;
          ret (temp_1109)) ;;
       temp_1111 ←
        (array_to_le_bytes (st_1101)) ;;
       '(temp_1113 : block_t) ←
        (array_from_seq (64) (temp_1111)) ;;
      @ret (block_t) (temp_1113) } : code (CEfset ([])) [interface
      #val #[ CHACHA20_CORE_STATE ] : chacha20_core_state_inp → chacha20_core_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_chacha20_encrypt_block_state : package _ _ _ :=
  (seq_link chacha20_encrypt_block_state link_rest(
      package_chacha20_core_state)).
Fail Next Obligation.

Notation "'chacha20_encrypt_block_inp'" :=(
  state_t '× uint32 '× block_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_encrypt_block_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_ENCRYPT_BLOCK : nat :=
  (1115).
Program Definition chacha20_encrypt_block
  (st0_1096 : state_t)
  (ctr_1097 : uint32)
  (plain_1098 : block_t)
  :both (CEfset ([])) [interface
  #val #[ CHACHA20_CORE ] : chacha20_core_inp → chacha20_core_out ] (
    block_t) :=
  #import {sig #[ CHACHA20_CORE ] : chacha20_core_inp → chacha20_core_out } as chacha20_core ;;
  let chacha20_core := fun x_0 x_1 => chacha20_core (x_0,x_1) in
  letb st_1099 : state_t :=
    chacha20_core (lift_to_both0 ctr_1097) (lift_to_both0 st0_1096) in
  letb pl_1100 : state_t :=
    array_from_seq (16) (array_to_le_uint32s (lift_to_both0 plain_1098)) in
  letb st_1101 : state_t :=
    (lift_to_both0 pl_1100) array_xor (lift_to_both0 st_1099) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (64) (
      array_to_le_bytes (lift_to_both0 st_1101)))
  .
Fail Next Obligation.

Definition chacha20_encrypt_last_pure
  (st0_1118 : state_t)
  (ctr_1119 : uint32)
  (plain_1120 : byte_seq)
  : byte_seq :=
  let b_1116 : block_t :=
    array_new_ (default : uint8) (64) in 
  let b_1116 :=
    array_update (b_1116) (usize 0) (plain_1120) in 
  let b_1116 :=
    chacha20_encrypt_block (st0_1118) (ctr_1119) (b_1116) in 
  array_slice (b_1116) (usize 0) (seq_len (plain_1120)).
Definition chacha20_encrypt_last_pure_code
  (st0_1118 : state_t)
  (ctr_1119 : uint32)
  (plain_1120 : byte_seq)
  : code fset.fset0 [interface] (@ct (byte_seq)) :=
  lift_to_code (chacha20_encrypt_last_pure st0_1118 ctr_1119 plain_1120).

Definition b_1116_loc : ChoiceEqualityLocation :=
  ((block_t ; 1131%nat)).
Notation "'chacha20_encrypt_last_state_inp'" := (
  state_t '× uint32 '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_encrypt_last_state_out'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_ENCRYPT_LAST_STATE : nat :=
  (1132).
Program Definition chacha20_encrypt_last_state
   : package (CEfset ([b_1116_loc])) [interface
  #val #[ CHACHA20_ENCRYPT_BLOCK_STATE ] : chacha20_encrypt_block_state_inp → chacha20_encrypt_block_state_out
  ] [interface
  #val #[ CHACHA20_ENCRYPT_LAST_STATE ] : chacha20_encrypt_last_state_inp → chacha20_encrypt_last_state_out
  ] :=
  (
    [package #def #[ CHACHA20_ENCRYPT_LAST_STATE ] (temp_inp : chacha20_encrypt_last_state_inp) : chacha20_encrypt_last_state_out { 
    let '(
      st0_1118 , ctr_1119 , plain_1120) := temp_inp : state_t '× uint32 '× byte_seq in
    #import {sig #[ CHACHA20_ENCRYPT_BLOCK_STATE ] : chacha20_encrypt_block_state_inp → chacha20_encrypt_block_state_out } as chacha20_encrypt_block_state ;;
    let chacha20_encrypt_block_state := fun x_0 x_1 x_2 => chacha20_encrypt_block_state (
      x_0,x_1,x_2) in
    ({ code  '(b_1116 : block_t) ←
          ( '(temp_1122 : block_t) ←
              (array_new_ (default : uint8) (64)) ;;
            ret (temp_1122)) ;;
        #put b_1116_loc := b_1116 ;;
       '(b_1116 : block_t) ←
          (( '(temp_1124 : block_t) ←
                (array_update (b_1116) (usize 0) (plain_1120)) ;;
              ret (temp_1124))) ;;
        #put b_1116_loc := b_1116 ;;
      
       '(b_1116 : block_t) ←
          (( temp_1126 ←
                (chacha20_encrypt_block (st0_1118) (ctr_1119) (b_1116)) ;;
              ret (temp_1126))) ;;
        #put b_1116_loc := b_1116 ;;
      
       '(temp_1128 : uint_size) ←
        (seq_len (plain_1120)) ;;
       '(temp_1130 : seq uint8) ←
        (array_slice (b_1116) (usize 0) (temp_1128)) ;;
      @ret (seq uint8) (temp_1130) } : code (CEfset ([b_1116_loc])) [interface
      #val #[ CHACHA20_ENCRYPT_BLOCK_STATE ] : chacha20_encrypt_block_state_inp → chacha20_encrypt_block_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_chacha20_encrypt_last_state : package _ _ _ :=
  (seq_link chacha20_encrypt_last_state link_rest(
      package_chacha20_encrypt_block_state)).
Fail Next Obligation.

Notation "'chacha20_encrypt_last_inp'" :=(
  state_t '× uint32 '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_encrypt_last_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_ENCRYPT_LAST : nat :=
  (1133).
Program Definition chacha20_encrypt_last
  (st0_1118 : state_t)
  (ctr_1119 : uint32)
  (plain_1120 : byte_seq)
  :both (CEfset ([b_1116_loc])) [interface
  #val #[ CHACHA20_ENCRYPT_BLOCK ] : chacha20_encrypt_block_inp → chacha20_encrypt_block_out
  ] (byte_seq) :=
  #import {sig #[ CHACHA20_ENCRYPT_BLOCK ] : chacha20_encrypt_block_inp → chacha20_encrypt_block_out } as chacha20_encrypt_block ;;
  let chacha20_encrypt_block := fun x_0 x_1 x_2 => chacha20_encrypt_block (
    x_0,x_1,x_2) in
  letbm b_1116 : block_t loc( b_1116_loc ) :=
    array_new_ (default : uint8) (64) in
  letbm b_1116 loc( b_1116_loc ) :=
    array_update (lift_to_both0 b_1116) (lift_to_both0 (usize 0)) (
      lift_to_both0 plain_1120) in
  letbm b_1116 loc( b_1116_loc ) :=
    chacha20_encrypt_block (lift_to_both0 st0_1118) (lift_to_both0 ctr_1119) (
      lift_to_both0 b_1116) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_slice (
      lift_to_both0 b_1116) (lift_to_both0 (usize 0)) (seq_len (
        lift_to_both0 plain_1120)))
  .
Fail Next Obligation.

Definition chacha20_update_pure
  (st0_1136 : state_t)
  (m_1137 : byte_seq)
  : byte_seq :=
  let blocks_out_1134 : seq uint8 :=
    seq_new_ (default : uint8) (seq_len (m_1137)) in 
  let n_blocks_1138 : uint_size :=
    seq_num_exact_chunks (m_1137) (usize 64) in 
  let blocks_out_1134 :=
    Hacspec_Lib_Pre.foldi (usize 0) (n_blocks_1138) blocks_out_1134
      (fun i_1139 blocks_out_1134 =>
      let msg_block_1140 : seq uint8 :=
        seq_get_exact_chunk (m_1137) (usize 64) (i_1139) in 
      let b_1141 : block_t :=
        chacha20_encrypt_block (st0_1136) (secret (pub_u32 (i_1139))) (
          array_from_seq (64) (msg_block_1140)) in 
      let blocks_out_1134 :=
        seq_set_exact_chunk (blocks_out_1134) (usize 64) (i_1139) (
          array_to_seq (b_1141)) in 
      (blocks_out_1134)) in 
  let last_block_1142 : seq uint8 :=
    seq_get_remainder_chunk (m_1137) (usize 64) in 
  let '(blocks_out_1134) :=
    ((if (((seq_len (last_block_1142)) !=.? (usize 0))):bool_ChoiceEquality
        then (let b_1143 : seq uint8 :=
            chacha20_encrypt_last (st0_1136) (secret (pub_u32 (
                  n_blocks_1138))) (last_block_1142) in 
          let blocks_out_1134 :=
            seq_set_chunk (blocks_out_1134) (usize 64) (n_blocks_1138) (
              b_1143) in 
          (blocks_out_1134))
        else ((blocks_out_1134))) : T _) in 
  blocks_out_1134.
Definition chacha20_update_pure_code
  (st0_1136 : state_t)
  (m_1137 : byte_seq)
  : code fset.fset0 [interface] (@ct (byte_seq)) :=
  lift_to_code (chacha20_update_pure st0_1136 m_1137).

Definition blocks_out_1134_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 1174%nat)).
Notation "'chacha20_update_state_inp'" := (
  state_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_update_state_out'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_UPDATE_STATE : nat :=
  (1175).
Program Definition chacha20_update_state
   : package (CEfset ([blocks_out_1134_loc])) [interface
  #val #[ CHACHA20_ENCRYPT_BLOCK_STATE ] : chacha20_encrypt_block_state_inp → chacha20_encrypt_block_state_out ;
  #val #[ CHACHA20_ENCRYPT_LAST_STATE ] : chacha20_encrypt_last_state_inp → chacha20_encrypt_last_state_out
  ] [interface
  #val #[ CHACHA20_UPDATE_STATE ] : chacha20_update_state_inp → chacha20_update_state_out
  ] :=
  (
    [package #def #[ CHACHA20_UPDATE_STATE ] (temp_inp : chacha20_update_state_inp) : chacha20_update_state_out { 
    let '(st0_1136 , m_1137) := temp_inp : state_t '× byte_seq in
    #import {sig #[ CHACHA20_ENCRYPT_BLOCK_STATE ] : chacha20_encrypt_block_state_inp → chacha20_encrypt_block_state_out } as chacha20_encrypt_block_state ;;
    let chacha20_encrypt_block_state := fun x_0 x_1 x_2 => chacha20_encrypt_block_state (
      x_0,x_1,x_2) in
    #import {sig #[ CHACHA20_ENCRYPT_LAST_STATE ] : chacha20_encrypt_last_state_inp → chacha20_encrypt_last_state_out } as chacha20_encrypt_last_state ;;
    let chacha20_encrypt_last_state := fun x_0 x_1 x_2 => chacha20_encrypt_last_state (
      x_0,x_1,x_2) in
    ({ code  '(blocks_out_1134 : seq uint8) ←
          ( '(temp_1145 : uint_size) ←
              (seq_len (m_1137)) ;;
             temp_1147 ←
              (seq_new_ (default : uint8) (temp_1145)) ;;
            ret (temp_1147)) ;;
        #put blocks_out_1134_loc := blocks_out_1134 ;;
       '(n_blocks_1138 : uint_size) ←
        ( '(temp_1149 : uint_size) ←
            (seq_num_exact_chunks (m_1137) (usize 64)) ;;
          ret (temp_1149)) ;;
       '(blocks_out_1134 : (seq uint8)) ←
        (foldi' (usize 0) (n_blocks_1138) blocks_out_1134 (L2 := CEfset (
                [blocks_out_1134_loc])) (I2 := [interface
              #val #[ CHACHA20_ENCRYPT_BLOCK_STATE ] : chacha20_encrypt_block_state_inp → chacha20_encrypt_block_state_out ;
              #val #[ CHACHA20_ENCRYPT_LAST_STATE ] : chacha20_encrypt_last_state_inp → chacha20_encrypt_last_state_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_1139 blocks_out_1134 =>
            ({ code  '(msg_block_1140 : seq uint8) ←
                ( '(temp_1151 : byte_seq) ←
                    (seq_get_exact_chunk (m_1137) (usize 64) (i_1139)) ;;
                  ret (temp_1151)) ;;
               '(b_1141 : block_t) ←
                ( '(temp_1153 : int32) ←
                    (secret (pub_u32 (i_1139))) ;;
                   '(temp_1155 : block_t) ←
                    (array_from_seq (64) (msg_block_1140)) ;;
                   temp_1157 ←
                    (chacha20_encrypt_block (st0_1136) (temp_1153) (
                        temp_1155)) ;;
                  ret (temp_1157)) ;;
               '(blocks_out_1134 : seq uint8) ←
                  (( '(temp_1159 : seq uint8) ←
                        (array_to_seq (b_1141)) ;;
                       '(temp_1161 : seq uint8) ←
                        (seq_set_exact_chunk (blocks_out_1134) (usize 64) (
                            i_1139) (temp_1159)) ;;
                      ret (temp_1161))) ;;
                #put blocks_out_1134_loc := blocks_out_1134 ;;
              
              @ret ((seq uint8)) (blocks_out_1134) } : code (CEfset (
                  [blocks_out_1134_loc])) [interface] _))) ;;
      
       '(last_block_1142 : seq uint8) ←
        ( '(temp_1163 : byte_seq) ←
            (seq_get_remainder_chunk (m_1137) (usize 64)) ;;
          ret (temp_1163)) ;;
       '(temp_1165 : uint_size) ←
        (seq_len (last_block_1142)) ;;
       '(temp_1167 : bool_ChoiceEquality) ←
        ((temp_1165) !=.? (usize 0)) ;;
       '(blocks_out_1134 : (seq uint8)) ←
        (if temp_1167:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(b_1143 : seq uint8) ←
              ( '(temp_1169 : int32) ←
                  (secret (pub_u32 (n_blocks_1138))) ;;
                 temp_1171 ←
                  (chacha20_encrypt_last (st0_1136) (temp_1169) (
                      last_block_1142)) ;;
                ret (temp_1171)) ;;
             '(blocks_out_1134 : seq uint8) ←
                (( '(temp_1173 : seq uint8) ←
                      (seq_set_chunk (blocks_out_1134) (usize 64) (
                          n_blocks_1138) (b_1143)) ;;
                    ret (temp_1173))) ;;
              #put blocks_out_1134_loc := blocks_out_1134 ;;
            
            @ret ((seq uint8)) (blocks_out_1134) in
            ({ code temp_then } : code (CEfset (
                  [blocks_out_1134_loc])) [interface] _))
          else @ret ((seq uint8)) (blocks_out_1134)) ;;
      
      @ret (seq uint8) (blocks_out_1134) } : code (CEfset (
          [blocks_out_1134_loc])) [interface
      #val #[ CHACHA20_ENCRYPT_BLOCK_STATE ] : chacha20_encrypt_block_state_inp → chacha20_encrypt_block_state_out ;
      #val #[ CHACHA20_ENCRYPT_LAST_STATE ] : chacha20_encrypt_last_state_inp → chacha20_encrypt_last_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_chacha20_update_state : package _ _ _ :=
  (seq_link chacha20_update_state link_rest(
      package_chacha20_encrypt_block_state,package_chacha20_encrypt_last_state)).
Fail Next Obligation.

Notation "'chacha20_update_inp'" :=(
  state_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_update_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_UPDATE : nat :=
  (1176).
Program Definition chacha20_update
  (st0_1136 : state_t)
  (m_1137 : byte_seq)
  :both (CEfset ([blocks_out_1134_loc])) [interface
  #val #[ CHACHA20_ENCRYPT_BLOCK ] : chacha20_encrypt_block_inp → chacha20_encrypt_block_out ;
  #val #[ CHACHA20_ENCRYPT_LAST ] : chacha20_encrypt_last_inp → chacha20_encrypt_last_out
  ] (byte_seq) :=
  #import {sig #[ CHACHA20_ENCRYPT_BLOCK ] : chacha20_encrypt_block_inp → chacha20_encrypt_block_out } as chacha20_encrypt_block ;;
  let chacha20_encrypt_block := fun x_0 x_1 x_2 => chacha20_encrypt_block (
    x_0,x_1,x_2) in
  #import {sig #[ CHACHA20_ENCRYPT_LAST ] : chacha20_encrypt_last_inp → chacha20_encrypt_last_out } as chacha20_encrypt_last ;;
  let chacha20_encrypt_last := fun x_0 x_1 x_2 => chacha20_encrypt_last (
    x_0,x_1,x_2) in
  letbm blocks_out_1134 : seq uint8 loc( blocks_out_1134_loc ) :=
    seq_new_ (default : uint8) (seq_len (lift_to_both0 m_1137)) in
  letb n_blocks_1138 : uint_size :=
    seq_num_exact_chunks (lift_to_both0 m_1137) (lift_to_both0 (usize 64)) in
  letb blocks_out_1134 :=
    foldi_both' (lift_to_both0 (usize 0)) (
        lift_to_both0 n_blocks_1138) blocks_out_1134 (L := (CEfset (
          [blocks_out_1134_loc]))) (I := ([interface
        #val #[ CHACHA20_ENCRYPT_BLOCK ] : chacha20_encrypt_block_inp → chacha20_encrypt_block_out ;
        #val #[ CHACHA20_ENCRYPT_LAST ] : chacha20_encrypt_last_inp → chacha20_encrypt_last_out
        ])) (fun i_1139 blocks_out_1134 =>
      letb msg_block_1140 : seq uint8 :=
        seq_get_exact_chunk (lift_to_both0 m_1137) (lift_to_both0 (usize 64)) (
          lift_to_both0 i_1139) in
      letb b_1141 : block_t :=
        chacha20_encrypt_block (lift_to_both0 st0_1136) (secret (pub_u32 (
              is_pure (lift_to_both0 i_1139)))) (array_from_seq (64) (
            lift_to_both0 msg_block_1140)) in
      letbm blocks_out_1134 loc( blocks_out_1134_loc ) :=
        seq_set_exact_chunk (lift_to_both0 blocks_out_1134) (lift_to_both0 (
            usize 64)) (lift_to_both0 i_1139) (
          array_to_seq (lift_to_both0 b_1141)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 blocks_out_1134)
      ) in
  letb last_block_1142 : seq uint8 :=
    seq_get_remainder_chunk (lift_to_both0 m_1137) (lift_to_both0 (usize 64)) in
  letb 'blocks_out_1134 :=
    if (seq_len (lift_to_both0 last_block_1142)) !=.? (lift_to_both0 (
        usize 0)) :bool_ChoiceEquality
    then lift_scope (L1 := CEfset ([blocks_out_1134_loc])) (L2 := CEfset (
      [blocks_out_1134_loc])) (H_loc_incl := _) (H_opsig_incl := _)a (
      letb b_1143 : seq uint8 :=
        chacha20_encrypt_last (lift_to_both0 st0_1136) (secret (pub_u32 (
              is_pure (lift_to_both0 n_blocks_1138)))) (
          lift_to_both0 last_block_1142) in
      letbm blocks_out_1134 loc( blocks_out_1134_loc ) :=
        seq_set_chunk (lift_to_both0 blocks_out_1134) (lift_to_both0 (
            usize 64)) (lift_to_both0 n_blocks_1138) (lift_to_both0 b_1143) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 blocks_out_1134)
      )
    else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
      lift_to_both0 blocks_out_1134)
     in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
    lift_to_both0 blocks_out_1134)
  .
Fail Next Obligation.

Definition chacha20_pure
  (key_1177 : cha_cha_key_t)
  (iv_1178 : cha_cha_iv_t)
  (ctr_1179 : int32)
  (m_1180 : byte_seq)
  : byte_seq :=
  let state_1181 : state_t :=
    chacha20_init (key_1177) (iv_1178) (secret (ctr_1179)) in 
  chacha20_update (state_1181) (m_1180).
Definition chacha20_pure_code
  (key_1177 : cha_cha_key_t)
  (iv_1178 : cha_cha_iv_t)
  (ctr_1179 : int32)
  (m_1180 : byte_seq)
  : code fset.fset0 [interface] (@ct (byte_seq)) :=
  lift_to_code (chacha20_pure key_1177 iv_1178 ctr_1179 m_1180).


Notation "'chacha20_state_inp'" := (
  cha_cha_key_t '× cha_cha_iv_t '× int32 '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_state_out'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_STATE : nat :=
  (1188).
Program Definition chacha20_state
   : package (CEfset ([])) [interface
  #val #[ CHACHA20_INIT_STATE ] : chacha20_init_state_inp → chacha20_init_state_out ;
  #val #[ CHACHA20_UPDATE_STATE ] : chacha20_update_state_inp → chacha20_update_state_out
  ] [interface
  #val #[ CHACHA20_STATE ] : chacha20_state_inp → chacha20_state_out ] :=
  (
    [package #def #[ CHACHA20_STATE ] (temp_inp : chacha20_state_inp) : chacha20_state_out { 
    let '(
      key_1177 , iv_1178 , ctr_1179 , m_1180) := temp_inp : cha_cha_key_t '× cha_cha_iv_t '× int32 '× byte_seq in
    #import {sig #[ CHACHA20_INIT_STATE ] : chacha20_init_state_inp → chacha20_init_state_out } as chacha20_init_state ;;
    let chacha20_init_state := fun x_0 x_1 x_2 => chacha20_init_state (
      x_0,x_1,x_2) in
    #import {sig #[ CHACHA20_UPDATE_STATE ] : chacha20_update_state_inp → chacha20_update_state_out } as chacha20_update_state ;;
    let chacha20_update_state := fun x_0 x_1 => chacha20_update_state (
      x_0,x_1) in
    ({ code  '(state_1181 : state_t) ←
        ( '(temp_1183 : int32) ←
            (secret (ctr_1179)) ;;
           temp_1185 ←
            (chacha20_init (key_1177) (iv_1178) (temp_1183)) ;;
          ret (temp_1185)) ;;
       temp_1187 ←
        (chacha20_update (state_1181) (m_1180)) ;;
      @ret (byte_seq) (temp_1187) } : code (CEfset ([])) [interface
      #val #[ CHACHA20_INIT_STATE ] : chacha20_init_state_inp → chacha20_init_state_out ;
      #val #[ CHACHA20_UPDATE_STATE ] : chacha20_update_state_inp → chacha20_update_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_chacha20_state : package _ _ _ :=
  (seq_link chacha20_state link_rest(
      package_chacha20_init_state,package_chacha20_update_state)).
Fail Next Obligation.

Notation "'chacha20_inp'" :=(
  cha_cha_key_t '× cha_cha_iv_t '× int32 '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition CHACHA20 : nat :=
  (1189).
Program Definition chacha20
  (key_1177 : cha_cha_key_t)
  (iv_1178 : cha_cha_iv_t)
  (ctr_1179 : int32)
  (m_1180 : byte_seq)
  :both (CEfset ([])) [interface
  #val #[ CHACHA20_INIT ] : chacha20_init_inp → chacha20_init_out ;
  #val #[ CHACHA20_UPDATE ] : chacha20_update_inp → chacha20_update_out ] (
    byte_seq) :=
  #import {sig #[ CHACHA20_INIT ] : chacha20_init_inp → chacha20_init_out } as chacha20_init ;;
  let chacha20_init := fun x_0 x_1 x_2 => chacha20_init (x_0,x_1,x_2) in
  #import {sig #[ CHACHA20_UPDATE ] : chacha20_update_inp → chacha20_update_out } as chacha20_update ;;
  let chacha20_update := fun x_0 x_1 => chacha20_update (x_0,x_1) in
  letb state_1181 : state_t :=
    chacha20_init (lift_to_both0 key_1177) (lift_to_both0 iv_1178) (secret (
        lift_to_both0 ctr_1179)) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (chacha20_update (
      lift_to_both0 state_1181) (lift_to_both0 m_1180))
  .
Fail Next Obligation.

