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

Obligation Tactic := try timeout 8 solve_ssprove_obligations.


Definition blocksize_v : uint_size :=
  usize 16.

Definition ivsize_v : uint_size :=
  usize 12.

Definition key_length_v : uint_size :=
  usize 4.

Definition rounds_v : uint_size :=
  usize 10.

Definition key_schedule_length_v : uint_size :=
  usize 176.

Definition iterations_v : uint_size :=
  usize 40.

Definition invalid_key_expansion_index_v : int8 :=
  @repr U8 1.

Definition block_t := nseq (uint8) (blocksize_v).

Definition word_t := nseq (uint8) (key_length_v).

Definition round_key_t := nseq (uint8) (blocksize_v).

Definition aes_nonce_t := nseq (uint8) (ivsize_v).

Definition s_box_t := nseq (uint8) (usize 256).

Definition r_con_t := nseq (uint8) (usize 15).

Definition bytes144_t := nseq (uint8) (usize 144).

Definition bytes176_t := nseq (uint8) (key_schedule_length_v).

Definition key128_t := nseq (uint8) (blocksize_v).

Notation "'byte_seq_result_t'" := ((result int8 byte_seq)) : hacspec_scope.

Notation "'block_result_t'" := ((result int8 block_t)) : hacspec_scope.

Notation "'word_result_t'" := ((result int8 word_t)) : hacspec_scope.

Definition sbox_v : s_box_t :=
  array_from_list uint8 (let0 l :=
      [
        (secret (@repr U8 99)) : uint8;
        (secret (@repr U8 124)) : uint8;
        (secret (@repr U8 119)) : uint8;
        (secret (@repr U8 123)) : uint8;
        (secret (@repr U8 242)) : uint8;
        (secret (@repr U8 107)) : uint8;
        (secret (@repr U8 111)) : uint8;
        (secret (@repr U8 197)) : uint8;
        (secret (@repr U8 48)) : uint8;
        (secret (@repr U8 1)) : uint8;
        (secret (@repr U8 103)) : uint8;
        (secret (@repr U8 43)) : uint8;
        (secret (@repr U8 254)) : uint8;
        (secret (@repr U8 215)) : uint8;
        (secret (@repr U8 171)) : uint8;
        (secret (@repr U8 118)) : uint8;
        (secret (@repr U8 202)) : uint8;
        (secret (@repr U8 130)) : uint8;
        (secret (@repr U8 201)) : uint8;
        (secret (@repr U8 125)) : uint8;
        (secret (@repr U8 250)) : uint8;
        (secret (@repr U8 89)) : uint8;
        (secret (@repr U8 71)) : uint8;
        (secret (@repr U8 240)) : uint8;
        (secret (@repr U8 173)) : uint8;
        (secret (@repr U8 212)) : uint8;
        (secret (@repr U8 162)) : uint8;
        (secret (@repr U8 175)) : uint8;
        (secret (@repr U8 156)) : uint8;
        (secret (@repr U8 164)) : uint8;
        (secret (@repr U8 114)) : uint8;
        (secret (@repr U8 192)) : uint8;
        (secret (@repr U8 183)) : uint8;
        (secret (@repr U8 253)) : uint8;
        (secret (@repr U8 147)) : uint8;
        (secret (@repr U8 38)) : uint8;
        (secret (@repr U8 54)) : uint8;
        (secret (@repr U8 63)) : uint8;
        (secret (@repr U8 247)) : uint8;
        (secret (@repr U8 204)) : uint8;
        (secret (@repr U8 52)) : uint8;
        (secret (@repr U8 165)) : uint8;
        (secret (@repr U8 229)) : uint8;
        (secret (@repr U8 241)) : uint8;
        (secret (@repr U8 113)) : uint8;
        (secret (@repr U8 216)) : uint8;
        (secret (@repr U8 49)) : uint8;
        (secret (@repr U8 21)) : uint8;
        (secret (@repr U8 4)) : uint8;
        (secret (@repr U8 199)) : uint8;
        (secret (@repr U8 35)) : uint8;
        (secret (@repr U8 195)) : uint8;
        (secret (@repr U8 24)) : uint8;
        (secret (@repr U8 150)) : uint8;
        (secret (@repr U8 5)) : uint8;
        (secret (@repr U8 154)) : uint8;
        (secret (@repr U8 7)) : uint8;
        (secret (@repr U8 18)) : uint8;
        (secret (@repr U8 128)) : uint8;
        (secret (@repr U8 226)) : uint8;
        (secret (@repr U8 235)) : uint8;
        (secret (@repr U8 39)) : uint8;
        (secret (@repr U8 178)) : uint8;
        (secret (@repr U8 117)) : uint8;
        (secret (@repr U8 9)) : uint8;
        (secret (@repr U8 131)) : uint8;
        (secret (@repr U8 44)) : uint8;
        (secret (@repr U8 26)) : uint8;
        (secret (@repr U8 27)) : uint8;
        (secret (@repr U8 110)) : uint8;
        (secret (@repr U8 90)) : uint8;
        (secret (@repr U8 160)) : uint8;
        (secret (@repr U8 82)) : uint8;
        (secret (@repr U8 59)) : uint8;
        (secret (@repr U8 214)) : uint8;
        (secret (@repr U8 179)) : uint8;
        (secret (@repr U8 41)) : uint8;
        (secret (@repr U8 227)) : uint8;
        (secret (@repr U8 47)) : uint8;
        (secret (@repr U8 132)) : uint8;
        (secret (@repr U8 83)) : uint8;
        (secret (@repr U8 209)) : uint8;
        (secret (@repr U8 0)) : uint8;
        (secret (@repr U8 237)) : uint8;
        (secret (@repr U8 32)) : uint8;
        (secret (@repr U8 252)) : uint8;
        (secret (@repr U8 177)) : uint8;
        (secret (@repr U8 91)) : uint8;
        (secret (@repr U8 106)) : uint8;
        (secret (@repr U8 203)) : uint8;
        (secret (@repr U8 190)) : uint8;
        (secret (@repr U8 57)) : uint8;
        (secret (@repr U8 74)) : uint8;
        (secret (@repr U8 76)) : uint8;
        (secret (@repr U8 88)) : uint8;
        (secret (@repr U8 207)) : uint8;
        (secret (@repr U8 208)) : uint8;
        (secret (@repr U8 239)) : uint8;
        (secret (@repr U8 170)) : uint8;
        (secret (@repr U8 251)) : uint8;
        (secret (@repr U8 67)) : uint8;
        (secret (@repr U8 77)) : uint8;
        (secret (@repr U8 51)) : uint8;
        (secret (@repr U8 133)) : uint8;
        (secret (@repr U8 69)) : uint8;
        (secret (@repr U8 249)) : uint8;
        (secret (@repr U8 2)) : uint8;
        (secret (@repr U8 127)) : uint8;
        (secret (@repr U8 80)) : uint8;
        (secret (@repr U8 60)) : uint8;
        (secret (@repr U8 159)) : uint8;
        (secret (@repr U8 168)) : uint8;
        (secret (@repr U8 81)) : uint8;
        (secret (@repr U8 163)) : uint8;
        (secret (@repr U8 64)) : uint8;
        (secret (@repr U8 143)) : uint8;
        (secret (@repr U8 146)) : uint8;
        (secret (@repr U8 157)) : uint8;
        (secret (@repr U8 56)) : uint8;
        (secret (@repr U8 245)) : uint8;
        (secret (@repr U8 188)) : uint8;
        (secret (@repr U8 182)) : uint8;
        (secret (@repr U8 218)) : uint8;
        (secret (@repr U8 33)) : uint8;
        (secret (@repr U8 16)) : uint8;
        (secret (@repr U8 255)) : uint8;
        (secret (@repr U8 243)) : uint8;
        (secret (@repr U8 210)) : uint8;
        (secret (@repr U8 205)) : uint8;
        (secret (@repr U8 12)) : uint8;
        (secret (@repr U8 19)) : uint8;
        (secret (@repr U8 236)) : uint8;
        (secret (@repr U8 95)) : uint8;
        (secret (@repr U8 151)) : uint8;
        (secret (@repr U8 68)) : uint8;
        (secret (@repr U8 23)) : uint8;
        (secret (@repr U8 196)) : uint8;
        (secret (@repr U8 167)) : uint8;
        (secret (@repr U8 126)) : uint8;
        (secret (@repr U8 61)) : uint8;
        (secret (@repr U8 100)) : uint8;
        (secret (@repr U8 93)) : uint8;
        (secret (@repr U8 25)) : uint8;
        (secret (@repr U8 115)) : uint8;
        (secret (@repr U8 96)) : uint8;
        (secret (@repr U8 129)) : uint8;
        (secret (@repr U8 79)) : uint8;
        (secret (@repr U8 220)) : uint8;
        (secret (@repr U8 34)) : uint8;
        (secret (@repr U8 42)) : uint8;
        (secret (@repr U8 144)) : uint8;
        (secret (@repr U8 136)) : uint8;
        (secret (@repr U8 70)) : uint8;
        (secret (@repr U8 238)) : uint8;
        (secret (@repr U8 184)) : uint8;
        (secret (@repr U8 20)) : uint8;
        (secret (@repr U8 222)) : uint8;
        (secret (@repr U8 94)) : uint8;
        (secret (@repr U8 11)) : uint8;
        (secret (@repr U8 219)) : uint8;
        (secret (@repr U8 224)) : uint8;
        (secret (@repr U8 50)) : uint8;
        (secret (@repr U8 58)) : uint8;
        (secret (@repr U8 10)) : uint8;
        (secret (@repr U8 73)) : uint8;
        (secret (@repr U8 6)) : uint8;
        (secret (@repr U8 36)) : uint8;
        (secret (@repr U8 92)) : uint8;
        (secret (@repr U8 194)) : uint8;
        (secret (@repr U8 211)) : uint8;
        (secret (@repr U8 172)) : uint8;
        (secret (@repr U8 98)) : uint8;
        (secret (@repr U8 145)) : uint8;
        (secret (@repr U8 149)) : uint8;
        (secret (@repr U8 228)) : uint8;
        (secret (@repr U8 121)) : uint8;
        (secret (@repr U8 231)) : uint8;
        (secret (@repr U8 200)) : uint8;
        (secret (@repr U8 55)) : uint8;
        (secret (@repr U8 109)) : uint8;
        (secret (@repr U8 141)) : uint8;
        (secret (@repr U8 213)) : uint8;
        (secret (@repr U8 78)) : uint8;
        (secret (@repr U8 169)) : uint8;
        (secret (@repr U8 108)) : uint8;
        (secret (@repr U8 86)) : uint8;
        (secret (@repr U8 244)) : uint8;
        (secret (@repr U8 234)) : uint8;
        (secret (@repr U8 101)) : uint8;
        (secret (@repr U8 122)) : uint8;
        (secret (@repr U8 174)) : uint8;
        (secret (@repr U8 8)) : uint8;
        (secret (@repr U8 186)) : uint8;
        (secret (@repr U8 120)) : uint8;
        (secret (@repr U8 37)) : uint8;
        (secret (@repr U8 46)) : uint8;
        (secret (@repr U8 28)) : uint8;
        (secret (@repr U8 166)) : uint8;
        (secret (@repr U8 180)) : uint8;
        (secret (@repr U8 198)) : uint8;
        (secret (@repr U8 232)) : uint8;
        (secret (@repr U8 221)) : uint8;
        (secret (@repr U8 116)) : uint8;
        (secret (@repr U8 31)) : uint8;
        (secret (@repr U8 75)) : uint8;
        (secret (@repr U8 189)) : uint8;
        (secret (@repr U8 139)) : uint8;
        (secret (@repr U8 138)) : uint8;
        (secret (@repr U8 112)) : uint8;
        (secret (@repr U8 62)) : uint8;
        (secret (@repr U8 181)) : uint8;
        (secret (@repr U8 102)) : uint8;
        (secret (@repr U8 72)) : uint8;
        (secret (@repr U8 3)) : uint8;
        (secret (@repr U8 246)) : uint8;
        (secret (@repr U8 14)) : uint8;
        (secret (@repr U8 97)) : uint8;
        (secret (@repr U8 53)) : uint8;
        (secret (@repr U8 87)) : uint8;
        (secret (@repr U8 185)) : uint8;
        (secret (@repr U8 134)) : uint8;
        (secret (@repr U8 193)) : uint8;
        (secret (@repr U8 29)) : uint8;
        (secret (@repr U8 158)) : uint8;
        (secret (@repr U8 225)) : uint8;
        (secret (@repr U8 248)) : uint8;
        (secret (@repr U8 152)) : uint8;
        (secret (@repr U8 17)) : uint8;
        (secret (@repr U8 105)) : uint8;
        (secret (@repr U8 217)) : uint8;
        (secret (@repr U8 142)) : uint8;
        (secret (@repr U8 148)) : uint8;
        (secret (@repr U8 155)) : uint8;
        (secret (@repr U8 30)) : uint8;
        (secret (@repr U8 135)) : uint8;
        (secret (@repr U8 233)) : uint8;
        (secret (@repr U8 206)) : uint8;
        (secret (@repr U8 85)) : uint8;
        (secret (@repr U8 40)) : uint8;
        (secret (@repr U8 223)) : uint8;
        (secret (@repr U8 140)) : uint8;
        (secret (@repr U8 161)) : uint8;
        (secret (@repr U8 137)) : uint8;
        (secret (@repr U8 13)) : uint8;
        (secret (@repr U8 191)) : uint8;
        (secret (@repr U8 230)) : uint8;
        (secret (@repr U8 66)) : uint8;
        (secret (@repr U8 104)) : uint8;
        (secret (@repr U8 65)) : uint8;
        (secret (@repr U8 153)) : uint8;
        (secret (@repr U8 45)) : uint8;
        (secret (@repr U8 15)) : uint8;
        (secret (@repr U8 176)) : uint8;
        (secret (@repr U8 84)) : uint8;
        (secret (@repr U8 187)) : uint8;
        (secret (@repr U8 22)) : uint8
      ] in  l).

Definition rcon_v : r_con_t :=
  array_from_list uint8 (let0 l :=
      [
        (secret (@repr U8 141)) : uint8;
        (secret (@repr U8 1)) : uint8;
        (secret (@repr U8 2)) : uint8;
        (secret (@repr U8 4)) : uint8;
        (secret (@repr U8 8)) : uint8;
        (secret (@repr U8 16)) : uint8;
        (secret (@repr U8 32)) : uint8;
        (secret (@repr U8 64)) : uint8;
        (secret (@repr U8 128)) : uint8;
        (secret (@repr U8 27)) : uint8;
        (secret (@repr U8 54)) : uint8;
        (secret (@repr U8 108)) : uint8;
        (secret (@repr U8 216)) : uint8;
        (secret (@repr U8 171)) : uint8;
        (secret (@repr U8 77)) : uint8
      ] in  l).

Definition sub_bytes_pure (state_2 : block_t) : block_t :=
  let0 st_0 : block_t :=
    state_2 in 
  let0 st_0 :=
    Hacspec_Lib_Pre.foldi (usize 0) (blocksize_v) st_0
      (fun i_3 st_0 =>
      let0 st_0 :=
        array_upd st_0 (i_3) (array_index (sbox_v) (uint8_declassify (
              array_index (state_2) (i_3)))) in 
      (st_0)) in 
  st_0.
Definition sub_bytes_pure_code
  (state_2 : block_t)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (sub_bytes_pure state_2).

Definition st_0_loc : Location :=
  (block_t : choice_type ; 7%nat).
Program Definition sub_bytes_state
  (state_2 : block_t)
  : code (fset ([ st_0_loc])) [interface] (@ct (block_t)) :=
  (({ code #put st_0_loc := 
        (state_2) ;;
      '(st_0 : block_t) ← get st_0_loc ;;
       st_0 ←
        (foldi (usize 0) (blocksize_v) st_0 (fun i_3 (st_0 : _) =>
            ({ code  '(st_0 : block_t) ←
                ( temp_4 ←
                    (array_index (state_2) (i_3)) ;;
                   temp_5 ←
                    (uint8_declassify (temp_4)) ;;
                   temp_6 ←
                    (array_index (sbox_v) (temp_5)) ;;
                  ret (array_upd st_0 (i_3) (temp_6))) ;;
              
              @pkg_core_definition.ret (_) ( ((st_0))) } : code (fset (
                  [ st_0_loc])) [interface] _))) ;;
      
      @pkg_core_definition.ret (block_t) ( (st_0)) } : code (fset (
          [ st_0_loc])) [interface] _)).
Fail Next Obligation.

Program Definition sub_bytes
  (state_2 : block_t)
  : both (fset ([ st_0_loc])) [interface] block_t :=
  {|
  is_pure := sub_bytes_pure (state_2 : block_t);
  is_state := sub_bytes_state (state_2 : block_t);
  |}.
Next Obligation.
  init_both_proof sub_bytes_state sub_bytes_pure.
  step_code.
Qed. (* Admitted. *)

Definition shift_row_pure
  (i_10 : uint_size)
  (shift_11 : uint_size)
  (state_12 : block_t)
  : block_t :=
  let0 out_8 : block_t :=
    state_12 in 
  let0 out_8 :=
    array_upd out_8 (i_10) (array_index (state_12) (((i_10) .+ (((usize 4) .* ((
                  (shift_11) %% (usize 4)))))))) in 
  let0 out_8 :=
    array_upd out_8 (((i_10) .+ (usize 4))) (array_index (state_12) (((
            i_10) .+ (((usize 4) .* (((((shift_11) .+ (usize 1))) %% (
                    usize 4)))))))) in 
  let0 out_8 :=
    array_upd out_8 (((i_10) .+ (usize 8))) (array_index (state_12) (((
            i_10) .+ (((usize 4) .* (((((shift_11) .+ (usize 2))) %% (
                    usize 4)))))))) in 
  let0 out_8 :=
    array_upd out_8 (((i_10) .+ (usize 12))) (array_index (state_12) (((
            i_10) .+ (((usize 4) .* (((((shift_11) .+ (usize 3))) %% (
                    usize 4)))))))) in 
  out_8.
Definition shift_row_pure_code
  (i_10 : uint_size)
  (shift_11 : uint_size)
  (state_12 : block_t)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (shift_row_pure i_10 shift_11 state_12).

Definition out_8_loc : Location :=
  (block_t : choice_type ; 35%nat).
Program Definition shift_row_state
  (i_10 : uint_size)
  (shift_11 : uint_size)
  (state_12 : block_t)
  : code (fset ([ out_8_loc])) [interface] (@ct (block_t)) :=
  (({ code #put out_8_loc := 
        (state_12) ;;
      '(out_8 : block_t) ← get out_8_loc ;;
       '(out_8 : block_t) ←
        ( temp_13 ←
            ((shift_11) %% (usize 4)) ;;
           temp_14 ←
            ((usize 4) .* (temp_13)) ;;
           temp_15 ←
            ((i_10) .+ (temp_14)) ;;
           temp_16 ←
            (array_index (state_12) (temp_15)) ;;
          ret (array_upd out_8 (i_10) (temp_16))) ;;
      
       '(out_8 : block_t) ←
        ( temp_17 ←
            ((i_10) .+ (usize 4)) ;;
           temp_18 ←
            ((shift_11) .+ (usize 1)) ;;
           temp_19 ←
            ((temp_18) %% (usize 4)) ;;
           temp_20 ←
            ((usize 4) .* (temp_19)) ;;
           temp_21 ←
            ((i_10) .+ (temp_20)) ;;
           temp_22 ←
            (array_index (state_12) (temp_21)) ;;
          ret (array_upd out_8 (temp_17) (temp_22))) ;;
      
       '(out_8 : block_t) ←
        ( temp_23 ←
            ((i_10) .+ (usize 8)) ;;
           temp_24 ←
            ((shift_11) .+ (usize 2)) ;;
           temp_25 ←
            ((temp_24) %% (usize 4)) ;;
           temp_26 ←
            ((usize 4) .* (temp_25)) ;;
           temp_27 ←
            ((i_10) .+ (temp_26)) ;;
           temp_28 ←
            (array_index (state_12) (temp_27)) ;;
          ret (array_upd out_8 (temp_23) (temp_28))) ;;
      
       '(out_8 : block_t) ←
        ( temp_29 ←
            ((i_10) .+ (usize 12)) ;;
           temp_30 ←
            ((shift_11) .+ (usize 3)) ;;
           temp_31 ←
            ((temp_30) %% (usize 4)) ;;
           temp_32 ←
            ((usize 4) .* (temp_31)) ;;
           temp_33 ←
            ((i_10) .+ (temp_32)) ;;
           temp_34 ←
            (array_index (state_12) (temp_33)) ;;
          ret (array_upd out_8 (temp_29) (temp_34))) ;;
      
      @pkg_core_definition.ret (block_t) ( (out_8)) } : code (fset (
          [ out_8_loc])) [interface] _)).
Fail Next Obligation.

Program Definition shift_row
  (i_10 : uint_size)
  (shift_11 : uint_size)
  (state_12 : block_t)
  : both (fset ([ out_8_loc])) [interface] block_t :=
  {|
  is_pure := shift_row_pure (i_10 : uint_size)
  (shift_11 : uint_size)
  (state_12 : block_t);
  is_state := shift_row_state (i_10 : uint_size)
  (shift_11 : uint_size)
  (state_12 : block_t);
  |}.
Next Obligation.
init_both_proof shift_row_state shift_row_pure.
step_code. Qed. (* Admitted. *)

Definition shift_rows_pure (state_36 : block_t) : block_t :=
  let0 state_37 : block_t :=
    shift_row (usize 1) (usize 1) (state_36) : T _ in 
  let0 state_38 : block_t :=
    shift_row (usize 2) (usize 2) (state_37) : T _ in 
  shift_row (usize 3) (usize 3) (state_38).
Definition shift_rows_pure_code
  (state_36 : block_t)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (shift_rows_pure state_36).


Program Definition shift_rows_state
  (state_36 : block_t)
  : code (fset ([ out_8_loc])) [interface] (@ct (block_t)) :=
  (({ code  '(state_37 : block_t) ←
        ( temp_39 ←
            (shift_row (usize 1) (usize 1) (state_36)) ;;
          ret temp_39) ;;
       '(state_38 : block_t) ←
        ( temp_40 ←
            (shift_row (usize 2) (usize 2) (state_37)) ;;
          ret temp_40) ;;
       temp_41 ←
        (shift_row (usize 3) (usize 3) (state_38)) ;;
      @pkg_core_definition.ret (block_t) ( (temp_41)) } : code (fset (
          [ out_8_loc])) [interface] _)).
Fail Next Obligation.

Program Definition shift_rows
  (state_36 : block_t)
  : both (fset ([ out_8_loc])) [interface] block_t :=
  {|
  is_pure := shift_rows_pure (state_36 : block_t);
  is_state := shift_rows_state (state_36 : block_t);
  |}.
Next Obligation.
init_both_proof shift_rows_state shift_rows_pure.
step_code. Qed. (* Admitted. *)

Definition xtime_pure (x_42 : uint8) : uint8 :=
  let0 x1_43 : uint8 :=
    ((x_42) shift_left (usize 1)) : T _ in 
  let0 x7_44 : uint8 :=
    ((x_42) shift_right (usize 7)) : T _ in 
  let0 x71_45 : uint8 :=
    ((x7_44) .& (secret (@repr U8 1))) : T _ in 
  let0 x711b_46 : uint8 :=
    ((x71_45) .* (secret (@repr U8 27))) : T _ in 
  ((x1_43) .^ (x711b_46)).
Definition xtime_pure_code
  (x_42 : uint8)
  : code fset.fset0 [interface] (@ct uint8) :=
  lift_to_code (xtime_pure x_42).


Program Definition xtime_state
  (x_42 : uint8)
  : code (fset.fset0) [interface] (@ct (uint8)) :=
  (({ code  '(x1_43 : uint8) ←
        ( temp_47 ← ((x_42) shift_left (usize 1)) ;; ret temp_47) ;;
       '(x7_44 : uint8) ←
        ( temp_48 ← ((x_42) shift_right (usize 7)) ;; ret temp_48) ;;
       '(x71_45 : uint8) ←
        ( '(temp_49 : int8) ←
            (secret (@repr U8 1)) ;;
           temp_50 ←
            ((x7_44) .& (temp_49)) ;;
          ret temp_50) ;;
       '(x711b_46 : uint8) ←
        ( '(temp_51 : int8) ←
            (secret (@repr U8 27)) ;;
           temp_52 ←
            ((x71_45) .* (temp_51)) ;;
          ret temp_52) ;;
       temp_53 ←
        ((x1_43) .^ (x711b_46)) ;;
      @pkg_core_definition.ret (uint8) ( (temp_53)) } : code (
        fset.fset0) [interface] _)).
Fail Next Obligation.

Program Definition xtime (x_42 : uint8) : both (fset.fset0) [interface] uint8 :=
  {|
  is_pure := xtime_pure (x_42 : uint8);
  is_state := xtime_state (x_42 : uint8);
  |}.
Next Obligation.
init_both_proof xtime_state xtime_pure.
step_code. Qed. (* Admitted. *)

Definition mix_column_pure (c_56 : uint_size) (state_57 : block_t) : block_t :=
  let0 i0_58 : uint_size :=
    ((usize 4) .* (c_56)) : T _ in 
  let0 s0_59 : uint8 :=
    array_index (state_57) (i0_58) : T _ in 
  let0 s1_60 : uint8 :=
    array_index (state_57) (((i0_58) .+ (usize 1))) : T _ in 
  let0 s2_61 : uint8 :=
    array_index (state_57) (((i0_58) .+ (usize 2))) : T _ in 
  let0 s3_62 : uint8 :=
    array_index (state_57) (((i0_58) .+ (usize 3))) : T _ in 
  let0 st_54 : block_t :=
    state_57 in 
  let0 tmp_63 : uint8 :=
    ((((((s0_59) .^ (s1_60))) .^ (s2_61))) .^ (s3_62)) : T _ in 
  let0 st_54 :=
    array_upd st_54 (i0_58) (((((s0_59) .^ (tmp_63))) .^ (xtime (((s0_59) .^ (
                s1_60)))))) in 
  let0 st_54 :=
    array_upd st_54 (((i0_58) .+ (usize 1))) (((((s1_60) .^ (tmp_63))) .^ (
          xtime (((s1_60) .^ (s2_61)))))) in 
  let0 st_54 :=
    array_upd st_54 (((i0_58) .+ (usize 2))) (((((s2_61) .^ (tmp_63))) .^ (
          xtime (((s2_61) .^ (s3_62)))))) in 
  let0 st_54 :=
    array_upd st_54 (((i0_58) .+ (usize 3))) (((((s3_62) .^ (tmp_63))) .^ (
          xtime (((s3_62) .^ (s0_59)))))) in 
  st_54.
Definition mix_column_pure_code
  (c_56 : uint_size)
  (state_57 : block_t)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (mix_column_pure c_56 state_57).

Definition st_54_loc : Location :=
  (block_t : choice_type ; 94%nat).
Program Definition mix_column_state
  (c_56 : uint_size)
  (state_57 : block_t)
  : code (fset ([ st_54_loc])) [interface] (@ct (block_t)) :=
  (({ code  '(i0_58 : uint_size) ←
        ( temp_64 ← ((usize 4) .* (c_56)) ;; ret temp_64) ;;
       '(s0_59 : uint8) ←
        ( temp_65 ← (array_index (state_57) (i0_58)) ;; ret temp_65) ;;
       '(s1_60 : uint8) ←
        ( temp_66 ←
            ((i0_58) .+ (usize 1)) ;;
           temp_67 ←
            (array_index (state_57) (temp_66)) ;;
          ret temp_67) ;;
       '(s2_61 : uint8) ←
        ( temp_68 ←
            ((i0_58) .+ (usize 2)) ;;
           temp_69 ←
            (array_index (state_57) (temp_68)) ;;
          ret temp_69) ;;
       '(s3_62 : uint8) ←
        ( temp_70 ←
            ((i0_58) .+ (usize 3)) ;;
           temp_71 ←
            (array_index (state_57) (temp_70)) ;;
          ret temp_71) ;;
      #put st_54_loc := 
        (state_57) ;;
      '(st_54 : block_t) ← get st_54_loc ;;
       '(tmp_63 : uint8) ←
        ( temp_72 ←
            ((s0_59) .^ (s1_60)) ;;
           temp_73 ←
            ((temp_72) .^ (s2_61)) ;;
           temp_74 ←
            ((temp_73) .^ (s3_62)) ;;
          ret temp_74) ;;
       '(st_54 : block_t) ←
        ( temp_75 ←
            ((s0_59) .^ (tmp_63)) ;;
           temp_76 ←
            ((s0_59) .^ (s1_60)) ;;
           temp_77 ←
            (xtime (temp_76)) ;;
           temp_78 ←
            ((temp_75) .^ (temp_77)) ;;
          ret (array_upd st_54 (i0_58) (temp_78))) ;;
      
       '(st_54 : block_t) ←
        ( temp_79 ←
            ((i0_58) .+ (usize 1)) ;;
           temp_80 ←
            ((s1_60) .^ (tmp_63)) ;;
           temp_81 ←
            ((s1_60) .^ (s2_61)) ;;
           temp_82 ←
            (xtime (temp_81)) ;;
           temp_83 ←
            ((temp_80) .^ (temp_82)) ;;
          ret (array_upd st_54 (temp_79) (temp_83))) ;;
      
       '(st_54 : block_t) ←
        ( temp_84 ←
            ((i0_58) .+ (usize 2)) ;;
           temp_85 ←
            ((s2_61) .^ (tmp_63)) ;;
           temp_86 ←
            ((s2_61) .^ (s3_62)) ;;
           temp_87 ←
            (xtime (temp_86)) ;;
           temp_88 ←
            ((temp_85) .^ (temp_87)) ;;
          ret (array_upd st_54 (temp_84) (temp_88))) ;;
      
       '(st_54 : block_t) ←
        ( temp_89 ←
            ((i0_58) .+ (usize 3)) ;;
           temp_90 ←
            ((s3_62) .^ (tmp_63)) ;;
           temp_91 ←
            ((s3_62) .^ (s0_59)) ;;
           temp_92 ←
            (xtime (temp_91)) ;;
           temp_93 ←
            ((temp_90) .^ (temp_92)) ;;
          ret (array_upd st_54 (temp_89) (temp_93))) ;;
      
      @pkg_core_definition.ret (block_t) ( (st_54)) } : code (fset (
          [ st_54_loc])) [interface] _)).
Fail Next Obligation.

Program Definition mix_column
  (c_56 : uint_size)
  (state_57 : block_t)
  : both (fset ([ st_54_loc])) [interface] block_t :=
  {|
  is_pure := mix_column_pure (c_56 : uint_size)
  (state_57 : block_t);
  is_state := mix_column_state (c_56 : uint_size)
  (state_57 : block_t);
  |}.
Next Obligation.
init_both_proof mix_column_state mix_column_pure.  
step_code. Qed. (* Admitted. *)

Definition mix_columns_pure (state_95 : block_t) : block_t :=
  let0 state_96 : block_t :=
    mix_column (usize 0) (state_95) : T _ in 
  let0 state_97 : block_t :=
    mix_column (usize 1) (state_96) : T _ in 
  let0 state_98 : block_t :=
    mix_column (usize 2) (state_97) : T _ in 
  mix_column (usize 3) (state_98).
Definition mix_columns_pure_code
  (state_95 : block_t)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (mix_columns_pure state_95).


Program Definition mix_columns_state
  (state_95 : block_t)
  : code (fset ([ st_54_loc])) [interface] (@ct (block_t)) :=
  (({ code  '(state_96 : block_t) ←
        ( temp_99 ← (mix_column (usize 0) (state_95)) ;; ret temp_99) ;;
       '(state_97 : block_t) ←
        ( temp_100 ← (mix_column (usize 1) (state_96)) ;; ret temp_100) ;;
       '(state_98 : block_t) ←
        ( temp_101 ← (mix_column (usize 2) (state_97)) ;; ret temp_101) ;;
       temp_102 ←
        (mix_column (usize 3) (state_98)) ;;
      @pkg_core_definition.ret (block_t) ( (temp_102)) } : code (fset (
          [ st_54_loc])) [interface] _)).
Fail Next Obligation.

Program Definition mix_columns
  (state_95 : block_t)
  : both (fset ([ st_54_loc])) [interface] block_t :=
  {|
  is_pure := mix_columns_pure (state_95 : block_t);
  is_state := mix_columns_state (state_95 : block_t);
  |}.
Next Obligation.
init_both_proof mix_columns_state mix_columns_pure.
step_code. Qed. (* Admitted. *)

Definition add_round_key_pure
  (state_105 : block_t)
  (key_106 : round_key_t)
  : block_t :=
  let0 out_103 : block_t :=
    state_105 in 
  let0 out_103 :=
    Hacspec_Lib_Pre.foldi (usize 0) (blocksize_v) out_103
      (fun i_107 out_103 =>
      let0 out_103 :=
        array_upd out_103 (i_107) (((array_index (out_103) (i_107)) .^ (
              array_index (key_106) (i_107)))) in 
      (out_103)) in 
  out_103.
Definition add_round_key_pure_code
  (state_105 : block_t)
  (key_106 : round_key_t)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (add_round_key_pure state_105 key_106).

Definition out_103_loc : Location :=
  (block_t : choice_type ; 111%nat).
Program Definition add_round_key_state
  (state_105 : block_t)
  (key_106 : round_key_t)
  : code (fset ([ out_103_loc])) [interface] (@ct (block_t)) :=
  (({ code #put out_103_loc := 
        (state_105) ;;
      '(out_103 : block_t) ← get out_103_loc ;;
       out_103 ←
        (foldi (usize 0) (blocksize_v) out_103 (fun i_107 (out_103 : _) =>
            ({ code  '(out_103 : block_t) ←
                ( temp_108 ←
                    (array_index (out_103) (i_107)) ;;
                   temp_109 ←
                    (array_index (key_106) (i_107)) ;;
                   temp_110 ←
                    ((temp_108) .^ (temp_109)) ;;
                  ret (array_upd out_103 (i_107) (temp_110))) ;;
              
              @pkg_core_definition.ret (_) ( ((out_103))) } : code (fset (
                  [ out_103_loc])) [interface] _))) ;;
      
      @pkg_core_definition.ret (block_t) ( (out_103)) } : code (fset (
          [ out_103_loc])) [interface] _)).
Fail Next Obligation.

Program Definition add_round_key
  (state_105 : block_t)
  (key_106 : round_key_t)
  : both (fset ([ out_103_loc])) [interface] block_t :=
  {|
  is_pure := add_round_key_pure (state_105 : block_t)
  (key_106 : round_key_t);
  is_state := add_round_key_state (state_105 : block_t)
  (key_106 : round_key_t);
  |}.
Next Obligation.
init_both_proof add_round_key_state add_round_key_pure.
step_code. Qed. (* Admitted. *)

Definition aes_enc_pure
  (state_112 : block_t)
  (round_key_113 : round_key_t)
  : block_t :=
  let0 state_114 : block_t :=
    sub_bytes (state_112) : T _ in 
  let0 state_115 : block_t :=
    shift_rows (state_114) : T _ in 
  let0 state_116 : block_t :=
    mix_columns (state_115) : T _ in 
  add_round_key (state_116) (round_key_113).
Definition aes_enc_pure_code
  (state_112 : block_t)
  (round_key_113 : round_key_t)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (aes_enc_pure state_112 round_key_113).


Program Definition aes_enc_state
  (state_112 : block_t)
  (round_key_113 : round_key_t)
  : code (fset (
      [ out_8_loc ; st_0_loc ; st_54_loc ; out_103_loc])) [interface] (@ct (
      block_t)) :=
  (({ code  '(state_114 : block_t) ←
        ( temp_117 ← (sub_bytes (state_112)) ;; ret temp_117) ;;
       '(state_115 : block_t) ←
        ( temp_118 ← (shift_rows (state_114)) ;; ret temp_118) ;;
       '(state_116 : block_t) ←
        ( temp_119 ← (mix_columns (state_115)) ;; ret temp_119) ;;
       temp_120 ←
        (add_round_key (state_116) (round_key_113)) ;;
      @pkg_core_definition.ret (block_t) ( (temp_120)) } : code (fset (
          [ out_8_loc ; st_0_loc ; st_54_loc ; out_103_loc])) [interface] _)).
Fail Next Obligation.

(* here *)

Program Definition aes_enc
  (state_112 : block_t)
  (round_key_113 : round_key_t)
  : both (fset (
      [ out_8_loc ; st_0_loc ; st_54_loc ; out_103_loc])) [interface] block_t :=
  {|
  is_pure := aes_enc_pure (state_112 : block_t)
  (round_key_113 : round_key_t);
  is_state := aes_enc_state (state_112 : block_t)
  (round_key_113 : round_key_t);
  |}.
Next Obligation.
init_both_proof aes_enc_state aes_enc_pure.
step_code. Qed. (* Admitted. *)

Definition aes_enc_last_pure
  (state_121 : block_t)
  (round_key_122 : round_key_t)
  : block_t :=
  let0 state_123 : block_t :=
    sub_bytes (state_121) : T _ in 
  let0 state_124 : block_t :=
    shift_rows (state_123) : T _ in 
  add_round_key (state_124) (round_key_122).
Definition aes_enc_last_pure_code
  (state_121 : block_t)
  (round_key_122 : round_key_t)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (aes_enc_last_pure state_121 round_key_122).


Program Definition aes_enc_last_state
  (state_121 : block_t)
  (round_key_122 : round_key_t)
  : code (fset ([ st_0_loc ; out_8_loc ; out_103_loc])) [interface] (@ct (
      block_t)) :=
  (({ code  '(state_123 : block_t) ←
        ( temp_125 ← (sub_bytes (state_121)) ;; ret temp_125) ;;
       '(state_124 : block_t) ←
        ( temp_126 ← (shift_rows (state_123)) ;; ret temp_126) ;;
       temp_127 ←
        (add_round_key (state_124) (round_key_122)) ;;
      @pkg_core_definition.ret (block_t) ( (temp_127)) } : code (fset (
          [ st_0_loc ; out_8_loc ; out_103_loc])) [interface] _)).
Fail Next Obligation.

(* here *)

Program Definition aes_enc_last
  (state_121 : block_t)
  (round_key_122 : round_key_t)
  : both (fset ([ st_0_loc ; out_8_loc ; out_103_loc])) [interface] block_t :=
  {|
  is_pure := aes_enc_last_pure (state_121 : block_t)
  (round_key_122 : round_key_t);
  is_state := aes_enc_last_state (state_121 : block_t)
  (round_key_122 : round_key_t);
  |}.
Next Obligation.
init_both_proof aes_enc_last_state aes_enc_last_pure.
step_code. Qed. (* Admitted. *)

Definition rounds_aes_pure
  (state_130 : block_t)
  (key_131 : byte_seq)
  : block_t :=
  let0 out_128 : block_t :=
    state_130 in 
  let0 out_128 :=
    Hacspec_Lib_Pre.foldi (usize 0) (seq_num_chunks (key_131) (
          blocksize_v)) out_128
      (fun i_132 out_128 =>
      let0 (_, key_block_133) :=
        seq_get_chunk (key_131) (blocksize_v) (i_132) : (uint_size '× seq uint8
        ) in 
      let0 out_128 :=
        aes_enc (out_128) (array_from_seq (blocksize_v) (key_block_133)) in 
      (out_128)) in 
  out_128.
Definition rounds_aes_pure_code
  (state_130 : block_t)
  (key_131 : byte_seq)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (rounds_aes_pure state_130 key_131).

Definition out_128_loc : Location :=
  (block_t : choice_type ; 138%nat).
Program Definition rounds_aes_state
  (state_130 : block_t)
  (key_131 : byte_seq)
  : code (fset (
      [ out_8_loc ; out_128_loc ; out_103_loc ; st_0_loc ; st_54_loc])) [interface] (
    @ct (block_t)) :=
  (({ code #put out_128_loc := 
        (state_130) ;;
      '(out_128 : block_t) ← get out_128_loc ;;
       temp_134 ←
        (seq_num_chunks (key_131) (blocksize_v)) ;;
       out_128 ←
        (foldi (usize 0) (temp_134) out_128 (fun i_132 (out_128 : block_t) =>
            ({ code  '(_, key_block_133) ←
                ( temp_135 ←
                    (seq_get_chunk (key_131) (blocksize_v) (i_132)) ;;
                  ret temp_135)  ;;
               out_128 ← (temp_136 ←
                      (array_from_seq (blocksize_v) (key_block_133 : seq uint8 )) ;;
               temp_137 ←
                      (aes_enc (out_128) (temp_136)) ;;
                   ret temp_137) ;;
              #put out_128_loc := out_128 ;;
              (* out_128 ← get out_128_loc ;; *)
              
              @pkg_core_definition.ret (_) ( ((out_128))) } : code (fset (
                  [ st_0_loc ; out_8_loc ; out_103_loc ; st_54_loc ; out_128_loc])) [interface] _))) ;;
      
      @pkg_core_definition.ret (block_t) ( (out_128)) } : code (fset (
          [ out_8_loc ; out_128_loc ; out_103_loc ; st_0_loc ; st_54_loc])) [interface] _)).
Fail Next Obligation.

(* here *)

Program Definition rounds_aes
  (state_130 : block_t)
  (key_131 : byte_seq)
  : both (fset (
      [ out_8_loc ; out_128_loc ; out_103_loc ; st_0_loc ; st_54_loc])) [interface] block_t :=
  {|
  is_pure := rounds_aes_pure (state_130 : block_t)
  (key_131 : byte_seq);
  is_state := rounds_aes_state (state_130 : block_t)
  (key_131 : byte_seq);
  |}.
Next Obligation.
init_both_proof rounds_aes_state rounds_aes_pure.

step_code.
set (hi := (seq_num_chunks key_131 blocksize_v)).
destruct_uint_size_as_nat hi. cbn. Lia.lia. rewrite H1. cbn. Lia.lia.
destruct (is_pure (seq_get_chunk key_131 blocksize_v x)).
step_code.
Qed. (* Admitted. *)

Definition block_cipher_aes_pure
  (input_139 : block_t)
  (key_140 : byte_seq)
  (nr_141 : uint_size)
  : block_t :=
  let0 k0_142 : round_key_t :=
    array_from_slice_range (default) (blocksize_v) (key_140) (((
          usize 0,
          usize 16
        ) : prod_ChoiceEquality _ _)) : T _ in 
  let0 k_143 : seq uint8 :=
    seq_from_slice_range (key_140) (((usize 16, ((nr_141) .* (usize 16))
        ) : prod_ChoiceEquality _ _)) : T _ in 
  let0 kn_144 : round_key_t :=
    array_from_slice (default) (blocksize_v) (key_140) (((nr_141) .* (
          usize 16))) (usize 16)  : T _ in 
  let0 state_145 : block_t :=
    add_round_key (input_139) (k0_142)  : T _ in 
  let0 state_146 : block_t :=
    rounds_aes (state_145) (k_143)  : T _ in 
  aes_enc_last (state_146) (kn_144).
Definition block_cipher_aes_pure_code
  (input_139 : block_t)
  (key_140 : byte_seq)
  (nr_141 : uint_size)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (block_cipher_aes_pure input_139 key_140 nr_141).


Program Definition block_cipher_aes_state
  (input_139 : block_t)
  (key_140 : byte_seq)
  (nr_141 : uint_size)
  : code (fset (
      [ st_0_loc ; st_54_loc ; out_8_loc ; out_128_loc ; out_103_loc])) [interface] (
    @ct (block_t)) :=
  (({ code  '(k0_142 : round_key_t) ←
        ( temp_147 ←
            (array_from_slice_range (default) (blocksize_v) (key_140) ((
                  usize 0,
                  usize 16
                ))) ;;
          ret temp_147) ;;
       '(k_143 : seq uint8) ←
        ( temp_148 ←
            ((nr_141) .* (usize 16)) ;;
           temp_149 ←
            (seq_from_slice_range (key_140) ((usize 16, temp_148))) ;;
          ret temp_149) ;;
       '(kn_144 : round_key_t) ←
        ( temp_150 ←
            ((nr_141) .* (usize 16)) ;;
           temp_151 ←
            (array_from_slice (default) (blocksize_v) (key_140) (temp_150) (
                usize 16)) ;;
          ret temp_151) ;;
       '(state_145 : block_t) ←
        ( temp_152 ← (add_round_key (input_139) (k0_142)) ;; ret temp_152) ;;
       '(state_146 : block_t) ←
        ( temp_153 ← (rounds_aes (state_145) (k_143)) ;; ret temp_153) ;;
       temp_154 ←
        (aes_enc_last (state_146) (kn_144)) ;;
      @pkg_core_definition.ret (block_t) ( (temp_154)) } : code (fset (
          [ st_0_loc ; st_54_loc ; out_8_loc ; out_128_loc ; out_103_loc])) [interface] _)).
Fail Next Obligation.

Program Definition block_cipher_aes
  (input_139 : block_t)
  (key_140 : byte_seq)
  (nr_141 : uint_size)
  : both (fset (
      [ st_0_loc ; st_54_loc ; out_8_loc ; out_128_loc ; out_103_loc])) [interface] block_t :=
  {|
  is_pure := block_cipher_aes_pure (input_139 : block_t)
  (key_140 : byte_seq)
  (nr_141 : uint_size);
  is_state := block_cipher_aes_state (input_139 : block_t)
  (key_140 : byte_seq)
  (nr_141 : uint_size);
  |}.
Next Obligation.
init_both_proof block_cipher_aes_state block_cipher_aes_pure.
step_code.
Qed. (* Admitted. *)

(* here *)

Definition rotate_word_pure (w_155 : word_t) : word_t :=
  array_from_list uint8 (let0 l :=
      [
        (array_index (w_155) (usize 1)) : uint8;
        (array_index (w_155) (usize 2)) : uint8;
        (array_index (w_155) (usize 3)) : uint8;
        (array_index (w_155) (usize 0)) : uint8
      ] in  l).
Definition rotate_word_pure_code
  (w_155 : word_t)
  : code fset.fset0 [interface] (@ct word_t) :=
  lift_to_code (rotate_word_pure w_155).


Program Definition rotate_word_state
  (w_155 : word_t)
  : code (fset.fset0) [interface] (@ct (word_t)) :=
  (({ code  temp_156 ←
        (array_index (w_155) (usize 1)) ;;
       temp_157 ←
        (array_index (w_155) (usize 2)) ;;
       temp_158 ←
        (array_index (w_155) (usize 3)) ;;
       temp_159 ←
        (array_index (w_155) (usize 0)) ;;
      @pkg_core_definition.ret (word_t) ( (array_from_list uint8 (let l :=
            ([temp_156; temp_157; temp_158; temp_159]) in
           l))) } : code (fset.fset0) [interface] _)).
Fail Next Obligation.

Program Definition rotate_word
  (w_155 : word_t)
  : both (fset.fset0) [interface] word_t :=
  {|
  is_pure := rotate_word_pure (w_155 : word_t);
  is_state := rotate_word_state (w_155 : word_t);
  |}.
Next Obligation.
init_both_proof rotate_word_state rotate_word_pure.
step_code. Qed. (* Admitted. *)

(* here *)

Definition slice_word_pure (w_160 : word_t) : word_t :=
  array_from_list uint8 (let0 l :=
      [
        (array_index (sbox_v) (declassify_usize_from_uint8 (array_index (
                w_160) (usize 0)))) : uint8;
        (array_index (sbox_v) (declassify_usize_from_uint8 (array_index (
                w_160) (usize 1)))) : uint8;
        (array_index (sbox_v) (declassify_usize_from_uint8 (array_index (
                w_160) (usize 2)))) : uint8;
        (array_index (sbox_v) (declassify_usize_from_uint8 (array_index (
                w_160) (usize 3)))) : uint8
      ] in  l).
Definition slice_word_pure_code
  (w_160 : word_t)
  : code fset.fset0 [interface] (@ct word_t) :=
  lift_to_code (slice_word_pure w_160).


Program Definition slice_word_state
  (w_160 : word_t)
  : code (fset.fset0) [interface] (@ct (word_t)) :=
  (({ code  temp_161 ←
        (array_index (w_160) (usize 0)) ;;
       temp_162 ←
        (declassify_usize_from_uint8 (temp_161)) ;;
       temp_163 ←
        (array_index (sbox_v) (temp_162)) ;;
       temp_164 ←
        (array_index (w_160) (usize 1)) ;;
       temp_165 ←
        (declassify_usize_from_uint8 (temp_164)) ;;
       temp_166 ←
        (array_index (sbox_v) (temp_165)) ;;
       temp_167 ←
        (array_index (w_160) (usize 2)) ;;
       temp_168 ←
        (declassify_usize_from_uint8 (temp_167)) ;;
       temp_169 ←
        (array_index (sbox_v) (temp_168)) ;;
       temp_170 ←
        (array_index (w_160) (usize 3)) ;;
       temp_171 ←
        (declassify_usize_from_uint8 (temp_170)) ;;
       temp_172 ←
        (array_index (sbox_v) (temp_171)) ;;
      @pkg_core_definition.ret (word_t) ( (array_from_list uint8 (let l :=
            ([temp_163; temp_166; temp_169; temp_172]) in
           l))) } : code (fset.fset0) [interface] _)).
Fail Next Obligation.

Program Definition slice_word
  (w_160 : word_t)
  : both (fset.fset0) [interface] word_t :=
  {|
  is_pure := slice_word_pure (w_160 : word_t);
  is_state := slice_word_state (w_160 : word_t);
  |}.
Next Obligation.
init_both_proof slice_word_state slice_word_pure.
step_code. Qed. (* Admitted. *)

(* here *)

Definition aes_keygen_assist_pure
  (w_175 : word_t)
  (rcon_176 : uint8)
  : word_t :=
  let0 k_173 : word_t :=
    rotate_word (w_175) : T _ in 
  let0 k_173 :=
    slice_word (k_173) in 
  let0 k_173 :=
    array_upd k_173 (usize 0) (((array_index (k_173) (usize 0)) .^ (
          rcon_176))) in 
  k_173.
Definition aes_keygen_assist_pure_code
  (w_175 : word_t)
  (rcon_176 : uint8)
  : code fset.fset0 [interface] (@ct word_t) :=
  lift_to_code (aes_keygen_assist_pure w_175 rcon_176).

Definition k_173_loc : Location :=
  (word_t : choice_type ; 181%nat).
Program Definition aes_keygen_assist_state
  (w_175 : word_t)
  (rcon_176 : uint8)
  : code (fset ([ k_173_loc])) [interface] (@ct (word_t)) :=
  (({ code
        temp_177 ← (rotate_word (w_175)) ;;
        #put k_173_loc := temp_177 ;;
                          '(k_173 : word_t) ← get k_173_loc ;;
                          temp_178 ← (slice_word (k_173)) ;;
      #put k_173_loc := 
        ((  temp_178)) ;;
      '(k_173 : word_t) ← get k_173_loc ;;
      
       '(k_173 : word_t) ←
        ( temp_179 ←
            (array_index (k_173) (usize 0)) ;;
           temp_180 ←
            ((temp_179) .^ (rcon_176)) ;;
          ret (array_upd k_173 (usize 0) (temp_180))) ;;
      
      @pkg_core_definition.ret (word_t) ( (k_173)) } : code (fset (
          [ k_173_loc])) [interface] _)).
Fail Next Obligation.

Program Definition aes_keygen_assist
  (w_175 : word_t)
  (rcon_176 : uint8)
  : both (fset ([ k_173_loc])) [interface] word_t :=
  {|
  is_pure := aes_keygen_assist_pure (w_175 : word_t)
  (rcon_176 : uint8);
  is_state := aes_keygen_assist_state (w_175 : word_t)
  (rcon_176 : uint8);
  |}.
Next Obligation.
init_both_proof aes_keygen_assist_state aes_keygen_assist_pure.
step_code. Qed. (* Admitted. *)

(* here *)

Definition key_expansion_word_pure
  (w0_186 : word_t)
  (w1_187 : word_t)
  (i_188 : uint_size)
  (nk_189 : uint_size)
  (nr_190 : uint_size)
  : word_result_t :=
  let0 k_183 : word_t :=
    w1_187 in 
  let0 result_182 : (result int8 word_t) :=
    @Err word_t int8 (invalid_key_expansion_index_v) : T _ in 
  let0 (k_183, result_182) :=
    if (((i_188) <.? (((usize 4) .* (((nr_190) .+ (
                  usize 1))))))):bool_ChoiceEquality then (let0 (k_183) :=
        if (((((i_188) %% (nk_189))) =.? (usize 0))):bool_ChoiceEquality then (
          let0 k_183 :=
            aes_keygen_assist (k_183) (array_index (rcon_v) (((i_188) ./ (
                    nk_189)))) in 
          (k_183 : T _)) else (let0 (k_183) :=
            if (((((nk_189) >.? (usize 6))) && (((((i_188) %% (nk_189))) =.? (
                      usize 4))))):bool_ChoiceEquality then (let0 k_183 :=
                slice_word (k_183) in 
              (k_183 : T _)) else ((k_183)) in 
          (k_183)) in 
      let0 k_183 :=
        Hacspec_Lib_Pre.foldi (usize 0) (usize 4) k_183
          (fun i_191 k_183 =>
          let0 k_183 :=
            array_upd k_183 (i_191) (((array_index (k_183) (i_191)) .^ (
                  array_index (w0_186) (i_191)))) in 
          (k_183)) in 
      let0 result_182 :=
        @Ok word_t int8 (k_183) in 
      ((k_183, result_182) : prod_ChoiceEquality _ _)) else (((k_183, result_182
        ) : prod_ChoiceEquality _ _)) in 
  result_182.
Definition key_expansion_word_pure_code
  (w0_186 : word_t)
  (w1_187 : word_t)
  (i_188 : uint_size)
  (nk_189 : uint_size)
  (nr_190 : uint_size)
  : code fset.fset0 [interface] (@ct word_result_t) :=
  lift_to_code (key_expansion_word_pure w0_186 w1_187 i_188 nk_189 nr_190).

Definition k_183_loc : Location :=
  (word_t : choice_type ; 208%nat).
Definition result_182_loc : Location :=
  ((result int8 word_t) : choice_type ; 209%nat).
Program Definition key_expansion_word_state
  (w0_186 : word_t)
  (w1_187 : word_t)
  (i_188 : uint_size)
  (nk_189 : uint_size)
  (nr_190 : uint_size)
  : code (fset ([ result_182_loc ; k_183_loc ; k_173_loc])) [interface] (@ct (
      word_result_t)) :=
  (({ code #put k_183_loc := 
        (w1_187) ;;
      '(k_183 : word_t) ← get k_183_loc ;;
      #put result_182_loc := 
        (@Err word_t int8 (invalid_key_expansion_index_v)) ;;
      '(result_182 : (result int8 word_t)) ← get result_182_loc ;;
       temp_192 ←
        ((nr_190) .+ (usize 1)) ;;
       temp_193 ←
        ((usize 4) .* (temp_192)) ;;
       temp_194 ←
        ((i_188) <.? (temp_193)) ;;
       '(k_183, result_182) ←
        (if temp_194:bool_ChoiceEquality then (({ code  temp_195 ←
                ((i_188) %% (nk_189)) ;;
               temp_196 ←
                ((temp_195) =.? (usize 0)) ;;
               '(k_183 : word_t) ←
                (if temp_196:bool_ChoiceEquality then ((
                      { code temp_197 ←
                              ((i_188) ./ (nk_189)) ;;
                             temp_198 ←
                              (array_index (rcon_v) (temp_197)) ;;
                             temp_199 ←
                              (aes_keygen_assist (k_183) (temp_198)) ;;
                           #put k_183_loc := 
                        ((  temp_199)) ;;
                      k_183 ← get k_183_loc ;;
                      
                      @pkg_core_definition.ret (_) ( ((k_183))) } : code (fset (
                          [ k_173_loc ; result_182_loc ; k_183_loc])) [interface] _)) else (
                    ({ code  temp_200 ←
                        ((nk_189) >.? (usize 6)) ;;
                       temp_201 ←
                        ((i_188) %% (nk_189)) ;;
                       temp_202 ←
                        ((temp_201) =.? (usize 4)) ;;
                       temp_203 ←
                        ((temp_200) && (temp_202)) ;;
                       '(k_183) ←
                        (if temp_203:bool_ChoiceEquality then ((
                              { code temp_204 ←
                                      (slice_word (k_183)) ;;
                                    #put k_183_loc := 
                                ((  temp_204)) ;;
                              k_183 ← get k_183_loc ;;
                              
                              @pkg_core_definition.ret (_) ( ((k_183
                                ))) } : code (fset (
                                  [ result_182_loc ; k_183_loc])) [interface] _)) else (
                            @pkg_core_definition.ret (_) ( ((k_183))))) ;;
                      
                      @pkg_core_definition.ret (_) ( ((k_183))) } : code (fset (
                          [ result_182_loc ; k_183_loc])) [interface] _))) ;;
              
               k_183 ←
                (foldi (usize 0) (usize 4) k_183 (fun i_191 (k_183 : _) =>
                    ({ code  '(k_183 : word_t) ←
                        ( temp_205 ←
                            (array_index (k_183) (i_191)) ;;
                           temp_206 ←
                            (array_index (w0_186) (i_191)) ;;
                           temp_207 ←
                            ((temp_205) .^ (temp_206)) ;;
                          ret (array_upd k_183 (i_191) (temp_207))) ;;
                      
                      @pkg_core_definition.ret (_) ( ((k_183))) } : code (fset (
                          [ result_182_loc ; k_173_loc ; k_183_loc])) [interface] _))) ;;
              
              #put result_182_loc := 
                ((@Ok word_t int8 (k_183))) ;;
              result_182 ← get result_182_loc ;;
              
              @pkg_core_definition.ret (prod_ChoiceEquality word_t word_result_t) ( ((k_183, result_182))) } : code (
                fset (
                  [ k_183_loc ; result_182_loc ; k_173_loc])) [interface] _)) else (
            @pkg_core_definition.ret (_) ( ((k_183, result_182))))) ;;
      
      @pkg_core_definition.ret ((result int8 word_t)) ( (result_182)) } : code (
        fset ([ result_182_loc ; k_183_loc ; k_173_loc])) [interface] _)).
Fail Next Obligation.

(* here *)

Program Definition key_expansion_word
  (w0_186 : word_t)
  (w1_187 : word_t)
  (i_188 : uint_size)
  (nk_189 : uint_size)
  (nr_190 : uint_size)
  : both (fset (
      [ result_182_loc ; k_183_loc ; k_173_loc])) [interface] word_result_t :=
  {|
  is_pure := key_expansion_word_pure (w0_186 : word_t)
  (w1_187 : word_t)
  (i_188 : uint_size)
  (nk_189 : uint_size)
  (nr_190 : uint_size);
  is_state := key_expansion_word_state (w0_186 : word_t)
  (w1_187 : word_t)
  (i_188 : uint_size)
  (nk_189 : uint_size)
  (nr_190 : uint_size);
  |}.
Next Obligation.
init_both_proof key_expansion_word_state key_expansion_word_pure.
step_code.
destruct (is_pure _).
- unfold prog.
  (rewrite bind_assoc).
  step_code.
  (rewrite bind_assoc).
  step_code.
  (rewrite bind_assoc).

  set ((is_pure (i_188 %% nk_189) =.? usize 0)).
  replace (is_pure (i_188 %% nk_189) =.? usize 0) with b by reflexivity.
  destruct (is_pure b).
  + repeat (rewrite bind_assoc ; step_code).
    unfold bind at 1.
    step_code.
    (rewrite bind_assoc).
    step_code.
    unfold bind at 1.
    step_code.
    repeat (rewrite bind_assoc ; step_code).
    set (is_pure
           (is_pure (nk_189 >.? usize 6) &&
              is_pure (is_pure (i_188 %% nk_189) =.? usize 4))).
    replace (is_pure
               (is_pure (nk_189 >.? usize 6) &&
                  is_pure (is_pure (i_188 %% nk_189) =.? usize 4))) with t by reflexivity.
    destruct t.
    * repeat (rewrite bind_assoc ; step_code).
      unfold bind at 1.
      step_code.
      rewrite bind_assoc.
      step_code.
      unfold bind at 1.
      step_code.
      rewrite bind_rewrite.

      repeat (rewrite bind_assoc ; step_code).
      unfold bind at 1.
      step_code.
      rewrite bind_rewrite.
      step_code.
Qed. (* Admitted. *)

(* here *)

Definition key_expansion_aes_pure
  (key_212 : byte_seq)
  (nk_213 : uint_size)
  (nr_214 : uint_size)
  (key_schedule_length_215 : uint_size)
  (key_length_216 : uint_size)
  (iterations_217 : uint_size)
  : byte_seq_result_t :=
  let0 key_ex_210 : seq uint8 :=
    seq_new_ (default) (key_schedule_length_215) : T _ in 
  let0 key_ex_210 :=
    seq_update_start (key_ex_210) (key_212) in 
  let0 word_size_218 : uint_size :=
    key_length_216 in 
  (key_ex_210 m( _ ) ⇠ (foldibnd (usize 0) to (
      iterations_217) M( _ ) for key_ex_210 >> (fun j_219 key_ex_210 =>
    let0 i_220 : uint_size :=
      ((j_219) .+ (word_size_218)): T _  in 
     (word_221 m( _ ) ⇠ (key_expansion_word (array_from_slice (default) (
          key_length_v) (key_ex_210) (((usize 4) .* (((i_220) .- (
                  word_size_218))))) (usize 4)) (array_from_slice (default) (
          key_length_v) (key_ex_210) (((((usize 4) .* (i_220))) .- (usize 4))) (
          usize 4)) (i_220) (nk_213) (nr_214)) ;;
    (let0 key_ex_210 :=
        seq_update (key_ex_210) (((usize 4) .* (i_220))) (
          array_to_seq (word_221)) in 
      Ok ((key_ex_210)))))) ;;
  (@Ok byte_seq int8 (key_ex_210))).
Definition key_expansion_aes_pure_code
  (key_212 : byte_seq)
  (nk_213 : uint_size)
  (nr_214 : uint_size)
  (key_schedule_length_215 : uint_size)
  (key_length_216 : uint_size)
  (iterations_217 : uint_size)
  : code fset.fset0 [interface] (@ct byte_seq_result_t) :=
  lift_to_code (key_expansion_aes_pure key_212
    nk_213
    nr_214
    key_schedule_length_215
    key_length_216
    iterations_217).

Definition key_ex_210_loc : Location :=
  (seq uint8 : choice_type ; 235%nat).
Program Definition key_expansion_aes_state
  (key_212 : byte_seq)
  (nk_213 : uint_size)
  (nr_214 : uint_size)
  (key_schedule_length_215 : uint_size)
  (key_length_216 : uint_size)
  (iterations_217 : uint_size)
  : code (fset (
      [ result_182_loc ; key_ex_210_loc ; k_183_loc ; k_173_loc])) [interface] (
    @ct (byte_seq_result_t)) :=
  (({ code temp_222 ←
            (seq_new_ (default) (key_schedule_length_215)) ;;
           #put key_ex_210_loc := 
        ( temp_222) ;;
      '(key_ex_210 : seq uint8) ← get key_ex_210_loc ;;
      temp_223 ←
              (seq_update_start (key_ex_210) (key_212)) ;;
           #put key_ex_210_loc := 
        ((  temp_223)) ;;
      '(key_ex_210 : seq uint8) ← get key_ex_210_loc ;;
      
       '(word_size_218 : uint_size) ←
        (ret key_length_216) ;;
       ChoiceEqualityMonad.bind_code (A := byte_seq) (B := byte_seq) (L1 := [ ]) (L2 := [ result_182_loc ; key_ex_210_loc ; k_183_loc ; k_173_loc]) (mnd_combined := ChoiceEqualityMonad.result_code_monad _ _ int8) (H_incl := ltac:(incl_compute)) (
        foldi_bind_code (A := byte_seq) (L1 := [ k_173_loc ; k_183_loc ; key_ex_210_loc ; result_182_loc]) (L2 := [ result_182_loc ; key_ex_210_loc ; k_183_loc ; k_173_loc]) (mnd_combined := ChoiceEqualityMonad.result_code_monad _ _ int8) (H_incl := ltac:(incl_compute))  (
          usize 0) (iterations_217) (Ok key_ex_210) (fun j_219 key_ex_210 =>
        ({ code  '(i_220 : uint_size) ←
            ( temp_224 ← ((j_219) .+ (word_size_218)) ;; ret temp_224) ;;
          ChoiceEqualityMonad.bind_code (A := word_t) (B := byte_seq) (L1 := [ key_ex_210_loc ]) (L2 := [ k_173_loc ; k_183_loc ; key_ex_210_loc ; result_182_loc]) (mnd_combined := ChoiceEqualityMonad.result_code_monad _ _ int8) (H_incl := ltac:(incl_compute)) (
            ({ code  temp_225 ←
                ((i_220) .- (word_size_218)) ;;
               temp_226 ←
                ((usize 4) .* (temp_225)) ;;
               temp_227 ←
                (array_from_slice (default) (key_length_v) (key_ex_210) (
                    temp_226) (usize 4)) ;;
               temp_228 ←
                ((usize 4) .* (i_220)) ;;
               temp_229 ←
                ((temp_228) .- (usize 4)) ;;
               temp_230 ←
                (array_from_slice (default) (key_length_v) (key_ex_210) (
                    temp_229) (usize 4)) ;;
               temp_231 ←
                (key_expansion_word (temp_227) (temp_230) (i_220) (nk_213) (
                    nr_214)) ;;
              @pkg_core_definition.ret _ temp_231 } : code _ [interface] _)) (
            fun word_221 => ({ code temp_232 ←
                      ((usize 4) .* (i_220)) ;;
                     '(temp_233 : seq uint8) ←
                      (array_to_seq (word_221)) ;;
                     temp_234 ←
                      (seq_update (key_ex_210) (temp_232) (temp_233)) ;;
                   #put key_ex_210_loc := 
                ((  temp_234)) ;;
              '(key_ex_210 : seq uint8) ← get key_ex_210_loc ;;
              
              @pkg_core_definition.ret (_) ( (Ok ((key_ex_210
                  )))) } : code _ [interface] _)) } : code (fset (
              [ k_173_loc ; k_183_loc ; key_ex_210_loc ; result_182_loc])) [interface] _))) (
        fun key_ex_210 => ({ code @pkg_core_definition.ret ((
              result int8 byte_seq)) ( (@Ok byte_seq int8 (
              key_ex_210))) } : code _ [interface] _)) } : code (fset (
                                                                     [ result_182_loc ; key_ex_210_loc ; k_183_loc ; k_173_loc])) [interface] _)).
Fail Next Obligation.

(* here *)

Program Definition key_expansion_aes
  (key_212 : byte_seq)
  (nk_213 : uint_size)
  (nr_214 : uint_size)
  (key_schedule_length_215 : uint_size)
  (key_length_216 : uint_size)
  (iterations_217 : uint_size)
  : both (fset (
      [ result_182_loc ; key_ex_210_loc ; k_183_loc ; k_173_loc])) [interface] byte_seq_result_t :=
  {|
  is_pure := key_expansion_aes_pure (key_212 : byte_seq)
  (nk_213 : uint_size)
  (nr_214 : uint_size)
  (key_schedule_length_215 : uint_size)
  (key_length_216 : uint_size)
  (iterations_217 : uint_size);
  is_state := key_expansion_aes_state (key_212 : byte_seq)
  (nk_213 : uint_size)
  (nr_214 : uint_size)
  (key_schedule_length_215 : uint_size)
  (key_length_216 : uint_size)
  (iterations_217 : uint_size);
  |}.
Next Obligation.
init_both_proof key_expansion_aes_state key_expansion_aes_pure.
(clear_bind || progress_step_code).
(clear_bind || progress_step_code).
(clear_bind || progress_step_code).
(clear_bind || progress_step_code).
(clear_bind || progress_step_code).
match goal with
  | [ |- context [ ⊢ ⦃ _ ⦄ _ ≈ ?os ⦃ ?Q ⦄ ] ] =>
      let H := fresh in
      let HQ := fresh in
      set (H := os)
      ; set (HQ := Q)
      ; subst H
      ; unfold let_ at 1
      ; subst HQ
      ; unfold let_ at 1
end.
(clear_bind || progress_step_code).
(clear_bind || progress_step_code).


match goal with
| [ |- context [ ⊢ ⦃ _ ⦄ prog (ChoiceEqualityMonad.bind_code (L1 := ?L1)  (L2 := ?L2) (I := ?interface) ?xb ?fb) ≈ ret (T_ct (ChoiceEqualityMonad.bind ?yb ?gb)) ⦃ _ ⦄ ] ] =>
    let Hcode_eq_xy := fresh in
    let Hcode_eq_fg := fresh in
    assert (Hcode_eq_xy : ⊢ ⦃ true_precond ⦄
        xb ≈ lift_to_code (L := fset L1) (I := interface) yb
        ⦃ pre_to_post_ret true_precond (T_ct yb) ⦄) ;
    [ | pose (bind_x := Build_both _ _ _ yb xb Hcode_eq_xy)
        ; assert (Hcode_eq_fg : forall x, ⊢ ⦃ true_precond ⦄
        prog (fb x) ≈ lift_to_code (L := fset L2) (I := interface) (gb x)
        ⦃ pre_to_post_ret true_precond (T_ct (gb x)) ⦄) ;
    [ | pose (bind_f := fun x => Build_both _ _ _ (gb x) (fb x) (Hcode_eq_fg x)) ]
    ]
end.

match goal with
| [ |- context [ ⊢ ⦃ _ ⦄ prog (@foldi_bind_code ?A ?L1 ?L2 ?I _ _ ?mnd_combined ?H_incl ?lo ?hi ?init_state ?f) ≈ prog (lift_to_code (Hacspec_Lib_Pre.foldi ?lo ?hi ?init_pure ?g)) ⦃ _ ⦄ ] ] =>
    let Hcode_eq_init := fresh in
    let Hcode_eq_fun := fresh in
    let Hcode_bound := fresh in
    let Hcode_through_code := fresh in
    assert (Hcode_eq_init : ⊢ ⦃ true_precond ⦄
                                       prog (lift_to_code (L := fset L2) (I := I) (init_state)) ≈ lift_to_code (L := fset L2) (I := I) (init_pure)
        ⦃ pre_to_post_ret true_precond (T_ct init_pure) ⦄) ;
    [
    | assert (Hcode_eq_fun : forall (x : uint_size) (y : byte_seq), ⊢ ⦃ true_precond ⦄
                                       prog (f x y) ≈ lift_to_code (L := fset L2) (I := I) (g x (Ok y))
        ⦃ pre_to_post_ret true_precond (T_ct (g x (Ok y))) ⦄) ;
    [
    |   assert (H_bound : (unsigned lo <= unsigned hi)%Z) ;
      [ |
        assert (H_through_code : @ChoiceEqualityMonad.bind_through_code L1 L2 I _ _ mnd_combined H_incl) ; [ |
        apply (@foldi_bind_both A L1 L2 H_incl I _ _ mnd_combined H_through_code lo hi H_bound (Build_both _ _ _ init_pure (lift_to_code (L := fset L2) (I := I) (init_state)) Hcode_eq_init) (fun (x : uint_size) (y : byte_seq) => Build_both _ _ _ (g x (Ok y)) (f x y) (Hcode_eq_fun x y)) ) ] ]
    ]
    ]
end.

step_code.
intros.
unfold prog, lift_to_code.
repeat (rewrite bind_assoc ; step_code).
Set Printing Coercions.

unfold ChoiceEqualityMonad.bind_code.
step_code.

match goal with
| [ |- context [ ⊢ ⦃ _ ⦄ prog (@ChoiceEqualityMonad.bind_code _ _ _ _ _ _ _ _ _ _ _) ≈ ret (T_ct (ChoiceEqualityMonad.bind ?yb ?gb)) ⦃ _ ⦄ ] ] =>
    let H := fresh in
    set (H := os)

    (* ; set yb *)
    (* ; set gb *)
    (* let Hcode_eq_xy := fresh in *)
    (* let Hcode_eq_fg := fresh in *)
    (* assert (Hcode_eq_xy : ⊢ ⦃ true_precond ⦄ *)
    (*     xb ≈ lift_to_code (L := fset L1) (I := interface) yb *)
    (*     ⦃ pre_to_post_ret true_precond (T_ct yb) ⦄) ; *)
    (* [ | pose (bind_x := Build_both _ _ _ yb xb Hcode_eq_xy) *)
    (*     ; assert (Hcode_eq_fg : forall x, ⊢ ⦃ true_precond ⦄ *)
    (*     prog (fb x) ≈ lift_to_code (L := fset L2) (I := interface) (gb x) *)
    (*     ⦃ pre_to_post_ret true_precond (T_ct (gb x)) ⦄) ; *)
    (* [ | pose (bind_f := fun x => Build_both _ _ _ (gb x) (fb x) (Hcode_eq_fg x)) ] *)
    (* ] *)
end.
pattern () in H0.
Set Printing All.
Set Printing Implicit.

specialize b with (lo := t) (hi := t0).


specialize b with (init := t2).

@foldi_bind_code A L1 L2 I _ _ mnd_combined H_incl a b init (fun x y => @lift_to_code (M A) (fset L1) I (f x y)) ;
{A : ChoiceEquality} {L1 L2 : list Location} (H_incl : List.incl L1 L2) {I} `{ChoiceEqualityMonad.CEMonad} `{mnd_combined : @ChoiceEqualityMonad.CEMonad (fun x : ChoiceEquality => code_ChoiceEquality (fset L2) I (ct (M x)))} `{@ChoiceEqualityMonad.bind_through_code L1 L2 I _ _ mnd_combined H_incl} (a : uint_size) (b : uint_size) (f : uint_size -> A -> M A) (init : M A) `((unsigned a <= unsigned b)%Z)
                     
apply (foldi_bind_both (usize 0) iterations_217 _).
apply foldi_both.

pose (bind_both [interface] (bind_x _) (bind_f _)).    

apply bind_both.

unfold ChoiceEqualityMonad.bind_code.
unfold ChoiceEqualityMonad.bind.
unfold ChoiceEqualityMonad.result_code_monad.
unfold ChoiceEqualityMonad.ComposeProd.
unfold ChoiceEqualityMonad.CEMonad2ToCEMonad.
unfold ChoiceEqualityMonad.join.
unfold ChoiceEqualityMonad.fmap.
unfold ChoiceEqualityMonad.ComposeProd2.
unfold ChoiceEqualityMonad.fmap.
unfold ChoiceEqualityMonad.join.
unfold ChoiceEqualityMonad.CEMonadToCEMonad2.

unfold ChoiceEqualityMonad.bind.
unfold ChoiceEqualityMonad.code_monad.
unfold prog.

unfold ChoiceEqualityMonad.result_monad.
unfold ChoiceEqualityMonad.result_bind.

rewrite bind_assoc.
rewrite bind_assoc.

(clear_bind || progress_step_code).


step_code.



unfold ChoiceEqualityMonad.bind_code.
step_code.
unfold foldi_bind_code.
step_code.

Qed. (* Admitted. *)

Definition aes_encrypt_block_pure
  (k_236 : byte_seq)
  (input_237 : block_t)
  (nk_238 : uint_size)
  (nr_239 : uint_size)
  (key_schedule_length_240 : uint_size)
  (key_length_241 : uint_size)
  (iterations_242 : uint_size)
  : block_result_t :=
   key_ex_243 m( _ ) ⇠ (key_expansion_aes (k_236) (nk_238) (nr_239) (
      key_schedule_length_240) (key_length_241) (iterations_242)) ;;
  (@Ok block_t int8 (block_cipher_aes (input_237) (key_ex_243) (nr_239))).
Definition aes_encrypt_block_pure_code
  (k_236 : byte_seq)
  (input_237 : block_t)
  (nk_238 : uint_size)
  (nr_239 : uint_size)
  (key_schedule_length_240 : uint_size)
  (key_length_241 : uint_size)
  (iterations_242 : uint_size)
  : code fset.fset0 [interface] (@ct block_result_t) :=
  lift_to_code (aes_encrypt_block_pure k_236
    input_237
    nk_238
    nr_239
    key_schedule_length_240
    key_length_241
    iterations_242).


Program Definition aes_encrypt_block_state
  (k_236 : byte_seq)
  (input_237 : block_t)
  (nk_238 : uint_size)
  (nr_239 : uint_size)
  (key_schedule_length_240 : uint_size)
  (key_length_241 : uint_size)
  (iterations_242 : uint_size)
  : code (fset (
      [ out_128_loc ; k_173_loc ; k_183_loc ; st_54_loc ; st_0_loc ; out_8_loc ; result_182_loc ; key_ex_210_loc ; out_103_loc])) [interface] (
    @ct (block_result_t)) :=
  ((
      { code ChoiceEqualityMonad.bind_code (A := byte_seq) (B := block_t) (L1 := [ out_128_loc ; st_54_loc ; st_0_loc ; out_8_loc ; out_103_loc]) (L2 := [ out_128_loc ; k_173_loc ; k_183_loc ; st_54_loc ; st_0_loc ; out_8_loc ; result_182_loc ; key_ex_210_loc ; out_103_loc]) (mnd_combined := ChoiceEqualityMonad.result_code_monad _ _ int8) (H_incl := ltac:(incl_compute)) (
        ({ code  temp_244 ←
            (key_expansion_aes (k_236) (nk_238) (nr_239) (
                key_schedule_length_240) (key_length_241) (iterations_242)) ;;
          @pkg_core_definition.ret _ temp_244 } : code _ [interface] _)) (
        fun key_ex_243 => ({ code  temp_245 ←
            (block_cipher_aes (input_237) (key_ex_243) (nr_239)) ;;
          @pkg_core_definition.ret ((result int8 block_t)) ( (@Ok block_t int8 (
              temp_245))) } : code _ [interface] _)) } : code (fset (
          [ out_128_loc ; k_173_loc ; k_183_loc ; st_54_loc ; st_0_loc ; out_8_loc ; result_182_loc ; key_ex_210_loc ; out_103_loc])) [interface] _)).
Fail Next Obligation.

Program Definition aes_encrypt_block
  (k_236 : byte_seq)
  (input_237 : block_t)
  (nk_238 : uint_size)
  (nr_239 : uint_size)
  (key_schedule_length_240 : uint_size)
  (key_length_241 : uint_size)
  (iterations_242 : uint_size)
  : both (fset (
      [ out_128_loc ; k_173_loc ; k_183_loc ; st_54_loc ; st_0_loc ; out_8_loc ; result_182_loc ; key_ex_210_loc ; out_103_loc])) [interface] block_result_t :=
  {|
  is_pure := aes_encrypt_block_pure (k_236 : byte_seq)
  (input_237 : block_t)
  (nk_238 : uint_size)
  (nr_239 : uint_size)
  (key_schedule_length_240 : uint_size)
  (key_length_241 : uint_size)
  (iterations_242 : uint_size);
  is_state := aes_encrypt_block_state (k_236 : byte_seq)
  (input_237 : block_t)
  (nk_238 : uint_size)
  (nr_239 : uint_size)
  (key_schedule_length_240 : uint_size)
  (key_length_241 : uint_size)
  (iterations_242 : uint_size);
  |}.
Next Obligation.
init_both_proof aes_encrypt_block_state aes_encrypt_block_pure.
step_code. Qed. (* Admitted. *)

Definition aes128_encrypt_block_pure
  (k_246 : key128_t)
  (input_247 : block_t)
  : block_t :=
  result_unwrap (aes_encrypt_block (seq_from_seq (array_to_seq (k_246))) (
      input_247) (key_length_v) (rounds_v) (key_schedule_length_v) (
      key_length_v) (iterations_v)).
Definition aes128_encrypt_block_pure_code
  (k_246 : key128_t)
  (input_247 : block_t)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (aes128_encrypt_block_pure k_246 input_247).


Program Definition aes128_encrypt_block_state
  (k_246 : key128_t)
  (input_247 : block_t)
  : code (fset (
      [ st_0_loc ; k_183_loc ; key_ex_210_loc ; k_173_loc ; out_103_loc ; result_182_loc ; out_8_loc ; out_128_loc ; st_54_loc])) [interface] (
    @ct (block_t)) :=
  (({ code  '(temp_248 : seq uint8) ←
        (array_to_seq (k_246)) ;;
       temp_249 ←
        (seq_from_seq (temp_248)) ;;
       temp_250 ←
        (aes_encrypt_block (temp_249) (input_247) (key_length_v) (rounds_v) (
            key_schedule_length_v) (key_length_v) (iterations_v)) ;;
       temp_251 ←
        (result_unwrap (temp_250)) ;;
      @pkg_core_definition.ret (block_t) ( (temp_251)) } : code (fset (
          [ st_0_loc ; k_183_loc ; key_ex_210_loc ; k_173_loc ; out_103_loc ; result_182_loc ; out_8_loc ; out_128_loc ; st_54_loc])) [interface] _)).
Fail Next Obligation.

Program Definition aes128_encrypt_block
  (k_246 : key128_t)
  (input_247 : block_t)
  : both (fset (
      [ st_0_loc ; k_183_loc ; key_ex_210_loc ; k_173_loc ; out_103_loc ; result_182_loc ; out_8_loc ; out_128_loc ; st_54_loc])) [interface] block_t :=
  {|
  is_pure := aes128_encrypt_block_pure (k_246 : key128_t)
  (input_247 : block_t);
  is_state := aes128_encrypt_block_state (k_246 : key128_t)
  (input_247 : block_t);
  |}.
Next Obligation.
init_both_proof aes128_encrypt_block_state aes128_encrypt_block_pure.
step_code. Qed. (* Admitted. *)

Definition aes_ctr_key_block_pure
  (k_254 : byte_seq)
  (n_255 : aes_nonce_t)
  (c_256 : uint32)
  (nk_257 : uint_size)
  (nr_258 : uint_size)
  (key_schedule_length_259 : uint_size)
  (key_length_260 : uint_size)
  (iterations_261 : uint_size)
  : block_result_t :=
  let0 input_252 : block_t :=
    array_new_ (default) (blocksize_v) in 
  let0 input_252 :=
    array_update (input_252) (usize 0) (array_to_seq (n_255)) in 
  let0 input_252 :=
    array_update (input_252) (usize 12) (array_to_seq (uint32_to_be_bytes (
        c_256))) in 
  aes_encrypt_block (k_254) (input_252) (nk_257) (nr_258) (
    key_schedule_length_259) (key_length_260) (iterations_261).
Definition aes_ctr_key_block_pure_code
  (k_254 : byte_seq)
  (n_255 : aes_nonce_t)
  (c_256 : uint32)
  (nk_257 : uint_size)
  (nr_258 : uint_size)
  (key_schedule_length_259 : uint_size)
  (key_length_260 : uint_size)
  (iterations_261 : uint_size)
  : code fset.fset0 [interface] (@ct block_result_t) :=
  lift_to_code (aes_ctr_key_block_pure k_254
    n_255
    c_256
    nk_257
    nr_258
    key_schedule_length_259
    key_length_260
    iterations_261).

Definition input_252_loc : Location :=
  (block_t : choice_type ; 269%nat).
Program Definition aes_ctr_key_block_state
  (k_254 : byte_seq)
  (n_255 : aes_nonce_t)
  (c_256 : uint32)
  (nk_257 : uint_size)
  (nr_258 : uint_size)
  (key_schedule_length_259 : uint_size)
  (key_length_260 : uint_size)
  (iterations_261 : uint_size)
  : code (fset (
      [ st_0_loc ; out_103_loc ; result_182_loc ; st_54_loc ; k_183_loc ; input_252_loc ; out_8_loc ; out_128_loc ; key_ex_210_loc ; k_173_loc])) [interface] (
    @ct (block_result_t)) :=
  (({ code #put input_252_loc := 
        ( temp_262 ← (array_new_ (default) (blocksize_v)) ;; temp_262) ;;
      '(input_252 : block_t) ← get input_252_loc ;;
      #put input_252_loc := 
        (( '(temp_263 : seq uint8) ←
              (array_to_seq (n_255)) ;;
             temp_264 ←
              (array_update (input_252) (usize 0) (temp_263)) ;;
            temp_264)) ;;
      input_252 ← get input_252_loc ;;
      
      #put input_252_loc := 
        (( temp_265 ←
              (uint32_to_be_bytes (c_256)) ;;
             '(temp_266 : seq uint8) ←
              (array_to_seq (temp_265)) ;;
             temp_267 ←
              (array_update (input_252) (usize 12) (temp_266)) ;;
            temp_267)) ;;
      input_252 ← get input_252_loc ;;
      
       temp_268 ←
        (aes_encrypt_block (k_254) (input_252) (nk_257) (nr_258) (
            key_schedule_length_259) (key_length_260) (iterations_261)) ;;
      @pkg_core_definition.ret (block_result_t) ( (temp_268)) } : code (fset (
          [ st_0_loc ; out_103_loc ; result_182_loc ; st_54_loc ; k_183_loc ; input_252_loc ; out_8_loc ; out_128_loc ; key_ex_210_loc ; k_173_loc])) [interface] _)).
Fail Next Obligation.

Program Definition aes_ctr_key_block
  (k_254 : byte_seq)
  (n_255 : aes_nonce_t)
  (c_256 : uint32)
  (nk_257 : uint_size)
  (nr_258 : uint_size)
  (key_schedule_length_259 : uint_size)
  (key_length_260 : uint_size)
  (iterations_261 : uint_size)
  : both (fset (
      [ st_0_loc ; out_103_loc ; result_182_loc ; st_54_loc ; k_183_loc ; input_252_loc ; out_8_loc ; out_128_loc ; key_ex_210_loc ; k_173_loc])) [interface] block_result_t :=
  {|
  is_pure := aes_ctr_key_block_pure (k_254 : byte_seq)
  (n_255 : aes_nonce_t)
  (c_256 : uint32)
  (nk_257 : uint_size)
  (nr_258 : uint_size)
  (key_schedule_length_259 : uint_size)
  (key_length_260 : uint_size)
  (iterations_261 : uint_size);
  is_state := aes_ctr_key_block_state (k_254 : byte_seq)
  (n_255 : aes_nonce_t)
  (c_256 : uint32)
  (nk_257 : uint_size)
  (nr_258 : uint_size)
  (key_schedule_length_259 : uint_size)
  (key_length_260 : uint_size)
  (iterations_261 : uint_size);
  |}.
Next Obligation.
init_both_proof aes_ctr_key_block_state aes_ctr_key_block_pure.
step_code. Qed. (* Admitted. *)

Definition xor_block_pure
  (block_272 : block_t)
  (key_block_273 : block_t)
  : block_t :=
  let0 out_270 : block_t :=
    block_272 in 
  let0 out_270 :=
    Hacspec_Lib_Pre.foldi (usize 0) (blocksize_v) out_270
      (fun i_274 out_270 =>
      let0 out_270 :=
        array_upd out_270 (i_274) (((array_index (out_270) (i_274)) .^ (
              array_index (key_block_273) (i_274)))) in 
      (out_270)) in 
  out_270.
Definition xor_block_pure_code
  (block_272 : block_t)
  (key_block_273 : block_t)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (xor_block_pure block_272 key_block_273).

Definition out_270_loc : Location :=
  (block_t : choice_type ; 278%nat).
Program Definition xor_block_state
  (block_272 : block_t)
  (key_block_273 : block_t)
  : code (fset ([ out_270_loc])) [interface] (@ct (block_t)) :=
  (({ code #put out_270_loc := 
        (block_272) ;;
      '(out_270 : block_t) ← get out_270_loc ;;
       out_270 ←
        (foldi (usize 0) (blocksize_v) out_270 (fun i_274 (out_270 : _) =>
            ({ code  '(out_270 : block_t) ←
                ( temp_275 ←
                    (array_index (out_270) (i_274)) ;;
                   temp_276 ←
                    (array_index (key_block_273) (i_274)) ;;
                   temp_277 ←
                    ((temp_275) .^ (temp_276)) ;;
                  ret (array_upd out_270 (i_274) (temp_277))) ;;
              
              @pkg_core_definition.ret (_) ( ((out_270))) } : code (fset (
                  [ out_270_loc])) [interface] _))) ;;
      
      @pkg_core_definition.ret (block_t) ( (out_270)) } : code (fset (
          [ out_270_loc])) [interface] _)).
Fail Next Obligation.

Program Definition xor_block
  (block_272 : block_t)
  (key_block_273 : block_t)
  : both (fset ([ out_270_loc])) [interface] block_t :=
  {|
  is_pure := xor_block_pure (block_272 : block_t)
  (key_block_273 : block_t);
  is_state := xor_block_state (block_272 : block_t)
  (key_block_273 : block_t);
  |}.
Next Obligation.
init_both_proof xor_block_state xor_block_pure.
step_code. Qed. (* Admitted. *)

Definition aes_counter_mode_pure
  (key_283 : byte_seq)
  (nonce_284 : aes_nonce_t)
  (counter_285 : uint32)
  (msg_286 : byte_seq)
  (nk_287 : uint_size)
  (nr_288 : uint_size)
  (key_schedule_length_289 : uint_size)
  (key_length_290 : uint_size)
  (iterations_291 : uint_size)
  : byte_seq_result_t :=
  let0 ctr_280 : uint32 :=
    counter_285 in 
  let0 blocks_out_279 : seq uint8 :=
    seq_new_ (default) (seq_len (msg_286)) in 
  let0 n_blocks_292 : uint_size :=
    seq_num_exact_chunks (msg_286) (blocksize_v) in 
  '(ctr_280, blocks_out_279) m( _ ) ⇠ (foldibnd (usize 0) to (
      n_blocks_292) M( _ ) for (ctr_280, blocks_out_279) >> (fun i_293 '(
      ctr_280,
      blocks_out_279
    ) =>
    let0 msg_block_294 : seq uint8 :=
      seq_get_exact_chunk (msg_286) (blocksize_v) (i_293) in 
     key_block_295 m( _ ) ⇠ (aes_ctr_key_block (key_283) (nonce_284) (
        ctr_280) (nk_287) (nr_288) (key_schedule_length_289) (key_length_290) (
        iterations_291)) ;;
    (let0 blocks_out_279 :=
        seq_set_chunk (blocks_out_279) (blocksize_v) (i_293) (
          array_to_seq (xor_block (array_from_seq (blocksize_v) (
              msg_block_294)) (key_block_295))) in 
      let0 ctr_280 :=
        ((ctr_280) .+ (secret (@repr U32 1))) in 
      Ok (((ctr_280, blocks_out_279) : prod_ChoiceEquality _ _))))) ;;
  (let0 last_block_296 : seq uint8 :=
      seq_get_remainder_chunk (msg_286) (blocksize_v) in 
    let0 last_block_len_297 : uint_size :=
      seq_len (last_block_296) in 
    ifbnd (((last_block_len_297) !=.? (usize 0))) : bool
    thenbnd (let0 last_block_298 : block_t :=
        array_update_start (array_new_ (default) (blocksize_v)) (
          last_block_296) in 
       key_block_299 m( _ ) ⇠ (aes_ctr_key_block (key_283) (nonce_284) (
          ctr_280) (nk_287) (nr_288) (key_schedule_length_289) (
          key_length_290) (iterations_291)) ;;
      (let0 blocks_out_279 :=
          seq_set_chunk (blocks_out_279) (blocksize_v) (n_blocks_292) (
            array_slice_range (xor_block (last_block_298) (key_block_299)) (((
                  usize 0,
                  last_block_len_297
                ) : prod_ChoiceEquality _ _))) in 
        Ok ((blocks_out_279))))
    else ((blocks_out_279)) >> (fun '(blocks_out_279) =>
    @Ok byte_seq int8 (blocks_out_279))).
Definition aes_counter_mode_pure_code
  (key_283 : byte_seq)
  (nonce_284 : aes_nonce_t)
  (counter_285 : uint32)
  (msg_286 : byte_seq)
  (nk_287 : uint_size)
  (nr_288 : uint_size)
  (key_schedule_length_289 : uint_size)
  (key_length_290 : uint_size)
  (iterations_291 : uint_size)
  : code fset.fset0 [interface] (@ct byte_seq_result_t) :=
  lift_to_code (aes_counter_mode_pure key_283
    nonce_284
    counter_285
    msg_286
    nk_287
    nr_288
    key_schedule_length_289
    key_length_290
    iterations_291).

Definition ctr_280_loc : Location :=
  (uint32 : choice_type ; 320%nat).
Definition blocks_out_279_loc : Location :=
  (seq uint8 : choice_type ; 321%nat).
Program Definition aes_counter_mode_state
  (key_283 : byte_seq)
  (nonce_284 : aes_nonce_t)
  (counter_285 : uint32)
  (msg_286 : byte_seq)
  (nk_287 : uint_size)
  (nr_288 : uint_size)
  (key_schedule_length_289 : uint_size)
  (key_length_290 : uint_size)
  (iterations_291 : uint_size)
  : code (fset (
      [ input_252_loc ; result_182_loc ; k_183_loc ; st_0_loc ; out_128_loc ; out_103_loc ; blocks_out_279_loc ; out_8_loc ; k_173_loc ; ctr_280_loc ; st_54_loc ; key_ex_210_loc ; out_270_loc])) [interface] (
    @ct (byte_seq_result_t)) :=
  (({ code #put ctr_280_loc := 
        (counter_285) ;;
      '(ctr_280 : uint32) ← get ctr_280_loc ;;
      #put blocks_out_279_loc := 
        ( temp_300 ←
            (seq_len (msg_286)) ;;
           temp_301 ←
            (seq_new_ (default) (temp_300)) ;;
          temp_301) ;;
      '(blocks_out_279 : seq uint8) ← get blocks_out_279_loc ;;
       '(n_blocks_292 : uint_size) ←
        ( temp_302 ←
            (seq_num_exact_chunks (msg_286) (blocksize_v)) ;;
          ret temp_302) ;;
      ChoiceEqualityMonad.bind_code (A := byte_seq) (B := byte_seq) (L1 := [ ]) (L2 := [ input_252_loc ; result_182_loc ; k_183_loc ; st_0_loc ; out_128_loc ; out_103_loc ; blocks_out_279_loc ; out_8_loc ; k_173_loc ; ctr_280_loc ; st_54_loc ; key_ex_210_loc ; out_270_loc]) (mnd_combined := ChoiceEqualityMonad.result_code_monad _ _ int8) (H_incl := ltac:(incl_compute)) (
        foldi_bind_code (A := byte_seq) (L1 := [ out_270_loc ; blocks_out_279_loc ; ctr_280_loc ; k_183_loc ; out_8_loc ; key_ex_210_loc ; out_103_loc ; k_173_loc ; st_0_loc ; input_252_loc ; result_182_loc ; out_128_loc ; st_54_loc]) (L2 := [ input_252_loc ; result_182_loc ; k_183_loc ; st_0_loc ; out_128_loc ; out_103_loc ; blocks_out_279_loc ; out_8_loc ; k_173_loc ; ctr_280_loc ; st_54_loc ; key_ex_210_loc ; out_270_loc]) (mnd_combined := ChoiceEqualityMonad.result_code_monad _ _ int8) (H_incl := ltac:(incl_compute))  (
          usize 0) (n_blocks_292) (Ok (ctr_280, blocks_out_279)) (fun i_293 '(
          ctr_280,
          blocks_out_279
        ) =>
        ({ code  '(msg_block_294 : seq uint8) ←
            ( temp_303 ←
                (seq_get_exact_chunk (msg_286) (blocksize_v) (i_293)) ;;
              ret temp_303) ;;
          ChoiceEqualityMonad.bind_code (A := block_t) (B := byte_seq) (L1 := [ out_270_loc]) (L2 := [ out_270_loc ; blocks_out_279_loc ; ctr_280_loc ; k_183_loc ; out_8_loc ; key_ex_210_loc ; out_103_loc ; k_173_loc ; st_0_loc ; input_252_loc ; result_182_loc ; out_128_loc ; st_54_loc]) (mnd_combined := ChoiceEqualityMonad.result_code_monad _ _ int8) (H_incl := ltac:(incl_compute)) (
            ({ code  temp_304 ←
                (aes_ctr_key_block (key_283) (nonce_284) (ctr_280) (nk_287) (
                    nr_288) (key_schedule_length_289) (key_length_290) (
                    iterations_291)) ;;
              @pkg_core_definition.ret _ temp_304 } : code _ [interface] _)) (
            fun key_block_295 => ({ code #put blocks_out_279_loc := 
                (( temp_305 ←
                      (array_from_seq (blocksize_v) (msg_block_294)) ;;
                     temp_306 ←
                      (xor_block (temp_305) (key_block_295)) ;;
                     '(temp_307 : seq uint8) ←
                      (array_to_seq (temp_306)) ;;
                     temp_308 ←
                      (seq_set_chunk (blocks_out_279) (blocksize_v) (i_293) (
                          temp_307)) ;;
                    temp_308)) ;;
              blocks_out_279 ← get blocks_out_279_loc ;;
              
              #put ctr_280_loc := 
                (( '(temp_309 : int32) ←
                      (secret (@repr U32 1)) ;;
                     temp_310 ←
                      ((ctr_280) .+ (temp_309)) ;;
                    temp_310)) ;;
              ctr_280 ← get ctr_280_loc ;;
              
              @pkg_core_definition.ret (_) ( (Ok ((ctr_280, blocks_out_279
                  )))) } : code _ [interface] _)) } : code (fset (
              [ out_270_loc ; blocks_out_279_loc ; ctr_280_loc ; k_183_loc ; out_8_loc ; key_ex_210_loc ; out_103_loc ; k_173_loc ; st_0_loc ; input_252_loc ; result_182_loc ; out_128_loc ; st_54_loc])) [interface] _))) (
        fun '(ctr_280, blocks_out_279) => ({ code  '(
              last_block_296 : seq uint8) ←
            ( temp_311 ←
                (seq_get_remainder_chunk (msg_286) (blocksize_v)) ;;
              ret temp_311) ;;
           '(last_block_len_297 : uint_size) ←
            ( temp_312 ← (seq_len (last_block_296)) ;; ret temp_312) ;;
           temp_313 ←
            ((last_block_len_297) !=.? (usize 0)) ;;
          if_bind_code (A := _) (B := _) (M := _) (Lx := [ key_ex_210_loc ; out_270_loc ; out_128_loc ; ctr_280_loc ; st_54_loc ; st_0_loc ; result_182_loc ; input_252_loc ; k_183_loc ; out_8_loc ; blocks_out_279_loc ; out_103_loc ; k_173_loc]) (Ly := []) (L2 := [ input_252_loc ; result_182_loc ; k_183_loc ; st_0_loc ; out_128_loc ; out_103_loc ; blocks_out_279_loc ; out_8_loc ; k_173_loc ; ctr_280_loc ; st_54_loc ; key_ex_210_loc ; out_270_loc]) (it1 := _) (it2 := _) (
            temp_313 : bool_ChoiceEquality)
          (({ code  '(last_block_298 : block_t) ←
                ( temp_314 ←
                    (array_new_ (default) (blocksize_v)) ;;
                   temp_315 ←
                    (array_update_start (temp_314) (last_block_296)) ;;
                  ret temp_315) ;;
              ChoiceEqualityMonad.bind_code (A := block_t) (B := byte_seq) (L1 := [ ]) (L2 := [ key_ex_210_loc ; out_270_loc ; out_128_loc ; ctr_280_loc ; st_54_loc ; st_0_loc ; result_182_loc ; input_252_loc ; k_183_loc ; out_8_loc ; blocks_out_279_loc ; out_103_loc ; k_173_loc]) (mnd_combined := ChoiceEqualityMonad.result_code_monad _ _ int8) (H_incl := ltac:(incl_compute)) (
                ({ code  temp_316 ←
                    (aes_ctr_key_block (key_283) (nonce_284) (ctr_280) (
                        nk_287) (nr_288) (key_schedule_length_289) (
                        key_length_290) (iterations_291)) ;;
                  @pkg_core_definition.ret _ temp_316 } : code _ [interface] _)) (
                fun key_block_299 => ({ code #put blocks_out_279_loc := 
                    (( temp_317 ←
                          (xor_block (last_block_298) (key_block_299)) ;;
                         temp_318 ←
                          (array_slice_range (temp_317) ((
                                usize 0,
                                last_block_len_297
                              ))) ;;
                         temp_319 ←
                          (seq_set_chunk (blocks_out_279) (blocksize_v) (
                              n_blocks_292) (temp_318)) ;;
                        temp_319)) ;;
                  blocks_out_279 ← get blocks_out_279_loc ;;
                  
                  @pkg_core_definition.ret (_) ( (Ok ((blocks_out_279
                      )))) } : code _ [interface] _)) } : code (fset (
                  [ key_ex_210_loc ; out_270_loc ; out_128_loc ; ctr_280_loc ; st_54_loc ; st_0_loc ; result_182_loc ; input_252_loc ; k_183_loc ; out_8_loc ; blocks_out_279_loc ; out_103_loc ; k_173_loc])) [interface] _))
          (({ code  (@pkg_core_definition.ret (_) ( ((blocks_out_279
                  )))) } : code _ [interface] _)) (fun '(blocks_out_279) =>
          ({ code @pkg_core_definition.ret ((result int8 byte_seq)) ( (
              @Ok byte_seq int8 (
                blocks_out_279))) } : code _ [interface] _)) } : code _ [interface] _)) } : code (
        fset (
          [ input_252_loc ; result_182_loc ; k_183_loc ; st_0_loc ; out_128_loc ; out_103_loc ; blocks_out_279_loc ; out_8_loc ; k_173_loc ; ctr_280_loc ; st_54_loc ; key_ex_210_loc ; out_270_loc])) [interface] _)).
Fail Next Obligation.

Program Definition aes_counter_mode
  (key_283 : byte_seq)
  (nonce_284 : aes_nonce_t)
  (counter_285 : uint32)
  (msg_286 : byte_seq)
  (nk_287 : uint_size)
  (nr_288 : uint_size)
  (key_schedule_length_289 : uint_size)
  (key_length_290 : uint_size)
  (iterations_291 : uint_size)
  : both (fset (
      [ input_252_loc ; result_182_loc ; k_183_loc ; st_0_loc ; out_128_loc ; out_103_loc ; blocks_out_279_loc ; out_8_loc ; k_173_loc ; ctr_280_loc ; st_54_loc ; key_ex_210_loc ; out_270_loc])) [interface] byte_seq_result_t :=
  {|
  is_pure := aes_counter_mode_pure (key_283 : byte_seq)
  (nonce_284 : aes_nonce_t)
  (counter_285 : uint32)
  (msg_286 : byte_seq)
  (nk_287 : uint_size)
  (nr_288 : uint_size)
  (key_schedule_length_289 : uint_size)
  (key_length_290 : uint_size)
  (iterations_291 : uint_size);
  is_state := aes_counter_mode_state (key_283 : byte_seq)
  (nonce_284 : aes_nonce_t)
  (counter_285 : uint32)
  (msg_286 : byte_seq)
  (nk_287 : uint_size)
  (nr_288 : uint_size)
  (key_schedule_length_289 : uint_size)
  (key_length_290 : uint_size)
  (iterations_291 : uint_size);
  |}.
Next Obligation.
init_both_proof aes_counter_mode_state aes_counter_mode_pure.
step_code. Qed. (* Admitted. *)

Definition aes128_encrypt_pure
  (key_322 : key128_t)
  (nonce_323 : aes_nonce_t)
  (counter_324 : uint32)
  (msg_325 : byte_seq)
  : byte_seq :=
  result_unwrap (aes_counter_mode (seq_from_seq (array_to_seq (key_322))) (
      nonce_323) (counter_324) (msg_325) (key_length_v) (rounds_v) (
      key_schedule_length_v) (key_length_v) (iterations_v)).
Definition aes128_encrypt_pure_code
  (key_322 : key128_t)
  (nonce_323 : aes_nonce_t)
  (counter_324 : uint32)
  (msg_325 : byte_seq)
  : code fset.fset0 [interface] (@ct byte_seq) :=
  lift_to_code (aes128_encrypt_pure key_322 nonce_323 counter_324 msg_325).


Program Definition aes128_encrypt_state
  (key_322 : key128_t)
  (nonce_323 : aes_nonce_t)
  (counter_324 : uint32)
  (msg_325 : byte_seq)
  : code (fset (
      [ k_183_loc ; out_128_loc ; st_54_loc ; key_ex_210_loc ; out_103_loc ; ctr_280_loc ; blocks_out_279_loc ; out_270_loc ; st_0_loc ; out_8_loc ; result_182_loc ; k_173_loc ; input_252_loc])) [interface] (
    @ct (byte_seq)) :=
  (({ code  '(temp_326 : seq uint8) ←
        (array_to_seq (key_322)) ;;
       temp_327 ←
        (seq_from_seq (temp_326)) ;;
       temp_328 ←
        (aes_counter_mode (temp_327) (nonce_323) (counter_324) (msg_325) (
            key_length_v) (rounds_v) (key_schedule_length_v) (key_length_v) (
            iterations_v)) ;;
       temp_329 ←
        (result_unwrap (temp_328)) ;;
      @pkg_core_definition.ret (seq uint8) ( (temp_329)) } : code (fset (
          [ k_183_loc ; out_128_loc ; st_54_loc ; key_ex_210_loc ; out_103_loc ; ctr_280_loc ; blocks_out_279_loc ; out_270_loc ; st_0_loc ; out_8_loc ; result_182_loc ; k_173_loc ; input_252_loc])) [interface] _)).
Fail Next Obligation.

Program Definition aes128_encrypt
  (key_322 : key128_t)
  (nonce_323 : aes_nonce_t)
  (counter_324 : uint32)
  (msg_325 : byte_seq)
  : both (fset (
      [ k_183_loc ; out_128_loc ; st_54_loc ; key_ex_210_loc ; out_103_loc ; ctr_280_loc ; blocks_out_279_loc ; out_270_loc ; st_0_loc ; out_8_loc ; result_182_loc ; k_173_loc ; input_252_loc])) [interface] byte_seq :=
  {|
  is_pure := aes128_encrypt_pure (key_322 : key128_t)
  (nonce_323 : aes_nonce_t)
  (counter_324 : uint32)
  (msg_325 : byte_seq);
  is_state := aes128_encrypt_state (key_322 : key128_t)
  (nonce_323 : aes_nonce_t)
  (counter_324 : uint32)
  (msg_325 : byte_seq);
  |}.
Next Obligation.
init_both_proof aes128_encrypt_state aes128_encrypt_pure.
step_code. Qed. (* Admitted. *)

Definition aes128_decrypt_pure
  (key_330 : key128_t)
  (nonce_331 : aes_nonce_t)
  (counter_332 : uint32)
  (ctxt_333 : byte_seq)
  : byte_seq :=
  result_unwrap (aes_counter_mode (seq_from_seq (array_to_seq (key_330))) (
      nonce_331) (counter_332) (ctxt_333) (key_length_v) (rounds_v) (
      key_schedule_length_v) (key_length_v) (iterations_v)).
Definition aes128_decrypt_pure_code
  (key_330 : key128_t)
  (nonce_331 : aes_nonce_t)
  (counter_332 : uint32)
  (ctxt_333 : byte_seq)
  : code fset.fset0 [interface] (@ct byte_seq) :=
  lift_to_code (aes128_decrypt_pure key_330 nonce_331 counter_332 ctxt_333).


Program Definition aes128_decrypt_state
  (key_330 : key128_t)
  (nonce_331 : aes_nonce_t)
  (counter_332 : uint32)
  (ctxt_333 : byte_seq)
  : code (fset (
      [ out_103_loc ; ctr_280_loc ; k_183_loc ; k_173_loc ; out_8_loc ; out_128_loc ; out_270_loc ; blocks_out_279_loc ; result_182_loc ; st_54_loc ; input_252_loc ; key_ex_210_loc ; st_0_loc])) [interface] (
    @ct (byte_seq)) :=
  (({ code  '(temp_334 : seq uint8) ←
        (array_to_seq (key_330)) ;;
       temp_335 ←
        (seq_from_seq (temp_334)) ;;
       temp_336 ←
        (aes_counter_mode (temp_335) (nonce_331) (counter_332) (ctxt_333) (
            key_length_v) (rounds_v) (key_schedule_length_v) (key_length_v) (
            iterations_v)) ;;
       temp_337 ←
        (result_unwrap (temp_336)) ;;
      @pkg_core_definition.ret (seq uint8) ( (temp_337)) } : code (fset (
          [ out_103_loc ; ctr_280_loc ; k_183_loc ; k_173_loc ; out_8_loc ; out_128_loc ; out_270_loc ; blocks_out_279_loc ; result_182_loc ; st_54_loc ; input_252_loc ; key_ex_210_loc ; st_0_loc])) [interface] _)).
Fail Next Obligation.

Program Definition aes128_decrypt
  (key_330 : key128_t)
  (nonce_331 : aes_nonce_t)
  (counter_332 : uint32)
  (ctxt_333 : byte_seq)
  : both (fset (
      [ out_103_loc ; ctr_280_loc ; k_183_loc ; k_173_loc ; out_8_loc ; out_128_loc ; out_270_loc ; blocks_out_279_loc ; result_182_loc ; st_54_loc ; input_252_loc ; key_ex_210_loc ; st_0_loc])) [interface] byte_seq :=
  {|
  is_pure := aes128_decrypt_pure (key_330 : key128_t)
  (nonce_331 : aes_nonce_t)
  (counter_332 : uint32)
  (ctxt_333 : byte_seq);
  is_state := aes128_decrypt_state (key_330 : key128_t)
  (nonce_331 : aes_nonce_t)
  (counter_332 : uint32)
  (ctxt_333 : byte_seq);
  |}.
Next Obligation.
init_both_proof aes128_decrypt_state aes128_decrypt_pure.
step_code. Qed. (* Admitted. *)

