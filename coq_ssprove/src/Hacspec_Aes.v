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
  array_from_list uint8 [
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
  ].

Definition rcon_v : r_con_t :=
  array_from_list uint8 [
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
  ].

Definition sub_bytes_pure (state_2 : block_t) : block_t :=
  let st_0 : block_t :=
    state_2 in 
  let st_0 :=
    Hacspec_Lib_Pre.foldi (usize 0) (blocksize_v) st_0
      (fun i_3 st_0 =>
      let st_0 :=
        array_upd st_0 (i_3) (array_index (sbox_v) (uint8_declassify (
              array_index (state_2) (i_3)))) in 
      (st_0)) in 
  st_0.
Definition sub_bytes_pure_code
  (state_2 : block_t)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (sub_bytes_pure state_2).

Definition st_0_loc : ChoiceEqualityLocation :=
  ((block_t ; 10%nat)).
Program Definition sub_bytes_state
  (state_2 : block_t) : code (CEfset ([st_0_loc])) [interface] (@ct (
      block_t)) :=
  (({ code  '(st_0 : block_t) ←
          (ret (state_2)) ;;
        #put st_0_loc := st_0 ;;
       st_0 ←
        (foldi (usize 0) (blocksize_v) st_0 (fun i_3 (st_0 : _) =>
            ({ code  '(st_0 : block_t) ←
                ( temp_5 ←
                    (array_index (state_2) (i_3)) ;;
                   temp_7 ←
                    (uint8_declassify (temp_5)) ;;
                   temp_9 ←
                    (array_index (sbox_v) (temp_7)) ;;
                  ret (array_upd st_0 (i_3) (temp_9))) ;;
              
              @ret (_) (st_0) } : code (CEfset ([st_0_loc])) [interface] _))) ;;
      
      @ret (block_t) (st_0) } : code (CEfset ([st_0_loc])) [interface] _)).
Fail Next Obligation.

Program Definition sub_bytes
  (state_2 : block_t)
  : both (CEfset ([st_0_loc])) [interface] (block_t) :=
  letbm st_0 : block_t loc( st_0_loc ) := lift_to_both0 state_2 in
  letb st_0 :=
    foldi_both' (lift_to_both0 (usize 0)) (
        lift_to_both0 blocksize_v) st_0 (L := (CEfset ([st_0_loc]))) (fun i_3 (
        st_0 : _) =>
      letb st_0 : block_t :=
        array_upd st_0 (lift_to_both0 i_3) (is_pure (array_index (sbox_v) (
              uint8_declassify (array_index (state_2) (lift_to_both0 i_3))))) in
      lift_scope (H_incl := _) (lift_to_both0 st_0)
      ) in
  lift_scope (H_incl := _) (lift_to_both0 st_0)
  .
Fail Next Obligation.

Definition shift_row_pure
  (i_13 : uint_size)
  (shift_14 : uint_size)
  (state_15 : block_t)
  : block_t :=
  let out_11 : block_t :=
    state_15 in 
  let out_11 :=
    array_upd out_11 (i_13) (array_index (state_15) (((i_13) .+ (((usize 4) .* (
                ((shift_14) %% (usize 4)))))))) in 
  let out_11 :=
    array_upd out_11 (((i_13) .+ (usize 4))) (array_index (state_15) (((
            i_13) .+ (((usize 4) .* (((((shift_14) .+ (usize 1))) %% (
                    usize 4)))))))) in 
  let out_11 :=
    array_upd out_11 (((i_13) .+ (usize 8))) (array_index (state_15) (((
            i_13) .+ (((usize 4) .* (((((shift_14) .+ (usize 2))) %% (
                    usize 4)))))))) in 
  let out_11 :=
    array_upd out_11 (((i_13) .+ (usize 12))) (array_index (state_15) (((
            i_13) .+ (((usize 4) .* (((((shift_14) .+ (usize 3))) %% (
                    usize 4)))))))) in 
  out_11.
Definition shift_row_pure_code
  (i_13 : uint_size)
  (shift_14 : uint_size)
  (state_15 : block_t)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (shift_row_pure i_13 shift_14 state_15).

Definition out_11_loc : ChoiceEqualityLocation :=
  ((block_t ; 60%nat)).
Program Definition shift_row_state
  (i_13 : uint_size)
  (shift_14 : uint_size)
  (state_15 : block_t) : code (CEfset ([out_11_loc])) [interface] (@ct (
      block_t)) :=
  (({ code  '(out_11 : block_t) ←
          (ret (state_15)) ;;
        #put out_11_loc := out_11 ;;
       '(out_11 : block_t) ←
        ( temp_17 ←
            ((shift_14) %% (usize 4)) ;;
           temp_19 ←
            ((usize 4) .* (temp_17)) ;;
           temp_21 ←
            ((i_13) .+ (temp_19)) ;;
           temp_23 ←
            (array_index (state_15) (temp_21)) ;;
          ret (array_upd out_11 (i_13) (temp_23))) ;;
      
       '(out_11 : block_t) ←
        ( temp_25 ←
            ((i_13) .+ (usize 4)) ;;
           temp_27 ←
            ((shift_14) .+ (usize 1)) ;;
           temp_29 ←
            ((temp_27) %% (usize 4)) ;;
           temp_31 ←
            ((usize 4) .* (temp_29)) ;;
           temp_33 ←
            ((i_13) .+ (temp_31)) ;;
           temp_35 ←
            (array_index (state_15) (temp_33)) ;;
          ret (array_upd out_11 (temp_25) (temp_35))) ;;
      
       '(out_11 : block_t) ←
        ( temp_37 ←
            ((i_13) .+ (usize 8)) ;;
           temp_39 ←
            ((shift_14) .+ (usize 2)) ;;
           temp_41 ←
            ((temp_39) %% (usize 4)) ;;
           temp_43 ←
            ((usize 4) .* (temp_41)) ;;
           temp_45 ←
            ((i_13) .+ (temp_43)) ;;
           temp_47 ←
            (array_index (state_15) (temp_45)) ;;
          ret (array_upd out_11 (temp_37) (temp_47))) ;;
      
       '(out_11 : block_t) ←
        ( temp_49 ←
            ((i_13) .+ (usize 12)) ;;
           temp_51 ←
            ((shift_14) .+ (usize 3)) ;;
           temp_53 ←
            ((temp_51) %% (usize 4)) ;;
           temp_55 ←
            ((usize 4) .* (temp_53)) ;;
           temp_57 ←
            ((i_13) .+ (temp_55)) ;;
           temp_59 ←
            (array_index (state_15) (temp_57)) ;;
          ret (array_upd out_11 (temp_49) (temp_59))) ;;
      
      @ret (block_t) (out_11) } : code (CEfset ([out_11_loc])) [interface] _)).
Fail Next Obligation.

Program Definition shift_row
  (i_13 : uint_size)
  (shift_14 : uint_size)
  (state_15 : block_t)
  : both (CEfset ([out_11_loc])) [interface] (block_t) :=
  letbm out_11 : block_t loc( out_11_loc ) := lift_to_both0 state_15 in
  letb out_11 : block_t :=
    array_upd out_11 (lift_to_both0 i_13) (is_pure (array_index (state_15) ((
            lift_to_both0 i_13) .+ ((lift_to_both0 (usize 4)) .* ((
                lift_to_both0 shift_14) %% (lift_to_both0 (usize 4))))))) in
  letb out_11 : block_t :=
    array_upd out_11 ((lift_to_both0 i_13) .+ (lift_to_both0 (usize 4))) (
      is_pure (array_index (state_15) ((lift_to_both0 i_13) .+ ((lift_to_both0 (
                usize 4)) .* (((lift_to_both0 shift_14) .+ (lift_to_both0 (
                    usize 1))) %% (lift_to_both0 (usize 4))))))) in
  letb out_11 : block_t :=
    array_upd out_11 ((lift_to_both0 i_13) .+ (lift_to_both0 (usize 8))) (
      is_pure (array_index (state_15) ((lift_to_both0 i_13) .+ ((lift_to_both0 (
                usize 4)) .* (((lift_to_both0 shift_14) .+ (lift_to_both0 (
                    usize 2))) %% (lift_to_both0 (usize 4))))))) in
  letb out_11 : block_t :=
    array_upd out_11 ((lift_to_both0 i_13) .+ (lift_to_both0 (usize 12))) (
      is_pure (array_index (state_15) ((lift_to_both0 i_13) .+ ((lift_to_both0 (
                usize 4)) .* (((lift_to_both0 shift_14) .+ (lift_to_both0 (
                    usize 3))) %% (lift_to_both0 (usize 4))))))) in
  lift_scope (H_incl := _) (lift_to_both0 out_11)
  .
Fail Next Obligation.

Definition shift_rows_pure (state_61 : block_t) : block_t :=
  let state_62 : block_t :=
    shift_row (usize 1) (usize 1) (state_61) in 
  let state_63 : block_t :=
    shift_row (usize 2) (usize 2) (state_62) in 
  shift_row (usize 3) (usize 3) (state_63).
Definition shift_rows_pure_code
  (state_61 : block_t)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (shift_rows_pure state_61).


Program Definition shift_rows_state
  (state_61 : block_t) : code (CEfset ([out_11_loc])) [interface] (@ct (
      block_t)) :=
  (({ code  '(state_62 : block_t) ←
        ( temp_65 ←
            (shift_row (usize 1) (usize 1) (state_61)) ;;
          ret (temp_65)) ;;
       '(state_63 : block_t) ←
        ( temp_67 ←
            (shift_row (usize 2) (usize 2) (state_62)) ;;
          ret (temp_67)) ;;
       temp_69 ←
        (shift_row (usize 3) (usize 3) (state_63)) ;;
      @ret (block_t) (temp_69) } : code (CEfset ([out_11_loc])) [interface] _)).
Fail Next Obligation.

Program Definition shift_rows
  (state_61 : block_t)
  : both (CEfset ([out_11_loc])) [interface] (block_t) :=
  letb state_62 : block_t :=
    shift_row (lift_to_both0 (usize 1)) (lift_to_both0 (usize 1)) (
      lift_to_both0 state_61) in
  letb state_63 : block_t :=
    shift_row (lift_to_both0 (usize 2)) (lift_to_both0 (usize 2)) (
      lift_to_both0 state_62) in
  lift_scope (H_incl := _) (shift_row (lift_to_both0 (usize 3)) (lift_to_both0 (
        usize 3)) (lift_to_both0 state_63))
  .
Fail Next Obligation.

Definition xtime_pure (x_70 : uint8) : uint8 :=
  let x1_71 : uint8 :=
    ((x_70) shift_left (usize 1)) in 
  let x7_72 : uint8 :=
    ((x_70) shift_right (usize 7)) in 
  let x71_73 : uint8 :=
    ((x7_72) .& (secret (@repr U8 1))) in 
  let x711b_74 : uint8 :=
    ((x71_73) .* (secret (@repr U8 27))) in 
  ((x1_71) .^ (x711b_74)).
Definition xtime_pure_code
  (x_70 : uint8)
  : code fset.fset0 [interface] (@ct uint8) :=
  lift_to_code (xtime_pure x_70).


Program Definition xtime_state
  (x_70 : uint8) : code (fset.fset0) [interface] (@ct (uint8)) :=
  (({ code  '(x1_71 : uint8) ←
        ( temp_76 ←
            ((x_70) shift_left (usize 1)) ;;
          ret (temp_76)) ;;
       '(x7_72 : uint8) ←
        ( temp_78 ←
            ((x_70) shift_right (usize 7)) ;;
          ret (temp_78)) ;;
       '(x71_73 : uint8) ←
        ( '(temp_80 : int8) ←
            (secret (@repr U8 1)) ;;
           temp_82 ←
            ((x7_72) .& (temp_80)) ;;
          ret (temp_82)) ;;
       '(x711b_74 : uint8) ←
        ( '(temp_84 : int8) ←
            (secret (@repr U8 27)) ;;
           temp_86 ←
            ((x71_73) .* (temp_84)) ;;
          ret (temp_86)) ;;
       temp_88 ←
        ((x1_71) .^ (x711b_74)) ;;
      @ret (uint8) (temp_88) } : code (fset.fset0) [interface] _)).
Fail Next Obligation.

Program Definition xtime
  (x_70 : uint8)
  : both (fset.fset0) [interface] (uint8) :=
  letb x1_71 : uint8 :=
    (lift_to_both0 x_70) shift_left (lift_to_both0 (usize 1)) in
  letb x7_72 : uint8 :=
    (lift_to_both0 x_70) shift_right (lift_to_both0 (usize 7)) in
  letb x71_73 : uint8 :=
    (lift_to_both0 x7_72) .& (secret (lift_to_both0 (@repr U8 1))) in
  letb x711b_74 : uint8 :=
    (lift_to_both0 x71_73) .* (secret (lift_to_both0 (@repr U8 27))) in
  lift_scope (H_incl := _) ((lift_to_both0 x1_71) .^ (lift_to_both0 x711b_74))
  .
Fail Next Obligation.

Definition mix_column_pure (c_91 : uint_size) (state_92 : block_t) : block_t :=
  let i0_93 : uint_size :=
    ((usize 4) .* (c_91)) in 
  let s0_94 : uint8 :=
    array_index (state_92) (i0_93) in 
  let s1_95 : uint8 :=
    array_index (state_92) (((i0_93) .+ (usize 1))) in 
  let s2_96 : uint8 :=
    array_index (state_92) (((i0_93) .+ (usize 2))) in 
  let s3_97 : uint8 :=
    array_index (state_92) (((i0_93) .+ (usize 3))) in 
  let st_89 : block_t :=
    state_92 in 
  let tmp_98 : uint8 :=
    ((((((s0_94) .^ (s1_95))) .^ (s2_96))) .^ (s3_97)) in 
  let st_89 :=
    array_upd st_89 (i0_93) (((((s0_94) .^ (tmp_98))) .^ (xtime (((s0_94) .^ (
                s1_95)))))) in 
  let st_89 :=
    array_upd st_89 (((i0_93) .+ (usize 1))) (((((s1_95) .^ (tmp_98))) .^ (
          xtime (((s1_95) .^ (s2_96)))))) in 
  let st_89 :=
    array_upd st_89 (((i0_93) .+ (usize 2))) (((((s2_96) .^ (tmp_98))) .^ (
          xtime (((s2_96) .^ (s3_97)))))) in 
  let st_89 :=
    array_upd st_89 (((i0_93) .+ (usize 3))) (((((s3_97) .^ (tmp_98))) .^ (
          xtime (((s3_97) .^ (s0_94)))))) in 
  st_89.
Definition mix_column_pure_code
  (c_91 : uint_size)
  (state_92 : block_t)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (mix_column_pure c_91 state_92).

Definition st_89_loc : ChoiceEqualityLocation :=
  ((block_t ; 159%nat)).
Program Definition mix_column_state
  (c_91 : uint_size)
  (state_92 : block_t) : code (CEfset ([st_89_loc])) [interface] (@ct (
      block_t)) :=
  (({ code  '(i0_93 : uint_size) ←
        ( temp_100 ←
            ((usize 4) .* (c_91)) ;;
          ret (temp_100)) ;;
       '(s0_94 : uint8) ←
        ( temp_102 ←
            (array_index (state_92) (i0_93)) ;;
          ret (temp_102)) ;;
       '(s1_95 : uint8) ←
        ( temp_104 ←
            ((i0_93) .+ (usize 1)) ;;
           temp_106 ←
            (array_index (state_92) (temp_104)) ;;
          ret (temp_106)) ;;
       '(s2_96 : uint8) ←
        ( temp_108 ←
            ((i0_93) .+ (usize 2)) ;;
           temp_110 ←
            (array_index (state_92) (temp_108)) ;;
          ret (temp_110)) ;;
       '(s3_97 : uint8) ←
        ( temp_112 ←
            ((i0_93) .+ (usize 3)) ;;
           temp_114 ←
            (array_index (state_92) (temp_112)) ;;
          ret (temp_114)) ;;
       '(st_89 : block_t) ←
          (ret (state_92)) ;;
        #put st_89_loc := st_89 ;;
       '(tmp_98 : uint8) ←
        ( temp_116 ←
            ((s0_94) .^ (s1_95)) ;;
           temp_118 ←
            ((temp_116) .^ (s2_96)) ;;
           temp_120 ←
            ((temp_118) .^ (s3_97)) ;;
          ret (temp_120)) ;;
       '(st_89 : block_t) ←
        ( temp_122 ←
            ((s0_94) .^ (tmp_98)) ;;
           temp_124 ←
            ((s0_94) .^ (s1_95)) ;;
           temp_126 ←
            (xtime (temp_124)) ;;
           temp_128 ←
            ((temp_122) .^ (temp_126)) ;;
          ret (array_upd st_89 (i0_93) (temp_128))) ;;
      
       '(st_89 : block_t) ←
        ( temp_130 ←
            ((i0_93) .+ (usize 1)) ;;
           temp_132 ←
            ((s1_95) .^ (tmp_98)) ;;
           temp_134 ←
            ((s1_95) .^ (s2_96)) ;;
           temp_136 ←
            (xtime (temp_134)) ;;
           temp_138 ←
            ((temp_132) .^ (temp_136)) ;;
          ret (array_upd st_89 (temp_130) (temp_138))) ;;
      
       '(st_89 : block_t) ←
        ( temp_140 ←
            ((i0_93) .+ (usize 2)) ;;
           temp_142 ←
            ((s2_96) .^ (tmp_98)) ;;
           temp_144 ←
            ((s2_96) .^ (s3_97)) ;;
           temp_146 ←
            (xtime (temp_144)) ;;
           temp_148 ←
            ((temp_142) .^ (temp_146)) ;;
          ret (array_upd st_89 (temp_140) (temp_148))) ;;
      
       '(st_89 : block_t) ←
        ( temp_150 ←
            ((i0_93) .+ (usize 3)) ;;
           temp_152 ←
            ((s3_97) .^ (tmp_98)) ;;
           temp_154 ←
            ((s3_97) .^ (s0_94)) ;;
           temp_156 ←
            (xtime (temp_154)) ;;
           temp_158 ←
            ((temp_152) .^ (temp_156)) ;;
          ret (array_upd st_89 (temp_150) (temp_158))) ;;
      
      @ret (block_t) (st_89) } : code (CEfset ([st_89_loc])) [interface] _)).
Fail Next Obligation.

Program Definition mix_column
  (c_91 : uint_size)
  (state_92 : block_t)
  : both (CEfset ([st_89_loc])) [interface] (block_t) :=
  letb i0_93 : uint_size := (lift_to_both0 (usize 4)) .* (lift_to_both0 c_91) in
  letb s0_94 : uint8 := array_index (state_92) (lift_to_both0 i0_93) in
  letb s1_95 : uint8 :=
    array_index (state_92) ((lift_to_both0 i0_93) .+ (lift_to_both0 (
          usize 1))) in
  letb s2_96 : uint8 :=
    array_index (state_92) ((lift_to_both0 i0_93) .+ (lift_to_both0 (
          usize 2))) in
  letb s3_97 : uint8 :=
    array_index (state_92) ((lift_to_both0 i0_93) .+ (lift_to_both0 (
          usize 3))) in
  letbm st_89 : block_t loc( st_89_loc ) := lift_to_both0 state_92 in
  letb tmp_98 : uint8 :=
    (((lift_to_both0 s0_94) .^ (lift_to_both0 s1_95)) .^ (
        lift_to_both0 s2_96)) .^ (lift_to_both0 s3_97) in
  letb st_89 : block_t :=
    array_upd st_89 (lift_to_both0 i0_93) (is_pure (((lift_to_both0 s0_94) .^ (
            lift_to_both0 tmp_98)) .^ (xtime ((lift_to_both0 s0_94) .^ (
              lift_to_both0 s1_95))))) in
  letb st_89 : block_t :=
    array_upd st_89 ((lift_to_both0 i0_93) .+ (lift_to_both0 (usize 1))) (
      is_pure (((lift_to_both0 s1_95) .^ (lift_to_both0 tmp_98)) .^ (xtime ((
              lift_to_both0 s1_95) .^ (lift_to_both0 s2_96))))) in
  letb st_89 : block_t :=
    array_upd st_89 ((lift_to_both0 i0_93) .+ (lift_to_both0 (usize 2))) (
      is_pure (((lift_to_both0 s2_96) .^ (lift_to_both0 tmp_98)) .^ (xtime ((
              lift_to_both0 s2_96) .^ (lift_to_both0 s3_97))))) in
  letb st_89 : block_t :=
    array_upd st_89 ((lift_to_both0 i0_93) .+ (lift_to_both0 (usize 3))) (
      is_pure (((lift_to_both0 s3_97) .^ (lift_to_both0 tmp_98)) .^ (xtime ((
              lift_to_both0 s3_97) .^ (lift_to_both0 s0_94))))) in
  lift_scope (H_incl := _) (lift_to_both0 st_89)
  .
Fail Next Obligation.

Definition mix_columns_pure (state_160 : block_t) : block_t :=
  let state_161 : block_t :=
    mix_column (usize 0) (state_160) in 
  let state_162 : block_t :=
    mix_column (usize 1) (state_161) in 
  let state_163 : block_t :=
    mix_column (usize 2) (state_162) in 
  mix_column (usize 3) (state_163).
Definition mix_columns_pure_code
  (state_160 : block_t)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (mix_columns_pure state_160).


Program Definition mix_columns_state
  (state_160 : block_t) : code (CEfset ([st_89_loc])) [interface] (@ct (
      block_t)) :=
  (({ code  '(state_161 : block_t) ←
        ( temp_165 ←
            (mix_column (usize 0) (state_160)) ;;
          ret (temp_165)) ;;
       '(state_162 : block_t) ←
        ( temp_167 ←
            (mix_column (usize 1) (state_161)) ;;
          ret (temp_167)) ;;
       '(state_163 : block_t) ←
        ( temp_169 ←
            (mix_column (usize 2) (state_162)) ;;
          ret (temp_169)) ;;
       temp_171 ←
        (mix_column (usize 3) (state_163)) ;;
      @ret (block_t) (temp_171) } : code (CEfset ([st_89_loc])) [interface] _)).
Fail Next Obligation.

Program Definition mix_columns
  (state_160 : block_t)
  : both (CEfset ([st_89_loc])) [interface] (block_t) :=
  letb state_161 : block_t :=
    mix_column (lift_to_both0 (usize 0)) (lift_to_both0 state_160) in
  letb state_162 : block_t :=
    mix_column (lift_to_both0 (usize 1)) (lift_to_both0 state_161) in
  letb state_163 : block_t :=
    mix_column (lift_to_both0 (usize 2)) (lift_to_both0 state_162) in
  lift_scope (H_incl := _) (mix_column (lift_to_both0 (usize 3)) (
      lift_to_both0 state_163))
  .
Fail Next Obligation.

Definition add_round_key_pure
  (state_174 : block_t)
  (key_175 : round_key_t)
  : block_t :=
  let out_172 : block_t :=
    state_174 in 
  let out_172 :=
    Hacspec_Lib_Pre.foldi (usize 0) (blocksize_v) out_172
      (fun i_176 out_172 =>
      let out_172 :=
        array_upd out_172 (i_176) (((array_index (out_172) (i_176)) .^ (
              array_index (key_175) (i_176)))) in 
      (out_172)) in 
  out_172.
Definition add_round_key_pure_code
  (state_174 : block_t)
  (key_175 : round_key_t)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (add_round_key_pure state_174 key_175).

Definition out_172_loc : ChoiceEqualityLocation :=
  ((block_t ; 183%nat)).
Program Definition add_round_key_state
  (state_174 : block_t)
  (key_175 : round_key_t) : code (CEfset ([out_172_loc])) [interface] (@ct (
      block_t)) :=
  (({ code  '(out_172 : block_t) ←
          (ret (state_174)) ;;
        #put out_172_loc := out_172 ;;
       out_172 ←
        (foldi (usize 0) (blocksize_v) out_172 (fun i_176 (out_172 : _) =>
            ({ code  '(out_172 : block_t) ←
                ( temp_178 ←
                    (array_index (out_172) (i_176)) ;;
                   temp_180 ←
                    (array_index (key_175) (i_176)) ;;
                   temp_182 ←
                    ((temp_178) .^ (temp_180)) ;;
                  ret (array_upd out_172 (i_176) (temp_182))) ;;
              
              @ret (_) (out_172) } : code (CEfset (
                  [out_172_loc])) [interface] _))) ;;
      
      @ret (block_t) (out_172) } : code (CEfset (
          [out_172_loc])) [interface] _)).
Fail Next Obligation.

Program Definition add_round_key
  (state_174 : block_t)
  (key_175 : round_key_t)
  : both (CEfset ([out_172_loc])) [interface] (block_t) :=
  letbm out_172 : block_t loc( out_172_loc ) := lift_to_both0 state_174 in
  letb out_172 :=
    foldi_both' (lift_to_both0 (usize 0)) (
        lift_to_both0 blocksize_v) out_172 (L := (CEfset (
          [out_172_loc]))) (fun i_176 (out_172 : _) =>
      letb out_172 : block_t :=
        array_upd out_172 (lift_to_both0 i_176) (is_pure ((array_index (
                out_172) (lift_to_both0 i_176)) .^ (array_index (key_175) (
                lift_to_both0 i_176)))) in
      lift_scope (H_incl := _) (lift_to_both0 out_172)
      ) in
  lift_scope (H_incl := _) (lift_to_both0 out_172)
  .
Fail Next Obligation.

Definition aes_enc_pure
  (state_184 : block_t)
  (round_key_185 : round_key_t)
  : block_t :=
  let state_186 : block_t :=
    sub_bytes (state_184) in 
  let state_187 : block_t :=
    shift_rows (state_186) in 
  let state_188 : block_t :=
    mix_columns (state_187) in 
  add_round_key (state_188) (round_key_185).
Definition aes_enc_pure_code
  (state_184 : block_t)
  (round_key_185 : round_key_t)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (aes_enc_pure state_184 round_key_185).


Program Definition aes_enc_state
  (state_184 : block_t)
  (round_key_185 : round_key_t) : code (CEfset (
      [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc])) [interface] (@ct (
      block_t)) :=
  (({ code  '(state_186 : block_t) ←
        ( temp_190 ←
            (sub_bytes (state_184)) ;;
          ret (temp_190)) ;;
       '(state_187 : block_t) ←
        ( temp_192 ←
            (shift_rows (state_186)) ;;
          ret (temp_192)) ;;
       '(state_188 : block_t) ←
        ( temp_194 ←
            (mix_columns (state_187)) ;;
          ret (temp_194)) ;;
       temp_196 ←
        (add_round_key (state_188) (round_key_185)) ;;
      @ret (block_t) (temp_196) } : code (CEfset (
          [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc])) [interface] _)).
Fail Next Obligation.

Program Definition aes_enc
  (state_184 : block_t)
  (round_key_185 : round_key_t)
  : both (CEfset (
      [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc])) [interface] (
    block_t) :=
  letb state_186 : block_t := sub_bytes (lift_to_both0 state_184) in
  letb state_187 : block_t := shift_rows (lift_to_both0 state_186) in
  letb state_188 : block_t := mix_columns (lift_to_both0 state_187) in
  lift_scope (H_incl := _) (add_round_key (lift_to_both0 state_188) (
      lift_to_both0 round_key_185))
  .
Fail Next Obligation.

Definition aes_enc_last_pure
  (state_197 : block_t)
  (round_key_198 : round_key_t)
  : block_t :=
  let state_199 : block_t :=
    sub_bytes (state_197) in 
  let state_200 : block_t :=
    shift_rows (state_199) in 
  add_round_key (state_200) (round_key_198).
Definition aes_enc_last_pure_code
  (state_197 : block_t)
  (round_key_198 : round_key_t)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (aes_enc_last_pure state_197 round_key_198).


Program Definition aes_enc_last_state
  (state_197 : block_t)
  (round_key_198 : round_key_t) : code (CEfset (
      [st_0_loc ; out_11_loc ; out_172_loc])) [interface] (@ct (block_t)) :=
  (({ code  '(state_199 : block_t) ←
        ( temp_202 ←
            (sub_bytes (state_197)) ;;
          ret (temp_202)) ;;
       '(state_200 : block_t) ←
        ( temp_204 ←
            (shift_rows (state_199)) ;;
          ret (temp_204)) ;;
       temp_206 ←
        (add_round_key (state_200) (round_key_198)) ;;
      @ret (block_t) (temp_206) } : code (CEfset (
          [st_0_loc ; out_11_loc ; out_172_loc])) [interface] _)).
Fail Next Obligation.

Program Definition aes_enc_last
  (state_197 : block_t)
  (round_key_198 : round_key_t)
  : both (CEfset ([st_0_loc ; out_11_loc ; out_172_loc])) [interface] (
    block_t) :=
  letb state_199 : block_t := sub_bytes (lift_to_both0 state_197) in
  letb state_200 : block_t := shift_rows (lift_to_both0 state_199) in
  lift_scope (H_incl := _) (add_round_key (lift_to_both0 state_200) (
      lift_to_both0 round_key_198))
  .
Fail Next Obligation.

Definition rounds_aes_pure
  (state_209 : block_t)
  (key_210 : byte_seq)
  : block_t :=
  let out_207 : block_t :=
    state_209 in 
  let out_207 :=
    Hacspec_Lib_Pre.foldi (usize 0) (seq_num_chunks (key_210) (
          blocksize_v)) out_207
      (fun i_211 out_207 =>
      let '(_, key_block_212) :=
        seq_get_chunk (key_210) (blocksize_v) (i_211) : (uint_size '× seq uint8
        ) in 
      let out_207 :=
        aes_enc (out_207) (array_from_seq (blocksize_v) (key_block_212)) in 
      (out_207)) in 
  out_207.
Definition rounds_aes_pure_code
  (state_209 : block_t)
  (key_210 : byte_seq)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (rounds_aes_pure state_209 key_210).

Definition out_207_loc : ChoiceEqualityLocation :=
  ((block_t ; 221%nat)).
Program Definition rounds_aes_state
  (state_209 : block_t)
  (key_210 : byte_seq) : code (CEfset (
      [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc])) [interface] (
    @ct (block_t)) :=
  (({ code  '(out_207 : block_t) ←
          (ret (state_209)) ;;
        #put out_207_loc := out_207 ;;
       temp_214 ←
        (seq_num_chunks (key_210) (blocksize_v)) ;;
       out_207 ←
        (foldi (usize 0) (temp_214) out_207 (fun i_211 (out_207 : _) =>
            ({ code  '(_, key_block_212) ←
                ( temp_216 ←
                    (seq_get_chunk (key_210) (blocksize_v) (i_211)) ;;
                  ret (temp_216)) ;;
               out_207 ←
                  (( temp_218 ←
                        (array_from_seq (blocksize_v) (key_block_212 : seq uint8)) ;;
                       temp_220 ←
                        (aes_enc (out_207) (temp_218)) ;;
                      ret (temp_220))) ;;
                #put out_207_loc := out_207 ;;
              
              @ret (_) (out_207) } : code (CEfset (
                  [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc])) [interface] _))) ;;
      
      @ret (block_t) (out_207) } : code (CEfset (
          [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc])) [interface] _)).
Fail Next Obligation.

Program Definition rounds_aes
  (state_209 : block_t)
  (key_210 : byte_seq)
  : both (CEfset (
      [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc])) [interface] (
    block_t) :=
  letbm out_207 : block_t loc( out_207_loc ) := lift_to_both0 state_209 in
  letb out_207 :=
    foldi_both' (lift_to_both0 (usize 0)) (seq_num_chunks (
          lift_to_both0 key_210) (lift_to_both0 blocksize_v)) out_207 (L := (
        CEfset (
          [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc]))) (fun i_211 (
        out_207 : _) =>
      letb '(_, key_block_212) : (uint_size '× seq uint8) :=
        seq_get_chunk (lift_to_both0 key_210) (lift_to_both0 blocksize_v) (
          lift_to_both0 i_211) in
      letbm out_207 loc( out_207_loc ) :=
        aes_enc (lift_to_both0 out_207) (array_from_seq (blocksize_v) (
            lift_to_both0 key_block_212)) in
      lift_scope (H_incl := _) (lift_to_both0 out_207)
      ) in
  lift_scope (H_incl := _) (lift_to_both0 out_207)
  .
Fail Next Obligation.

Definition block_cipher_aes_pure
  (input_222 : block_t)
  (key_223 : byte_seq)
  (nr_224 : uint_size)
  : block_t :=
  let k0_225 : round_key_t :=
    array_from_slice_range (default : uint8) (blocksize_v) (key_223) (prod_ce(
        usize 0,
        usize 16
      )) in 
  let k_226 : seq uint8 :=
    seq_from_slice_range (key_223) (prod_ce(usize 16, ((nr_224) .* (usize 16))
      )) in 
  let kn_227 : round_key_t :=
    array_from_slice (default : uint8) (blocksize_v) (key_223) (((nr_224) .* (
          usize 16))) (usize 16) in 
  let state_228 : block_t :=
    add_round_key (input_222) (k0_225) in 
  let state_229 : block_t :=
    rounds_aes (state_228) (k_226) in 
  aes_enc_last (state_229) (kn_227).
Definition block_cipher_aes_pure_code
  (input_222 : block_t)
  (key_223 : byte_seq)
  (nr_224 : uint_size)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (block_cipher_aes_pure input_222 key_223 nr_224).


Program Definition block_cipher_aes_state
  (input_222 : block_t)
  (key_223 : byte_seq)
  (nr_224 : uint_size) : code (CEfset (
      [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc])) [interface] (
    @ct (block_t)) :=
  (({ code  '(k0_225 : round_key_t) ←
        ( temp_231 ←
            (array_from_slice_range (default : uint8) (blocksize_v) (key_223) (
                prod_ce(usize 0, usize 16))) ;;
          ret (temp_231)) ;;
       '(k_226 : seq uint8) ←
        ( temp_233 ←
            ((nr_224) .* (usize 16)) ;;
           temp_235 ←
            (seq_from_slice_range (key_223) (prod_ce(usize 16, temp_233))) ;;
          ret (temp_235)) ;;
       '(kn_227 : round_key_t) ←
        ( temp_237 ←
            ((nr_224) .* (usize 16)) ;;
           temp_239 ←
            (array_from_slice (default : uint8) (blocksize_v) (key_223) (
                temp_237) (usize 16)) ;;
          ret (temp_239)) ;;
       '(state_228 : block_t) ←
        ( temp_241 ←
            (add_round_key (input_222) (k0_225)) ;;
          ret (temp_241)) ;;
       '(state_229 : block_t) ←
        ( temp_243 ←
            (rounds_aes (state_228) (k_226)) ;;
          ret (temp_243)) ;;
       temp_245 ←
        (aes_enc_last (state_229) (kn_227)) ;;
      @ret (block_t) (temp_245) } : code (CEfset (
          [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc])) [interface] _)).
Fail Next Obligation.

Program Definition block_cipher_aes
  (input_222 : block_t)
  (key_223 : byte_seq)
  (nr_224 : uint_size)
  : both (CEfset (
      [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc])) [interface] (
    block_t) :=
  letb k0_225 : round_key_t :=
    array_from_slice_range (default : uint8) (blocksize_v) (
      lift_to_both0 key_223) (prod_b(
        lift_to_both0 (usize 0),
        lift_to_both0 (usize 16)
      )) in
  letb k_226 : seq uint8 :=
    seq_from_slice_range (lift_to_both0 key_223) (prod_b(
        lift_to_both0 (usize 16),
        (lift_to_both0 nr_224) .* (lift_to_both0 (usize 16))
      )) in
  letb kn_227 : round_key_t :=
    array_from_slice (default : uint8) (blocksize_v) (lift_to_both0 key_223) ((
        lift_to_both0 nr_224) .* (lift_to_both0 (usize 16))) (lift_to_both0 (
        usize 16)) in
  letb state_228 : block_t :=
    add_round_key (lift_to_both0 input_222) (lift_to_both0 k0_225) in
  letb state_229 : block_t :=
    rounds_aes (lift_to_both0 state_228) (lift_to_both0 k_226) in
  lift_scope (H_incl := _) (aes_enc_last (lift_to_both0 state_229) (
      lift_to_both0 kn_227))
  .
Fail Next Obligation.

Definition rotate_word_pure (w_246 : word_t) : word_t :=
  array_from_list uint8 [
    (array_index (w_246) (usize 1)) : uint8;
    (array_index (w_246) (usize 2)) : uint8;
    (array_index (w_246) (usize 3)) : uint8;
    (array_index (w_246) (usize 0)) : uint8
  ].
Definition rotate_word_pure_code
  (w_246 : word_t)
  : code fset.fset0 [interface] (@ct word_t) :=
  lift_to_code (rotate_word_pure w_246).


Program Definition rotate_word_state
  (w_246 : word_t) : code (fset.fset0) [interface] (@ct (word_t)) :=
  (({ code  temp_248 ←
        (array_index (w_246) (usize 1)) ;;
       temp_250 ←
        (array_index (w_246) (usize 2)) ;;
       temp_252 ←
        (array_index (w_246) (usize 3)) ;;
       temp_254 ←
        (array_index (w_246) (usize 0)) ;;
      @ret (word_t) (array_from_list uint8 [
          temp_248;
          temp_250;
          temp_252;
          temp_254
        ]) } : code (fset.fset0) [interface] _)).
Fail Next Obligation.

Program Definition rotate_word
  (w_246 : word_t)
  : both (fset.fset0) [interface] (word_t) :=
  lift_scope (H_incl := _) (array_from_list uint8 ([
        (array_index (w_246) (lift_to_both0 (usize 1))) : uint8;
        (array_index (w_246) (lift_to_both0 (usize 2))) : uint8;
        (array_index (w_246) (lift_to_both0 (usize 3))) : uint8;
        (array_index (w_246) (lift_to_both0 (usize 0))) : uint8
      ]))
  .
Fail Next Obligation.

Definition slice_word_pure (w_255 : word_t) : word_t :=
  array_from_list uint8 [
    (array_index (sbox_v) (declassify_usize_from_uint8 (array_index (w_255) (
            usize 0)))) : uint8;
    (array_index (sbox_v) (declassify_usize_from_uint8 (array_index (w_255) (
            usize 1)))) : uint8;
    (array_index (sbox_v) (declassify_usize_from_uint8 (array_index (w_255) (
            usize 2)))) : uint8;
    (array_index (sbox_v) (declassify_usize_from_uint8 (array_index (w_255) (
            usize 3)))) : uint8
  ].
Definition slice_word_pure_code
  (w_255 : word_t)
  : code fset.fset0 [interface] (@ct word_t) :=
  lift_to_code (slice_word_pure w_255).


Program Definition slice_word_state
  (w_255 : word_t) : code (fset.fset0) [interface] (@ct (word_t)) :=
  (({ code  temp_257 ←
        (array_index (w_255) (usize 0)) ;;
       temp_259 ←
        (declassify_usize_from_uint8 (temp_257)) ;;
       temp_261 ←
        (array_index (sbox_v) (temp_259)) ;;
       temp_263 ←
        (array_index (w_255) (usize 1)) ;;
       temp_265 ←
        (declassify_usize_from_uint8 (temp_263)) ;;
       temp_267 ←
        (array_index (sbox_v) (temp_265)) ;;
       temp_269 ←
        (array_index (w_255) (usize 2)) ;;
       temp_271 ←
        (declassify_usize_from_uint8 (temp_269)) ;;
       temp_273 ←
        (array_index (sbox_v) (temp_271)) ;;
       temp_275 ←
        (array_index (w_255) (usize 3)) ;;
       temp_277 ←
        (declassify_usize_from_uint8 (temp_275)) ;;
       temp_279 ←
        (array_index (sbox_v) (temp_277)) ;;
      @ret (word_t) (array_from_list uint8 [
          temp_261;
          temp_267;
          temp_273;
          temp_279
        ]) } : code (fset.fset0) [interface] _)).
Fail Next Obligation.

Program Definition slice_word
  (w_255 : word_t)
  : both (fset.fset0) [interface] (word_t) :=
  lift_scope (H_incl := _) (array_from_list uint8 ([
        (array_index (sbox_v) (declassify_usize_from_uint8 (array_index (
                w_255) (lift_to_both0 (usize 0))))) : uint8;
        (array_index (sbox_v) (declassify_usize_from_uint8 (array_index (
                w_255) (lift_to_both0 (usize 1))))) : uint8;
        (array_index (sbox_v) (declassify_usize_from_uint8 (array_index (
                w_255) (lift_to_both0 (usize 2))))) : uint8;
        (array_index (sbox_v) (declassify_usize_from_uint8 (array_index (
                w_255) (lift_to_both0 (usize 3))))) : uint8
      ]))
  .
Fail Next Obligation.

Definition aes_keygen_assist_pure
  (w_282 : word_t)
  (rcon_283 : uint8)
  : word_t :=
  let k_280 : word_t :=
    rotate_word (w_282) in 
  let k_280 :=
    slice_word (k_280) in 
  let k_280 :=
    array_upd k_280 (usize 0) (((array_index (k_280) (usize 0)) .^ (
          rcon_283))) in 
  k_280.
Definition aes_keygen_assist_pure_code
  (w_282 : word_t)
  (rcon_283 : uint8)
  : code fset.fset0 [interface] (@ct word_t) :=
  lift_to_code (aes_keygen_assist_pure w_282 rcon_283).

Definition k_280_loc : ChoiceEqualityLocation :=
  ((word_t ; 292%nat)).
Program Definition aes_keygen_assist_state
  (w_282 : word_t)
  (rcon_283 : uint8) : code (CEfset ([k_280_loc])) [interface] (@ct (word_t)) :=
  (({ code  '(k_280 : word_t) ←
          ( temp_285 ←
              (rotate_word (w_282)) ;;
            ret (temp_285)) ;;
        #put k_280_loc := k_280 ;;
       '(k_280 : word_t) ←
          (( temp_287 ←
                (slice_word (k_280)) ;;
              ret (temp_287))) ;;
        #put k_280_loc := k_280 ;;
      
       '(k_280 : word_t) ←
        ( temp_289 ←
            (array_index (k_280) (usize 0)) ;;
           temp_291 ←
            ((temp_289) .^ (rcon_283)) ;;
          ret (array_upd k_280 (usize 0) (temp_291))) ;;
      
      @ret (word_t) (k_280) } : code (CEfset ([k_280_loc])) [interface] _)).
Fail Next Obligation.

Program Definition aes_keygen_assist
  (w_282 : word_t)
  (rcon_283 : uint8)
  : both (CEfset ([k_280_loc])) [interface] (word_t) :=
  letbm k_280 : word_t loc( k_280_loc ) := rotate_word (lift_to_both0 w_282) in
  letbm k_280 loc( k_280_loc ) := slice_word (lift_to_both0 k_280) in
  letb k_280 : word_t :=
    array_upd k_280 (lift_to_both0 (usize 0)) (is_pure ((array_index (k_280) (
            lift_to_both0 (usize 0))) .^ (lift_to_both0 rcon_283))) in
  lift_scope (H_incl := _) (lift_to_both0 k_280)
  .
Fail Next Obligation.

Definition key_expansion_word_pure
  (w0_297 : word_t)
  (w1_298 : word_t)
  (i_299 : uint_size)
  (nk_300 : uint_size)
  (nr_301 : uint_size)
  : word_result_t :=
  let k_293 : word_t :=
    w1_298 in 
  let result_294 : (result int8 word_t) :=
    @Err word_t int8 (invalid_key_expansion_index_v) in 
  let '(k_293, result_294) :=
    if (((i_299) <.? (((usize 4) .* (((nr_301) .+ (
                  usize 1))))))):bool_ChoiceEquality
    then (let '(k_293) :=
        if (((((i_299) %% (nk_300))) =.? (usize 0))):bool_ChoiceEquality
        then (let k_293 :=
            aes_keygen_assist (k_293) (array_index (rcon_v) (((i_299) ./ (
                    nk_300)))) in 
          (k_293 : T _))
        else (let '(k_293) :=
            if (((((nk_300) >.? (usize 6))) && (((((i_299) %% (nk_300))) =.? (
                      usize 4))))):bool_ChoiceEquality
            then (let k_293 :=
                slice_word (k_293) in 
              (k_293 : T _))
            else ((k_293)) in 
          (k_293)) in 
      let k_293 :=
        Hacspec_Lib_Pre.foldi (usize 0) (usize 4) k_293
          (fun i_302 k_293 =>
          let k_293 :=
            array_upd k_293 (i_302) (((array_index (k_293) (i_302)) .^ (
                  array_index (w0_297) (i_302)))) in 
          (k_293)) in 
      let result_294 :=
        @Ok word_t int8 (k_293) in 
      prod_ce(k_293, result_294))
    else (prod_ce(k_293, result_294)) in 
  result_294.
Definition key_expansion_word_pure_code
  (w0_297 : word_t)
  (w1_298 : word_t)
  (i_299 : uint_size)
  (nk_300 : uint_size)
  (nr_301 : uint_size)
  : code fset.fset0 [interface] (@ct word_result_t) :=
  lift_to_code (key_expansion_word_pure w0_297 w1_298 i_299 nk_300 nr_301).

Definition k_293_loc : ChoiceEqualityLocation :=
  ((word_t ; 335%nat)).
Definition result_294_loc : ChoiceEqualityLocation :=
  (((result int8 word_t) ; 336%nat)).
Program Definition key_expansion_word_state
  (w0_297 : word_t)
  (w1_298 : word_t)
  (i_299 : uint_size)
  (nk_300 : uint_size)
  (nr_301 : uint_size) : code (CEfset (
      [k_280_loc ; k_293_loc ; result_294_loc])) [interface] (@ct (
      word_result_t)) :=
  (({ code  '(k_293 : word_t) ←
          (ret (w1_298)) ;;
        #put k_293_loc := k_293 ;;
       '(result_294 : (result int8 word_t)) ←
          (ret (@Err word_t int8 (invalid_key_expansion_index_v))) ;;
        #put result_294_loc := result_294 ;;
       temp_304 ←
        ((nr_301) .+ (usize 1)) ;;
       temp_306 ←
        ((usize 4) .* (temp_304)) ;;
       temp_308 ←
        ((i_299) <.? (temp_306)) ;;
       '(k_293, result_294) ←
        (if temp_308:bool_ChoiceEquality
          then (({ code  temp_310 ←
                ((i_299) %% (nk_300)) ;;
               temp_312 ←
                ((temp_310) =.? (usize 0)) ;;
               '(k_293 : word_t) ←
                (if temp_312:bool_ChoiceEquality
                  then (({ code  k_293 ←
                          (( temp_314 ←
                                ((i_299) ./ (nk_300)) ;;
                               temp_316 ←
                                (array_index (rcon_v) (temp_314)) ;;
                               temp_318 ←
                                (aes_keygen_assist (k_293) (temp_316)) ;;
                              ret (temp_318))) ;;
                        #put k_293_loc := k_293 ;;
                      
                      @ret (_) (k_293) } : code (CEfset (
                          [k_280_loc ; k_293_loc ; result_294_loc])) [interface] _))
                  else (({ code  temp_320 ←
                        ((nk_300) >.? (usize 6)) ;;
                       temp_322 ←
                        ((i_299) %% (nk_300)) ;;
                       temp_324 ←
                        ((temp_322) =.? (usize 4)) ;;
                       temp_326 ←
                        ((temp_320) && (temp_324)) ;;
                       'k_293 ←
                        (if temp_326:bool_ChoiceEquality
                          then (({ code  k_293 ←
                                  (( temp_328 ←
                                        (slice_word (k_293)) ;;
                                      ret (temp_328))) ;;
                                #put k_293_loc := k_293 ;;
                              
                              @ret (_) (k_293) } : code (CEfset (
                                  [k_293_loc ; result_294_loc])) [interface] _))
                          else@ret (_) (k_293)) ;;
                      
                      @ret (_) (k_293) } : code (CEfset (
                          [k_293_loc ; result_294_loc])) [interface] _))) ;;
              
               '(k_293 : word_t) ←
                (foldi (usize 0) (usize 4) k_293 (fun i_302 (k_293 : _) =>
                    ({ code  '(k_293 : word_t) ←
                        ( temp_330 ←
                            (array_index (k_293) (i_302)) ;;
                           temp_332 ←
                            (array_index (w0_297) (i_302)) ;;
                           temp_334 ←
                            ((temp_330) .^ (temp_332)) ;;
                          ret (array_upd k_293 (i_302) (temp_334))) ;;
                      
                      @ret (_) (k_293) } : code (CEfset (
                          [k_280_loc ; k_293_loc ; result_294_loc])) [interface] _))) ;;
              
               '(result_294 : word_result_t) ←
                  ((ret (@Ok word_t int8 (k_293)))) ;;
                #put result_294_loc := result_294 ;;
              
              @ret (_) (prod_ce(k_293, result_294)) } : code (CEfset (
                  [k_280_loc ; k_293_loc ; result_294_loc])) [interface] _))
          else@ret (_) (prod_ce(k_293, result_294))) ;;
      
      @ret ((result int8 word_t)) (result_294) } : code (CEfset (
          [k_280_loc ; k_293_loc ; result_294_loc])) [interface] _)).
Fail Next Obligation.

Program Definition key_expansion_word
  (w0_297 : word_t)
  (w1_298 : word_t)
  (i_299 : uint_size)
  (nk_300 : uint_size)
  (nr_301 : uint_size)
  : both (CEfset ([k_280_loc ; k_293_loc ; result_294_loc])) [interface] (
    word_result_t) :=
  letbm k_293 : word_t loc( k_293_loc ) := lift_to_both0 w1_298 in
  letbm result_294 : (result int8 word_t) loc( result_294_loc ) :=
    @Err word_t int8 (lift_to_both0 invalid_key_expansion_index_v) in
  letb '(k_293, result_294) :=
    if (lift_to_both0 i_299) <.? ((lift_to_both0 (usize 4)) .* ((
          lift_to_both0 nr_301) .+ (lift_to_both0 (
            usize 1)))) :bool_ChoiceEquality
    then lift_scope (L1 := CEfset (
      [k_280_loc ; k_293_loc ; result_294_loc])) (L2 := CEfset (
      [k_280_loc ; k_293_loc ; result_294_loc])) (H_incl := _) (letb 'k_293 :=
        if ((lift_to_both0 i_299) %% (lift_to_both0 nk_300)) =.? (
          lift_to_both0 (usize 0)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
          [k_280_loc ; k_293_loc ; result_294_loc])) (L2 := CEfset (
          [k_280_loc ; k_293_loc ; result_294_loc])) (H_incl := _) (
          letbm k_293 loc( k_293_loc ) :=
            aes_keygen_assist (lift_to_both0 k_293) (array_index (rcon_v) ((
                  lift_to_both0 i_299) ./ (lift_to_both0 nk_300))) in
          lift_scope (H_incl := _) (lift_to_both0 k_293)
          )
        else lift_scope (L1 := CEfset (
          [k_293_loc ; result_294_loc])) (L2 := CEfset (
          [k_280_loc ; k_293_loc ; result_294_loc])) (H_incl := _) (
          letb 'k_293 :=
            if ((lift_to_both0 nk_300) >.? (lift_to_both0 (usize 6))) && (((
                  lift_to_both0 i_299) %% (lift_to_both0 nk_300)) =.? (
                lift_to_both0 (usize 4))) :bool_ChoiceEquality
            then lift_scope (L1 := CEfset (
              [k_293_loc ; result_294_loc])) (L2 := CEfset (
              [k_293_loc ; result_294_loc])) (H_incl := _) (
              letbm k_293 loc( k_293_loc ) :=
                slice_word (lift_to_both0 k_293) in
              lift_scope (H_incl := _) (lift_to_both0 k_293)
              )
            else lift_scope (H_incl := _) (lift_to_both0 k_293)
             in
          lift_scope (H_incl := _) (lift_to_both0 k_293)
          ) in
      letb k_293 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 4)) k_293 (L := (CEfset (
              [k_280_loc ; k_293_loc ; result_294_loc]))) (fun i_302 (
            k_293 : _) =>
          letb k_293 : word_t :=
            array_upd k_293 (lift_to_both0 i_302) (is_pure ((array_index (
                    k_293) (lift_to_both0 i_302)) .^ (array_index (w0_297) (
                    lift_to_both0 i_302)))) in
          lift_scope (H_incl := _) (lift_to_both0 k_293)
          ) in
      letbm result_294 loc( result_294_loc ) :=
        @Ok word_t int8 (lift_to_both0 k_293) in
      lift_scope (H_incl := _) (prod_b(
          lift_to_both0 k_293,
          lift_to_both0 result_294
        ))
      )
    else lift_scope (H_incl := _) (prod_b(
        lift_to_both0 k_293,
        lift_to_both0 result_294
      ))
     in
  lift_scope (H_incl := _) (lift_to_both0 result_294)
  .
Fail Next Obligation.

Definition key_expansion_aes_pure
  (key_339 : byte_seq)
  (nk_340 : uint_size)
  (nr_341 : uint_size)
  (key_schedule_length_342 : uint_size)
  (key_length_343 : uint_size)
  (iterations_344 : uint_size)
  : byte_seq_result_t :=
  let key_ex_337 : seq uint8 :=
    seq_new_ (default : uint8) (key_schedule_length_342) in 
  let key_ex_337 :=
    seq_update_start (key_ex_337) (key_339) in 
  let word_size_345 : uint_size :=
    key_length_343 in 
  key_ex_337 m( _ ) ⇠ (foldibnd (usize 0) to (
      iterations_344) M( _ ) for key_ex_337 >> (fun j_346 key_ex_337 =>
    let i_347 : uint_size :=
      ((j_346) .+ (word_size_345)) in 
     word_348 m( _ ) ⇠ (key_expansion_word (array_from_slice (
          default : uint8) (key_length_v) (key_ex_337) (((usize 4) .* (((
                  i_347) .- (word_size_345))))) (usize 4)) (array_from_slice (
          default : uint8) (key_length_v) (key_ex_337) (((((usize 4) .* (
                  i_347))) .- (usize 4))) (usize 4)) (i_347) (nk_340) (
        nr_341)) ;;
    (let key_ex_337 :=
        seq_update (key_ex_337) (((usize 4) .* (i_347))) (
          array_to_seq (word_348)) in 
      Ok ((key_ex_337))))) ;;
  (@Ok byte_seq int8 (key_ex_337)).
Definition key_expansion_aes_pure_code
  (key_339 : byte_seq)
  (nk_340 : uint_size)
  (nr_341 : uint_size)
  (key_schedule_length_342 : uint_size)
  (key_length_343 : uint_size)
  (iterations_344 : uint_size)
  : code fset.fset0 [interface] (@ct byte_seq_result_t) :=
  lift_to_code (key_expansion_aes_pure key_339
    nk_340
    nr_341
    key_schedule_length_342
    key_length_343
    iterations_344).

Definition key_ex_337_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 375%nat)).
Program Definition key_expansion_aes_state
  (key_339 : byte_seq)
  (nk_340 : uint_size)
  (nr_341 : uint_size)
  (key_schedule_length_342 : uint_size)
  (key_length_343 : uint_size)
  (iterations_344 : uint_size) : code (CEfset (
      [k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc])) [interface] (
    @ct (byte_seq_result_t)) :=
  (({ code  '(key_ex_337 : seq uint8) ←
          ( temp_350 ←
              (seq_new_ (default : uint8) (key_schedule_length_342)) ;;
            ret (temp_350)) ;;
        #put key_ex_337_loc := key_ex_337 ;;
       '(key_ex_337 : seq uint8) ←
          (( temp_352 ←
                (seq_update_start (key_ex_337) (key_339)) ;;
              ret (temp_352))) ;;
        #put key_ex_337_loc := key_ex_337 ;;
      
       '(word_size_345 : uint_size) ←
        (ret (key_length_343)) ;;
      bnd( ChoiceEqualityMonad.result_bind_code int8 , _ , byte_seq , CEfset (
        [k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc])) 'key_ex_337 ⇠
      (foldi_bind_code (usize 0) (iterations_344) (
          lift_to_code (ChoiceEqualityMonad.ret key_ex_337)) (fun j_346 key_ex_337 =>
        ({ code  '(i_347 : uint_size) ←
            ( temp_354 ←
                ((j_346) .+ (word_size_345)) ;;
              ret (temp_354)) ;;
          bnd( ChoiceEqualityMonad.result_bind_code _ , word_t , _ , CEfset (
            [k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc])) word_348 ⇠
          (({ code  temp_356 ←
                ((i_347) .- (word_size_345)) ;;
               temp_358 ←
                ((usize 4) .* (temp_356)) ;;
               temp_360 ←
                (array_from_slice (default : uint8) (key_length_v) (
                    key_ex_337) (temp_358) (usize 4)) ;;
               temp_362 ←
                ((usize 4) .* (i_347)) ;;
               temp_364 ←
                ((temp_362) .- (usize 4)) ;;
               temp_366 ←
                (array_from_slice (default : uint8) (key_length_v) (
                    key_ex_337) (temp_364) (usize 4)) ;;
               temp_368 ←
                (key_expansion_word (temp_360) (temp_366) (i_347) (nk_340) (
                    nr_341)) ;;
              @ret _ (temp_368) } : code _ [interface] _)) in
          ({ code  '(key_ex_337 : seq uint8) ←
                (( temp_370 ←
                      ((usize 4) .* (i_347)) ;;
                     '(temp_372 : seq uint8) ←
                      (array_to_seq (word_348)) ;;
                     temp_374 ←
                      (seq_update (key_ex_337) (temp_370) (temp_372)) ;;
                    ret (temp_374))) ;;
              #put key_ex_337_loc := key_ex_337 ;;
            
            @ret (_) (Ok (key_ex_337)) } : code _ [interface] _) } : code (
            CEfset (
              [k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc])) [interface] _))) in
      ({ code @ret ((result int8 byte_seq)) (@Ok byte_seq int8 (
            key_ex_337)) } : code _ [interface] _) } : code (CEfset (
          [k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc])) [interface] _)).
Fail Next Obligation.

Program Definition key_expansion_aes
  (key_339 : byte_seq)
  (nk_340 : uint_size)
  (nr_341 : uint_size)
  (key_schedule_length_342 : uint_size)
  (key_length_343 : uint_size)
  (iterations_344 : uint_size)
  : both (CEfset (
      [k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc])) [interface] (
    byte_seq_result_t) :=
  letbm key_ex_337 : seq uint8 loc( key_ex_337_loc ) :=
    seq_new_ (default : uint8) (lift_to_both0 key_schedule_length_342) in
  letbm key_ex_337 loc( key_ex_337_loc ) :=
    seq_update_start (lift_to_both0 key_ex_337) (lift_to_both0 key_339) in
  letb word_size_345 : uint_size := lift_to_both0 key_length_343 in
  letbnd(_) key_ex_337 :=
    foldi_bind_both' (lift_to_both0 (usize 0)) (
        lift_to_both0 iterations_344) key_ex_337 (L := (CEfset (
          [k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc]))) (fun j_346 (
        key_ex_337 : _) =>
      letb i_347 : uint_size :=
        (lift_to_both0 j_346) .+ (lift_to_both0 word_size_345) in
      letbnd(ChoiceEqualityMonad.result_bind_code int8) word_348 : word_t :=
        key_expansion_word (array_from_slice (default : uint8) (key_length_v) (
            lift_to_both0 key_ex_337) ((lift_to_both0 (usize 4)) .* ((
                lift_to_both0 i_347) .- (lift_to_both0 word_size_345))) (
            lift_to_both0 (usize 4))) (array_from_slice (default : uint8) (
            key_length_v) (lift_to_both0 key_ex_337) (((lift_to_both0 (
                  usize 4)) .* (lift_to_both0 i_347)) .- (lift_to_both0 (
                usize 4))) (lift_to_both0 (usize 4))) (lift_to_both0 i_347) (
          lift_to_both0 nk_340) (lift_to_both0 nr_341) in
      letbm key_ex_337 loc( key_ex_337_loc ) :=
        seq_update (lift_to_both0 key_ex_337) ((lift_to_both0 (usize 4)) .* (
            lift_to_both0 i_347)) (array_to_seq (lift_to_both0 word_348)) in
      lift_scope (H_incl := _) (Ok (lift_to_both0 key_ex_337))
      ) in
  lift_scope (H_incl := _) (@Ok byte_seq int8 (lift_to_both0 key_ex_337))
  .
Fail Next Obligation.

Definition aes_encrypt_block_pure
  (k_376 : byte_seq)
  (input_377 : block_t)
  (nk_378 : uint_size)
  (nr_379 : uint_size)
  (key_schedule_length_380 : uint_size)
  (key_length_381 : uint_size)
  (iterations_382 : uint_size)
  : block_result_t :=
   key_ex_383 m( _ ) ⇠ (key_expansion_aes (k_376) (nk_378) (nr_379) (
      key_schedule_length_380) (key_length_381) (iterations_382)) ;;
  (@Ok block_t int8 (block_cipher_aes (input_377) (key_ex_383) (nr_379))).
Definition aes_encrypt_block_pure_code
  (k_376 : byte_seq)
  (input_377 : block_t)
  (nk_378 : uint_size)
  (nr_379 : uint_size)
  (key_schedule_length_380 : uint_size)
  (key_length_381 : uint_size)
  (iterations_382 : uint_size)
  : code fset.fset0 [interface] (@ct block_result_t) :=
  lift_to_code (aes_encrypt_block_pure k_376
    input_377
    nk_378
    nr_379
    key_schedule_length_380
    key_length_381
    iterations_382).


Program Definition aes_encrypt_block_state
  (k_376 : byte_seq)
  (input_377 : block_t)
  (nk_378 : uint_size)
  (nr_379 : uint_size)
  (key_schedule_length_380 : uint_size)
  (key_length_381 : uint_size)
  (iterations_382 : uint_size) : code (CEfset (
      [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc])) [interface] (
    @ct (block_result_t)) :=
  (({ code bnd( ChoiceEqualityMonad.result_bind_code _ , byte_seq , _ , CEfset (
        [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc])) key_ex_383 ⇠
      (({ code  temp_385 ←
            (key_expansion_aes (k_376) (nk_378) (nr_379) (
                key_schedule_length_380) (key_length_381) (iterations_382)) ;;
          @ret _ (temp_385) } : code _ [interface] _)) in
      ({ code  temp_387 ←
          (block_cipher_aes (input_377) (key_ex_383) (nr_379)) ;;
        @ret ((result int8 block_t)) (@Ok block_t int8 (
            temp_387)) } : code _ [interface] _) } : code (CEfset (
          [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc])) [interface] _)).
Fail Next Obligation.

Program Definition aes_encrypt_block
  (k_376 : byte_seq)
  (input_377 : block_t)
  (nk_378 : uint_size)
  (nr_379 : uint_size)
  (key_schedule_length_380 : uint_size)
  (key_length_381 : uint_size)
  (iterations_382 : uint_size)
  : both (CEfset (
      [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc])) [interface] (
    block_result_t) :=
  letbnd(ChoiceEqualityMonad.result_bind_code int8) key_ex_383 : byte_seq :=
    key_expansion_aes (lift_to_both0 k_376) (lift_to_both0 nk_378) (
      lift_to_both0 nr_379) (lift_to_both0 key_schedule_length_380) (
      lift_to_both0 key_length_381) (lift_to_both0 iterations_382) in
  lift_scope (H_incl := _) (@Ok block_t int8 (block_cipher_aes (
        lift_to_both0 input_377) (lift_to_both0 key_ex_383) (
        lift_to_both0 nr_379)))
  .
Fail Next Obligation.

Definition aes128_encrypt_block_pure
  (k_388 : key128_t)
  (input_389 : block_t)
  : block_t :=
  result_unwrap (aes_encrypt_block (seq_from_seq (array_to_seq (k_388))) (
      input_389) (key_length_v) (rounds_v) (key_schedule_length_v) (
      key_length_v) (iterations_v)).
Definition aes128_encrypt_block_pure_code
  (k_388 : key128_t)
  (input_389 : block_t)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (aes128_encrypt_block_pure k_388 input_389).


Program Definition aes128_encrypt_block_state
  (k_388 : key128_t)
  (input_389 : block_t) : code (CEfset (
      [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc])) [interface] (
    @ct (block_t)) :=
  (({ code  '(temp_391 : seq uint8) ←
        (array_to_seq (k_388)) ;;
       temp_393 ←
        (seq_from_seq (temp_391)) ;;
       '(temp_395 : block_result_t) ←
        (aes_encrypt_block (temp_393) (input_389) (key_length_v) (rounds_v) (
            key_schedule_length_v) (key_length_v) (iterations_v)) ;;
       temp_397 ←
        (result_unwrap (temp_395)) ;;
      @ret (block_t) (temp_397) } : code (CEfset (
          [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc])) [interface] _)).
Fail Next Obligation.

Program Definition aes128_encrypt_block
  (k_388 : key128_t)
  (input_389 : block_t)
  : both (CEfset (
      [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc])) [interface] (
    block_t) :=
  lift_scope (H_incl := _) (result_unwrap (aes_encrypt_block (seq_from_seq (
          array_to_seq (lift_to_both0 k_388))) (lift_to_both0 input_389) (
        lift_to_both0 key_length_v) (lift_to_both0 rounds_v) (
        lift_to_both0 key_schedule_length_v) (lift_to_both0 key_length_v) (
        lift_to_both0 iterations_v)))
  .
Fail Next Obligation.

Definition aes_ctr_key_block_pure
  (k_400 : byte_seq)
  (n_401 : aes_nonce_t)
  (c_402 : uint32)
  (nk_403 : uint_size)
  (nr_404 : uint_size)
  (key_schedule_length_405 : uint_size)
  (key_length_406 : uint_size)
  (iterations_407 : uint_size)
  : block_result_t :=
  let input_398 : block_t :=
    array_new_ (default : uint8) (blocksize_v) in 
  let input_398 :=
    array_update (input_398) (usize 0) (array_to_seq (n_401)) in 
  let input_398 :=
    array_update (input_398) (usize 12) (array_to_seq (uint32_to_be_bytes (
        c_402))) in 
  aes_encrypt_block (k_400) (input_398) (nk_403) (nr_404) (
    key_schedule_length_405) (key_length_406) (iterations_407).
Definition aes_ctr_key_block_pure_code
  (k_400 : byte_seq)
  (n_401 : aes_nonce_t)
  (c_402 : uint32)
  (nk_403 : uint_size)
  (nr_404 : uint_size)
  (key_schedule_length_405 : uint_size)
  (key_length_406 : uint_size)
  (iterations_407 : uint_size)
  : code fset.fset0 [interface] (@ct block_result_t) :=
  lift_to_code (aes_ctr_key_block_pure k_400
    n_401
    c_402
    nk_403
    nr_404
    key_schedule_length_405
    key_length_406
    iterations_407).

Definition input_398_loc : ChoiceEqualityLocation :=
  ((block_t ; 422%nat)).
Program Definition aes_ctr_key_block_state
  (k_400 : byte_seq)
  (n_401 : aes_nonce_t)
  (c_402 : uint32)
  (nk_403 : uint_size)
  (nr_404 : uint_size)
  (key_schedule_length_405 : uint_size)
  (key_length_406 : uint_size)
  (iterations_407 : uint_size) : code (CEfset (
      [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc ; input_398_loc])) [interface] (
    @ct (block_result_t)) :=
  (({ code  '(input_398 : block_t) ←
          ( temp_409 ←
              (array_new_ (default : uint8) (blocksize_v)) ;;
            ret (temp_409)) ;;
        #put input_398_loc := input_398 ;;
       '(input_398 : block_t) ←
          (( '(temp_411 : seq uint8) ←
                (array_to_seq (n_401)) ;;
               temp_413 ←
                (array_update (input_398) (usize 0) (temp_411)) ;;
              ret (temp_413))) ;;
        #put input_398_loc := input_398 ;;
      
       input_398 ←
          (( temp_415 ←
                (uint32_to_be_bytes (c_402)) ;;
               '(temp_417 : seq uint8) ←
                (array_to_seq (ct_T temp_415)) ;;
               temp_419 ←
                (array_update (input_398) (usize 12) (temp_417)) ;;
              ret (temp_419))) ;;
        #put input_398_loc := input_398 ;;
      
       temp_421 ←
        (aes_encrypt_block (k_400) (input_398) (nk_403) (nr_404) (
            key_schedule_length_405) (key_length_406) (iterations_407)) ;;
      @ret (block_result_t) (temp_421) } : code (CEfset (
          [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc ; input_398_loc])) [interface] _)).
Fail Next Obligation.

Program Definition aes_ctr_key_block
  (k_400 : byte_seq)
  (n_401 : aes_nonce_t)
  (c_402 : uint32)
  (nk_403 : uint_size)
  (nr_404 : uint_size)
  (key_schedule_length_405 : uint_size)
  (key_length_406 : uint_size)
  (iterations_407 : uint_size)
  : both (CEfset (
      [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc ; input_398_loc])) [interface] (
    block_result_t) :=
  letbm input_398 : block_t loc( input_398_loc ) :=
    array_new_ (default : uint8) (blocksize_v) in
  letbm input_398 loc( input_398_loc ) :=
    array_update (lift_to_both0 input_398) (is_pure (lift_to_both0 (usize 0))) (
      array_to_seq (lift_to_both0 n_401)) in
  letbm input_398 loc( input_398_loc ) :=
        array_update (lift_to_both0 input_398) (is_pure (lift_to_both0 (usize 12))) (
      array_to_seq (uint32_to_be_bytes (lift_to_both0 c_402))) in
  lift_scope (H_incl := _) (aes_encrypt_block (lift_to_both0 k_400) (
      lift_to_both0 input_398) (lift_to_both0 nk_403) (lift_to_both0 nr_404) (
      lift_to_both0 key_schedule_length_405) (lift_to_both0 key_length_406) (
      lift_to_both0 iterations_407))
  .
Fail Next Obligation.

Definition xor_block_pure
  (block_425 : block_t)
  (key_block_426 : block_t)
  : block_t :=
  let out_423 : block_t :=
    block_425 in 
  let out_423 :=
    Hacspec_Lib_Pre.foldi (usize 0) (blocksize_v) out_423
      (fun i_427 out_423 =>
      let out_423 :=
        array_upd out_423 (i_427) (((array_index (out_423) (i_427)) .^ (
              array_index (key_block_426) (i_427)))) in 
      (out_423)) in 
  out_423.
Definition xor_block_pure_code
  (block_425 : block_t)
  (key_block_426 : block_t)
  : code fset.fset0 [interface] (@ct block_t) :=
  lift_to_code (xor_block_pure block_425 key_block_426).

Definition out_423_loc : ChoiceEqualityLocation :=
  ((block_t ; 434%nat)).
Program Definition xor_block_state
  (block_425 : block_t)
  (key_block_426 : block_t) : code (CEfset ([out_423_loc])) [interface] (@ct (
      block_t)) :=
  (({ code  '(out_423 : block_t) ←
          (ret (block_425)) ;;
        #put out_423_loc := out_423 ;;
       out_423 ←
        (foldi (usize 0) (blocksize_v) out_423 (fun i_427 (out_423 : _) =>
            ({ code  '(out_423 : block_t) ←
                ( temp_429 ←
                    (array_index (out_423) (i_427)) ;;
                   temp_431 ←
                    (array_index (key_block_426) (i_427)) ;;
                   temp_433 ←
                    ((temp_429) .^ (temp_431)) ;;
                  ret (array_upd out_423 (i_427) (temp_433))) ;;
              
              @ret (_) (out_423) } : code (CEfset (
                  [out_423_loc])) [interface] _))) ;;
      
      @ret (block_t) (out_423) } : code (CEfset (
          [out_423_loc])) [interface] _)).
Fail Next Obligation.

Program Definition xor_block
  (block_425 : block_t)
  (key_block_426 : block_t)
  : both (CEfset ([out_423_loc])) [interface] (block_t) :=
  letbm out_423 : block_t loc( out_423_loc ) := lift_to_both0 block_425 in
  letb out_423 :=
    foldi_both' (lift_to_both0 (usize 0)) (
        lift_to_both0 blocksize_v) out_423 (L := (CEfset (
          [out_423_loc]))) (fun i_427 (out_423 : _) =>
      letb out_423 : block_t :=
        array_upd out_423 (lift_to_both0 i_427) (is_pure ((array_index (
                out_423) (lift_to_both0 i_427)) .^ (array_index (
                key_block_426) (lift_to_both0 i_427)))) in
      lift_scope (H_incl := _) (lift_to_both0 out_423)
      ) in
  lift_scope (H_incl := _) (lift_to_both0 out_423)
  .
Fail Next Obligation.

Definition aes_counter_mode_pure
  (key_439 : byte_seq)
  (nonce_440 : aes_nonce_t)
  (counter_441 : uint32)
  (msg_442 : byte_seq)
  (nk_443 : uint_size)
  (nr_444 : uint_size)
  (key_schedule_length_445 : uint_size)
  (key_length_446 : uint_size)
  (iterations_447 : uint_size)
  : byte_seq_result_t :=
  let ctr_435 : uint32 :=
    counter_441 in 
  let blocks_out_436 : seq uint8 :=
    seq_new_ (default : uint8) (seq_len (msg_442)) in 
  let n_blocks_448 : uint_size :=
    seq_num_exact_chunks (msg_442) (blocksize_v) in 
  '(ctr_435, blocks_out_436) m( _ ) ⇠ (foldibnd (usize 0) to (
      n_blocks_448) M( _ ) for prod_ce(ctr_435, blocks_out_436) >> (fun i_449 '(
      ctr_435,
      blocks_out_436
    ) =>
    let msg_block_450 : seq uint8 :=
      seq_get_exact_chunk (msg_442) (blocksize_v) (i_449) in 
     key_block_451 m( _ ) ⇠ (aes_ctr_key_block (key_439) (nonce_440) (
        ctr_435) (nk_443) (nr_444) (key_schedule_length_445) (key_length_446) (
        iterations_447)) ;;
    (let blocks_out_436 :=
        seq_set_chunk (blocks_out_436) (blocksize_v) (i_449) (
          array_to_seq (xor_block (array_from_seq (blocksize_v) (
              msg_block_450)) (key_block_451))) in 
      let ctr_435 :=
        ((ctr_435) .+ (secret (@repr U32 1))) in 
      Ok (prod_ce(ctr_435, blocks_out_436))))) ;;
  (let last_block_452 : seq uint8 :=
      seq_get_remainder_chunk (msg_442) (blocksize_v) in 
    let last_block_len_453 : uint_size :=
      seq_len (last_block_452) in 
    ifbnd (((last_block_len_453) !=.? (usize 0))) : bool_ChoiceEquality
    thenbnd (let last_block_454 : block_t :=
        array_update_start (array_new_ (default : uint8) (blocksize_v)) (
          last_block_452) in 
       key_block_455 m( _ ) ⇠ (aes_ctr_key_block (key_439) (nonce_440) (
          ctr_435) (nk_443) (nr_444) (key_schedule_length_445) (
          key_length_446) (iterations_447)) ;;
      (let blocks_out_436 :=
          seq_set_chunk (blocks_out_436) (blocksize_v) (n_blocks_448) (
            array_slice_range (xor_block (last_block_454) (key_block_455)) (
              prod_ce(usize 0, last_block_len_453))) in 
        Ok ((blocks_out_436))))
    else ((blocks_out_436)) >> (fun '(blocks_out_436) =>
    @Ok byte_seq int8 (blocks_out_436))).
Definition aes_counter_mode_pure_code
  (key_439 : byte_seq)
  (nonce_440 : aes_nonce_t)
  (counter_441 : uint32)
  (msg_442 : byte_seq)
  (nk_443 : uint_size)
  (nr_444 : uint_size)
  (key_schedule_length_445 : uint_size)
  (key_length_446 : uint_size)
  (iterations_447 : uint_size)
  : code fset.fset0 [interface] (@ct byte_seq_result_t) :=
  lift_to_code (aes_counter_mode_pure key_439
    nonce_440
    counter_441
    msg_442
    nk_443
    nr_444
    key_schedule_length_445
    key_length_446
    iterations_447).

Definition blocks_out_436_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 496%nat)).
Definition ctr_435_loc : ChoiceEqualityLocation :=
  ((uint32 ; 497%nat)).
Program Definition aes_counter_mode_state
  (key_439 : byte_seq)
  (nonce_440 : aes_nonce_t)
  (counter_441 : uint32)
  (msg_442 : byte_seq)
  (nk_443 : uint_size)
  (nr_444 : uint_size)
  (key_schedule_length_445 : uint_size)
  (key_length_446 : uint_size)
  (iterations_447 : uint_size) : code (CEfset (
      [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc ; input_398_loc ; out_423_loc ; ctr_435_loc ; blocks_out_436_loc])) [interface] (
    @ct (byte_seq_result_t)) :=
  (({ code  '(ctr_435 : uint32) ←
          (ret (counter_441)) ;;
        #put ctr_435_loc := ctr_435 ;;
       '(blocks_out_436 : seq uint8) ←
          ( temp_457 ←
              (seq_len (msg_442)) ;;
             temp_459 ←
              (seq_new_ (default : uint8) (temp_457)) ;;
            ret (temp_459)) ;;
        #put blocks_out_436_loc := blocks_out_436 ;;
       '(n_blocks_448 : uint_size) ←
        ( temp_461 ←
            (seq_num_exact_chunks (msg_442) (blocksize_v)) ;;
          ret (temp_461)) ;;
      bnd( ChoiceEqualityMonad.result_bind_code int8 , _ , byte_seq , CEfset (
        [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc ; input_398_loc ; out_423_loc ; ctr_435_loc ; blocks_out_436_loc])) '(
        ctr_435,
        blocks_out_436
      ) ⇠
      (foldi_bind_code (usize 0) (n_blocks_448) (
          lift_to_code (ChoiceEqualityMonad.ret prod_ce(ctr_435, blocks_out_436
          ))) (fun i_449 '(ctr_435, blocks_out_436) =>
        ({ code  '(msg_block_450 : seq uint8) ←
            ( temp_463 ←
                (seq_get_exact_chunk (msg_442) (blocksize_v) (i_449)) ;;
              ret (temp_463)) ;;
          bnd( ChoiceEqualityMonad.result_bind_code _ , block_t , _ , CEfset (
            [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc ; input_398_loc ; out_423_loc ; ctr_435_loc ; blocks_out_436_loc])) key_block_451 ⇠
          (({ code  temp_465 ←
                (aes_ctr_key_block (key_439) (nonce_440) (ctr_435) (nk_443) (
                    nr_444) (key_schedule_length_445) (key_length_446) (
                    iterations_447)) ;;
              @ret _ (temp_465) } : code _ [interface] _)) in
          ({ code  '(blocks_out_436 : seq uint8) ←
                (( temp_467 ←
                      (array_from_seq (blocksize_v) (msg_block_450)) ;;
                     '(temp_469 : block_t) ←
                      (xor_block (temp_467) (key_block_451)) ;;
                     '(temp_471 : seq uint8) ←
                      (array_to_seq (temp_469)) ;;
                     temp_473 ←
                      (seq_set_chunk (blocks_out_436) (blocksize_v) (i_449) (
                          temp_471)) ;;
                    ret (temp_473))) ;;
              #put blocks_out_436_loc := blocks_out_436 ;;
            
             '(ctr_435 : uint32) ←
                (( '(temp_475 : int32) ←
                      (secret (@repr U32 1)) ;;
                     temp_477 ←
                      ((ctr_435) .+ (temp_475)) ;;
                    ret (temp_477))) ;;
              #put ctr_435_loc := ctr_435 ;;
            
            @ret (_) (Ok (prod_ce(ctr_435, blocks_out_436
                ))) } : code _ [interface] _) } : code (CEfset (
              [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc ; input_398_loc ; out_423_loc ; ctr_435_loc ; blocks_out_436_loc])) [interface] _))) in
      ({ code  '(last_block_452 : seq uint8) ←
          ( temp_479 ←
              (seq_get_remainder_chunk (msg_442) (blocksize_v)) ;;
            ret (temp_479)) ;;
         '(last_block_len_453 : uint_size) ←
          ( temp_481 ←
              (seq_len (last_block_452)) ;;
            ret (temp_481)) ;;
         temp_483 ←
          ((last_block_len_453) !=.? (usize 0)) ;;
        bnd( ChoiceEqualityMonad.result_bind_code int8 , _ , byte_seq , CEfset (
          [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc ; input_398_loc ; out_423_loc ; ctr_435_loc ; blocks_out_436_loc])) 'blocks_out_436 ⇠
        (if temp_483 : bool_ChoiceEquality
          then ({ code ({ code  '(last_block_454 : block_t) ←
                ( temp_485 ←
                    (array_new_ (default : uint8) (blocksize_v)) ;;
                   temp_487 ←
                    (array_update_start (ct_T temp_485) (last_block_452)) ;;
                  ret (temp_487)) ;;
              bnd( ChoiceEqualityMonad.result_bind_code _ , block_t , _ , CEfset (
                [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc ; input_398_loc ; out_423_loc ; ctr_435_loc ; blocks_out_436_loc])) key_block_455 ⇠
              (({ code  temp_489 ←
                    (aes_ctr_key_block (key_439) (nonce_440) (ctr_435) (
                        nk_443) (nr_444) (key_schedule_length_445) (
                        key_length_446) (iterations_447)) ;;
                  @ret _ (temp_489) } : code _ [interface] _)) in
              ({ code  '(blocks_out_436 : seq uint8) ←
                    (( '(temp_491 : block_t) ←
                          (xor_block (last_block_454) (key_block_455)) ;;
                         temp_493 ←
                          (array_slice_range (temp_491) (prod_ce(
                                usize 0,
                                last_block_len_453
                              ))) ;;
                         temp_495 ←
                          (seq_set_chunk (blocks_out_436) (blocksize_v) (
                              n_blocks_448) (temp_493)) ;;
                        ret (temp_495))) ;;
                  #put blocks_out_436_loc := blocks_out_436 ;;
                
                @ret (_) (Ok (
                    blocks_out_436)) } : code _ [interface] _) } : code (
                CEfset (
                  [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc ; input_398_loc ; out_423_loc ; ctr_435_loc ; blocks_out_436_loc])) [interface] _) } : code _ [interface] _)
          else ({ code @ret (_) (Ok (
                blocks_out_436)) } : code _ [interface] _) ) in
        ({ code @ret ((result int8 byte_seq)) (@Ok byte_seq int8 (
              blocks_out_436)) } : code _ [interface] _) } : code _ [interface] _) } : code (
        CEfset (
          [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc ; input_398_loc ; out_423_loc ; ctr_435_loc ; blocks_out_436_loc])) [interface] _)).
Fail Next Obligation.

Program Definition aes_counter_mode
  (key_439 : byte_seq)
  (nonce_440 : aes_nonce_t)
  (counter_441 : uint32)
  (msg_442 : byte_seq)
  (nk_443 : uint_size)
  (nr_444 : uint_size)
  (key_schedule_length_445 : uint_size)
  (key_length_446 : uint_size)
  (iterations_447 : uint_size)
  : both (CEfset (
      [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc ; input_398_loc ; out_423_loc ; ctr_435_loc ; blocks_out_436_loc])) [interface] (
    byte_seq_result_t) :=
  letbm ctr_435 : uint32 loc( ctr_435_loc ) := lift_to_both0 counter_441 in
  letbm blocks_out_436 : seq uint8 loc( blocks_out_436_loc ) :=
    seq_new_ (default : uint8) (seq_len (lift_to_both0 msg_442)) in
  letb n_blocks_448 : uint_size :=
    seq_num_exact_chunks (lift_to_both0 msg_442) (lift_to_both0 blocksize_v) in
  letbnd(_) '(ctr_435, blocks_out_436) :=
    foldi_bind_both' (lift_to_both0 (usize 0)) (lift_to_both0 n_blocks_448) prod_ce(
        ctr_435,
        blocks_out_436
      ) (L := (CEfset (
          [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc ; input_398_loc ; out_423_loc ; ctr_435_loc ; blocks_out_436_loc]))) (fun i_449 
        '(ctr_435, blocks_out_436) =>
      letb msg_block_450 : seq uint8 :=
        seq_get_exact_chunk (lift_to_both0 msg_442) (
          lift_to_both0 blocksize_v) (lift_to_both0 i_449) in
      letbnd(ChoiceEqualityMonad.result_bind_code int8) key_block_451 : block_t :=
        aes_ctr_key_block (lift_to_both0 key_439) (lift_to_both0 nonce_440) (
          lift_to_both0 ctr_435) (lift_to_both0 nk_443) (lift_to_both0 nr_444) (
          lift_to_both0 key_schedule_length_445) (
          lift_to_both0 key_length_446) (lift_to_both0 iterations_447) in
      letbm blocks_out_436 loc( blocks_out_436_loc ) :=
        seq_set_chunk (lift_to_both0 blocks_out_436) (
          lift_to_both0 blocksize_v) (lift_to_both0 i_449) (
          array_to_seq (xor_block (array_from_seq (blocksize_v) (
              lift_to_both0 msg_block_450)) (lift_to_both0 key_block_451))) in
      letbm ctr_435 loc( ctr_435_loc ) :=
        (lift_to_both0 ctr_435) .+ (secret (lift_to_both0 (@repr U32 1))) in
      lift_scope (H_incl := _) (Ok (prod_b(
            lift_to_both0 ctr_435,
            lift_to_both0 blocks_out_436
          )))
      ) in
  letb last_block_452 : seq uint8 :=
    seq_get_remainder_chunk (lift_to_both0 msg_442) (
      lift_to_both0 blocksize_v) in
  letb last_block_len_453 : uint_size :=
    seq_len (lift_to_both0 last_block_452) in
  letbnd(_) 'blocks_out_436 :=
    if (lift_to_both0 last_block_len_453) !=.? (lift_to_both0 (
        usize 0)) :bool_ChoiceEquality
    then lift_scope (L1 := CEfset (
      [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc ; input_398_loc ; out_423_loc ; ctr_435_loc ; blocks_out_436_loc])) (L2 := CEfset (
      [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc ; input_398_loc ; out_423_loc ; ctr_435_loc ; blocks_out_436_loc])) (H_incl := _) (
      letb last_block_454 : block_t :=
        array_update_start (array_new_ (default : uint8) (blocksize_v)) (
          lift_to_both0 last_block_452) in
      letbnd(ChoiceEqualityMonad.result_bind_code int8) key_block_455 : block_t :=
        aes_ctr_key_block (lift_to_both0 key_439) (lift_to_both0 nonce_440) (
          lift_to_both0 ctr_435) (lift_to_both0 nk_443) (lift_to_both0 nr_444) (
          lift_to_both0 key_schedule_length_445) (
          lift_to_both0 key_length_446) (lift_to_both0 iterations_447) in
      letbm blocks_out_436 loc( blocks_out_436_loc ) :=
        seq_set_chunk (lift_to_both0 blocks_out_436) (
          lift_to_both0 blocksize_v) (lift_to_both0 n_blocks_448) (
          array_slice_range (xor_block (lift_to_both0 last_block_454) (
              lift_to_both0 key_block_455)) (prod_b(
              lift_to_both0 (usize 0),
              lift_to_both0 last_block_len_453
            ))) in
      lift_scope (H_incl := _) (Ok (lift_to_both0 blocks_out_436))
      )
    else lift_scope (H_incl := _) (Ok (lift_to_both0 blocks_out_436))
     in
  lift_scope (H_incl := _) (@Ok byte_seq int8 (lift_to_both0 blocks_out_436))
  .
Fail Next Obligation.

Definition aes128_encrypt_pure
  (key_498 : key128_t)
  (nonce_499 : aes_nonce_t)
  (counter_500 : uint32)
  (msg_501 : byte_seq)
  : byte_seq :=
  result_unwrap (aes_counter_mode (seq_from_seq (array_to_seq (key_498))) (
      nonce_499) (counter_500) (msg_501) (key_length_v) (rounds_v) (
      key_schedule_length_v) (key_length_v) (iterations_v)).
Definition aes128_encrypt_pure_code
  (key_498 : key128_t)
  (nonce_499 : aes_nonce_t)
  (counter_500 : uint32)
  (msg_501 : byte_seq)
  : code fset.fset0 [interface] (@ct byte_seq) :=
  lift_to_code (aes128_encrypt_pure key_498 nonce_499 counter_500 msg_501).


Program Definition aes128_encrypt_state
  (key_498 : key128_t)
  (nonce_499 : aes_nonce_t)
  (counter_500 : uint32)
  (msg_501 : byte_seq) : code (CEfset (
      [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc ; input_398_loc ; out_423_loc ; ctr_435_loc ; blocks_out_436_loc])) [interface] (
    @ct (byte_seq)) :=
  (({ code  '(temp_503 : seq uint8) ←
        (array_to_seq (key_498)) ;;
       temp_505 ←
        (seq_from_seq (temp_503)) ;;
       '(temp_507 : byte_seq_result_t) ←
        (aes_counter_mode (temp_505) (nonce_499) (counter_500) (msg_501) (
            key_length_v) (rounds_v) (key_schedule_length_v) (key_length_v) (
            iterations_v)) ;;
       temp_509 ←
        (result_unwrap (temp_507)) ;;
      @ret (seq uint8) (temp_509) } : code (CEfset (
          [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc ; input_398_loc ; out_423_loc ; ctr_435_loc ; blocks_out_436_loc])) [interface] _)).
Fail Next Obligation.

Program Definition aes128_encrypt
  (key_498 : key128_t)
  (nonce_499 : aes_nonce_t)
  (counter_500 : uint32)
  (msg_501 : byte_seq)
  : both (CEfset (
      [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc ; input_398_loc ; out_423_loc ; ctr_435_loc ; blocks_out_436_loc])) [interface] (
    byte_seq) :=
  lift_scope (H_incl := _) (result_unwrap (aes_counter_mode (seq_from_seq (
          array_to_seq (lift_to_both0 key_498))) (lift_to_both0 nonce_499) (
        lift_to_both0 counter_500) (lift_to_both0 msg_501) (
        lift_to_both0 key_length_v) (lift_to_both0 rounds_v) (
        lift_to_both0 key_schedule_length_v) (lift_to_both0 key_length_v) (
        lift_to_both0 iterations_v)))
  .
Fail Next Obligation.

Definition aes128_decrypt_pure
  (key_510 : key128_t)
  (nonce_511 : aes_nonce_t)
  (counter_512 : uint32)
  (ctxt_513 : byte_seq)
  : byte_seq :=
  result_unwrap (aes_counter_mode (seq_from_seq (array_to_seq (key_510))) (
      nonce_511) (counter_512) (ctxt_513) (key_length_v) (rounds_v) (
      key_schedule_length_v) (key_length_v) (iterations_v)).
Definition aes128_decrypt_pure_code
  (key_510 : key128_t)
  (nonce_511 : aes_nonce_t)
  (counter_512 : uint32)
  (ctxt_513 : byte_seq)
  : code fset.fset0 [interface] (@ct byte_seq) :=
  lift_to_code (aes128_decrypt_pure key_510 nonce_511 counter_512 ctxt_513).


Program Definition aes128_decrypt_state
  (key_510 : key128_t)
  (nonce_511 : aes_nonce_t)
  (counter_512 : uint32)
  (ctxt_513 : byte_seq) : code (CEfset (
      [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc ; input_398_loc ; out_423_loc ; ctr_435_loc ; blocks_out_436_loc])) [interface] (
    @ct (byte_seq)) :=
  (({ code  '(temp_515 : seq uint8) ←
        (array_to_seq (key_510)) ;;
       temp_517 ←
        (seq_from_seq (temp_515)) ;;
       '(temp_519 : byte_seq_result_t) ←
        (aes_counter_mode (temp_517) (nonce_511) (counter_512) (ctxt_513) (
            key_length_v) (rounds_v) (key_schedule_length_v) (key_length_v) (
            iterations_v)) ;;
       temp_521 ←
        (result_unwrap (temp_519)) ;;
      @ret (seq uint8) (temp_521) } : code (CEfset (
          [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc ; input_398_loc ; out_423_loc ; ctr_435_loc ; blocks_out_436_loc])) [interface] _)).
Fail Next Obligation.

Program Definition aes128_decrypt
  (key_510 : key128_t)
  (nonce_511 : aes_nonce_t)
  (counter_512 : uint32)
  (ctxt_513 : byte_seq)
  : both (CEfset (
      [st_0_loc ; out_11_loc ; st_89_loc ; out_172_loc ; out_207_loc ; k_280_loc ; k_293_loc ; result_294_loc ; key_ex_337_loc ; input_398_loc ; out_423_loc ; ctr_435_loc ; blocks_out_436_loc])) [interface] (
    byte_seq) :=
  lift_scope (H_incl := _) (result_unwrap (aes_counter_mode (seq_from_seq (
          array_to_seq (lift_to_both0 key_510))) (lift_to_both0 nonce_511) (
        lift_to_both0 counter_512) (lift_to_both0 ctxt_513) (
        lift_to_both0 key_length_v) (lift_to_both0 rounds_v) (
        lift_to_both0 key_schedule_length_v) (lift_to_both0 key_length_v) (
        lift_to_both0 iterations_v)))
  .
Fail Next Obligation.

