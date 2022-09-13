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

Definition st_0_loc : ChoiceEqualityLocation :=
  ((block_t ; 1%nat)).
Notation "'sub_bytes_inp'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'sub_bytes_inp'" :=(block_t : ChoiceEquality) (at level 2).
Notation "'sub_bytes_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'sub_bytes_out'" :=(block_t : ChoiceEquality) (at level 2).
Definition SUB_BYTES : nat :=
  (4).
Program Definition sub_bytes
  : both_package (CEfset ([st_0_loc])) [interface] [(SUB_BYTES,(
      sub_bytes_inp,sub_bytes_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(state_2) := temp_inp : block_t in
    
    ((letbm st_0 : block_t loc( st_0_loc ) := lift_to_both0 state_2 in
        letb st_0 :=
          foldi_both' (lift_to_both0 (usize 0)) (
              lift_to_both0 blocksize_v) st_0 (L := (CEfset (
                [st_0_loc]))) (I := ([interface])) (fun i_3 st_0 =>
            letb st_0 : block_t :=
              array_upd st_0 (lift_to_both0 i_3) (is_pure (array_index (
                    sbox_v) (uint8_declassify (array_index (state_2) (
                        lift_to_both0 i_3))))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 st_0)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 st_0)
        ) : both (CEfset ([st_0_loc])) [interface] (block_t)))in
  both_package' _ _ (SUB_BYTES,(sub_bytes_inp,sub_bytes_out)) temp_package_both.
Fail Next Obligation.

Definition out_5_loc : ChoiceEqualityLocation :=
  ((block_t ; 6%nat)).
Notation "'shift_row_inp'" :=(
  uint_size '× uint_size '× block_t : choice_type) (in custom pack_type at level 2).
Notation "'shift_row_inp'" :=(
  uint_size '× uint_size '× block_t : ChoiceEquality) (at level 2).
Notation "'shift_row_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'shift_row_out'" :=(block_t : ChoiceEquality) (at level 2).
Definition SHIFT_ROW : nat :=
  (10).
Program Definition shift_row
  : both_package (CEfset ([out_5_loc])) [interface] [(SHIFT_ROW,(
      shift_row_inp,shift_row_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      i_8 , shift_9 , state_7) := temp_inp : uint_size '× uint_size '× block_t in
    
    ((letbm out_5 : block_t loc( out_5_loc ) := lift_to_both0 state_7 in
        letb out_5 : block_t :=
          array_upd out_5 (lift_to_both0 i_8) (is_pure (array_index (state_7) ((
                  lift_to_both0 i_8) .+ ((lift_to_both0 (usize 4)) .* ((
                      lift_to_both0 shift_9) %% (lift_to_both0 (
                        usize 4))))))) in
        letb out_5 : block_t :=
          array_upd out_5 ((lift_to_both0 i_8) .+ (lift_to_both0 (usize 4))) (
            is_pure (array_index (state_7) ((lift_to_both0 i_8) .+ ((
                    lift_to_both0 (usize 4)) .* (((lift_to_both0 shift_9) .+ (
                        lift_to_both0 (usize 1))) %% (lift_to_both0 (
                        usize 4))))))) in
        letb out_5 : block_t :=
          array_upd out_5 ((lift_to_both0 i_8) .+ (lift_to_both0 (usize 8))) (
            is_pure (array_index (state_7) ((lift_to_both0 i_8) .+ ((
                    lift_to_both0 (usize 4)) .* (((lift_to_both0 shift_9) .+ (
                        lift_to_both0 (usize 2))) %% (lift_to_both0 (
                        usize 4))))))) in
        letb out_5 : block_t :=
          array_upd out_5 ((lift_to_both0 i_8) .+ (lift_to_both0 (usize 12))) (
            is_pure (array_index (state_7) ((lift_to_both0 i_8) .+ ((
                    lift_to_both0 (usize 4)) .* (((lift_to_both0 shift_9) .+ (
                        lift_to_both0 (usize 3))) %% (lift_to_both0 (
                        usize 4))))))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 out_5)
        ) : both (CEfset ([out_5_loc])) [interface] (block_t)))in
  both_package' _ _ (SHIFT_ROW,(shift_row_inp,shift_row_out)) temp_package_both.
Fail Next Obligation.


Notation "'shift_rows_inp'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'shift_rows_inp'" :=(block_t : ChoiceEquality) (at level 2).
Notation "'shift_rows_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'shift_rows_out'" :=(block_t : ChoiceEquality) (at level 2).
Definition SHIFT_ROWS : nat :=
  (14).
Program Definition shift_rows
  : both_package (CEfset ([])) [interface
  #val #[ SHIFT_ROW ] : shift_row_inp → shift_row_out ] [(SHIFT_ROWS,(
      shift_rows_inp,shift_rows_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(state_11) := temp_inp : block_t in
    
    let shift_row := fun x_0 x_1 x_2 => package_both shift_row (x_0,x_1,x_2) in
    ((letb state_12 : block_t :=
          shift_row (lift_to_both0 (usize 1)) (lift_to_both0 (usize 1)) (
            lift_to_both0 state_11) in
        letb state_13 : block_t :=
          shift_row (lift_to_both0 (usize 2)) (lift_to_both0 (usize 2)) (
            lift_to_both0 state_12) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (shift_row (
            lift_to_both0 (usize 3)) (lift_to_both0 (usize 3)) (
            lift_to_both0 state_13))
        ) : both (CEfset ([])) [interface
      #val #[ SHIFT_ROW ] : shift_row_inp → shift_row_out ] (block_t)))in
  both_package' _ _ (SHIFT_ROWS,(
      shift_rows_inp,shift_rows_out)) temp_package_both.
Fail Next Obligation.


Notation "'xtime_inp'" :=(uint8 : choice_type) (in custom pack_type at level 2).
Notation "'xtime_inp'" :=(uint8 : ChoiceEquality) (at level 2).
Notation "'xtime_out'" :=(uint8 : choice_type) (in custom pack_type at level 2).
Notation "'xtime_out'" :=(uint8 : ChoiceEquality) (at level 2).
Definition XTIME : nat :=
  (20).
Program Definition xtime
  : both_package (fset.fset0) [interface] [(XTIME,(xtime_inp,xtime_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_15) := temp_inp : uint8 in
    
    ((letb x1_16 : uint8 :=
          (lift_to_both0 x_15) shift_left (lift_to_both0 (usize 1)) in
        letb x7_17 : uint8 :=
          (lift_to_both0 x_15) shift_right (lift_to_both0 (usize 7)) in
        letb x71_18 : uint8 :=
          (lift_to_both0 x7_17) .& (secret (lift_to_both0 (@repr U8 1))) in
        letb x711b_19 : uint8 :=
          (lift_to_both0 x71_18) .* (secret (lift_to_both0 (@repr U8 27))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
            lift_to_both0 x1_16) .^ (lift_to_both0 x711b_19))
        ) : both (fset.fset0) [interface] (uint8)))in
  both_package' _ _ (XTIME,(xtime_inp,xtime_out)) temp_package_both.
Fail Next Obligation.

Definition st_21_loc : ChoiceEqualityLocation :=
  ((block_t ; 22%nat)).
Notation "'mix_column_inp'" :=(
  uint_size '× block_t : choice_type) (in custom pack_type at level 2).
Notation "'mix_column_inp'" :=(
  uint_size '× block_t : ChoiceEquality) (at level 2).
Notation "'mix_column_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'mix_column_out'" :=(block_t : ChoiceEquality) (at level 2).
Definition MIX_COLUMN : nat :=
  (31).
Program Definition mix_column
  : both_package (CEfset ([st_21_loc])) [interface
  #val #[ XTIME ] : xtime_inp → xtime_out ] [(MIX_COLUMN,(
      mix_column_inp,mix_column_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(c_23 , state_25) := temp_inp : uint_size '× block_t in
    
    let xtime := fun x_0 => package_both xtime (x_0) in
    ((letb i0_24 : uint_size :=
          (lift_to_both0 (usize 4)) .* (lift_to_both0 c_23) in
        letb s0_26 : uint8 := array_index (state_25) (lift_to_both0 i0_24) in
        letb s1_27 : uint8 :=
          array_index (state_25) ((lift_to_both0 i0_24) .+ (lift_to_both0 (
                usize 1))) in
        letb s2_28 : uint8 :=
          array_index (state_25) ((lift_to_both0 i0_24) .+ (lift_to_both0 (
                usize 2))) in
        letb s3_29 : uint8 :=
          array_index (state_25) ((lift_to_both0 i0_24) .+ (lift_to_both0 (
                usize 3))) in
        letbm st_21 : block_t loc( st_21_loc ) := lift_to_both0 state_25 in
        letb tmp_30 : uint8 :=
          (((lift_to_both0 s0_26) .^ (lift_to_both0 s1_27)) .^ (
              lift_to_both0 s2_28)) .^ (lift_to_both0 s3_29) in
        letb st_21 : block_t :=
          array_upd st_21 (lift_to_both0 i0_24) (is_pure (((
                  lift_to_both0 s0_26) .^ (lift_to_both0 tmp_30)) .^ (xtime ((
                    lift_to_both0 s0_26) .^ (lift_to_both0 s1_27))))) in
        letb st_21 : block_t :=
          array_upd st_21 ((lift_to_both0 i0_24) .+ (lift_to_both0 (usize 1))) (
            is_pure (((lift_to_both0 s1_27) .^ (lift_to_both0 tmp_30)) .^ (
                xtime ((lift_to_both0 s1_27) .^ (lift_to_both0 s2_28))))) in
        letb st_21 : block_t :=
          array_upd st_21 ((lift_to_both0 i0_24) .+ (lift_to_both0 (usize 2))) (
            is_pure (((lift_to_both0 s2_28) .^ (lift_to_both0 tmp_30)) .^ (
                xtime ((lift_to_both0 s2_28) .^ (lift_to_both0 s3_29))))) in
        letb st_21 : block_t :=
          array_upd st_21 ((lift_to_both0 i0_24) .+ (lift_to_both0 (usize 3))) (
            is_pure (((lift_to_both0 s3_29) .^ (lift_to_both0 tmp_30)) .^ (
                xtime ((lift_to_both0 s3_29) .^ (lift_to_both0 s0_26))))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 st_21)
        ) : both (CEfset ([st_21_loc])) [interface
      #val #[ XTIME ] : xtime_inp → xtime_out ] (block_t)))in
  both_package' _ _ (MIX_COLUMN,(
      mix_column_inp,mix_column_out)) temp_package_both.
Fail Next Obligation.


Notation "'mix_columns_inp'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'mix_columns_inp'" :=(block_t : ChoiceEquality) (at level 2).
Notation "'mix_columns_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'mix_columns_out'" :=(block_t : ChoiceEquality) (at level 2).
Definition MIX_COLUMNS : nat :=
  (36).
Program Definition mix_columns
  : both_package (CEfset ([])) [interface
  #val #[ MIX_COLUMN ] : mix_column_inp → mix_column_out ] [(MIX_COLUMNS,(
      mix_columns_inp,mix_columns_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(state_32) := temp_inp : block_t in
    
    let mix_column := fun x_0 x_1 => package_both mix_column (x_0,x_1) in
    ((letb state_33 : block_t :=
          mix_column (lift_to_both0 (usize 0)) (lift_to_both0 state_32) in
        letb state_34 : block_t :=
          mix_column (lift_to_both0 (usize 1)) (lift_to_both0 state_33) in
        letb state_35 : block_t :=
          mix_column (lift_to_both0 (usize 2)) (lift_to_both0 state_34) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (mix_column (
            lift_to_both0 (usize 3)) (lift_to_both0 state_35))
        ) : both (CEfset ([])) [interface
      #val #[ MIX_COLUMN ] : mix_column_inp → mix_column_out ] (block_t)))in
  both_package' _ _ (MIX_COLUMNS,(
      mix_columns_inp,mix_columns_out)) temp_package_both.
Fail Next Obligation.

Definition out_37_loc : ChoiceEqualityLocation :=
  ((block_t ; 38%nat)).
Notation "'add_round_key_inp'" :=(
  block_t '× round_key_t : choice_type) (in custom pack_type at level 2).
Notation "'add_round_key_inp'" :=(
  block_t '× round_key_t : ChoiceEquality) (at level 2).
Notation "'add_round_key_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'add_round_key_out'" :=(block_t : ChoiceEquality) (at level 2).
Definition ADD_ROUND_KEY : nat :=
  (42).
Program Definition add_round_key
  : both_package (CEfset ([out_37_loc])) [interface] [(ADD_ROUND_KEY,(
      add_round_key_inp,add_round_key_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(state_39 , key_41) := temp_inp : block_t '× round_key_t in
    
    ((letbm out_37 : block_t loc( out_37_loc ) := lift_to_both0 state_39 in
        letb out_37 :=
          foldi_both' (lift_to_both0 (usize 0)) (
              lift_to_both0 blocksize_v) out_37 (L := (CEfset (
                [out_37_loc]))) (I := ([interface])) (fun i_40 out_37 =>
            letb out_37 : block_t :=
              array_upd out_37 (lift_to_both0 i_40) (is_pure ((array_index (
                      out_37) (lift_to_both0 i_40)) .^ (array_index (key_41) (
                      lift_to_both0 i_40)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 out_37)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 out_37)
        ) : both (CEfset ([out_37_loc])) [interface] (block_t)))in
  both_package' _ _ (ADD_ROUND_KEY,(
      add_round_key_inp,add_round_key_out)) temp_package_both.
Fail Next Obligation.


Notation "'aes_enc_inp'" :=(
  block_t '× round_key_t : choice_type) (in custom pack_type at level 2).
Notation "'aes_enc_inp'" :=(
  block_t '× round_key_t : ChoiceEquality) (at level 2).
Notation "'aes_enc_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'aes_enc_out'" :=(block_t : ChoiceEquality) (at level 2).
Definition AES_ENC : nat :=
  (48).
Program Definition aes_enc
  : both_package (CEfset ([])) [interface
  #val #[ ADD_ROUND_KEY ] : add_round_key_inp → add_round_key_out ;
  #val #[ MIX_COLUMNS ] : mix_columns_inp → mix_columns_out ;
  #val #[ SHIFT_ROWS ] : shift_rows_inp → shift_rows_out ;
  #val #[ SUB_BYTES ] : sub_bytes_inp → sub_bytes_out ] [(AES_ENC,(
      aes_enc_inp,aes_enc_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(state_43 , round_key_47) := temp_inp : block_t '× round_key_t in
    
    let add_round_key := fun x_0 x_1 => package_both add_round_key (x_0,x_1) in
    let mix_columns := fun x_0 => package_both mix_columns (x_0) in
    let shift_rows := fun x_0 => package_both shift_rows (x_0) in
    let sub_bytes := fun x_0 => package_both sub_bytes (x_0) in
    ((letb state_44 : block_t := sub_bytes (lift_to_both0 state_43) in
        letb state_45 : block_t := shift_rows (lift_to_both0 state_44) in
        letb state_46 : block_t := mix_columns (lift_to_both0 state_45) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (add_round_key (
            lift_to_both0 state_46) (lift_to_both0 round_key_47))
        ) : both (CEfset ([])) [interface
      #val #[ ADD_ROUND_KEY ] : add_round_key_inp → add_round_key_out ;
      #val #[ MIX_COLUMNS ] : mix_columns_inp → mix_columns_out ;
      #val #[ SHIFT_ROWS ] : shift_rows_inp → shift_rows_out ;
      #val #[ SUB_BYTES ] : sub_bytes_inp → sub_bytes_out ] (block_t)))in
  both_package' _ _ (AES_ENC,(aes_enc_inp,aes_enc_out)) temp_package_both.
Fail Next Obligation.


Notation "'aes_enc_last_inp'" :=(
  block_t '× round_key_t : choice_type) (in custom pack_type at level 2).
Notation "'aes_enc_last_inp'" :=(
  block_t '× round_key_t : ChoiceEquality) (at level 2).
Notation "'aes_enc_last_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'aes_enc_last_out'" :=(block_t : ChoiceEquality) (at level 2).
Definition AES_ENC_LAST : nat :=
  (53).
Program Definition aes_enc_last
  : both_package (CEfset ([])) [interface
  #val #[ ADD_ROUND_KEY ] : add_round_key_inp → add_round_key_out ;
  #val #[ SHIFT_ROWS ] : shift_rows_inp → shift_rows_out ;
  #val #[ SUB_BYTES ] : sub_bytes_inp → sub_bytes_out ] [(AES_ENC_LAST,(
      aes_enc_last_inp,aes_enc_last_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(state_49 , round_key_52) := temp_inp : block_t '× round_key_t in
    
    let add_round_key := fun x_0 x_1 => package_both add_round_key (x_0,x_1) in
    let shift_rows := fun x_0 => package_both shift_rows (x_0) in
    let sub_bytes := fun x_0 => package_both sub_bytes (x_0) in
    ((letb state_50 : block_t := sub_bytes (lift_to_both0 state_49) in
        letb state_51 : block_t := shift_rows (lift_to_both0 state_50) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (add_round_key (
            lift_to_both0 state_51) (lift_to_both0 round_key_52))
        ) : both (CEfset ([])) [interface
      #val #[ ADD_ROUND_KEY ] : add_round_key_inp → add_round_key_out ;
      #val #[ SHIFT_ROWS ] : shift_rows_inp → shift_rows_out ;
      #val #[ SUB_BYTES ] : sub_bytes_inp → sub_bytes_out ] (block_t)))in
  both_package' _ _ (AES_ENC_LAST,(
      aes_enc_last_inp,aes_enc_last_out)) temp_package_both.
Fail Next Obligation.

Definition out_54_loc : ChoiceEqualityLocation :=
  ((block_t ; 55%nat)).
Notation "'rounds_aes_inp'" :=(
  block_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'rounds_aes_inp'" :=(
  block_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'rounds_aes_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'rounds_aes_out'" :=(block_t : ChoiceEquality) (at level 2).
Definition ROUNDS_AES : nat :=
  (60).
Program Definition rounds_aes
  : both_package (CEfset ([out_54_loc])) [interface
  #val #[ AES_ENC ] : aes_enc_inp → aes_enc_out ] [(ROUNDS_AES,(
      rounds_aes_inp,rounds_aes_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(state_56 , key_57) := temp_inp : block_t '× byte_seq in
    
    let aes_enc := fun x_0 x_1 => package_both aes_enc (x_0,x_1) in
    ((letbm out_54 : block_t loc( out_54_loc ) := lift_to_both0 state_56 in
        letb out_54 :=
          foldi_both' (lift_to_both0 (usize 0)) (seq_num_chunks (
                lift_to_both0 key_57) (
                lift_to_both0 blocksize_v)) out_54 (L := (CEfset (
                [out_54_loc]))) (I := ([interface
              #val #[ AES_ENC ] : aes_enc_inp → aes_enc_out
              ])) (fun i_58 out_54 =>
            letb '(_, key_block_59) : (uint_size '× seq uint8) :=
              seq_get_chunk (lift_to_both0 key_57) (lift_to_both0 blocksize_v) (
                lift_to_both0 i_58) in
            letbm out_54 loc( out_54_loc ) :=
              aes_enc (lift_to_both0 out_54) (array_from_seq (blocksize_v) (
                  lift_to_both0 key_block_59)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 out_54)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 out_54)
        ) : both (CEfset ([out_54_loc])) [interface
      #val #[ AES_ENC ] : aes_enc_inp → aes_enc_out ] (block_t)))in
  both_package' _ _ (ROUNDS_AES,(
      rounds_aes_inp,rounds_aes_out)) temp_package_both.
Fail Next Obligation.


Notation "'block_cipher_aes_inp'" :=(
  block_t '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'block_cipher_aes_inp'" :=(
  block_t '× byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'block_cipher_aes_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'block_cipher_aes_out'" :=(block_t : ChoiceEquality) (at level 2).
Definition BLOCK_CIPHER_AES : nat :=
  (69).
Program Definition block_cipher_aes
  : both_package (CEfset ([])) [interface
  #val #[ ADD_ROUND_KEY ] : add_round_key_inp → add_round_key_out ;
  #val #[ AES_ENC_LAST ] : aes_enc_last_inp → aes_enc_last_out ;
  #val #[ ROUNDS_AES ] : rounds_aes_inp → rounds_aes_out ] [(
    BLOCK_CIPHER_AES,(block_cipher_aes_inp,block_cipher_aes_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      input_66 , key_61 , nr_63) := temp_inp : block_t '× byte_seq '× uint_size in
    
    let add_round_key := fun x_0 x_1 => package_both add_round_key (x_0,x_1) in
    let aes_enc_last := fun x_0 x_1 => package_both aes_enc_last (x_0,x_1) in
    let rounds_aes := fun x_0 x_1 => package_both rounds_aes (x_0,x_1) in
    ((letb k0_62 : round_key_t :=
          array_from_slice_range (default : uint8) (blocksize_v) (
            lift_to_both0 key_61) (prod_b(
              lift_to_both0 (usize 0),
              lift_to_both0 (usize 16)
            )) in
        letb k_64 : seq uint8 :=
          seq_from_slice_range (lift_to_both0 key_61) (prod_b(
              lift_to_both0 (usize 16),
              (lift_to_both0 nr_63) .* (lift_to_both0 (usize 16))
            )) in
        letb kn_65 : round_key_t :=
          array_from_slice (default : uint8) (blocksize_v) (
            lift_to_both0 key_61) ((lift_to_both0 nr_63) .* (lift_to_both0 (
                usize 16))) (lift_to_both0 (usize 16)) in
        letb state_67 : block_t :=
          add_round_key (lift_to_both0 input_66) (lift_to_both0 k0_62) in
        letb state_68 : block_t :=
          rounds_aes (lift_to_both0 state_67) (lift_to_both0 k_64) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (aes_enc_last (
            lift_to_both0 state_68) (lift_to_both0 kn_65))
        ) : both (CEfset ([])) [interface
      #val #[ ADD_ROUND_KEY ] : add_round_key_inp → add_round_key_out ;
      #val #[ AES_ENC_LAST ] : aes_enc_last_inp → aes_enc_last_out ;
      #val #[ ROUNDS_AES ] : rounds_aes_inp → rounds_aes_out ] (block_t)))in
  both_package' _ _ (BLOCK_CIPHER_AES,(
      block_cipher_aes_inp,block_cipher_aes_out)) temp_package_both.
Fail Next Obligation.


Notation "'rotate_word_inp'" :=(
  word_t : choice_type) (in custom pack_type at level 2).
Notation "'rotate_word_inp'" :=(word_t : ChoiceEquality) (at level 2).
Notation "'rotate_word_out'" :=(
  word_t : choice_type) (in custom pack_type at level 2).
Notation "'rotate_word_out'" :=(word_t : ChoiceEquality) (at level 2).
Definition ROTATE_WORD : nat :=
  (71).
Program Definition rotate_word
  : both_package (fset.fset0) [interface] [(ROTATE_WORD,(
      rotate_word_inp,rotate_word_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(w_70) := temp_inp : word_t in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_list uint8 ([
              (array_index (w_70) (lift_to_both0 (usize 1))) : uint8;
              (array_index (w_70) (lift_to_both0 (usize 2))) : uint8;
              (array_index (w_70) (lift_to_both0 (usize 3))) : uint8;
              (array_index (w_70) (lift_to_both0 (usize 0))) : uint8
            ]))
        ) : both (fset.fset0) [interface] (word_t)))in
  both_package' _ _ (ROTATE_WORD,(
      rotate_word_inp,rotate_word_out)) temp_package_both.
Fail Next Obligation.


Notation "'slice_word_inp'" :=(
  word_t : choice_type) (in custom pack_type at level 2).
Notation "'slice_word_inp'" :=(word_t : ChoiceEquality) (at level 2).
Notation "'slice_word_out'" :=(
  word_t : choice_type) (in custom pack_type at level 2).
Notation "'slice_word_out'" :=(word_t : ChoiceEquality) (at level 2).
Definition SLICE_WORD : nat :=
  (73).
Program Definition slice_word
  : both_package (fset.fset0) [interface] [(SLICE_WORD,(
      slice_word_inp,slice_word_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(w_72) := temp_inp : word_t in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_list uint8 ([
              (array_index (sbox_v) (declassify_usize_from_uint8 (array_index (
                      w_72) (lift_to_both0 (usize 0))))) : uint8;
              (array_index (sbox_v) (declassify_usize_from_uint8 (array_index (
                      w_72) (lift_to_both0 (usize 1))))) : uint8;
              (array_index (sbox_v) (declassify_usize_from_uint8 (array_index (
                      w_72) (lift_to_both0 (usize 2))))) : uint8;
              (array_index (sbox_v) (declassify_usize_from_uint8 (array_index (
                      w_72) (lift_to_both0 (usize 3))))) : uint8
            ]))
        ) : both (fset.fset0) [interface] (word_t)))in
  both_package' _ _ (SLICE_WORD,(
      slice_word_inp,slice_word_out)) temp_package_both.
Fail Next Obligation.

Definition k_74_loc : ChoiceEqualityLocation :=
  ((word_t ; 75%nat)).
Notation "'aes_keygen_assist_inp'" :=(
  word_t '× uint8 : choice_type) (in custom pack_type at level 2).
Notation "'aes_keygen_assist_inp'" :=(
  word_t '× uint8 : ChoiceEquality) (at level 2).
Notation "'aes_keygen_assist_out'" :=(
  word_t : choice_type) (in custom pack_type at level 2).
Notation "'aes_keygen_assist_out'" :=(word_t : ChoiceEquality) (at level 2).
Definition AES_KEYGEN_ASSIST : nat :=
  (78).
Program Definition aes_keygen_assist
  : both_package (CEfset ([k_74_loc])) [interface
  #val #[ ROTATE_WORD ] : rotate_word_inp → rotate_word_out ;
  #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ] [(
    AES_KEYGEN_ASSIST,(aes_keygen_assist_inp,aes_keygen_assist_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(w_76 , rcon_77) := temp_inp : word_t '× uint8 in
    
    let rotate_word := fun x_0 => package_both rotate_word (x_0) in
    let slice_word := fun x_0 => package_both slice_word (x_0) in
    ((letbm k_74 : word_t loc( k_74_loc ) := rotate_word (lift_to_both0 w_76) in
        letbm k_74 loc( k_74_loc ) := slice_word (lift_to_both0 k_74) in
        letb k_74 : word_t :=
          array_upd k_74 (lift_to_both0 (usize 0)) (is_pure ((array_index (
                  k_74) (lift_to_both0 (usize 0))) .^ (
                lift_to_both0 rcon_77))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 k_74)
        ) : both (CEfset ([k_74_loc])) [interface
      #val #[ ROTATE_WORD ] : rotate_word_inp → rotate_word_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ] (word_t)))in
  both_package' _ _ (AES_KEYGEN_ASSIST,(
      aes_keygen_assist_inp,aes_keygen_assist_out)) temp_package_both.
Fail Next Obligation.

Definition k_79_loc : ChoiceEqualityLocation :=
  ((word_t ; 81%nat)).
Definition result_80_loc : ChoiceEqualityLocation :=
  (((result int8 word_t) ; 82%nat)).
Notation "'key_expansion_word_inp'" :=(
  word_t '× word_t '× uint_size '× uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'key_expansion_word_inp'" :=(
  word_t '× word_t '× uint_size '× uint_size '× uint_size : ChoiceEquality) (at level 2).
Notation "'key_expansion_word_out'" :=(
  word_result_t : choice_type) (in custom pack_type at level 2).
Notation "'key_expansion_word_out'" :=(
  word_result_t : ChoiceEquality) (at level 2).
Definition KEY_EXPANSION_WORD : nat :=
  (89).
Program Definition key_expansion_word
  : both_package (CEfset ([k_79_loc ; result_80_loc])) [interface
  #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
  #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ] [(
    KEY_EXPANSION_WORD,(key_expansion_word_inp,key_expansion_word_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      w0_88 , w1_83 , i_84 , nk_86 , nr_85) := temp_inp : word_t '× word_t '× uint_size '× uint_size '× uint_size in
    
    let aes_keygen_assist := fun x_0 x_1 => package_both aes_keygen_assist (
      x_0,x_1) in
    let slice_word := fun x_0 => package_both slice_word (x_0) in
    ((letbm k_79 : word_t loc( k_79_loc ) := lift_to_both0 w1_83 in
        letbm result_80 : (result int8 word_t) loc( result_80_loc ) :=
          @Err word_t int8 (lift_to_both0 invalid_key_expansion_index_v) in
        letb '(k_79, result_80) :=
          if (lift_to_both0 i_84) <.? ((lift_to_both0 (usize 4)) .* ((
                lift_to_both0 nr_85) .+ (lift_to_both0 (
                  usize 1)))) :bool_ChoiceEquality
          then lift_scope (I1 := [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ]) (I2 := [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ]) (L1 := CEfset (
            [k_79_loc ; result_80_loc])) (L2 := CEfset (
            [k_79_loc ; result_80_loc])) (H_loc_incl := _) (H_opsig_incl := _) (
            letb 'k_79 :=
              if ((lift_to_both0 i_84) %% (lift_to_both0 nk_86)) =.? (
                lift_to_both0 (usize 0)) :bool_ChoiceEquality
              then lift_scope (I1 := [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ]) (L1 := CEfset (
                [k_79_loc ; result_80_loc])) (L2 := CEfset (
                [k_79_loc ; result_80_loc])) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm k_79 loc( k_79_loc ) :=
                  aes_keygen_assist (lift_to_both0 k_79) (array_index (rcon_v) (
                      (lift_to_both0 i_84) ./ (lift_to_both0 nk_86))) in
                lift_scope (I1 := [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ]) (I2 := [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ]) (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 k_79)
                )
              else  lift_scope (I1 := [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ]) (I2 := [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ]) (L1 := CEfset (
                [k_79_loc ; result_80_loc])) (L2 := CEfset (
                [k_79_loc ; result_80_loc])) (H_loc_incl := _) (H_opsig_incl := _) (
                letb 'k_79 :=
                  if ((lift_to_both0 nk_86) >.? (lift_to_both0 (usize 6))) && ((
                      (lift_to_both0 i_84) %% (lift_to_both0 nk_86)) =.? (
                      lift_to_both0 (usize 4))) :bool_ChoiceEquality
                  then lift_scope (I1 := [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ])  (I2 := [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ]) (L1 := CEfset (
                    [k_79_loc ; result_80_loc])) (L2 := CEfset (
                    [k_79_loc ; result_80_loc])) (H_loc_incl := _) (H_opsig_incl := _) (
                    letbm k_79 loc( k_79_loc ) :=
                      slice_word (lift_to_both0 k_79) in
                    lift_scope (I1 := [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ]) (I2 := [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ]) (H_loc_incl := _) (H_opsig_incl := _) (
                      lift_to_both0 k_79)
                    )
                  else lift_scope (I1 := [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ]) (I2 := [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ]) (H_loc_incl := _)(H_opsig_incl := _) (
                    lift_to_both0 k_79)
                   in
                lift_scope (I1 := [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ]) (I2 := [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ]) (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 k_79)
                ) in
            letb k_79 :=
              foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                    usize 4)) k_79 (L := (CEfset (
                    [k_79_loc ; result_80_loc]))) (I := ([interface
                  #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
                  #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out
                  ])) (fun i_87 k_79 =>
                letb k_79 : word_t :=
                  array_upd k_79 (lift_to_both0 i_87) (is_pure ((array_index (
                          k_79) (lift_to_both0 i_87)) .^ (array_index (w0_88) (
                          lift_to_both0 i_87)))) in
                lift_scope (I1 := [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ]) (I2 := [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ]) (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 k_79)
                ) in
            letbm result_80 loc( result_80_loc ) :=
              @Ok word_t int8 (lift_to_both0 k_79) in
            lift_scope (I1 := [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ]) (I2 := [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ]) (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 k_79,
                lift_to_both0 result_80
              ))
            )
          else lift_scope (I1 := [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ]) (I2 := [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ])  (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 k_79,
              lift_to_both0 result_80
            ))
           in
        lift_scope (I1 := [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ]) (I2 := [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ])  (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 result_80)
        ) : both (CEfset ([k_79_loc ; result_80_loc])) [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ] (
        word_result_t)))in
  both_package' _ _ (KEY_EXPANSION_WORD,(
                                           key_expansion_word_inp,key_expansion_word_out)) temp_package_both.
Fail Next Obligation.

Definition key_ex_90_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 91%nat)).
Notation "'key_expansion_aes_inp'" :=(
  byte_seq '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'key_expansion_aes_inp'" :=(
  byte_seq '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size : ChoiceEquality) (at level 2).
Notation "'key_expansion_aes_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'key_expansion_aes_out'" :=(
  byte_seq_result_t : ChoiceEquality) (at level 2).
Definition KEY_EXPANSION_AES : nat :=
  (102).
Program Definition key_expansion_aes
  : both_package (CEfset ([key_ex_90_loc])) [interface
  #val #[ KEY_EXPANSION_WORD ] : key_expansion_word_inp → key_expansion_word_out
  ] [(KEY_EXPANSION_AES,(key_expansion_aes_inp,key_expansion_aes_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      key_93 , nk_99 , nr_100 , key_schedule_length_92 , key_length_94 , iterations_96) := temp_inp : byte_seq '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size in
    
    let key_expansion_word := fun x_0 x_1 x_2 x_3 x_4 => package_both key_expansion_word (
      x_0,x_1,x_2,x_3,x_4) in
    ((letbm key_ex_90 : seq uint8 loc( key_ex_90_loc ) :=
          seq_new_ (default : uint8) (lift_to_both0 key_schedule_length_92) in
        letbm key_ex_90 loc( key_ex_90_loc ) :=
          seq_update_start (lift_to_both0 key_ex_90) (lift_to_both0 key_93) in
        letb word_size_95 : uint_size := lift_to_both0 key_length_94 in
        letbnd(_) key_ex_90 :=
          foldi_bind_both' (lift_to_both0 (usize 0)) (
              lift_to_both0 iterations_96) key_ex_90 (L := (CEfset (
                [key_ex_90_loc]))) (I := ([interface
              #val #[ KEY_EXPANSION_WORD ] : key_expansion_word_inp → key_expansion_word_out
              ])) (fun j_97 key_ex_90 =>
            letb i_98 : uint_size :=
              (lift_to_both0 j_97) .+ (lift_to_both0 word_size_95) in
            letbm key_ex_90 loc( key_ex_90_loc ) := lift_to_both0 key_ex_90 in
            letbnd(
                ChoiceEqualityMonad.result_bind_both int8) word_101 : word_t :=
              key_expansion_word (array_from_slice (default : uint8) (
                  key_length_v) (lift_to_both0 key_ex_90) ((lift_to_both0 (
                      usize 4)) .* ((lift_to_both0 i_98) .- (
                      lift_to_both0 word_size_95))) (lift_to_both0 (usize 4))) (
                array_from_slice (default : uint8) (key_length_v) (
                  lift_to_both0 key_ex_90) (((lift_to_both0 (usize 4)) .* (
                      lift_to_both0 i_98)) .- (lift_to_both0 (usize 4))) (
                  lift_to_both0 (usize 4))) (lift_to_both0 i_98) (
                lift_to_both0 nk_99) (lift_to_both0 nr_100) in
            letbm key_ex_90 loc( key_ex_90_loc ) :=
              seq_update (lift_to_both0 key_ex_90) ((lift_to_both0 (
                    usize 4)) .* (lift_to_both0 i_98)) (
                array_to_seq (lift_to_both0 word_101)) in
            lift_scope (I1 := [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ]) (H_loc_incl := _) (@Ok (seq uint8
              ) int8 (lift_to_both0 key_ex_90))
            ) in
        lift_scope (I1 := [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ]) (H_loc_incl := _) (@Ok byte_seq int8 (
            lift_to_both0 key_ex_90))
        ) : both (CEfset ([key_ex_90_loc])) [interface
      #val #[ KEY_EXPANSION_WORD ] : key_expansion_word_inp → key_expansion_word_out
      ] (byte_seq_result_t)))in
  both_package' _ _ (KEY_EXPANSION_AES,(
      key_expansion_aes_inp,key_expansion_aes_out)) temp_package_both.
Fail Next Obligation.


Notation "'aes_encrypt_block_inp'" :=(
  byte_seq '× block_t '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'aes_encrypt_block_inp'" :=(
  byte_seq '× block_t '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size : ChoiceEquality) (at level 2).
Notation "'aes_encrypt_block_out'" :=(
  block_result_t : choice_type) (in custom pack_type at level 2).
Notation "'aes_encrypt_block_out'" :=(
  block_result_t : ChoiceEquality) (at level 2).
Definition AES_ENCRYPT_BLOCK : nat :=
  (111).
Program Definition aes_encrypt_block
  : both_package (CEfset ([])) [interface
  #val #[ BLOCK_CIPHER_AES ] : block_cipher_aes_inp → block_cipher_aes_out ;
  #val #[ KEY_EXPANSION_AES ] : key_expansion_aes_inp → key_expansion_aes_out
  ] [(AES_ENCRYPT_BLOCK,(aes_encrypt_block_inp,aes_encrypt_block_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      k_103 , input_110 , nk_104 , nr_105 , key_schedule_length_106 , key_length_107 , iterations_108) := temp_inp : byte_seq '× block_t '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size in
    
    let block_cipher_aes := fun x_0 x_1 x_2 => package_both block_cipher_aes (
      x_0,x_1,x_2) in
    let key_expansion_aes := fun x_0 x_1 x_2 x_3 x_4 x_5 => package_both key_expansion_aes (
      x_0,x_1,x_2,x_3,x_4,x_5) in
    ((letbnd(ChoiceEqualityMonad.result_bind_both int8) key_ex_109 : byte_seq :=
          key_expansion_aes (lift_to_both0 k_103) (lift_to_both0 nk_104) (
            lift_to_both0 nr_105) (lift_to_both0 key_schedule_length_106) (
            lift_to_both0 key_length_107) (lift_to_both0 iterations_108) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok block_t int8 (
            block_cipher_aes (lift_to_both0 input_110) (
              lift_to_both0 key_ex_109) (lift_to_both0 nr_105)))
        ) : both (CEfset ([])) [interface
      #val #[ BLOCK_CIPHER_AES ] : block_cipher_aes_inp → block_cipher_aes_out ;
      #val #[ KEY_EXPANSION_AES ] : key_expansion_aes_inp → key_expansion_aes_out
      ] (block_result_t)))in
  both_package' _ _ (AES_ENCRYPT_BLOCK,(
      aes_encrypt_block_inp,aes_encrypt_block_out)) temp_package_both.
Fail Next Obligation.


Notation "'aes128_encrypt_block_inp'" :=(
  key128_t '× block_t : choice_type) (in custom pack_type at level 2).
Notation "'aes128_encrypt_block_inp'" :=(
  key128_t '× block_t : ChoiceEquality) (at level 2).
Notation "'aes128_encrypt_block_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'aes128_encrypt_block_out'" :=(block_t : ChoiceEquality) (at level 2).
Definition AES128_ENCRYPT_BLOCK : nat :=
  (114).
Program Definition aes128_encrypt_block
  : both_package (CEfset ([])) [interface
  #val #[ AES_ENCRYPT_BLOCK ] : aes_encrypt_block_inp → aes_encrypt_block_out
  ] [(AES128_ENCRYPT_BLOCK,(
      aes128_encrypt_block_inp,aes128_encrypt_block_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(k_112 , input_113) := temp_inp : key128_t '× block_t in
    
    let aes_encrypt_block := fun x_0 x_1 x_2 x_3 x_4 x_5 x_6 => package_both aes_encrypt_block (
      x_0,x_1,x_2,x_3,x_4,x_5,x_6) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (result_unwrap (
            aes_encrypt_block (seq_from_seq (
                array_to_seq (lift_to_both0 k_112))) (lift_to_both0 input_113) (
              lift_to_both0 key_length_v) (lift_to_both0 rounds_v) (
              lift_to_both0 key_schedule_length_v) (
              lift_to_both0 key_length_v) (lift_to_both0 iterations_v)))
        ) : both (CEfset ([])) [interface
      #val #[ AES_ENCRYPT_BLOCK ] : aes_encrypt_block_inp → aes_encrypt_block_out
      ] (block_t)))in
  both_package' _ _ (AES128_ENCRYPT_BLOCK,(
      aes128_encrypt_block_inp,aes128_encrypt_block_out)) temp_package_both.
Fail Next Obligation.

Definition input_115_loc : ChoiceEqualityLocation :=
  ((block_t ; 116%nat)).
Notation "'aes_ctr_key_block_inp'" :=(
  byte_seq '× aes_nonce_t '× uint32 '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'aes_ctr_key_block_inp'" :=(
  byte_seq '× aes_nonce_t '× uint32 '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size : ChoiceEquality) (at level 2).
Notation "'aes_ctr_key_block_out'" :=(
  block_result_t : choice_type) (in custom pack_type at level 2).
Notation "'aes_ctr_key_block_out'" :=(
  block_result_t : ChoiceEquality) (at level 2).
Definition AES_CTR_KEY_BLOCK : nat :=
  (125).
Program Definition aes_ctr_key_block
  : both_package (CEfset ([input_115_loc])) [interface
  #val #[ AES_ENCRYPT_BLOCK ] : aes_encrypt_block_inp → aes_encrypt_block_out
  ] [(AES_CTR_KEY_BLOCK,(aes_ctr_key_block_inp,aes_ctr_key_block_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      k_119 , n_117 , c_118 , nk_120 , nr_121 , key_schedule_length_122 , key_length_123 , iterations_124) := temp_inp : byte_seq '× aes_nonce_t '× uint32 '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size in
    
    let aes_encrypt_block := fun x_0 x_1 x_2 x_3 x_4 x_5 x_6 => package_both aes_encrypt_block (
      x_0,x_1,x_2,x_3,x_4,x_5,x_6) in
    ((letbm input_115 : block_t loc( input_115_loc ) :=
          array_new_ (default : uint8) (blocksize_v) in
        letbm input_115 loc( input_115_loc ) :=
          array_update (lift_to_both0 input_115) (lift_to_both0 (usize 0)) (
            array_to_seq (lift_to_both0 n_117)) in
        letbm input_115 loc( input_115_loc ) :=
          array_update (lift_to_both0 input_115) (lift_to_both0 (usize 12)) (
            array_to_seq (uint32_to_be_bytes (lift_to_both0 c_118))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (aes_encrypt_block (
            lift_to_both0 k_119) (lift_to_both0 input_115) (
            lift_to_both0 nk_120) (lift_to_both0 nr_121) (
            lift_to_both0 key_schedule_length_122) (
            lift_to_both0 key_length_123) (lift_to_both0 iterations_124))
        ) : both (CEfset ([input_115_loc])) [interface
      #val #[ AES_ENCRYPT_BLOCK ] : aes_encrypt_block_inp → aes_encrypt_block_out
      ] (block_result_t)))in
  both_package' _ _ (AES_CTR_KEY_BLOCK,(
      aes_ctr_key_block_inp,aes_ctr_key_block_out)) temp_package_both.
Fail Next Obligation.

Definition out_126_loc : ChoiceEqualityLocation :=
  ((block_t ; 127%nat)).
Notation "'xor_block_inp'" :=(
  block_t '× block_t : choice_type) (in custom pack_type at level 2).
Notation "'xor_block_inp'" :=(
  block_t '× block_t : ChoiceEquality) (at level 2).
Notation "'xor_block_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'xor_block_out'" :=(block_t : ChoiceEquality) (at level 2).
Definition XOR_BLOCK : nat :=
  (131).
Program Definition xor_block
  : both_package (CEfset ([out_126_loc])) [interface] [(XOR_BLOCK,(
      xor_block_inp,xor_block_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(block_128 , key_block_130) := temp_inp : block_t '× block_t in
    
    ((letbm out_126 : block_t loc( out_126_loc ) := lift_to_both0 block_128 in
        letb out_126 :=
          foldi_both' (lift_to_both0 (usize 0)) (
              lift_to_both0 blocksize_v) out_126 (L := (CEfset (
                [out_126_loc]))) (I := ([interface])) (fun i_129 out_126 =>
            letb out_126 : block_t :=
              array_upd out_126 (lift_to_both0 i_129) (is_pure ((array_index (
                      out_126) (lift_to_both0 i_129)) .^ (array_index (
                      key_block_130) (lift_to_both0 i_129)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 out_126)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 out_126)
        ) : both (CEfset ([out_126_loc])) [interface] (block_t)))in
  both_package' _ _ (XOR_BLOCK,(xor_block_inp,xor_block_out)) temp_package_both.
Fail Next Obligation.

Definition ctr_132_loc : ChoiceEqualityLocation :=
  ((uint32 ; 134%nat)).
Definition blocks_out_133_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 135%nat)).
Notation "'aes_counter_mode_inp'" :=(
  byte_seq '× aes_nonce_t '× uint32 '× byte_seq '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'aes_counter_mode_inp'" :=(
  byte_seq '× aes_nonce_t '× uint32 '× byte_seq '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size : ChoiceEquality) (at level 2).
Notation "'aes_counter_mode_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'aes_counter_mode_out'" :=(
  byte_seq_result_t : ChoiceEquality) (at level 2).
Definition AES_COUNTER_MODE : nat :=
  (153).
Program Definition aes_counter_mode
  : both_package (CEfset ([ctr_132_loc ; blocks_out_133_loc])) [interface
  #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
  #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out ] [(AES_COUNTER_MODE,(
      aes_counter_mode_inp,aes_counter_mode_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      key_141 , nonce_142 , counter_136 , msg_137 , nk_143 , nr_144 , key_schedule_length_145 , key_length_146 , iterations_147) := temp_inp : byte_seq '× aes_nonce_t '× uint32 '× byte_seq '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size in
    
    let aes_ctr_key_block := fun x_0 x_1 x_2 x_3 x_4 x_5 x_6 x_7 => package_both aes_ctr_key_block (
      x_0,x_1,x_2,x_3,x_4,x_5,x_6,x_7) in
    let xor_block := fun x_0 x_1 => package_both xor_block (x_0,x_1) in
    ((letbm ctr_132 : uint32 loc( ctr_132_loc ) := lift_to_both0 counter_136 in
        letbm blocks_out_133 : seq uint8 loc( blocks_out_133_loc ) :=
          seq_new_ (default : uint8) (seq_len (lift_to_both0 msg_137)) in
        letb n_blocks_138 : uint_size :=
          seq_num_exact_chunks (lift_to_both0 msg_137) (
            lift_to_both0 blocksize_v) in
        letbnd(_) '(ctr_132, blocks_out_133) :=
          foldi_bind_both' (lift_to_both0 (usize 0)) (
              lift_to_both0 n_blocks_138) prod_ce(ctr_132, blocks_out_133
            ) (L := (CEfset ([ctr_132_loc ; blocks_out_133_loc]))) (I := (
              [interface
              #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
              #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out
              ])) (fun i_139 '(ctr_132, blocks_out_133) =>
            letb msg_block_140 : seq uint8 :=
              seq_get_exact_chunk (lift_to_both0 msg_137) (
                lift_to_both0 blocksize_v) (lift_to_both0 i_139) in
            letbnd(
                ChoiceEqualityMonad.result_bind_both int8) key_block_148 : block_t :=
              aes_ctr_key_block (lift_to_both0 key_141) (
                lift_to_both0 nonce_142) (lift_to_both0 ctr_132) (
                lift_to_both0 nk_143) (lift_to_both0 nr_144) (
                lift_to_both0 key_schedule_length_145) (
                lift_to_both0 key_length_146) (lift_to_both0 iterations_147) in
            letbm blocks_out_133 loc( blocks_out_133_loc ) :=
              seq_set_chunk (lift_to_both0 blocks_out_133) (
                lift_to_both0 blocksize_v) (lift_to_both0 i_139) (
                array_to_seq (xor_block (array_from_seq (blocksize_v) (
                    lift_to_both0 msg_block_140)) (
                  lift_to_both0 key_block_148))) in
            letbm ctr_132 loc( ctr_132_loc ) :=
              (lift_to_both0 ctr_132) .+ (secret (lift_to_both0 (
                    @repr U32 1))) in
            lift_scope (I2 := [interface
  #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
  #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out ]) (H_loc_incl := _) (H_opsig_incl := _) (@Ok (
                uint32 '×
                seq uint8
              ) int8 (prod_b(lift_to_both0 ctr_132, lift_to_both0 blocks_out_133
                )))
            ) in
        letb last_block_149 : seq uint8 :=
          seq_get_remainder_chunk (lift_to_both0 msg_137) (
            lift_to_both0 blocksize_v) in
        letb last_block_len_150 : uint_size :=
          seq_len (lift_to_both0 last_block_149) in
        letbnd(_) 'blocks_out_133 :=
          if (lift_to_both0 last_block_len_150) !=.? (lift_to_both0 (
              usize 0)) :bool_ChoiceEquality
          then lift_scope (I1 := [interface
  #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
  #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out ])  (I2 := [interface
  #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
  #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out ])  (L1 := CEfset (
            [ctr_132_loc ; blocks_out_133_loc])) (L2 := CEfset (
            [ctr_132_loc ; blocks_out_133_loc])) (H_loc_incl := _) (H_opsig_incl := _) (
            letb last_block_151 : block_t :=
              array_update_start (array_new_ (default : uint8) (blocksize_v)) (
                lift_to_both0 last_block_149) in
            letbnd(
                ChoiceEqualityMonad.result_bind_both int8) key_block_152 : block_t :=
              aes_ctr_key_block (lift_to_both0 key_141) (
                lift_to_both0 nonce_142) (lift_to_both0 ctr_132) (
                lift_to_both0 nk_143) (lift_to_both0 nr_144) (
                lift_to_both0 key_schedule_length_145) (
                lift_to_both0 key_length_146) (lift_to_both0 iterations_147) in
            letbm blocks_out_133 loc( blocks_out_133_loc ) :=
              seq_set_chunk (lift_to_both0 blocks_out_133) (
                lift_to_both0 blocksize_v) (lift_to_both0 n_blocks_138) (
                array_slice_range (xor_block (lift_to_both0 last_block_151) (
                    lift_to_both0 key_block_152)) (prod_b(
                    lift_to_both0 (usize 0),
                    lift_to_both0 last_block_len_150
                  ))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (seq uint8
              ) int8 (lift_to_both0 blocks_out_133))
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (seq uint8
            ) int8 (lift_to_both0 blocks_out_133))
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok byte_seq int8 (
            lift_to_both0 blocks_out_133))
        ) : both (CEfset ([ctr_132_loc ; blocks_out_133_loc])) [interface
      #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
      #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out ] (
        byte_seq_result_t)))in
  both_package' _ _ (AES_COUNTER_MODE,(
      aes_counter_mode_inp,aes_counter_mode_out)) temp_package_both.
Fail Next Obligation.


Notation "'aes128_encrypt_inp'" :=(
  key128_t '× aes_nonce_t '× uint32 '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'aes128_encrypt_inp'" :=(
  key128_t '× aes_nonce_t '× uint32 '× byte_seq : ChoiceEquality) (at level 2).
Notation "'aes128_encrypt_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'aes128_encrypt_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition AES128_ENCRYPT : nat :=
  (158).
Program Definition aes128_encrypt
  : both_package (CEfset ([])) [interface
  #val #[ AES_COUNTER_MODE ] : aes_counter_mode_inp → aes_counter_mode_out
  ] [(AES128_ENCRYPT,(aes128_encrypt_inp,aes128_encrypt_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      key_154 , nonce_155 , counter_156 , msg_157) := temp_inp : key128_t '× aes_nonce_t '× uint32 '× byte_seq in
    
    let aes_counter_mode := fun x_0 x_1 x_2 x_3 x_4 x_5 x_6 x_7 x_8 => package_both aes_counter_mode (
      x_0,x_1,x_2,x_3,x_4,x_5,x_6,x_7,x_8) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (result_unwrap (
            aes_counter_mode (seq_from_seq (
                array_to_seq (lift_to_both0 key_154))) (
              lift_to_both0 nonce_155) (lift_to_both0 counter_156) (
              lift_to_both0 msg_157) (lift_to_both0 key_length_v) (
              lift_to_both0 rounds_v) (lift_to_both0 key_schedule_length_v) (
              lift_to_both0 key_length_v) (lift_to_both0 iterations_v)))
        ) : both (CEfset ([])) [interface
      #val #[ AES_COUNTER_MODE ] : aes_counter_mode_inp → aes_counter_mode_out
      ] (byte_seq)))in
  both_package' _ _ (AES128_ENCRYPT,(
      aes128_encrypt_inp,aes128_encrypt_out)) temp_package_both.
Fail Next Obligation.


Notation "'aes128_decrypt_inp'" :=(
  key128_t '× aes_nonce_t '× uint32 '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'aes128_decrypt_inp'" :=(
  key128_t '× aes_nonce_t '× uint32 '× byte_seq : ChoiceEquality) (at level 2).
Notation "'aes128_decrypt_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'aes128_decrypt_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition AES128_DECRYPT : nat :=
  (163).
Program Definition aes128_decrypt
  : both_package (CEfset ([])) [interface
  #val #[ AES_COUNTER_MODE ] : aes_counter_mode_inp → aes_counter_mode_out
  ] [(AES128_DECRYPT,(aes128_decrypt_inp,aes128_decrypt_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      key_159 , nonce_160 , counter_161 , ctxt_162) := temp_inp : key128_t '× aes_nonce_t '× uint32 '× byte_seq in
    
    let aes_counter_mode := fun x_0 x_1 x_2 x_3 x_4 x_5 x_6 x_7 x_8 => package_both aes_counter_mode (
      x_0,x_1,x_2,x_3,x_4,x_5,x_6,x_7,x_8) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (result_unwrap (
            aes_counter_mode (seq_from_seq (
                array_to_seq (lift_to_both0 key_159))) (
              lift_to_both0 nonce_160) (lift_to_both0 counter_161) (
              lift_to_both0 ctxt_162) (lift_to_both0 key_length_v) (
              lift_to_both0 rounds_v) (lift_to_both0 key_schedule_length_v) (
              lift_to_both0 key_length_v) (lift_to_both0 iterations_v)))
        ) : both (CEfset ([])) [interface
      #val #[ AES_COUNTER_MODE ] : aes_counter_mode_inp → aes_counter_mode_out
      ] (byte_seq)))in
  both_package' _ _ (AES128_DECRYPT,(
      aes128_decrypt_inp,aes128_decrypt_out)) temp_package_both.
Fail Next Obligation.

