(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp Require Import ssrZ word.
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

Definition st_187_loc : ChoiceEqualityLocation :=
  (block_t ; 188%nat).
Notation "'sub_bytes_inp'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'sub_bytes_inp'" :=(block_t : ChoiceEquality) (at level 2).
Notation "'sub_bytes_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'sub_bytes_out'" :=(block_t : ChoiceEquality) (at level 2).
Definition SUB_BYTES : nat :=
  191.
Program Definition sub_bytes
  : both_package (CEfset ([st_187_loc])) [interface] [(SUB_BYTES,(
      sub_bytes_inp,sub_bytes_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(state_189) := temp_inp : block_t in
    
    ((letbm st_187 : block_t loc( st_187_loc ) := lift_to_both0 state_189 in
        letb st_187 :=
          foldi_both' (lift_to_both0 (usize 0)) (
              lift_to_both0 blocksize_v) st_187 (L := (CEfset (
                [st_187_loc]))) (I := ([interface])) (fun i_190 st_187 =>
            letb st_187 : block_t :=
              array_upd st_187 (lift_to_both0 i_190) (is_pure (array_index (
                    sbox_v) (uint8_declassify (array_index (state_189) (
                        lift_to_both0 i_190))))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 st_187)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 st_187)
        ) : both (CEfset ([st_187_loc])) [interface] (block_t)))in
  both_package' _ _ (SUB_BYTES,(sub_bytes_inp,sub_bytes_out)) temp_package_both.
Fail Next Obligation.

Definition out_192_loc : ChoiceEqualityLocation :=
  (block_t ; 193%nat).
Notation "'shift_row_inp'" :=(
  uint_size '× uint_size '× block_t : choice_type) (in custom pack_type at level 2).
Notation "'shift_row_inp'" :=(
  uint_size '× uint_size '× block_t : ChoiceEquality) (at level 2).
Notation "'shift_row_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'shift_row_out'" :=(block_t : ChoiceEquality) (at level 2).
Definition SHIFT_ROW : nat :=
  197.
Program Definition shift_row
  : both_package (CEfset ([out_192_loc])) [interface] [(SHIFT_ROW,(
      shift_row_inp,shift_row_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      i_195 , shift_196 , state_194) := temp_inp : uint_size '× uint_size '× block_t in
    
    ((letbm out_192 : block_t loc( out_192_loc ) := lift_to_both0 state_194 in
        letb out_192 : block_t :=
          array_upd out_192 (lift_to_both0 i_195) (is_pure (array_index (
                state_194) ((lift_to_both0 i_195) .+ ((lift_to_both0 (
                      usize 4)) .* ((lift_to_both0 shift_196) %% (
                      lift_to_both0 (usize 4))))))) in
        letb out_192 : block_t :=
          array_upd out_192 ((lift_to_both0 i_195) .+ (lift_to_both0 (
                usize 4))) (is_pure (array_index (state_194) ((
                  lift_to_both0 i_195) .+ ((lift_to_both0 (usize 4)) .* (((
                        lift_to_both0 shift_196) .+ (lift_to_both0 (
                          usize 1))) %% (lift_to_both0 (usize 4))))))) in
        letb out_192 : block_t :=
          array_upd out_192 ((lift_to_both0 i_195) .+ (lift_to_both0 (
                usize 8))) (is_pure (array_index (state_194) ((
                  lift_to_both0 i_195) .+ ((lift_to_both0 (usize 4)) .* (((
                        lift_to_both0 shift_196) .+ (lift_to_both0 (
                          usize 2))) %% (lift_to_both0 (usize 4))))))) in
        letb out_192 : block_t :=
          array_upd out_192 ((lift_to_both0 i_195) .+ (lift_to_both0 (
                usize 12))) (is_pure (array_index (state_194) ((
                  lift_to_both0 i_195) .+ ((lift_to_both0 (usize 4)) .* (((
                        lift_to_both0 shift_196) .+ (lift_to_both0 (
                          usize 3))) %% (lift_to_both0 (usize 4))))))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 out_192)
        ) : both (CEfset ([out_192_loc])) [interface] (block_t)))in
  both_package' _ _ (SHIFT_ROW,(shift_row_inp,shift_row_out)) temp_package_both.
Fail Next Obligation.


Notation "'shift_rows_inp'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'shift_rows_inp'" :=(block_t : ChoiceEquality) (at level 2).
Notation "'shift_rows_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'shift_rows_out'" :=(block_t : ChoiceEquality) (at level 2).
Definition SHIFT_ROWS : nat :=
  201.
Program Definition shift_rows
  : both_package (CEfset ([])) [interface
  #val #[ SHIFT_ROW ] : shift_row_inp → shift_row_out ] [(SHIFT_ROWS,(
      shift_rows_inp,shift_rows_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(state_198) := temp_inp : block_t in
    
    let shift_row := fun x_0 x_1 x_2 => package_both shift_row (x_0,x_1,x_2) in
    ((letb state_199 : block_t :=
          shift_row (lift_to_both0 (usize 1)) (lift_to_both0 (usize 1)) (
            lift_to_both0 state_198) in
        letb state_200 : block_t :=
          shift_row (lift_to_both0 (usize 2)) (lift_to_both0 (usize 2)) (
            lift_to_both0 state_199) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (shift_row (
            lift_to_both0 (usize 3)) (lift_to_both0 (usize 3)) (
            lift_to_both0 state_200))
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
  207.
Program Definition xtime
  : both_package (fset.fset0) [interface] [(XTIME,(xtime_inp,xtime_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_202) := temp_inp : uint8 in
    
    ((letb x1_203 : uint8 :=
          (lift_to_both0 x_202) shift_left (lift_to_both0 (usize 1)) in
        letb x7_204 : uint8 :=
          (lift_to_both0 x_202) shift_right (lift_to_both0 (usize 7)) in
        letb x71_205 : uint8 :=
          (lift_to_both0 x7_204) .& (secret (lift_to_both0 (@repr U8 1))) in
        letb x711b_206 : uint8 :=
          (lift_to_both0 x71_205) .* (secret (lift_to_both0 (@repr U8 27))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
            lift_to_both0 x1_203) .^ (lift_to_both0 x711b_206))
        ) : both (fset.fset0) [interface] (uint8)))in
  both_package' _ _ (XTIME,(xtime_inp,xtime_out)) temp_package_both.
Fail Next Obligation.

Definition st_208_loc : ChoiceEqualityLocation :=
  (block_t ; 209%nat).
Notation "'mix_column_inp'" :=(
  uint_size '× block_t : choice_type) (in custom pack_type at level 2).
Notation "'mix_column_inp'" :=(
  uint_size '× block_t : ChoiceEquality) (at level 2).
Notation "'mix_column_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'mix_column_out'" :=(block_t : ChoiceEquality) (at level 2).
Definition MIX_COLUMN : nat :=
  218.
Program Definition mix_column
  : both_package (CEfset ([st_208_loc])) [interface
  #val #[ XTIME ] : xtime_inp → xtime_out ] [(MIX_COLUMN,(
      mix_column_inp,mix_column_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(c_210 , state_212) := temp_inp : uint_size '× block_t in
    
    let xtime := fun x_0 => package_both xtime (x_0) in
    ((letb i0_211 : uint_size :=
          (lift_to_both0 (usize 4)) .* (lift_to_both0 c_210) in
        letb s0_213 : uint8 := array_index (state_212) (lift_to_both0 i0_211) in
        letb s1_214 : uint8 :=
          array_index (state_212) ((lift_to_both0 i0_211) .+ (lift_to_both0 (
                usize 1))) in
        letb s2_215 : uint8 :=
          array_index (state_212) ((lift_to_both0 i0_211) .+ (lift_to_both0 (
                usize 2))) in
        letb s3_216 : uint8 :=
          array_index (state_212) ((lift_to_both0 i0_211) .+ (lift_to_both0 (
                usize 3))) in
        letbm st_208 : block_t loc( st_208_loc ) := lift_to_both0 state_212 in
        letb tmp_217 : uint8 :=
          (((lift_to_both0 s0_213) .^ (lift_to_both0 s1_214)) .^ (
              lift_to_both0 s2_215)) .^ (lift_to_both0 s3_216) in
        letb st_208 : block_t :=
          array_upd st_208 (lift_to_both0 i0_211) (is_pure (((
                  lift_to_both0 s0_213) .^ (lift_to_both0 tmp_217)) .^ (xtime ((
                    lift_to_both0 s0_213) .^ (lift_to_both0 s1_214))))) in
        letb st_208 : block_t :=
          array_upd st_208 ((lift_to_both0 i0_211) .+ (lift_to_both0 (
                usize 1))) (is_pure (((lift_to_both0 s1_214) .^ (
                  lift_to_both0 tmp_217)) .^ (xtime ((lift_to_both0 s1_214) .^ (
                    lift_to_both0 s2_215))))) in
        letb st_208 : block_t :=
          array_upd st_208 ((lift_to_both0 i0_211) .+ (lift_to_both0 (
                usize 2))) (is_pure (((lift_to_both0 s2_215) .^ (
                  lift_to_both0 tmp_217)) .^ (xtime ((lift_to_both0 s2_215) .^ (
                    lift_to_both0 s3_216))))) in
        letb st_208 : block_t :=
          array_upd st_208 ((lift_to_both0 i0_211) .+ (lift_to_both0 (
                usize 3))) (is_pure (((lift_to_both0 s3_216) .^ (
                  lift_to_both0 tmp_217)) .^ (xtime ((lift_to_both0 s3_216) .^ (
                    lift_to_both0 s0_213))))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 st_208)
        ) : both (CEfset ([st_208_loc])) [interface
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
  223.
Program Definition mix_columns
  : both_package (CEfset ([])) [interface
  #val #[ MIX_COLUMN ] : mix_column_inp → mix_column_out ] [(MIX_COLUMNS,(
      mix_columns_inp,mix_columns_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(state_219) := temp_inp : block_t in
    
    let mix_column := fun x_0 x_1 => package_both mix_column (x_0,x_1) in
    ((letb state_220 : block_t :=
          mix_column (lift_to_both0 (usize 0)) (lift_to_both0 state_219) in
        letb state_221 : block_t :=
          mix_column (lift_to_both0 (usize 1)) (lift_to_both0 state_220) in
        letb state_222 : block_t :=
          mix_column (lift_to_both0 (usize 2)) (lift_to_both0 state_221) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (mix_column (
            lift_to_both0 (usize 3)) (lift_to_both0 state_222))
        ) : both (CEfset ([])) [interface
      #val #[ MIX_COLUMN ] : mix_column_inp → mix_column_out ] (block_t)))in
  both_package' _ _ (MIX_COLUMNS,(
      mix_columns_inp,mix_columns_out)) temp_package_both.
Fail Next Obligation.

Definition out_224_loc : ChoiceEqualityLocation :=
  (block_t ; 225%nat).
Notation "'add_round_key_inp'" :=(
  block_t '× round_key_t : choice_type) (in custom pack_type at level 2).
Notation "'add_round_key_inp'" :=(
  block_t '× round_key_t : ChoiceEquality) (at level 2).
Notation "'add_round_key_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'add_round_key_out'" :=(block_t : ChoiceEquality) (at level 2).
Definition ADD_ROUND_KEY : nat :=
  229.
Program Definition add_round_key
  : both_package (CEfset ([out_224_loc])) [interface] [(ADD_ROUND_KEY,(
      add_round_key_inp,add_round_key_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(state_226 , key_228) := temp_inp : block_t '× round_key_t in
    
    ((letbm out_224 : block_t loc( out_224_loc ) := lift_to_both0 state_226 in
        letb out_224 :=
          foldi_both' (lift_to_both0 (usize 0)) (
              lift_to_both0 blocksize_v) out_224 (L := (CEfset (
                [out_224_loc]))) (I := ([interface])) (fun i_227 out_224 =>
            letb out_224 : block_t :=
              array_upd out_224 (lift_to_both0 i_227) (is_pure ((array_index (
                      out_224) (lift_to_both0 i_227)) .^ (array_index (
                      key_228) (lift_to_both0 i_227)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 out_224)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 out_224)
        ) : both (CEfset ([out_224_loc])) [interface] (block_t)))in
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
  235.
Program Definition aes_enc
  : both_package (CEfset ([])) [interface
  #val #[ ADD_ROUND_KEY ] : add_round_key_inp → add_round_key_out ;
  #val #[ MIX_COLUMNS ] : mix_columns_inp → mix_columns_out ;
  #val #[ SHIFT_ROWS ] : shift_rows_inp → shift_rows_out ;
  #val #[ SUB_BYTES ] : sub_bytes_inp → sub_bytes_out ] [(AES_ENC,(
      aes_enc_inp,aes_enc_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(state_230 , round_key_234) := temp_inp : block_t '× round_key_t in
    
    let add_round_key := fun x_0 x_1 => package_both add_round_key (x_0,x_1) in
    let mix_columns := fun x_0 => package_both mix_columns (x_0) in
    let shift_rows := fun x_0 => package_both shift_rows (x_0) in
    let sub_bytes := fun x_0 => package_both sub_bytes (x_0) in
    ((letb state_231 : block_t := sub_bytes (lift_to_both0 state_230) in
        letb state_232 : block_t := shift_rows (lift_to_both0 state_231) in
        letb state_233 : block_t := mix_columns (lift_to_both0 state_232) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (add_round_key (
            lift_to_both0 state_233) (lift_to_both0 round_key_234))
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
  240.
Program Definition aes_enc_last
  : both_package (CEfset ([])) [interface
  #val #[ ADD_ROUND_KEY ] : add_round_key_inp → add_round_key_out ;
  #val #[ SHIFT_ROWS ] : shift_rows_inp → shift_rows_out ;
  #val #[ SUB_BYTES ] : sub_bytes_inp → sub_bytes_out ] [(AES_ENC_LAST,(
      aes_enc_last_inp,aes_enc_last_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(state_236 , round_key_239) := temp_inp : block_t '× round_key_t in
    
    let add_round_key := fun x_0 x_1 => package_both add_round_key (x_0,x_1) in
    let shift_rows := fun x_0 => package_both shift_rows (x_0) in
    let sub_bytes := fun x_0 => package_both sub_bytes (x_0) in
    ((letb state_237 : block_t := sub_bytes (lift_to_both0 state_236) in
        letb state_238 : block_t := shift_rows (lift_to_both0 state_237) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (add_round_key (
            lift_to_both0 state_238) (lift_to_both0 round_key_239))
        ) : both (CEfset ([])) [interface
      #val #[ ADD_ROUND_KEY ] : add_round_key_inp → add_round_key_out ;
      #val #[ SHIFT_ROWS ] : shift_rows_inp → shift_rows_out ;
      #val #[ SUB_BYTES ] : sub_bytes_inp → sub_bytes_out ] (block_t)))in
  both_package' _ _ (AES_ENC_LAST,(
      aes_enc_last_inp,aes_enc_last_out)) temp_package_both.
Fail Next Obligation.

Definition out_241_loc : ChoiceEqualityLocation :=
  (block_t ; 242%nat).
Notation "'rounds_aes_inp'" :=(
  block_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'rounds_aes_inp'" :=(
  block_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'rounds_aes_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'rounds_aes_out'" :=(block_t : ChoiceEquality) (at level 2).
Definition ROUNDS_AES : nat :=
  247.
Program Definition rounds_aes
  : both_package (CEfset ([out_241_loc])) [interface
  #val #[ AES_ENC ] : aes_enc_inp → aes_enc_out ] [(ROUNDS_AES,(
      rounds_aes_inp,rounds_aes_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(state_243 , key_244) := temp_inp : block_t '× byte_seq in
    
    let aes_enc := fun x_0 x_1 => package_both aes_enc (x_0,x_1) in
    ((letbm out_241 : block_t loc( out_241_loc ) := lift_to_both0 state_243 in
        letb out_241 :=
          foldi_both' (lift_to_both0 (usize 0)) (seq_num_chunks (
                lift_to_both0 key_244) (
                lift_to_both0 blocksize_v)) out_241 (L := (CEfset (
                [out_241_loc]))) (I := ([interface
              #val #[ AES_ENC ] : aes_enc_inp → aes_enc_out
              ])) (fun i_245 out_241 =>
            letb '(_, key_block_246) : (uint_size '× seq uint8) :=
              seq_get_chunk (lift_to_both0 key_244) (
                lift_to_both0 blocksize_v) (lift_to_both0 i_245) in
            letbm out_241 loc( out_241_loc ) :=
              aes_enc (lift_to_both0 out_241) (array_from_seq (blocksize_v) (
                  lift_to_both0 key_block_246)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 out_241)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 out_241)
        ) : both (CEfset ([out_241_loc])) [interface
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
  256.
Program Definition block_cipher_aes
  : both_package (CEfset ([])) [interface
  #val #[ ADD_ROUND_KEY ] : add_round_key_inp → add_round_key_out ;
  #val #[ AES_ENC_LAST ] : aes_enc_last_inp → aes_enc_last_out ;
  #val #[ ROUNDS_AES ] : rounds_aes_inp → rounds_aes_out ] [(
    BLOCK_CIPHER_AES,(block_cipher_aes_inp,block_cipher_aes_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      input_253 , key_248 , nr_250) := temp_inp : block_t '× byte_seq '× uint_size in
    
    let add_round_key := fun x_0 x_1 => package_both add_round_key (x_0,x_1) in
    let aes_enc_last := fun x_0 x_1 => package_both aes_enc_last (x_0,x_1) in
    let rounds_aes := fun x_0 x_1 => package_both rounds_aes (x_0,x_1) in
    ((letb k0_249 : round_key_t :=
          array_from_slice_range (default : uint8) (blocksize_v) (
            lift_to_both0 key_248) (prod_b(
              lift_to_both0 (usize 0),
              lift_to_both0 (usize 16)
            )) in
        letb k_251 : seq uint8 :=
          seq_from_slice_range (lift_to_both0 key_248) (prod_b(
              lift_to_both0 (usize 16),
              (lift_to_both0 nr_250) .* (lift_to_both0 (usize 16))
            )) in
        letb kn_252 : round_key_t :=
          array_from_slice (default : uint8) (blocksize_v) (
            lift_to_both0 key_248) ((lift_to_both0 nr_250) .* (lift_to_both0 (
                usize 16))) (lift_to_both0 (usize 16)) in
        letb state_254 : block_t :=
          add_round_key (lift_to_both0 input_253) (lift_to_both0 k0_249) in
        letb state_255 : block_t :=
          rounds_aes (lift_to_both0 state_254) (lift_to_both0 k_251) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (aes_enc_last (
            lift_to_both0 state_255) (lift_to_both0 kn_252))
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
  258.
Program Definition rotate_word
  : both_package (fset.fset0) [interface] [(ROTATE_WORD,(
      rotate_word_inp,rotate_word_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(w_257) := temp_inp : word_t in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_list uint8 ([
              (array_index (w_257) (lift_to_both0 (usize 1))) : uint8;
              (array_index (w_257) (lift_to_both0 (usize 2))) : uint8;
              (array_index (w_257) (lift_to_both0 (usize 3))) : uint8;
              (array_index (w_257) (lift_to_both0 (usize 0))) : uint8
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
  260.
Program Definition slice_word
  : both_package (fset.fset0) [interface] [(SLICE_WORD,(
      slice_word_inp,slice_word_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(w_259) := temp_inp : word_t in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_list uint8 ([
              (array_index (sbox_v) (declassify_usize_from_uint8 (array_index (
                      w_259) (lift_to_both0 (usize 0))))) : uint8;
              (array_index (sbox_v) (declassify_usize_from_uint8 (array_index (
                      w_259) (lift_to_both0 (usize 1))))) : uint8;
              (array_index (sbox_v) (declassify_usize_from_uint8 (array_index (
                      w_259) (lift_to_both0 (usize 2))))) : uint8;
              (array_index (sbox_v) (declassify_usize_from_uint8 (array_index (
                      w_259) (lift_to_both0 (usize 3))))) : uint8
            ]))
        ) : both (fset.fset0) [interface] (word_t)))in
  both_package' _ _ (SLICE_WORD,(
      slice_word_inp,slice_word_out)) temp_package_both.
Fail Next Obligation.

Definition k_261_loc : ChoiceEqualityLocation :=
  (word_t ; 262%nat).
Notation "'aes_keygen_assist_inp'" :=(
  word_t '× uint8 : choice_type) (in custom pack_type at level 2).
Notation "'aes_keygen_assist_inp'" :=(
  word_t '× uint8 : ChoiceEquality) (at level 2).
Notation "'aes_keygen_assist_out'" :=(
  word_t : choice_type) (in custom pack_type at level 2).
Notation "'aes_keygen_assist_out'" :=(word_t : ChoiceEquality) (at level 2).
Definition AES_KEYGEN_ASSIST : nat :=
  265.
Program Definition aes_keygen_assist
  : both_package (CEfset ([k_261_loc])) [interface
  #val #[ ROTATE_WORD ] : rotate_word_inp → rotate_word_out ;
  #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ] [(
    AES_KEYGEN_ASSIST,(aes_keygen_assist_inp,aes_keygen_assist_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(w_263 , rcon_264) := temp_inp : word_t '× uint8 in
    
    let rotate_word := fun x_0 => package_both rotate_word (x_0) in
    let slice_word := fun x_0 => package_both slice_word (x_0) in
    ((letbm k_261 : word_t loc( k_261_loc ) :=
          rotate_word (lift_to_both0 w_263) in
        letbm k_261 loc( k_261_loc ) := slice_word (lift_to_both0 k_261) in
        letb k_261 : word_t :=
          array_upd k_261 (lift_to_both0 (usize 0)) (is_pure ((array_index (
                  k_261) (lift_to_both0 (usize 0))) .^ (
                lift_to_both0 rcon_264))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 k_261)
        ) : both (CEfset ([k_261_loc])) [interface
      #val #[ ROTATE_WORD ] : rotate_word_inp → rotate_word_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ] (word_t)))in
  both_package' _ _ (AES_KEYGEN_ASSIST,(
      aes_keygen_assist_inp,aes_keygen_assist_out)) temp_package_both.
Fail Next Obligation.

Definition k_266_loc : ChoiceEqualityLocation :=
  (word_t ; 268%nat).
Definition result_267_loc : ChoiceEqualityLocation :=
  ((result (int8) (word_t)) ; 269%nat).
Notation "'key_expansion_word_inp'" :=(
  word_t '× word_t '× uint_size '× uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'key_expansion_word_inp'" :=(
  word_t '× word_t '× uint_size '× uint_size '× uint_size : ChoiceEquality) (at level 2).
Notation "'key_expansion_word_out'" :=(
  word_result_t : choice_type) (in custom pack_type at level 2).
Notation "'key_expansion_word_out'" :=(
  word_result_t : ChoiceEquality) (at level 2).
Definition KEY_EXPANSION_WORD : nat :=
  276.
Program Definition key_expansion_word
  : both_package (CEfset ([k_266_loc ; result_267_loc])) [interface
  #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
  #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ] [(
    KEY_EXPANSION_WORD,(key_expansion_word_inp,key_expansion_word_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      w0_275 , w1_270 , i_271 , nk_273 , nr_272) := temp_inp : word_t '× word_t '× uint_size '× uint_size '× uint_size in
    
    let aes_keygen_assist := fun x_0 x_1 => package_both aes_keygen_assist (
      x_0,x_1) in
    let slice_word := fun x_0 => package_both slice_word (x_0) in
    ((letbm k_266 : word_t loc( k_266_loc ) := lift_to_both0 w1_270 in
        letbm result_267 : (result (int8) (word_t)) loc( result_267_loc ) :=
          @Err word_t int8 (lift_to_both0 invalid_key_expansion_index_v) in
        letb '(k_266, result_267) :=
          if (lift_to_both0 i_271) <.? ((lift_to_both0 (usize 4)) .* ((
                lift_to_both0 nr_272) .+ (lift_to_both0 (
                  usize 1)))) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset (
            [k_266_loc ; result_267_loc])) (L2 := CEfset (
            [k_266_loc ; result_267_loc])) (I1 := [interface
          #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
          #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out
          ]) (I2 := [interface
          #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
          #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (letb 'k_266 :=
              if ((lift_to_both0 i_271) %% (lift_to_both0 nk_273)) =.? (
                lift_to_both0 (usize 0)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                [k_266_loc ; result_267_loc])) (L2 := CEfset (
                [k_266_loc ; result_267_loc])) (I1 := [interface
              #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out
              ]) (I2 := [interface
              #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
              #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm k_266 loc( k_266_loc ) :=
                  aes_keygen_assist (lift_to_both0 k_266) (array_index (
                      rcon_v) ((lift_to_both0 i_271) ./ (
                        lift_to_both0 nk_273))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 k_266)
                )
              else  lift_scope (L1 := CEfset (
                [k_266_loc ; result_267_loc])) (L2 := CEfset (
                [k_266_loc ; result_267_loc])) (I1 := [interface
              #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out
              ]) (I2 := [interface
              #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
              #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (letb 'k_266 :=
                  if ((lift_to_both0 nk_273) >.? (lift_to_both0 (usize 6))) && (
                    ((lift_to_both0 i_271) %% (lift_to_both0 nk_273)) =.? (
                      lift_to_both0 (usize 4))) :bool_ChoiceEquality
                  then lift_scope (L1 := CEfset (
                    [k_266_loc ; result_267_loc])) (L2 := CEfset (
                    [k_266_loc ; result_267_loc])) (I1 := [interface
                  #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out
                  ]) (I2 := [interface
                  #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out
                  ]) (H_loc_incl := _) (H_opsig_incl := _) (
                    letbm k_266 loc( k_266_loc ) :=
                      slice_word (lift_to_both0 k_266) in
                    lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                      lift_to_both0 k_266)
                    )
                  else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                    lift_to_both0 k_266)
                   in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 k_266)
                ) in
            letb k_266 :=
              foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                    usize 4)) k_266 (L := (CEfset (
                    [k_266_loc ; result_267_loc]))) (I := ([interface
                  #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
                  #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out
                  ])) (fun i_274 k_266 =>
                letb k_266 : word_t :=
                  array_upd k_266 (lift_to_both0 i_274) (is_pure ((array_index (
                          k_266) (lift_to_both0 i_274)) .^ (array_index (
                          w0_275) (lift_to_both0 i_274)))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 k_266)
                ) in
            letbm result_267 loc( result_267_loc ) :=
              @Ok word_t int8 (lift_to_both0 k_266) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 k_266,
                lift_to_both0 result_267
              ))
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 k_266,
              lift_to_both0 result_267
            ))
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 result_267)
        ) : both (CEfset ([k_266_loc ; result_267_loc])) [interface
      #val #[ AES_KEYGEN_ASSIST ] : aes_keygen_assist_inp → aes_keygen_assist_out ;
      #val #[ SLICE_WORD ] : slice_word_inp → slice_word_out ] (
        word_result_t)))in
  both_package' _ _ (KEY_EXPANSION_WORD,(
      key_expansion_word_inp,key_expansion_word_out)) temp_package_both.
Fail Next Obligation.

Definition key_ex_277_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 278%nat).
Notation "'key_expansion_aes_inp'" :=(
  byte_seq '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'key_expansion_aes_inp'" :=(
  byte_seq '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size : ChoiceEquality) (at level 2).
Notation "'key_expansion_aes_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'key_expansion_aes_out'" :=(
  byte_seq_result_t : ChoiceEquality) (at level 2).
Definition KEY_EXPANSION_AES : nat :=
  289.
Program Definition key_expansion_aes
  : both_package (CEfset ([key_ex_277_loc])) [interface
  #val #[ KEY_EXPANSION_WORD ] : key_expansion_word_inp → key_expansion_word_out
  ] [(KEY_EXPANSION_AES,(key_expansion_aes_inp,key_expansion_aes_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      key_280 , nk_286 , nr_287 , key_schedule_length_279 , key_length_281 , iterations_283) := temp_inp : byte_seq '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size in
    
    let key_expansion_word := fun x_0 x_1 x_2 x_3 x_4 => package_both key_expansion_word (
      x_0,x_1,x_2,x_3,x_4) in
    ((letbm key_ex_277 : seq uint8 loc( key_ex_277_loc ) :=
          seq_new_ (default : uint8) (lift_to_both0 key_schedule_length_279) in
        letbm key_ex_277 loc( key_ex_277_loc ) :=
          seq_update_start (lift_to_both0 key_ex_277) (lift_to_both0 key_280) in
        letb word_size_282 : uint_size := lift_to_both0 key_length_281 in
        letbnd(_) key_ex_277 :=
          foldi_bind_both' (lift_to_both0 (usize 0)) (
              lift_to_both0 iterations_283) key_ex_277 (L := (CEfset (
                [key_ex_277_loc]))) (I := ([interface
              #val #[ KEY_EXPANSION_WORD ] : key_expansion_word_inp → key_expansion_word_out
              ])) (fun j_284 key_ex_277 =>
            letb i_285 : uint_size :=
              (lift_to_both0 j_284) .+ (lift_to_both0 word_size_282) in
            letbnd(_) word_288 : word_t :=
              key_expansion_word (array_from_slice (default : uint8) (
                  key_length_v) (lift_to_both0 key_ex_277) ((lift_to_both0 (
                      usize 4)) .* ((lift_to_both0 i_285) .- (
                      lift_to_both0 word_size_282))) (lift_to_both0 (
                    usize 4))) (array_from_slice (default : uint8) (
                  key_length_v) (lift_to_both0 key_ex_277) (((lift_to_both0 (
                        usize 4)) .* (lift_to_both0 i_285)) .- (lift_to_both0 (
                      usize 4))) (lift_to_both0 (usize 4))) (
                lift_to_both0 i_285) (lift_to_both0 nk_286) (
                lift_to_both0 nr_287) in
            letbm key_ex_277 loc( key_ex_277_loc ) :=
              seq_update (lift_to_both0 key_ex_277) ((lift_to_both0 (
                    usize 4)) .* (lift_to_both0 i_285)) (
                array_to_seq (lift_to_both0 word_288)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (seq uint8
              ) int8 (lift_to_both0 key_ex_277))
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok byte_seq int8 (
            lift_to_both0 key_ex_277))
        ) : both (CEfset ([key_ex_277_loc])) [interface
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
  298.
Program Definition aes_encrypt_block
  : both_package (CEfset ([])) [interface
  #val #[ BLOCK_CIPHER_AES ] : block_cipher_aes_inp → block_cipher_aes_out ;
  #val #[ KEY_EXPANSION_AES ] : key_expansion_aes_inp → key_expansion_aes_out
  ] [(AES_ENCRYPT_BLOCK,(aes_encrypt_block_inp,aes_encrypt_block_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      k_290 , input_297 , nk_291 , nr_292 , key_schedule_length_293 , key_length_294 , iterations_295) := temp_inp : byte_seq '× block_t '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size in
    
    let block_cipher_aes := fun x_0 x_1 x_2 => package_both block_cipher_aes (
      x_0,x_1,x_2) in
    let key_expansion_aes := fun x_0 x_1 x_2 x_3 x_4 x_5 => package_both key_expansion_aes (
      x_0,x_1,x_2,x_3,x_4,x_5) in
    ((letbnd(_) key_ex_296 : byte_seq :=
          key_expansion_aes (lift_to_both0 k_290) (lift_to_both0 nk_291) (
            lift_to_both0 nr_292) (lift_to_both0 key_schedule_length_293) (
            lift_to_both0 key_length_294) (lift_to_both0 iterations_295) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok block_t int8 (
            block_cipher_aes (lift_to_both0 input_297) (
              lift_to_both0 key_ex_296) (lift_to_both0 nr_292)))
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
  301.
Program Definition aes128_encrypt_block
  : both_package (CEfset ([])) [interface
  #val #[ AES_ENCRYPT_BLOCK ] : aes_encrypt_block_inp → aes_encrypt_block_out
  ] [(AES128_ENCRYPT_BLOCK,(
      aes128_encrypt_block_inp,aes128_encrypt_block_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(k_299 , input_300) := temp_inp : key128_t '× block_t in
    
    let aes_encrypt_block := fun x_0 x_1 x_2 x_3 x_4 x_5 x_6 => package_both aes_encrypt_block (
      x_0,x_1,x_2,x_3,x_4,x_5,x_6) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (result_unwrap (
            aes_encrypt_block (seq_from_seq (
                array_to_seq (lift_to_both0 k_299))) (lift_to_both0 input_300) (
              lift_to_both0 key_length_v) (lift_to_both0 rounds_v) (
              lift_to_both0 key_schedule_length_v) (
              lift_to_both0 key_length_v) (lift_to_both0 iterations_v)))
        ) : both (CEfset ([])) [interface
      #val #[ AES_ENCRYPT_BLOCK ] : aes_encrypt_block_inp → aes_encrypt_block_out
      ] (block_t)))in
  both_package' _ _ (AES128_ENCRYPT_BLOCK,(
      aes128_encrypt_block_inp,aes128_encrypt_block_out)) temp_package_both.
Fail Next Obligation.

Definition input_302_loc : ChoiceEqualityLocation :=
  (block_t ; 303%nat).
Notation "'aes_ctr_key_block_inp'" :=(
  byte_seq '× aes_nonce_t '× uint32 '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'aes_ctr_key_block_inp'" :=(
  byte_seq '× aes_nonce_t '× uint32 '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size : ChoiceEquality) (at level 2).
Notation "'aes_ctr_key_block_out'" :=(
  block_result_t : choice_type) (in custom pack_type at level 2).
Notation "'aes_ctr_key_block_out'" :=(
  block_result_t : ChoiceEquality) (at level 2).
Definition AES_CTR_KEY_BLOCK : nat :=
  312.
Program Definition aes_ctr_key_block
  : both_package (CEfset ([input_302_loc])) [interface
  #val #[ AES_ENCRYPT_BLOCK ] : aes_encrypt_block_inp → aes_encrypt_block_out
  ] [(AES_CTR_KEY_BLOCK,(aes_ctr_key_block_inp,aes_ctr_key_block_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      k_306 , n_304 , c_305 , nk_307 , nr_308 , key_schedule_length_309 , key_length_310 , iterations_311) := temp_inp : byte_seq '× aes_nonce_t '× uint32 '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size in
    
    let aes_encrypt_block := fun x_0 x_1 x_2 x_3 x_4 x_5 x_6 => package_both aes_encrypt_block (
      x_0,x_1,x_2,x_3,x_4,x_5,x_6) in
    ((letbm input_302 : block_t loc( input_302_loc ) :=
          array_new_ (default : uint8) (blocksize_v) in
        letbm input_302 loc( input_302_loc ) :=
          array_update (lift_to_both0 input_302) (lift_to_both0 (usize 0)) (
            array_to_seq (lift_to_both0 n_304)) in
        letbm input_302 loc( input_302_loc ) :=
          array_update (lift_to_both0 input_302) (lift_to_both0 (usize 12)) (
            array_to_seq (uint32_to_be_bytes (lift_to_both0 c_305))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (aes_encrypt_block (
            lift_to_both0 k_306) (lift_to_both0 input_302) (
            lift_to_both0 nk_307) (lift_to_both0 nr_308) (
            lift_to_both0 key_schedule_length_309) (
            lift_to_both0 key_length_310) (lift_to_both0 iterations_311))
        ) : both (CEfset ([input_302_loc])) [interface
      #val #[ AES_ENCRYPT_BLOCK ] : aes_encrypt_block_inp → aes_encrypt_block_out
      ] (block_result_t)))in
  both_package' _ _ (AES_CTR_KEY_BLOCK,(
      aes_ctr_key_block_inp,aes_ctr_key_block_out)) temp_package_both.
Fail Next Obligation.

Definition out_313_loc : ChoiceEqualityLocation :=
  (block_t ; 314%nat).
Notation "'xor_block_inp'" :=(
  block_t '× block_t : choice_type) (in custom pack_type at level 2).
Notation "'xor_block_inp'" :=(
  block_t '× block_t : ChoiceEquality) (at level 2).
Notation "'xor_block_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'xor_block_out'" :=(block_t : ChoiceEquality) (at level 2).
Definition XOR_BLOCK : nat :=
  318.
Program Definition xor_block
  : both_package (CEfset ([out_313_loc])) [interface] [(XOR_BLOCK,(
      xor_block_inp,xor_block_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(block_315 , key_block_317) := temp_inp : block_t '× block_t in
    
    ((letbm out_313 : block_t loc( out_313_loc ) := lift_to_both0 block_315 in
        letb out_313 :=
          foldi_both' (lift_to_both0 (usize 0)) (
              lift_to_both0 blocksize_v) out_313 (L := (CEfset (
                [out_313_loc]))) (I := ([interface])) (fun i_316 out_313 =>
            letb out_313 : block_t :=
              array_upd out_313 (lift_to_both0 i_316) (is_pure ((array_index (
                      out_313) (lift_to_both0 i_316)) .^ (array_index (
                      key_block_317) (lift_to_both0 i_316)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 out_313)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 out_313)
        ) : both (CEfset ([out_313_loc])) [interface] (block_t)))in
  both_package' _ _ (XOR_BLOCK,(xor_block_inp,xor_block_out)) temp_package_both.
Fail Next Obligation.

Definition ctr_319_loc : ChoiceEqualityLocation :=
  (uint32 ; 321%nat).
Definition blocks_out_320_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 322%nat).
Notation "'aes_counter_mode_inp'" :=(
  byte_seq '× aes_nonce_t '× uint32 '× byte_seq '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'aes_counter_mode_inp'" :=(
  byte_seq '× aes_nonce_t '× uint32 '× byte_seq '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size : ChoiceEquality) (at level 2).
Notation "'aes_counter_mode_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'aes_counter_mode_out'" :=(
  byte_seq_result_t : ChoiceEquality) (at level 2).
Definition AES_COUNTER_MODE : nat :=
  340.
Program Definition aes_counter_mode
  : both_package (CEfset ([ctr_319_loc ; blocks_out_320_loc])) [interface
  #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
  #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out ] [(AES_COUNTER_MODE,(
      aes_counter_mode_inp,aes_counter_mode_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      key_328 , nonce_329 , counter_323 , msg_324 , nk_330 , nr_331 , key_schedule_length_332 , key_length_333 , iterations_334) := temp_inp : byte_seq '× aes_nonce_t '× uint32 '× byte_seq '× uint_size '× uint_size '× uint_size '× uint_size '× uint_size in
    
    let aes_ctr_key_block := fun x_0 x_1 x_2 x_3 x_4 x_5 x_6 x_7 => package_both aes_ctr_key_block (
      x_0,x_1,x_2,x_3,x_4,x_5,x_6,x_7) in
    let xor_block := fun x_0 x_1 => package_both xor_block (x_0,x_1) in
    ((letbm ctr_319 : uint32 loc( ctr_319_loc ) := lift_to_both0 counter_323 in
        letbm blocks_out_320 : seq uint8 loc( blocks_out_320_loc ) :=
          seq_new_ (default : uint8) (seq_len (lift_to_both0 msg_324)) in
        letb n_blocks_325 : uint_size :=
          seq_num_exact_chunks (lift_to_both0 msg_324) (
            lift_to_both0 blocksize_v) in
        letbnd(_) '(ctr_319, blocks_out_320) :=
          foldi_bind_both' (lift_to_both0 (usize 0)) (
              lift_to_both0 n_blocks_325) prod_ce(ctr_319, blocks_out_320
            ) (L := (CEfset ([ctr_319_loc ; blocks_out_320_loc]))) (I := (
              [interface
              #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
              #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out
              ])) (fun i_326 '(ctr_319, blocks_out_320) =>
            letb msg_block_327 : seq uint8 :=
              seq_get_exact_chunk (lift_to_both0 msg_324) (
                lift_to_both0 blocksize_v) (lift_to_both0 i_326) in
            letbnd(_) key_block_335 : block_t :=
              aes_ctr_key_block (lift_to_both0 key_328) (
                lift_to_both0 nonce_329) (lift_to_both0 ctr_319) (
                lift_to_both0 nk_330) (lift_to_both0 nr_331) (
                lift_to_both0 key_schedule_length_332) (
                lift_to_both0 key_length_333) (lift_to_both0 iterations_334) in
            letbm blocks_out_320 loc( blocks_out_320_loc ) :=
              seq_set_chunk (lift_to_both0 blocks_out_320) (
                lift_to_both0 blocksize_v) (lift_to_both0 i_326) (
                array_to_seq (xor_block (array_from_seq (blocksize_v) (
                    lift_to_both0 msg_block_327)) (
                  lift_to_both0 key_block_335))) in
            letbm ctr_319 loc( ctr_319_loc ) :=
              (lift_to_both0 ctr_319) .+ (secret (lift_to_both0 (
                    @repr U32 1))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (
                uint32 '×
                seq uint8
              ) int8 (prod_b(lift_to_both0 ctr_319, lift_to_both0 blocks_out_320
                )))
            ) in
        letb last_block_336 : seq uint8 :=
          seq_get_remainder_chunk (lift_to_both0 msg_324) (
            lift_to_both0 blocksize_v) in
        letb last_block_len_337 : uint_size :=
          seq_len (lift_to_both0 last_block_336) in
        letbnd(_) 'blocks_out_320 :=
          if (lift_to_both0 last_block_len_337) !=.? (lift_to_both0 (
              usize 0)) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset (
            [ctr_319_loc ; blocks_out_320_loc])) (L2 := CEfset (
            [ctr_319_loc ; blocks_out_320_loc])) (I1 := [interface
          #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
          #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out
          ]) (I2 := [interface
          #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
          #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letb last_block_338 : block_t :=
              array_update_start (array_new_ (default : uint8) (blocksize_v)) (
                lift_to_both0 last_block_336) in
            letbnd(_) key_block_339 : block_t :=
              aes_ctr_key_block (lift_to_both0 key_328) (
                lift_to_both0 nonce_329) (lift_to_both0 ctr_319) (
                lift_to_both0 nk_330) (lift_to_both0 nr_331) (
                lift_to_both0 key_schedule_length_332) (
                lift_to_both0 key_length_333) (lift_to_both0 iterations_334) in
            letbm blocks_out_320 loc( blocks_out_320_loc ) :=
              seq_set_chunk (lift_to_both0 blocks_out_320) (
                lift_to_both0 blocksize_v) (lift_to_both0 n_blocks_325) (
                array_slice_range (xor_block (lift_to_both0 last_block_338) (
                    lift_to_both0 key_block_339)) (prod_b(
                    lift_to_both0 (usize 0),
                    lift_to_both0 last_block_len_337
                  ))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (seq uint8
              ) int8 (lift_to_both0 blocks_out_320))
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (seq uint8
            ) int8 (lift_to_both0 blocks_out_320))
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok byte_seq int8 (
            lift_to_both0 blocks_out_320))
        ) : both (CEfset ([ctr_319_loc ; blocks_out_320_loc])) [interface
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
  345.
Program Definition aes128_encrypt
  : both_package (CEfset ([])) [interface
  #val #[ AES_COUNTER_MODE ] : aes_counter_mode_inp → aes_counter_mode_out
  ] [(AES128_ENCRYPT,(aes128_encrypt_inp,aes128_encrypt_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      key_341 , nonce_342 , counter_343 , msg_344) := temp_inp : key128_t '× aes_nonce_t '× uint32 '× byte_seq in
    
    let aes_counter_mode := fun x_0 x_1 x_2 x_3 x_4 x_5 x_6 x_7 x_8 => package_both aes_counter_mode (
      x_0,x_1,x_2,x_3,x_4,x_5,x_6,x_7,x_8) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (result_unwrap (
            aes_counter_mode (seq_from_seq (
                array_to_seq (lift_to_both0 key_341))) (
              lift_to_both0 nonce_342) (lift_to_both0 counter_343) (
              lift_to_both0 msg_344) (lift_to_both0 key_length_v) (
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
  350.
Program Definition aes128_decrypt
  : both_package (CEfset ([])) [interface
  #val #[ AES_COUNTER_MODE ] : aes_counter_mode_inp → aes_counter_mode_out
  ] [(AES128_DECRYPT,(aes128_decrypt_inp,aes128_decrypt_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      key_346 , nonce_347 , counter_348 , ctxt_349) := temp_inp : key128_t '× aes_nonce_t '× uint32 '× byte_seq in
    
    let aes_counter_mode := fun x_0 x_1 x_2 x_3 x_4 x_5 x_6 x_7 x_8 => package_both aes_counter_mode (
      x_0,x_1,x_2,x_3,x_4,x_5,x_6,x_7,x_8) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (result_unwrap (
            aes_counter_mode (seq_from_seq (
                array_to_seq (lift_to_both0 key_346))) (
              lift_to_both0 nonce_347) (lift_to_both0 counter_348) (
              lift_to_both0 ctxt_349) (lift_to_both0 key_length_v) (
              lift_to_both0 rounds_v) (lift_to_both0 key_schedule_length_v) (
              lift_to_both0 key_length_v) (lift_to_both0 iterations_v)))
        ) : both (CEfset ([])) [interface
      #val #[ AES_COUNTER_MODE ] : aes_counter_mode_inp → aes_counter_mode_out
      ] (byte_seq)))in
  both_package' _ _ (AES128_DECRYPT,(
      aes128_decrypt_inp,aes128_decrypt_out)) temp_package_both.
Fail Next Obligation.

