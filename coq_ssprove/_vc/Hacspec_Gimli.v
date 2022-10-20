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


Definition state_t := nseq (uint32) (usize 12).

Definition state_idx_t :=
  nat_mod (usize 12).
Definition uint_size_in_state_idx_t(n : uint_size) : state_idx_t := int_in_nat_mod n.
Coercion uint_size_in_state_idx_t : uint_size >-> state_idx_t.


Notation "'swap_inp'" :=(
  state_t '× state_idx_t '× state_idx_t : choice_type) (in custom pack_type at level 2).
Notation "'swap_inp'" :=(
  state_t '× state_idx_t '× state_idx_t : ChoiceEquality) (at level 2).
Notation "'swap_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'swap_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition SWAP : nat :=
  1254.
Program Definition swap
  : both_package (fset.fset0) [interface] [(SWAP,(swap_inp,swap_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      s_1251 , i_1250 , j_1253) := temp_inp : state_t '× state_idx_t '× state_idx_t in
    
    ((letb tmp_1252 : uint32 := array_index (s_1251) (lift_to_both0 i_1250) in
        letb s_1251 : state_t :=
          array_upd s_1251 (lift_to_both0 i_1250) (is_pure (array_index (
                s_1251) (lift_to_both0 j_1253))) in
        letb s_1251 : state_t :=
          array_upd s_1251 (lift_to_both0 j_1253) (is_pure (
              lift_to_both0 tmp_1252)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1251)
        ) : both (fset.fset0) [interface] (state_t)))in
  both_package' _ _ (SWAP,(swap_inp,swap_out)) temp_package_both.
Fail Next Obligation.


Notation "'gimli_round_inp'" :=(
  state_t '× int32 : choice_type) (in custom pack_type at level 2).
Notation "'gimli_round_inp'" :=(
  state_t '× int32 : ChoiceEquality) (at level 2).
Notation "'gimli_round_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'gimli_round_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition GIMLI_ROUND : nat :=
  1261.
Program Definition gimli_round
  : both_package (fset.fset0) [interface #val #[ SWAP ] : swap_inp → swap_out
  ] [(GIMLI_ROUND,(gimli_round_inp,gimli_round_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(s_1255 , r_1260) := temp_inp : state_t '× int32 in
    
    let swap := fun x_0 x_1 x_2 => package_both swap (x_0,x_1,x_2) in
    ((letb s_1255 :=
          foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                usize 4)) s_1255 (L := (fset.fset0)) (I := ([interface
              #val #[ SWAP ] : swap_inp → swap_out ])) (fun col_1256 s_1255 =>
            letb x_1257 : uint32 :=
              uint32_rotate_left (array_index (s_1255) (
                  lift_to_both0 col_1256)) (lift_to_both0 (usize 24)) in
            letb y_1258 : uint32 :=
              uint32_rotate_left (array_index (s_1255) ((
                    lift_to_both0 col_1256) .+ (lift_to_both0 (usize 4)))) (
                lift_to_both0 (usize 9)) in
            letb z_1259 : uint32 :=
              array_index (s_1255) ((lift_to_both0 col_1256) .+ (lift_to_both0 (
                    usize 8))) in
            letb s_1255 : state_t :=
              array_upd s_1255 ((lift_to_both0 col_1256) .+ (lift_to_both0 (
                    usize 8))) (is_pure (((lift_to_both0 x_1257) .^ ((
                        lift_to_both0 z_1259) shift_left (lift_to_both0 (
                          usize 1)))) .^ (((lift_to_both0 y_1258) .& (
                        lift_to_both0 z_1259)) shift_left (lift_to_both0 (
                        usize 2))))) in
            letb s_1255 : state_t :=
              array_upd s_1255 ((lift_to_both0 col_1256) .+ (lift_to_both0 (
                    usize 4))) (is_pure (((lift_to_both0 y_1258) .^ (
                      lift_to_both0 x_1257)) .^ (((lift_to_both0 x_1257) .| (
                        lift_to_both0 z_1259)) shift_left (lift_to_both0 (
                        usize 1))))) in
            letb s_1255 : state_t :=
              array_upd s_1255 (lift_to_both0 col_1256) (is_pure (((
                      lift_to_both0 z_1259) .^ (lift_to_both0 y_1258)) .^ (((
                        lift_to_both0 x_1257) .& (
                        lift_to_both0 y_1258)) shift_left (lift_to_both0 (
                        usize 3))))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_1255)
            ) in
        letb 's_1255 :=
          if ((lift_to_both0 r_1260) .& (lift_to_both0 (@repr U32 3))) =.? (
            lift_to_both0 (@repr U32 0)) :bool_ChoiceEquality
          then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (I1 := [interface
          #val #[ SWAP ] : swap_inp → swap_out ]) (I2 := [interface
          #val #[ SWAP ] : swap_inp → swap_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm s_1255 loc( s_1255_loc ) :=
              swap (lift_to_both0 s_1255) (lift_to_both0 (usize 0)) (
                lift_to_both0 (usize 1)) in
            letbm s_1255 loc( s_1255_loc ) :=
              swap (lift_to_both0 s_1255) (lift_to_both0 (usize 2)) (
                lift_to_both0 (usize 3)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_1255)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 s_1255)
           in
        letb 's_1255 :=
          if ((lift_to_both0 r_1260) .& (lift_to_both0 (@repr U32 3))) =.? (
            lift_to_both0 (@repr U32 2)) :bool_ChoiceEquality
          then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (I1 := [interface
          #val #[ SWAP ] : swap_inp → swap_out ]) (I2 := [interface
          #val #[ SWAP ] : swap_inp → swap_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm s_1255 loc( s_1255_loc ) :=
              swap (lift_to_both0 s_1255) (lift_to_both0 (usize 0)) (
                lift_to_both0 (usize 2)) in
            letbm s_1255 loc( s_1255_loc ) :=
              swap (lift_to_both0 s_1255) (lift_to_both0 (usize 1)) (
                lift_to_both0 (usize 3)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_1255)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 s_1255)
           in
        letb 's_1255 :=
          if ((lift_to_both0 r_1260) .& (lift_to_both0 (@repr U32 3))) =.? (
            lift_to_both0 (@repr U32 0)) :bool_ChoiceEquality
          then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (I1 := [interface]) (I2 := [interface
          #val #[ SWAP ] : swap_inp → swap_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (letb s_1255 : state_t :=
              array_upd s_1255 (lift_to_both0 (usize 0)) (is_pure ((
                    array_index (s_1255) (lift_to_both0 (usize 0))) .^ ((
                      secret (lift_to_both0 (@repr U32 2654435584))) .| (
                      secret (lift_to_both0 r_1260))))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_1255)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 s_1255)
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1255)
        ) : both (fset.fset0) [interface #val #[ SWAP ] : swap_inp → swap_out
      ] (state_t)))in
  both_package' _ _ (GIMLI_ROUND,(
      gimli_round_inp,gimli_round_out)) temp_package_both.
Fail Next Obligation.


Notation "'gimli_inp'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'gimli_inp'" :=(state_t : ChoiceEquality) (at level 2).
Notation "'gimli_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'gimli_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition GIMLI : nat :=
  1265.
Program Definition gimli
  : both_package (fset.fset0) [interface
  #val #[ GIMLI_ROUND ] : gimli_round_inp → gimli_round_out ] [(GIMLI,(
      gimli_inp,gimli_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(s_1262) := temp_inp : state_t in
    
    let gimli_round := fun x_0 x_1 => package_both gimli_round (x_0,x_1) in
    ((letb s_1262 :=
          foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                usize 24)) s_1262 (L := (fset.fset0)) (I := ([interface
              #val #[ GIMLI_ROUND ] : gimli_round_inp → gimli_round_out
              ])) (fun rnd_1263 s_1262 =>
            letb rnd_1264 : int32 :=
              pub_u32 (is_pure ((lift_to_both0 (usize 24)) .- (
                    lift_to_both0 rnd_1263))) in
            letbm s_1262 loc( s_1262_loc ) :=
              gimli_round (lift_to_both0 s_1262) (lift_to_both0 rnd_1264) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_1262)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1262)
        ) : both (fset.fset0) [interface
      #val #[ GIMLI_ROUND ] : gimli_round_inp → gimli_round_out ] (
        state_t)))in
  both_package' _ _ (GIMLI,(gimli_inp,gimli_out)) temp_package_both.
Fail Next Obligation.

Definition block_t := nseq (uint8) (usize 16).

Definition digest_t := nseq (uint8) (usize 32).


Notation "'absorb_block_inp'" :=(
  block_t '× state_t : choice_type) (in custom pack_type at level 2).
Notation "'absorb_block_inp'" :=(
  block_t '× state_t : ChoiceEquality) (at level 2).
Notation "'absorb_block_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'absorb_block_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition ABSORB_BLOCK : nat :=
  1269.
Program Definition absorb_block
  : both_package (fset.fset0) [interface
  #val #[ GIMLI ] : gimli_inp → gimli_out ] [(ABSORB_BLOCK,(
      absorb_block_inp,absorb_block_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(input_block_1266 , s_1268) := temp_inp : block_t '× state_t in
    
    let gimli := fun x_0 => package_both gimli (x_0) in
    ((letb input_bytes_1267 : seq uint32 :=
          array_to_le_uint32s (lift_to_both0 input_block_1266) in
        letb s_1268 : state_t :=
          array_upd s_1268 (lift_to_both0 (usize 0)) (is_pure ((array_index (
                  s_1268) (lift_to_both0 (usize 0))) .^ (seq_index (
                  input_bytes_1267) (lift_to_both0 (usize 0))))) in
        letb s_1268 : state_t :=
          array_upd s_1268 (lift_to_both0 (usize 1)) (is_pure ((array_index (
                  s_1268) (lift_to_both0 (usize 1))) .^ (seq_index (
                  input_bytes_1267) (lift_to_both0 (usize 1))))) in
        letb s_1268 : state_t :=
          array_upd s_1268 (lift_to_both0 (usize 2)) (is_pure ((array_index (
                  s_1268) (lift_to_both0 (usize 2))) .^ (seq_index (
                  input_bytes_1267) (lift_to_both0 (usize 2))))) in
        letb s_1268 : state_t :=
          array_upd s_1268 (lift_to_both0 (usize 3)) (is_pure ((array_index (
                  s_1268) (lift_to_both0 (usize 3))) .^ (seq_index (
                  input_bytes_1267) (lift_to_both0 (usize 3))))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (gimli (
            lift_to_both0 s_1268))
        ) : both (fset.fset0) [interface
      #val #[ GIMLI ] : gimli_inp → gimli_out ] (state_t)))in
  both_package' _ _ (ABSORB_BLOCK,(
      absorb_block_inp,absorb_block_out)) temp_package_both.
Fail Next Obligation.

Definition block_1270_loc : ChoiceEqualityLocation :=
  (block_t ; 1271%nat).
Notation "'squeeze_block_inp'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'squeeze_block_inp'" :=(state_t : ChoiceEquality) (at level 2).
Notation "'squeeze_block_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'squeeze_block_out'" :=(block_t : ChoiceEquality) (at level 2).
Definition SQUEEZE_BLOCK : nat :=
  1276.
Program Definition squeeze_block
  : both_package (CEfset ([block_1270_loc])) [interface] [(SQUEEZE_BLOCK,(
      squeeze_block_inp,squeeze_block_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(s_1273) := temp_inp : state_t in
    
    ((letbm block_1270 : block_t loc( block_1270_loc ) :=
          array_new_ (default : uint8) (16) in
        letb block_1270 :=
          foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                usize 4)) block_1270 (L := (CEfset ([block_1270_loc]))) (I := (
              [interface])) (fun i_1272 block_1270 =>
            letb s_i_1274 : uint32 :=
              array_index (s_1273) (lift_to_both0 i_1272) in
            letb s_i_bytes_1275 : seq uint8 :=
              uint32_to_le_bytes (lift_to_both0 s_i_1274) in
            letb block_1270 : block_t :=
              array_upd block_1270 ((lift_to_both0 (usize 4)) .* (
                  lift_to_both0 i_1272)) (is_pure (seq_index (s_i_bytes_1275) (
                    lift_to_both0 (usize 0)))) in
            letb block_1270 : block_t :=
              array_upd block_1270 (((lift_to_both0 (usize 4)) .* (
                    lift_to_both0 i_1272)) .+ (lift_to_both0 (usize 1))) (
                is_pure (seq_index (s_i_bytes_1275) (lift_to_both0 (
                      usize 1)))) in
            letb block_1270 : block_t :=
              array_upd block_1270 (((lift_to_both0 (usize 4)) .* (
                    lift_to_both0 i_1272)) .+ (lift_to_both0 (usize 2))) (
                is_pure (seq_index (s_i_bytes_1275) (lift_to_both0 (
                      usize 2)))) in
            letb block_1270 : block_t :=
              array_upd block_1270 (((lift_to_both0 (usize 4)) .* (
                    lift_to_both0 i_1272)) .+ (lift_to_both0 (usize 3))) (
                is_pure (seq_index (s_i_bytes_1275) (lift_to_both0 (
                      usize 3)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 block_1270)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 block_1270)
        ) : both (CEfset ([block_1270_loc])) [interface] (block_t)))in
  both_package' _ _ (SQUEEZE_BLOCK,(
      squeeze_block_inp,squeeze_block_out)) temp_package_both.
Fail Next Obligation.

Definition input_block_padded_1277_loc : ChoiceEqualityLocation :=
  (block_t ; 1278%nat).
Notation "'gimli_hash_state_inp'" :=(
  byte_seq '× state_t : choice_type) (in custom pack_type at level 2).
Notation "'gimli_hash_state_inp'" :=(
  byte_seq '× state_t : ChoiceEquality) (at level 2).
Notation "'gimli_hash_state_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'gimli_hash_state_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition GIMLI_HASH_STATE : nat :=
  1288.
Program Definition gimli_hash_state
  : both_package (CEfset ([input_block_padded_1277_loc])) [interface
  #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out ] [(
    GIMLI_HASH_STATE,(gimli_hash_state_inp,gimli_hash_state_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(input_1280 , s_1282) := temp_inp : byte_seq '× state_t in
    
    let absorb_block := fun x_0 x_1 => package_both absorb_block (x_0,x_1) in
    ((letb rate_1279 : uint_size := array_length  in
        letb chunks_1281 : uint_size :=
          seq_num_exact_chunks (lift_to_both0 input_1280) (
            lift_to_both0 rate_1279) in
        letb s_1282 :=
          foldi_both' (lift_to_both0 (usize 0)) (
              lift_to_both0 chunks_1281) s_1282 (L := (CEfset (
                [input_block_padded_1277_loc]))) (I := ([interface
              #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out
              ])) (fun i_1283 s_1282 =>
            letb input_block_1284 : seq uint8 :=
              seq_get_exact_chunk (lift_to_both0 input_1280) (
                lift_to_both0 rate_1279) (lift_to_both0 i_1283) in
            letb full_block_1285 : block_t :=
              array_from_seq (16) (lift_to_both0 input_block_1284) in
            letbm s_1282 loc( s_1282_loc ) :=
              absorb_block (lift_to_both0 full_block_1285) (
                lift_to_both0 s_1282) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_1282)
            ) in
        letb input_block_1286 : seq uint8 :=
          seq_get_remainder_chunk (lift_to_both0 input_1280) (
            lift_to_both0 rate_1279) in
        letb input_block_padded_1287 : block_t :=
          array_new_ (default : uint8) (16) in
        letbm input_block_padded_1277 : block_t loc( input_block_padded_1277_loc ) :=
          array_update_start (lift_to_both0 input_block_padded_1287) (
            lift_to_both0 input_block_1286) in
        letb input_block_padded_1277 : block_t :=
          array_upd input_block_padded_1277 (seq_len (
              lift_to_both0 input_block_1286)) (is_pure (secret (lift_to_both0 (
                  @repr U8 1)))) in
        letb s_1282 : state_t :=
          array_upd s_1282 (lift_to_both0 (usize 11)) (is_pure ((array_index (
                  s_1282) (lift_to_both0 (usize 11))) .^ (secret (
                  lift_to_both0 (@repr U32 16777216))))) in
        letbm s_1282 loc( s_1282_loc ) :=
          absorb_block (lift_to_both0 input_block_padded_1277) (
            lift_to_both0 s_1282) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1282)
        ) : both (CEfset ([input_block_padded_1277_loc])) [interface
      #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out ] (
        state_t)))in
  both_package' _ _ (GIMLI_HASH_STATE,(
      gimli_hash_state_inp,gimli_hash_state_out)) temp_package_both.
Fail Next Obligation.


Notation "'gimli_hash_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'gimli_hash_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'gimli_hash_out'" :=(
  digest_t : choice_type) (in custom pack_type at level 2).
Notation "'gimli_hash_out'" :=(digest_t : ChoiceEquality) (at level 2).
Definition GIMLI_HASH : nat :=
  1295.
Program Definition gimli_hash
  : both_package (CEfset ([])) [interface
  #val #[ GIMLI ] : gimli_inp → gimli_out ;
  #val #[ GIMLI_HASH_STATE ] : gimli_hash_state_inp → gimli_hash_state_out ;
  #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out ] [(
    GIMLI_HASH,(gimli_hash_inp,gimli_hash_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(input_bytes_1290) := temp_inp : byte_seq in
    
    let gimli := fun x_0 => package_both gimli (x_0) in
    let gimli_hash_state := fun x_0 x_1 => package_both gimli_hash_state (
      x_0,x_1) in
    let squeeze_block := fun x_0 => package_both squeeze_block (x_0) in
    ((letb s_1289 : state_t := array_new_ (default : uint32) (12) in
        letb s_1291 : state_t :=
          gimli_hash_state (lift_to_both0 input_bytes_1290) (
            lift_to_both0 s_1289) in
        letb output_1292 : digest_t := array_new_ (default : uint8) (32) in
        letb output_1293 : digest_t :=
          array_update_start (lift_to_both0 output_1292) (
            array_to_seq (squeeze_block (lift_to_both0 s_1291))) in
        letb s_1294 : state_t := gimli (lift_to_both0 s_1291) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_update (
            lift_to_both0 output_1293) (array_length ) (
            array_to_seq (squeeze_block (lift_to_both0 s_1294))))
        ) : both (CEfset ([])) [interface
      #val #[ GIMLI ] : gimli_inp → gimli_out ;
      #val #[ GIMLI_HASH_STATE ] : gimli_hash_state_inp → gimli_hash_state_out ;
      #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out ] (
        digest_t)))in
  both_package' _ _ (GIMLI_HASH,(
      gimli_hash_inp,gimli_hash_out)) temp_package_both.
Fail Next Obligation.

Definition nonce_t := nseq (uint8) (usize 16).

Definition key_t := nseq (uint8) (usize 32).

Definition tag_t := nseq (uint8) (usize 16).


Notation "'process_ad_inp'" :=(
  byte_seq '× state_t : choice_type) (in custom pack_type at level 2).
Notation "'process_ad_inp'" :=(
  byte_seq '× state_t : ChoiceEquality) (at level 2).
Notation "'process_ad_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'process_ad_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition PROCESS_AD : nat :=
  1298.
Program Definition process_ad
  : both_package (CEfset ([])) [interface
  #val #[ GIMLI_HASH_STATE ] : gimli_hash_state_inp → gimli_hash_state_out
  ] [(PROCESS_AD,(process_ad_inp,process_ad_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(ad_1296 , s_1297) := temp_inp : byte_seq '× state_t in
    
    let gimli_hash_state := fun x_0 x_1 => package_both gimli_hash_state (
      x_0,x_1) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (gimli_hash_state (
            lift_to_both0 ad_1296) (lift_to_both0 s_1297))
        ) : both (CEfset ([])) [interface
      #val #[ GIMLI_HASH_STATE ] : gimli_hash_state_inp → gimli_hash_state_out
      ] (state_t)))in
  both_package' _ _ (PROCESS_AD,(
      process_ad_inp,process_ad_out)) temp_package_both.
Fail Next Obligation.

Definition ciphertext_1299_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 1301%nat).
Definition msg_block_padded_1300_loc : ChoiceEqualityLocation :=
  (block_t ; 1302%nat).
Notation "'process_msg_inp'" :=(
  byte_seq '× state_t : choice_type) (in custom pack_type at level 2).
Notation "'process_msg_inp'" :=(
  byte_seq '× state_t : ChoiceEquality) (at level 2).
Notation "'process_msg_out'" :=((state_t '× byte_seq
  ) : choice_type) (in custom pack_type at level 2).
Notation "'process_msg_out'" :=((state_t '× byte_seq
  ) : ChoiceEquality) (at level 2).
Definition PROCESS_MSG : nat :=
  1315.
Program Definition process_msg
  : both_package (CEfset (
      [ciphertext_1299_loc ; msg_block_padded_1300_loc])) [interface
  #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out ;
  #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out ] [(
    PROCESS_MSG,(process_msg_inp,process_msg_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(message_1303 , s_1306) := temp_inp : byte_seq '× state_t in
    
    let absorb_block := fun x_0 x_1 => package_both absorb_block (x_0,x_1) in
    let squeeze_block := fun x_0 => package_both squeeze_block (x_0) in
    ((letbm ciphertext_1299 : seq uint8 loc( ciphertext_1299_loc ) :=
          seq_new_ (default : uint8) (seq_len (lift_to_both0 message_1303)) in
        letb rate_1304 : uint_size := array_length  in
        letb num_chunks_1305 : uint_size :=
          seq_num_exact_chunks (lift_to_both0 message_1303) (
            lift_to_both0 rate_1304) in
        letb '(s_1306, ciphertext_1299) :=
          foldi_both' (lift_to_both0 (usize 0)) (
              lift_to_both0 num_chunks_1305) prod_ce(s_1306, ciphertext_1299
            ) (L := (CEfset (
                [ciphertext_1299_loc ; msg_block_padded_1300_loc]))) (I := (
              [interface
              #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out ;
              #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out
              ])) (fun i_1307 '(s_1306, ciphertext_1299) =>
            letb key_block_1308 : block_t :=
              squeeze_block (lift_to_both0 s_1306) in
            letb msg_block_1309 : seq uint8 :=
              seq_get_exact_chunk (lift_to_both0 message_1303) (
                lift_to_both0 rate_1304) (lift_to_both0 i_1307) in
            letb msg_block_1310 : block_t :=
              array_from_seq (16) (lift_to_both0 msg_block_1309) in
            letbm ciphertext_1299 loc( ciphertext_1299_loc ) :=
              seq_set_exact_chunk (lift_to_both0 ciphertext_1299) (
                lift_to_both0 rate_1304) (lift_to_both0 i_1307) (array_to_seq ((
                  lift_to_both0 msg_block_1310) array_xor (
                  lift_to_both0 key_block_1308))) in
            letbm s_1306 loc( s_1306_loc ) :=
              absorb_block (lift_to_both0 msg_block_1310) (
                lift_to_both0 s_1306) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 s_1306,
                lift_to_both0 ciphertext_1299
              ))
            ) in
        letb key_block_1311 : block_t := squeeze_block (lift_to_both0 s_1306) in
        letb last_block_1312 : seq uint8 :=
          seq_get_remainder_chunk (lift_to_both0 message_1303) (
            lift_to_both0 rate_1304) in
        letb block_len_1313 : uint_size :=
          seq_len (lift_to_both0 last_block_1312) in
        letb msg_block_padded_1314 : block_t :=
          array_new_ (default : uint8) (16) in
        letbm msg_block_padded_1300 : block_t loc( msg_block_padded_1300_loc ) :=
          array_update_start (lift_to_both0 msg_block_padded_1314) (
            lift_to_both0 last_block_1312) in
        letbm ciphertext_1299 loc( ciphertext_1299_loc ) :=
          seq_set_chunk (lift_to_both0 ciphertext_1299) (
            lift_to_both0 rate_1304) (lift_to_both0 num_chunks_1305) (
            array_slice_range ((lift_to_both0 msg_block_padded_1300) array_xor (
                lift_to_both0 key_block_1311)) (prod_b(
                lift_to_both0 (usize 0),
                lift_to_both0 block_len_1313
              ))) in
        letb msg_block_padded_1300 : block_t :=
          array_upd msg_block_padded_1300 (lift_to_both0 block_len_1313) (
            is_pure ((array_index (msg_block_padded_1300) (
                  lift_to_both0 block_len_1313)) .^ (secret (lift_to_both0 (
                    @repr U8 1))))) in
        letb s_1306 : state_t :=
          array_upd s_1306 (lift_to_both0 (usize 11)) (is_pure ((array_index (
                  s_1306) (lift_to_both0 (usize 11))) .^ (secret (
                  lift_to_both0 (@repr U32 16777216))))) in
        letbm s_1306 loc( s_1306_loc ) :=
          absorb_block (lift_to_both0 msg_block_padded_1300) (
            lift_to_both0 s_1306) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 s_1306,
            lift_to_both0 ciphertext_1299
          ))
        ) : both (CEfset (
          [ciphertext_1299_loc ; msg_block_padded_1300_loc])) [interface
      #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out ;
      #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out ] ((
          state_t '×
          byte_seq
        ))))in
  both_package' _ _ (PROCESS_MSG,(
      process_msg_inp,process_msg_out)) temp_package_both.
Fail Next Obligation.

Definition msg_block_1317_loc : ChoiceEqualityLocation :=
  (block_t ; 1318%nat).
Definition message_1316_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 1319%nat).
Notation "'process_ct_inp'" :=(
  byte_seq '× state_t : choice_type) (in custom pack_type at level 2).
Notation "'process_ct_inp'" :=(
  byte_seq '× state_t : ChoiceEquality) (at level 2).
Notation "'process_ct_out'" :=((state_t '× byte_seq
  ) : choice_type) (in custom pack_type at level 2).
Notation "'process_ct_out'" :=((state_t '× byte_seq
  ) : ChoiceEquality) (at level 2).
Definition PROCESS_CT : nat :=
  1335.
Program Definition process_ct
  : both_package (CEfset ([message_1316_loc ; msg_block_1317_loc])) [interface
  #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out ;
  #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out ] [(
    PROCESS_CT,(process_ct_inp,process_ct_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(ciphertext_1320 , s_1323) := temp_inp : byte_seq '× state_t in
    
    let absorb_block := fun x_0 x_1 => package_both absorb_block (x_0,x_1) in
    let squeeze_block := fun x_0 => package_both squeeze_block (x_0) in
    ((letbm message_1316 : seq uint8 loc( message_1316_loc ) :=
          seq_new_ (default : uint8) (seq_len (
              lift_to_both0 ciphertext_1320)) in
        letb rate_1321 : uint_size := array_length  in
        letb num_chunks_1322 : uint_size :=
          seq_num_exact_chunks (lift_to_both0 ciphertext_1320) (
            lift_to_both0 rate_1321) in
        letb '(s_1323, message_1316) :=
          foldi_both' (lift_to_both0 (usize 0)) (
              lift_to_both0 num_chunks_1322) prod_ce(s_1323, message_1316
            ) (L := (CEfset ([message_1316_loc ; msg_block_1317_loc]))) (I := (
              [interface
              #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out ;
              #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out
              ])) (fun i_1324 '(s_1323, message_1316) =>
            letb key_block_1325 : block_t :=
              squeeze_block (lift_to_both0 s_1323) in
            letb ct_block_1326 : seq uint8 :=
              seq_get_exact_chunk (lift_to_both0 ciphertext_1320) (
                lift_to_both0 rate_1321) (lift_to_both0 i_1324) in
            letb ct_block_1327 : block_t :=
              array_from_seq (16) (lift_to_both0 ct_block_1326) in
            letb msg_block_1328 : block_t :=
              (lift_to_both0 ct_block_1327) array_xor (
                lift_to_both0 key_block_1325) in
            letbm message_1316 loc( message_1316_loc ) :=
              seq_set_exact_chunk (lift_to_both0 message_1316) (
                lift_to_both0 rate_1321) (lift_to_both0 i_1324) (array_to_seq ((
                  lift_to_both0 ct_block_1327) array_xor (
                  lift_to_both0 key_block_1325))) in
            letbm s_1323 loc( s_1323_loc ) :=
              absorb_block (lift_to_both0 msg_block_1328) (
                lift_to_both0 s_1323) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 s_1323,
                lift_to_both0 message_1316
              ))
            ) in
        letb key_block_1329 : block_t := squeeze_block (lift_to_both0 s_1323) in
        letb ct_final_1330 : seq uint8 :=
          seq_get_remainder_chunk (lift_to_both0 ciphertext_1320) (
            lift_to_both0 rate_1321) in
        letb block_len_1331 : uint_size :=
          seq_len (lift_to_both0 ct_final_1330) in
        letb ct_block_padded_1332 : block_t :=
          array_new_ (default : uint8) (16) in
        letb ct_block_padded_1333 : block_t :=
          array_update_start (lift_to_both0 ct_block_padded_1332) (
            lift_to_both0 ct_final_1330) in
        letb msg_block_1334 : block_t :=
          (lift_to_both0 ct_block_padded_1333) array_xor (
            lift_to_both0 key_block_1329) in
        letbm message_1316 loc( message_1316_loc ) :=
          seq_set_chunk (lift_to_both0 message_1316) (lift_to_both0 rate_1321) (
            lift_to_both0 num_chunks_1322) (array_slice_range (
              lift_to_both0 msg_block_1334) (prod_b(
                lift_to_both0 (usize 0),
                lift_to_both0 block_len_1331
              ))) in
        letbm msg_block_1317 : block_t loc( msg_block_1317_loc ) :=
          array_from_slice_range (default : uint8) (16) (
            array_to_seq (lift_to_both0 msg_block_1334)) (prod_b(
              lift_to_both0 (usize 0),
              lift_to_both0 block_len_1331
            )) in
        letb msg_block_1317 : block_t :=
          array_upd msg_block_1317 (lift_to_both0 block_len_1331) (is_pure ((
                array_index (msg_block_1317) (
                  lift_to_both0 block_len_1331)) .^ (secret (lift_to_both0 (
                    @repr U8 1))))) in
        letb s_1323 : state_t :=
          array_upd s_1323 (lift_to_both0 (usize 11)) (is_pure ((array_index (
                  s_1323) (lift_to_both0 (usize 11))) .^ (secret (
                  lift_to_both0 (@repr U32 16777216))))) in
        letbm s_1323 loc( s_1323_loc ) :=
          absorb_block (lift_to_both0 msg_block_1317) (lift_to_both0 s_1323) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 s_1323,
            lift_to_both0 message_1316
          ))
        ) : both (CEfset ([message_1316_loc ; msg_block_1317_loc])) [interface
      #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out ;
      #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out ] ((
          state_t '×
          byte_seq
        ))))in
  both_package' _ _ (PROCESS_CT,(
      process_ct_inp,process_ct_out)) temp_package_both.
Fail Next Obligation.

Definition uints_1336_loc : ChoiceEqualityLocation :=
  (seq uint32 ; 1337%nat).
Notation "'nonce_to_u32s_inp'" :=(
  nonce_t : choice_type) (in custom pack_type at level 2).
Notation "'nonce_to_u32s_inp'" :=(nonce_t : ChoiceEquality) (at level 2).
Notation "'nonce_to_u32s_out'" :=(
  seq uint32 : choice_type) (in custom pack_type at level 2).
Notation "'nonce_to_u32s_out'" :=(seq uint32 : ChoiceEquality) (at level 2).
Definition NONCE_TO_U32S : nat :=
  1339.
Program Definition nonce_to_u32s
  : both_package (CEfset ([uints_1336_loc])) [interface] [(NONCE_TO_U32S,(
      nonce_to_u32s_inp,nonce_to_u32s_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(nonce_1338) := temp_inp : nonce_t in
    
    ((letbm uints_1336 : seq uint32 loc( uints_1336_loc ) :=
          seq_new_ (default : uint32) (lift_to_both0 (usize 4)) in
        letb uints_1336 : seq uint32 :=
          seq_upd uints_1336 (lift_to_both0 (usize 0)) (is_pure (
              uint32_from_le_bytes (array_from_slice_range (default : uint8) (
                  4) (array_to_seq (lift_to_both0 nonce_1338)) (prod_b(
                    lift_to_both0 (usize 0),
                    lift_to_both0 (usize 4)
                  ))))) in
        letb uints_1336 : seq uint32 :=
          seq_upd uints_1336 (lift_to_both0 (usize 1)) (is_pure (
              uint32_from_le_bytes (array_from_slice_range (default : uint8) (
                  4) (array_to_seq (lift_to_both0 nonce_1338)) (prod_b(
                    lift_to_both0 (usize 4),
                    lift_to_both0 (usize 8)
                  ))))) in
        letb uints_1336 : seq uint32 :=
          seq_upd uints_1336 (lift_to_both0 (usize 2)) (is_pure (
              uint32_from_le_bytes (array_from_slice_range (default : uint8) (
                  4) (array_to_seq (lift_to_both0 nonce_1338)) (prod_b(
                    lift_to_both0 (usize 8),
                    lift_to_both0 (usize 12)
                  ))))) in
        letb uints_1336 : seq uint32 :=
          seq_upd uints_1336 (lift_to_both0 (usize 3)) (is_pure (
              uint32_from_le_bytes (array_from_slice_range (default : uint8) (
                  4) (array_to_seq (lift_to_both0 nonce_1338)) (prod_b(
                    lift_to_both0 (usize 12),
                    lift_to_both0 (usize 16)
                  ))))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 uints_1336)
        ) : both (CEfset ([uints_1336_loc])) [interface] (seq uint32)))in
  both_package' _ _ (NONCE_TO_U32S,(
      nonce_to_u32s_inp,nonce_to_u32s_out)) temp_package_both.
Fail Next Obligation.

Definition uints_1340_loc : ChoiceEqualityLocation :=
  (seq uint32 ; 1341%nat).
Notation "'key_to_u32s_inp'" :=(
  key_t : choice_type) (in custom pack_type at level 2).
Notation "'key_to_u32s_inp'" :=(key_t : ChoiceEquality) (at level 2).
Notation "'key_to_u32s_out'" :=(
  seq uint32 : choice_type) (in custom pack_type at level 2).
Notation "'key_to_u32s_out'" :=(seq uint32 : ChoiceEquality) (at level 2).
Definition KEY_TO_U32S : nat :=
  1343.
Program Definition key_to_u32s
  : both_package (CEfset ([uints_1340_loc])) [interface] [(KEY_TO_U32S,(
      key_to_u32s_inp,key_to_u32s_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(key_1342) := temp_inp : key_t in
    
    ((letbm uints_1340 : seq uint32 loc( uints_1340_loc ) :=
          seq_new_ (default : uint32) (lift_to_both0 (usize 8)) in
        letb uints_1340 : seq uint32 :=
          seq_upd uints_1340 (lift_to_both0 (usize 0)) (is_pure (
              uint32_from_le_bytes (array_from_slice_range (default : uint8) (
                  4) (array_to_seq (lift_to_both0 key_1342)) (prod_b(
                    lift_to_both0 (usize 0),
                    lift_to_both0 (usize 4)
                  ))))) in
        letb uints_1340 : seq uint32 :=
          seq_upd uints_1340 (lift_to_both0 (usize 1)) (is_pure (
              uint32_from_le_bytes (array_from_slice_range (default : uint8) (
                  4) (array_to_seq (lift_to_both0 key_1342)) (prod_b(
                    lift_to_both0 (usize 4),
                    lift_to_both0 (usize 8)
                  ))))) in
        letb uints_1340 : seq uint32 :=
          seq_upd uints_1340 (lift_to_both0 (usize 2)) (is_pure (
              uint32_from_le_bytes (array_from_slice_range (default : uint8) (
                  4) (array_to_seq (lift_to_both0 key_1342)) (prod_b(
                    lift_to_both0 (usize 8),
                    lift_to_both0 (usize 12)
                  ))))) in
        letb uints_1340 : seq uint32 :=
          seq_upd uints_1340 (lift_to_both0 (usize 3)) (is_pure (
              uint32_from_le_bytes (array_from_slice_range (default : uint8) (
                  4) (array_to_seq (lift_to_both0 key_1342)) (prod_b(
                    lift_to_both0 (usize 12),
                    lift_to_both0 (usize 16)
                  ))))) in
        letb uints_1340 : seq uint32 :=
          seq_upd uints_1340 (lift_to_both0 (usize 4)) (is_pure (
              uint32_from_le_bytes (array_from_slice_range (default : uint8) (
                  4) (array_to_seq (lift_to_both0 key_1342)) (prod_b(
                    lift_to_both0 (usize 16),
                    lift_to_both0 (usize 20)
                  ))))) in
        letb uints_1340 : seq uint32 :=
          seq_upd uints_1340 (lift_to_both0 (usize 5)) (is_pure (
              uint32_from_le_bytes (array_from_slice_range (default : uint8) (
                  4) (array_to_seq (lift_to_both0 key_1342)) (prod_b(
                    lift_to_both0 (usize 20),
                    lift_to_both0 (usize 24)
                  ))))) in
        letb uints_1340 : seq uint32 :=
          seq_upd uints_1340 (lift_to_both0 (usize 6)) (is_pure (
              uint32_from_le_bytes (array_from_slice_range (default : uint8) (
                  4) (array_to_seq (lift_to_both0 key_1342)) (prod_b(
                    lift_to_both0 (usize 24),
                    lift_to_both0 (usize 28)
                  ))))) in
        letb uints_1340 : seq uint32 :=
          seq_upd uints_1340 (lift_to_both0 (usize 7)) (is_pure (
              uint32_from_le_bytes (array_from_slice_range (default : uint8) (
                  4) (array_to_seq (lift_to_both0 key_1342)) (prod_b(
                    lift_to_both0 (usize 28),
                    lift_to_both0 (usize 32)
                  ))))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 uints_1340)
        ) : both (CEfset ([uints_1340_loc])) [interface] (seq uint32)))in
  both_package' _ _ (KEY_TO_U32S,(
      key_to_u32s_inp,key_to_u32s_out)) temp_package_both.
Fail Next Obligation.


Notation "'gimli_aead_encrypt_inp'" :=(
  byte_seq '× byte_seq '× nonce_t '× key_t : choice_type) (in custom pack_type at level 2).
Notation "'gimli_aead_encrypt_inp'" :=(
  byte_seq '× byte_seq '× nonce_t '× key_t : ChoiceEquality) (at level 2).
Notation "'gimli_aead_encrypt_out'" :=((byte_seq '× tag_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'gimli_aead_encrypt_out'" :=((byte_seq '× tag_t
  ) : ChoiceEquality) (at level 2).
Definition GIMLI_AEAD_ENCRYPT : nat :=
  1355.
Program Definition gimli_aead_encrypt
  : both_package (CEfset ([])) [interface
  #val #[ GIMLI ] : gimli_inp → gimli_out ;
  #val #[ KEY_TO_U32S ] : key_to_u32s_inp → key_to_u32s_out ;
  #val #[ NONCE_TO_U32S ] : nonce_to_u32s_inp → nonce_to_u32s_out ;
  #val #[ PROCESS_AD ] : process_ad_inp → process_ad_out ;
  #val #[ PROCESS_MSG ] : process_msg_inp → process_msg_out ;
  #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out ] [(
    GIMLI_AEAD_ENCRYPT,(gimli_aead_encrypt_inp,gimli_aead_encrypt_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      message_1350 , ad_1348 , nonce_1344 , key_1345) := temp_inp : byte_seq '× byte_seq '× nonce_t '× key_t in
    
    let gimli := fun x_0 => package_both gimli (x_0) in
    let key_to_u32s := fun x_0 => package_both key_to_u32s (x_0) in
    let nonce_to_u32s := fun x_0 => package_both nonce_to_u32s (x_0) in
    let process_ad := fun x_0 x_1 => package_both process_ad (x_0,x_1) in
    let process_msg := fun x_0 x_1 => package_both process_msg (x_0,x_1) in
    let squeeze_block := fun x_0 => package_both squeeze_block (x_0) in
    ((letb s_1346 : state_t :=
          array_from_seq (12) (seq_concat (nonce_to_u32s (
                lift_to_both0 nonce_1344)) (key_to_u32s (
                lift_to_both0 key_1345))) in
        letb s_1347 : state_t := gimli (lift_to_both0 s_1346) in
        letb s_1349 : state_t :=
          process_ad (lift_to_both0 ad_1348) (lift_to_both0 s_1347) in
        letb '(s_1351, ciphertext_1352) : (state_t '× byte_seq) :=
          process_msg (lift_to_both0 message_1350) (lift_to_both0 s_1349) in
        letb tag_1353 : block_t := squeeze_block (lift_to_both0 s_1351) in
        letb tag_1354 : tag_t :=
          array_from_seq (16) (array_to_seq (lift_to_both0 tag_1353)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 ciphertext_1352,
            lift_to_both0 tag_1354
          ))
        ) : both (CEfset ([])) [interface
      #val #[ GIMLI ] : gimli_inp → gimli_out ;
      #val #[ KEY_TO_U32S ] : key_to_u32s_inp → key_to_u32s_out ;
      #val #[ NONCE_TO_U32S ] : nonce_to_u32s_inp → nonce_to_u32s_out ;
      #val #[ PROCESS_AD ] : process_ad_inp → process_ad_out ;
      #val #[ PROCESS_MSG ] : process_msg_inp → process_msg_out ;
      #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out ] ((
          byte_seq '×
          tag_t
        ))))in
  both_package' _ _ (GIMLI_AEAD_ENCRYPT,(
      gimli_aead_encrypt_inp,gimli_aead_encrypt_out)) temp_package_both.
Fail Next Obligation.

Definition out_1356_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 1357%nat).
Notation "'gimli_aead_decrypt_inp'" :=(
  byte_seq '× byte_seq '× tag_t '× nonce_t '× key_t : choice_type) (in custom pack_type at level 2).
Notation "'gimli_aead_decrypt_inp'" :=(
  byte_seq '× byte_seq '× tag_t '× nonce_t '× key_t : ChoiceEquality) (at level 2).
Notation "'gimli_aead_decrypt_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'gimli_aead_decrypt_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition GIMLI_AEAD_DECRYPT : nat :=
  1370.
Program Definition gimli_aead_decrypt
  : both_package (CEfset ([out_1356_loc])) [interface
  #val #[ GIMLI ] : gimli_inp → gimli_out ;
  #val #[ KEY_TO_U32S ] : key_to_u32s_inp → key_to_u32s_out ;
  #val #[ NONCE_TO_U32S ] : nonce_to_u32s_inp → nonce_to_u32s_out ;
  #val #[ PROCESS_AD ] : process_ad_inp → process_ad_out ;
  #val #[ PROCESS_CT ] : process_ct_inp → process_ct_out ;
  #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out ] [(
    GIMLI_AEAD_DECRYPT,(gimli_aead_decrypt_inp,gimli_aead_decrypt_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      ciphertext_1364 , ad_1362 , tag_1369 , nonce_1358 , key_1359) := temp_inp : byte_seq '× byte_seq '× tag_t '× nonce_t '× key_t in
    
    let gimli := fun x_0 => package_both gimli (x_0) in
    let key_to_u32s := fun x_0 => package_both key_to_u32s (x_0) in
    let nonce_to_u32s := fun x_0 => package_both nonce_to_u32s (x_0) in
    let process_ad := fun x_0 x_1 => package_both process_ad (x_0,x_1) in
    let process_ct := fun x_0 x_1 => package_both process_ct (x_0,x_1) in
    let squeeze_block := fun x_0 => package_both squeeze_block (x_0) in
    ((letb s_1360 : state_t :=
          array_from_seq (12) (seq_concat (nonce_to_u32s (
                lift_to_both0 nonce_1358)) (key_to_u32s (
                lift_to_both0 key_1359))) in
        letb s_1361 : state_t := gimli (lift_to_both0 s_1360) in
        letb s_1363 : state_t :=
          process_ad (lift_to_both0 ad_1362) (lift_to_both0 s_1361) in
        letb '(s_1365, message_1366) : (state_t '× byte_seq) :=
          process_ct (lift_to_both0 ciphertext_1364) (lift_to_both0 s_1363) in
        letb my_tag_1367 : block_t := squeeze_block (lift_to_both0 s_1365) in
        letb my_tag_1368 : tag_t :=
          array_from_seq (16) (array_to_seq (lift_to_both0 my_tag_1367)) in
        letbm out_1356 : seq uint8 loc( out_1356_loc ) :=
          seq_new_ (default : uint8) (lift_to_both0 (usize 0)) in
        letb 'out_1356 :=
          if array_equal (lift_to_both0 my_tag_1368) (
            lift_to_both0 tag_1369) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset ([out_1356_loc])) (L2 := CEfset (
            [out_1356_loc])) (I1 := [interface]) (I2 := [interface
          #val #[ GIMLI ] : gimli_inp → gimli_out ;
          #val #[ KEY_TO_U32S ] : key_to_u32s_inp → key_to_u32s_out ;
          #val #[ NONCE_TO_U32S ] : nonce_to_u32s_inp → nonce_to_u32s_out ;
          #val #[ PROCESS_AD ] : process_ad_inp → process_ad_out ;
          #val #[ PROCESS_CT ] : process_ct_inp → process_ct_out ;
          #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm out_1356 loc( out_1356_loc ) := lift_to_both0 message_1366 in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 out_1356)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 out_1356)
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 out_1356)
        ) : both (CEfset ([out_1356_loc])) [interface
      #val #[ GIMLI ] : gimli_inp → gimli_out ;
      #val #[ KEY_TO_U32S ] : key_to_u32s_inp → key_to_u32s_out ;
      #val #[ NONCE_TO_U32S ] : nonce_to_u32s_inp → nonce_to_u32s_out ;
      #val #[ PROCESS_AD ] : process_ad_inp → process_ad_out ;
      #val #[ PROCESS_CT ] : process_ct_inp → process_ct_out ;
      #val #[ SQUEEZE_BLOCK ] : squeeze_block_inp → squeeze_block_out ] (
        byte_seq)))in
  both_package' _ _ (GIMLI_AEAD_DECRYPT,(
      gimli_aead_decrypt_inp,gimli_aead_decrypt_out)) temp_package_both.
Fail Next Obligation.

