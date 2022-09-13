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


Definition poly_key_t := nseq (uint8) (usize 32).

Definition blocksize_v : uint_size :=
  usize 16.

Definition poly_block_t := nseq (uint8) (usize 16).

Definition poly1305_tag_t := nseq (uint8) (usize 16).

Notation "'sub_block_t'" := (byte_seq) : hacspec_scope.

Notation "'block_index_t'" := (uint_size) : hacspec_scope.

Definition field_canvas_t := nseq (int8) (usize 17).
Definition field_element_t := nat_mod 0x03fffffffffffffffffffffffffffffffb.

Notation "'poly_state_t'" := ((
  field_element_t '×
  field_element_t '×
  poly_key_t
)) : hacspec_scope.

Definition poly1305_encode_r_pure (b_1301 : poly_block_t) : field_element_t :=
  let n_1299 : uint128 :=
    uint128_from_le_bytes (array_from_seq (16) (array_to_seq (b_1301))) in 
  let n_1299 :=
    ((n_1299) .& (secret (
          @repr U128 21267647620597763993911028882763415551))) in 
  nat_mod_from_secret_literal (n_1299).
Definition poly1305_encode_r_pure_code
  (b_1301 : poly_block_t)
  : code fset.fset0 [interface] (@ct (field_element_t)) :=
  lift_to_code (poly1305_encode_r_pure b_1301).

Definition n_1299_loc : ChoiceEqualityLocation :=
  ((uint128 ; 1314%nat)).
Notation "'poly1305_encode_r_state_inp'" := (
  poly_block_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_encode_r_state_out'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_ENCODE_R_STATE : nat :=
  (1315).
Program Definition poly1305_encode_r_state
   : package (CEfset ([n_1299_loc])) [interface] [interface
  #val #[ POLY1305_ENCODE_R_STATE ] : poly1305_encode_r_state_inp → poly1305_encode_r_state_out
  ] :=
  (
    [package #def #[ POLY1305_ENCODE_R_STATE ] (temp_inp : poly1305_encode_r_state_inp) : poly1305_encode_r_state_out { 
    let '(b_1301) := temp_inp : poly_block_t in
    ({ code  '(n_1299 : uint128) ←
          ( '(temp_1303 : seq uint8) ←
              (array_to_seq (b_1301)) ;;
             '(temp_1305 : uint128_word_t) ←
              (array_from_seq (16) (temp_1303)) ;;
             '(temp_1307 : int128) ←
              (uint128_from_le_bytes (temp_1305)) ;;
            ret (temp_1307)) ;;
        #put n_1299_loc := n_1299 ;;
       '(n_1299 : uint128) ←
          (( '(temp_1309 : int128) ←
                (secret (@repr U128 21267647620597763993911028882763415551)) ;;
               temp_1311 ←
                ((n_1299) .& (temp_1309)) ;;
              ret (temp_1311))) ;;
        #put n_1299_loc := n_1299 ;;
      
       '(temp_1313 : field_element_t) ←
        (nat_mod_from_secret_literal (n_1299)) ;;
      @ret (field_element_t) (temp_1313) } : code (CEfset (
          [n_1299_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_poly1305_encode_r_state : package _ _ _ :=
  (poly1305_encode_r_state).
Fail Next Obligation.

Notation "'poly1305_encode_r_inp'" :=(
  poly_block_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_encode_r_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_ENCODE_R : nat :=
  (1316).
Program Definition poly1305_encode_r
  (b_1301 : poly_block_t)
  :both (CEfset ([n_1299_loc])) [interface] (field_element_t) :=
  letbm n_1299 : uint128 loc( n_1299_loc ) :=
    uint128_from_le_bytes (array_from_seq (16) (
        array_to_seq (lift_to_both0 b_1301))) in
  letbm n_1299 loc( n_1299_loc ) :=
    (lift_to_both0 n_1299) .& (secret (lift_to_both0 (
          @repr U128 21267647620597763993911028882763415551))) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
    nat_mod_from_secret_literal (lift_to_both0 n_1299))
  .
Fail Next Obligation.

Definition poly1305_encode_block_pure
  (b_1317 : poly_block_t)
  : field_element_t :=
  let n_1318 : uint128 :=
    uint128_from_le_bytes (array_from_seq (16) (array_to_seq (b_1317))) in 
  let f_1319 : field_element_t :=
    nat_mod_from_secret_literal (n_1318) in 
  ((f_1319) +% (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (
        usize 128))).
Definition poly1305_encode_block_pure_code
  (b_1317 : poly_block_t)
  : code fset.fset0 [interface] (@ct (field_element_t)) :=
  lift_to_code (poly1305_encode_block_pure b_1317).


Notation "'poly1305_encode_block_state_inp'" := (
  poly_block_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_encode_block_state_out'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_ENCODE_BLOCK_STATE : nat :=
  (1332).
Program Definition poly1305_encode_block_state
   : package (fset.fset0) [interface] [interface
  #val #[ POLY1305_ENCODE_BLOCK_STATE ] : poly1305_encode_block_state_inp → poly1305_encode_block_state_out
  ] :=
  (
    [package #def #[ POLY1305_ENCODE_BLOCK_STATE ] (temp_inp : poly1305_encode_block_state_inp) : poly1305_encode_block_state_out { 
    let '(b_1317) := temp_inp : poly_block_t in
    ({ code  '(n_1318 : uint128) ←
        ( '(temp_1321 : seq uint8) ←
            (array_to_seq (b_1317)) ;;
           '(temp_1323 : uint128_word_t) ←
            (array_from_seq (16) (temp_1321)) ;;
           '(temp_1325 : int128) ←
            (uint128_from_le_bytes (temp_1323)) ;;
          ret (temp_1325)) ;;
       '(f_1319 : field_element_t) ←
        ( '(temp_1327 : field_element_t) ←
            (nat_mod_from_secret_literal (n_1318)) ;;
          ret (temp_1327)) ;;
       '(temp_1329 : field_element_t) ←
        (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (usize 128)) ;;
       '(temp_1331 : field_element_t) ←
        ((f_1319) +% (temp_1329)) ;;
      @ret (field_element_t) (temp_1331) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_poly1305_encode_block_state : package _ _ _ :=
  (poly1305_encode_block_state).
Fail Next Obligation.

Notation "'poly1305_encode_block_inp'" :=(
  poly_block_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_encode_block_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_ENCODE_BLOCK : nat :=
  (1333).
Program Definition poly1305_encode_block
  (b_1317 : poly_block_t)
  :both (fset.fset0) [interface] (field_element_t) :=
  letb n_1318 : uint128 :=
    uint128_from_le_bytes (array_from_seq (16) (
        array_to_seq (lift_to_both0 b_1317))) in
  letb f_1319 : field_element_t :=
    nat_mod_from_secret_literal (lift_to_both0 n_1318) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((lift_to_both0 f_1319) +% (
      nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (lift_to_both0 (
          usize 128))))
  .
Fail Next Obligation.

Definition poly1305_encode_last_pure
  (pad_len_1334 : block_index_t)
  (b_1335 : sub_block_t)
  : field_element_t :=
  let n_1336 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default : uint8) (16) (b_1335) (
        usize 0) (seq_len (b_1335))) in 
  let f_1337 : field_element_t :=
    nat_mod_from_secret_literal (n_1336) in 
  ((f_1337) +% (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (((
            usize 8) .* (pad_len_1334))))).
Definition poly1305_encode_last_pure_code
  (pad_len_1334 : block_index_t)
  (b_1335 : sub_block_t)
  : code fset.fset0 [interface] (@ct (field_element_t)) :=
  lift_to_code (poly1305_encode_last_pure pad_len_1334 b_1335).


Notation "'poly1305_encode_last_state_inp'" := (
  block_index_t '× sub_block_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_encode_last_state_out'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_ENCODE_LAST_STATE : nat :=
  (1352).
Program Definition poly1305_encode_last_state
   : package (fset.fset0) [interface] [interface
  #val #[ POLY1305_ENCODE_LAST_STATE ] : poly1305_encode_last_state_inp → poly1305_encode_last_state_out
  ] :=
  (
    [package #def #[ POLY1305_ENCODE_LAST_STATE ] (temp_inp : poly1305_encode_last_state_inp) : poly1305_encode_last_state_out { 
    let '(pad_len_1334 , b_1335) := temp_inp : block_index_t '× sub_block_t in
    ({ code  '(n_1336 : uint128) ←
        ( '(temp_1339 : uint_size) ←
            (seq_len (b_1335)) ;;
           '(temp_1341 : uint128_word_t) ←
            (array_from_slice (default : uint8) (16) (b_1335) (usize 0) (
                temp_1339)) ;;
           '(temp_1343 : int128) ←
            (uint128_from_le_bytes (temp_1341)) ;;
          ret (temp_1343)) ;;
       '(f_1337 : field_element_t) ←
        ( '(temp_1345 : field_element_t) ←
            (nat_mod_from_secret_literal (n_1336)) ;;
          ret (temp_1345)) ;;
       '(temp_1347 : uint_size) ←
        ((usize 8) .* (pad_len_1334)) ;;
       '(temp_1349 : field_element_t) ←
        (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (temp_1347)) ;;
       '(temp_1351 : field_element_t) ←
        ((f_1337) +% (temp_1349)) ;;
      @ret (field_element_t) (temp_1351) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_poly1305_encode_last_state : package _ _ _ :=
  (poly1305_encode_last_state).
Fail Next Obligation.

Notation "'poly1305_encode_last_inp'" :=(
  block_index_t '× sub_block_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_encode_last_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_ENCODE_LAST : nat :=
  (1353).
Program Definition poly1305_encode_last
  (pad_len_1334 : block_index_t)
  (b_1335 : sub_block_t)
  :both (fset.fset0) [interface] (field_element_t) :=
  letb n_1336 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default : uint8) (16) (
        lift_to_both0 b_1335) (lift_to_both0 (usize 0)) (seq_len (
          lift_to_both0 b_1335))) in
  letb f_1337 : field_element_t :=
    nat_mod_from_secret_literal (lift_to_both0 n_1336) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((lift_to_both0 f_1337) +% (
      nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) ((lift_to_both0 (
            usize 8)) .* (lift_to_both0 pad_len_1334))))
  .
Fail Next Obligation.

Definition poly1305_init_pure (k_1354 : poly_key_t) : poly_state_t :=
  let r_1355 : field_element_t :=
    poly1305_encode_r (array_from_slice (default : uint8) (16) (
        array_to_seq (k_1354)) (usize 0) (usize 16)) in 
  prod_ce(nat_mod_zero , r_1355, k_1354).
Definition poly1305_init_pure_code
  (k_1354 : poly_key_t)
  : code fset.fset0 [interface] (@ct (poly_state_t)) :=
  lift_to_code (poly1305_init_pure k_1354).


Notation "'poly1305_init_state_inp'" := (
  poly_key_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_init_state_out'" := (
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_INIT_STATE : nat :=
  (1364).
Program Definition poly1305_init_state
   : package (CEfset ([])) [interface
  #val #[ POLY1305_ENCODE_R_STATE ] : poly1305_encode_r_state_inp → poly1305_encode_r_state_out
  ] [interface
  #val #[ POLY1305_INIT_STATE ] : poly1305_init_state_inp → poly1305_init_state_out
  ] :=
  (
    [package #def #[ POLY1305_INIT_STATE ] (temp_inp : poly1305_init_state_inp) : poly1305_init_state_out { 
    let '(k_1354) := temp_inp : poly_key_t in
    #import {sig #[ POLY1305_ENCODE_R_STATE ] : poly1305_encode_r_state_inp → poly1305_encode_r_state_out } as poly1305_encode_r_state ;;
    let poly1305_encode_r_state := fun x_0 => poly1305_encode_r_state (x_0) in
    ({ code  '(r_1355 : field_element_t) ←
        ( '(temp_1357 : seq uint8) ←
            (array_to_seq (k_1354)) ;;
           '(temp_1359 : poly_block_t) ←
            (array_from_slice (default : uint8) (16) (temp_1357) (usize 0) (
                usize 16)) ;;
           temp_1361 ←
            (poly1305_encode_r (temp_1359)) ;;
          ret (temp_1361)) ;;
       '(temp_1363 : field_element_t) ←
        (nat_mod_zero ) ;;
      @ret ((field_element_t '× field_element_t '× poly_key_t)) (prod_ce(
          temp_1363,
          r_1355,
          k_1354
        )) } : code (CEfset ([])) [interface
      #val #[ POLY1305_ENCODE_R_STATE ] : poly1305_encode_r_state_inp → poly1305_encode_r_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_poly1305_init_state : package _ _ _ :=
  (seq_link poly1305_init_state link_rest(package_poly1305_encode_r_state)).
Fail Next Obligation.

Notation "'poly1305_init_inp'" :=(
  poly_key_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_init_out'" :=(
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_INIT : nat :=
  (1365).
Program Definition poly1305_init
  (k_1354 : poly_key_t)
  :both (CEfset ([])) [interface
  #val #[ POLY1305_ENCODE_R ] : poly1305_encode_r_inp → poly1305_encode_r_out
  ] (poly_state_t) :=
  #import {sig #[ POLY1305_ENCODE_R ] : poly1305_encode_r_inp → poly1305_encode_r_out } as poly1305_encode_r ;;
  let poly1305_encode_r := fun x_0 => poly1305_encode_r (x_0) in
  letb r_1355 : field_element_t :=
    poly1305_encode_r (array_from_slice (default : uint8) (16) (
        array_to_seq (lift_to_both0 k_1354)) (lift_to_both0 (usize 0)) (
        lift_to_both0 (usize 16))) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
      nat_mod_zero ,
      lift_to_both0 r_1355,
      lift_to_both0 k_1354
    ))
  .
Fail Next Obligation.

Definition poly1305_update_block_pure
  (b_1366 : poly_block_t)
  (st_1367 : poly_state_t)
  : poly_state_t :=
  let '(acc_1368, r_1369, k_1370) :=
    st_1367 : (field_element_t '× field_element_t '× poly_key_t) in 
  prod_ce(
    ((((poly1305_encode_block (b_1366)) +% (acc_1368))) *% (r_1369)),
    r_1369,
    k_1370
  ).
Definition poly1305_update_block_pure_code
  (b_1366 : poly_block_t)
  (st_1367 : poly_state_t)
  : code fset.fset0 [interface] (@ct (poly_state_t)) :=
  lift_to_code (poly1305_update_block_pure b_1366 st_1367).


Notation "'poly1305_update_block_state_inp'" := (
  poly_block_t '× poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_block_state_out'" := (
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_UPDATE_BLOCK_STATE : nat :=
  (1379).
Program Definition poly1305_update_block_state
   : package (fset.fset0) [interface
  #val #[ POLY1305_ENCODE_BLOCK_STATE ] : poly1305_encode_block_state_inp → poly1305_encode_block_state_out
  ] [interface
  #val #[ POLY1305_UPDATE_BLOCK_STATE ] : poly1305_update_block_state_inp → poly1305_update_block_state_out
  ] :=
  (
    [package #def #[ POLY1305_UPDATE_BLOCK_STATE ] (temp_inp : poly1305_update_block_state_inp) : poly1305_update_block_state_out { 
    let '(b_1366 , st_1367) := temp_inp : poly_block_t '× poly_state_t in
    #import {sig #[ POLY1305_ENCODE_BLOCK_STATE ] : poly1305_encode_block_state_inp → poly1305_encode_block_state_out } as poly1305_encode_block_state ;;
    let poly1305_encode_block_state := fun x_0 => poly1305_encode_block_state (
      x_0) in
    ({ code  temp_1378 ←
        (ret (st_1367)) ;;
      let '(acc_1368, r_1369, k_1370) :=
        (temp_1378) : (field_element_t '× field_element_t '× poly_key_t) in
       temp_1372 ←
        (poly1305_encode_block (b_1366)) ;;
       '(temp_1374 : field_element_t) ←
        ((temp_1372) +% (acc_1368)) ;;
       '(temp_1376 : field_element_t) ←
        ((temp_1374) *% (r_1369)) ;;
      @ret ((field_element_t '× field_element_t '× poly_key_t)) (prod_ce(
          temp_1376,
          r_1369,
          k_1370
        )) } : code (fset.fset0) [interface
      #val #[ POLY1305_ENCODE_BLOCK_STATE ] : poly1305_encode_block_state_inp → poly1305_encode_block_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_poly1305_update_block_state : package _ _ _ :=
  (seq_link poly1305_update_block_state link_rest(
      package_poly1305_encode_block_state)).
Fail Next Obligation.

Notation "'poly1305_update_block_inp'" :=(
  poly_block_t '× poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_block_out'" :=(
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_UPDATE_BLOCK : nat :=
  (1380).
Program Definition poly1305_update_block
  (b_1366 : poly_block_t)
  (st_1367 : poly_state_t)
  :both (fset.fset0) [interface
  #val #[ POLY1305_ENCODE_BLOCK ] : poly1305_encode_block_inp → poly1305_encode_block_out
  ] (poly_state_t) :=
  #import {sig #[ POLY1305_ENCODE_BLOCK ] : poly1305_encode_block_inp → poly1305_encode_block_out } as poly1305_encode_block ;;
  let poly1305_encode_block := fun x_0 => poly1305_encode_block (x_0) in
  letb '(acc_1368, r_1369, k_1370) : (
      field_element_t '×
      field_element_t '×
      poly_key_t
    ) :=
    lift_to_both0 st_1367 in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
      ((poly1305_encode_block (lift_to_both0 b_1366)) +% (
          lift_to_both0 acc_1368)) *% (lift_to_both0 r_1369),
      lift_to_both0 r_1369,
      lift_to_both0 k_1370
    ))
  .
Fail Next Obligation.

Definition poly1305_update_blocks_pure
  (m_1383 : byte_seq)
  (st_1384 : poly_state_t)
  : poly_state_t :=
  let st_1381 : (field_element_t '× field_element_t '× poly_key_t) :=
    st_1384 in 
  let n_blocks_1385 : uint_size :=
    ((seq_len (m_1383)) ./ (blocksize_v)) in 
  let st_1381 :=
    Hacspec_Lib_Pre.foldi (usize 0) (n_blocks_1385) st_1381
      (fun i_1386 st_1381 =>
      let block_1387 : poly_block_t :=
        array_from_seq (16) (seq_get_exact_chunk (m_1383) (blocksize_v) (
            i_1386)) in 
      let st_1381 :=
        poly1305_update_block (block_1387) (st_1381) in 
      (st_1381)) in 
  st_1381.
Definition poly1305_update_blocks_pure_code
  (m_1383 : byte_seq)
  (st_1384 : poly_state_t)
  : code fset.fset0 [interface] (@ct (poly_state_t)) :=
  lift_to_code (poly1305_update_blocks_pure m_1383 st_1384).

Definition st_1381_loc : ChoiceEqualityLocation :=
  (((field_element_t '× field_element_t '× poly_key_t) ; 1398%nat)).
Notation "'poly1305_update_blocks_state_inp'" := (
  byte_seq '× poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_blocks_state_out'" := (
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_UPDATE_BLOCKS_STATE : nat :=
  (1399).
Program Definition poly1305_update_blocks_state
   : package (CEfset ([st_1381_loc])) [interface
  #val #[ POLY1305_UPDATE_BLOCK_STATE ] : poly1305_update_block_state_inp → poly1305_update_block_state_out
  ] [interface
  #val #[ POLY1305_UPDATE_BLOCKS_STATE ] : poly1305_update_blocks_state_inp → poly1305_update_blocks_state_out
  ] :=
  (
    [package #def #[ POLY1305_UPDATE_BLOCKS_STATE ] (temp_inp : poly1305_update_blocks_state_inp) : poly1305_update_blocks_state_out { 
    let '(m_1383 , st_1384) := temp_inp : byte_seq '× poly_state_t in
    #import {sig #[ POLY1305_UPDATE_BLOCK_STATE ] : poly1305_update_block_state_inp → poly1305_update_block_state_out } as poly1305_update_block_state ;;
    let poly1305_update_block_state := fun x_0 x_1 => poly1305_update_block_state (
      x_0,x_1) in
    ({ code  '(st_1381 : (field_element_t '× field_element_t '× poly_key_t
            )) ←
          (ret (st_1384)) ;;
        #put st_1381_loc := st_1381 ;;
       '(n_blocks_1385 : uint_size) ←
        ( '(temp_1389 : uint_size) ←
            (seq_len (m_1383)) ;;
           '(temp_1391 : uint_size) ←
            ((temp_1389) ./ (blocksize_v)) ;;
          ret (temp_1391)) ;;
       '(st_1381 : ((field_element_t '× field_element_t '× poly_key_t))) ←
        (foldi' (usize 0) (n_blocks_1385) st_1381 (L2 := CEfset (
                [st_1381_loc])) (I2 := [interface
              #val #[ POLY1305_UPDATE_BLOCK_STATE ] : poly1305_update_block_state_inp → poly1305_update_block_state_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_1386 st_1381 =>
            ({ code  '(block_1387 : poly_block_t) ←
                ( '(temp_1393 : byte_seq) ←
                    (seq_get_exact_chunk (m_1383) (blocksize_v) (i_1386)) ;;
                   '(temp_1395 : poly_block_t) ←
                    (array_from_seq (16) (temp_1393)) ;;
                  ret (temp_1395)) ;;
               '(st_1381 : (field_element_t '× field_element_t '× poly_key_t
                    )) ←
                  (( temp_1397 ←
                        (poly1305_update_block (block_1387) (st_1381)) ;;
                      ret (temp_1397))) ;;
                #put st_1381_loc := st_1381 ;;
              
              @ret (((field_element_t '× field_element_t '× poly_key_t))) (
                st_1381) } : code (CEfset ([st_1381_loc])) [interface] _))) ;;
      
      @ret ((field_element_t '× field_element_t '× poly_key_t)) (
        st_1381) } : code (CEfset ([st_1381_loc])) [interface
      #val #[ POLY1305_UPDATE_BLOCK_STATE ] : poly1305_update_block_state_inp → poly1305_update_block_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_poly1305_update_blocks_state : package _ _ _ :=
  (seq_link poly1305_update_blocks_state link_rest(
      package_poly1305_update_block_state)).
Fail Next Obligation.

Notation "'poly1305_update_blocks_inp'" :=(
  byte_seq '× poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_blocks_out'" :=(
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_UPDATE_BLOCKS : nat :=
  (1400).
Program Definition poly1305_update_blocks
  (m_1383 : byte_seq)
  (st_1384 : poly_state_t)
  :both (CEfset ([st_1381_loc])) [interface
  #val #[ POLY1305_UPDATE_BLOCK ] : poly1305_update_block_inp → poly1305_update_block_out
  ] (poly_state_t) :=
  #import {sig #[ POLY1305_UPDATE_BLOCK ] : poly1305_update_block_inp → poly1305_update_block_out } as poly1305_update_block ;;
  let poly1305_update_block := fun x_0 x_1 => poly1305_update_block (x_0,x_1) in
  letbm st_1381 : (field_element_t '× field_element_t '× poly_key_t
    ) loc( st_1381_loc ) :=
    lift_to_both0 st_1384 in
  letb n_blocks_1385 : uint_size :=
    (seq_len (lift_to_both0 m_1383)) ./ (lift_to_both0 blocksize_v) in
  letb st_1381 :=
    foldi_both' (lift_to_both0 (usize 0)) (
        lift_to_both0 n_blocks_1385) st_1381 (L := (CEfset (
          [st_1381_loc]))) (I := ([interface
        #val #[ POLY1305_UPDATE_BLOCK ] : poly1305_update_block_inp → poly1305_update_block_out
        ])) (fun i_1386 st_1381 =>
      letb block_1387 : poly_block_t :=
        array_from_seq (16) (seq_get_exact_chunk (lift_to_both0 m_1383) (
            lift_to_both0 blocksize_v) (lift_to_both0 i_1386)) in
      letbm st_1381 loc( st_1381_loc ) :=
        poly1305_update_block (lift_to_both0 block_1387) (
          lift_to_both0 st_1381) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 st_1381)
      ) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 st_1381)
  .
Fail Next Obligation.

Definition poly1305_update_last_pure
  (pad_len_1403 : uint_size)
  (b_1404 : sub_block_t)
  (st_1405 : poly_state_t)
  : poly_state_t :=
  let st_1401 : (field_element_t '× field_element_t '× poly_key_t) :=
    st_1405 in 
  let '(st_1401) :=
    ((if (((seq_len (b_1404)) !=.? (usize 0))):bool_ChoiceEquality
        then (let '(acc_1406, r_1407, k_1408) :=
            st_1401 : (field_element_t '× field_element_t '× poly_key_t) in 
          let st_1401 :=
            prod_ce(
              ((((poly1305_encode_last (pad_len_1403) (b_1404)) +% (
                      acc_1406))) *% (r_1407)),
              r_1407,
              k_1408
            ) in 
          (st_1401))
        else ((st_1401))) : T _) in 
  st_1401.
Definition poly1305_update_last_pure_code
  (pad_len_1403 : uint_size)
  (b_1404 : sub_block_t)
  (st_1405 : poly_state_t)
  : code fset.fset0 [interface] (@ct (poly_state_t)) :=
  lift_to_code (poly1305_update_last_pure pad_len_1403 b_1404 st_1405).

Definition st_1401_loc : ChoiceEqualityLocation :=
  (((field_element_t '× field_element_t '× poly_key_t) ; 1421%nat)).
Notation "'poly1305_update_last_state_inp'" := (
  uint_size '× sub_block_t '× poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_last_state_out'" := (
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_UPDATE_LAST_STATE : nat :=
  (1422).
Program Definition poly1305_update_last_state
   : package (CEfset ([st_1401_loc])) [interface
  #val #[ POLY1305_ENCODE_LAST_STATE ] : poly1305_encode_last_state_inp → poly1305_encode_last_state_out
  ] [interface
  #val #[ POLY1305_UPDATE_LAST_STATE ] : poly1305_update_last_state_inp → poly1305_update_last_state_out
  ] :=
  (
    [package #def #[ POLY1305_UPDATE_LAST_STATE ] (temp_inp : poly1305_update_last_state_inp) : poly1305_update_last_state_out { 
    let '(
      pad_len_1403 , b_1404 , st_1405) := temp_inp : uint_size '× sub_block_t '× poly_state_t in
    #import {sig #[ POLY1305_ENCODE_LAST_STATE ] : poly1305_encode_last_state_inp → poly1305_encode_last_state_out } as poly1305_encode_last_state ;;
    let poly1305_encode_last_state := fun x_0 x_1 => poly1305_encode_last_state (
      x_0,x_1) in
    ({ code  '(st_1401 : (field_element_t '× field_element_t '× poly_key_t
            )) ←
          (ret (st_1405)) ;;
        #put st_1401_loc := st_1401 ;;
       '(temp_1410 : uint_size) ←
        (seq_len (b_1404)) ;;
       '(temp_1412 : bool_ChoiceEquality) ←
        ((temp_1410) !=.? (usize 0)) ;;
       '(st_1401 : ((field_element_t '× field_element_t '× poly_key_t))) ←
        (if temp_1412:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  temp_1420 ←
              (ret (st_1401)) ;;
            let '(acc_1406, r_1407, k_1408) :=
              (temp_1420) : (field_element_t '× field_element_t '× poly_key_t
            ) in
             '(st_1401 : (field_element_t '× field_element_t '× poly_key_t
                  )) ←
                (( temp_1414 ←
                      (poly1305_encode_last (pad_len_1403) (b_1404)) ;;
                     '(temp_1416 : field_element_t) ←
                      ((temp_1414) +% (acc_1406)) ;;
                     '(temp_1418 : field_element_t) ←
                      ((temp_1416) *% (r_1407)) ;;
                    ret (prod_ce(temp_1418, r_1407, k_1408)))) ;;
              #put st_1401_loc := st_1401 ;;
            
            @ret (((field_element_t '× field_element_t '× poly_key_t))) (
              st_1401) in
            ({ code temp_then } : code (CEfset ([st_1401_loc])) [interface] _))
          else @ret (((field_element_t '× field_element_t '× poly_key_t))) (
            st_1401)) ;;
      
      @ret ((field_element_t '× field_element_t '× poly_key_t)) (
        st_1401) } : code (CEfset ([st_1401_loc])) [interface
      #val #[ POLY1305_ENCODE_LAST_STATE ] : poly1305_encode_last_state_inp → poly1305_encode_last_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_poly1305_update_last_state : package _ _ _ :=
  (seq_link poly1305_update_last_state link_rest(
      package_poly1305_encode_last_state)).
Fail Next Obligation.

Notation "'poly1305_update_last_inp'" :=(
  uint_size '× sub_block_t '× poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_last_out'" :=(
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_UPDATE_LAST : nat :=
  (1423).
Program Definition poly1305_update_last
  (pad_len_1403 : uint_size)
  (b_1404 : sub_block_t)
  (st_1405 : poly_state_t)
  :both (CEfset ([st_1401_loc])) [interface
  #val #[ POLY1305_ENCODE_LAST ] : poly1305_encode_last_inp → poly1305_encode_last_out
  ] (poly_state_t) :=
  #import {sig #[ POLY1305_ENCODE_LAST ] : poly1305_encode_last_inp → poly1305_encode_last_out } as poly1305_encode_last ;;
  let poly1305_encode_last := fun x_0 x_1 => poly1305_encode_last (x_0,x_1) in
  letbm st_1401 : (field_element_t '× field_element_t '× poly_key_t
    ) loc( st_1401_loc ) :=
    lift_to_both0 st_1405 in
  letb 'st_1401 :=
    if (seq_len (lift_to_both0 b_1404)) !=.? (lift_to_both0 (
        usize 0)) :bool_ChoiceEquality
    then lift_scope (L1 := CEfset ([st_1401_loc])) (L2 := CEfset (
      [st_1401_loc])) (H_loc_incl := _) (H_opsig_incl := _)a (letb '(
          acc_1406,
          r_1407,
          k_1408
        ) : (field_element_t '× field_element_t '× poly_key_t) :=
        lift_to_both0 st_1401 in
      letbm st_1401 loc( st_1401_loc ) :=
        prod_b(
          ((poly1305_encode_last (lift_to_both0 pad_len_1403) (
                lift_to_both0 b_1404)) +% (lift_to_both0 acc_1406)) *% (
            lift_to_both0 r_1407),
          lift_to_both0 r_1407,
          lift_to_both0 k_1408
        ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 st_1401)
      )
    else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
      lift_to_both0 st_1401)
     in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 st_1401)
  .
Fail Next Obligation.

Definition poly1305_update_pure
  (m_1424 : byte_seq)
  (st_1425 : poly_state_t)
  : poly_state_t :=
  let st_1426 : (field_element_t '× field_element_t '× poly_key_t) :=
    poly1305_update_blocks (m_1424) (st_1425) in 
  let last_1427 : seq uint8 :=
    seq_get_remainder_chunk (m_1424) (blocksize_v) in 
  poly1305_update_last (seq_len (last_1427)) (last_1427) (st_1426).
Definition poly1305_update_pure_code
  (m_1424 : byte_seq)
  (st_1425 : poly_state_t)
  : code fset.fset0 [interface] (@ct (poly_state_t)) :=
  lift_to_code (poly1305_update_pure m_1424 st_1425).


Notation "'poly1305_update_state_inp'" := (
  byte_seq '× poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_state_out'" := (
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_UPDATE_STATE : nat :=
  (1436).
Program Definition poly1305_update_state
   : package (CEfset ([])) [interface
  #val #[ POLY1305_UPDATE_BLOCKS_STATE ] : poly1305_update_blocks_state_inp → poly1305_update_blocks_state_out ;
  #val #[ POLY1305_UPDATE_LAST_STATE ] : poly1305_update_last_state_inp → poly1305_update_last_state_out
  ] [interface
  #val #[ POLY1305_UPDATE_STATE ] : poly1305_update_state_inp → poly1305_update_state_out
  ] :=
  (
    [package #def #[ POLY1305_UPDATE_STATE ] (temp_inp : poly1305_update_state_inp) : poly1305_update_state_out { 
    let '(m_1424 , st_1425) := temp_inp : byte_seq '× poly_state_t in
    #import {sig #[ POLY1305_UPDATE_BLOCKS_STATE ] : poly1305_update_blocks_state_inp → poly1305_update_blocks_state_out } as poly1305_update_blocks_state ;;
    let poly1305_update_blocks_state := fun x_0 x_1 => poly1305_update_blocks_state (
      x_0,x_1) in
    #import {sig #[ POLY1305_UPDATE_LAST_STATE ] : poly1305_update_last_state_inp → poly1305_update_last_state_out } as poly1305_update_last_state ;;
    let poly1305_update_last_state := fun x_0 x_1 x_2 => poly1305_update_last_state (
      x_0,x_1,x_2) in
    ({ code  '(st_1426 : (field_element_t '× field_element_t '× poly_key_t
          )) ←
        ( temp_1429 ←
            (poly1305_update_blocks (m_1424) (st_1425)) ;;
          ret (temp_1429)) ;;
       '(last_1427 : seq uint8) ←
        ( '(temp_1431 : byte_seq) ←
            (seq_get_remainder_chunk (m_1424) (blocksize_v)) ;;
          ret (temp_1431)) ;;
       '(temp_1433 : uint_size) ←
        (seq_len (last_1427)) ;;
       temp_1435 ←
        (poly1305_update_last (temp_1433) (last_1427) (st_1426)) ;;
      @ret (poly_state_t) (temp_1435) } : code (CEfset ([])) [interface
      #val #[ POLY1305_UPDATE_BLOCKS_STATE ] : poly1305_update_blocks_state_inp → poly1305_update_blocks_state_out ;
      #val #[ POLY1305_UPDATE_LAST_STATE ] : poly1305_update_last_state_inp → poly1305_update_last_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_poly1305_update_state : package _ _ _ :=
  (seq_link poly1305_update_state link_rest(
      package_poly1305_update_blocks_state,package_poly1305_update_last_state)).
Fail Next Obligation.

Notation "'poly1305_update_inp'" :=(
  byte_seq '× poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_out'" :=(
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_UPDATE : nat :=
  (1437).
Program Definition poly1305_update
  (m_1424 : byte_seq)
  (st_1425 : poly_state_t)
  :both (CEfset ([])) [interface
  #val #[ POLY1305_UPDATE_BLOCKS ] : poly1305_update_blocks_inp → poly1305_update_blocks_out ;
  #val #[ POLY1305_UPDATE_LAST ] : poly1305_update_last_inp → poly1305_update_last_out
  ] (poly_state_t) :=
  #import {sig #[ POLY1305_UPDATE_BLOCKS ] : poly1305_update_blocks_inp → poly1305_update_blocks_out } as poly1305_update_blocks ;;
  let poly1305_update_blocks := fun x_0 x_1 => poly1305_update_blocks (
    x_0,x_1) in
  #import {sig #[ POLY1305_UPDATE_LAST ] : poly1305_update_last_inp → poly1305_update_last_out } as poly1305_update_last ;;
  let poly1305_update_last := fun x_0 x_1 x_2 => poly1305_update_last (
    x_0,x_1,x_2) in
  letb st_1426 : (field_element_t '× field_element_t '× poly_key_t) :=
    poly1305_update_blocks (lift_to_both0 m_1424) (lift_to_both0 st_1425) in
  letb last_1427 : seq uint8 :=
    seq_get_remainder_chunk (lift_to_both0 m_1424) (
      lift_to_both0 blocksize_v) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (poly1305_update_last (
      seq_len (lift_to_both0 last_1427)) (lift_to_both0 last_1427) (
      lift_to_both0 st_1426))
  .
Fail Next Obligation.

Definition poly1305_finish_pure (st_1438 : poly_state_t) : poly1305_tag_t :=
  let '(acc_1439, _, k_1440) :=
    st_1438 : (field_element_t '× field_element_t '× poly_key_t) in 
  let n_1441 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default : uint8) (16) (
        array_to_seq (k_1440)) (usize 16) (usize 16)) in 
  let aby_1442 : seq uint8 :=
    nat_mod_to_byte_seq_le (acc_1439) in 
  let a_1443 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default : uint8) (16) (aby_1442) (
        usize 0) (usize 16)) in 
  array_from_seq (16) (array_to_seq (uint128_to_le_bytes (((a_1443) .+ (
          n_1441))))).
Definition poly1305_finish_pure_code
  (st_1438 : poly_state_t)
  : code fset.fset0 [interface] (@ct (poly1305_tag_t)) :=
  lift_to_code (poly1305_finish_pure st_1438).


Notation "'poly1305_finish_state_inp'" := (
  poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_finish_state_out'" := (
  poly1305_tag_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_FINISH_STATE : nat :=
  (1466).
Program Definition poly1305_finish_state
   : package (fset.fset0) [interface] [interface
  #val #[ POLY1305_FINISH_STATE ] : poly1305_finish_state_inp → poly1305_finish_state_out
  ] :=
  (
    [package #def #[ POLY1305_FINISH_STATE ] (temp_inp : poly1305_finish_state_inp) : poly1305_finish_state_out { 
    let '(st_1438) := temp_inp : poly_state_t in
    ({ code  temp_1465 ←
        (ret (st_1438)) ;;
      let '(acc_1439, _, k_1440) :=
        (temp_1465) : (field_element_t '× field_element_t '× poly_key_t) in
       '(n_1441 : uint128) ←
        ( '(temp_1445 : seq uint8) ←
            (array_to_seq (k_1440)) ;;
           '(temp_1447 : uint128_word_t) ←
            (array_from_slice (default : uint8) (16) (temp_1445) (usize 16) (
                usize 16)) ;;
           '(temp_1449 : int128) ←
            (uint128_from_le_bytes (temp_1447)) ;;
          ret (temp_1449)) ;;
       '(aby_1442 : seq uint8) ←
        ( temp_1451 ←
            (nat_mod_to_byte_seq_le (acc_1439)) ;;
          ret (temp_1451)) ;;
       '(a_1443 : uint128) ←
        ( '(temp_1453 : uint128_word_t) ←
            (array_from_slice (default : uint8) (16) (aby_1442) (usize 0) (
                usize 16)) ;;
           '(temp_1455 : int128) ←
            (uint128_from_le_bytes (temp_1453)) ;;
          ret (temp_1455)) ;;
       '(temp_1457 : uint128) ←
        ((a_1443) .+ (n_1441)) ;;
       '(temp_1459 : uint128_word_t) ←
        (uint128_to_le_bytes (temp_1457)) ;;
       '(temp_1461 : seq uint8) ←
        (array_to_seq (temp_1459)) ;;
       '(temp_1463 : poly1305_tag_t) ←
        (array_from_seq (16) (temp_1461)) ;;
      @ret (poly1305_tag_t) (temp_1463) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_poly1305_finish_state : package _ _ _ :=
  (poly1305_finish_state).
Fail Next Obligation.

Notation "'poly1305_finish_inp'" :=(
  poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_finish_out'" :=(
  poly1305_tag_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_FINISH : nat :=
  (1467).
Program Definition poly1305_finish
  (st_1438 : poly_state_t)
  :both (fset.fset0) [interface] (poly1305_tag_t) :=
  letb '(acc_1439, _, k_1440) : (
      field_element_t '×
      field_element_t '×
      poly_key_t
    ) :=
    lift_to_both0 st_1438 in
  letb n_1441 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default : uint8) (16) (
        array_to_seq (lift_to_both0 k_1440)) (lift_to_both0 (usize 16)) (
        lift_to_both0 (usize 16))) in
  letb aby_1442 : seq uint8 :=
    nat_mod_to_byte_seq_le (lift_to_both0 acc_1439) in
  letb a_1443 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default : uint8) (16) (
        lift_to_both0 aby_1442) (lift_to_both0 (usize 0)) (lift_to_both0 (
          usize 16))) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (16) (
      array_to_seq (uint128_to_le_bytes ((lift_to_both0 a_1443) .+ (
          lift_to_both0 n_1441)))))
  .
Fail Next Obligation.

Definition poly1305_pure
  (m_1470 : byte_seq)
  (key_1471 : poly_key_t)
  : poly1305_tag_t :=
  let st_1468 : (field_element_t '× field_element_t '× poly_key_t) :=
    poly1305_init (key_1471) in 
  let st_1468 :=
    poly1305_update (m_1470) (st_1468) in 
  poly1305_finish (st_1468).
Definition poly1305_pure_code
  (m_1470 : byte_seq)
  (key_1471 : poly_key_t)
  : code fset.fset0 [interface] (@ct (poly1305_tag_t)) :=
  lift_to_code (poly1305_pure m_1470 key_1471).

Definition st_1468_loc : ChoiceEqualityLocation :=
  (((field_element_t '× field_element_t '× poly_key_t) ; 1478%nat)).
Notation "'poly1305_state_inp'" := (
  byte_seq '× poly_key_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_state_out'" := (
  poly1305_tag_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_STATE : nat :=
  (1479).
Program Definition poly1305_state
   : package (CEfset ([st_1468_loc])) [interface
  #val #[ POLY1305_FINISH_STATE ] : poly1305_finish_state_inp → poly1305_finish_state_out ;
  #val #[ POLY1305_INIT_STATE ] : poly1305_init_state_inp → poly1305_init_state_out ;
  #val #[ POLY1305_UPDATE_STATE ] : poly1305_update_state_inp → poly1305_update_state_out
  ] [interface
  #val #[ POLY1305_STATE ] : poly1305_state_inp → poly1305_state_out ] :=
  (
    [package #def #[ POLY1305_STATE ] (temp_inp : poly1305_state_inp) : poly1305_state_out { 
    let '(m_1470 , key_1471) := temp_inp : byte_seq '× poly_key_t in
    #import {sig #[ POLY1305_FINISH_STATE ] : poly1305_finish_state_inp → poly1305_finish_state_out } as poly1305_finish_state ;;
    let poly1305_finish_state := fun x_0 => poly1305_finish_state (x_0) in
    #import {sig #[ POLY1305_INIT_STATE ] : poly1305_init_state_inp → poly1305_init_state_out } as poly1305_init_state ;;
    let poly1305_init_state := fun x_0 => poly1305_init_state (x_0) in
    #import {sig #[ POLY1305_UPDATE_STATE ] : poly1305_update_state_inp → poly1305_update_state_out } as poly1305_update_state ;;
    let poly1305_update_state := fun x_0 x_1 => poly1305_update_state (
      x_0,x_1) in
    ({ code  '(st_1468 : (field_element_t '× field_element_t '× poly_key_t
            )) ←
          ( temp_1473 ←
              (poly1305_init (key_1471)) ;;
            ret (temp_1473)) ;;
        #put st_1468_loc := st_1468 ;;
       '(st_1468 : (field_element_t '× field_element_t '× poly_key_t)) ←
          (( temp_1475 ←
                (poly1305_update (m_1470) (st_1468)) ;;
              ret (temp_1475))) ;;
        #put st_1468_loc := st_1468 ;;
      
       temp_1477 ←
        (poly1305_finish (st_1468)) ;;
      @ret (poly1305_tag_t) (temp_1477) } : code (CEfset (
          [st_1468_loc])) [interface
      #val #[ POLY1305_FINISH_STATE ] : poly1305_finish_state_inp → poly1305_finish_state_out ;
      #val #[ POLY1305_INIT_STATE ] : poly1305_init_state_inp → poly1305_init_state_out ;
      #val #[ POLY1305_UPDATE_STATE ] : poly1305_update_state_inp → poly1305_update_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_poly1305_state : package _ _ _ :=
  (seq_link poly1305_state link_rest(
      package_poly1305_finish_state,package_poly1305_init_state,package_poly1305_update_state)).
Fail Next Obligation.

Notation "'poly1305_inp'" :=(
  byte_seq '× poly_key_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_out'" :=(
  poly1305_tag_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305 : nat :=
  (1480).
Program Definition poly1305
  (m_1470 : byte_seq)
  (key_1471 : poly_key_t)
  :both (CEfset ([st_1468_loc])) [interface
  #val #[ POLY1305_FINISH ] : poly1305_finish_inp → poly1305_finish_out ;
  #val #[ POLY1305_INIT ] : poly1305_init_inp → poly1305_init_out ;
  #val #[ POLY1305_UPDATE ] : poly1305_update_inp → poly1305_update_out ] (
    poly1305_tag_t) :=
  #import {sig #[ POLY1305_FINISH ] : poly1305_finish_inp → poly1305_finish_out } as poly1305_finish ;;
  let poly1305_finish := fun x_0 => poly1305_finish (x_0) in
  #import {sig #[ POLY1305_INIT ] : poly1305_init_inp → poly1305_init_out } as poly1305_init ;;
  let poly1305_init := fun x_0 => poly1305_init (x_0) in
  #import {sig #[ POLY1305_UPDATE ] : poly1305_update_inp → poly1305_update_out } as poly1305_update ;;
  let poly1305_update := fun x_0 x_1 => poly1305_update (x_0,x_1) in
  letbm st_1468 : (field_element_t '× field_element_t '× poly_key_t
    ) loc( st_1468_loc ) :=
    poly1305_init (lift_to_both0 key_1471) in
  letbm st_1468 loc( st_1468_loc ) :=
    poly1305_update (lift_to_both0 m_1470) (lift_to_both0 st_1468) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (poly1305_finish (
      lift_to_both0 st_1468))
  .
Fail Next Obligation.

