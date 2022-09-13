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


Require Import Hacspec_Chacha20.

Require Import Hacspec_Poly1305.

Inductive error_t :=
| InvalidTag : error_t.

Notation "'cha_cha_poly_key_t'" := (cha_cha_key_t) : hacspec_scope.

Notation "'cha_cha_poly_iv_t'" := (cha_cha_iv_t) : hacspec_scope.

Notation "'byte_seq_result_t'" := ((result error_t byte_seq)) : hacspec_scope.

Definition init_pure
  (key_1190 : cha_cha_poly_key_t)
  (iv_1191 : cha_cha_poly_iv_t)
  : poly_state_t :=
  let key_block0_1192 : block_t :=
    chacha20_key_block0 (key_1190) (iv_1191) in 
  let poly_key_1193 : poly_key_t :=
    array_from_slice (default : uint8) (32) (array_to_seq (key_block0_1192)) (
      usize 0) (usize 32) in 
  poly1305_init (poly_key_1193).
Definition init_pure_code
  (key_1190 : cha_cha_poly_key_t)
  (iv_1191 : cha_cha_poly_iv_t)
  : code fset.fset0 [interface] (@ct (poly_state_t)) :=
  lift_to_code (init_pure key_1190 iv_1191).


Notation "'init_state_inp'" := (
  cha_cha_poly_key_t '× cha_cha_poly_iv_t : choice_type) (in custom pack_type at level 2).
Notation "'init_state_out'" := (
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition INIT_STATE : nat :=
  (1202).
Program Definition init_state
   : package (fset.fset0) [interface] [interface
  #val #[ INIT_STATE ] : init_state_inp → init_state_out ] :=
  ([package #def #[ INIT_STATE ] (temp_inp : init_state_inp) : init_state_out { 
    let '(
      key_1190 , iv_1191) := temp_inp : cha_cha_poly_key_t '× cha_cha_poly_iv_t in
    ({ code  '(key_block0_1192 : block_t) ←
        ( temp_1195 ←
            (chacha20_key_block0 (key_1190) (iv_1191)) ;;
          ret (temp_1195)) ;;
       '(poly_key_1193 : poly_key_t) ←
        ( '(temp_1197 : seq uint8) ←
            (array_to_seq (key_block0_1192)) ;;
           '(temp_1199 : poly_key_t) ←
            (array_from_slice (default : uint8) (32) (temp_1197) (usize 0) (
                usize 32)) ;;
          ret (temp_1199)) ;;
       temp_1201 ←
        (poly1305_init (poly_key_1193)) ;;
      @ret ((field_element_t '× field_element_t '× poly_key_t)) (
        temp_1201) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_init_state : package _ _ _ :=
  (init_state).
Fail Next Obligation.

Notation "'init_inp'" :=(
  cha_cha_poly_key_t '× cha_cha_poly_iv_t : choice_type) (in custom pack_type at level 2).
Notation "'init_out'" :=(
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition INIT : nat :=
  (1203).
Program Definition init
  (key_1190 : cha_cha_poly_key_t)
  (iv_1191 : cha_cha_poly_iv_t)
  :both (fset.fset0) [interface
  #val #[ CHACHA20_KEY_BLOCK0 ] : chacha20_key_block0_inp → chacha20_key_block0_out ;
  #val #[ POLY1305_INIT ] : poly1305_init_inp → poly1305_init_out ] (
    poly_state_t) :=
  #import {sig #[ CHACHA20_KEY_BLOCK0 ] : chacha20_key_block0_inp → chacha20_key_block0_out } as chacha20_key_block0 ;;
  let chacha20_key_block0 := fun x_0 x_1 => chacha20_key_block0 (x_0,x_1) in
  #import {sig #[ POLY1305_INIT ] : poly1305_init_inp → poly1305_init_out } as poly1305_init ;;
  let poly1305_init := fun x_0 => poly1305_init (x_0) in
  letb key_block0_1192 : block_t :=
    chacha20_key_block0 (lift_to_both0 key_1190) (lift_to_both0 iv_1191) in
  letb poly_key_1193 : poly_key_t :=
    array_from_slice (default : uint8) (32) (
      array_to_seq (lift_to_both0 key_block0_1192)) (lift_to_both0 (usize 0)) (
      lift_to_both0 (usize 32)) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (poly1305_init (
      lift_to_both0 poly_key_1193))
  .
Fail Next Obligation.

Definition poly1305_update_padded_pure
  (m_1204 : byte_seq)
  (st_1205 : poly_state_t)
  : poly_state_t :=
  let st_1206 : (field_element_t '× field_element_t '× poly_key_t) :=
    poly1305_update_blocks (m_1204) (st_1205) in 
  let last_1207 : seq uint8 :=
    seq_get_remainder_chunk (m_1204) (usize 16) in 
  poly1305_update_last (usize 16) (last_1207) (st_1206).
Definition poly1305_update_padded_pure_code
  (m_1204 : byte_seq)
  (st_1205 : poly_state_t)
  : code fset.fset0 [interface] (@ct (poly_state_t)) :=
  lift_to_code (poly1305_update_padded_pure m_1204 st_1205).


Notation "'poly1305_update_padded_state_inp'" := (
  byte_seq '× poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_padded_state_out'" := (
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_UPDATE_PADDED_STATE : nat :=
  (1214).
Program Definition poly1305_update_padded_state
   : package (fset.fset0) [interface] [interface
  #val #[ POLY1305_UPDATE_PADDED_STATE ] : poly1305_update_padded_state_inp → poly1305_update_padded_state_out
  ] :=
  (
    [package #def #[ POLY1305_UPDATE_PADDED_STATE ] (temp_inp : poly1305_update_padded_state_inp) : poly1305_update_padded_state_out { 
    let '(m_1204 , st_1205) := temp_inp : byte_seq '× poly_state_t in
    ({ code  '(st_1206 : (field_element_t '× field_element_t '× poly_key_t
          )) ←
        ( temp_1209 ←
            (poly1305_update_blocks (m_1204) (st_1205)) ;;
          ret (temp_1209)) ;;
       '(last_1207 : seq uint8) ←
        ( '(temp_1211 : byte_seq) ←
            (seq_get_remainder_chunk (m_1204) (usize 16)) ;;
          ret (temp_1211)) ;;
       temp_1213 ←
        (poly1305_update_last (usize 16) (last_1207) (st_1206)) ;;
      @ret ((field_element_t '× field_element_t '× poly_key_t)) (
        temp_1213) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_poly1305_update_padded_state : package _ _ _ :=
  (poly1305_update_padded_state).
Fail Next Obligation.

Notation "'poly1305_update_padded_inp'" :=(
  byte_seq '× poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_padded_out'" :=(
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_UPDATE_PADDED : nat :=
  (1215).
Program Definition poly1305_update_padded
  (m_1204 : byte_seq)
  (st_1205 : poly_state_t)
  :both (fset.fset0) [interface
  #val #[ POLY1305_UPDATE_BLOCKS ] : poly1305_update_blocks_inp → poly1305_update_blocks_out ;
  #val #[ POLY1305_UPDATE_LAST ] : poly1305_update_last_inp → poly1305_update_last_out
  ] (poly_state_t) :=
  #import {sig #[ POLY1305_UPDATE_BLOCKS ] : poly1305_update_blocks_inp → poly1305_update_blocks_out } as poly1305_update_blocks ;;
  let poly1305_update_blocks := fun x_0 x_1 => poly1305_update_blocks (
    x_0,x_1) in
  #import {sig #[ POLY1305_UPDATE_LAST ] : poly1305_update_last_inp → poly1305_update_last_out } as poly1305_update_last ;;
  let poly1305_update_last := fun x_0 x_1 x_2 => poly1305_update_last (
    x_0,x_1,x_2) in
  letb st_1206 : (field_element_t '× field_element_t '× poly_key_t) :=
    poly1305_update_blocks (lift_to_both0 m_1204) (lift_to_both0 st_1205) in
  letb last_1207 : seq uint8 :=
    seq_get_remainder_chunk (lift_to_both0 m_1204) (lift_to_both0 (usize 16)) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (poly1305_update_last (
      lift_to_both0 (usize 16)) (lift_to_both0 last_1207) (
      lift_to_both0 st_1206))
  .
Fail Next Obligation.

Definition finish_pure
  (aad_len_1218 : uint_size)
  (cipher_len_1219 : uint_size)
  (st_1220 : poly_state_t)
  : poly1305_tag_t :=
  let last_block_1216 : poly_block_t :=
    array_new_ (default : uint8) (16) in 
  let last_block_1216 :=
    array_update (last_block_1216) (usize 0) (array_to_seq (uint64_to_le_bytes (
        secret (pub_u64 (aad_len_1218))))) in 
  let last_block_1216 :=
    array_update (last_block_1216) (usize 8) (array_to_seq (uint64_to_le_bytes (
        secret (pub_u64 (cipher_len_1219))))) in 
  let st_1221 : (field_element_t '× field_element_t '× poly_key_t) :=
    poly1305_update_block (last_block_1216) (st_1220) in 
  poly1305_finish (st_1221).
Definition finish_pure_code
  (aad_len_1218 : uint_size)
  (cipher_len_1219 : uint_size)
  (st_1220 : poly_state_t)
  : code fset.fset0 [interface] (@ct (poly1305_tag_t)) :=
  lift_to_code (finish_pure aad_len_1218 cipher_len_1219 st_1220).

Definition last_block_1216_loc : ChoiceEqualityLocation :=
  ((poly_block_t ; 1244%nat)).
Notation "'finish_state_inp'" := (
  uint_size '× uint_size '× poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'finish_state_out'" := (
  poly1305_tag_t : choice_type) (in custom pack_type at level 2).
Definition FINISH_STATE : nat :=
  (1245).
Program Definition finish_state
   : package (CEfset ([last_block_1216_loc])) [interface] [interface
  #val #[ FINISH_STATE ] : finish_state_inp → finish_state_out ] :=
  (
    [package #def #[ FINISH_STATE ] (temp_inp : finish_state_inp) : finish_state_out { 
    let '(
      aad_len_1218 , cipher_len_1219 , st_1220) := temp_inp : uint_size '× uint_size '× poly_state_t in
    ({ code  '(last_block_1216 : poly_block_t) ←
          ( '(temp_1223 : poly_block_t) ←
              (array_new_ (default : uint8) (16)) ;;
            ret (temp_1223)) ;;
        #put last_block_1216_loc := last_block_1216 ;;
       '(last_block_1216 : poly_block_t) ←
          (( '(temp_1225 : int64) ←
                (secret (pub_u64 (aad_len_1218))) ;;
               '(temp_1227 : uint64_word_t) ←
                (uint64_to_le_bytes (temp_1225)) ;;
               '(temp_1229 : seq uint8) ←
                (array_to_seq (temp_1227)) ;;
               '(temp_1231 : poly_block_t) ←
                (array_update (last_block_1216) (usize 0) (temp_1229)) ;;
              ret (temp_1231))) ;;
        #put last_block_1216_loc := last_block_1216 ;;
      
       '(last_block_1216 : poly_block_t) ←
          (( '(temp_1233 : int64) ←
                (secret (pub_u64 (cipher_len_1219))) ;;
               '(temp_1235 : uint64_word_t) ←
                (uint64_to_le_bytes (temp_1233)) ;;
               '(temp_1237 : seq uint8) ←
                (array_to_seq (temp_1235)) ;;
               '(temp_1239 : poly_block_t) ←
                (array_update (last_block_1216) (usize 8) (temp_1237)) ;;
              ret (temp_1239))) ;;
        #put last_block_1216_loc := last_block_1216 ;;
      
       '(st_1221 : (field_element_t '× field_element_t '× poly_key_t)) ←
        ( temp_1241 ←
            (poly1305_update_block (last_block_1216) (st_1220)) ;;
          ret (temp_1241)) ;;
       temp_1243 ←
        (poly1305_finish (st_1221)) ;;
      @ret (poly1305_tag_t) (temp_1243) } : code (CEfset (
          [last_block_1216_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_finish_state : package _ _ _ :=
  (finish_state).
Fail Next Obligation.

Notation "'finish_inp'" :=(
  uint_size '× uint_size '× poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'finish_out'" :=(
  poly1305_tag_t : choice_type) (in custom pack_type at level 2).
Definition FINISH : nat :=
  (1246).
Program Definition finish
  (aad_len_1218 : uint_size)
  (cipher_len_1219 : uint_size)
  (st_1220 : poly_state_t)
  :both (CEfset ([last_block_1216_loc])) [interface
  #val #[ POLY1305_FINISH ] : poly1305_finish_inp → poly1305_finish_out ;
  #val #[ POLY1305_UPDATE_BLOCK ] : poly1305_update_block_inp → poly1305_update_block_out
  ] (poly1305_tag_t) :=
  #import {sig #[ POLY1305_FINISH ] : poly1305_finish_inp → poly1305_finish_out } as poly1305_finish ;;
  let poly1305_finish := fun x_0 => poly1305_finish (x_0) in
  #import {sig #[ POLY1305_UPDATE_BLOCK ] : poly1305_update_block_inp → poly1305_update_block_out } as poly1305_update_block ;;
  let poly1305_update_block := fun x_0 x_1 => poly1305_update_block (x_0,x_1) in
  letbm last_block_1216 : poly_block_t loc( last_block_1216_loc ) :=
    array_new_ (default : uint8) (16) in
  letbm last_block_1216 loc( last_block_1216_loc ) :=
    array_update (lift_to_both0 last_block_1216) (lift_to_both0 (usize 0)) (
      array_to_seq (uint64_to_le_bytes (secret (pub_u64 (is_pure (
              lift_to_both0 aad_len_1218)))))) in
  letbm last_block_1216 loc( last_block_1216_loc ) :=
    array_update (lift_to_both0 last_block_1216) (lift_to_both0 (usize 8)) (
      array_to_seq (uint64_to_le_bytes (secret (pub_u64 (is_pure (
              lift_to_both0 cipher_len_1219)))))) in
  letb st_1221 : (field_element_t '× field_element_t '× poly_key_t) :=
    poly1305_update_block (lift_to_both0 last_block_1216) (
      lift_to_both0 st_1220) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (poly1305_finish (
      lift_to_both0 st_1221))
  .
Fail Next Obligation.

Definition chacha20_poly1305_encrypt_pure
  (key_1249 : cha_cha_poly_key_t)
  (iv_1250 : cha_cha_poly_iv_t)
  (aad_1251 : byte_seq)
  (msg_1252 : byte_seq)
  : (byte_seq '× poly1305_tag_t) :=
  let cipher_text_1253 : seq uint8 :=
    chacha20 (key_1249) (iv_1250) (@repr U32 1) (msg_1252) in 
  let poly_st_1247 : (field_element_t '× field_element_t '× poly_key_t) :=
    init (key_1249) (iv_1250) in 
  let poly_st_1247 :=
    poly1305_update_padded (aad_1251) (poly_st_1247) in 
  let poly_st_1247 :=
    poly1305_update_padded (cipher_text_1253) (poly_st_1247) in 
  let tag_1254 : poly1305_tag_t :=
    finish (seq_len (aad_1251)) (seq_len (cipher_text_1253)) (poly_st_1247) in 
  prod_ce(cipher_text_1253, tag_1254).
Definition chacha20_poly1305_encrypt_pure_code
  (key_1249 : cha_cha_poly_key_t)
  (iv_1250 : cha_cha_poly_iv_t)
  (aad_1251 : byte_seq)
  (msg_1252 : byte_seq)
  : code fset.fset0 [interface] (@ct ((byte_seq '× poly1305_tag_t))) :=
  lift_to_code (chacha20_poly1305_encrypt_pure key_1249
    iv_1250
    aad_1251
    msg_1252).

Definition poly_st_1247_loc : ChoiceEqualityLocation :=
  (((field_element_t '× field_element_t '× poly_key_t) ; 1269%nat)).
Notation "'chacha20_poly1305_encrypt_state_inp'" := (
  cha_cha_poly_key_t '× cha_cha_poly_iv_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_poly1305_encrypt_state_out'" := ((
    byte_seq '×
    poly1305_tag_t
  ) : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_POLY1305_ENCRYPT_STATE : nat :=
  (1270).
Program Definition chacha20_poly1305_encrypt_state
   : package (CEfset ([poly_st_1247_loc])) [interface
  #val #[ FINISH_STATE ] : finish_state_inp → finish_state_out ;
  #val #[ INIT_STATE ] : init_state_inp → init_state_out ;
  #val #[ POLY1305_UPDATE_PADDED_STATE ] : poly1305_update_padded_state_inp → poly1305_update_padded_state_out
  ] [interface
  #val #[ CHACHA20_POLY1305_ENCRYPT_STATE ] : chacha20_poly1305_encrypt_state_inp → chacha20_poly1305_encrypt_state_out
  ] :=
  (
    [package #def #[ CHACHA20_POLY1305_ENCRYPT_STATE ] (temp_inp : chacha20_poly1305_encrypt_state_inp) : chacha20_poly1305_encrypt_state_out { 
    let '(
      key_1249 , iv_1250 , aad_1251 , msg_1252) := temp_inp : cha_cha_poly_key_t '× cha_cha_poly_iv_t '× byte_seq '× byte_seq in
    #import {sig #[ FINISH_STATE ] : finish_state_inp → finish_state_out } as finish_state ;;
    let finish_state := fun x_0 x_1 x_2 => finish_state (x_0,x_1,x_2) in
    #import {sig #[ INIT_STATE ] : init_state_inp → init_state_out } as init_state ;;
    let init_state := fun x_0 x_1 => init_state (x_0,x_1) in
    #import {sig #[ POLY1305_UPDATE_PADDED_STATE ] : poly1305_update_padded_state_inp → poly1305_update_padded_state_out } as poly1305_update_padded_state ;;
    let poly1305_update_padded_state := fun x_0 x_1 => poly1305_update_padded_state (
      x_0,x_1) in
    ({ code  '(cipher_text_1253 : seq uint8) ←
        ( temp_1256 ←
            (chacha20 (key_1249) (iv_1250) (@repr U32 1) (msg_1252)) ;;
          ret (temp_1256)) ;;
       '(poly_st_1247 : (field_element_t '× field_element_t '× poly_key_t
            )) ←
          ( temp_1258 ←
              (init (key_1249) (iv_1250)) ;;
            ret (temp_1258)) ;;
        #put poly_st_1247_loc := poly_st_1247 ;;
       '(poly_st_1247 : (field_element_t '× field_element_t '× poly_key_t
            )) ←
          (( temp_1260 ←
                (poly1305_update_padded (aad_1251) (poly_st_1247)) ;;
              ret (temp_1260))) ;;
        #put poly_st_1247_loc := poly_st_1247 ;;
      
       '(poly_st_1247 : (field_element_t '× field_element_t '× poly_key_t
            )) ←
          (( temp_1262 ←
                (poly1305_update_padded (cipher_text_1253) (poly_st_1247)) ;;
              ret (temp_1262))) ;;
        #put poly_st_1247_loc := poly_st_1247 ;;
      
       '(tag_1254 : poly1305_tag_t) ←
        ( '(temp_1264 : uint_size) ←
            (seq_len (aad_1251)) ;;
           '(temp_1266 : uint_size) ←
            (seq_len (cipher_text_1253)) ;;
           temp_1268 ←
            (finish (temp_1264) (temp_1266) (poly_st_1247)) ;;
          ret (temp_1268)) ;;
      @ret ((seq uint8 '× poly1305_tag_t)) (prod_ce(cipher_text_1253, tag_1254
        )) } : code (CEfset ([poly_st_1247_loc])) [interface
      #val #[ FINISH_STATE ] : finish_state_inp → finish_state_out ;
      #val #[ INIT_STATE ] : init_state_inp → init_state_out ;
      #val #[ POLY1305_UPDATE_PADDED_STATE ] : poly1305_update_padded_state_inp → poly1305_update_padded_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_chacha20_poly1305_encrypt_state : package _ _ _ :=
  (seq_link chacha20_poly1305_encrypt_state link_rest(
      package_finish_state,package_init_state,package_poly1305_update_padded_state)).
Fail Next Obligation.

Notation "'chacha20_poly1305_encrypt_inp'" :=(
  cha_cha_poly_key_t '× cha_cha_poly_iv_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_poly1305_encrypt_out'" :=((byte_seq '× poly1305_tag_t
  ) : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_POLY1305_ENCRYPT : nat :=
  (1271).
Program Definition chacha20_poly1305_encrypt
  (key_1249 : cha_cha_poly_key_t)
  (iv_1250 : cha_cha_poly_iv_t)
  (aad_1251 : byte_seq)
  (msg_1252 : byte_seq)
  :both (CEfset ([poly_st_1247_loc])) [interface
  #val #[ CHACHA20 ] : chacha20_inp → chacha20_out ;
  #val #[ FINISH ] : finish_inp → finish_out ;
  #val #[ INIT ] : init_inp → init_out ;
  #val #[ POLY1305_UPDATE_PADDED ] : poly1305_update_padded_inp → poly1305_update_padded_out
  ] ((byte_seq '× poly1305_tag_t)) :=
  #import {sig #[ CHACHA20 ] : chacha20_inp → chacha20_out } as chacha20 ;;
  let chacha20 := fun x_0 x_1 x_2 x_3 => chacha20 (x_0,x_1,x_2,x_3) in
  #import {sig #[ FINISH ] : finish_inp → finish_out } as finish ;;
  let finish := fun x_0 x_1 x_2 => finish (x_0,x_1,x_2) in
  #import {sig #[ INIT ] : init_inp → init_out } as init ;;
  let init := fun x_0 x_1 => init (x_0,x_1) in
  #import {sig #[ POLY1305_UPDATE_PADDED ] : poly1305_update_padded_inp → poly1305_update_padded_out } as poly1305_update_padded ;;
  let poly1305_update_padded := fun x_0 x_1 => poly1305_update_padded (
    x_0,x_1) in
  letb cipher_text_1253 : seq uint8 :=
    chacha20 (lift_to_both0 key_1249) (lift_to_both0 iv_1250) (lift_to_both0 (
        @repr U32 1)) (lift_to_both0 msg_1252) in
  letbm poly_st_1247 : (field_element_t '× field_element_t '× poly_key_t
    ) loc( poly_st_1247_loc ) :=
    init (lift_to_both0 key_1249) (lift_to_both0 iv_1250) in
  letbm poly_st_1247 loc( poly_st_1247_loc ) :=
    poly1305_update_padded (lift_to_both0 aad_1251) (
      lift_to_both0 poly_st_1247) in
  letbm poly_st_1247 loc( poly_st_1247_loc ) :=
    poly1305_update_padded (lift_to_both0 cipher_text_1253) (
      lift_to_both0 poly_st_1247) in
  letb tag_1254 : poly1305_tag_t :=
    finish (seq_len (lift_to_both0 aad_1251)) (seq_len (
        lift_to_both0 cipher_text_1253)) (lift_to_both0 poly_st_1247) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
      lift_to_both0 cipher_text_1253,
      lift_to_both0 tag_1254
    ))
  .
Fail Next Obligation.

Definition chacha20_poly1305_decrypt_pure
  (key_1274 : cha_cha_poly_key_t)
  (iv_1275 : cha_cha_poly_iv_t)
  (aad_1276 : byte_seq)
  (cipher_text_1277 : byte_seq)
  (tag_1278 : poly1305_tag_t)
  : byte_seq_result_t :=
  let poly_st_1272 : (field_element_t '× field_element_t '× poly_key_t) :=
    init (key_1274) (iv_1275) in 
  let poly_st_1272 :=
    poly1305_update_padded (aad_1276) (poly_st_1272) in 
  let poly_st_1272 :=
    poly1305_update_padded (cipher_text_1277) (poly_st_1272) in 
  let my_tag_1279 : poly1305_tag_t :=
    finish (seq_len (aad_1276)) (seq_len (cipher_text_1277)) (poly_st_1272) in 
  (if (array_declassify_eq (my_tag_1279) (tag_1278)):bool_ChoiceEquality then (
      @Ok byte_seq error_t (chacha20 (key_1274) (iv_1275) (@repr U32 1) (
          cipher_text_1277))) else (@Err byte_seq error_t (InvalidTag))).
Definition chacha20_poly1305_decrypt_pure_code
  (key_1274 : cha_cha_poly_key_t)
  (iv_1275 : cha_cha_poly_iv_t)
  (aad_1276 : byte_seq)
  (cipher_text_1277 : byte_seq)
  (tag_1278 : poly1305_tag_t)
  : code fset.fset0 [interface] (@ct (byte_seq_result_t)) :=
  lift_to_code (chacha20_poly1305_decrypt_pure key_1274
    iv_1275
    aad_1276
    cipher_text_1277
    tag_1278).

Definition poly_st_1272_loc : ChoiceEqualityLocation :=
  (((field_element_t '× field_element_t '× poly_key_t) ; 1296%nat)).
Notation "'chacha20_poly1305_decrypt_state_inp'" := (
  cha_cha_poly_key_t '× cha_cha_poly_iv_t '× byte_seq '× byte_seq '× poly1305_tag_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_poly1305_decrypt_state_out'" := (
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_POLY1305_DECRYPT_STATE : nat :=
  (1297).
Program Definition chacha20_poly1305_decrypt_state
   : package (CEfset ([poly_st_1272_loc])) [interface
  #val #[ FINISH_STATE ] : finish_state_inp → finish_state_out ;
  #val #[ INIT_STATE ] : init_state_inp → init_state_out ;
  #val #[ POLY1305_UPDATE_PADDED_STATE ] : poly1305_update_padded_state_inp → poly1305_update_padded_state_out
  ] [interface
  #val #[ CHACHA20_POLY1305_DECRYPT_STATE ] : chacha20_poly1305_decrypt_state_inp → chacha20_poly1305_decrypt_state_out
  ] :=
  (
    [package #def #[ CHACHA20_POLY1305_DECRYPT_STATE ] (temp_inp : chacha20_poly1305_decrypt_state_inp) : chacha20_poly1305_decrypt_state_out { 
    let '(
      key_1274 , iv_1275 , aad_1276 , cipher_text_1277 , tag_1278) := temp_inp : cha_cha_poly_key_t '× cha_cha_poly_iv_t '× byte_seq '× byte_seq '× poly1305_tag_t in
    #import {sig #[ FINISH_STATE ] : finish_state_inp → finish_state_out } as finish_state ;;
    let finish_state := fun x_0 x_1 x_2 => finish_state (x_0,x_1,x_2) in
    #import {sig #[ INIT_STATE ] : init_state_inp → init_state_out } as init_state ;;
    let init_state := fun x_0 x_1 => init_state (x_0,x_1) in
    #import {sig #[ POLY1305_UPDATE_PADDED_STATE ] : poly1305_update_padded_state_inp → poly1305_update_padded_state_out } as poly1305_update_padded_state ;;
    let poly1305_update_padded_state := fun x_0 x_1 => poly1305_update_padded_state (
      x_0,x_1) in
    ({ code  '(poly_st_1272 : (
              field_element_t '×
              field_element_t '×
              poly_key_t
            )) ←
          ( temp_1281 ←
              (init (key_1274) (iv_1275)) ;;
            ret (temp_1281)) ;;
        #put poly_st_1272_loc := poly_st_1272 ;;
       '(poly_st_1272 : (field_element_t '× field_element_t '× poly_key_t
            )) ←
          (( temp_1283 ←
                (poly1305_update_padded (aad_1276) (poly_st_1272)) ;;
              ret (temp_1283))) ;;
        #put poly_st_1272_loc := poly_st_1272 ;;
      
       '(poly_st_1272 : (field_element_t '× field_element_t '× poly_key_t
            )) ←
          (( temp_1285 ←
                (poly1305_update_padded (cipher_text_1277) (poly_st_1272)) ;;
              ret (temp_1285))) ;;
        #put poly_st_1272_loc := poly_st_1272 ;;
      
       '(my_tag_1279 : poly1305_tag_t) ←
        ( '(temp_1287 : uint_size) ←
            (seq_len (aad_1276)) ;;
           '(temp_1289 : uint_size) ←
            (seq_len (cipher_text_1277)) ;;
           temp_1291 ←
            (finish (temp_1287) (temp_1289) (poly_st_1272)) ;;
          ret (temp_1291)) ;;
       temp_1293 ←
        (array_declassify_eq (my_tag_1279) (tag_1278)) ;;
       temp_1295 ←
        (chacha20 (key_1274) (iv_1275) (@repr U32 1) (cipher_text_1277)) ;;
      @ret ((result error_t byte_seq)) ((if (
            temp_1293):bool_ChoiceEquality then (*inline*) (
            @inl byte_seq error_t (temp_1295)) else (@inr byte_seq error_t (
              InvalidTag)))) } : code (CEfset ([poly_st_1272_loc])) [interface
      #val #[ FINISH_STATE ] : finish_state_inp → finish_state_out ;
      #val #[ INIT_STATE ] : init_state_inp → init_state_out ;
      #val #[ POLY1305_UPDATE_PADDED_STATE ] : poly1305_update_padded_state_inp → poly1305_update_padded_state_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_chacha20_poly1305_decrypt_state : package _ _ _ :=
  (seq_link chacha20_poly1305_decrypt_state link_rest(
      package_finish_state,package_init_state,package_poly1305_update_padded_state)).
Fail Next Obligation.

Notation "'chacha20_poly1305_decrypt_inp'" :=(
  cha_cha_poly_key_t '× cha_cha_poly_iv_t '× byte_seq '× byte_seq '× poly1305_tag_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_poly1305_decrypt_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_POLY1305_DECRYPT : nat :=
  (1298).
Program Definition chacha20_poly1305_decrypt
  (key_1274 : cha_cha_poly_key_t)
  (iv_1275 : cha_cha_poly_iv_t)
  (aad_1276 : byte_seq)
  (cipher_text_1277 : byte_seq)
  (tag_1278 : poly1305_tag_t)
  :both (CEfset ([poly_st_1272_loc])) [interface
  #val #[ CHACHA20 ] : chacha20_inp → chacha20_out ;
  #val #[ FINISH ] : finish_inp → finish_out ;
  #val #[ INIT ] : init_inp → init_out ;
  #val #[ POLY1305_UPDATE_PADDED ] : poly1305_update_padded_inp → poly1305_update_padded_out
  ] (byte_seq_result_t) :=
  #import {sig #[ CHACHA20 ] : chacha20_inp → chacha20_out } as chacha20 ;;
  let chacha20 := fun x_0 x_1 x_2 x_3 => chacha20 (x_0,x_1,x_2,x_3) in
  #import {sig #[ FINISH ] : finish_inp → finish_out } as finish ;;
  let finish := fun x_0 x_1 x_2 => finish (x_0,x_1,x_2) in
  #import {sig #[ INIT ] : init_inp → init_out } as init ;;
  let init := fun x_0 x_1 => init (x_0,x_1) in
  #import {sig #[ POLY1305_UPDATE_PADDED ] : poly1305_update_padded_inp → poly1305_update_padded_out } as poly1305_update_padded ;;
  let poly1305_update_padded := fun x_0 x_1 => poly1305_update_padded (
    x_0,x_1) in
  letbm poly_st_1272 : (field_element_t '× field_element_t '× poly_key_t
    ) loc( poly_st_1272_loc ) :=
    init (lift_to_both0 key_1274) (lift_to_both0 iv_1275) in
  letbm poly_st_1272 loc( poly_st_1272_loc ) :=
    poly1305_update_padded (lift_to_both0 aad_1276) (
      lift_to_both0 poly_st_1272) in
  letbm poly_st_1272 loc( poly_st_1272_loc ) :=
    poly1305_update_padded (lift_to_both0 cipher_text_1277) (
      lift_to_both0 poly_st_1272) in
  letb my_tag_1279 : poly1305_tag_t :=
    finish (seq_len (lift_to_both0 aad_1276)) (seq_len (
        lift_to_both0 cipher_text_1277)) (lift_to_both0 poly_st_1272) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
    if is_pure (I := [interface]) (array_declassify_eq (
        lift_to_both0 my_tag_1279) (lift_to_both0 tag_1278))
    then @Ok byte_seq error_t (chacha20 (lift_to_both0 key_1274) (
        lift_to_both0 iv_1275) (lift_to_both0 (@repr U32 1)) (
        lift_to_both0 cipher_text_1277))
    else @Err byte_seq error_t (InvalidTag))
  .
Fail Next Obligation.

