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
Require Import Hacspec_Lib.

Definition poly_key_t  :=
  ( nseq (uint8) (usize 32)).

Definition blocksize_v : (uint_size) :=
  ((usize 16)).

Definition poly_block_t  :=
  ( nseq (uint8) (usize 16)).

Definition poly1305_tag_t  :=
  ( nseq (uint8) (usize 16)).

Notation "'sub_block_t'" := (byte_seq) : hacspec_scope.

Notation "'block_index_t'" := (uint_size) : hacspec_scope.

Definition field_canvas_t  :=
  (nseq (int8) (17)).
Definition field_element_t  :=
  (nat_mod 0x03fffffffffffffffffffffffffffffffb).

Notation "'poly_state_t'" := ((
  field_element_t '×
  field_element_t '×
  poly_key_t
)) : hacspec_scope.

Definition n_7_loc : ChoiceEqualityLocation :=
  ((uint128 ; 14%nat)).
Notation "'poly1305_encode_r_inp'" := (
  poly_block_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_encode_r_out'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_ENCODE_R : nat :=
  (15).
Program Definition poly1305_encode_r
   : package (CEfset ([n_7_loc])) [interface  ] [interface
  #val #[ POLY1305_ENCODE_R ] : poly1305_encode_r_inp → poly1305_encode_r_out
  ] :=
  (
    [package #def #[ POLY1305_ENCODE_R ] (temp_inp : poly1305_encode_r_inp) : poly1305_encode_r_out { 
    let '(b_0) := temp_inp : poly_block_t in
    ({ code  '(n_7 : uint128) ←
          ( '(temp_2 : seq uint8) ←
              (array_to_seq (b_0)) ;;
             '(temp_4 : uint128_word_t) ←
              (array_from_seq (16) (temp_2)) ;;
             '(temp_6 : int128) ←
              (uint128_from_le_bytes (temp_4)) ;;
            ret (temp_6)) ;;
        #put n_7_loc := n_7 ;;
       '(n_7 : uint128) ←
          (( '(temp_9 : int128) ←
                (secret (@repr U128 21267647620597763993911028882763415551)) ;;
               temp_11 ←
                ((n_7) .& (temp_9)) ;;
              ret (temp_11))) ;;
        #put n_7_loc := n_7 ;;
      
       '(temp_13 : field_element_t) ←
        (nat_mod_from_secret_literal (n_7)) ;;
      @ret (field_element_t) (temp_13) } : code (CEfset ([n_7_loc])) [interface 
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_poly1305_encode_r : package _ _ _ :=
  (poly1305_encode_r).
Fail Next Obligation.


Notation "'poly1305_encode_block_inp'" := (
  poly_block_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_encode_block_out'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_ENCODE_BLOCK : nat :=
  (31).
Program Definition poly1305_encode_block
   : package (fset.fset0) [interface  ] [interface
  #val #[ POLY1305_ENCODE_BLOCK ] : poly1305_encode_block_inp → poly1305_encode_block_out
  ] :=
  (
    [package #def #[ POLY1305_ENCODE_BLOCK ] (temp_inp : poly1305_encode_block_inp) : poly1305_encode_block_out { 
    let '(b_16) := temp_inp : poly_block_t in
    ({ code  '(n_23 : uint128) ←
        ( '(temp_18 : seq uint8) ←
            (array_to_seq (b_16)) ;;
           '(temp_20 : uint128_word_t) ←
            (array_from_seq (16) (temp_18)) ;;
           '(temp_22 : int128) ←
            (uint128_from_le_bytes (temp_20)) ;;
          ret (temp_22)) ;;
       '(f_26 : field_element_t) ←
        ( '(temp_25 : field_element_t) ←
            (nat_mod_from_secret_literal (n_23)) ;;
          ret (temp_25)) ;;
       '(temp_28 : field_element_t) ←
        (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (usize 128)) ;;
       '(temp_30 : field_element_t) ←
        ((f_26) +% (temp_28)) ;;
      @ret (field_element_t) (temp_30) } : code (fset.fset0) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_poly1305_encode_block : package _ _ _ :=
  (poly1305_encode_block).
Fail Next Obligation.


Notation "'poly1305_encode_last_inp'" := (
  block_index_t '× sub_block_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_encode_last_out'" := (
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_ENCODE_LAST : nat :=
  (50).
Program Definition poly1305_encode_last
   : package (fset.fset0) [interface  ] [interface
  #val #[ POLY1305_ENCODE_LAST ] : poly1305_encode_last_inp → poly1305_encode_last_out
  ] :=
  (
    [package #def #[ POLY1305_ENCODE_LAST ] (temp_inp : poly1305_encode_last_inp) : poly1305_encode_last_out { 
    let '(pad_len_43 , b_32) := temp_inp : block_index_t '× sub_block_t in
    ({ code  '(n_39 : uint128) ←
        ( '(temp_34 : uint_size) ←
            (seq_len (b_32)) ;;
           '(temp_36 : uint128_word_t) ←
            (array_from_slice (default : uint8) (16) (b_32) (usize 0) (
                temp_34)) ;;
           '(temp_38 : int128) ←
            (uint128_from_le_bytes (temp_36)) ;;
          ret (temp_38)) ;;
       '(f_42 : field_element_t) ←
        ( '(temp_41 : field_element_t) ←
            (nat_mod_from_secret_literal (n_39)) ;;
          ret (temp_41)) ;;
       '(temp_45 : uint_size) ←
        ((usize 8) .* (pad_len_43)) ;;
       '(temp_47 : field_element_t) ←
        (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (temp_45)) ;;
       '(temp_49 : field_element_t) ←
        ((f_42) +% (temp_47)) ;;
      @ret (field_element_t) (temp_49) } : code (fset.fset0) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_poly1305_encode_last : package _ _ _ :=
  (poly1305_encode_last).
Fail Next Obligation.


Notation "'poly1305_init_inp'" := (
  poly_key_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_init_out'" := (
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_INIT : nat :=
  (61).
Program Definition poly1305_init
   : package (CEfset ([])) [interface
  #val #[ POLY1305_ENCODE_R ] : poly1305_encode_r_inp → poly1305_encode_r_out
  ] [interface #val #[ POLY1305_INIT ] : poly1305_init_inp → poly1305_init_out
  ] :=
  (
    [package #def #[ POLY1305_INIT ] (temp_inp : poly1305_init_inp) : poly1305_init_out { 
    let '(k_51) := temp_inp : poly_key_t in
    #import {sig #[ POLY1305_ENCODE_R ] : poly1305_encode_r_inp → poly1305_encode_r_out } as poly1305_encode_r ;;
    let poly1305_encode_r := fun x_0 => poly1305_encode_r (x_0) in
    ({ code  '(r_60 : field_element_t) ←
        ( '(temp_53 : seq uint8) ←
            (array_to_seq (k_51)) ;;
           '(temp_55 : poly_block_t) ←
            (array_from_slice (default : uint8) (16) (temp_53) (usize 0) (
                usize 16)) ;;
           '(temp_57 : field_element_t) ←
            (poly1305_encode_r (temp_55)) ;;
          ret (temp_57)) ;;
       '(temp_59 : field_element_t) ←
        (nat_mod_zero ) ;;
      @ret ((field_element_t '× field_element_t '× poly_key_t)) (prod_ce(
          temp_59,
          r_60,
          k_51
        )) } : code (CEfset ([])) [interface
      #val #[ POLY1305_ENCODE_R ] : poly1305_encode_r_inp → poly1305_encode_r_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_poly1305_init : package _ _ _ :=
  (seq_link poly1305_init link_rest(package_poly1305_encode_r)).
Fail Next Obligation.


Notation "'poly1305_update_block_inp'" := (
  poly_block_t '× poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_block_out'" := (
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_UPDATE_BLOCK : nat :=
  (75).
Program Definition poly1305_update_block
   : package (fset.fset0) [interface
  #val #[ POLY1305_ENCODE_BLOCK ] : poly1305_encode_block_inp → poly1305_encode_block_out
  ] [interface
  #val #[ POLY1305_UPDATE_BLOCK ] : poly1305_update_block_inp → poly1305_update_block_out
  ] :=
  (
    [package #def #[ POLY1305_UPDATE_BLOCK ] (temp_inp : poly1305_update_block_inp) : poly1305_update_block_out { 
    let '(b_63 , st_62) := temp_inp : poly_block_t '× poly_state_t in
    #import {sig #[ POLY1305_ENCODE_BLOCK ] : poly1305_encode_block_inp → poly1305_encode_block_out } as poly1305_encode_block ;;
    let poly1305_encode_block := fun x_0 => poly1305_encode_block (x_0) in
    ({ code  temp_74 ←
        (ret (st_62)) ;;
      let '(acc_66, r_69, k_72) :=
        (temp_74) : (field_element_t '× field_element_t '× poly_key_t) in
       '(temp_65 : field_element_t) ←
        (poly1305_encode_block (b_63)) ;;
       '(temp_68 : field_element_t) ←
        ((temp_65) +% (acc_66)) ;;
       '(temp_71 : field_element_t) ←
        ((temp_68) *% (r_69)) ;;
      @ret ((field_element_t '× field_element_t '× poly_key_t)) (prod_ce(
          temp_71,
          r_69,
          k_72
        )) } : code (fset.fset0) [interface
      #val #[ POLY1305_ENCODE_BLOCK ] : poly1305_encode_block_inp → poly1305_encode_block_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_poly1305_update_block : package _ _ _ :=
  (seq_link poly1305_update_block link_rest(package_poly1305_encode_block)).
Fail Next Obligation.

Definition st_89_loc : ChoiceEqualityLocation :=
  (((field_element_t '× field_element_t '× poly_key_t) ; 92%nat)).
Notation "'poly1305_update_blocks_inp'" := (
  byte_seq '× poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_blocks_out'" := (
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_UPDATE_BLOCKS : nat :=
  (93).
Program Definition poly1305_update_blocks
   : package (CEfset ([st_89_loc])) [interface
  #val #[ POLY1305_UPDATE_BLOCK ] : poly1305_update_block_inp → poly1305_update_block_out
  ] [interface
  #val #[ POLY1305_UPDATE_BLOCKS ] : poly1305_update_blocks_inp → poly1305_update_blocks_out
  ] :=
  (
    [package #def #[ POLY1305_UPDATE_BLOCKS ] (temp_inp : poly1305_update_blocks_inp) : poly1305_update_blocks_out { 
    let '(m_77 , st_76) := temp_inp : byte_seq '× poly_state_t in
    #import {sig #[ POLY1305_UPDATE_BLOCK ] : poly1305_update_block_inp → poly1305_update_block_out } as poly1305_update_block ;;
    let poly1305_update_block := fun x_0 x_1 => poly1305_update_block (
      x_0,x_1) in
    ({ code  '(st_89 : (field_element_t '× field_element_t '× poly_key_t)) ←
          (ret (st_76)) ;;
        #put st_89_loc := st_89 ;;
       '(n_blocks_82 : uint_size) ←
        ( '(temp_79 : uint_size) ←
            (seq_len (m_77)) ;;
           '(temp_81 : uint_size) ←
            ((temp_79) ./ (blocksize_v)) ;;
          ret (temp_81)) ;;
       '(st_89 : ((field_element_t '× field_element_t '× poly_key_t))) ←
        (foldi' (usize 0) (n_blocks_82) st_89 (L2 := CEfset ([st_89_loc])) (
              I2 := [interface
              #val #[ POLY1305_UPDATE_BLOCK ] : poly1305_update_block_inp → poly1305_update_block_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_83 st_89 =>
            ({ code  '(block_88 : poly_block_t) ←
                ( '(temp_85 : byte_seq) ←
                    (seq_get_exact_chunk (m_77) (blocksize_v) (i_83)) ;;
                   '(temp_87 : poly_block_t) ←
                    (array_from_seq (16) (temp_85)) ;;
                  ret (temp_87)) ;;
               '(st_89 : (field_element_t '× field_element_t '× poly_key_t
                    )) ←
                  (( '(temp_91 : poly_state_t) ←
                        (poly1305_update_block (block_88) (st_89)) ;;
                      ret (temp_91))) ;;
                #put st_89_loc := st_89 ;;
              
              @ret (((field_element_t '× field_element_t '× poly_key_t))) (
                st_89) } : code (CEfset ([st_89_loc])) [interface
              #val #[ POLY1305_UPDATE_BLOCK ] : poly1305_update_block_inp → poly1305_update_block_out
              ] _))) ;;
      
      @ret ((field_element_t '× field_element_t '× poly_key_t)) (
        st_89) } : code (CEfset ([st_89_loc])) [interface
      #val #[ POLY1305_UPDATE_BLOCK ] : poly1305_update_block_inp → poly1305_update_block_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_poly1305_update_blocks : package _ _ _ :=
  (seq_link poly1305_update_blocks link_rest(package_poly1305_update_block)).
Fail Next Obligation.

Definition st_100_loc : ChoiceEqualityLocation :=
  (((field_element_t '× field_element_t '× poly_key_t) ; 113%nat)).
Notation "'poly1305_update_last_inp'" := (
  uint_size '× sub_block_t '× poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_last_out'" := (
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_UPDATE_LAST : nat :=
  (114).
Program Definition poly1305_update_last
   : package (CEfset ([st_100_loc])) [interface
  #val #[ POLY1305_ENCODE_LAST ] : poly1305_encode_last_inp → poly1305_encode_last_out
  ] [interface
  #val #[ POLY1305_UPDATE_LAST ] : poly1305_update_last_inp → poly1305_update_last_out
  ] :=
  (
    [package #def #[ POLY1305_UPDATE_LAST ] (temp_inp : poly1305_update_last_inp) : poly1305_update_last_out { 
    let '(
      pad_len_101 , b_95 , st_94) := temp_inp : uint_size '× sub_block_t '× poly_state_t in
    #import {sig #[ POLY1305_ENCODE_LAST ] : poly1305_encode_last_inp → poly1305_encode_last_out } as poly1305_encode_last ;;
    let poly1305_encode_last := fun x_0 x_1 => poly1305_encode_last (x_0,x_1) in
    ({ code  '(st_100 : (field_element_t '× field_element_t '× poly_key_t
            )) ←
          (ret (st_94)) ;;
        #put st_100_loc := st_100 ;;
       '(temp_97 : uint_size) ←
        (seq_len (b_95)) ;;
       '(temp_99 : bool_ChoiceEquality) ←
        ((temp_97) !=.? (usize 0)) ;;
       '(st_100 : ((field_element_t '× field_element_t '× poly_key_t))) ←
        (if temp_99:bool_ChoiceEquality
          then (({ code  temp_112 ←
                (ret (st_100)) ;;
              let '(acc_104, r_107, k_110) :=
                (temp_112) : (field_element_t '× field_element_t '× poly_key_t
              ) in
               '(st_100 : (field_element_t '× field_element_t '× poly_key_t
                    )) ←
                  (( '(temp_103 : field_element_t) ←
                        (poly1305_encode_last (pad_len_101) (b_95)) ;;
                       '(temp_106 : field_element_t) ←
                        ((temp_103) +% (acc_104)) ;;
                       '(temp_109 : field_element_t) ←
                        ((temp_106) *% (r_107)) ;;
                      ret (prod_ce(temp_109, r_107, k_110)))) ;;
                #put st_100_loc := st_100 ;;
              
              @ret (((field_element_t '× field_element_t '× poly_key_t))) (
                st_100) } : code (CEfset ([st_100_loc])) [interface
              #val #[ POLY1305_ENCODE_LAST ] : poly1305_encode_last_inp → poly1305_encode_last_out
              ] _))
          else @ret (((field_element_t '× field_element_t '× poly_key_t))) (
            st_100)) ;;
      
      @ret ((field_element_t '× field_element_t '× poly_key_t)) (
        st_100) } : code (CEfset ([st_100_loc])) [interface
      #val #[ POLY1305_ENCODE_LAST ] : poly1305_encode_last_inp → poly1305_encode_last_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_poly1305_update_last : package _ _ _ :=
  (seq_link poly1305_update_last link_rest(package_poly1305_encode_last)).
Fail Next Obligation.


Notation "'poly1305_update_inp'" := (
  byte_seq '× poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_out'" := (
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_UPDATE : nat :=
  (127).
Program Definition poly1305_update
   : package (CEfset ([])) [interface
  #val #[ POLY1305_UPDATE_BLOCKS ] : poly1305_update_blocks_inp → poly1305_update_blocks_out ;
  #val #[ POLY1305_UPDATE_LAST ] : poly1305_update_last_inp → poly1305_update_last_out
  ] [interface
  #val #[ POLY1305_UPDATE ] : poly1305_update_inp → poly1305_update_out ] :=
  (
    [package #def #[ POLY1305_UPDATE ] (temp_inp : poly1305_update_inp) : poly1305_update_out { 
    let '(m_115 , st_116) := temp_inp : byte_seq '× poly_state_t in
    #import {sig #[ POLY1305_UPDATE_BLOCKS ] : poly1305_update_blocks_inp → poly1305_update_blocks_out } as poly1305_update_blocks ;;
    let poly1305_update_blocks := fun x_0 x_1 => poly1305_update_blocks (
      x_0,x_1) in
    #import {sig #[ POLY1305_UPDATE_LAST ] : poly1305_update_last_inp → poly1305_update_last_out } as poly1305_update_last ;;
    let poly1305_update_last := fun x_0 x_1 x_2 => poly1305_update_last (
      x_0,x_1,x_2) in
    ({ code  '(st_124 : (field_element_t '× field_element_t '× poly_key_t
          )) ←
        ( '(temp_118 : poly_state_t) ←
            (poly1305_update_blocks (m_115) (st_116)) ;;
          ret (temp_118)) ;;
       '(last_121 : seq uint8) ←
        ( '(temp_120 : byte_seq) ←
            (seq_get_remainder_chunk (m_115) (blocksize_v)) ;;
          ret (temp_120)) ;;
       '(temp_123 : uint_size) ←
        (seq_len (last_121)) ;;
       '(temp_126 : poly_state_t) ←
        (poly1305_update_last (temp_123) (last_121) (st_124)) ;;
      @ret (poly_state_t) (temp_126) } : code (CEfset ([])) [interface
      #val #[ POLY1305_UPDATE_BLOCKS ] : poly1305_update_blocks_inp → poly1305_update_blocks_out ;
      #val #[ POLY1305_UPDATE_LAST ] : poly1305_update_last_inp → poly1305_update_last_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_poly1305_update : package _ _ _ :=
  (seq_link poly1305_update link_rest(
      package_poly1305_update_blocks,package_poly1305_update_last)).
Fail Next Obligation.


Notation "'poly1305_finish_inp'" := (
  poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_finish_out'" := (
  poly1305_tag_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_FINISH : nat :=
  (156).
Program Definition poly1305_finish
   : package (fset.fset0) [interface  ] [interface
  #val #[ POLY1305_FINISH ] : poly1305_finish_inp → poly1305_finish_out ] :=
  (
    [package #def #[ POLY1305_FINISH ] (temp_inp : poly1305_finish_inp) : poly1305_finish_out { 
    let '(st_128) := temp_inp : poly_state_t in
    ({ code  temp_155 ←
        (ret (st_128)) ;;
      let '(acc_136, _, k_129) :=
        (temp_155) : (field_element_t '× field_element_t '× poly_key_t) in
       '(n_145 : uint128) ←
        ( '(temp_131 : seq uint8) ←
            (array_to_seq (k_129)) ;;
           '(temp_133 : uint128_word_t) ←
            (array_from_slice (default : uint8) (16) (temp_131) (usize 16) (
                usize 16)) ;;
           '(temp_135 : int128) ←
            (uint128_from_le_bytes (temp_133)) ;;
          ret (temp_135)) ;;
       '(aby_139 : seq uint8) ←
        ( temp_138 ←
            (nat_mod_to_byte_seq_le (acc_136)) ;;
          ret (temp_138)) ;;
       '(a_144 : uint128) ←
        ( '(temp_141 : uint128_word_t) ←
            (array_from_slice (default : uint8) (16) (aby_139) (usize 0) (
                usize 16)) ;;
           '(temp_143 : int128) ←
            (uint128_from_le_bytes (temp_141)) ;;
          ret (temp_143)) ;;
       '(temp_147 : uint128) ←
        ((a_144) .+ (n_145)) ;;
       '(temp_149 : uint128_word_t) ←
        (uint128_to_le_bytes (temp_147)) ;;
       '(temp_151 : seq uint8) ←
        (array_to_seq (temp_149)) ;;
       '(temp_153 : poly1305_tag_t) ←
        (array_from_seq (16) (temp_151)) ;;
      @ret (poly1305_tag_t) (temp_153) } : code (fset.fset0) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_poly1305_finish : package _ _ _ :=
  (poly1305_finish).
Fail Next Obligation.

Definition st_161_loc : ChoiceEqualityLocation :=
  (((field_element_t '× field_element_t '× poly_key_t) ; 166%nat)).
Notation "'poly1305_inp'" := (
  byte_seq '× poly_key_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_out'" := (
  poly1305_tag_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305 : nat :=
  (167).
Program Definition poly1305
   : package (CEfset ([st_161_loc])) [interface
  #val #[ POLY1305_FINISH ] : poly1305_finish_inp → poly1305_finish_out ;
  #val #[ POLY1305_INIT ] : poly1305_init_inp → poly1305_init_out ;
  #val #[ POLY1305_UPDATE ] : poly1305_update_inp → poly1305_update_out
  ] [interface #val #[ POLY1305 ] : poly1305_inp → poly1305_out ] :=
  ([package #def #[ POLY1305 ] (temp_inp : poly1305_inp) : poly1305_out { 
    let '(m_160 , key_157) := temp_inp : byte_seq '× poly_key_t in
    #import {sig #[ POLY1305_FINISH ] : poly1305_finish_inp → poly1305_finish_out } as poly1305_finish ;;
    let poly1305_finish := fun x_0 => poly1305_finish (x_0) in
    #import {sig #[ POLY1305_INIT ] : poly1305_init_inp → poly1305_init_out } as poly1305_init ;;
    let poly1305_init := fun x_0 => poly1305_init (x_0) in
    #import {sig #[ POLY1305_UPDATE ] : poly1305_update_inp → poly1305_update_out } as poly1305_update ;;
    let poly1305_update := fun x_0 x_1 => poly1305_update (x_0,x_1) in
    ({ code  '(st_161 : (field_element_t '× field_element_t '× poly_key_t
            )) ←
          ( '(temp_159 : poly_state_t) ←
              (poly1305_init (key_157)) ;;
            ret (temp_159)) ;;
        #put st_161_loc := st_161 ;;
       '(st_161 : (field_element_t '× field_element_t '× poly_key_t)) ←
          (( '(temp_163 : poly_state_t) ←
                (poly1305_update (m_160) (st_161)) ;;
              ret (temp_163))) ;;
        #put st_161_loc := st_161 ;;
      
       '(temp_165 : poly1305_tag_t) ←
        (poly1305_finish (st_161)) ;;
      @ret (poly1305_tag_t) (temp_165) } : code (CEfset (
          [st_161_loc])) [interface
      #val #[ POLY1305_FINISH ] : poly1305_finish_inp → poly1305_finish_out ;
      #val #[ POLY1305_INIT ] : poly1305_init_inp → poly1305_init_out ;
      #val #[ POLY1305_UPDATE ] : poly1305_update_inp → poly1305_update_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_poly1305 : package _ _ _ :=
  (seq_link poly1305 link_rest(
      package_poly1305_finish,package_poly1305_init,package_poly1305_update)).
Fail Next Obligation.

