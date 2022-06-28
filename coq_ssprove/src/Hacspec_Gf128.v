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

Definition blocksize_v : (uint_size) :=
  ((usize 16)).

Definition gf128_block_t  :=
  ( nseq (uint8) (blocksize_v)).

Definition gf128_key_t  :=
  ( nseq (uint8) (blocksize_v)).

Definition gf128_tag_t  :=
  ( nseq (uint8) (blocksize_v)).

Notation "'element_t'" := (uint128) : hacspec_scope.

Definition irred_v : (element_t) :=
  (let temp_1 : int128 :=
      (secret (@repr U128 299076299051606071403356588563077529600)) in
    (temp_1)).


Notation "'fadd_inp'" :=(
  element_t '× element_t : choice_type) (in custom pack_type at level 2).
Notation "'fadd_out'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Definition FADD : nat :=
  (6).
Program Definition fadd
   : package (fset.fset0) [interface  ] [interface
  #val #[ FADD ] : fadd_inp → fadd_out ] :=
  ([package #def #[ FADD ] (temp_inp : fadd_inp) : fadd_out { 
    let '(x_2 , y_3) := temp_inp : element_t '× element_t in
    ({ code  temp_5 ←
        ((x_2) .^ (y_3)) ;;
      @ret (element_t) (temp_5) } : code (fset.fset0) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_fadd : package _ _ _ :=
  (fadd).
Fail Next Obligation.

Definition sh_29_loc : ChoiceEqualityLocation :=
  ((uint128 ; 52%nat)).
Definition res_28_loc : ChoiceEqualityLocation :=
  ((element_t ; 53%nat)).
Notation "'fmul_inp'" :=(
  element_t '× element_t : choice_type) (in custom pack_type at level 2).
Notation "'fmul_out'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Definition FMUL : nat :=
  (54).
Program Definition fmul
   : package (CEfset ([res_28_loc ; sh_29_loc])) [interface  ] [interface
  #val #[ FMUL ] : fmul_inp → fmul_out ] :=
  ([package #def #[ FMUL ] (temp_inp : fmul_inp) : fmul_out { 
    let '(x_9 , y_10) := temp_inp : element_t '× element_t in
    ({ code  '(res_28 : element_t) ←
          ( '(temp_8 : int128) ←
              (secret (@repr U128 0)) ;;
            ret (temp_8)) ;;
        #put res_28_loc := res_28 ;;
       '(sh_29 : uint128) ←
          (ret (x_9)) ;;
        #put sh_29_loc := sh_29 ;;
       temp_51 ←
        (foldi' (usize 0) (usize 128) prod_ce(res_28, sh_29) (L2 := CEfset (
                [res_28_loc ; sh_29_loc])) (I2 := [interface 
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_13 '(res_28, sh_29
            ) =>
            ({ code  '(temp_12 : int128) ←
                (secret (@repr U128 1)) ;;
               '(temp_15 : uint_size) ←
                ((usize 127) .- (i_13)) ;;
               temp_17 ←
                ((temp_12) shift_left (temp_15)) ;;
               temp_19 ←
                ((y_10) .& (temp_17)) ;;
               '(temp_21 : element_t) ←
                (uint128_declassify (temp_19)) ;;
               '(temp_23 : int128) ←
                (secret (@repr U128 0)) ;;
               '(temp_25 : uint128) ←
                (uint128_declassify (temp_23)) ;;
               '(temp_27 : bool_ChoiceEquality) ←
                ((temp_21) !=.? (temp_25)) ;;
               '(res_28 : (uint128)) ←
                (if temp_27:bool_ChoiceEquality
                  then (({ code  '(res_28 : uint128) ←
                          (( temp_31 ←
                                ((res_28) .^ (sh_29)) ;;
                              ret (temp_31))) ;;
                        #put res_28_loc := res_28 ;;
                      
                      @ret ((uint128)) (res_28) } : code (CEfset (
                          [res_28_loc ; sh_29_loc])) [interface  ] _))
                  else @ret ((uint128)) (res_28)) ;;
              
               '(temp_33 : int128) ←
                (secret (@repr U128 1)) ;;
               temp_35 ←
                ((sh_29) .& (temp_33)) ;;
               '(temp_37 : uint128) ←
                (uint128_declassify (temp_35)) ;;
               '(temp_39 : int128) ←
                (secret (@repr U128 0)) ;;
               '(temp_41 : uint128) ←
                (uint128_declassify (temp_39)) ;;
               '(temp_43 : bool_ChoiceEquality) ←
                ((temp_37) !=.? (temp_41)) ;;
               '(sh_29 : (uint128)) ←
                (if temp_43:bool_ChoiceEquality
                  then (({ code  '(sh_29 : uint128) ←
                          (( temp_45 ←
                                ((sh_29) shift_right (usize 1)) ;;
                               temp_47 ←
                                ((temp_45) .^ (irred_v)) ;;
                              ret (temp_47))) ;;
                        #put sh_29_loc := sh_29 ;;
                      
                      @ret ((uint128)) (sh_29) } : code (CEfset (
                          [res_28_loc ; sh_29_loc])) [interface  ] _))
                  else  (({ code  '(sh_29 : uint128) ←
                          (( temp_49 ←
                                ((sh_29) shift_right (usize 1)) ;;
                              ret (temp_49))) ;;
                        #put sh_29_loc := sh_29 ;;
                      
                      @ret ((uint128)) (sh_29) } : code (CEfset (
                          [res_28_loc ; sh_29_loc])) [interface  ] _))) ;;
              
              @ret ((uint128 '× uint128)) (prod_ce(res_28, sh_29)) } : code (
                CEfset ([res_28_loc ; sh_29_loc])) [interface  ] _))) ;;
      let '(res_28, sh_29) :=
        (temp_51) : (uint128 '× uint128) in
      
      @ret (uint128) (res_28) } : code (CEfset (
          [res_28_loc ; sh_29_loc])) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_fmul : package _ _ _ :=
  (fmul).
Fail Next Obligation.


Notation "'encode_inp'" :=(
  gf128_block_t : choice_type) (in custom pack_type at level 2).
Notation "'encode_out'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Definition ENCODE : nat :=
  (62).
Program Definition encode
   : package (fset.fset0) [interface  ] [interface
  #val #[ ENCODE ] : encode_inp → encode_out ] :=
  ([package #def #[ ENCODE ] (temp_inp : encode_inp) : encode_out { 
    let '(block_55) := temp_inp : gf128_block_t in
    ({ code  '(temp_57 : seq uint8) ←
        (array_to_seq (block_55)) ;;
       '(temp_59 : uint128_word_t) ←
        (array_from_seq (16) (temp_57)) ;;
       '(temp_61 : int128) ←
        (uint128_from_be_bytes (temp_59)) ;;
      @ret (uint128) (temp_61) } : code (fset.fset0) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_encode : package _ _ _ :=
  (encode).
Fail Next Obligation.


Notation "'decode_inp'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Notation "'decode_out'" :=(
  gf128_block_t : choice_type) (in custom pack_type at level 2).
Definition DECODE : nat :=
  (70).
Program Definition decode
   : package (fset.fset0) [interface  ] [interface
  #val #[ DECODE ] : decode_inp → decode_out ] :=
  ([package #def #[ DECODE ] (temp_inp : decode_inp) : decode_out { 
    let '(e_63) := temp_inp : element_t in
    ({ code  '(temp_65 : uint128_word_t) ←
        (uint128_to_be_bytes (e_63)) ;;
       '(temp_67 : seq uint8) ←
        (array_to_seq (temp_65)) ;;
       '(temp_69 : gf128_block_t) ←
        (array_from_seq (blocksize_v) (temp_67)) ;;
      @ret (gf128_block_t) (temp_69) } : code (fset.fset0) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_decode : package _ _ _ :=
  (decode).
Fail Next Obligation.


Notation "'update_inp'" :=(
  element_t '× gf128_block_t '× element_t : choice_type) (in custom pack_type at level 2).
Notation "'update_out'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Definition UPDATE : nat :=
  (80).
Program Definition update
   : package (CEfset ([])) [interface
  #val #[ ENCODE ] : encode_inp → encode_out ;
  #val #[ FADD ] : fadd_inp → fadd_out ;
  #val #[ FMUL ] : fmul_inp → fmul_out ] [interface
  #val #[ UPDATE ] : update_inp → update_out ] :=
  ([package #def #[ UPDATE ] (temp_inp : update_inp) : update_out { 
    let '(
      r_77 , block_71 , acc_74) := temp_inp : element_t '× gf128_block_t '× element_t in
    #import {sig #[ ENCODE ] : encode_inp → encode_out } as  encode ;;
    let encode := fun x_0 => encode (x_0) in
    #import {sig #[ FADD ] : fadd_inp → fadd_out } as  fadd ;;
    let fadd := fun x_0 x_1 => fadd (x_0,x_1) in
    #import {sig #[ FMUL ] : fmul_inp → fmul_out } as  fmul ;;
    let fmul := fun x_0 x_1 => fmul (x_0,x_1) in
    ({ code  '(temp_73 : element_t) ←
        (encode (block_71)) ;;
       '(temp_76 : element_t) ←
        (fadd (temp_73) (acc_74)) ;;
       '(temp_79 : element_t) ←
        (fmul (temp_76) (r_77)) ;;
      @ret (element_t) (temp_79) } : code (CEfset ([])) [interface
      #val #[ ENCODE ] : encode_inp → encode_out ;
      #val #[ FADD ] : fadd_inp → fadd_out ;
      #val #[ FMUL ] : fmul_inp → fmul_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_update : package _ _ _ :=
  (seq_link update link_rest(package_encode,package_fadd,package_fmul)).
Fail Next Obligation.

Definition block_97_loc : ChoiceEqualityLocation :=
  ((gf128_block_t ; 122%nat)).
Definition last_block_116_loc : ChoiceEqualityLocation :=
  ((gf128_block_t ; 123%nat)).
Definition acc_106_loc : ChoiceEqualityLocation :=
  ((uint128 ; 124%nat)).
Notation "'poly_inp'" :=(
  byte_seq '× element_t : choice_type) (in custom pack_type at level 2).
Notation "'poly_out'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Definition POLY : nat :=
  (125).
Program Definition poly
   : package (CEfset (
      [acc_106_loc ; block_97_loc ; last_block_116_loc])) [interface
  #val #[ UPDATE ] : update_inp → update_out ] [interface
  #val #[ POLY ] : poly_inp → poly_out ] :=
  ([package #def #[ POLY ] (temp_inp : poly_inp) : poly_out { 
    let '(msg_81 , r_105) := temp_inp : byte_seq '× element_t in
    #import {sig #[ UPDATE ] : update_inp → update_out } as  update ;;
    let update := fun x_0 x_1 x_2 => update (x_0,x_1,x_2) in
    ({ code  '(l_84 : uint_size) ←
        ( '(temp_83 : uint_size) ←
            (seq_len (msg_81)) ;;
          ret (temp_83)) ;;
       '(n_blocks_91 : uint_size) ←
        ( '(temp_86 : uint_size) ←
            ((l_84) ./ (blocksize_v)) ;;
          ret (temp_86)) ;;
       '(rem_109 : uint_size) ←
        ( '(temp_88 : uint_size) ←
            ((l_84) %% (blocksize_v)) ;;
          ret (temp_88)) ;;
       '(acc_106 : uint128) ←
          ( '(temp_90 : int128) ←
              (secret (@repr U128 0)) ;;
            ret (temp_90)) ;;
        #put acc_106_loc := acc_106 ;;
       '(acc_106 : (uint128)) ←
        (foldi' (usize 0) (n_blocks_91) acc_106 (L2 := CEfset (
                [acc_106_loc ; block_97_loc ; last_block_116_loc])) (
              I2 := [interface #val #[ UPDATE ] : update_inp → update_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_92 acc_106 =>
            ({ code  '(k_98 : uint_size) ←
                ( '(temp_94 : uint_size) ←
                    ((i_92) .* (blocksize_v)) ;;
                  ret (temp_94)) ;;
               '(block_97 : gf128_block_t) ←
                  ( '(temp_96 : gf128_block_t) ←
                      (array_new_ (default : uint8) (blocksize_v)) ;;
                    ret (temp_96)) ;;
                #put block_97_loc := block_97 ;;
               '(block_97 : gf128_block_t) ←
                  (( '(temp_100 : uint_size) ←
                        ((k_98) .+ (blocksize_v)) ;;
                       '(temp_102 : byte_seq) ←
                        (seq_slice_range (msg_81) (prod_ce(k_98, temp_100))) ;;
                       '(temp_104 : gf128_block_t) ←
                        (array_update_start (block_97) (temp_102)) ;;
                      ret (temp_104))) ;;
                #put block_97_loc := block_97 ;;
              
               '(acc_106 : uint128) ←
                  (( '(temp_108 : element_t) ←
                        (update (r_105) (block_97) (acc_106)) ;;
                      ret (temp_108))) ;;
                #put acc_106_loc := acc_106 ;;
              
              @ret ((uint128)) (acc_106) } : code (CEfset (
                  [acc_106_loc ; block_97_loc])) [interface
              #val #[ UPDATE ] : update_inp → update_out ] _))) ;;
      
       '(temp_111 : bool_ChoiceEquality) ←
        ((rem_109) !=.? (usize 0)) ;;
       '(acc_106 : (uint128)) ←
        (if temp_111:bool_ChoiceEquality
          then (({ code  '(k_117 : uint_size) ←
                ( '(temp_113 : uint_size) ←
                    ((n_blocks_91) .* (blocksize_v)) ;;
                  ret (temp_113)) ;;
               '(last_block_116 : gf128_block_t) ←
                  ( '(temp_115 : gf128_block_t) ←
                      (array_new_ (default : uint8) (blocksize_v)) ;;
                    ret (temp_115)) ;;
                #put last_block_116_loc := last_block_116 ;;
               '(last_block_116 : gf128_block_t) ←
                  (( '(temp_119 : gf128_block_t) ←
                        (array_update_slice (last_block_116) (usize 0) (
                            msg_81) (k_117) (rem_109)) ;;
                      ret (temp_119))) ;;
                #put last_block_116_loc := last_block_116 ;;
              
               '(acc_106 : uint128) ←
                  (( '(temp_121 : element_t) ←
                        (update (r_105) (last_block_116) (acc_106)) ;;
                      ret (temp_121))) ;;
                #put acc_106_loc := acc_106 ;;
              
              @ret ((uint128)) (acc_106) } : code (CEfset (
                  [acc_106_loc ; block_97_loc ; last_block_116_loc])) [interface
              #val #[ UPDATE ] : update_inp → update_out ] _))
          else @ret ((uint128)) (acc_106)) ;;
      
      @ret (uint128) (acc_106) } : code (CEfset (
          [acc_106_loc ; block_97_loc ; last_block_116_loc])) [interface
      #val #[ UPDATE ] : update_inp → update_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_poly : package _ _ _ :=
  (seq_link poly link_rest(package_update)).
Fail Next Obligation.


Notation "'gmac_inp'" :=(
  byte_seq '× gf128_key_t : choice_type) (in custom pack_type at level 2).
Notation "'gmac_out'" :=(
  gf128_tag_t : choice_type) (in custom pack_type at level 2).
Definition GMAC : nat :=
  (151).
Program Definition gmac
   : package (CEfset ([])) [interface
  #val #[ DECODE ] : decode_inp → decode_out ;
  #val #[ ENCODE ] : encode_inp → encode_out ;
  #val #[ FADD ] : fadd_inp → fadd_out ;
  #val #[ POLY ] : poly_inp → poly_out ] [interface
  #val #[ GMAC ] : gmac_inp → gmac_out ] :=
  ([package #def #[ GMAC ] (temp_inp : gmac_inp) : gmac_out { 
    let '(text_135 , k_128) := temp_inp : byte_seq '× gf128_key_t in
    #import {sig #[ DECODE ] : decode_inp → decode_out } as  decode ;;
    let decode := fun x_0 => decode (x_0) in
    #import {sig #[ ENCODE ] : encode_inp → encode_out } as  encode ;;
    let encode := fun x_0 => encode (x_0) in
    #import {sig #[ FADD ] : fadd_inp → fadd_out } as  fadd ;;
    let fadd := fun x_0 x_1 => fadd (x_0,x_1) in
    #import {sig #[ POLY ] : poly_inp → poly_out } as  poly ;;
    let poly := fun x_0 x_1 => poly (x_0,x_1) in
    ({ code  '(s_140 : gf128_block_t) ←
        ( '(temp_127 : gf128_block_t) ←
            (array_new_ (default : uint8) (blocksize_v)) ;;
          ret (temp_127)) ;;
       '(r_136 : uint128) ←
        ( '(temp_130 : seq uint8) ←
            (array_to_seq (k_128)) ;;
           '(temp_132 : gf128_block_t) ←
            (array_from_seq (blocksize_v) (temp_130)) ;;
           '(temp_134 : element_t) ←
            (encode (temp_132)) ;;
          ret (temp_134)) ;;
       '(a_139 : uint128) ←
        ( '(temp_138 : element_t) ←
            (poly (text_135) (r_136)) ;;
          ret (temp_138)) ;;
       '(temp_142 : element_t) ←
        (encode (s_140)) ;;
       '(temp_144 : element_t) ←
        (fadd (a_139) (temp_142)) ;;
       '(temp_146 : gf128_block_t) ←
        (decode (temp_144)) ;;
       '(temp_148 : seq uint8) ←
        (array_to_seq (temp_146)) ;;
       '(temp_150 : gf128_tag_t) ←
        (array_from_seq (blocksize_v) (temp_148)) ;;
      @ret (gf128_tag_t) (temp_150) } : code (CEfset ([])) [interface
      #val #[ DECODE ] : decode_inp → decode_out ;
      #val #[ ENCODE ] : encode_inp → encode_out ;
      #val #[ FADD ] : fadd_inp → fadd_out ;
      #val #[ POLY ] : poly_inp → poly_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_gmac : package _ _ _ :=
  (seq_link gmac link_rest(
      package_decode,package_encode,package_fadd,package_poly)).
Fail Next Obligation.

