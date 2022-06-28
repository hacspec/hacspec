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
Require Import Hacspec_Hmac.

Require Import Hacspec_Lib.

Require Import Hacspec_Sha256.

Definition hash_len_v : (uint_size) :=
  (let temp_1 : uint_size :=
      ((usize 256) ./ (usize 8)) in
    (temp_1)).

Definition hkdf_error_t : ChoiceEquality :=
  (unit_ChoiceEquality).
Definition InvalidOutputLength : hkdf_error_t :=
  ( tt).

Notation "'hkdf_byte_seq_result_t'" := ((
  result hkdf_error_t byte_seq)) : hacspec_scope.

Definition salt_or_zero_11_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 19%nat)).
Notation "'extract_inp'" := (
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'extract_out'" := (
  prk_t : choice_type) (in custom pack_type at level 2).
Definition EXTRACT : nat :=
  (20).
Program Definition extract
   : package (CEfset ([salt_or_zero_11_loc])) [interface
  #val #[ HMAC ] : hmac_inp → hmac_out ] [interface
  #val #[ EXTRACT ] : extract_inp → extract_out ] :=
  ([package #def #[ EXTRACT ] (temp_inp : extract_inp) : extract_out { 
    let '(salt_4 , ikm_12) := temp_inp : byte_seq '× byte_seq in
    #import {sig #[ HMAC ] : hmac_inp → hmac_out } as hmac ;;
    let hmac := fun x_0 x_1 => hmac (x_0,x_1) in
    ({ code  '(salt_or_zero_11 : seq uint8) ←
          ( temp_3 ←
              (seq_new_ (default : uint8) (hash_len_v)) ;;
            ret (temp_3)) ;;
        #put salt_or_zero_11_loc := salt_or_zero_11 ;;
       '(temp_6 : uint_size) ←
        (seq_len (salt_4)) ;;
       '(temp_8 : bool_ChoiceEquality) ←
        ((temp_6) >.? (usize 0)) ;;
       '(salt_or_zero_11 : (seq uint8)) ←
        (if temp_8:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(
                  salt_or_zero_11 : seq uint8) ←
                (( '(temp_10 : byte_seq) ←
                      (seq_from_seq (salt_4)) ;;
                    ret (temp_10))) ;;
              #put salt_or_zero_11_loc := salt_or_zero_11 ;;
            
            @ret ((seq uint8)) (salt_or_zero_11) in
            ({ code temp_then } : code (CEfset (
                  [salt_or_zero_11_loc])) [interface] _))
          else @ret ((seq uint8)) (salt_or_zero_11)) ;;
      
       '(temp_14 : prk_t) ←
        (hmac (salt_or_zero_11) (ikm_12)) ;;
       '(temp_16 : seq uint8) ←
        (array_to_seq (temp_14)) ;;
       '(temp_18 : prk_t) ←
        (array_from_seq (hash_size_v) (temp_16)) ;;
      @ret (prk_t) (temp_18) } : code (CEfset (
          [salt_or_zero_11_loc])) [interface
      #val #[ HMAC ] : hmac_inp → hmac_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_extract : package _ _ _ :=
  (seq_link extract link_rest(package_hmac)).
Fail Next Obligation.

Definition out_33_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 47%nat)).
Notation "'build_hmac_txt_inp'" := (
  byte_seq '× byte_seq '× uint8 : choice_type) (in custom pack_type at level 2).
Notation "'build_hmac_txt_out'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition BUILD_HMAC_TXT : nat :=
  (48).
Program Definition build_hmac_txt
   : package (CEfset ([out_33_loc])) [interface] [interface
  #val #[ BUILD_HMAC_TXT ] : build_hmac_txt_inp → build_hmac_txt_out ] :=
  (
    [package #def #[ BUILD_HMAC_TXT ] (temp_inp : build_hmac_txt_inp) : build_hmac_txt_out { 
    let '(
      t_21 , info_24 , iteration_46) := temp_inp : byte_seq '× byte_seq '× uint8 in
    ({ code  '(out_33 : seq uint8) ←
          ( '(temp_23 : uint_size) ←
              (seq_len (t_21)) ;;
             '(temp_26 : uint_size) ←
              (seq_len (info_24)) ;;
             '(temp_28 : uint_size) ←
              ((temp_23) .+ (temp_26)) ;;
             '(temp_30 : uint_size) ←
              ((temp_28) .+ (usize 1)) ;;
             temp_32 ←
              (seq_new_ (default : uint8) (temp_30)) ;;
            ret (temp_32)) ;;
        #put out_33_loc := out_33 ;;
       '(out_33 : seq uint8) ←
          (( '(temp_35 : seq uint8) ←
                (seq_update (out_33) (usize 0) (t_21)) ;;
              ret (temp_35))) ;;
        #put out_33_loc := out_33 ;;
      
       '(out_33 : seq uint8) ←
          (( '(temp_37 : uint_size) ←
                (seq_len (t_21)) ;;
               '(temp_39 : seq uint8) ←
                (seq_update (out_33) (temp_37) (info_24)) ;;
              ret (temp_39))) ;;
        #put out_33_loc := out_33 ;;
      
       '(out_33 : seq uint8) ←
        ( '(temp_41 : uint_size) ←
            (seq_len (t_21)) ;;
           '(temp_43 : uint_size) ←
            (seq_len (info_24)) ;;
           '(temp_45 : uint_size) ←
            ((temp_41) .+ (temp_43)) ;;
          ret (seq_upd out_33 (temp_45) (iteration_46))) ;;
      
      @ret (seq uint8) (out_33) } : code (CEfset ([out_33_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_build_hmac_txt : package _ _ _ :=
  (build_hmac_txt).
Fail Next Obligation.

Definition q_57_loc : ChoiceEqualityLocation :=
  ((uint_size ; 60%nat)).
Notation "'div_ceil_inp'" := (
  uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'div_ceil_out'" := (
  uint_size : choice_type) (in custom pack_type at level 2).
Definition DIV_CEIL : nat :=
  (61).
Program Definition div_ceil
   : package (CEfset ([q_57_loc])) [interface] [interface
  #val #[ DIV_CEIL ] : div_ceil_inp → div_ceil_out ] :=
  ([package #def #[ DIV_CEIL ] (temp_inp : div_ceil_inp) : div_ceil_out { 
    let '(a_49 , b_50) := temp_inp : uint_size '× uint_size in
    ({ code  '(q_57 : uint_size) ←
          ( '(temp_52 : uint_size) ←
              ((a_49) ./ (b_50)) ;;
            ret (temp_52)) ;;
        #put q_57_loc := q_57 ;;
       '(temp_54 : uint_size) ←
        ((a_49) %% (b_50)) ;;
       '(temp_56 : bool_ChoiceEquality) ←
        ((temp_54) !=.? (usize 0)) ;;
       '(q_57 : (uint_size)) ←
        (if temp_56:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(q_57 : uint_size) ←
                (( '(temp_59 : uint_size) ←
                      ((q_57) .+ (usize 1)) ;;
                    ret (temp_59))) ;;
              #put q_57_loc := q_57 ;;
            
            @ret ((uint_size)) (q_57) in
            ({ code temp_then } : code (CEfset ([q_57_loc])) [interface] _))
          else @ret ((uint_size)) (q_57)) ;;
      
      @ret (uint_size) (q_57) } : code (CEfset ([q_57_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_div_ceil : package _ _ _ :=
  (div_ceil).
Fail Next Obligation.


Notation "'check_output_limit_inp'" := (
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'check_output_limit_out'" := ((
    result hkdf_error_t uint_size) : choice_type) (in custom pack_type at level 2).
Definition CHECK_OUTPUT_LIMIT : nat :=
  (68).
Program Definition check_output_limit
   : package (CEfset ([])) [interface
  #val #[ DIV_CEIL ] : div_ceil_inp → div_ceil_out ] [interface
  #val #[ CHECK_OUTPUT_LIMIT ] : check_output_limit_inp → check_output_limit_out
  ] :=
  (
    [package #def #[ CHECK_OUTPUT_LIMIT ] (temp_inp : check_output_limit_inp) : check_output_limit_out { 
    let '(l_62) := temp_inp : uint_size in
    #import {sig #[ DIV_CEIL ] : div_ceil_inp → div_ceil_out } as div_ceil ;;
    let div_ceil := fun x_0 x_1 => div_ceil (x_0,x_1) in
    ({ code  '(n_65 : uint_size) ←
        ( '(temp_64 : uint_size) ←
            (div_ceil (l_62) (hash_len_v)) ;;
          ret (temp_64)) ;;
       '(temp_67 : bool_ChoiceEquality) ←
        ((n_65) <=.? (usize 255)) ;;
      @ret ((result hkdf_error_t uint_size)) ((if (
            temp_67):bool_ChoiceEquality then (*inline*) (
            @inl uint_size hkdf_error_t (n_65)) else (
            @inr uint_size hkdf_error_t (InvalidOutputLength)))) } : code (
        CEfset ([])) [interface
      #val #[ DIV_CEIL ] : div_ceil_inp → div_ceil_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_check_output_limit : package _ _ _ :=
  (seq_link check_output_limit link_rest(package_div_ceil)).
Fail Next Obligation.

Definition t_106_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 119%nat)).
Definition t_i_91_loc : ChoiceEqualityLocation :=
  ((prk_t ; 120%nat)).
Notation "'expand_inp'" := (
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'expand_out'" := (
  hkdf_byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Definition EXPAND : nat :=
  (121).
Program Definition expand
   : package (CEfset ([t_i_91_loc ; t_106_loc])) [interface
  #val #[ BUILD_HMAC_TXT ] : build_hmac_txt_inp → build_hmac_txt_out ;
  #val #[ CHECK_OUTPUT_LIMIT ] : check_output_limit_inp → check_output_limit_out ;
  #val #[ HMAC ] : hmac_inp → hmac_out ] [interface
  #val #[ EXPAND ] : expand_inp → expand_out ] :=
  ([package #def #[ EXPAND ] (temp_inp : expand_inp) : expand_out { 
    let '(
      prk_102 , info_84 , l_69) := temp_inp : byte_seq '× byte_seq '× uint_size in
    #import {sig #[ BUILD_HMAC_TXT ] : build_hmac_txt_inp → build_hmac_txt_out } as build_hmac_txt ;;
    let build_hmac_txt := fun x_0 x_1 x_2 => build_hmac_txt (x_0,x_1,x_2) in
    #import {sig #[ CHECK_OUTPUT_LIMIT ] : check_output_limit_inp → check_output_limit_out } as check_output_limit ;;
    let check_output_limit := fun x_0 => check_output_limit (x_0) in
    #import {sig #[ HMAC ] : hmac_inp → hmac_out } as hmac ;;
    let hmac := fun x_0 x_1 => hmac (x_0,x_1) in
    ({ code bnd(
        ChoiceEqualityMonad.result_bind_code hkdf_error_t , uint_size , _ , CEfset (
          [t_i_91_loc ; t_106_loc])) n_74 ⇠
      (({ code  '(temp_71 : (result hkdf_error_t uint_size)) ←
            (check_output_limit (l_69)) ;;
          @ret _ (temp_71) } : code (CEfset ([])) [interface
          #val #[ CHECK_OUTPUT_LIMIT ] : check_output_limit_inp → check_output_limit_out
          ] _)) in
      ({ code  '(t_i_91 : prk_t) ←
            ( '(temp_73 : prk_t) ←
                (array_new_ (default : uint8) (hash_size_v)) ;;
              ret (temp_73)) ;;
          #put t_i_91_loc := t_i_91 ;;
         '(t_106 : seq uint8) ←
            ( '(temp_76 : uint_size) ←
                ((n_74) .* (hash_size_v)) ;;
               temp_78 ←
                (seq_new_ (default : uint8) (temp_76)) ;;
              ret (temp_78)) ;;
          #put t_106_loc := t_106 ;;
         temp_118 ←
          (foldi' (usize 0) (n_74) prod_ce(t_i_91, t_106) (L2 := CEfset (
                  [t_i_91_loc ; t_106_loc])) (I2 := [interface
                #val #[ BUILD_HMAC_TXT ] : build_hmac_txt_inp → build_hmac_txt_out ;
                #val #[ CHECK_OUTPUT_LIMIT ] : check_output_limit_inp → check_output_limit_out ;
                #val #[ HMAC ] : hmac_inp → hmac_out
                ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_79 '(
                t_i_91,
                t_106
              ) =>
              ({ code  '(hmac_txt_in_103 : seq uint8) ←
                  ( '(temp_81 : bool_ChoiceEquality) ←
                      ((i_79) =.? (usize 0)) ;;
                     temp_83 ←
                      (seq_new_ (default : uint8) (usize 0)) ;;
                     '(temp_86 : int8) ←
                      ((pub_u8 (i_79)) .+ (@repr U8 1)) ;;
                     '(temp_88 : int8) ←
                      (secret (temp_86)) ;;
                     '(temp_90 : byte_seq) ←
                      (build_hmac_txt (temp_83) (info_84) (temp_88)) ;;
                     '(temp_93 : seq uint8) ←
                      (array_to_seq (t_i_91)) ;;
                     '(temp_95 : byte_seq) ←
                      (seq_from_seq (temp_93)) ;;
                     '(temp_97 : int8) ←
                      ((pub_u8 (i_79)) .+ (@repr U8 1)) ;;
                     '(temp_99 : int8) ←
                      (secret (temp_97)) ;;
                     '(temp_101 : byte_seq) ←
                      (build_hmac_txt (temp_95) (info_84) (temp_99)) ;;
                    ret ((if (temp_81):bool_ChoiceEquality then (*inline*) (
                          temp_90) else (temp_101)))) ;;
                 '(t_i_91 : prk_t) ←
                    (( temp_105 ←
                          (hmac (prk_102) (hmac_txt_in_103)) ;;
                        ret (temp_105))) ;;
                  #put t_i_91_loc := t_i_91 ;;
                
                 '(t_106 : seq uint8) ←
                    (( temp_108 ←
                          (array_len (t_i_91)) ;;
                         '(temp_110 : uint_size) ←
                          ((i_79) .* (temp_108)) ;;
                         '(temp_112 : seq uint8) ←
                          (array_to_seq (t_i_91)) ;;
                         '(temp_114 : seq uint8) ←
                          (seq_update (t_106) (temp_110) (temp_112)) ;;
                        ret (temp_114))) ;;
                  #put t_106_loc := t_106 ;;
                
                @ret ((prk_t '× seq uint8)) (prod_ce(t_i_91, t_106)) } : code (
                  CEfset ([t_i_91_loc ; t_106_loc])) [interface
                #val #[ BUILD_HMAC_TXT ] : build_hmac_txt_inp → build_hmac_txt_out ;
                #val #[ HMAC ] : hmac_inp → hmac_out ] _))) ;;
        let '(t_i_91, t_106) :=
          (temp_118) : (prk_t '× seq uint8) in
        
         '(temp_116 : seq uint8) ←
          (seq_slice (t_106) (usize 0) (l_69)) ;;
        @ret ((result hkdf_error_t byte_seq)) (@inl byte_seq hkdf_error_t (
            temp_116)) } : code (CEfset ([t_i_91_loc ; t_106_loc])) [interface
        #val #[ BUILD_HMAC_TXT ] : build_hmac_txt_inp → build_hmac_txt_out ;
        #val #[ CHECK_OUTPUT_LIMIT ] : check_output_limit_inp → check_output_limit_out ;
        #val #[ HMAC ] : hmac_inp → hmac_out ] _) } : code (CEfset (
          [t_i_91_loc ; t_106_loc])) [interface
      #val #[ BUILD_HMAC_TXT ] : build_hmac_txt_inp → build_hmac_txt_out ;
      #val #[ CHECK_OUTPUT_LIMIT ] : check_output_limit_inp → check_output_limit_out ;
      #val #[ HMAC ] : hmac_inp → hmac_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_expand : package _ _ _ :=
  (seq_link expand link_rest(
      package_build_hmac_txt,package_check_output_limit,package_hmac)).
Fail Next Obligation.

