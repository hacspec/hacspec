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
Require Import Hacspec_Hmac.

Require Import Hacspec_Lib.

Require Import Hacspec_Sha256.

Definition hash_len_v : (uint_size) :=
  (let temp_4051 : uint_size :=
      ((usize 256) ./ (usize 8)) in
    (temp_4051)).

Definition hkdf_error_t : ChoiceEquality :=
  (unit_ChoiceEquality).
Definition InvalidOutputLength : hkdf_error_t :=
  ( tt).

Notation "'hkdf_byte_seq_result_t'" := ((
  result hkdf_error_t byte_seq)) : hacspec_scope.

Definition salt_or_zero_4061_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 4069%nat)).
Notation "'extract_inp'" := (
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'extract_out'" := (
  prk_t : choice_type) (in custom pack_type at level 2).
Definition EXTRACT : nat :=
  (4070).
Program Definition extract
   : package (CEfset ([salt_or_zero_4061_loc])) [interface
  #val #[ HMAC ] : hmac_inp → hmac_out ] [interface
  #val #[ EXTRACT ] : extract_inp → extract_out ] :=
  ([package #def #[ EXTRACT ] (temp_inp : extract_inp) : extract_out { 
    let '(salt_4054 , ikm_4062) := temp_inp : byte_seq '× byte_seq in
    #import {sig #[ HMAC ] : hmac_inp → hmac_out } as hmac ;;
    let hmac := fun x_0 x_1 => hmac (x_0,x_1) in
    ({ code  '(salt_or_zero_4061 : seq uint8) ←
          ( temp_4053 ←
              (seq_new_ (default : uint8) (hash_len_v)) ;;
            ret (temp_4053)) ;;
        #put salt_or_zero_4061_loc := salt_or_zero_4061 ;;
       '(temp_4056 : uint_size) ←
        (seq_len (salt_4054)) ;;
       '(temp_4058 : bool_ChoiceEquality) ←
        ((temp_4056) >.? (usize 0)) ;;
       '(salt_or_zero_4061 : (seq uint8)) ←
        (if temp_4058:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(
                  salt_or_zero_4061 : seq uint8) ←
                (( '(temp_4060 : byte_seq) ←
                      (seq_from_seq (salt_4054)) ;;
                    ret (temp_4060))) ;;
              #put salt_or_zero_4061_loc := salt_or_zero_4061 ;;
            
            @ret ((seq uint8)) (salt_or_zero_4061) in
            ({ code temp_then } : code (CEfset (
                  [salt_or_zero_4061_loc])) [interface] _))
          else @ret ((seq uint8)) (salt_or_zero_4061)) ;;
      
       '(temp_4064 : prk_t) ←
        (hmac (salt_or_zero_4061) (ikm_4062)) ;;
       '(temp_4066 : seq uint8) ←
        (array_to_seq (temp_4064)) ;;
       '(temp_4068 : prk_t) ←
        (array_from_seq (hash_size_v) (temp_4066)) ;;
      @ret (prk_t) (temp_4068) } : code (CEfset (
          [salt_or_zero_4061_loc])) [interface
      #val #[ HMAC ] : hmac_inp → hmac_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_extract : package _ _ _ :=
  (seq_link extract link_rest(package_hmac)).
Fail Next Obligation.

Definition out_4083_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 4097%nat)).
Notation "'build_hmac_txt_inp'" := (
  byte_seq '× byte_seq '× uint8 : choice_type) (in custom pack_type at level 2).
Notation "'build_hmac_txt_out'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition BUILD_HMAC_TXT : nat :=
  (4098).
Program Definition build_hmac_txt
   : package (CEfset ([out_4083_loc])) [interface] [interface
  #val #[ BUILD_HMAC_TXT ] : build_hmac_txt_inp → build_hmac_txt_out ] :=
  (
    [package #def #[ BUILD_HMAC_TXT ] (temp_inp : build_hmac_txt_inp) : build_hmac_txt_out { 
    let '(
      t_4071 , info_4074 , iteration_4096) := temp_inp : byte_seq '× byte_seq '× uint8 in
    ({ code  '(out_4083 : seq uint8) ←
          ( '(temp_4073 : uint_size) ←
              (seq_len (t_4071)) ;;
             '(temp_4076 : uint_size) ←
              (seq_len (info_4074)) ;;
             '(temp_4078 : uint_size) ←
              ((temp_4073) .+ (temp_4076)) ;;
             '(temp_4080 : uint_size) ←
              ((temp_4078) .+ (usize 1)) ;;
             temp_4082 ←
              (seq_new_ (default : uint8) (temp_4080)) ;;
            ret (temp_4082)) ;;
        #put out_4083_loc := out_4083 ;;
       '(out_4083 : seq uint8) ←
          (( '(temp_4085 : seq uint8) ←
                (seq_update (out_4083) (usize 0) (t_4071)) ;;
              ret (temp_4085))) ;;
        #put out_4083_loc := out_4083 ;;
      
       '(out_4083 : seq uint8) ←
          (( '(temp_4087 : uint_size) ←
                (seq_len (t_4071)) ;;
               '(temp_4089 : seq uint8) ←
                (seq_update (out_4083) (temp_4087) (info_4074)) ;;
              ret (temp_4089))) ;;
        #put out_4083_loc := out_4083 ;;
      
       '(out_4083 : seq uint8) ←
        ( '(temp_4091 : uint_size) ←
            (seq_len (t_4071)) ;;
           '(temp_4093 : uint_size) ←
            (seq_len (info_4074)) ;;
           '(temp_4095 : uint_size) ←
            ((temp_4091) .+ (temp_4093)) ;;
          ret (seq_upd out_4083 (temp_4095) (iteration_4096))) ;;
      
      @ret (seq uint8) (out_4083) } : code (CEfset (
          [out_4083_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_build_hmac_txt : package _ _ _ :=
  (build_hmac_txt).
Fail Next Obligation.

Definition q_4107_loc : ChoiceEqualityLocation :=
  ((uint_size ; 4110%nat)).
Notation "'div_ceil_inp'" := (
  uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'div_ceil_out'" := (
  uint_size : choice_type) (in custom pack_type at level 2).
Definition DIV_CEIL : nat :=
  (4111).
Program Definition div_ceil
   : package (CEfset ([q_4107_loc])) [interface] [interface
  #val #[ DIV_CEIL ] : div_ceil_inp → div_ceil_out ] :=
  ([package #def #[ DIV_CEIL ] (temp_inp : div_ceil_inp) : div_ceil_out { 
    let '(a_4099 , b_4100) := temp_inp : uint_size '× uint_size in
    ({ code  '(q_4107 : uint_size) ←
          ( '(temp_4102 : uint_size) ←
              ((a_4099) ./ (b_4100)) ;;
            ret (temp_4102)) ;;
        #put q_4107_loc := q_4107 ;;
       '(temp_4104 : uint_size) ←
        ((a_4099) %% (b_4100)) ;;
       '(temp_4106 : bool_ChoiceEquality) ←
        ((temp_4104) !=.? (usize 0)) ;;
       '(q_4107 : (uint_size)) ←
        (if temp_4106:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(q_4107 : uint_size) ←
                (( '(temp_4109 : uint_size) ←
                      ((q_4107) .+ (usize 1)) ;;
                    ret (temp_4109))) ;;
              #put q_4107_loc := q_4107 ;;
            
            @ret ((uint_size)) (q_4107) in
            ({ code temp_then } : code (CEfset ([q_4107_loc])) [interface] _))
          else @ret ((uint_size)) (q_4107)) ;;
      
      @ret (uint_size) (q_4107) } : code (CEfset ([q_4107_loc])) [interface] _)
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
  (4118).
Program Definition check_output_limit
   : package (CEfset ([])) [interface
  #val #[ DIV_CEIL ] : div_ceil_inp → div_ceil_out ] [interface
  #val #[ CHECK_OUTPUT_LIMIT ] : check_output_limit_inp → check_output_limit_out
  ] :=
  (
    [package #def #[ CHECK_OUTPUT_LIMIT ] (temp_inp : check_output_limit_inp) : check_output_limit_out { 
    let '(l_4112) := temp_inp : uint_size in
    #import {sig #[ DIV_CEIL ] : div_ceil_inp → div_ceil_out } as div_ceil ;;
    let div_ceil := fun x_0 x_1 => div_ceil (x_0,x_1) in
    ({ code  '(n_4115 : uint_size) ←
        ( '(temp_4114 : uint_size) ←
            (div_ceil (l_4112) (hash_len_v)) ;;
          ret (temp_4114)) ;;
       '(temp_4117 : bool_ChoiceEquality) ←
        ((n_4115) <=.? (usize 255)) ;;
      @ret ((result hkdf_error_t uint_size)) ((if (
            temp_4117):bool_ChoiceEquality then (*inline*) (
            @inl uint_size hkdf_error_t (n_4115)) else (
            @inr uint_size hkdf_error_t (InvalidOutputLength)))) } : code (
        CEfset ([])) [interface
      #val #[ DIV_CEIL ] : div_ceil_inp → div_ceil_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_check_output_limit : package _ _ _ :=
  (seq_link check_output_limit link_rest(package_div_ceil)).
Fail Next Obligation.

Definition t_4156_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 4169%nat)).
Definition t_i_4141_loc : ChoiceEqualityLocation :=
  ((prk_t ; 4170%nat)).
Notation "'expand_inp'" := (
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'expand_out'" := (
  hkdf_byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Definition EXPAND : nat :=
  (4171).
Program Definition expand
   : package (CEfset ([t_i_4141_loc ; t_4156_loc])) [interface
  #val #[ BUILD_HMAC_TXT ] : build_hmac_txt_inp → build_hmac_txt_out ;
  #val #[ CHECK_OUTPUT_LIMIT ] : check_output_limit_inp → check_output_limit_out ;
  #val #[ HMAC ] : hmac_inp → hmac_out ] [interface
  #val #[ EXPAND ] : expand_inp → expand_out ] :=
  ([package #def #[ EXPAND ] (temp_inp : expand_inp) : expand_out { 
    let '(
      prk_4152 , info_4134 , l_4119) := temp_inp : byte_seq '× byte_seq '× uint_size in
    #import {sig #[ BUILD_HMAC_TXT ] : build_hmac_txt_inp → build_hmac_txt_out } as build_hmac_txt ;;
    let build_hmac_txt := fun x_0 x_1 x_2 => build_hmac_txt (x_0,x_1,x_2) in
    #import {sig #[ CHECK_OUTPUT_LIMIT ] : check_output_limit_inp → check_output_limit_out } as check_output_limit ;;
    let check_output_limit := fun x_0 => check_output_limit (x_0) in
    #import {sig #[ HMAC ] : hmac_inp → hmac_out } as hmac ;;
    let hmac := fun x_0 x_1 => hmac (x_0,x_1) in
    ({ code bnd(
        ChoiceEqualityMonad.result_bind_code hkdf_error_t , uint_size , _ , CEfset (
          [t_i_4141_loc ; t_4156_loc])) n_4124 ⇠
      (({ code  '(temp_4121 : (result hkdf_error_t uint_size)) ←
            (check_output_limit (l_4119)) ;;
          @ret _ (temp_4121) } : code (CEfset ([])) [interface
          #val #[ CHECK_OUTPUT_LIMIT ] : check_output_limit_inp → check_output_limit_out
          ] _)) in
      ({ code  '(t_i_4141 : prk_t) ←
            ( '(temp_4123 : prk_t) ←
                (array_new_ (default : uint8) (hash_size_v)) ;;
              ret (temp_4123)) ;;
          #put t_i_4141_loc := t_i_4141 ;;
         '(t_4156 : seq uint8) ←
            ( '(temp_4126 : uint_size) ←
                ((n_4124) .* (hash_size_v)) ;;
               temp_4128 ←
                (seq_new_ (default : uint8) (temp_4126)) ;;
              ret (temp_4128)) ;;
          #put t_4156_loc := t_4156 ;;
         temp_4168 ←
          (foldi' (usize 0) (n_4124) prod_ce(t_i_4141, t_4156) (L2 := CEfset (
                  [t_i_4141_loc ; t_4156_loc])) (I2 := [interface
                #val #[ BUILD_HMAC_TXT ] : build_hmac_txt_inp → build_hmac_txt_out ;
                #val #[ CHECK_OUTPUT_LIMIT ] : check_output_limit_inp → check_output_limit_out ;
                #val #[ HMAC ] : hmac_inp → hmac_out
                ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_4129 '(
                t_i_4141,
                t_4156
              ) =>
              ({ code  '(hmac_txt_in_4153 : seq uint8) ←
                  ( '(temp_4131 : bool_ChoiceEquality) ←
                      ((i_4129) =.? (usize 0)) ;;
                     temp_4133 ←
                      (seq_new_ (default : uint8) (usize 0)) ;;
                     '(temp_4136 : int8) ←
                      ((pub_u8 (i_4129)) .+ (@repr U8 1)) ;;
                     '(temp_4138 : int8) ←
                      (secret (temp_4136)) ;;
                     '(temp_4140 : byte_seq) ←
                      (build_hmac_txt (temp_4133) (info_4134) (temp_4138)) ;;
                     '(temp_4143 : seq uint8) ←
                      (array_to_seq (t_i_4141)) ;;
                     '(temp_4145 : byte_seq) ←
                      (seq_from_seq (temp_4143)) ;;
                     '(temp_4147 : int8) ←
                      ((pub_u8 (i_4129)) .+ (@repr U8 1)) ;;
                     '(temp_4149 : int8) ←
                      (secret (temp_4147)) ;;
                     '(temp_4151 : byte_seq) ←
                      (build_hmac_txt (temp_4145) (info_4134) (temp_4149)) ;;
                    ret ((if (temp_4131):bool_ChoiceEquality then (*inline*) (
                          temp_4140) else (temp_4151)))) ;;
                 '(t_i_4141 : prk_t) ←
                    (( temp_4155 ←
                          (hmac (prk_4152) (hmac_txt_in_4153)) ;;
                        ret (temp_4155))) ;;
                  #put t_i_4141_loc := t_i_4141 ;;
                
                 '(t_4156 : seq uint8) ←
                    (( temp_4158 ←
                          (array_len (t_i_4141)) ;;
                         '(temp_4160 : uint_size) ←
                          ((i_4129) .* (temp_4158)) ;;
                         '(temp_4162 : seq uint8) ←
                          (array_to_seq (t_i_4141)) ;;
                         '(temp_4164 : seq uint8) ←
                          (seq_update (t_4156) (temp_4160) (temp_4162)) ;;
                        ret (temp_4164))) ;;
                  #put t_4156_loc := t_4156 ;;
                
                @ret ((prk_t '× seq uint8)) (prod_ce(t_i_4141, t_4156
                  )) } : code (CEfset ([t_i_4141_loc ; t_4156_loc])) [interface
                #val #[ BUILD_HMAC_TXT ] : build_hmac_txt_inp → build_hmac_txt_out ;
                #val #[ HMAC ] : hmac_inp → hmac_out ] _))) ;;
        let '(t_i_4141, t_4156) :=
          (temp_4168) : (prk_t '× seq uint8) in
        
         '(temp_4166 : seq uint8) ←
          (seq_slice (t_4156) (usize 0) (l_4119)) ;;
        @ret ((result hkdf_error_t byte_seq)) (@inl byte_seq hkdf_error_t (
            temp_4166)) } : code (CEfset (
            [t_i_4141_loc ; t_4156_loc])) [interface
        #val #[ BUILD_HMAC_TXT ] : build_hmac_txt_inp → build_hmac_txt_out ;
        #val #[ CHECK_OUTPUT_LIMIT ] : check_output_limit_inp → check_output_limit_out ;
        #val #[ HMAC ] : hmac_inp → hmac_out ] _) } : code (CEfset (
          [t_i_4141_loc ; t_4156_loc])) [interface
      #val #[ BUILD_HMAC_TXT ] : build_hmac_txt_inp → build_hmac_txt_out ;
      #val #[ CHECK_OUTPUT_LIMIT ] : check_output_limit_inp → check_output_limit_out ;
      #val #[ HMAC ] : hmac_inp → hmac_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_expand : package _ _ _ :=
  (seq_link expand link_rest(
      package_build_hmac_txt,package_check_output_limit,package_hmac)).
Fail Next Obligation.

