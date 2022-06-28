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

Require Import Hacspec_Sha256.

Definition block_len_v : (uint_size) :=
  ((k_size_v)).

Definition prk_t  :=
  ( nseq (uint8) (hash_size_v)).

Definition block_t  :=
  ( nseq (uint8) (block_len_v)).

Definition i_pad_v : (block_t) :=
  (let temp_1 : int8 :=
      (secret (@repr U8 54)) in
    let temp_3 : int8 :=
      (secret (@repr U8 54)) in
    let temp_5 : int8 :=
      (secret (@repr U8 54)) in
    let temp_7 : int8 :=
      (secret (@repr U8 54)) in
    let temp_9 : int8 :=
      (secret (@repr U8 54)) in
    let temp_11 : int8 :=
      (secret (@repr U8 54)) in
    let temp_13 : int8 :=
      (secret (@repr U8 54)) in
    let temp_15 : int8 :=
      (secret (@repr U8 54)) in
    let temp_17 : int8 :=
      (secret (@repr U8 54)) in
    let temp_19 : int8 :=
      (secret (@repr U8 54)) in
    let temp_21 : int8 :=
      (secret (@repr U8 54)) in
    let temp_23 : int8 :=
      (secret (@repr U8 54)) in
    let temp_25 : int8 :=
      (secret (@repr U8 54)) in
    let temp_27 : int8 :=
      (secret (@repr U8 54)) in
    let temp_29 : int8 :=
      (secret (@repr U8 54)) in
    let temp_31 : int8 :=
      (secret (@repr U8 54)) in
    let temp_33 : int8 :=
      (secret (@repr U8 54)) in
    let temp_35 : int8 :=
      (secret (@repr U8 54)) in
    let temp_37 : int8 :=
      (secret (@repr U8 54)) in
    let temp_39 : int8 :=
      (secret (@repr U8 54)) in
    let temp_41 : int8 :=
      (secret (@repr U8 54)) in
    let temp_43 : int8 :=
      (secret (@repr U8 54)) in
    let temp_45 : int8 :=
      (secret (@repr U8 54)) in
    let temp_47 : int8 :=
      (secret (@repr U8 54)) in
    let temp_49 : int8 :=
      (secret (@repr U8 54)) in
    let temp_51 : int8 :=
      (secret (@repr U8 54)) in
    let temp_53 : int8 :=
      (secret (@repr U8 54)) in
    let temp_55 : int8 :=
      (secret (@repr U8 54)) in
    let temp_57 : int8 :=
      (secret (@repr U8 54)) in
    let temp_59 : int8 :=
      (secret (@repr U8 54)) in
    let temp_61 : int8 :=
      (secret (@repr U8 54)) in
    let temp_63 : int8 :=
      (secret (@repr U8 54)) in
    let temp_65 : int8 :=
      (secret (@repr U8 54)) in
    let temp_67 : int8 :=
      (secret (@repr U8 54)) in
    let temp_69 : int8 :=
      (secret (@repr U8 54)) in
    let temp_71 : int8 :=
      (secret (@repr U8 54)) in
    let temp_73 : int8 :=
      (secret (@repr U8 54)) in
    let temp_75 : int8 :=
      (secret (@repr U8 54)) in
    let temp_77 : int8 :=
      (secret (@repr U8 54)) in
    let temp_79 : int8 :=
      (secret (@repr U8 54)) in
    let temp_81 : int8 :=
      (secret (@repr U8 54)) in
    let temp_83 : int8 :=
      (secret (@repr U8 54)) in
    let temp_85 : int8 :=
      (secret (@repr U8 54)) in
    let temp_87 : int8 :=
      (secret (@repr U8 54)) in
    let temp_89 : int8 :=
      (secret (@repr U8 54)) in
    let temp_91 : int8 :=
      (secret (@repr U8 54)) in
    let temp_93 : int8 :=
      (secret (@repr U8 54)) in
    let temp_95 : int8 :=
      (secret (@repr U8 54)) in
    let temp_97 : int8 :=
      (secret (@repr U8 54)) in
    let temp_99 : int8 :=
      (secret (@repr U8 54)) in
    let temp_101 : int8 :=
      (secret (@repr U8 54)) in
    let temp_103 : int8 :=
      (secret (@repr U8 54)) in
    let temp_105 : int8 :=
      (secret (@repr U8 54)) in
    let temp_107 : int8 :=
      (secret (@repr U8 54)) in
    let temp_109 : int8 :=
      (secret (@repr U8 54)) in
    let temp_111 : int8 :=
      (secret (@repr U8 54)) in
    let temp_113 : int8 :=
      (secret (@repr U8 54)) in
    let temp_115 : int8 :=
      (secret (@repr U8 54)) in
    let temp_117 : int8 :=
      (secret (@repr U8 54)) in
    let temp_119 : int8 :=
      (secret (@repr U8 54)) in
    let temp_121 : int8 :=
      (secret (@repr U8 54)) in
    let temp_123 : int8 :=
      (secret (@repr U8 54)) in
    let temp_125 : int8 :=
      (secret (@repr U8 54)) in
    let temp_127 : int8 :=
      (secret (@repr U8 54)) in
    let temp_129 : nseq uint8 64 :=
      (array_from_list uint8 [
          temp_1;
          temp_3;
          temp_5;
          temp_7;
          temp_9;
          temp_11;
          temp_13;
          temp_15;
          temp_17;
          temp_19;
          temp_21;
          temp_23;
          temp_25;
          temp_27;
          temp_29;
          temp_31;
          temp_33;
          temp_35;
          temp_37;
          temp_39;
          temp_41;
          temp_43;
          temp_45;
          temp_47;
          temp_49;
          temp_51;
          temp_53;
          temp_55;
          temp_57;
          temp_59;
          temp_61;
          temp_63;
          temp_65;
          temp_67;
          temp_69;
          temp_71;
          temp_73;
          temp_75;
          temp_77;
          temp_79;
          temp_81;
          temp_83;
          temp_85;
          temp_87;
          temp_89;
          temp_91;
          temp_93;
          temp_95;
          temp_97;
          temp_99;
          temp_101;
          temp_103;
          temp_105;
          temp_107;
          temp_109;
          temp_111;
          temp_113;
          temp_115;
          temp_117;
          temp_119;
          temp_121;
          temp_123;
          temp_125;
          temp_127
        ]) in
    (temp_129)).

Definition o_pad_v : (block_t) :=
  (let temp_131 : int8 :=
      (secret (@repr U8 92)) in
    let temp_133 : int8 :=
      (secret (@repr U8 92)) in
    let temp_135 : int8 :=
      (secret (@repr U8 92)) in
    let temp_137 : int8 :=
      (secret (@repr U8 92)) in
    let temp_139 : int8 :=
      (secret (@repr U8 92)) in
    let temp_141 : int8 :=
      (secret (@repr U8 92)) in
    let temp_143 : int8 :=
      (secret (@repr U8 92)) in
    let temp_145 : int8 :=
      (secret (@repr U8 92)) in
    let temp_147 : int8 :=
      (secret (@repr U8 92)) in
    let temp_149 : int8 :=
      (secret (@repr U8 92)) in
    let temp_151 : int8 :=
      (secret (@repr U8 92)) in
    let temp_153 : int8 :=
      (secret (@repr U8 92)) in
    let temp_155 : int8 :=
      (secret (@repr U8 92)) in
    let temp_157 : int8 :=
      (secret (@repr U8 92)) in
    let temp_159 : int8 :=
      (secret (@repr U8 92)) in
    let temp_161 : int8 :=
      (secret (@repr U8 92)) in
    let temp_163 : int8 :=
      (secret (@repr U8 92)) in
    let temp_165 : int8 :=
      (secret (@repr U8 92)) in
    let temp_167 : int8 :=
      (secret (@repr U8 92)) in
    let temp_169 : int8 :=
      (secret (@repr U8 92)) in
    let temp_171 : int8 :=
      (secret (@repr U8 92)) in
    let temp_173 : int8 :=
      (secret (@repr U8 92)) in
    let temp_175 : int8 :=
      (secret (@repr U8 92)) in
    let temp_177 : int8 :=
      (secret (@repr U8 92)) in
    let temp_179 : int8 :=
      (secret (@repr U8 92)) in
    let temp_181 : int8 :=
      (secret (@repr U8 92)) in
    let temp_183 : int8 :=
      (secret (@repr U8 92)) in
    let temp_185 : int8 :=
      (secret (@repr U8 92)) in
    let temp_187 : int8 :=
      (secret (@repr U8 92)) in
    let temp_189 : int8 :=
      (secret (@repr U8 92)) in
    let temp_191 : int8 :=
      (secret (@repr U8 92)) in
    let temp_193 : int8 :=
      (secret (@repr U8 92)) in
    let temp_195 : int8 :=
      (secret (@repr U8 92)) in
    let temp_197 : int8 :=
      (secret (@repr U8 92)) in
    let temp_199 : int8 :=
      (secret (@repr U8 92)) in
    let temp_201 : int8 :=
      (secret (@repr U8 92)) in
    let temp_203 : int8 :=
      (secret (@repr U8 92)) in
    let temp_205 : int8 :=
      (secret (@repr U8 92)) in
    let temp_207 : int8 :=
      (secret (@repr U8 92)) in
    let temp_209 : int8 :=
      (secret (@repr U8 92)) in
    let temp_211 : int8 :=
      (secret (@repr U8 92)) in
    let temp_213 : int8 :=
      (secret (@repr U8 92)) in
    let temp_215 : int8 :=
      (secret (@repr U8 92)) in
    let temp_217 : int8 :=
      (secret (@repr U8 92)) in
    let temp_219 : int8 :=
      (secret (@repr U8 92)) in
    let temp_221 : int8 :=
      (secret (@repr U8 92)) in
    let temp_223 : int8 :=
      (secret (@repr U8 92)) in
    let temp_225 : int8 :=
      (secret (@repr U8 92)) in
    let temp_227 : int8 :=
      (secret (@repr U8 92)) in
    let temp_229 : int8 :=
      (secret (@repr U8 92)) in
    let temp_231 : int8 :=
      (secret (@repr U8 92)) in
    let temp_233 : int8 :=
      (secret (@repr U8 92)) in
    let temp_235 : int8 :=
      (secret (@repr U8 92)) in
    let temp_237 : int8 :=
      (secret (@repr U8 92)) in
    let temp_239 : int8 :=
      (secret (@repr U8 92)) in
    let temp_241 : int8 :=
      (secret (@repr U8 92)) in
    let temp_243 : int8 :=
      (secret (@repr U8 92)) in
    let temp_245 : int8 :=
      (secret (@repr U8 92)) in
    let temp_247 : int8 :=
      (secret (@repr U8 92)) in
    let temp_249 : int8 :=
      (secret (@repr U8 92)) in
    let temp_251 : int8 :=
      (secret (@repr U8 92)) in
    let temp_253 : int8 :=
      (secret (@repr U8 92)) in
    let temp_255 : int8 :=
      (secret (@repr U8 92)) in
    let temp_257 : int8 :=
      (secret (@repr U8 92)) in
    let temp_259 : nseq uint8 64 :=
      (array_from_list uint8 [
          temp_131;
          temp_133;
          temp_135;
          temp_137;
          temp_139;
          temp_141;
          temp_143;
          temp_145;
          temp_147;
          temp_149;
          temp_151;
          temp_153;
          temp_155;
          temp_157;
          temp_159;
          temp_161;
          temp_163;
          temp_165;
          temp_167;
          temp_169;
          temp_171;
          temp_173;
          temp_175;
          temp_177;
          temp_179;
          temp_181;
          temp_183;
          temp_185;
          temp_187;
          temp_189;
          temp_191;
          temp_193;
          temp_195;
          temp_197;
          temp_199;
          temp_201;
          temp_203;
          temp_205;
          temp_207;
          temp_209;
          temp_211;
          temp_213;
          temp_215;
          temp_217;
          temp_219;
          temp_221;
          temp_223;
          temp_225;
          temp_227;
          temp_229;
          temp_231;
          temp_233;
          temp_235;
          temp_237;
          temp_239;
          temp_241;
          temp_243;
          temp_245;
          temp_247;
          temp_249;
          temp_251;
          temp_253;
          temp_255;
          temp_257
        ]) in
    (temp_259)).


Notation "'k_block_inp'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'k_block_out'" := (
  block_t : choice_type) (in custom pack_type at level 2).
Definition K_BLOCK : nat :=
  (277).
Program Definition k_block
   : package (fset.fset0) [interface #val #[ HASH ] : hash_inp → hash_out
  ] [interface #val #[ K_BLOCK ] : k_block_inp → k_block_out ] :=
  ([package #def #[ K_BLOCK ] (temp_inp : k_block_inp) : k_block_out { 
    let '(k_260) := temp_inp : byte_seq in
    #import {sig #[ HASH ] : hash_inp → hash_out } as hash ;;
    let hash := fun x_0 => hash (x_0) in
    ({ code  '(temp_262 : uint_size) ←
        (seq_len (k_260)) ;;
       '(temp_264 : bool_ChoiceEquality) ←
        ((temp_262) >.? (block_len_v)) ;;
       '(temp_266 : block_t) ←
        (array_new_ (default : uint8) (block_len_v)) ;;
       '(temp_268 : sha256_digest_t) ←
        (hash (k_260)) ;;
       '(temp_270 : seq uint8) ←
        (array_to_seq (temp_268)) ;;
       '(temp_272 : block_t) ←
        (array_update_start (temp_266) (temp_270)) ;;
       '(temp_274 : block_t) ←
        (array_new_ (default : uint8) (block_len_v)) ;;
       '(temp_276 : block_t) ←
        (array_update_start (temp_274) (k_260)) ;;
      @ret (block_t) ((if (temp_264):bool_ChoiceEquality then (*inline*) (
            temp_272) else (temp_276))) } : code (fset.fset0) [interface
      #val #[ HASH ] : hash_inp → hash_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_k_block : package _ _ _ :=
  (seq_link k_block link_rest(package_hash)).
Fail Next Obligation.

Definition h_in_300_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 312%nat)).
Definition h_in_288_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 313%nat)).
Notation "'hmac_inp'" := (
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'hmac_out'" := (prk_t : choice_type) (in custom pack_type at level 2).
Definition HMAC : nat :=
  (314).
Program Definition hmac
   : package (CEfset ([h_in_288_loc ; h_in_300_loc])) [interface
  #val #[ HASH ] : hash_inp → hash_out ;
  #val #[ K_BLOCK ] : k_block_inp → k_block_out ] [interface
  #val #[ HMAC ] : hmac_inp → hmac_out ] :=
  ([package #def #[ HMAC ] (temp_inp : hmac_inp) : hmac_out { 
    let '(k_278 , txt_289) := temp_inp : byte_seq '× byte_seq in
    #import {sig #[ HASH ] : hash_inp → hash_out } as hash ;;
    let hash := fun x_0 => hash (x_0) in
    #import {sig #[ K_BLOCK ] : k_block_inp → k_block_out } as k_block ;;
    let k_block := fun x_0 => k_block (x_0) in
    ({ code  '(k_block_281 : block_t) ←
        ( '(temp_280 : block_t) ←
            (k_block (k_278)) ;;
          ret (temp_280)) ;;
       '(h_in_288 : seq uint8) ←
          ( '(temp_283 : block_t) ←
              ((k_block_281) array_xor (i_pad_v)) ;;
             '(temp_285 : seq uint8) ←
              (array_to_seq (temp_283)) ;;
             '(temp_287 : byte_seq) ←
              (seq_from_seq (temp_285)) ;;
            ret (temp_287)) ;;
        #put h_in_288_loc := h_in_288 ;;
       '(h_in_288 : seq uint8) ←
          (( '(temp_291 : seq uint8) ←
                (seq_concat (h_in_288) (txt_289)) ;;
              ret (temp_291))) ;;
        #put h_in_288_loc := h_in_288 ;;
      
       '(h_inner_301 : sha256_digest_t) ←
        ( temp_293 ←
            (hash (h_in_288)) ;;
          ret (temp_293)) ;;
       '(h_in_300 : seq uint8) ←
          ( '(temp_295 : block_t) ←
              ((k_block_281) array_xor (o_pad_v)) ;;
             '(temp_297 : seq uint8) ←
              (array_to_seq (temp_295)) ;;
             '(temp_299 : byte_seq) ←
              (seq_from_seq (temp_297)) ;;
            ret (temp_299)) ;;
        #put h_in_300_loc := h_in_300 ;;
       '(h_in_300 : seq uint8) ←
          (( '(temp_303 : seq uint8) ←
                (array_to_seq (h_inner_301)) ;;
               '(temp_305 : seq uint8) ←
                (seq_concat (h_in_300) (temp_303)) ;;
              ret (temp_305))) ;;
        #put h_in_300_loc := h_in_300 ;;
      
       '(temp_307 : sha256_digest_t) ←
        (hash (h_in_300)) ;;
       '(temp_309 : seq uint8) ←
        (array_to_seq (temp_307)) ;;
       '(temp_311 : prk_t) ←
        (array_from_seq (hash_size_v) (temp_309)) ;;
      @ret (prk_t) (temp_311) } : code (CEfset (
          [h_in_288_loc ; h_in_300_loc])) [interface
      #val #[ HASH ] : hash_inp → hash_out ;
      #val #[ K_BLOCK ] : k_block_inp → k_block_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_hmac : package _ _ _ :=
  (seq_link hmac link_rest(package_hash,package_k_block)).
Fail Next Obligation.

