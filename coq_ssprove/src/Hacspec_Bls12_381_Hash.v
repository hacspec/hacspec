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

Require Import Hacspec_Bls12_381.

Require Import Hacspec_Lib.

Require Import Hacspec_Sha256.

Obligation Tactic := try timeout 130 solve_ssprove_obligations.

Definition fp_hash_canvas_t  :=
  (nseq (int8) (64)).
Definition fp_hash_t  :=
  (
    nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab).

Definition arr_fp_t  :=
  ( nseq (uint64) (usize 6)).

Definition b_in_bytes_v : (uint_size) :=
  ((usize 32)).

Definition s_in_bytes_v : (uint_size) :=
  ((usize 64)).

Definition l_v : (uint_size) :=
  ((usize 64)).

Definition p_1_2_v : (arr_fp_t) :=
  (let temp_1 : int64 :=
      (secret (@repr U64 936899308823769933)) in
    let temp_3 : int64 :=
      (secret (@repr U64 2706051889235351147)) in
    let temp_5 : int64 :=
      (secret (@repr U64 12843041017062132063)) in
    let temp_7 : int64 :=
      (secret (@repr U64 12941209323636816658)) in
    let temp_9 : int64 :=
      (secret (@repr U64 1105070755758604287)) in
    let temp_11 : int64 :=
      (secret (@repr U64 15924587544893707605)) in
    let temp_13 : nseq uint64 6 :=
      (array_from_list uint64 [temp_1; temp_3; temp_5; temp_7; temp_9; temp_11
        ]) in
    (temp_13)).

Definition p_1_4_v : (arr_fp_t) :=
  (let temp_15 : int64 :=
      (secret (@repr U64 468449654411884966)) in
    let temp_17 : int64 :=
      (secret (@repr U64 10576397981472451381)) in
    let temp_19 : int64 :=
      (secret (@repr U64 15644892545385841839)) in
    let temp_21 : int64 :=
      (secret (@repr U64 15693976698673184137)) in
    let temp_23 : int64 :=
      (secret (@repr U64 552535377879302143)) in
    let temp_25 : int64 :=
      (secret (@repr U64 17185665809301629611)) in
    let temp_27 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_15;
          temp_17;
          temp_19;
          temp_21;
          temp_23;
          temp_25
        ]) in
    (temp_27)).

Definition p_3_4_v : (arr_fp_t) :=
  (let temp_29 : int64 :=
      (secret (@repr U64 468449654411884966)) in
    let temp_31 : int64 :=
      (secret (@repr U64 10576397981472451381)) in
    let temp_33 : int64 :=
      (secret (@repr U64 15644892545385841839)) in
    let temp_35 : int64 :=
      (secret (@repr U64 15693976698673184137)) in
    let temp_37 : int64 :=
      (secret (@repr U64 552535377879302143)) in
    let temp_39 : int64 :=
      (secret (@repr U64 17185665809301629610)) in
    let temp_41 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_29;
          temp_31;
          temp_33;
          temp_35;
          temp_37;
          temp_39
        ]) in
    (temp_41)).
Infix "seq_xor" := seq_xor_ (at level 33) : hacspec_scope.

Definition l_i_b_str_70_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 131%nat)).
Definition b_i_100_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 132%nat)).
Definition uniform_bytes_124_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 133%nat)).
Notation "'expand_message_xmd_inp'" := (
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'expand_message_xmd_out'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition EXPAND_MESSAGE_XMD : nat :=
  (134).

Program Definition expand_message_xmd
   : package (CEfset (
      [l_i_b_str_70_loc ; b_i_100_loc ; uniform_bytes_124_loc])) [interface
  #val #[ HASH ] : hash_inp → hash_out ] [interface
  #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
  ] :=
  (
    [package #def #[ EXPAND_MESSAGE_XMD ] (temp_inp : expand_message_xmd_inp) : expand_message_xmd_out { 
    let '(
      msg_67 , dst_49 , len_in_bytes_42) := temp_inp : byte_seq '× byte_seq '× uint_size in
    #import {sig #[ HASH ] : hash_inp → hash_out } as  hash ;;
    let hash := fun x_0 => hash (x_0) in
    ({ code  '(ell_103 : uint_size) ←
        ( '(temp_44 : uint_size) ←
            ((len_in_bytes_42) .+ (b_in_bytes_v)) ;;
           '(temp_46 : uint_size) ←
            ((temp_44) .- (usize 1)) ;;
           '(temp_48 : uint_size) ←
            ((temp_46) ./ (b_in_bytes_v)) ;;
          ret (temp_48)) ;;
       '(dst_prime_77 : seq uint8) ←
        ( '(temp_51 : uint_size) ←
            (seq_len (dst_49)) ;;
           temp_53 ←
            (lift_to_both0 (uint8_from_usize (temp_51))) ;;
           '(temp_55 : byte_seq) ←
            (seq_push_pre (dst_49) (temp_53)) ;;
          ret (temp_55)) ;;
       '(z_pad_66 : seq uint8) ←
        ( temp_57 ←
            (seq_new_ (default : uint8) (s_in_bytes_v)) ;;
          ret (temp_57)) ;;
       '(l_i_b_str_70 : seq uint8) ←
          ( temp_59 ←
              (seq_new_ (default : uint8) (usize 2)) ;;
            ret (temp_59)) ;;
        #put l_i_b_str_70_loc := l_i_b_str_70 ;;
       '(l_i_b_str_70 : seq uint8) ←
        ( '(temp_61 : uint_size) ←
            ((len_in_bytes_42) ./ (usize 256)) ;;
           temp_63 ←
            (lift_to_both0 (uint8_from_usize (temp_61))) ;;
          ret (seq_upd l_i_b_str_70 (usize 0) (temp_63))) ;;
      
       '(l_i_b_str_70 : seq uint8) ←
        ( temp_65 ←
            (lift_to_both0 (uint8_from_usize (len_in_bytes_42))) ;;
          ret (seq_upd l_i_b_str_70 (usize 1) (temp_65))) ;;
      
       '(msg_prime_80 : seq uint8) ←
        ( '(temp_69 : seq uint8) ←
            (seq_concat (z_pad_66) (msg_67)) ;;
           '(temp_72 : seq uint8) ←
            (seq_concat (temp_69) (l_i_b_str_70)) ;;
           temp_74 ←
            (seq_new_ (default : uint8) (usize 1)) ;;
           '(temp_76 : seq uint8) ←
            (seq_concat (temp_72) (temp_74)) ;;
           '(temp_79 : seq uint8) ←
            (seq_concat (temp_76) (dst_prime_77)) ;;
          ret (temp_79)) ;;
       '(b_0_87 : seq uint8) ←
        ( '(temp_82 : sha256_digest_t) ←
            (hash (msg_prime_80)) ;;
           '(temp_84 : seq uint8) ←
            (array_to_seq (temp_82)) ;;
           '(temp_86 : byte_seq) ←
            (seq_from_seq (temp_84)) ;;
          ret (temp_86)) ;;
       '(b_i_100 : seq uint8) ←
          ( '(temp_89 : int8) ←
              (secret (@repr U8 1)) ;;
             '(temp_91 : seq uint8) ←
              (seq_push_pre (b_0_87) (temp_89)) ;;
             '(temp_93 : seq uint8) ←
              (seq_concat (temp_91) (dst_prime_77)) ;;
             '(temp_95 : sha256_digest_t) ←
              (hash (temp_93)) ;;
             '(temp_97 : seq uint8) ←
              (array_to_seq (temp_95)) ;;
             '(temp_99 : byte_seq) ←
              (seq_from_seq (temp_97)) ;;
            ret (temp_99)) ;;
        #put b_i_100_loc := b_i_100 ;;
       '(uniform_bytes_124 : seq uint8) ←
          ( '(temp_102 : byte_seq) ←
              (seq_from_seq (b_i_100)) ;;
            ret (temp_102)) ;;
        #put uniform_bytes_124_loc := uniform_bytes_124 ;;
       '(temp_105 : uint_size) ←
        ((ell_103) .+ (usize 1)) ;;
       temp_130 ←
        (foldi' (usize 2) (temp_105) prod_ce(b_i_100, uniform_bytes_124) (
              L2 := CEfset (
                [l_i_b_str_70_loc ; b_i_100_loc ; uniform_bytes_124_loc])) (
              I2 := [interface #val #[ HASH ] : hash_inp → hash_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_111 '(
              b_i_100,
              uniform_bytes_124
            ) =>
            ({ code  '(t_108 : seq uint8) ←
                ( '(temp_107 : byte_seq) ←
                    (seq_from_seq (b_0_87)) ;;
                  ret (temp_107)) ;;
               '(b_i_100 : seq uint8) ←
                  (( '(temp_110 : seq uint8) ←
                        ((t_108) seq_xor (b_i_100)) ;;
                       '(temp_113 : uint8) ←
                        (lift_to_both0 (uint8_from_usize (i_111))) ;;
                       '(temp_115 : seq uint8) ←
                        (seq_push_pre (temp_110) (temp_113)) ;;
                       '(temp_117 : seq uint8) ←
                        (seq_concat (temp_115) (dst_prime_77)) ;;
                       '(temp_119 : sha256_digest_t) ←
                        (hash (temp_117)) ;;
                       '(temp_121 : seq uint8) ←
                        (array_to_seq (temp_119)) ;;
                       '(temp_123 : byte_seq) ←
                        (seq_from_seq (temp_121)) ;;
                      ret (temp_123))) ;;
                #put b_i_100_loc := b_i_100 ;;
              
               '(uniform_bytes_124 : seq uint8) ←
                  (( '(temp_126 : seq uint8) ←
                        (seq_concat (uniform_bytes_124) (b_i_100)) ;;
                      ret (temp_126))) ;;
                #put uniform_bytes_124_loc := uniform_bytes_124 ;;
              
              @ret ((seq uint8 '× seq uint8)) (prod_ce(
                  b_i_100,
                  uniform_bytes_124
                )) } : code (CEfset (
                  [l_i_b_str_70_loc ; b_i_100_loc ; uniform_bytes_124_loc])) [interface
              #val #[ HASH ] : hash_inp → hash_out ] _))) ;;
      let '(b_i_100, uniform_bytes_124) :=
        (temp_130) : (seq uint8 '× seq uint8) in
      
       temp_128 ←
        (seq_truncate (uniform_bytes_124) (len_in_bytes_42)) ;;
      @ret (seq uint8) (temp_128) } : code (CEfset (
          [l_i_b_str_70_loc ; b_i_100_loc ; uniform_bytes_124_loc])) [interface
      #val #[ HASH ] : hash_inp → hash_out ] _)
  }]).
Fail Next Obligation.
Program Definition package_expand_message_xmd : package _ _ _ :=
  (seq_link expand_message_xmd link_rest(package_hash)).
Fail Next Obligation.

Definition output_162_loc : ChoiceEqualityLocation :=
  ((seq fp_t ; 163%nat)).
Notation "'fp_hash_to_field_inp'" := (
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'fp_hash_to_field_out'" := (
  seq fp_t : choice_type) (in custom pack_type at level 2).
Definition FP_HASH_TO_FIELD : nat :=
  (164).
Program Definition fp_hash_to_field
   : package (CEfset ([output_162_loc])) [interface
  #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
  ] [interface
  #val #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out
  ] :=
  (
    [package #def #[ FP_HASH_TO_FIELD ] (temp_inp : fp_hash_to_field_inp) : fp_hash_to_field_out { 
    let '(
      msg_138 , dst_139 , count_135) := temp_inp : byte_seq '× byte_seq '× uint_size in
    #import {sig #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out } as  expand_message_xmd ;;
    let expand_message_xmd := fun x_0 x_1 x_2 => expand_message_xmd (
      x_0,x_1,x_2) in
    ({ code  '(len_in_bytes_140 : uint_size) ←
        ( '(temp_137 : uint_size) ←
            ((count_135) .* (l_v)) ;;
          ret (temp_137)) ;;
       '(uniform_bytes_148 : seq uint8) ←
        ( '(temp_142 : byte_seq) ←
            (expand_message_xmd (msg_138) (dst_139) (len_in_bytes_140)) ;;
          ret (temp_142)) ;;
       '(output_162 : seq fp_t) ←
          ( temp_144 ←
              (seq_new_ (default : fp_t) (count_135)) ;;
            ret (temp_144)) ;;
        #put output_162_loc := output_162 ;;
       '(output_162 : (seq fp_t)) ←
        (foldi' (usize 0) (count_135) output_162 (L2 := CEfset (
                [output_162_loc])) (I2 := [interface
              #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_145 output_162 =>
            ({ code  '(elm_offset_149 : uint_size) ←
                ( '(temp_147 : uint_size) ←
                    ((l_v) .* (i_145)) ;;
                  ret (temp_147)) ;;
               '(tv_152 : seq uint8) ←
                ( '(temp_151 : seq uint8) ←
                    (seq_slice (uniform_bytes_148) (elm_offset_149) (l_v)) ;;
                  ret (temp_151)) ;;
               '(u_i_161 : fp_t) ←
                ( '(temp_154 : fp_hash_t) ←
                    (nat_mod_from_byte_seq_be (tv_152)) ;;
                   '(temp_156 : seq uint8) ←
                    (nat_mod_to_byte_seq_be (temp_154)) ;;
                   '(temp_158 : seq uint8) ←
                    (seq_slice (temp_156) (usize 16) (usize 48)) ;;
                   '(temp_160 : fp_t) ←
                    (nat_mod_from_byte_seq_be (temp_158)) ;;
                  ret (temp_160)) ;;
               '(output_162 : seq fp_t) ←
                (ret (seq_upd output_162 (i_145) (u_i_161))) ;;
              
              @ret ((seq fp_t)) (output_162) } : code (CEfset (
                  [output_162_loc])) [interface  ] _))) ;;
      
      @ret (seq fp_t) (output_162) } : code (CEfset (
          [output_162_loc])) [interface
      #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp_hash_to_field : package _ _ _ :=
  (seq_link fp_hash_to_field link_rest(package_expand_message_xmd)).
Fail Next Obligation.


Definition nat_mod_rem {n : Z} (a:nat_mod n) (b:nat_mod n) : both0 (nat_mod n) :=
  lift_to_both (nat_mod_rem a b).
Infix "rem" := nat_mod_rem (at level 33) : hacspec_scope.

Notation "'fp_sgn0_inp'" := (
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_sgn0_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition FP_SGN0 : nat :=
  (174).
Program Definition fp_sgn0
   : package (fset.fset0) [interface  ] [interface
  #val #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out ] :=
  ([package #def #[ FP_SGN0 ] (temp_inp : fp_sgn0_inp) : fp_sgn0_out { 
    let '(x_165) := temp_inp : fp_t in
    ({ code  '(temp_167 : fp_t) ←
        (nat_mod_two ) ;;
       '(temp_169 : fp_t) ←
        ((x_165) rem (temp_167)) ;;
       '(temp_171 : fp_t) ←
        (nat_mod_one ) ;;
       '(temp_173 : bool_ChoiceEquality) ←
        ((temp_169) =.? (temp_171)) ;;
      @ret (bool_ChoiceEquality) (temp_173) } : code (fset.fset0) [interface 
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp_sgn0 : package _ _ _ :=
  (fp_sgn0).
Fail Next Obligation.

Definition nat_mod_pow_self {p} (a n : nat_mod p) := @nat_mod_exp_def p a (Z.to_nat (ssreflect.fintype.nat_of_ord n)).

Notation "'fp_is_square_inp'" := (
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_is_square_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition FP_IS_SQUARE : nat :=
  (194).
Program Definition fp_is_square
   : package (fset.fset0) [interface  ] [interface
  #val #[ FP_IS_SQUARE ] : fp_is_square_inp → fp_is_square_out ] :=
  (
    [package #def #[ FP_IS_SQUARE ] (temp_inp : fp_is_square_inp) : fp_is_square_out { 
    let '(x_179) := temp_inp : fp_t in
    ({ code  '(c1_180 : fp_t) ←
        ( '(temp_176 : seq int8) ←
            (array_to_be_bytes (p_1_2_v)) ;;
           '(temp_178 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_176)) ;;
          ret (temp_178)) ;;
       '(tv_183 : fp_t) ←
        ( temp_182 ←
            (nat_mod_pow_self (x_179) (c1_180)) ;;
          ret (temp_182)) ;;
       '(temp_185 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_187 : bool_ChoiceEquality) ←
        ((tv_183) =.? (temp_185)) ;;
       '(temp_189 : fp_t) ←
        (nat_mod_one ) ;;
       '(temp_191 : bool_ChoiceEquality) ←
        ((tv_183) =.? (temp_189)) ;;
       '(temp_193 : bool_ChoiceEquality) ←
        ((temp_187) || (temp_191)) ;;
      @ret (bool_ChoiceEquality) (temp_193) } : code (fset.fset0) [interface 
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp_is_square : package _ _ _ :=
  (fp_is_square).
Fail Next Obligation.


Notation "'fp_sqrt_inp'" := (
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_sqrt_out'" := (
  fp_t : choice_type) (in custom pack_type at level 2).
Definition FP_SQRT : nat :=
  (203).
Program Definition fp_sqrt
   : package (fset.fset0) [interface  ] [interface
  #val #[ FP_SQRT ] : fp_sqrt_inp → fp_sqrt_out ] :=
  ([package #def #[ FP_SQRT ] (temp_inp : fp_sqrt_inp) : fp_sqrt_out { 
    let '(x_199) := temp_inp : fp_t in
    ({ code  '(c1_200 : fp_t) ←
        ( '(temp_196 : seq int8) ←
            (array_to_be_bytes (p_1_4_v)) ;;
           '(temp_198 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_196)) ;;
          ret (temp_198)) ;;
       temp_202 ←
        (nat_mod_pow_self (x_199) (c1_200)) ;;
      @ret (fp_t) (temp_202) } : code (fset.fset0) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp_sqrt : package _ _ _ :=
  (fp_sqrt).
Fail Next Obligation.


Notation "'g1_curve_func_inp'" := (
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_curve_func_out'" := (
  fp_t : choice_type) (in custom pack_type at level 2).
Definition G1_CURVE_FUNC : nat :=
  (213).
Program Definition g1_curve_func
   : package (fset.fset0) [interface  ] [interface
  #val #[ G1_CURVE_FUNC ] : g1_curve_func_inp → g1_curve_func_out ] :=
  (
    [package #def #[ G1_CURVE_FUNC ] (temp_inp : g1_curve_func_inp) : g1_curve_func_out { 
    let '(x_204) := temp_inp : fp_t in
    ({ code  '(temp_206 : fp_t) ←
        ((x_204) *% (x_204)) ;;
       '(temp_208 : fp_t) ←
        ((temp_206) *% (x_204)) ;;
       '(temp_210 : fp_t) ←
        (nat_mod_from_literal (_) (@repr U128 4)) ;;
       '(temp_212 : fp_t) ←
        ((temp_208) +% (temp_210)) ;;
      @ret (fp_t) (temp_212) } : code (fset.fset0) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_g1_curve_func : package _ _ _ :=
  (g1_curve_func).
Fail Next Obligation.

Definition y_348_loc : ChoiceEqualityLocation :=
  ((fp_t ; 357%nat)).
Definition tv4_258_loc : ChoiceEqualityLocation :=
  ((fp_t ; 358%nat)).
Notation "'g1_map_to_curve_svdw_inp'" := (
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_map_to_curve_svdw_out'" := (
  g1_t : choice_type) (in custom pack_type at level 2).
Definition G1_MAP_TO_CURVE_SVDW : nat :=
  (359).

Obligation Tactic := try timeout 460 solve_ssprove_obligations.

Time Program Definition g1_map_to_curve_svdw
   : package (CEfset ([tv4_258_loc ; y_348_loc])) [interface
  #val #[ FP_IS_SQUARE ] : fp_is_square_inp → fp_is_square_out ;
  #val #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out ;
  #val #[ FP_SQRT ] : fp_sqrt_inp → fp_sqrt_out ;
  #val #[ G1_CURVE_FUNC ] : g1_curve_func_inp → g1_curve_func_out ] [interface
  #val #[ G1_MAP_TO_CURVE_SVDW ] : g1_map_to_curve_svdw_inp → g1_map_to_curve_svdw_out
  ] :=
  (
    [package #def #[ G1_MAP_TO_CURVE_SVDW ] (temp_inp : g1_map_to_curve_svdw_inp) : g1_map_to_curve_svdw_out { 
    let '(u_223) := temp_inp : fp_t in
    #import {sig #[ FP_IS_SQUARE ] : fp_is_square_inp → fp_is_square_out } as  fp_is_square ;;
    let fp_is_square := fun x_0 => fp_is_square (x_0) in
    #import {sig #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out } as  fp_sgn0 ;;
    let fp_sgn0 := fun x_0 => fp_sgn0 (x_0) in
    #import {sig #[ FP_SQRT ] : fp_sqrt_inp → fp_sqrt_out } as  fp_sqrt ;;
    let fp_sqrt := fun x_0 => fp_sqrt (x_0) in
    #import {sig #[ G1_CURVE_FUNC ] : g1_curve_func_inp → g1_curve_func_out } as  g1_curve_func ;;
    let g1_curve_func := fun x_0 => g1_curve_func (x_0) in
    ({ code  '(z_220 : fp_t) ←
        ( '(temp_215 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_217 : fp_t) ←
            (nat_mod_from_literal (_) (@repr U128 3)) ;;
           '(temp_219 : fp_t) ←
            ((temp_215) -% (temp_217)) ;;
          ret (temp_219)) ;;
       '(gz_226 : fp_t) ←
        ( '(temp_222 : fp_t) ←
            (g1_curve_func (z_220)) ;;
          ret (temp_222)) ;;
       '(tv1_231 : fp_t) ←
        ( '(temp_225 : fp_t) ←
            ((u_223) *% (u_223)) ;;
           '(temp_228 : fp_t) ←
            ((temp_225) *% (gz_226)) ;;
          ret (temp_228)) ;;
       '(tv2_239 : fp_t) ←
        ( '(temp_230 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_233 : fp_t) ←
            ((temp_230) +% (tv1_231)) ;;
          ret (temp_233)) ;;
       '(tv1_238 : fp_t) ←
        ( '(temp_235 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_237 : fp_t) ←
            ((temp_235) -% (tv1_231)) ;;
          ret (temp_237)) ;;
       '(tv3_267 : fp_t) ←
        ( '(temp_241 : fp_t) ←
            ((tv1_238) *% (tv2_239)) ;;
           temp_243 ←
            (nat_mod_inv (temp_241)) ;;
          ret (temp_243)) ;;
       '(tv4_258 : fp_t) ←
          ( '(temp_245 : fp_t) ←
              (nat_mod_zero ) ;;
             '(temp_247 : fp_t) ←
              ((temp_245) -% (gz_226)) ;;
             '(temp_249 : fp_t) ←
              (nat_mod_from_literal (_) (@repr U128 3)) ;;
             '(temp_251 : fp_t) ←
              ((temp_249) *% (z_220)) ;;
             '(temp_253 : fp_t) ←
              ((temp_251) *% (z_220)) ;;
             '(temp_255 : fp_t) ←
              ((temp_247) *% (temp_253)) ;;
             '(temp_257 : fp_t) ←
              (fp_sqrt (temp_255)) ;;
            ret (temp_257)) ;;
        #put tv4_258_loc := tv4_258 ;;
       '(temp_260 : bool_ChoiceEquality) ←
        (fp_sgn0 (tv4_258)) ;;
       '(tv4_258 : (fp_t)) ←
        (if temp_260:bool_ChoiceEquality
          then (({ code  '(tv4_258 : fp_t) ←
                  (( '(temp_262 : fp_t) ←
                        (nat_mod_zero ) ;;
                       '(temp_264 : fp_t) ←
                        ((temp_262) -% (tv4_258)) ;;
                      ret (temp_264))) ;;
                #put tv4_258_loc := tv4_258 ;;
              
              @ret ((fp_t)) (tv4_258) } : code (CEfset (
                  [tv4_258_loc])) [interface  ] _))
          else @ret ((fp_t)) (tv4_258)) ;;
      
       '(tv5_300 : fp_t) ←
        ( '(temp_266 : fp_t) ←
            ((u_223) *% (tv1_238)) ;;
           '(temp_269 : fp_t) ←
            ((temp_266) *% (tv3_267)) ;;
           '(temp_271 : fp_t) ←
            ((temp_269) *% (tv4_258)) ;;
          ret (temp_271)) ;;
       '(tv6_315 : fp_t) ←
        ( '(temp_273 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_275 : fp_t) ←
            (nat_mod_from_literal (_) (@repr U128 4)) ;;
           '(temp_277 : fp_t) ←
            ((temp_273) -% (temp_275)) ;;
           '(temp_279 : fp_t) ←
            ((temp_277) *% (gz_226)) ;;
           '(temp_281 : fp_t) ←
            (nat_mod_from_literal (_) (@repr U128 3)) ;;
           '(temp_283 : fp_t) ←
            ((temp_281) *% (z_220)) ;;
           '(temp_285 : fp_t) ←
            ((temp_283) *% (z_220)) ;;
           temp_287 ←
            (nat_mod_inv (temp_285)) ;;
           '(temp_289 : fp_t) ←
            ((temp_279) *% (temp_287)) ;;
          ret (temp_289)) ;;
       '(x1_330 : fp_t) ←
        ( '(temp_291 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_293 : fp_t) ←
            ((temp_291) -% (z_220)) ;;
           '(temp_295 : fp_t) ←
            (nat_mod_two ) ;;
           temp_297 ←
            (nat_mod_inv (temp_295)) ;;
           '(temp_299 : fp_t) ←
            ((temp_293) *% (temp_297)) ;;
           '(temp_302 : fp_t) ←
            ((temp_299) -% (tv5_300)) ;;
          ret (temp_302)) ;;
       '(x2_335 : fp_t) ←
        ( '(temp_304 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_306 : fp_t) ←
            ((temp_304) -% (z_220)) ;;
           '(temp_308 : fp_t) ←
            (nat_mod_two ) ;;
           temp_310 ←
            (nat_mod_inv (temp_308)) ;;
           '(temp_312 : fp_t) ←
            ((temp_306) *% (temp_310)) ;;
           '(temp_314 : fp_t) ←
            ((temp_312) +% (tv5_300)) ;;
          ret (temp_314)) ;;
       '(x3_340 : fp_t) ←
        ( '(temp_317 : fp_t) ←
            ((tv2_239) *% (tv2_239)) ;;
           '(temp_319 : fp_t) ←
            ((temp_317) *% (tv3_267)) ;;
           '(temp_321 : fp_t) ←
            ((tv6_315) *% (temp_319)) ;;
           '(temp_323 : fp_t) ←
            ((tv2_239) *% (tv2_239)) ;;
           '(temp_325 : fp_t) ←
            ((temp_323) *% (tv3_267)) ;;
           '(temp_327 : fp_t) ←
            ((temp_321) *% (temp_325)) ;;
           '(temp_329 : fp_t) ←
            ((z_220) +% (temp_327)) ;;
          ret (temp_329)) ;;
       '(x_341 : fp_t) ←
        ( '(temp_332 : fp_t) ←
            (g1_curve_func (x1_330)) ;;
           '(temp_334 : bool_ChoiceEquality) ←
            (fp_is_square (temp_332)) ;;
           '(temp_337 : fp_t) ←
            (g1_curve_func (x2_335)) ;;
           '(temp_339 : bool_ChoiceEquality) ←
            (fp_is_square (temp_337)) ;;
          ret ((if (temp_334):bool_ChoiceEquality then (x1_330) else ((if (
                    temp_339):bool_ChoiceEquality then (x2_335) else (
                    x3_340)))))) ;;
       '(y_348 : fp_t) ←
          ( '(temp_343 : fp_t) ←
              (g1_curve_func (x_341)) ;;
             '(temp_345 : fp_t) ←
              (fp_sqrt (temp_343)) ;;
            ret (temp_345)) ;;
        #put y_348_loc := y_348 ;;
       '(temp_347 : bool_ChoiceEquality) ←
        (fp_sgn0 (u_223)) ;;
       '(temp_350 : bool_ChoiceEquality) ←
        (fp_sgn0 (y_348)) ;;
       '(temp_352 : bool_ChoiceEquality) ←
        ((temp_347) !=.? (temp_350)) ;;
       '(y_348 : (fp_t)) ←
        (if temp_352:bool_ChoiceEquality
          then (({ code  '(y_348 : fp_t) ←
                  (( '(temp_354 : fp_t) ←
                        (nat_mod_zero ) ;;
                       '(temp_356 : fp_t) ←
                        ((temp_354) -% (y_348)) ;;
                      ret (temp_356))) ;;
                #put y_348_loc := y_348 ;;
              
              @ret ((fp_t)) (y_348) } : code (CEfset (
                  [tv4_258_loc ; y_348_loc])) [interface  ] _))
          else @ret ((fp_t)) (y_348)) ;;
      
      @ret ((fp_t '× fp_t '× bool_ChoiceEquality)) (prod_ce(
          x_341,
          y_348,
          (false : bool_ChoiceEquality)
        )) } : code (CEfset ([tv4_258_loc ; y_348_loc])) [interface
      #val #[ FP_IS_SQUARE ] : fp_is_square_inp → fp_is_square_out ;
      #val #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out ;
      #val #[ FP_SQRT ] : fp_sqrt_inp → fp_sqrt_out ;
      #val #[ G1_CURVE_FUNC ] : g1_curve_func_inp → g1_curve_func_out ] _)
  }]).
Fail Next Obligation.
Program Definition package_g1_map_to_curve_svdw : package _ _ _ :=
  (seq_link g1_map_to_curve_svdw link_rest(
      package_fp_is_square,package_fp_sgn0,package_fp_sqrt,package_g1_curve_func)).
Fail Next Obligation.


Notation "'g1_clear_cofactor_inp'" := (
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_clear_cofactor_out'" := (
  g1_t : choice_type) (in custom pack_type at level 2).
Definition G1_CLEAR_COFACTOR : nat :=
  (366).
Program Definition g1_clear_cofactor
   : package (fset.fset0) [interface #val #[ G1MUL ] : g1mul_inp → g1mul_out
  ] [interface
  #val #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out
  ] :=
  (
    [package #def #[ G1_CLEAR_COFACTOR ] (temp_inp : g1_clear_cofactor_inp) : g1_clear_cofactor_out { 
    let '(x_363) := temp_inp : g1_t in
    #import {sig #[ G1MUL ] : g1mul_inp → g1mul_out } as  g1mul ;;
    let g1mul := fun x_0 x_1 => g1mul (x_0,x_1) in
    ({ code  '(h_eff_362 : scalar_t) ←
        ( '(temp_361 : scalar_t) ←
            (nat_mod_from_literal (_) (@repr U128 15132376222941642753)) ;;
          ret (temp_361)) ;;
       temp_365 ←
        (g1mul (h_eff_362) (x_363)) ;;
      @ret ((fp_t '× fp_t '× bool_ChoiceEquality)) (temp_365) } : code (
        fset.fset0) [interface #val #[ G1MUL ] : g1mul_inp → g1mul_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_g1_clear_cofactor : package _ _ _ :=
  (seq_link g1_clear_cofactor link_rest(package_g1mul)).
Fail Next Obligation.


Notation "'g1_hash_to_curve_svdw_inp'" := (
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g1_hash_to_curve_svdw_out'" := (
  g1_t : choice_type) (in custom pack_type at level 2).
Definition G1_HASH_TO_CURVE_SVDW : nat :=
  (388).
Program Definition g1_hash_to_curve_svdw
   : package (CEfset ([])) [interface
  #val #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out ;
  #val #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out ;
  #val #[ G1_MAP_TO_CURVE_SVDW ] : g1_map_to_curve_svdw_inp → g1_map_to_curve_svdw_out ;
  #val #[ G1ADD ] : g1add_inp → g1add_out ] [interface
  #val #[ G1_HASH_TO_CURVE_SVDW ] : g1_hash_to_curve_svdw_inp → g1_hash_to_curve_svdw_out
  ] :=
  (
    [package #def #[ G1_HASH_TO_CURVE_SVDW ] (temp_inp : g1_hash_to_curve_svdw_inp) : g1_hash_to_curve_svdw_out { 
    let '(msg_367 , dst_368) := temp_inp : byte_seq '× byte_seq in
    #import {sig #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out } as  fp_hash_to_field ;;
    let fp_hash_to_field := fun x_0 x_1 x_2 => fp_hash_to_field (x_0,x_1,x_2) in
    #import {sig #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out } as  g1_clear_cofactor ;;
    let g1_clear_cofactor := fun x_0 => g1_clear_cofactor (x_0) in
    #import {sig #[ G1_MAP_TO_CURVE_SVDW ] : g1_map_to_curve_svdw_inp → g1_map_to_curve_svdw_out } as  g1_map_to_curve_svdw ;;
    let g1_map_to_curve_svdw := fun x_0 => g1_map_to_curve_svdw (x_0) in
    #import {sig #[ G1ADD ] : g1add_inp → g1add_out } as  g1add ;;
    let g1add := fun x_0 x_1 => g1add (x_0,x_1) in
    ({ code  '(u_372 : seq fp_t) ←
        ( '(temp_370 : seq fp_t) ←
            (fp_hash_to_field (msg_367) (dst_368) (usize 2)) ;;
          ret (temp_370)) ;;
       '(q0_380 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( '(temp_373 : fp_t) ←
            (seq_index (u_372) (usize 0)) ;;
           '(temp_375 : g1_t) ←
            (g1_map_to_curve_svdw (temp_373)) ;;
          ret (temp_375)) ;;
       '(q1_381 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( '(temp_377 : fp_t) ←
            (seq_index (u_372) (usize 1)) ;;
           '(temp_379 : g1_t) ←
            (g1_map_to_curve_svdw (temp_377)) ;;
          ret (temp_379)) ;;
       '(r_384 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( temp_383 ←
            (g1add (q0_380) (q1_381)) ;;
          ret (temp_383)) ;;
       '(p_387 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( '(temp_386 : g1_t) ←
            (g1_clear_cofactor (r_384)) ;;
          ret (temp_386)) ;;
      @ret ((fp_t '× fp_t '× bool_ChoiceEquality)) (p_387) } : code (CEfset (
          [])) [interface
      #val #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out ;
      #val #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out ;
      #val #[ G1_MAP_TO_CURVE_SVDW ] : g1_map_to_curve_svdw_inp → g1_map_to_curve_svdw_out ;
      #val #[ G1ADD ] : g1add_inp → g1add_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_g1_hash_to_curve_svdw : package _ _ _ :=
  (seq_link g1_hash_to_curve_svdw link_rest(
      package_fp_hash_to_field,package_g1_clear_cofactor,package_g1_map_to_curve_svdw,package_g1add)).
Fail Next Obligation.


Notation "'g1_encode_to_curve_svdw_inp'" := (
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g1_encode_to_curve_svdw_out'" := (
  g1_t : choice_type) (in custom pack_type at level 2).
Definition G1_ENCODE_TO_CURVE_SVDW : nat :=
  (402).
Program Definition g1_encode_to_curve_svdw
   : package (CEfset ([])) [interface
  #val #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out ;
  #val #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out ;
  #val #[ G1_MAP_TO_CURVE_SVDW ] : g1_map_to_curve_svdw_inp → g1_map_to_curve_svdw_out
  ] [interface
  #val #[ G1_ENCODE_TO_CURVE_SVDW ] : g1_encode_to_curve_svdw_inp → g1_encode_to_curve_svdw_out
  ] :=
  (
    [package #def #[ G1_ENCODE_TO_CURVE_SVDW ] (temp_inp : g1_encode_to_curve_svdw_inp) : g1_encode_to_curve_svdw_out { 
    let '(msg_389 , dst_390) := temp_inp : byte_seq '× byte_seq in
    #import {sig #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out } as  fp_hash_to_field ;;
    let fp_hash_to_field := fun x_0 x_1 x_2 => fp_hash_to_field (x_0,x_1,x_2) in
    #import {sig #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out } as  g1_clear_cofactor ;;
    let g1_clear_cofactor := fun x_0 => g1_clear_cofactor (x_0) in
    #import {sig #[ G1_MAP_TO_CURVE_SVDW ] : g1_map_to_curve_svdw_inp → g1_map_to_curve_svdw_out } as  g1_map_to_curve_svdw ;;
    let g1_map_to_curve_svdw := fun x_0 => g1_map_to_curve_svdw (x_0) in
    ({ code  '(u_394 : seq fp_t) ←
        ( '(temp_392 : seq fp_t) ←
            (fp_hash_to_field (msg_389) (dst_390) (usize 1)) ;;
          ret (temp_392)) ;;
       '(q_398 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( '(temp_395 : fp_t) ←
            (seq_index (u_394) (usize 0)) ;;
           '(temp_397 : g1_t) ←
            (g1_map_to_curve_svdw (temp_395)) ;;
          ret (temp_397)) ;;
       '(p_401 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( '(temp_400 : g1_t) ←
            (g1_clear_cofactor (q_398)) ;;
          ret (temp_400)) ;;
      @ret ((fp_t '× fp_t '× bool_ChoiceEquality)) (p_401) } : code (CEfset (
          [])) [interface
      #val #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out ;
      #val #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out ;
      #val #[ G1_MAP_TO_CURVE_SVDW ] : g1_map_to_curve_svdw_inp → g1_map_to_curve_svdw_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_g1_encode_to_curve_svdw : package _ _ _ :=
  (seq_link g1_encode_to_curve_svdw link_rest(
      package_fp_hash_to_field,package_g1_clear_cofactor,package_g1_map_to_curve_svdw)).
Fail Next Obligation.

Definition output_453_loc : ChoiceEqualityLocation :=
  ((seq (fp_t '× fp_t) ; 454%nat)).
Notation "'fp2_hash_to_field_inp'" := (
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'fp2_hash_to_field_out'" := (
  seq fp2_t : choice_type) (in custom pack_type at level 2).
Definition FP2_HASH_TO_FIELD : nat :=
  (455).
Program Definition fp2_hash_to_field
   : package (CEfset ([output_453_loc])) [interface
  #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
  ] [interface
  #val #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out
  ] :=
  (
    [package #def #[ FP2_HASH_TO_FIELD ] (temp_inp : fp2_hash_to_field_inp) : fp2_hash_to_field_out { 
    let '(
      msg_408 , dst_409 , count_403) := temp_inp : byte_seq '× byte_seq '× uint_size in
    #import {sig #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out } as  expand_message_xmd ;;
    let expand_message_xmd := fun x_0 x_1 x_2 => expand_message_xmd (
      x_0,x_1,x_2) in
    ({ code  '(len_in_bytes_410 : uint_size) ←
        ( '(temp_405 : uint_size) ←
            ((count_403) .* (usize 2)) ;;
           '(temp_407 : uint_size) ←
            ((temp_405) .* (l_v)) ;;
          ret (temp_407)) ;;
       '(uniform_bytes_420 : seq uint8) ←
        ( '(temp_412 : byte_seq) ←
            (expand_message_xmd (msg_408) (dst_409) (len_in_bytes_410)) ;;
          ret (temp_412)) ;;
       '(output_453 : seq (fp_t '× fp_t)) ←
          ( temp_414 ←
              (seq_new_ (default : fp2_t) (count_403)) ;;
            ret (temp_414)) ;;
        #put output_453_loc := output_453 ;;
       '(output_453 : (seq (fp_t '× fp_t))) ←
        (foldi' (usize 0) (count_403) output_453 (L2 := CEfset (
                [output_453_loc])) (I2 := [interface
              #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_415 output_453 =>
            ({ code  '(elm_offset_421 : uint_size) ←
                ( '(temp_417 : uint_size) ←
                    ((l_v) .* (i_415)) ;;
                   '(temp_419 : uint_size) ←
                    ((temp_417) .* (usize 2)) ;;
                  ret (temp_419)) ;;
               '(tv_424 : seq uint8) ←
                ( '(temp_423 : seq uint8) ←
                    (seq_slice (uniform_bytes_420) (elm_offset_421) (l_v)) ;;
                  ret (temp_423)) ;;
               '(e_1_451 : fp_t) ←
                ( '(temp_426 : fp_hash_t) ←
                    (nat_mod_from_byte_seq_be (tv_424)) ;;
                   '(temp_428 : seq int8) ←
                    (nat_mod_to_byte_seq_be (temp_426)) ;;
                   '(temp_430 : seq uint8) ←
                    (seq_slice (temp_428) (usize 16) (usize 48)) ;;
                   '(temp_432 : fp_t) ←
                    (nat_mod_from_byte_seq_be (temp_430)) ;;
                  ret (temp_432)) ;;
               '(elm_offset_439 : uint_size) ←
                ( '(temp_434 : uint_size) ←
                    ((i_415) .* (usize 2)) ;;
                   '(temp_436 : uint_size) ←
                    ((usize 1) .+ (temp_434)) ;;
                   '(temp_438 : uint_size) ←
                    ((l_v) .* (temp_436)) ;;
                  ret (temp_438)) ;;
               '(tv_442 : seq uint8) ←
                ( '(temp_441 : seq uint8) ←
                    (seq_slice (uniform_bytes_420) (elm_offset_439) (l_v)) ;;
                  ret (temp_441)) ;;
               '(e_2_452 : fp_t) ←
                ( '(temp_444 : fp_hash_t) ←
                    (nat_mod_from_byte_seq_be (tv_442)) ;;
                   '(temp_446 : seq int8) ←
                    (nat_mod_to_byte_seq_be (temp_444)) ;;
                   '(temp_448 : seq uint8) ←
                    (seq_slice (temp_446) (usize 16) (usize 48)) ;;
                   '(temp_450 : fp_t) ←
                    (nat_mod_from_byte_seq_be (temp_448)) ;;
                  ret (temp_450)) ;;
               '(output_453 : seq (fp_t '× fp_t)) ←
                (ret (seq_upd output_453 (i_415) (prod_ce(e_1_451, e_2_452
                      )))) ;;
              
              @ret ((seq (fp_t '× fp_t))) (output_453) } : code (CEfset (
                  [output_453_loc])) [interface  ] _))) ;;
      
      @ret (seq (fp_t '× fp_t)) (output_453) } : code (CEfset (
          [output_453_loc])) [interface
      #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp2_hash_to_field : package _ _ _ :=
  (seq_link fp2_hash_to_field link_rest(package_expand_message_xmd)).
Fail Next Obligation.


Notation "'fp2_sgn0_inp'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2_sgn0_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition FP2_SGN0 : nat :=
  (476).
Program Definition fp2_sgn0
   : package (fset.fset0) [interface
  #val #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out ] [interface
  #val #[ FP2_SGN0 ] : fp2_sgn0_inp → fp2_sgn0_out ] :=
  ([package #def #[ FP2_SGN0 ] (temp_inp : fp2_sgn0_inp) : fp2_sgn0_out { 
    let '(x_456) := temp_inp : fp2_t in
    #import {sig #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out } as  fp_sgn0 ;;
    let fp_sgn0 := fun x_0 => fp_sgn0 (x_0) in
    ({ code  temp_475 ←
        (ret (x_456)) ;;
      let '(x0_457, x1_464) :=
        (temp_475) : (fp_t '× fp_t) in
       '(sign_0_467 : bool_ChoiceEquality) ←
        ( '(temp_459 : bool_ChoiceEquality) ←
            (fp_sgn0 (x0_457)) ;;
          ret (temp_459)) ;;
       '(zero_0_468 : bool_ChoiceEquality) ←
        ( '(temp_461 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_463 : bool_ChoiceEquality) ←
            ((x0_457) =.? (temp_461)) ;;
          ret (temp_463)) ;;
       '(sign_1_469 : bool_ChoiceEquality) ←
        ( '(temp_466 : bool_ChoiceEquality) ←
            (fp_sgn0 (x1_464)) ;;
          ret (temp_466)) ;;
       '(temp_471 : bool_ChoiceEquality) ←
        ((zero_0_468) && (sign_1_469)) ;;
       '(temp_473 : bool_ChoiceEquality) ←
        ((sign_0_467) || (temp_471)) ;;
      @ret (bool_ChoiceEquality) (temp_473) } : code (fset.fset0) [interface
      #val #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp2_sgn0 : package _ _ _ :=
  (seq_link fp2_sgn0 link_rest(package_fp_sgn0)).
Fail Next Obligation.


Notation "'fp2_is_square_inp'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2_is_square_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition FP2_IS_SQUARE : nat :=
  (508).
Program Definition fp2_is_square
   : package (fset.fset0) [interface  ] [interface
  #val #[ FP2_IS_SQUARE ] : fp2_is_square_inp → fp2_is_square_out ] :=
  (
    [package #def #[ FP2_IS_SQUARE ] (temp_inp : fp2_is_square_inp) : fp2_is_square_out { 
    let '(x_481) := temp_inp : fp2_t in
    ({ code  '(c1_493 : fp_t) ←
        ( '(temp_478 : seq int8) ←
            (array_to_be_bytes (p_1_2_v)) ;;
           '(temp_480 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_478)) ;;
          ret (temp_480)) ;;
       temp_507 ←
        (ret (x_481)) ;;
      let '(x1_482, x2_485) :=
        (temp_507) : (fp_t '× fp_t) in
       '(tv1_488 : fp_t) ←
        ( '(temp_484 : fp_t) ←
            ((x1_482) *% (x1_482)) ;;
          ret (temp_484)) ;;
       '(tv2_489 : fp_t) ←
        ( '(temp_487 : fp_t) ←
            ((x2_485) *% (x2_485)) ;;
          ret (temp_487)) ;;
       '(tv1_492 : fp_t) ←
        ( '(temp_491 : fp_t) ←
            ((tv1_488) +% (tv2_489)) ;;
          ret (temp_491)) ;;
       '(tv1_502 : fp_t) ←
        ( temp_495 ←
            (nat_mod_pow_self (tv1_492) (c1_493)) ;;
          ret (temp_495)) ;;
       '(neg1_503 : fp_t) ←
        ( '(temp_497 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_499 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_501 : fp_t) ←
            ((temp_497) -% (temp_499)) ;;
          ret (temp_501)) ;;
       '(temp_505 : bool_ChoiceEquality) ←
        ((tv1_502) !=.? (neg1_503)) ;;
      @ret (bool_ChoiceEquality) (temp_505) } : code (fset.fset0) [interface 
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp2_is_square : package _ _ _ :=
  (fp2_is_square).
Fail Next Obligation.

Definition c_513_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 525%nat)).
Notation "'fp2exp_inp'" := (
  fp2_t '× fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2exp_out'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Definition FP2EXP : nat :=
  (526).
Program Definition fp2exp
   : package (CEfset ([c_513_loc])) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] [interface
  #val #[ FP2EXP ] : fp2exp_inp → fp2exp_out ] :=
  ([package #def #[ FP2EXP ] (temp_inp : fp2exp_inp) : fp2exp_out { 
    let '(n_522 , k_516) := temp_inp : fp2_t '× fp_t in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as  fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as  fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    ({ code  '(c_513 : (fp_t '× fp_t)) ←
          ( '(temp_510 : fp_t) ←
              (nat_mod_one ) ;;
             temp_512 ←
              (fp2fromfp (temp_510)) ;;
            ret (temp_512)) ;;
        #put c_513_loc := c_513 ;;
       '(c_513 : ((fp_t '× fp_t))) ←
        (foldi' (usize 0) (usize 381) c_513 (L2 := CEfset ([c_513_loc])) (
              I2 := [interface
              #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_517 c_513 =>
            ({ code  '(c_513 : (fp_t '× fp_t)) ←
                  (( temp_515 ←
                        (fp2mul (c_513) (c_513)) ;;
                      ret (temp_515))) ;;
                #put c_513_loc := c_513 ;;
              
               '(temp_519 : uint_size) ←
                ((usize 380) .- (i_517)) ;;
               temp_521 ←
                (nat_mod_bit (k_516) (temp_519)) ;;
               '(c_513 : ((fp_t '× fp_t))) ←
                (if temp_521:bool_ChoiceEquality
                  then (({ code  '(c_513 : (fp_t '× fp_t)) ←
                          (( temp_524 ←
                                (fp2mul (c_513) (n_522)) ;;
                              ret (temp_524))) ;;
                        #put c_513_loc := c_513 ;;
                      
                      @ret (((fp_t '× fp_t))) (c_513) } : code (CEfset (
                          [c_513_loc])) [interface
                      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] _))
                  else @ret (((fp_t '× fp_t))) (c_513)) ;;
              
              @ret (((fp_t '× fp_t))) (c_513) } : code (CEfset (
                  [c_513_loc])) [interface
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] _))) ;;
      
      @ret ((fp_t '× fp_t)) (c_513) } : code (CEfset ([c_513_loc])) [interface
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp2exp : package _ _ _ :=
  (seq_link fp2exp link_rest(package_fp2fromfp,package_fp2mul)).
Fail Next Obligation.


Notation "'fp2_sqrt_inp'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2_sqrt_out'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Definition FP2_SQRT : nat :=
  (577).
Program Definition fp2_sqrt
   : package (CEfset ([])) [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
  #val #[ FP2EXP ] : fp2exp_inp → fp2exp_out ;
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] [interface
  #val #[ FP2_SQRT ] : fp2_sqrt_inp → fp2_sqrt_out ] :=
  ([package #def #[ FP2_SQRT ] (temp_inp : fp2_sqrt_inp) : fp2_sqrt_out { 
    let '(a_535) := temp_inp : fp2_t in
    #import {sig #[ FP2ADD ] : fp2add_inp → fp2add_out } as  fp2add ;;
    let fp2add := fun x_0 x_1 => fp2add (x_0,x_1) in
    #import {sig #[ FP2EXP ] : fp2exp_inp → fp2exp_out } as  fp2exp ;;
    let fp2exp := fun x_0 x_1 => fp2exp (x_0,x_1) in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as  fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as  fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    ({ code  '(c1_536 : fp_t) ←
        ( '(temp_528 : seq int8) ←
            (array_to_be_bytes (p_3_4_v)) ;;
           '(temp_530 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_528)) ;;
          ret (temp_530)) ;;
       '(c2_561 : fp_t) ←
        ( '(temp_532 : seq int8) ←
            (array_to_be_bytes (p_1_2_v)) ;;
           '(temp_534 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_532)) ;;
          ret (temp_534)) ;;
       '(a1_539 : (fp_t '× fp_t)) ←
        ( '(temp_538 : fp2_t) ←
            (fp2exp (a_535) (c1_536)) ;;
          ret (temp_538)) ;;
       '(alpha_558 : (fp_t '× fp_t)) ←
        ( temp_541 ←
            (fp2mul (a1_539) (a_535)) ;;
           temp_543 ←
            (fp2mul (a1_539) (temp_541)) ;;
          ret (temp_543)) ;;
       '(x0_571 : (fp_t '× fp_t)) ←
        ( temp_545 ←
            (fp2mul (a1_539) (a_535)) ;;
          ret (temp_545)) ;;
       '(neg1_564 : (fp_t '× fp_t)) ←
        ( '(temp_547 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_549 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_551 : fp_t) ←
            ((temp_547) -% (temp_549)) ;;
           '(temp_553 : fp_t) ←
            (nat_mod_zero ) ;;
          ret (prod_ce(temp_551, temp_553))) ;;
       '(b_574 : (fp_t '× fp_t)) ←
        ( '(temp_555 : fp_t) ←
            (nat_mod_one ) ;;
           temp_557 ←
            (fp2fromfp (temp_555)) ;;
           temp_560 ←
            (fp2add (temp_557) (alpha_558)) ;;
           '(temp_563 : fp2_t) ←
            (fp2exp (temp_560) (c2_561)) ;;
          ret (temp_563)) ;;
       '(temp_566 : bool_ChoiceEquality) ←
        ((alpha_558) =.? (neg1_564)) ;;
       '(temp_568 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_570 : fp_t) ←
        (nat_mod_one ) ;;
       temp_573 ←
        (fp2mul (prod_ce(temp_568, temp_570)) (x0_571)) ;;
       temp_576 ←
        (fp2mul (b_574) (x0_571)) ;;
      @ret ((fp_t '× fp_t)) ((if (temp_566):bool_ChoiceEquality then (
            temp_573) else (temp_576))) } : code (CEfset ([])) [interface
      #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
      #val #[ FP2EXP ] : fp2exp_inp → fp2exp_out ;
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp2_sqrt : package _ _ _ :=
  (seq_link fp2_sqrt link_rest(
      package_fp2add,package_fp2exp,package_fp2fromfp,package_fp2mul)).
Fail Next Obligation.


Notation "'g2_curve_func_inp'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_curve_func_out'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Definition G2_CURVE_FUNC : nat :=
  (589).
Program Definition g2_curve_func
   : package (fset.fset0) [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] [interface
  #val #[ G2_CURVE_FUNC ] : g2_curve_func_inp → g2_curve_func_out ] :=
  (
    [package #def #[ G2_CURVE_FUNC ] (temp_inp : g2_curve_func_inp) : g2_curve_func_out { 
    let '(x_578) := temp_inp : fp2_t in
    #import {sig #[ FP2ADD ] : fp2add_inp → fp2add_out } as  fp2add ;;
    let fp2add := fun x_0 x_1 => fp2add (x_0,x_1) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as  fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    ({ code  temp_580 ←
        (fp2mul (x_578) (x_578)) ;;
       temp_582 ←
        (fp2mul (x_578) (temp_580)) ;;
       '(temp_584 : fp_t) ←
        (nat_mod_from_literal (_) (@repr U128 4)) ;;
       '(temp_586 : fp_t) ←
        (nat_mod_from_literal (_) (@repr U128 4)) ;;
       temp_588 ←
        (fp2add (temp_582) (prod_ce(temp_584, temp_586))) ;;
      @ret ((fp_t '× fp_t)) (temp_588) } : code (fset.fset0) [interface
      #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_g2_curve_func : package _ _ _ :=
  (seq_link g2_curve_func link_rest(package_fp2add,package_fp2mul)).
Fail Next Obligation.

Definition y_725_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 732%nat)).
Definition tv4_638_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 733%nat)).
Notation "'g2_map_to_curve_svdw_inp'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_map_to_curve_svdw_out'" := (
  g2_t : choice_type) (in custom pack_type at level 2).
Definition G2_MAP_TO_CURVE_SVDW : nat :=
  (734).
Program Definition g2_map_to_curve_svdw
   : package (CEfset ([tv4_638_loc ; y_725_loc])) [interface
  #val #[ FP2_IS_SQUARE ] : fp2_is_square_inp → fp2_is_square_out ;
  #val #[ FP2_SGN0 ] : fp2_sgn0_inp → fp2_sgn0_out ;
  #val #[ FP2_SQRT ] : fp2_sqrt_inp → fp2_sqrt_out ;
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
  #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ;
  #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ;
  #val #[ G2_CURVE_FUNC ] : g2_curve_func_inp → g2_curve_func_out ] [interface
  #val #[ G2_MAP_TO_CURVE_SVDW ] : g2_map_to_curve_svdw_inp → g2_map_to_curve_svdw_out
  ] :=
  (
    [package #def #[ G2_MAP_TO_CURVE_SVDW ] (temp_inp : g2_map_to_curve_svdw_inp) : g2_map_to_curve_svdw_out { 
    let '(u_599) := temp_inp : fp2_t in
    #import {sig #[ FP2_IS_SQUARE ] : fp2_is_square_inp → fp2_is_square_out } as  fp2_is_square ;;
    let fp2_is_square := fun x_0 => fp2_is_square (x_0) in
    #import {sig #[ FP2_SGN0 ] : fp2_sgn0_inp → fp2_sgn0_out } as  fp2_sgn0 ;;
    let fp2_sgn0 := fun x_0 => fp2_sgn0 (x_0) in
    #import {sig #[ FP2_SQRT ] : fp2_sqrt_inp → fp2_sqrt_out } as  fp2_sqrt ;;
    let fp2_sqrt := fun x_0 => fp2_sqrt (x_0) in
    #import {sig #[ FP2ADD ] : fp2add_inp → fp2add_out } as  fp2add ;;
    let fp2add := fun x_0 x_1 => fp2add (x_0,x_1) in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as  fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP2INV ] : fp2inv_inp → fp2inv_out } as  fp2inv ;;
    let fp2inv := fun x_0 => fp2inv (x_0) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as  fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    #import {sig #[ FP2NEG ] : fp2neg_inp → fp2neg_out } as  fp2neg ;;
    let fp2neg := fun x_0 => fp2neg (x_0) in
    #import {sig #[ FP2SUB ] : fp2sub_inp → fp2sub_out } as  fp2sub ;;
    let fp2sub := fun x_0 x_1 => fp2sub (x_0,x_1) in
    #import {sig #[ G2_CURVE_FUNC ] : g2_curve_func_inp → g2_curve_func_out } as  g2_curve_func ;;
    let g2_curve_func := fun x_0 => g2_curve_func (x_0) in
    ({ code  '(z_596 : (fp_t '× fp_t)) ←
        ( '(temp_591 : fp_t) ←
            (nat_mod_one ) ;;
           temp_593 ←
            (fp2fromfp (temp_591)) ;;
           temp_595 ←
            (fp2neg (temp_593)) ;;
          ret (temp_595)) ;;
       '(gz_602 : (fp_t '× fp_t)) ←
        ( '(temp_598 : fp2_t) ←
            (g2_curve_func (z_596)) ;;
          ret (temp_598)) ;;
       '(tv1_609 : (fp_t '× fp_t)) ←
        ( temp_601 ←
            (fp2mul (u_599) (u_599)) ;;
           temp_604 ←
            (fp2mul (temp_601) (gz_602)) ;;
          ret (temp_604)) ;;
       '(tv2_619 : (fp_t '× fp_t)) ←
        ( '(temp_606 : fp_t) ←
            (nat_mod_one ) ;;
           temp_608 ←
            (fp2fromfp (temp_606)) ;;
           temp_611 ←
            (fp2add (temp_608) (tv1_609)) ;;
          ret (temp_611)) ;;
       '(tv1_618 : (fp_t '× fp_t)) ←
        ( '(temp_613 : fp_t) ←
            (nat_mod_one ) ;;
           temp_615 ←
            (fp2fromfp (temp_613)) ;;
           temp_617 ←
            (fp2sub (temp_615) (tv1_609)) ;;
          ret (temp_617)) ;;
       '(tv3_645 : (fp_t '× fp_t)) ←
        ( temp_621 ←
            (fp2mul (tv1_618) (tv2_619)) ;;
           temp_623 ←
            (fp2inv (temp_621)) ;;
          ret (temp_623)) ;;
       '(tv4_638 : (fp_t '× fp_t)) ←
          ( temp_625 ←
              (fp2neg (gz_602)) ;;
             '(temp_627 : fp_t) ←
              (nat_mod_from_literal (_) (@repr U128 3)) ;;
             temp_629 ←
              (fp2fromfp (temp_627)) ;;
             temp_631 ←
              (fp2mul (z_596) (z_596)) ;;
             temp_633 ←
              (fp2mul (temp_629) (temp_631)) ;;
             temp_635 ←
              (fp2mul (temp_625) (temp_633)) ;;
             '(temp_637 : fp2_t) ←
              (fp2_sqrt (temp_635)) ;;
            ret (temp_637)) ;;
        #put tv4_638_loc := tv4_638 ;;
       '(temp_640 : bool_ChoiceEquality) ←
        (fp2_sgn0 (tv4_638)) ;;
       '(tv4_638 : ((fp_t '× fp_t))) ←
        (if temp_640:bool_ChoiceEquality
          then (({ code  '(tv4_638 : (fp_t '× fp_t)) ←
                  (( temp_642 ←
                        (fp2neg (tv4_638)) ;;
                      ret (temp_642))) ;;
                #put tv4_638_loc := tv4_638 ;;
              
              @ret (((fp_t '× fp_t))) (tv4_638) } : code (CEfset (
                  [tv4_638_loc])) [interface
              #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ] _))
          else @ret (((fp_t '× fp_t))) (tv4_638)) ;;
      
       '(tv5_680 : (fp_t '× fp_t)) ←
        ( temp_644 ←
            (fp2mul (u_599) (tv1_618)) ;;
           temp_647 ←
            (fp2mul (temp_644) (tv3_645)) ;;
           temp_649 ←
            (fp2mul (temp_647) (tv4_638)) ;;
          ret (temp_649)) ;;
       '(tv6_699 : (fp_t '× fp_t)) ←
        ( '(temp_651 : fp_t) ←
            (nat_mod_from_literal (_) (@repr U128 4)) ;;
           temp_653 ←
            (fp2fromfp (temp_651)) ;;
           temp_655 ←
            (fp2neg (temp_653)) ;;
           temp_657 ←
            (fp2mul (temp_655) (gz_602)) ;;
           '(temp_659 : fp_t) ←
            (nat_mod_from_literal (_) (@repr U128 3)) ;;
           temp_661 ←
            (fp2fromfp (temp_659)) ;;
           temp_663 ←
            (fp2mul (z_596) (z_596)) ;;
           temp_665 ←
            (fp2mul (temp_661) (temp_663)) ;;
           temp_667 ←
            (fp2inv (temp_665)) ;;
           temp_669 ←
            (fp2mul (temp_657) (temp_667)) ;;
          ret (temp_669)) ;;
       '(x1_707 : (fp_t '× fp_t)) ←
        ( temp_671 ←
            (fp2neg (z_596)) ;;
           '(temp_673 : fp_t) ←
            (nat_mod_two ) ;;
           temp_675 ←
            (fp2fromfp (temp_673)) ;;
           temp_677 ←
            (fp2inv (temp_675)) ;;
           temp_679 ←
            (fp2mul (temp_671) (temp_677)) ;;
           temp_682 ←
            (fp2sub (temp_679) (tv5_680)) ;;
          ret (temp_682)) ;;
       '(x2_712 : (fp_t '× fp_t)) ←
        ( temp_684 ←
            (fp2neg (z_596)) ;;
           '(temp_686 : fp_t) ←
            (nat_mod_two ) ;;
           temp_688 ←
            (fp2fromfp (temp_686)) ;;
           temp_690 ←
            (fp2inv (temp_688)) ;;
           temp_692 ←
            (fp2mul (temp_684) (temp_690)) ;;
           temp_694 ←
            (fp2add (temp_692) (tv5_680)) ;;
          ret (temp_694)) ;;
       '(tv7_700 : (fp_t '× fp_t)) ←
        ( temp_696 ←
            (fp2mul (tv2_619) (tv2_619)) ;;
           temp_698 ←
            (fp2mul (temp_696) (tv3_645)) ;;
          ret (temp_698)) ;;
       '(x3_717 : (fp_t '× fp_t)) ←
        ( temp_702 ←
            (fp2mul (tv7_700) (tv7_700)) ;;
           temp_704 ←
            (fp2mul (tv6_699) (temp_702)) ;;
           temp_706 ←
            (fp2add (z_596) (temp_704)) ;;
          ret (temp_706)) ;;
       '(x_718 : (fp_t '× fp_t)) ←
        ( '(temp_709 : fp2_t) ←
            (g2_curve_func (x1_707)) ;;
           '(temp_711 : bool_ChoiceEquality) ←
            (fp2_is_square (temp_709)) ;;
           '(temp_714 : fp2_t) ←
            (g2_curve_func (x2_712)) ;;
           '(temp_716 : bool_ChoiceEquality) ←
            (fp2_is_square (temp_714)) ;;
          ret ((if (temp_711):bool_ChoiceEquality then (x1_707) else ((if (
                    temp_716):bool_ChoiceEquality then (x2_712) else (
                    x3_717)))))) ;;
       '(y_725 : (fp_t '× fp_t)) ←
          ( '(temp_720 : fp2_t) ←
              (g2_curve_func (x_718)) ;;
             '(temp_722 : fp2_t) ←
              (fp2_sqrt (temp_720)) ;;
            ret (temp_722)) ;;
        #put y_725_loc := y_725 ;;
       '(temp_724 : bool_ChoiceEquality) ←
        (fp2_sgn0 (u_599)) ;;
       '(temp_727 : bool_ChoiceEquality) ←
        (fp2_sgn0 (y_725)) ;;
       '(temp_729 : bool_ChoiceEquality) ←
        ((temp_724) !=.? (temp_727)) ;;
       '(y_725 : ((fp_t '× fp_t))) ←
        (if temp_729:bool_ChoiceEquality
          then (({ code  '(y_725 : (fp_t '× fp_t)) ←
                  (( temp_731 ←
                        (fp2neg (y_725)) ;;
                      ret (temp_731))) ;;
                #put y_725_loc := y_725 ;;
              
              @ret (((fp_t '× fp_t))) (y_725) } : code (CEfset (
                  [tv4_638_loc ; y_725_loc])) [interface
              #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ] _))
          else @ret (((fp_t '× fp_t))) (y_725)) ;;
      
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality)) (
        prod_ce(x_718, y_725, (false : bool_ChoiceEquality))) } : code (CEfset (
          [tv4_638_loc ; y_725_loc])) [interface
      #val #[ FP2_IS_SQUARE ] : fp2_is_square_inp → fp2_is_square_out ;
      #val #[ FP2_SGN0 ] : fp2_sgn0_inp → fp2_sgn0_out ;
      #val #[ FP2_SQRT ] : fp2_sqrt_inp → fp2_sqrt_out ;
      #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
      #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ;
      #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ;
      #val #[ G2_CURVE_FUNC ] : g2_curve_func_inp → g2_curve_func_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_g2_map_to_curve_svdw : package _ _ _ :=
  (seq_link g2_map_to_curve_svdw link_rest(
      package_fp2_is_square,package_fp2_sgn0,package_fp2_sqrt,package_fp2add,package_fp2fromfp,package_fp2inv,package_fp2mul,package_fp2neg,package_fp2sub,package_g2_curve_func)).
Fail Next Obligation.


Notation "'psi_inp'" := (g2_t : choice_type) (in custom pack_type at level 2).
Notation "'psi_out'" := (g2_t : choice_type) (in custom pack_type at level 2).
Definition PSI : nat :=
  (793).
Program Definition psi
   : package (CEfset ([])) [interface
  #val #[ FP2CONJUGATE ] : fp2conjugate_inp → fp2conjugate_out ;
  #val #[ FP2EXP ] : fp2exp_inp → fp2exp_out ;
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] [interface
  #val #[ PSI ] : psi_inp → psi_out ] :=
  ([package #def #[ PSI ] (temp_inp : psi_inp) : psi_out { 
    let '(p_775) := temp_inp : g2_t in
    #import {sig #[ FP2CONJUGATE ] : fp2conjugate_inp → fp2conjugate_out } as  fp2conjugate ;;
    let fp2conjugate := fun x_0 => fp2conjugate (x_0) in
    #import {sig #[ FP2EXP ] : fp2exp_inp → fp2exp_out } as  fp2exp ;;
    let fp2exp := fun x_0 x_1 => fp2exp (x_0,x_1) in
    #import {sig #[ FP2INV ] : fp2inv_inp → fp2inv_out } as  fp2inv ;;
    let fp2inv := fun x_0 => fp2inv (x_0) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as  fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    ({ code  '(c1_776 : (fp_t '× fp_t)) ←
        ( '(temp_736 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_738 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_740 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_742 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_744 : fp_t) ←
            ((temp_740) -% (temp_742)) ;;
           '(temp_746 : fp_t) ←
            (nat_mod_from_literal (_) (@repr U128 3)) ;;
           temp_748 ←
            (nat_mod_inv (temp_746)) ;;
           '(temp_750 : fp_t) ←
            ((temp_744) *% (temp_748)) ;;
           '(temp_752 : fp2_t) ←
            (fp2exp (prod_ce(temp_736, temp_738)) (temp_750)) ;;
           temp_754 ←
            (fp2inv (temp_752)) ;;
          ret (temp_754)) ;;
       '(c2_782 : (fp_t '× fp_t)) ←
        ( '(temp_756 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_758 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_760 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_762 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_764 : fp_t) ←
            ((temp_760) -% (temp_762)) ;;
           '(temp_766 : fp_t) ←
            (nat_mod_two ) ;;
           temp_768 ←
            (nat_mod_inv (temp_766)) ;;
           '(temp_770 : fp_t) ←
            ((temp_764) *% (temp_768)) ;;
           '(temp_772 : fp2_t) ←
            (fp2exp (prod_ce(temp_756, temp_758)) (temp_770)) ;;
           temp_774 ←
            (fp2inv (temp_772)) ;;
          ret (temp_774)) ;;
       temp_792 ←
        (ret (p_775)) ;;
      let '(x_777, y_783, inf_790) :=
        (temp_792) : (
        (fp_t '× fp_t) '×
        (fp_t '× fp_t) '×
        bool_ChoiceEquality
      ) in
       '(qx_788 : (fp_t '× fp_t)) ←
        ( temp_779 ←
            (fp2conjugate (x_777)) ;;
           temp_781 ←
            (fp2mul (c1_776) (temp_779)) ;;
          ret (temp_781)) ;;
       '(qy_789 : (fp_t '× fp_t)) ←
        ( temp_785 ←
            (fp2conjugate (y_783)) ;;
           temp_787 ←
            (fp2mul (c2_782) (temp_785)) ;;
          ret (temp_787)) ;;
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality)) (
        prod_ce(qx_788, qy_789, inf_790)) } : code (CEfset ([])) [interface
      #val #[ FP2CONJUGATE ] : fp2conjugate_inp → fp2conjugate_out ;
      #val #[ FP2EXP ] : fp2exp_inp → fp2exp_out ;
      #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_psi : package _ _ _ :=
  (seq_link psi link_rest(
      package_fp2conjugate,package_fp2exp,package_fp2inv,package_fp2mul)).
Fail Next Obligation.


Notation "'g2_clear_cofactor_inp'" := (
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_clear_cofactor_out'" := (
  g2_t : choice_type) (in custom pack_type at level 2).
Definition G2_CLEAR_COFACTOR : nat :=
  (842).
Program Definition g2_clear_cofactor
   : package (CEfset ([])) [interface
  #val #[ G2ADD ] : g2add_inp → g2add_out ;
  #val #[ G2DOUBLE ] : g2double_inp → g2double_out ;
  #val #[ G2MUL ] : g2mul_inp → g2mul_out ;
  #val #[ G2NEG ] : g2neg_inp → g2neg_out ;
  #val #[ PSI ] : psi_inp → psi_out ] [interface
  #val #[ G2_CLEAR_COFACTOR ] : g2_clear_cofactor_inp → g2_clear_cofactor_out
  ] :=
  (
    [package #def #[ G2_CLEAR_COFACTOR ] (temp_inp : g2_clear_cofactor_inp) : g2_clear_cofactor_out { 
    let '(p_797) := temp_inp : g2_t in
    #import {sig #[ G2ADD ] : g2add_inp → g2add_out } as  g2add ;;
    let g2add := fun x_0 x_1 => g2add (x_0,x_1) in
    #import {sig #[ G2DOUBLE ] : g2double_inp → g2double_out } as  g2double ;;
    let g2double := fun x_0 => g2double (x_0) in
    #import {sig #[ G2MUL ] : g2mul_inp → g2mul_out } as  g2mul ;;
    let g2mul := fun x_0 x_1 => g2mul (x_0,x_1) in
    #import {sig #[ G2NEG ] : g2neg_inp → g2neg_out } as  g2neg ;;
    let g2neg := fun x_0 => g2neg (x_0) in
    #import {sig #[ PSI ] : psi_inp → psi_out } as  psi ;;
    let psi := fun x_0 => psi (x_0) in
    ({ code  '(c1_796 : scalar_t) ←
        ( '(temp_795 : scalar_t) ←
            (nat_mod_from_literal (_) (@repr U128 15132376222941642752)) ;;
          ret (temp_795)) ;;
       '(t1_800 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( temp_799 ←
            (g2mul (c1_796) (p_797)) ;;
          ret (temp_799)) ;;
       '(t1_818 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( temp_802 ←
            (g2neg (t1_800)) ;;
          ret (temp_802)) ;;
       '(t2_813 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_804 : g2_t) ←
            (psi (p_797)) ;;
          ret (temp_804)) ;;
       '(t3_807 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( temp_806 ←
            (g2double (p_797)) ;;
          ret (temp_806)) ;;
       '(t3_812 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_809 : g2_t) ←
            (psi (t3_807)) ;;
           '(temp_811 : g2_t) ←
            (psi (temp_809)) ;;
          ret (temp_811)) ;;
       '(t3_827 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( temp_815 ←
            (g2neg (t2_813)) ;;
           temp_817 ←
            (g2add (t3_812) (temp_815)) ;;
          ret (temp_817)) ;;
       '(t2_821 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( temp_820 ←
            (g2add (t1_818) (t2_813)) ;;
          ret (temp_820)) ;;
       '(t2_824 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( temp_823 ←
            (g2mul (c1_796) (t2_821)) ;;
          ret (temp_823)) ;;
       '(t2_828 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( temp_826 ←
            (g2neg (t2_824)) ;;
          ret (temp_826)) ;;
       '(t3_831 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( temp_830 ←
            (g2add (t3_827) (t2_828)) ;;
          ret (temp_830)) ;;
       '(t3_836 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( temp_833 ←
            (g2neg (t1_818)) ;;
           temp_835 ←
            (g2add (t3_831) (temp_833)) ;;
          ret (temp_835)) ;;
       '(q_841 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( temp_838 ←
            (g2neg (p_797)) ;;
           temp_840 ←
            (g2add (t3_836) (temp_838)) ;;
          ret (temp_840)) ;;
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality)) (
        q_841) } : code (CEfset ([])) [interface
      #val #[ G2ADD ] : g2add_inp → g2add_out ;
      #val #[ G2DOUBLE ] : g2double_inp → g2double_out ;
      #val #[ G2MUL ] : g2mul_inp → g2mul_out ;
      #val #[ G2NEG ] : g2neg_inp → g2neg_out ;
      #val #[ PSI ] : psi_inp → psi_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_g2_clear_cofactor : package _ _ _ :=
  (seq_link g2_clear_cofactor link_rest(
      package_g2add,package_g2double,package_g2mul,package_g2neg,package_psi)).
Fail Next Obligation.


Notation "'g2_hash_to_curve_svdw_inp'" := (
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g2_hash_to_curve_svdw_out'" := (
  g2_t : choice_type) (in custom pack_type at level 2).
Definition G2_HASH_TO_CURVE_SVDW : nat :=
  (864).
Program Definition g2_hash_to_curve_svdw
   : package (CEfset ([])) [interface
  #val #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out ;
  #val #[ G2_CLEAR_COFACTOR ] : g2_clear_cofactor_inp → g2_clear_cofactor_out ;
  #val #[ G2_MAP_TO_CURVE_SVDW ] : g2_map_to_curve_svdw_inp → g2_map_to_curve_svdw_out ;
  #val #[ G2ADD ] : g2add_inp → g2add_out ] [interface
  #val #[ G2_HASH_TO_CURVE_SVDW ] : g2_hash_to_curve_svdw_inp → g2_hash_to_curve_svdw_out
  ] :=
  (
    [package #def #[ G2_HASH_TO_CURVE_SVDW ] (temp_inp : g2_hash_to_curve_svdw_inp) : g2_hash_to_curve_svdw_out { 
    let '(msg_843 , dst_844) := temp_inp : byte_seq '× byte_seq in
    #import {sig #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out } as  fp2_hash_to_field ;;
    let fp2_hash_to_field := fun x_0 x_1 x_2 => fp2_hash_to_field (
      x_0,x_1,x_2) in
    #import {sig #[ G2_CLEAR_COFACTOR ] : g2_clear_cofactor_inp → g2_clear_cofactor_out } as  g2_clear_cofactor ;;
    let g2_clear_cofactor := fun x_0 => g2_clear_cofactor (x_0) in
    #import {sig #[ G2_MAP_TO_CURVE_SVDW ] : g2_map_to_curve_svdw_inp → g2_map_to_curve_svdw_out } as  g2_map_to_curve_svdw ;;
    let g2_map_to_curve_svdw := fun x_0 => g2_map_to_curve_svdw (x_0) in
    #import {sig #[ G2ADD ] : g2add_inp → g2add_out } as  g2add ;;
    let g2add := fun x_0 x_1 => g2add (x_0,x_1) in
    ({ code  '(u_848 : seq fp2_t) ←
        ( '(temp_846 : seq fp2_t) ←
            (fp2_hash_to_field (msg_843) (dst_844) (usize 2)) ;;
          ret (temp_846)) ;;
       '(q0_856 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_849 : fp2_t) ←
            (seq_index (u_848) (usize 0)) ;;
           '(temp_851 : g2_t) ←
            (g2_map_to_curve_svdw (temp_849)) ;;
          ret (temp_851)) ;;
       '(q1_857 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_853 : fp2_t) ←
            (seq_index (u_848) (usize 1)) ;;
           '(temp_855 : g2_t) ←
            (g2_map_to_curve_svdw (temp_853)) ;;
          ret (temp_855)) ;;
       '(r_860 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( temp_859 ←
            (g2add (q0_856) (q1_857)) ;;
          ret (temp_859)) ;;
       '(p_863 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_862 : g2_t) ←
            (g2_clear_cofactor (r_860)) ;;
          ret (temp_862)) ;;
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality)) (
        p_863) } : code (CEfset ([])) [interface
      #val #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out ;
      #val #[ G2_CLEAR_COFACTOR ] : g2_clear_cofactor_inp → g2_clear_cofactor_out ;
      #val #[ G2_MAP_TO_CURVE_SVDW ] : g2_map_to_curve_svdw_inp → g2_map_to_curve_svdw_out ;
      #val #[ G2ADD ] : g2add_inp → g2add_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_g2_hash_to_curve_svdw : package _ _ _ :=
  (seq_link g2_hash_to_curve_svdw link_rest(
      package_fp2_hash_to_field,package_g2_clear_cofactor,package_g2_map_to_curve_svdw,package_g2add)).
Fail Next Obligation.


Notation "'g2_encode_to_curve_svdw_inp'" := (
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g2_encode_to_curve_svdw_out'" := (
  g2_t : choice_type) (in custom pack_type at level 2).
Definition G2_ENCODE_TO_CURVE_SVDW : nat :=
  (878).
Program Definition g2_encode_to_curve_svdw
   : package (CEfset ([])) [interface
  #val #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out ;
  #val #[ G2_CLEAR_COFACTOR ] : g2_clear_cofactor_inp → g2_clear_cofactor_out ;
  #val #[ G2_MAP_TO_CURVE_SVDW ] : g2_map_to_curve_svdw_inp → g2_map_to_curve_svdw_out
  ] [interface
  #val #[ G2_ENCODE_TO_CURVE_SVDW ] : g2_encode_to_curve_svdw_inp → g2_encode_to_curve_svdw_out
  ] :=
  (
    [package #def #[ G2_ENCODE_TO_CURVE_SVDW ] (temp_inp : g2_encode_to_curve_svdw_inp) : g2_encode_to_curve_svdw_out { 
    let '(msg_865 , dst_866) := temp_inp : byte_seq '× byte_seq in
    #import {sig #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out } as  fp2_hash_to_field ;;
    let fp2_hash_to_field := fun x_0 x_1 x_2 => fp2_hash_to_field (
      x_0,x_1,x_2) in
    #import {sig #[ G2_CLEAR_COFACTOR ] : g2_clear_cofactor_inp → g2_clear_cofactor_out } as  g2_clear_cofactor ;;
    let g2_clear_cofactor := fun x_0 => g2_clear_cofactor (x_0) in
    #import {sig #[ G2_MAP_TO_CURVE_SVDW ] : g2_map_to_curve_svdw_inp → g2_map_to_curve_svdw_out } as  g2_map_to_curve_svdw ;;
    let g2_map_to_curve_svdw := fun x_0 => g2_map_to_curve_svdw (x_0) in
    ({ code  '(u_870 : seq fp2_t) ←
        ( '(temp_868 : seq fp2_t) ←
            (fp2_hash_to_field (msg_865) (dst_866) (usize 1)) ;;
          ret (temp_868)) ;;
       '(q_874 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_871 : fp2_t) ←
            (seq_index (u_870) (usize 0)) ;;
           '(temp_873 : g2_t) ←
            (g2_map_to_curve_svdw (temp_871)) ;;
          ret (temp_873)) ;;
       '(p_877 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_876 : g2_t) ←
            (g2_clear_cofactor (q_874)) ;;
          ret (temp_876)) ;;
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality)) (
        p_877) } : code (CEfset ([])) [interface
      #val #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out ;
      #val #[ G2_CLEAR_COFACTOR ] : g2_clear_cofactor_inp → g2_clear_cofactor_out ;
      #val #[ G2_MAP_TO_CURVE_SVDW ] : g2_map_to_curve_svdw_inp → g2_map_to_curve_svdw_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_g2_encode_to_curve_svdw : package _ _ _ :=
  (seq_link g2_encode_to_curve_svdw link_rest(
      package_fp2_hash_to_field,package_g2_clear_cofactor,package_g2_map_to_curve_svdw)).
Fail Next Obligation.

Definition g1_iso_a_v : (arr_fp_t) :=
  (let temp_880 : int64 :=
      (secret (@repr U64 5707120929990979)) in
    let temp_882 : int64 :=
      (secret (@repr U64 4425131892511951234)) in
    let temp_884 : int64 :=
      (secret (@repr U64 12748169179688756904)) in
    let temp_886 : int64 :=
      (secret (@repr U64 15629909748249821612)) in
    let temp_888 : int64 :=
      (secret (@repr U64 10994253769421683071)) in
    let temp_890 : int64 :=
      (secret (@repr U64 6698022561392380957)) in
    let temp_892 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_880;
          temp_882;
          temp_884;
          temp_886;
          temp_888;
          temp_890
        ]) in
    (temp_892)).

Definition g1_iso_b_v : (arr_fp_t) :=
  (let temp_894 : int64 :=
      (secret (@repr U64 1360808972976160816)) in
    let temp_896 : int64 :=
      (secret (@repr U64 111203405409480251)) in
    let temp_898 : int64 :=
      (secret (@repr U64 2312248699302920304)) in
    let temp_900 : int64 :=
      (secret (@repr U64 11581500465278574325)) in
    let temp_902 : int64 :=
      (secret (@repr U64 6495071758858381989)) in
    let temp_904 : int64 :=
      (secret (@repr U64 15117538217124375520)) in
    let temp_906 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_894;
          temp_896;
          temp_898;
          temp_900;
          temp_902;
          temp_904
        ]) in
    (temp_906)).

Definition g1_xnum_k_0_v : (arr_fp_t) :=
  (let temp_908 : int64 :=
      (secret (@repr U64 1270119733718627136)) in
    let temp_910 : int64 :=
      (secret (@repr U64 13261148298159854981)) in
    let temp_912 : int64 :=
      (secret (@repr U64 7723742117508874335)) in
    let temp_914 : int64 :=
      (secret (@repr U64 17465657917644792520)) in
    let temp_916 : int64 :=
      (secret (@repr U64 6201670911048166766)) in
    let temp_918 : int64 :=
      (secret (@repr U64 12586459670690286007)) in
    let temp_920 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_908;
          temp_910;
          temp_912;
          temp_914;
          temp_916;
          temp_918
        ]) in
    (temp_920)).

Definition g1_xnum_k_1_v : (arr_fp_t) :=
  (let temp_922 : int64 :=
      (secret (@repr U64 1668951808976071471)) in
    let temp_924 : int64 :=
      (secret (@repr U64 398773841247578140)) in
    let temp_926 : int64 :=
      (secret (@repr U64 8941869963990959127)) in
    let temp_928 : int64 :=
      (secret (@repr U64 17682789360670468203)) in
    let temp_930 : int64 :=
      (secret (@repr U64 5204176168283587414)) in
    let temp_932 : int64 :=
      (secret (@repr U64 16732261237459223483)) in
    let temp_934 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_922;
          temp_924;
          temp_926;
          temp_928;
          temp_930;
          temp_932
        ]) in
    (temp_934)).

Definition g1_xnum_k_2_v : (arr_fp_t) :=
  (let temp_936 : int64 :=
      (secret (@repr U64 960393023080265964)) in
    let temp_938 : int64 :=
      (secret (@repr U64 2094253841180170779)) in
    let temp_940 : int64 :=
      (secret (@repr U64 14844748873776858085)) in
    let temp_942 : int64 :=
      (secret (@repr U64 7528018573573808732)) in
    let temp_944 : int64 :=
      (secret (@repr U64 10776056440809943711)) in
    let temp_946 : int64 :=
      (secret (@repr U64 16147550488514976944)) in
    let temp_948 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_936;
          temp_938;
          temp_940;
          temp_942;
          temp_944;
          temp_946
        ]) in
    (temp_948)).

Definition g1_xnum_k_3_v : (arr_fp_t) :=
  (let temp_950 : int64 :=
      (secret (@repr U64 1691355743628586423)) in
    let temp_952 : int64 :=
      (secret (@repr U64 5622191986793862162)) in
    let temp_954 : int64 :=
      (secret (@repr U64 15561595211679121189)) in
    let temp_956 : int64 :=
      (secret (@repr U64 17416319752018800771)) in
    let temp_958 : int64 :=
      (secret (@repr U64 5996228842464768403)) in
    let temp_960 : int64 :=
      (secret (@repr U64 14245880009877842017)) in
    let temp_962 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_950;
          temp_952;
          temp_954;
          temp_956;
          temp_958;
          temp_960
        ]) in
    (temp_962)).

Definition g1_xnum_k_4_v : (arr_fp_t) :=
  (let temp_964 : int64 :=
      (secret (@repr U64 1051997788391994435)) in
    let temp_966 : int64 :=
      (secret (@repr U64 7368650625050054228)) in
    let temp_968 : int64 :=
      (secret (@repr U64 11086623519836470079)) in
    let temp_970 : int64 :=
      (secret (@repr U64 607681821319080984)) in
    let temp_972 : int64 :=
      (secret (@repr U64 10978131499682789316)) in
    let temp_974 : int64 :=
      (secret (@repr U64 5842660658088809945)) in
    let temp_976 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_964;
          temp_966;
          temp_968;
          temp_970;
          temp_972;
          temp_974
        ]) in
    (temp_976)).

Definition g1_xnum_k_5_v : (arr_fp_t) :=
  (let temp_978 : int64 :=
      (secret (@repr U64 1598992431623377919)) in
    let temp_980 : int64 :=
      (secret (@repr U64 130921168661596853)) in
    let temp_982 : int64 :=
      (secret (@repr U64 15797696746983946651)) in
    let temp_984 : int64 :=
      (secret (@repr U64 11444679715590672272)) in
    let temp_986 : int64 :=
      (secret (@repr U64 11567228658253249817)) in
    let temp_988 : int64 :=
      (secret (@repr U64 14777367860349315459)) in
    let temp_990 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_978;
          temp_980;
          temp_982;
          temp_984;
          temp_986;
          temp_988
        ]) in
    (temp_990)).

Definition g1_xnum_k_6_v : (arr_fp_t) :=
  (let temp_992 : int64 :=
      (secret (@repr U64 967946631563726121)) in
    let temp_994 : int64 :=
      (secret (@repr U64 7653628713030275775)) in
    let temp_996 : int64 :=
      (secret (@repr U64 12760252618317466849)) in
    let temp_998 : int64 :=
      (secret (@repr U64 10378793938173061930)) in
    let temp_1000 : int64 :=
      (secret (@repr U64 10205808941053849290)) in
    let temp_1002 : int64 :=
      (secret (@repr U64 15985511645807504772)) in
    let temp_1004 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_992;
          temp_994;
          temp_996;
          temp_998;
          temp_1000;
          temp_1002
        ]) in
    (temp_1004)).

Definition g1_xnum_k_7_v : (arr_fp_t) :=
  (let temp_1006 : int64 :=
      (secret (@repr U64 1709149555065084898)) in
    let temp_1008 : int64 :=
      (secret (@repr U64 16750075057192140371)) in
    let temp_1010 : int64 :=
      (secret (@repr U64 3849985779734105521)) in
    let temp_1012 : int64 :=
      (secret (@repr U64 11998370262181639475)) in
    let temp_1014 : int64 :=
      (secret (@repr U64 4159013751748851119)) in
    let temp_1016 : int64 :=
      (secret (@repr U64 11298218755092433038)) in
    let temp_1018 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1006;
          temp_1008;
          temp_1010;
          temp_1012;
          temp_1014;
          temp_1016
        ]) in
    (temp_1018)).

Definition g1_xnum_k_8_v : (arr_fp_t) :=
  (let temp_1020 : int64 :=
      (secret (@repr U64 580186936973955012)) in
    let temp_1022 : int64 :=
      (secret (@repr U64 8903813505199544589)) in
    let temp_1024 : int64 :=
      (secret (@repr U64 14140024565662700916)) in
    let temp_1026 : int64 :=
      (secret (@repr U64 11728946595272970718)) in
    let temp_1028 : int64 :=
      (secret (@repr U64 5738313744366653077)) in
    let temp_1030 : int64 :=
      (secret (@repr U64 7886252005760951063)) in
    let temp_1032 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1020;
          temp_1022;
          temp_1024;
          temp_1026;
          temp_1028;
          temp_1030
        ]) in
    (temp_1032)).

Definition g1_xnum_k_9_v : (arr_fp_t) :=
  (let temp_1034 : int64 :=
      (secret (@repr U64 1628930385436977092)) in
    let temp_1036 : int64 :=
      (secret (@repr U64 3318087848058654498)) in
    let temp_1038 : int64 :=
      (secret (@repr U64 15937899882900905113)) in
    let temp_1040 : int64 :=
      (secret (@repr U64 7449821001803307903)) in
    let temp_1042 : int64 :=
      (secret (@repr U64 11752436998487615353)) in
    let temp_1044 : int64 :=
      (secret (@repr U64 9161465579737517214)) in
    let temp_1046 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1034;
          temp_1036;
          temp_1038;
          temp_1040;
          temp_1042;
          temp_1044
        ]) in
    (temp_1046)).

Definition g1_xnum_k_10_v : (arr_fp_t) :=
  (let temp_1048 : int64 :=
      (secret (@repr U64 1167027828517898210)) in
    let temp_1050 : int64 :=
      (secret (@repr U64 8275623842221021965)) in
    let temp_1052 : int64 :=
      (secret (@repr U64 18049808134997311382)) in
    let temp_1054 : int64 :=
      (secret (@repr U64 15351349873550116966)) in
    let temp_1056 : int64 :=
      (secret (@repr U64 17769927732099571180)) in
    let temp_1058 : int64 :=
      (secret (@repr U64 14584871380308065147)) in
    let temp_1060 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1048;
          temp_1050;
          temp_1052;
          temp_1054;
          temp_1056;
          temp_1058
        ]) in
    (temp_1060)).

Definition g1_xnum_k_11_v : (arr_fp_t) :=
  (let temp_1062 : int64 :=
      (secret (@repr U64 495550047642324592)) in
    let temp_1064 : int64 :=
      (secret (@repr U64 13627494601717575229)) in
    let temp_1066 : int64 :=
      (secret (@repr U64 3591512392926246844)) in
    let temp_1068 : int64 :=
      (secret (@repr U64 2576269112800734056)) in
    let temp_1070 : int64 :=
      (secret (@repr U64 14000314106239596831)) in
    let temp_1072 : int64 :=
      (secret (@repr U64 12234233096825917993)) in
    let temp_1074 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1062;
          temp_1064;
          temp_1066;
          temp_1068;
          temp_1070;
          temp_1072
        ]) in
    (temp_1074)).

Definition g1_xden_k_0_v : (arr_fp_t) :=
  (let temp_1076 : int64 :=
      (secret (@repr U64 633474091881273774)) in
    let temp_1078 : int64 :=
      (secret (@repr U64 1779737893574802031)) in
    let temp_1080 : int64 :=
      (secret (@repr U64 132274872219551930)) in
    let temp_1082 : int64 :=
      (secret (@repr U64 11283074393783708770)) in
    let temp_1084 : int64 :=
      (secret (@repr U64 13067430171545714168)) in
    let temp_1086 : int64 :=
      (secret (@repr U64 11041975239630265116)) in
    let temp_1088 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1076;
          temp_1078;
          temp_1080;
          temp_1082;
          temp_1084;
          temp_1086
        ]) in
    (temp_1088)).

Definition g1_xden_k_1_v : (arr_fp_t) :=
  (let temp_1090 : int64 :=
      (secret (@repr U64 1321272531362356291)) in
    let temp_1092 : int64 :=
      (secret (@repr U64 5238936591227237942)) in
    let temp_1094 : int64 :=
      (secret (@repr U64 8089002360232247308)) in
    let temp_1096 : int64 :=
      (secret (@repr U64 82967328719421271)) in
    let temp_1098 : int64 :=
      (secret (@repr U64 1430641118356186857)) in
    let temp_1100 : int64 :=
      (secret (@repr U64 16557527386785790975)) in
    let temp_1102 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1090;
          temp_1092;
          temp_1094;
          temp_1096;
          temp_1098;
          temp_1100
        ]) in
    (temp_1102)).

Definition g1_xden_k_2_v : (arr_fp_t) :=
  (let temp_1104 : int64 :=
      (secret (@repr U64 804282852993868382)) in
    let temp_1106 : int64 :=
      (secret (@repr U64 9311163821600184607)) in
    let temp_1108 : int64 :=
      (secret (@repr U64 8037026956533927121)) in
    let temp_1110 : int64 :=
      (secret (@repr U64 18205324308570099372)) in
    let temp_1112 : int64 :=
      (secret (@repr U64 15466434890074226396)) in
    let temp_1114 : int64 :=
      (secret (@repr U64 18213183315621985817)) in
    let temp_1116 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1104;
          temp_1106;
          temp_1108;
          temp_1110;
          temp_1112;
          temp_1114
        ]) in
    (temp_1116)).

Definition g1_xden_k_3_v : (arr_fp_t) :=
  (let temp_1118 : int64 :=
      (secret (@repr U64 234844145893171966)) in
    let temp_1120 : int64 :=
      (secret (@repr U64 14428037799351479124)) in
    let temp_1122 : int64 :=
      (secret (@repr U64 6559532710647391569)) in
    let temp_1124 : int64 :=
      (secret (@repr U64 6110444250091843536)) in
    let temp_1126 : int64 :=
      (secret (@repr U64 5293652763671852484)) in
    let temp_1128 : int64 :=
      (secret (@repr U64 1373009181854280920)) in
    let temp_1130 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1118;
          temp_1120;
          temp_1122;
          temp_1124;
          temp_1126;
          temp_1128
        ]) in
    (temp_1130)).

Definition g1_xden_k_4_v : (arr_fp_t) :=
  (let temp_1132 : int64 :=
      (secret (@repr U64 1416629893867312296)) in
    let temp_1134 : int64 :=
      (secret (@repr U64 751851957792514173)) in
    let temp_1136 : int64 :=
      (secret (@repr U64 18437674587247370939)) in
    let temp_1138 : int64 :=
      (secret (@repr U64 10190314345946351322)) in
    let temp_1140 : int64 :=
      (secret (@repr U64 11228207967368476701)) in
    let temp_1142 : int64 :=
      (secret (@repr U64 6025034940388909598)) in
    let temp_1144 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1132;
          temp_1134;
          temp_1136;
          temp_1138;
          temp_1140;
          temp_1142
        ]) in
    (temp_1144)).

Definition g1_xden_k_5_v : (arr_fp_t) :=
  (let temp_1146 : int64 :=
      (secret (@repr U64 1041270466333271993)) in
    let temp_1148 : int64 :=
      (secret (@repr U64 6140956605115975401)) in
    let temp_1150 : int64 :=
      (secret (@repr U64 4131830461445745997)) in
    let temp_1152 : int64 :=
      (secret (@repr U64 739642499118176303)) in
    let temp_1154 : int64 :=
      (secret (@repr U64 8358912131254619921)) in
    let temp_1156 : int64 :=
      (secret (@repr U64 13847998906088228005)) in
    let temp_1158 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1146;
          temp_1148;
          temp_1150;
          temp_1152;
          temp_1154;
          temp_1156
        ]) in
    (temp_1158)).

Definition g1_xden_k_6_v : (arr_fp_t) :=
  (let temp_1160 : int64 :=
      (secret (@repr U64 536714149743900185)) in
    let temp_1162 : int64 :=
      (secret (@repr U64 1098328982230230817)) in
    let temp_1164 : int64 :=
      (secret (@repr U64 6273329123533496713)) in
    let temp_1166 : int64 :=
      (secret (@repr U64 5633448088282521244)) in
    let temp_1168 : int64 :=
      (secret (@repr U64 16894043798660571244)) in
    let temp_1170 : int64 :=
      (secret (@repr U64 17016134625831438906)) in
    let temp_1172 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1160;
          temp_1162;
          temp_1164;
          temp_1166;
          temp_1168;
          temp_1170
        ]) in
    (temp_1172)).

Definition g1_xden_k_7_v : (arr_fp_t) :=
  (let temp_1174 : int64 :=
      (secret (@repr U64 1488347500898461874)) in
    let temp_1176 : int64 :=
      (secret (@repr U64 3509418672874520985)) in
    let temp_1178 : int64 :=
      (secret (@repr U64 7962192351555381416)) in
    let temp_1180 : int64 :=
      (secret (@repr U64 1843909372225399896)) in
    let temp_1182 : int64 :=
      (secret (@repr U64 1127511003250156243)) in
    let temp_1184 : int64 :=
      (secret (@repr U64 1294742680819751518)) in
    let temp_1186 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1174;
          temp_1176;
          temp_1178;
          temp_1180;
          temp_1182;
          temp_1184
        ]) in
    (temp_1186)).

Definition g1_xden_k_8_v : (arr_fp_t) :=
  (let temp_1188 : int64 :=
      (secret (@repr U64 725340084226051970)) in
    let temp_1190 : int64 :=
      (secret (@repr U64 6814521545734988748)) in
    let temp_1192 : int64 :=
      (secret (@repr U64 16176803544133875307)) in
    let temp_1194 : int64 :=
      (secret (@repr U64 8363199516777220149)) in
    let temp_1196 : int64 :=
      (secret (@repr U64 252877309218538352)) in
    let temp_1198 : int64 :=
      (secret (@repr U64 5149562959837648449)) in
    let temp_1200 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1188;
          temp_1190;
          temp_1192;
          temp_1194;
          temp_1196;
          temp_1198
        ]) in
    (temp_1200)).

Definition g1_xden_k_9_v : (arr_fp_t) :=
  (let temp_1202 : int64 :=
      (secret (@repr U64 675470927100193492)) in
    let temp_1204 : int64 :=
      (secret (@repr U64 5146891164735334016)) in
    let temp_1206 : int64 :=
      (secret (@repr U64 17762958817130696759)) in
    let temp_1208 : int64 :=
      (secret (@repr U64 8565656522589412373)) in
    let temp_1210 : int64 :=
      (secret (@repr U64 10599026333335446784)) in
    let temp_1212 : int64 :=
      (secret (@repr U64 3270603789344496906)) in
    let temp_1214 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1202;
          temp_1204;
          temp_1206;
          temp_1208;
          temp_1210;
          temp_1212
        ]) in
    (temp_1214)).

Definition g1_ynum_k_0_v : (arr_fp_t) :=
  (let temp_1216 : int64 :=
      (secret (@repr U64 652344406751465184)) in
    let temp_1218 : int64 :=
      (secret (@repr U64 2710356675495255290)) in
    let temp_1220 : int64 :=
      (secret (@repr U64 1273695771440998738)) in
    let temp_1222 : int64 :=
      (secret (@repr U64 3121750372618945491)) in
    let temp_1224 : int64 :=
      (secret (@repr U64 14775319642720936898)) in
    let temp_1226 : int64 :=
      (secret (@repr U64 13733803417833814835)) in
    let temp_1228 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1216;
          temp_1218;
          temp_1220;
          temp_1222;
          temp_1224;
          temp_1226
        ]) in
    (temp_1228)).

Definition g1_ynum_k_1_v : (arr_fp_t) :=
  (let temp_1230 : int64 :=
      (secret (@repr U64 1389807578337138705)) in
    let temp_1232 : int64 :=
      (secret (@repr U64 15352831428748068483)) in
    let temp_1234 : int64 :=
      (secret (@repr U64 1307144967559264317)) in
    let temp_1236 : int64 :=
      (secret (@repr U64 1121505450578652468)) in
    let temp_1238 : int64 :=
      (secret (@repr U64 15475889019760388287)) in
    let temp_1240 : int64 :=
      (secret (@repr U64 16183658160488302230)) in
    let temp_1242 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1230;
          temp_1232;
          temp_1234;
          temp_1236;
          temp_1238;
          temp_1240
        ]) in
    (temp_1242)).

Definition g1_ynum_k_2_v : (arr_fp_t) :=
  (let temp_1244 : int64 :=
      (secret (@repr U64 57553299067792998)) in
    let temp_1246 : int64 :=
      (secret (@repr U64 17628079362768849300)) in
    let temp_1248 : int64 :=
      (secret (@repr U64 2689461337731570914)) in
    let temp_1250 : int64 :=
      (secret (@repr U64 14070580367580990887)) in
    let temp_1252 : int64 :=
      (secret (@repr U64 15162865775551710499)) in
    let temp_1254 : int64 :=
      (secret (@repr U64 13321614990632673782)) in
    let temp_1256 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1244;
          temp_1246;
          temp_1248;
          temp_1250;
          temp_1252;
          temp_1254
        ]) in
    (temp_1256)).

Definition g1_ynum_k_3_v : (arr_fp_t) :=
  (let temp_1258 : int64 :=
      (secret (@repr U64 141972750621744161)) in
    let temp_1260 : int64 :=
      (secret (@repr U64 8689824239172478807)) in
    let temp_1262 : int64 :=
      (secret (@repr U64 15288216298323671324)) in
    let temp_1264 : int64 :=
      (secret (@repr U64 712874875091754233)) in
    let temp_1266 : int64 :=
      (secret (@repr U64 16014900032503684588)) in
    let temp_1268 : int64 :=
      (secret (@repr U64 11976580453200426187)) in
    let temp_1270 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1258;
          temp_1260;
          temp_1262;
          temp_1264;
          temp_1266;
          temp_1268
        ]) in
    (temp_1270)).

Definition g1_ynum_k_4_v : (arr_fp_t) :=
  (let temp_1272 : int64 :=
      (secret (@repr U64 633886036738506515)) in
    let temp_1274 : int64 :=
      (secret (@repr U64 6678644607214234052)) in
    let temp_1276 : int64 :=
      (secret (@repr U64 1825425679455244472)) in
    let temp_1278 : int64 :=
      (secret (@repr U64 8755912272271186652)) in
    let temp_1280 : int64 :=
      (secret (@repr U64 3379943669301788840)) in
    let temp_1282 : int64 :=
      (secret (@repr U64 4735212769449148123)) in
    let temp_1284 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1272;
          temp_1274;
          temp_1276;
          temp_1278;
          temp_1280;
          temp_1282
        ]) in
    (temp_1284)).

Definition g1_ynum_k_5_v : (arr_fp_t) :=
  (let temp_1286 : int64 :=
      (secret (@repr U64 1612358804494830442)) in
    let temp_1288 : int64 :=
      (secret (@repr U64 2454990789666711200)) in
    let temp_1290 : int64 :=
      (secret (@repr U64 8405916841409361853)) in
    let temp_1292 : int64 :=
      (secret (@repr U64 8525415512662168654)) in
    let temp_1294 : int64 :=
      (secret (@repr U64 2323684950984523890)) in
    let temp_1296 : int64 :=
      (secret (@repr U64 11074978966450447856)) in
    let temp_1298 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1286;
          temp_1288;
          temp_1290;
          temp_1292;
          temp_1294;
          temp_1296
        ]) in
    (temp_1298)).

Definition g1_ynum_k_6_v : (arr_fp_t) :=
  (let temp_1300 : int64 :=
      (secret (@repr U64 336375361001233340)) in
    let temp_1302 : int64 :=
      (secret (@repr U64 12882959944969186108)) in
    let temp_1304 : int64 :=
      (secret (@repr U64 16671121624101127371)) in
    let temp_1306 : int64 :=
      (secret (@repr U64 5922586712221110071)) in
    let temp_1308 : int64 :=
      (secret (@repr U64 5163511947597922654)) in
    let temp_1310 : int64 :=
      (secret (@repr U64 14511152726087948018)) in
    let temp_1312 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1300;
          temp_1302;
          temp_1304;
          temp_1306;
          temp_1308;
          temp_1310
        ]) in
    (temp_1312)).

Definition g1_ynum_k_7_v : (arr_fp_t) :=
  (let temp_1314 : int64 :=
      (secret (@repr U64 686738286210365551)) in
    let temp_1316 : int64 :=
      (secret (@repr U64 16039894141796533876)) in
    let temp_1318 : int64 :=
      (secret (@repr U64 1660145734357211167)) in
    let temp_1320 : int64 :=
      (secret (@repr U64 18231571463891878950)) in
    let temp_1322 : int64 :=
      (secret (@repr U64 4825120264949852469)) in
    let temp_1324 : int64 :=
      (secret (@repr U64 11627815551290637097)) in
    let temp_1326 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1314;
          temp_1316;
          temp_1318;
          temp_1320;
          temp_1322;
          temp_1324
        ]) in
    (temp_1326)).

Definition g1_ynum_k_8_v : (arr_fp_t) :=
  (let temp_1328 : int64 :=
      (secret (@repr U64 719520515476580427)) in
    let temp_1330 : int64 :=
      (secret (@repr U64 16756942182913253819)) in
    let temp_1332 : int64 :=
      (secret (@repr U64 10320769399998235244)) in
    let temp_1334 : int64 :=
      (secret (@repr U64 2200974244968450750)) in
    let temp_1336 : int64 :=
      (secret (@repr U64 7626373186594408355)) in
    let temp_1338 : int64 :=
      (secret (@repr U64 6933025920263103879)) in
    let temp_1340 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1328;
          temp_1330;
          temp_1332;
          temp_1334;
          temp_1336;
          temp_1338
        ]) in
    (temp_1340)).

Definition g1_ynum_k_9_v : (arr_fp_t) :=
  (let temp_1342 : int64 :=
      (secret (@repr U64 1016611174344998325)) in
    let temp_1344 : int64 :=
      (secret (@repr U64 2466492548686891555)) in
    let temp_1346 : int64 :=
      (secret (@repr U64 14135124294293452542)) in
    let temp_1348 : int64 :=
      (secret (@repr U64 475233659467912251)) in
    let temp_1350 : int64 :=
      (secret (@repr U64 11186783513499056751)) in
    let temp_1352 : int64 :=
      (secret (@repr U64 3147922594245844016)) in
    let temp_1354 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1342;
          temp_1344;
          temp_1346;
          temp_1348;
          temp_1350;
          temp_1352
        ]) in
    (temp_1354)).

Definition g1_ynum_k_10_v : (arr_fp_t) :=
  (let temp_1356 : int64 :=
      (secret (@repr U64 1833315000454533566)) in
    let temp_1358 : int64 :=
      (secret (@repr U64 1007974600900082579)) in
    let temp_1360 : int64 :=
      (secret (@repr U64 14785260176242854207)) in
    let temp_1362 : int64 :=
      (secret (@repr U64 15066861003931772432)) in
    let temp_1364 : int64 :=
      (secret (@repr U64 3584647998681889532)) in
    let temp_1366 : int64 :=
      (secret (@repr U64 16722834201330696498)) in
    let temp_1368 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1356;
          temp_1358;
          temp_1360;
          temp_1362;
          temp_1364;
          temp_1366
        ]) in
    (temp_1368)).

Definition g1_ynum_k_11_v : (arr_fp_t) :=
  (let temp_1370 : int64 :=
      (secret (@repr U64 1780164921828767454)) in
    let temp_1372 : int64 :=
      (secret (@repr U64 13337622794239929804)) in
    let temp_1374 : int64 :=
      (secret (@repr U64 5923739534552515142)) in
    let temp_1376 : int64 :=
      (secret (@repr U64 3345046972101780530)) in
    let temp_1378 : int64 :=
      (secret (@repr U64 5321510883028162054)) in
    let temp_1380 : int64 :=
      (secret (@repr U64 14846055306840460686)) in
    let temp_1382 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1370;
          temp_1372;
          temp_1374;
          temp_1376;
          temp_1378;
          temp_1380
        ]) in
    (temp_1382)).

Definition g1_ynum_k_12_v : (arr_fp_t) :=
  (let temp_1384 : int64 :=
      (secret (@repr U64 799438051374502809)) in
    let temp_1386 : int64 :=
      (secret (@repr U64 15083972834952036164)) in
    let temp_1388 : int64 :=
      (secret (@repr U64 8838227588559581326)) in
    let temp_1390 : int64 :=
      (secret (@repr U64 13846054168121598783)) in
    let temp_1392 : int64 :=
      (secret (@repr U64 488730451382505970)) in
    let temp_1394 : int64 :=
      (secret (@repr U64 958146249756188408)) in
    let temp_1396 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1384;
          temp_1386;
          temp_1388;
          temp_1390;
          temp_1392;
          temp_1394
        ]) in
    (temp_1396)).

Definition g1_ynum_k_13_v : (arr_fp_t) :=
  (let temp_1398 : int64 :=
      (secret (@repr U64 163716820423854747)) in
    let temp_1400 : int64 :=
      (secret (@repr U64 8285498163857659356)) in
    let temp_1402 : int64 :=
      (secret (@repr U64 8465424830341846400)) in
    let temp_1404 : int64 :=
      (secret (@repr U64 1433942577299613084)) in
    let temp_1406 : int64 :=
      (secret (@repr U64 14325828012864645732)) in
    let temp_1408 : int64 :=
      (secret (@repr U64 4817114329354076467)) in
    let temp_1410 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1398;
          temp_1400;
          temp_1402;
          temp_1404;
          temp_1406;
          temp_1408
        ]) in
    (temp_1410)).

Definition g1_ynum_k_14_v : (arr_fp_t) :=
  (let temp_1412 : int64 :=
      (secret (@repr U64 414658151749832465)) in
    let temp_1414 : int64 :=
      (secret (@repr U64 189531577938912252)) in
    let temp_1416 : int64 :=
      (secret (@repr U64 6802473390048830824)) in
    let temp_1418 : int64 :=
      (secret (@repr U64 15684647020317539556)) in
    let temp_1420 : int64 :=
      (secret (@repr U64 7755485098777620407)) in
    let temp_1422 : int64 :=
      (secret (@repr U64 9685868895687483979)) in
    let temp_1424 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1412;
          temp_1414;
          temp_1416;
          temp_1418;
          temp_1420;
          temp_1422
        ]) in
    (temp_1424)).

Definition g1_ynum_k_15_v : (arr_fp_t) :=
  (let temp_1426 : int64 :=
      (secret (@repr U64 1578157964224562126)) in
    let temp_1428 : int64 :=
      (secret (@repr U64 5666948055268535989)) in
    let temp_1430 : int64 :=
      (secret (@repr U64 14634479491382401593)) in
    let temp_1432 : int64 :=
      (secret (@repr U64 6317940024988860850)) in
    let temp_1434 : int64 :=
      (secret (@repr U64 13142913832013798519)) in
    let temp_1436 : int64 :=
      (secret (@repr U64 338991247778166276)) in
    let temp_1438 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1426;
          temp_1428;
          temp_1430;
          temp_1432;
          temp_1434;
          temp_1436
        ]) in
    (temp_1438)).

Definition g1_yden_k_0_v : (arr_fp_t) :=
  (let temp_1440 : int64 :=
      (secret (@repr U64 1590100849350973618)) in
    let temp_1442 : int64 :=
      (secret (@repr U64 5915497081334721257)) in
    let temp_1444 : int64 :=
      (secret (@repr U64 6924968209373727718)) in
    let temp_1446 : int64 :=
      (secret (@repr U64 17204633670617869946)) in
    let temp_1448 : int64 :=
      (secret (@repr U64 572916540828819565)) in
    let temp_1450 : int64 :=
      (secret (@repr U64 92203205520679873)) in
    let temp_1452 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1440;
          temp_1442;
          temp_1444;
          temp_1446;
          temp_1448;
          temp_1450
        ]) in
    (temp_1452)).

Definition g1_yden_k_1_v : (arr_fp_t) :=
  (let temp_1454 : int64 :=
      (secret (@repr U64 1829261189398470686)) in
    let temp_1456 : int64 :=
      (secret (@repr U64 1877083417397643448)) in
    let temp_1458 : int64 :=
      (secret (@repr U64 9640042925497046428)) in
    let temp_1460 : int64 :=
      (secret (@repr U64 11862766565471805471)) in
    let temp_1462 : int64 :=
      (secret (@repr U64 8693114993904885301)) in
    let temp_1464 : int64 :=
      (secret (@repr U64 3672140328108400701)) in
    let temp_1466 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1454;
          temp_1456;
          temp_1458;
          temp_1460;
          temp_1462;
          temp_1464
        ]) in
    (temp_1466)).

Definition g1_yden_k_2_v : (arr_fp_t) :=
  (let temp_1468 : int64 :=
      (secret (@repr U64 400243331105348135)) in
    let temp_1470 : int64 :=
      (secret (@repr U64 8046435537999802711)) in
    let temp_1472 : int64 :=
      (secret (@repr U64 8702226981475745585)) in
    let temp_1474 : int64 :=
      (secret (@repr U64 879791671491744492)) in
    let temp_1476 : int64 :=
      (secret (@repr U64 11994630442058346377)) in
    let temp_1478 : int64 :=
      (secret (@repr U64 2172204746352322546)) in
    let temp_1480 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1468;
          temp_1470;
          temp_1472;
          temp_1474;
          temp_1476;
          temp_1478
        ]) in
    (temp_1480)).

Definition g1_yden_k_3_v : (arr_fp_t) :=
  (let temp_1482 : int64 :=
      (secret (@repr U64 1637008473169220501)) in
    let temp_1484 : int64 :=
      (secret (@repr U64 17441636237435581649)) in
    let temp_1486 : int64 :=
      (secret (@repr U64 15066165676546511630)) in
    let temp_1488 : int64 :=
      (secret (@repr U64 1314387578457599809)) in
    let temp_1490 : int64 :=
      (secret (@repr U64 8247046336453711789)) in
    let temp_1492 : int64 :=
      (secret (@repr U64 12164906044230685718)) in
    let temp_1494 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1482;
          temp_1484;
          temp_1486;
          temp_1488;
          temp_1490;
          temp_1492
        ]) in
    (temp_1494)).

Definition g1_yden_k_4_v : (arr_fp_t) :=
  (let temp_1496 : int64 :=
      (secret (@repr U64 855930740911588324)) in
    let temp_1498 : int64 :=
      (secret (@repr U64 12685735333705453020)) in
    let temp_1500 : int64 :=
      (secret (@repr U64 14326404096614579120)) in
    let temp_1502 : int64 :=
      (secret (@repr U64 6066025509460822294)) in
    let temp_1504 : int64 :=
      (secret (@repr U64 11676450493790612973)) in
    let temp_1506 : int64 :=
      (secret (@repr U64 15724621714793234461)) in
    let temp_1508 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1496;
          temp_1498;
          temp_1500;
          temp_1502;
          temp_1504;
          temp_1506
        ]) in
    (temp_1508)).

Definition g1_yden_k_5_v : (arr_fp_t) :=
  (let temp_1510 : int64 :=
      (secret (@repr U64 637792788410719021)) in
    let temp_1512 : int64 :=
      (secret (@repr U64 11507373155986977154)) in
    let temp_1514 : int64 :=
      (secret (@repr U64 13186912195705886849)) in
    let temp_1516 : int64 :=
      (secret (@repr U64 14262012144631372388)) in
    let temp_1518 : int64 :=
      (secret (@repr U64 5328758613570342114)) in
    let temp_1520 : int64 :=
      (secret (@repr U64 199925847119476652)) in
    let temp_1522 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1510;
          temp_1512;
          temp_1514;
          temp_1516;
          temp_1518;
          temp_1520
        ]) in
    (temp_1522)).

Definition g1_yden_k_6_v : (arr_fp_t) :=
  (let temp_1524 : int64 :=
      (secret (@repr U64 1612297190139091759)) in
    let temp_1526 : int64 :=
      (secret (@repr U64 14103733843373163083)) in
    let temp_1528 : int64 :=
      (secret (@repr U64 6840121186619029743)) in
    let temp_1530 : int64 :=
      (secret (@repr U64 6760859324815900753)) in
    let temp_1532 : int64 :=
      (secret (@repr U64 15418807805142572985)) in
    let temp_1534 : int64 :=
      (secret (@repr U64 4402853133867972444)) in
    let temp_1536 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1524;
          temp_1526;
          temp_1528;
          temp_1530;
          temp_1532;
          temp_1534
        ]) in
    (temp_1536)).

Definition g1_yden_k_7_v : (arr_fp_t) :=
  (let temp_1538 : int64 :=
      (secret (@repr U64 1631410310868805610)) in
    let temp_1540 : int64 :=
      (secret (@repr U64 269334146695233390)) in
    let temp_1542 : int64 :=
      (secret (@repr U64 16547411811928854487)) in
    let temp_1544 : int64 :=
      (secret (@repr U64 18353100669930795314)) in
    let temp_1546 : int64 :=
      (secret (@repr U64 13339932232668798692)) in
    let temp_1548 : int64 :=
      (secret (@repr U64 6984591927261867737)) in
    let temp_1550 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1538;
          temp_1540;
          temp_1542;
          temp_1544;
          temp_1546;
          temp_1548
        ]) in
    (temp_1550)).

Definition g1_yden_k_8_v : (arr_fp_t) :=
  (let temp_1552 : int64 :=
      (secret (@repr U64 1758313625630302499)) in
    let temp_1554 : int64 :=
      (secret (@repr U64 1881349400343039172)) in
    let temp_1556 : int64 :=
      (secret (@repr U64 18013005311323887904)) in
    let temp_1558 : int64 :=
      (secret (@repr U64 12377427846571989832)) in
    let temp_1560 : int64 :=
      (secret (@repr U64 5967237584920922243)) in
    let temp_1562 : int64 :=
      (secret (@repr U64 7720081932193848650)) in
    let temp_1564 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1552;
          temp_1554;
          temp_1556;
          temp_1558;
          temp_1560;
          temp_1562
        ]) in
    (temp_1564)).

Definition g1_yden_k_9_v : (arr_fp_t) :=
  (let temp_1566 : int64 :=
      (secret (@repr U64 1619701357752249884)) in
    let temp_1568 : int64 :=
      (secret (@repr U64 16898074901591262352)) in
    let temp_1570 : int64 :=
      (secret (@repr U64 3609344159736760251)) in
    let temp_1572 : int64 :=
      (secret (@repr U64 5983130161189999867)) in
    let temp_1574 : int64 :=
      (secret (@repr U64 14355327869992416094)) in
    let temp_1576 : int64 :=
      (secret (@repr U64 3778226018344582997)) in
    let temp_1578 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1566;
          temp_1568;
          temp_1570;
          temp_1572;
          temp_1574;
          temp_1576
        ]) in
    (temp_1578)).

Definition g1_yden_k_10_v : (arr_fp_t) :=
  (let temp_1580 : int64 :=
      (secret (@repr U64 347606589330687421)) in
    let temp_1582 : int64 :=
      (secret (@repr U64 5255719044972187933)) in
    let temp_1584 : int64 :=
      (secret (@repr U64 11271894388753671721)) in
    let temp_1586 : int64 :=
      (secret (@repr U64 1033887512062764488)) in
    let temp_1588 : int64 :=
      (secret (@repr U64 8189165486932690436)) in
    let temp_1590 : int64 :=
      (secret (@repr U64 70004379462101672)) in
    let temp_1592 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1580;
          temp_1582;
          temp_1584;
          temp_1586;
          temp_1588;
          temp_1590
        ]) in
    (temp_1592)).

Definition g1_yden_k_11_v : (arr_fp_t) :=
  (let temp_1594 : int64 :=
      (secret (@repr U64 778202887894139711)) in
    let temp_1596 : int64 :=
      (secret (@repr U64 17691595219776375879)) in
    let temp_1598 : int64 :=
      (secret (@repr U64 9193253711563866834)) in
    let temp_1600 : int64 :=
      (secret (@repr U64 10092455202333888821)) in
    let temp_1602 : int64 :=
      (secret (@repr U64 1655469341950262250)) in
    let temp_1604 : int64 :=
      (secret (@repr U64 10845992994110574738)) in
    let temp_1606 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1594;
          temp_1596;
          temp_1598;
          temp_1600;
          temp_1602;
          temp_1604
        ]) in
    (temp_1606)).

Definition g1_yden_k_12_v : (arr_fp_t) :=
  (let temp_1608 : int64 :=
      (secret (@repr U64 781015344221683683)) in
    let temp_1610 : int64 :=
      (secret (@repr U64 14078588081290548374)) in
    let temp_1612 : int64 :=
      (secret (@repr U64 6067271023149908518)) in
    let temp_1614 : int64 :=
      (secret (@repr U64 9033357708497886086)) in
    let temp_1616 : int64 :=
      (secret (@repr U64 10592474449179118273)) in
    let temp_1618 : int64 :=
      (secret (@repr U64 2204988348113831372)) in
    let temp_1620 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1608;
          temp_1610;
          temp_1612;
          temp_1614;
          temp_1616;
          temp_1618
        ]) in
    (temp_1620)).

Definition g1_yden_k_13_v : (arr_fp_t) :=
  (let temp_1622 : int64 :=
      (secret (@repr U64 172830037692534587)) in
    let temp_1624 : int64 :=
      (secret (@repr U64 7101012286790006514)) in
    let temp_1626 : int64 :=
      (secret (@repr U64 13787308004332873665)) in
    let temp_1628 : int64 :=
      (secret (@repr U64 14660498759553796110)) in
    let temp_1630 : int64 :=
      (secret (@repr U64 4757234684169342080)) in
    let temp_1632 : int64 :=
      (secret (@repr U64 15130647872920159991)) in
    let temp_1634 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1622;
          temp_1624;
          temp_1626;
          temp_1628;
          temp_1630;
          temp_1632
        ]) in
    (temp_1634)).

Definition g1_yden_k_14_v : (arr_fp_t) :=
  (let temp_1636 : int64 :=
      (secret (@repr U64 1013206390650290238)) in
    let temp_1638 : int64 :=
      (secret (@repr U64 7720336747103001025)) in
    let temp_1640 : int64 :=
      (secret (@repr U64 8197694151986493523)) in
    let temp_1642 : int64 :=
      (secret (@repr U64 3625112747029342752)) in
    let temp_1644 : int64 :=
      (secret (@repr U64 6675167463148394368)) in
    let temp_1646 : int64 :=
      (secret (@repr U64 4905905684016745359)) in
    let temp_1648 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_1636;
          temp_1638;
          temp_1640;
          temp_1642;
          temp_1644;
          temp_1646
        ]) in
    (temp_1648)).

Definition y_1736_loc : ChoiceEqualityLocation :=
  ((fp_t ; 1748%nat)).
Definition x1_1702_loc : ChoiceEqualityLocation :=
  ((fp_t ; 1749%nat)).
Notation "'g1_simple_swu_iso_inp'" := (
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_simple_swu_iso_out'" := ((fp_t '× fp_t
  ) : choice_type) (in custom pack_type at level 2).
Definition G1_SIMPLE_SWU_ISO : nat :=
  (1750).
Program Definition g1_simple_swu_iso
   : package (CEfset ([x1_1702_loc ; y_1736_loc])) [interface
  #val #[ FP_IS_SQUARE ] : fp_is_square_inp → fp_is_square_out ;
  #val #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out ;
  #val #[ FP_SQRT ] : fp_sqrt_inp → fp_sqrt_out ] [interface
  #val #[ G1_SIMPLE_SWU_ISO ] : g1_simple_swu_iso_inp → g1_simple_swu_iso_out
  ] :=
  (
    [package #def #[ G1_SIMPLE_SWU_ISO ] (temp_inp : g1_simple_swu_iso_inp) : g1_simple_swu_iso_out { 
    let '(u_1662) := temp_inp : fp_t in
    #import {sig #[ FP_IS_SQUARE ] : fp_is_square_inp → fp_is_square_out } as  fp_is_square ;;
    let fp_is_square := fun x_0 => fp_is_square (x_0) in
    #import {sig #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out } as  fp_sgn0 ;;
    let fp_sgn0 := fun x_0 => fp_sgn0 (x_0) in
    #import {sig #[ FP_SQRT ] : fp_sqrt_inp → fp_sqrt_out } as  fp_sqrt ;;
    let fp_sqrt := fun x_0 => fp_sqrt (x_0) in
    ({ code  '(z_1659 : fp_t) ←
        ( '(temp_1650 : fp_t) ←
            (nat_mod_from_literal (_) (@repr U128 11)) ;;
          ret (temp_1650)) ;;
       '(a_1680 : fp_t) ←
        ( '(temp_1652 : seq int8) ←
            (array_to_be_bytes (g1_iso_a_v)) ;;
           '(temp_1654 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1652)) ;;
          ret (temp_1654)) ;;
       '(b_1677 : fp_t) ←
        ( '(temp_1656 : seq int8) ←
            (array_to_be_bytes (g1_iso_b_v)) ;;
           '(temp_1658 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1656)) ;;
          ret (temp_1658)) ;;
       '(tv1_1687 : fp_t) ←
        ( '(temp_1661 : fp_t) ←
            ((z_1659) *% (z_1659)) ;;
           temp_1664 ←
            (nat_mod_exp (u_1662) (@repr U32 4)) ;;
           '(temp_1666 : fp_t) ←
            ((temp_1661) *% (temp_1664)) ;;
           '(temp_1668 : fp_t) ←
            ((z_1659) *% (u_1662)) ;;
           '(temp_1670 : fp_t) ←
            ((temp_1668) *% (u_1662)) ;;
           '(temp_1672 : fp_t) ←
            ((temp_1666) +% (temp_1670)) ;;
           temp_1674 ←
            (nat_mod_inv (temp_1672)) ;;
          ret (temp_1674)) ;;
       '(x1_1702 : fp_t) ←
          ( '(temp_1676 : fp_t) ←
              (nat_mod_zero ) ;;
             '(temp_1679 : fp_t) ←
              ((temp_1676) -% (b_1677)) ;;
             temp_1682 ←
              (nat_mod_inv (a_1680)) ;;
             '(temp_1684 : fp_t) ←
              ((temp_1679) *% (temp_1682)) ;;
             '(temp_1686 : fp_t) ←
              (nat_mod_one ) ;;
             '(temp_1689 : fp_t) ←
              ((temp_1686) +% (tv1_1687)) ;;
             '(temp_1691 : fp_t) ←
              ((temp_1684) *% (temp_1689)) ;;
            ret (temp_1691)) ;;
        #put x1_1702_loc := x1_1702 ;;
       '(temp_1693 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_1695 : bool_ChoiceEquality) ←
        ((tv1_1687) =.? (temp_1693)) ;;
       '(x1_1702 : (fp_t)) ←
        (if temp_1695:bool_ChoiceEquality
          then (({ code  '(x1_1702 : fp_t) ←
                  (( '(temp_1697 : fp_t) ←
                        ((z_1659) *% (a_1680)) ;;
                       temp_1699 ←
                        (nat_mod_inv (temp_1697)) ;;
                       '(temp_1701 : fp_t) ←
                        ((b_1677) *% (temp_1699)) ;;
                      ret (temp_1701))) ;;
                #put x1_1702_loc := x1_1702 ;;
              
              @ret ((fp_t)) (x1_1702) } : code (CEfset (
                  [x1_1702_loc])) [interface  ] _))
          else @ret ((fp_t)) (x1_1702)) ;;
      
       '(gx1_1726 : fp_t) ←
        ( temp_1704 ←
            (nat_mod_exp (x1_1702) (@repr U32 3)) ;;
           '(temp_1706 : fp_t) ←
            ((a_1680) *% (x1_1702)) ;;
           '(temp_1708 : fp_t) ←
            ((temp_1704) +% (temp_1706)) ;;
           '(temp_1710 : fp_t) ←
            ((temp_1708) +% (b_1677)) ;;
          ret (temp_1710)) ;;
       '(x2_1717 : fp_t) ←
        ( '(temp_1712 : fp_t) ←
            ((z_1659) *% (u_1662)) ;;
           '(temp_1714 : fp_t) ←
            ((temp_1712) *% (u_1662)) ;;
           '(temp_1716 : fp_t) ←
            ((temp_1714) *% (x1_1702)) ;;
          ret (temp_1716)) ;;
       '(gx2_1731 : fp_t) ←
        ( temp_1719 ←
            (nat_mod_exp (x2_1717) (@repr U32 3)) ;;
           '(temp_1721 : fp_t) ←
            ((a_1680) *% (x2_1717)) ;;
           '(temp_1723 : fp_t) ←
            ((temp_1719) +% (temp_1721)) ;;
           '(temp_1725 : fp_t) ←
            ((temp_1723) +% (b_1677)) ;;
          ret (temp_1725)) ;;
       temp_1747 ←
        ( '(temp_1728 : bool_ChoiceEquality) ←
            (fp_is_square (gx1_1726)) ;;
           '(temp_1730 : fp_t) ←
            (fp_sqrt (gx1_1726)) ;;
           '(temp_1733 : fp_t) ←
            (fp_sqrt (gx2_1731)) ;;
          ret ((if (temp_1728):bool_ChoiceEquality then (prod_ce(
                  x1_1702,
                  temp_1730
                )) else (prod_ce(x2_1717, temp_1733))))) ;;
      let '(x_1745, y_1736) :=
        (temp_1747) : (fp_t '× fp_t) in
       '(temp_1735 : bool_ChoiceEquality) ←
        (fp_sgn0 (u_1662)) ;;
       '(temp_1738 : bool_ChoiceEquality) ←
        (fp_sgn0 (y_1736)) ;;
       '(temp_1740 : bool_ChoiceEquality) ←
        ((temp_1735) !=.? (temp_1738)) ;;
       '(y_1736 : (fp_t)) ←
        (if temp_1740:bool_ChoiceEquality
          then (({ code  '(y_1736 : fp_t) ←
                  (( '(temp_1742 : fp_t) ←
                        (nat_mod_zero ) ;;
                       '(temp_1744 : fp_t) ←
                        ((temp_1742) -% (y_1736)) ;;
                      ret (temp_1744))) ;;
                #put y_1736_loc := y_1736 ;;
              
              @ret ((fp_t)) (y_1736) } : code (CEfset (
                  [x1_1702_loc ; y_1736_loc])) [interface  ] _))
          else @ret ((fp_t)) (y_1736)) ;;
      
      @ret ((fp_t '× fp_t)) (prod_ce(x_1745, y_1736)) } : code (CEfset (
          [x1_1702_loc ; y_1736_loc])) [interface
      #val #[ FP_IS_SQUARE ] : fp_is_square_inp → fp_is_square_out ;
      #val #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out ;
      #val #[ FP_SQRT ] : fp_sqrt_inp → fp_sqrt_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_g1_simple_swu_iso : package _ _ _ :=
  (seq_link g1_simple_swu_iso link_rest(
      package_fp_is_square,package_fp_sgn0,package_fp_sqrt)).
Fail Next Obligation.

Definition xx_2019_loc : ChoiceEqualityLocation :=
  ((fp_t ; 2080%nat)).
Definition xx_1979_loc : ChoiceEqualityLocation :=
  ((fp_t ; 2081%nat)).
Definition inf_2069_loc : ChoiceEqualityLocation :=
  ((bool_ChoiceEquality ; 2082%nat)).
Definition xx_2036_loc : ChoiceEqualityLocation :=
  ((fp_t ; 2083%nat)).
Definition xnum_k_1975_loc : ChoiceEqualityLocation :=
  ((seq fp_t ; 2084%nat)).
Definition xnum_1978_loc : ChoiceEqualityLocation :=
  ((fp_t ; 2085%nat)).
Definition xden_1999_loc : ChoiceEqualityLocation :=
  ((fp_t ; 2086%nat)).
Definition xx_2000_loc : ChoiceEqualityLocation :=
  ((fp_t ; 2087%nat)).
Definition yden_k_1992_loc : ChoiceEqualityLocation :=
  ((seq fp_t ; 2088%nat)).
Definition yden_2035_loc : ChoiceEqualityLocation :=
  ((fp_t ; 2089%nat)).
Definition ynum_k_1991_loc : ChoiceEqualityLocation :=
  ((seq fp_t ; 2090%nat)).
Definition ynum_2018_loc : ChoiceEqualityLocation :=
  ((fp_t ; 2091%nat)).
Definition xden_k_1990_loc : ChoiceEqualityLocation :=
  ((seq fp_t ; 2092%nat)).
Notation "'g1_isogeny_map_inp'" := (
  fp_t '× fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_isogeny_map_out'" := (
  g1_t : choice_type) (in custom pack_type at level 2).
Definition G1_ISOGENY_MAP : nat :=
  (2093).
Program Definition g1_isogeny_map
   : package (CEfset (
      [xnum_k_1975_loc ; xden_k_1990_loc ; ynum_k_1991_loc ; yden_k_1992_loc ; xnum_1978_loc ; xx_1979_loc ; xden_1999_loc ; xx_2000_loc ; ynum_2018_loc ; xx_2019_loc ; yden_2035_loc ; xx_2036_loc ; inf_2069_loc])) [interface
   ] [interface
  #val #[ G1_ISOGENY_MAP ] : g1_isogeny_map_inp → g1_isogeny_map_out ] :=
  (
    [package #def #[ G1_ISOGENY_MAP ] (temp_inp : g1_isogeny_map_inp) : g1_isogeny_map_out { 
    let '(x_1987 , y_2052) := temp_inp : fp_t '× fp_t in
    ({ code  '(xnum_k_1975 : seq fp_t) ←
          ( temp_1752 ←
              (seq_new_ (default : fp_t) (usize 12)) ;;
            ret (temp_1752)) ;;
        #put xnum_k_1975_loc := xnum_k_1975 ;;
       '(xnum_k_1975 : seq fp_t) ←
        ( '(temp_1754 : seq int8) ←
            (array_to_be_bytes (g1_xnum_k_0_v)) ;;
           '(temp_1756 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1754)) ;;
          ret (seq_upd xnum_k_1975 (usize 0) (temp_1756))) ;;
      
       '(xnum_k_1975 : seq fp_t) ←
        ( '(temp_1758 : seq int8) ←
            (array_to_be_bytes (g1_xnum_k_1_v)) ;;
           '(temp_1760 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1758)) ;;
          ret (seq_upd xnum_k_1975 (usize 1) (temp_1760))) ;;
      
       '(xnum_k_1975 : seq fp_t) ←
        ( '(temp_1762 : seq int8) ←
            (array_to_be_bytes (g1_xnum_k_2_v)) ;;
           '(temp_1764 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1762)) ;;
          ret (seq_upd xnum_k_1975 (usize 2) (temp_1764))) ;;
      
       '(xnum_k_1975 : seq fp_t) ←
        ( '(temp_1766 : seq int8) ←
            (array_to_be_bytes (g1_xnum_k_3_v)) ;;
           '(temp_1768 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1766)) ;;
          ret (seq_upd xnum_k_1975 (usize 3) (temp_1768))) ;;
      
       '(xnum_k_1975 : seq fp_t) ←
        ( '(temp_1770 : seq int8) ←
            (array_to_be_bytes (g1_xnum_k_4_v)) ;;
           '(temp_1772 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1770)) ;;
          ret (seq_upd xnum_k_1975 (usize 4) (temp_1772))) ;;
      
       '(xnum_k_1975 : seq fp_t) ←
        ( '(temp_1774 : seq int8) ←
            (array_to_be_bytes (g1_xnum_k_5_v)) ;;
           '(temp_1776 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1774)) ;;
          ret (seq_upd xnum_k_1975 (usize 5) (temp_1776))) ;;
      
       '(xnum_k_1975 : seq fp_t) ←
        ( '(temp_1778 : seq int8) ←
            (array_to_be_bytes (g1_xnum_k_6_v)) ;;
           '(temp_1780 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1778)) ;;
          ret (seq_upd xnum_k_1975 (usize 6) (temp_1780))) ;;
      
       '(xnum_k_1975 : seq fp_t) ←
        ( '(temp_1782 : seq int8) ←
            (array_to_be_bytes (g1_xnum_k_7_v)) ;;
           '(temp_1784 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1782)) ;;
          ret (seq_upd xnum_k_1975 (usize 7) (temp_1784))) ;;
      
       '(xnum_k_1975 : seq fp_t) ←
        ( '(temp_1786 : seq int8) ←
            (array_to_be_bytes (g1_xnum_k_8_v)) ;;
           '(temp_1788 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1786)) ;;
          ret (seq_upd xnum_k_1975 (usize 8) (temp_1788))) ;;
      
       '(xnum_k_1975 : seq fp_t) ←
        ( '(temp_1790 : seq int8) ←
            (array_to_be_bytes (g1_xnum_k_9_v)) ;;
           '(temp_1792 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1790)) ;;
          ret (seq_upd xnum_k_1975 (usize 9) (temp_1792))) ;;
      
       '(xnum_k_1975 : seq fp_t) ←
        ( '(temp_1794 : seq int8) ←
            (array_to_be_bytes (g1_xnum_k_10_v)) ;;
           '(temp_1796 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1794)) ;;
          ret (seq_upd xnum_k_1975 (usize 10) (temp_1796))) ;;
      
       '(xnum_k_1975 : seq fp_t) ←
        ( '(temp_1798 : seq int8) ←
            (array_to_be_bytes (g1_xnum_k_11_v)) ;;
           '(temp_1800 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1798)) ;;
          ret (seq_upd xnum_k_1975 (usize 11) (temp_1800))) ;;
      
       '(xden_k_1990 : seq fp_t) ←
          ( temp_1802 ←
              (seq_new_ (default : fp_t) (usize 10)) ;;
            ret (temp_1802)) ;;
        #put xden_k_1990_loc := xden_k_1990 ;;
       '(xden_k_1990 : seq fp_t) ←
        ( '(temp_1804 : seq int8) ←
            (array_to_be_bytes (g1_xden_k_0_v)) ;;
           '(temp_1806 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1804)) ;;
          ret (seq_upd xden_k_1990 (usize 0) (temp_1806))) ;;
      
       '(xden_k_1990 : seq fp_t) ←
        ( '(temp_1808 : seq int8) ←
            (array_to_be_bytes (g1_xden_k_1_v)) ;;
           '(temp_1810 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1808)) ;;
          ret (seq_upd xden_k_1990 (usize 1) (temp_1810))) ;;
      
       '(xden_k_1990 : seq fp_t) ←
        ( '(temp_1812 : seq int8) ←
            (array_to_be_bytes (g1_xden_k_2_v)) ;;
           '(temp_1814 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1812)) ;;
          ret (seq_upd xden_k_1990 (usize 2) (temp_1814))) ;;
      
       '(xden_k_1990 : seq fp_t) ←
        ( '(temp_1816 : seq int8) ←
            (array_to_be_bytes (g1_xden_k_3_v)) ;;
           '(temp_1818 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1816)) ;;
          ret (seq_upd xden_k_1990 (usize 3) (temp_1818))) ;;
      
       '(xden_k_1990 : seq fp_t) ←
        ( '(temp_1820 : seq int8) ←
            (array_to_be_bytes (g1_xden_k_4_v)) ;;
           '(temp_1822 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1820)) ;;
          ret (seq_upd xden_k_1990 (usize 4) (temp_1822))) ;;
      
       '(xden_k_1990 : seq fp_t) ←
        ( '(temp_1824 : seq int8) ←
            (array_to_be_bytes (g1_xden_k_5_v)) ;;
           '(temp_1826 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1824)) ;;
          ret (seq_upd xden_k_1990 (usize 5) (temp_1826))) ;;
      
       '(xden_k_1990 : seq fp_t) ←
        ( '(temp_1828 : seq int8) ←
            (array_to_be_bytes (g1_xden_k_6_v)) ;;
           '(temp_1830 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1828)) ;;
          ret (seq_upd xden_k_1990 (usize 6) (temp_1830))) ;;
      
       '(xden_k_1990 : seq fp_t) ←
        ( '(temp_1832 : seq int8) ←
            (array_to_be_bytes (g1_xden_k_7_v)) ;;
           '(temp_1834 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1832)) ;;
          ret (seq_upd xden_k_1990 (usize 7) (temp_1834))) ;;
      
       '(xden_k_1990 : seq fp_t) ←
        ( '(temp_1836 : seq int8) ←
            (array_to_be_bytes (g1_xden_k_8_v)) ;;
           '(temp_1838 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1836)) ;;
          ret (seq_upd xden_k_1990 (usize 8) (temp_1838))) ;;
      
       '(xden_k_1990 : seq fp_t) ←
        ( '(temp_1840 : seq int8) ←
            (array_to_be_bytes (g1_xden_k_9_v)) ;;
           '(temp_1842 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1840)) ;;
          ret (seq_upd xden_k_1990 (usize 9) (temp_1842))) ;;
      
       '(ynum_k_1991 : seq fp_t) ←
          ( temp_1844 ←
              (seq_new_ (default : fp_t) (usize 16)) ;;
            ret (temp_1844)) ;;
        #put ynum_k_1991_loc := ynum_k_1991 ;;
       '(ynum_k_1991 : seq fp_t) ←
        ( '(temp_1846 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_0_v)) ;;
           '(temp_1848 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1846)) ;;
          ret (seq_upd ynum_k_1991 (usize 0) (temp_1848))) ;;
      
       '(ynum_k_1991 : seq fp_t) ←
        ( '(temp_1850 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_1_v)) ;;
           '(temp_1852 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1850)) ;;
          ret (seq_upd ynum_k_1991 (usize 1) (temp_1852))) ;;
      
       '(ynum_k_1991 : seq fp_t) ←
        ( '(temp_1854 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_2_v)) ;;
           '(temp_1856 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1854)) ;;
          ret (seq_upd ynum_k_1991 (usize 2) (temp_1856))) ;;
      
       '(ynum_k_1991 : seq fp_t) ←
        ( '(temp_1858 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_3_v)) ;;
           '(temp_1860 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1858)) ;;
          ret (seq_upd ynum_k_1991 (usize 3) (temp_1860))) ;;
      
       '(ynum_k_1991 : seq fp_t) ←
        ( '(temp_1862 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_4_v)) ;;
           '(temp_1864 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1862)) ;;
          ret (seq_upd ynum_k_1991 (usize 4) (temp_1864))) ;;
      
       '(ynum_k_1991 : seq fp_t) ←
        ( '(temp_1866 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_5_v)) ;;
           '(temp_1868 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1866)) ;;
          ret (seq_upd ynum_k_1991 (usize 5) (temp_1868))) ;;
      
       '(ynum_k_1991 : seq fp_t) ←
        ( '(temp_1870 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_6_v)) ;;
           '(temp_1872 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1870)) ;;
          ret (seq_upd ynum_k_1991 (usize 6) (temp_1872))) ;;
      
       '(ynum_k_1991 : seq fp_t) ←
        ( '(temp_1874 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_7_v)) ;;
           '(temp_1876 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1874)) ;;
          ret (seq_upd ynum_k_1991 (usize 7) (temp_1876))) ;;
      
       '(ynum_k_1991 : seq fp_t) ←
        ( '(temp_1878 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_8_v)) ;;
           '(temp_1880 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1878)) ;;
          ret (seq_upd ynum_k_1991 (usize 8) (temp_1880))) ;;
      
       '(ynum_k_1991 : seq fp_t) ←
        ( '(temp_1882 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_9_v)) ;;
           '(temp_1884 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1882)) ;;
          ret (seq_upd ynum_k_1991 (usize 9) (temp_1884))) ;;
      
       '(ynum_k_1991 : seq fp_t) ←
        ( '(temp_1886 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_10_v)) ;;
           '(temp_1888 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1886)) ;;
          ret (seq_upd ynum_k_1991 (usize 10) (temp_1888))) ;;
      
       '(ynum_k_1991 : seq fp_t) ←
        ( '(temp_1890 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_11_v)) ;;
           '(temp_1892 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1890)) ;;
          ret (seq_upd ynum_k_1991 (usize 11) (temp_1892))) ;;
      
       '(ynum_k_1991 : seq fp_t) ←
        ( '(temp_1894 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_12_v)) ;;
           '(temp_1896 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1894)) ;;
          ret (seq_upd ynum_k_1991 (usize 12) (temp_1896))) ;;
      
       '(ynum_k_1991 : seq fp_t) ←
        ( '(temp_1898 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_13_v)) ;;
           '(temp_1900 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1898)) ;;
          ret (seq_upd ynum_k_1991 (usize 13) (temp_1900))) ;;
      
       '(ynum_k_1991 : seq fp_t) ←
        ( '(temp_1902 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_14_v)) ;;
           '(temp_1904 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1902)) ;;
          ret (seq_upd ynum_k_1991 (usize 14) (temp_1904))) ;;
      
       '(ynum_k_1991 : seq fp_t) ←
        ( '(temp_1906 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_15_v)) ;;
           '(temp_1908 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1906)) ;;
          ret (seq_upd ynum_k_1991 (usize 15) (temp_1908))) ;;
      
       '(yden_k_1992 : seq fp_t) ←
          ( temp_1910 ←
              (seq_new_ (default : fp_t) (usize 15)) ;;
            ret (temp_1910)) ;;
        #put yden_k_1992_loc := yden_k_1992 ;;
       '(yden_k_1992 : seq fp_t) ←
        ( '(temp_1912 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_0_v)) ;;
           '(temp_1914 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1912)) ;;
          ret (seq_upd yden_k_1992 (usize 0) (temp_1914))) ;;
      
       '(yden_k_1992 : seq fp_t) ←
        ( '(temp_1916 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_1_v)) ;;
           '(temp_1918 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1916)) ;;
          ret (seq_upd yden_k_1992 (usize 1) (temp_1918))) ;;
      
       '(yden_k_1992 : seq fp_t) ←
        ( '(temp_1920 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_2_v)) ;;
           '(temp_1922 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1920)) ;;
          ret (seq_upd yden_k_1992 (usize 2) (temp_1922))) ;;
      
       '(yden_k_1992 : seq fp_t) ←
        ( '(temp_1924 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_3_v)) ;;
           '(temp_1926 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1924)) ;;
          ret (seq_upd yden_k_1992 (usize 3) (temp_1926))) ;;
      
       '(yden_k_1992 : seq fp_t) ←
        ( '(temp_1928 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_4_v)) ;;
           '(temp_1930 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1928)) ;;
          ret (seq_upd yden_k_1992 (usize 4) (temp_1930))) ;;
      
       '(yden_k_1992 : seq fp_t) ←
        ( '(temp_1932 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_5_v)) ;;
           '(temp_1934 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1932)) ;;
          ret (seq_upd yden_k_1992 (usize 5) (temp_1934))) ;;
      
       '(yden_k_1992 : seq fp_t) ←
        ( '(temp_1936 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_6_v)) ;;
           '(temp_1938 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1936)) ;;
          ret (seq_upd yden_k_1992 (usize 6) (temp_1938))) ;;
      
       '(yden_k_1992 : seq fp_t) ←
        ( '(temp_1940 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_7_v)) ;;
           '(temp_1942 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1940)) ;;
          ret (seq_upd yden_k_1992 (usize 7) (temp_1942))) ;;
      
       '(yden_k_1992 : seq fp_t) ←
        ( '(temp_1944 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_8_v)) ;;
           '(temp_1946 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1944)) ;;
          ret (seq_upd yden_k_1992 (usize 8) (temp_1946))) ;;
      
       '(yden_k_1992 : seq fp_t) ←
        ( '(temp_1948 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_9_v)) ;;
           '(temp_1950 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1948)) ;;
          ret (seq_upd yden_k_1992 (usize 9) (temp_1950))) ;;
      
       '(yden_k_1992 : seq fp_t) ←
        ( '(temp_1952 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_10_v)) ;;
           '(temp_1954 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1952)) ;;
          ret (seq_upd yden_k_1992 (usize 10) (temp_1954))) ;;
      
       '(yden_k_1992 : seq fp_t) ←
        ( '(temp_1956 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_11_v)) ;;
           '(temp_1958 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1956)) ;;
          ret (seq_upd yden_k_1992 (usize 11) (temp_1958))) ;;
      
       '(yden_k_1992 : seq fp_t) ←
        ( '(temp_1960 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_12_v)) ;;
           '(temp_1962 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1960)) ;;
          ret (seq_upd yden_k_1992 (usize 12) (temp_1962))) ;;
      
       '(yden_k_1992 : seq fp_t) ←
        ( '(temp_1964 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_13_v)) ;;
           '(temp_1966 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1964)) ;;
          ret (seq_upd yden_k_1992 (usize 13) (temp_1966))) ;;
      
       '(yden_k_1992 : seq fp_t) ←
        ( '(temp_1968 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_14_v)) ;;
           '(temp_1970 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_1968)) ;;
          ret (seq_upd yden_k_1992 (usize 14) (temp_1970))) ;;
      
       '(xnum_1978 : fp_t) ←
          ( '(temp_1972 : fp_t) ←
              (nat_mod_zero ) ;;
            ret (temp_1972)) ;;
        #put xnum_1978_loc := xnum_1978 ;;
       '(xx_1979 : fp_t) ←
          ( '(temp_1974 : fp_t) ←
              (nat_mod_one ) ;;
            ret (temp_1974)) ;;
        #put xx_1979_loc := xx_1979 ;;
       '(temp_1977 : uint_size) ←
        (seq_len (xnum_k_1975)) ;;
       temp_2079 ←
        (foldi' (usize 0) (temp_1977) prod_ce(xnum_1978, xx_1979) (
              L2 := CEfset (
                [xnum_k_1975_loc ; xden_k_1990_loc ; ynum_k_1991_loc ; yden_k_1992_loc ; xnum_1978_loc ; xx_1979_loc ; xden_1999_loc ; xx_2000_loc ; ynum_2018_loc ; xx_2019_loc ; yden_2035_loc ; xx_2036_loc ; inf_2069_loc])) (
              I2 := [interface 
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_1980 '(
              xnum_1978,
              xx_1979
            ) =>
            ({ code  '(xnum_1978 : fp_t) ←
                  (( '(temp_1982 : fp_t) ←
                        (seq_index (xnum_k_1975) (i_1980)) ;;
                       '(temp_1984 : fp_t) ←
                        ((xx_1979) *% (temp_1982)) ;;
                       '(temp_1986 : fp_t) ←
                        ((xnum_1978) +% (temp_1984)) ;;
                      ret (temp_1986))) ;;
                #put xnum_1978_loc := xnum_1978 ;;
              
               '(xx_1979 : fp_t) ←
                  (( '(temp_1989 : fp_t) ←
                        ((xx_1979) *% (x_1987)) ;;
                      ret (temp_1989))) ;;
                #put xx_1979_loc := xx_1979 ;;
              
              @ret ((fp_t '× fp_t)) (prod_ce(xnum_1978, xx_1979)) } : code (
                CEfset (
                  [xnum_k_1975_loc ; xden_k_1990_loc ; ynum_k_1991_loc ; yden_k_1992_loc ; xnum_1978_loc ; xx_1979_loc])) [interface
               ] _))) ;;
      let '(xnum_1978, xx_1979) :=
        (temp_2079) : (fp_t '× fp_t) in
      
       '(xden_1999 : fp_t) ←
          ( '(temp_1994 : fp_t) ←
              (nat_mod_zero ) ;;
            ret (temp_1994)) ;;
        #put xden_1999_loc := xden_1999 ;;
       '(xx_2000 : fp_t) ←
          ( '(temp_1996 : fp_t) ←
              (nat_mod_one ) ;;
            ret (temp_1996)) ;;
        #put xx_2000_loc := xx_2000 ;;
       '(temp_1998 : uint_size) ←
        (seq_len (xden_k_1990)) ;;
       temp_2077 ←
        (foldi' (usize 0) (temp_1998) prod_ce(xden_1999, xx_2000) (
              L2 := CEfset (
                [xnum_k_1975_loc ; xden_k_1990_loc ; ynum_k_1991_loc ; yden_k_1992_loc ; xnum_1978_loc ; xx_1979_loc ; xden_1999_loc ; xx_2000_loc ; ynum_2018_loc ; xx_2019_loc ; yden_2035_loc ; xx_2036_loc ; inf_2069_loc])) (
              I2 := [interface 
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_2001 '(
              xden_1999,
              xx_2000
            ) =>
            ({ code  '(xden_1999 : fp_t) ←
                  (( '(temp_2003 : fp_t) ←
                        (seq_index (xden_k_1990) (i_2001)) ;;
                       '(temp_2005 : fp_t) ←
                        ((xx_2000) *% (temp_2003)) ;;
                       '(temp_2007 : fp_t) ←
                        ((xden_1999) +% (temp_2005)) ;;
                      ret (temp_2007))) ;;
                #put xden_1999_loc := xden_1999 ;;
              
               '(xx_2000 : fp_t) ←
                  (( '(temp_2009 : fp_t) ←
                        ((xx_2000) *% (x_1987)) ;;
                      ret (temp_2009))) ;;
                #put xx_2000_loc := xx_2000 ;;
              
              @ret ((fp_t '× fp_t)) (prod_ce(xden_1999, xx_2000)) } : code (
                CEfset (
                  [xnum_k_1975_loc ; xden_k_1990_loc ; ynum_k_1991_loc ; yden_k_1992_loc ; xnum_1978_loc ; xx_1979_loc ; xden_1999_loc ; xx_2000_loc])) [interface
               ] _))) ;;
      let '(xden_1999, xx_2000) :=
        (temp_2077) : (fp_t '× fp_t) in
      
       '(xden_1999 : fp_t) ←
          (( '(temp_2011 : fp_t) ←
                ((xden_1999) +% (xx_2000)) ;;
              ret (temp_2011))) ;;
        #put xden_1999_loc := xden_1999 ;;
      
       '(ynum_2018 : fp_t) ←
          ( '(temp_2013 : fp_t) ←
              (nat_mod_zero ) ;;
            ret (temp_2013)) ;;
        #put ynum_2018_loc := ynum_2018 ;;
       '(xx_2019 : fp_t) ←
          ( '(temp_2015 : fp_t) ←
              (nat_mod_one ) ;;
            ret (temp_2015)) ;;
        #put xx_2019_loc := xx_2019 ;;
       '(temp_2017 : uint_size) ←
        (seq_len (ynum_k_1991)) ;;
       temp_2075 ←
        (foldi' (usize 0) (temp_2017) prod_ce(ynum_2018, xx_2019) (
              L2 := CEfset (
                [xnum_k_1975_loc ; xden_k_1990_loc ; ynum_k_1991_loc ; yden_k_1992_loc ; xnum_1978_loc ; xx_1979_loc ; xden_1999_loc ; xx_2000_loc ; ynum_2018_loc ; xx_2019_loc ; yden_2035_loc ; xx_2036_loc ; inf_2069_loc])) (
              I2 := [interface 
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_2020 '(
              ynum_2018,
              xx_2019
            ) =>
            ({ code  '(ynum_2018 : fp_t) ←
                  (( '(temp_2022 : fp_t) ←
                        (seq_index (ynum_k_1991) (i_2020)) ;;
                       '(temp_2024 : fp_t) ←
                        ((xx_2019) *% (temp_2022)) ;;
                       '(temp_2026 : fp_t) ←
                        ((ynum_2018) +% (temp_2024)) ;;
                      ret (temp_2026))) ;;
                #put ynum_2018_loc := ynum_2018 ;;
              
               '(xx_2019 : fp_t) ←
                  (( '(temp_2028 : fp_t) ←
                        ((xx_2019) *% (x_1987)) ;;
                      ret (temp_2028))) ;;
                #put xx_2019_loc := xx_2019 ;;
              
              @ret ((fp_t '× fp_t)) (prod_ce(ynum_2018, xx_2019)) } : code (
                CEfset (
                  [xnum_k_1975_loc ; xden_k_1990_loc ; ynum_k_1991_loc ; yden_k_1992_loc ; xnum_1978_loc ; xx_1979_loc ; xden_1999_loc ; xx_2000_loc ; ynum_2018_loc ; xx_2019_loc])) [interface
               ] _))) ;;
      let '(ynum_2018, xx_2019) :=
        (temp_2075) : (fp_t '× fp_t) in
      
       '(yden_2035 : fp_t) ←
          ( '(temp_2030 : fp_t) ←
              (nat_mod_zero ) ;;
            ret (temp_2030)) ;;
        #put yden_2035_loc := yden_2035 ;;
       '(xx_2036 : fp_t) ←
          ( '(temp_2032 : fp_t) ←
              (nat_mod_one ) ;;
            ret (temp_2032)) ;;
        #put xx_2036_loc := xx_2036 ;;
       '(temp_2034 : uint_size) ←
        (seq_len (yden_k_1992)) ;;
       temp_2073 ←
        (foldi' (usize 0) (temp_2034) prod_ce(yden_2035, xx_2036) (
              L2 := CEfset (
                [xnum_k_1975_loc ; xden_k_1990_loc ; ynum_k_1991_loc ; yden_k_1992_loc ; xnum_1978_loc ; xx_1979_loc ; xden_1999_loc ; xx_2000_loc ; ynum_2018_loc ; xx_2019_loc ; yden_2035_loc ; xx_2036_loc ; inf_2069_loc])) (
              I2 := [interface 
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_2037 '(
              yden_2035,
              xx_2036
            ) =>
            ({ code  '(yden_2035 : fp_t) ←
                  (( '(temp_2039 : fp_t) ←
                        (seq_index (yden_k_1992) (i_2037)) ;;
                       '(temp_2041 : fp_t) ←
                        ((xx_2036) *% (temp_2039)) ;;
                       '(temp_2043 : fp_t) ←
                        ((yden_2035) +% (temp_2041)) ;;
                      ret (temp_2043))) ;;
                #put yden_2035_loc := yden_2035 ;;
              
               '(xx_2036 : fp_t) ←
                  (( '(temp_2045 : fp_t) ←
                        ((xx_2036) *% (x_1987)) ;;
                      ret (temp_2045))) ;;
                #put xx_2036_loc := xx_2036 ;;
              
              @ret ((fp_t '× fp_t)) (prod_ce(yden_2035, xx_2036)) } : code (
                CEfset (
                  [xnum_k_1975_loc ; xden_k_1990_loc ; ynum_k_1991_loc ; yden_k_1992_loc ; xnum_1978_loc ; xx_1979_loc ; xden_1999_loc ; xx_2000_loc ; ynum_2018_loc ; xx_2019_loc ; yden_2035_loc ; xx_2036_loc])) [interface
               ] _))) ;;
      let '(yden_2035, xx_2036) :=
        (temp_2073) : (fp_t '× fp_t) in
      
       '(yden_2035 : fp_t) ←
          (( '(temp_2047 : fp_t) ←
                ((yden_2035) +% (xx_2036)) ;;
              ret (temp_2047))) ;;
        #put yden_2035_loc := yden_2035 ;;
      
       '(xr_2070 : fp_t) ←
        ( temp_2049 ←
            (nat_mod_inv (xden_1999)) ;;
           '(temp_2051 : fp_t) ←
            ((xnum_1978) *% (temp_2049)) ;;
          ret (temp_2051)) ;;
       '(yr_2071 : fp_t) ←
        ( '(temp_2054 : fp_t) ←
            ((y_2052) *% (ynum_2018)) ;;
           temp_2056 ←
            (nat_mod_inv (yden_2035)) ;;
           '(temp_2058 : fp_t) ←
            ((temp_2054) *% (temp_2056)) ;;
          ret (temp_2058)) ;;
       '(inf_2069 : bool_ChoiceEquality) ←
          (ret ((false : bool_ChoiceEquality))) ;;
        #put inf_2069_loc := inf_2069 ;;
       '(temp_2060 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_2062 : bool_ChoiceEquality) ←
        ((xden_1999) =.? (temp_2060)) ;;
       '(temp_2064 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_2066 : bool_ChoiceEquality) ←
        ((yden_2035) =.? (temp_2064)) ;;
       '(temp_2068 : bool_ChoiceEquality) ←
        ((temp_2062) || (temp_2066)) ;;
       '(inf_2069 : (bool_ChoiceEquality)) ←
        (if temp_2068:bool_ChoiceEquality
          then (({ code  '(inf_2069 : bool_ChoiceEquality) ←
                  ((ret ((true : bool_ChoiceEquality)))) ;;
                #put inf_2069_loc := inf_2069 ;;
              
              @ret ((bool_ChoiceEquality)) (inf_2069) } : code (CEfset (
                  [xnum_k_1975_loc ; xden_k_1990_loc ; ynum_k_1991_loc ; yden_k_1992_loc ; xnum_1978_loc ; xx_1979_loc ; xden_1999_loc ; xx_2000_loc ; ynum_2018_loc ; xx_2019_loc ; yden_2035_loc ; xx_2036_loc ; inf_2069_loc])) [interface
               ] _))
          else @ret ((bool_ChoiceEquality)) (inf_2069)) ;;
      
      @ret ((fp_t '× fp_t '× bool_ChoiceEquality)) (prod_ce(
          xr_2070,
          yr_2071,
          inf_2069
        )) } : code (CEfset (
          [xnum_k_1975_loc ; xden_k_1990_loc ; ynum_k_1991_loc ; yden_k_1992_loc ; xnum_1978_loc ; xx_1979_loc ; xden_1999_loc ; xx_2000_loc ; ynum_2018_loc ; xx_2019_loc ; yden_2035_loc ; xx_2036_loc ; inf_2069_loc])) [interface
       ] _)
    }]).
Fail Next Obligation.
Program Definition package_g1_isogeny_map : package _ _ _ :=
  (g1_isogeny_map).
Fail Next Obligation.


Notation "'g1_map_to_curve_sswu_inp'" := (
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_map_to_curve_sswu_out'" := (
  g1_t : choice_type) (in custom pack_type at level 2).
Definition G1_MAP_TO_CURVE_SSWU : nat :=
  (2104).
Program Definition g1_map_to_curve_sswu
   : package (CEfset ([])) [interface
  #val #[ G1_ISOGENY_MAP ] : g1_isogeny_map_inp → g1_isogeny_map_out ;
  #val #[ G1_SIMPLE_SWU_ISO ] : g1_simple_swu_iso_inp → g1_simple_swu_iso_out
  ] [interface
  #val #[ G1_MAP_TO_CURVE_SSWU ] : g1_map_to_curve_sswu_inp → g1_map_to_curve_sswu_out
  ] :=
  (
    [package #def #[ G1_MAP_TO_CURVE_SSWU ] (temp_inp : g1_map_to_curve_sswu_inp) : g1_map_to_curve_sswu_out { 
    let '(u_2094) := temp_inp : fp_t in
    #import {sig #[ G1_ISOGENY_MAP ] : g1_isogeny_map_inp → g1_isogeny_map_out } as  g1_isogeny_map ;;
    let g1_isogeny_map := fun x_0 x_1 => g1_isogeny_map (x_0,x_1) in
    #import {sig #[ G1_SIMPLE_SWU_ISO ] : g1_simple_swu_iso_inp → g1_simple_swu_iso_out } as  g1_simple_swu_iso ;;
    let g1_simple_swu_iso := fun x_0 => g1_simple_swu_iso (x_0) in
    ({ code  temp_2103 ←
        ( '(temp_2096 : (fp_t '× fp_t)) ←
            (g1_simple_swu_iso (u_2094)) ;;
          ret (temp_2096)) ;;
      let '(xp_2097, yp_2098) :=
        (temp_2103) : (fp_t '× fp_t) in
       '(p_2101 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( '(temp_2100 : g1_t) ←
            (g1_isogeny_map (xp_2097) (yp_2098)) ;;
          ret (temp_2100)) ;;
      @ret ((fp_t '× fp_t '× bool_ChoiceEquality)) (p_2101) } : code (CEfset (
          [])) [interface
      #val #[ G1_ISOGENY_MAP ] : g1_isogeny_map_inp → g1_isogeny_map_out ;
      #val #[ G1_SIMPLE_SWU_ISO ] : g1_simple_swu_iso_inp → g1_simple_swu_iso_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_g1_map_to_curve_sswu : package _ _ _ :=
  (seq_link g1_map_to_curve_sswu link_rest(
      package_g1_isogeny_map,package_g1_simple_swu_iso)).
Fail Next Obligation.


Notation "'g1_hash_to_curve_sswu_inp'" := (
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g1_hash_to_curve_sswu_out'" := (
  g1_t : choice_type) (in custom pack_type at level 2).
Definition G1_HASH_TO_CURVE_SSWU : nat :=
  (2126).
Program Definition g1_hash_to_curve_sswu
   : package (CEfset ([])) [interface
  #val #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out ;
  #val #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out ;
  #val #[ G1_MAP_TO_CURVE_SSWU ] : g1_map_to_curve_sswu_inp → g1_map_to_curve_sswu_out ;
  #val #[ G1ADD ] : g1add_inp → g1add_out ] [interface
  #val #[ G1_HASH_TO_CURVE_SSWU ] : g1_hash_to_curve_sswu_inp → g1_hash_to_curve_sswu_out
  ] :=
  (
    [package #def #[ G1_HASH_TO_CURVE_SSWU ] (temp_inp : g1_hash_to_curve_sswu_inp) : g1_hash_to_curve_sswu_out { 
    let '(msg_2105 , dst_2106) := temp_inp : byte_seq '× byte_seq in
    #import {sig #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out } as  fp_hash_to_field ;;
    let fp_hash_to_field := fun x_0 x_1 x_2 => fp_hash_to_field (x_0,x_1,x_2) in
    #import {sig #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out } as  g1_clear_cofactor ;;
    let g1_clear_cofactor := fun x_0 => g1_clear_cofactor (x_0) in
    #import {sig #[ G1_MAP_TO_CURVE_SSWU ] : g1_map_to_curve_sswu_inp → g1_map_to_curve_sswu_out } as  g1_map_to_curve_sswu ;;
    let g1_map_to_curve_sswu := fun x_0 => g1_map_to_curve_sswu (x_0) in
    #import {sig #[ G1ADD ] : g1add_inp → g1add_out } as  g1add ;;
    let g1add := fun x_0 x_1 => g1add (x_0,x_1) in
    ({ code  '(u_2110 : seq fp_t) ←
        ( '(temp_2108 : seq fp_t) ←
            (fp_hash_to_field (msg_2105) (dst_2106) (usize 2)) ;;
          ret (temp_2108)) ;;
       '(q0_2118 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( '(temp_2111 : fp_t) ←
            (seq_index (u_2110) (usize 0)) ;;
           '(temp_2113 : g1_t) ←
            (g1_map_to_curve_sswu (temp_2111)) ;;
          ret (temp_2113)) ;;
       '(q1_2119 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( '(temp_2115 : fp_t) ←
            (seq_index (u_2110) (usize 1)) ;;
           '(temp_2117 : g1_t) ←
            (g1_map_to_curve_sswu (temp_2115)) ;;
          ret (temp_2117)) ;;
       '(r_2122 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( temp_2121 ←
            (g1add (q0_2118) (q1_2119)) ;;
          ret (temp_2121)) ;;
       '(p_2125 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( '(temp_2124 : g1_t) ←
            (g1_clear_cofactor (r_2122)) ;;
          ret (temp_2124)) ;;
      @ret ((fp_t '× fp_t '× bool_ChoiceEquality)) (p_2125) } : code (CEfset (
          [])) [interface
      #val #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out ;
      #val #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out ;
      #val #[ G1_MAP_TO_CURVE_SSWU ] : g1_map_to_curve_sswu_inp → g1_map_to_curve_sswu_out ;
      #val #[ G1ADD ] : g1add_inp → g1add_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_g1_hash_to_curve_sswu : package _ _ _ :=
  (seq_link g1_hash_to_curve_sswu link_rest(
      package_fp_hash_to_field,package_g1_clear_cofactor,package_g1_map_to_curve_sswu,package_g1add)).
Fail Next Obligation.


Notation "'g1_encode_to_curve_sswu_inp'" := (
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g1_encode_to_curve_sswu_out'" := (
  g1_t : choice_type) (in custom pack_type at level 2).
Definition G1_ENCODE_TO_CURVE_SSWU : nat :=
  (2140).
Program Definition g1_encode_to_curve_sswu
   : package (CEfset ([])) [interface
  #val #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out ;
  #val #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out ;
  #val #[ G1_MAP_TO_CURVE_SSWU ] : g1_map_to_curve_sswu_inp → g1_map_to_curve_sswu_out
  ] [interface
  #val #[ G1_ENCODE_TO_CURVE_SSWU ] : g1_encode_to_curve_sswu_inp → g1_encode_to_curve_sswu_out
  ] :=
  (
    [package #def #[ G1_ENCODE_TO_CURVE_SSWU ] (temp_inp : g1_encode_to_curve_sswu_inp) : g1_encode_to_curve_sswu_out { 
    let '(msg_2127 , dst_2128) := temp_inp : byte_seq '× byte_seq in
    #import {sig #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out } as  fp_hash_to_field ;;
    let fp_hash_to_field := fun x_0 x_1 x_2 => fp_hash_to_field (x_0,x_1,x_2) in
    #import {sig #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out } as  g1_clear_cofactor ;;
    let g1_clear_cofactor := fun x_0 => g1_clear_cofactor (x_0) in
    #import {sig #[ G1_MAP_TO_CURVE_SSWU ] : g1_map_to_curve_sswu_inp → g1_map_to_curve_sswu_out } as  g1_map_to_curve_sswu ;;
    let g1_map_to_curve_sswu := fun x_0 => g1_map_to_curve_sswu (x_0) in
    ({ code  '(u_2132 : seq fp_t) ←
        ( '(temp_2130 : seq fp_t) ←
            (fp_hash_to_field (msg_2127) (dst_2128) (usize 1)) ;;
          ret (temp_2130)) ;;
       '(q_2136 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( '(temp_2133 : fp_t) ←
            (seq_index (u_2132) (usize 0)) ;;
           '(temp_2135 : g1_t) ←
            (g1_map_to_curve_sswu (temp_2133)) ;;
          ret (temp_2135)) ;;
       '(p_2139 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( '(temp_2138 : g1_t) ←
            (g1_clear_cofactor (q_2136)) ;;
          ret (temp_2138)) ;;
      @ret ((fp_t '× fp_t '× bool_ChoiceEquality)) (p_2139) } : code (CEfset (
          [])) [interface
      #val #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out ;
      #val #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out ;
      #val #[ G1_MAP_TO_CURVE_SSWU ] : g1_map_to_curve_sswu_inp → g1_map_to_curve_sswu_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_g1_encode_to_curve_sswu : package _ _ _ :=
  (seq_link g1_encode_to_curve_sswu link_rest(
      package_fp_hash_to_field,package_g1_clear_cofactor,package_g1_map_to_curve_sswu)).
Fail Next Obligation.

Definition g2_xnum_k_0_v : (arr_fp_t) :=
  (let temp_2142 : int64 :=
      (secret (@repr U64 416399692810564414)) in
    let temp_2144 : int64 :=
      (secret (@repr U64 13500519111022079365)) in
    let temp_2146 : int64 :=
      (secret (@repr U64 3658379999393219626)) in
    let temp_2148 : int64 :=
      (secret (@repr U64 9850925049107374429)) in
    let temp_2150 : int64 :=
      (secret (@repr U64 6640057249351452444)) in
    let temp_2152 : int64 :=
      (secret (@repr U64 7077594464397203414)) in
    let temp_2154 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_2142;
          temp_2144;
          temp_2146;
          temp_2148;
          temp_2150;
          temp_2152
        ]) in
    (temp_2154)).

Definition g2_xnum_k_1_i_v : (arr_fp_t) :=
  (let temp_2156 : int64 :=
      (secret (@repr U64 1249199078431693244)) in
    let temp_2158 : int64 :=
      (secret (@repr U64 3608069185647134863)) in
    let temp_2160 : int64 :=
      (secret (@repr U64 10975139998179658879)) in
    let temp_2162 : int64 :=
      (secret (@repr U64 11106031073612571672)) in
    let temp_2164 : int64 :=
      (secret (@repr U64 1473427674344805717)) in
    let temp_2166 : int64 :=
      (secret (@repr U64 2786039319482058522)) in
    let temp_2168 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_2156;
          temp_2158;
          temp_2160;
          temp_2162;
          temp_2164;
          temp_2166
        ]) in
    (temp_2168)).

Definition g2_xnum_k_2_r_v : (arr_fp_t) :=
  (let temp_2170 : int64 :=
      (secret (@repr U64 1249199078431693244)) in
    let temp_2172 : int64 :=
      (secret (@repr U64 3608069185647134863)) in
    let temp_2174 : int64 :=
      (secret (@repr U64 10975139998179658879)) in
    let temp_2176 : int64 :=
      (secret (@repr U64 11106031073612571672)) in
    let temp_2178 : int64 :=
      (secret (@repr U64 1473427674344805717)) in
    let temp_2180 : int64 :=
      (secret (@repr U64 2786039319482058526)) in
    let temp_2182 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_2170;
          temp_2172;
          temp_2174;
          temp_2176;
          temp_2178;
          temp_2180
        ]) in
    (temp_2182)).

Definition g2_xnum_k_2_i_v : (arr_fp_t) :=
  (let temp_2184 : int64 :=
      (secret (@repr U64 624599539215846622)) in
    let temp_2186 : int64 :=
      (secret (@repr U64 1804034592823567431)) in
    let temp_2188 : int64 :=
      (secret (@repr U64 14710942035944605247)) in
    let temp_2190 : int64 :=
      (secret (@repr U64 14776387573661061644)) in
    let temp_2192 : int64 :=
      (secret (@repr U64 736713837172402858)) in
    let temp_2194 : int64 :=
      (secret (@repr U64 10616391696595805069)) in
    let temp_2196 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_2184;
          temp_2186;
          temp_2188;
          temp_2190;
          temp_2192;
          temp_2194
        ]) in
    (temp_2196)).

Definition g2_xnum_k_3_r_v : (arr_fp_t) :=
  (let temp_2198 : int64 :=
      (secret (@repr U64 1665598771242257658)) in
    let temp_2200 : int64 :=
      (secret (@repr U64 17108588296669214228)) in
    let temp_2202 : int64 :=
      (secret (@repr U64 14633519997572878506)) in
    let temp_2204 : int64 :=
      (secret (@repr U64 2510212049010394485)) in
    let temp_2206 : int64 :=
      (secret (@repr U64 8113484923696258161)) in
    let temp_2208 : int64 :=
      (secret (@repr U64 9863633783879261905)) in
    let temp_2210 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_2198;
          temp_2200;
          temp_2202;
          temp_2204;
          temp_2206;
          temp_2208
        ]) in
    (temp_2210)).

Definition g2_xden_k_0_i_v : (arr_fp_t) :=
  (let temp_2212 : int64 :=
      (secret (@repr U64 1873798617647539866)) in
    let temp_2214 : int64 :=
      (secret (@repr U64 5412103778470702295)) in
    let temp_2216 : int64 :=
      (secret (@repr U64 7239337960414712511)) in
    let temp_2218 : int64 :=
      (secret (@repr U64 7435674573564081700)) in
    let temp_2220 : int64 :=
      (secret (@repr U64 2210141511517208575)) in
    let temp_2222 : int64 :=
      (secret (@repr U64 13402431016077863523)) in
    let temp_2224 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_2212;
          temp_2214;
          temp_2216;
          temp_2218;
          temp_2220;
          temp_2222
        ]) in
    (temp_2224)).

Definition g2_xden_k_1_i_v : (arr_fp_t) :=
  (let temp_2226 : int64 :=
      (secret (@repr U64 1873798617647539866)) in
    let temp_2228 : int64 :=
      (secret (@repr U64 5412103778470702295)) in
    let temp_2230 : int64 :=
      (secret (@repr U64 7239337960414712511)) in
    let temp_2232 : int64 :=
      (secret (@repr U64 7435674573564081700)) in
    let temp_2234 : int64 :=
      (secret (@repr U64 2210141511517208575)) in
    let temp_2236 : int64 :=
      (secret (@repr U64 13402431016077863583)) in
    let temp_2238 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_2226;
          temp_2228;
          temp_2230;
          temp_2232;
          temp_2234;
          temp_2236
        ]) in
    (temp_2238)).

Definition g2_ynum_k_0_v : (arr_fp_t) :=
  (let temp_2240 : int64 :=
      (secret (@repr U64 1526798873638736187)) in
    let temp_2242 : int64 :=
      (secret (@repr U64 6459500568425337235)) in
    let temp_2244 : int64 :=
      (secret (@repr U64 1116230615302104219)) in
    let temp_2246 : int64 :=
      (secret (@repr U64 17673314439684154624)) in
    let temp_2248 : int64 :=
      (secret (@repr U64 18197961889718808424)) in
    let temp_2250 : int64 :=
      (secret (@repr U64 1355520937843676934)) in
    let temp_2252 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_2240;
          temp_2242;
          temp_2244;
          temp_2246;
          temp_2248;
          temp_2250
        ]) in
    (temp_2252)).

Definition g2_ynum_k_1_i_v : (arr_fp_t) :=
  (let temp_2254 : int64 :=
      (secret (@repr U64 416399692810564414)) in
    let temp_2256 : int64 :=
      (secret (@repr U64 13500519111022079365)) in
    let temp_2258 : int64 :=
      (secret (@repr U64 3658379999393219626)) in
    let temp_2260 : int64 :=
      (secret (@repr U64 9850925049107374429)) in
    let temp_2262 : int64 :=
      (secret (@repr U64 6640057249351452444)) in
    let temp_2264 : int64 :=
      (secret (@repr U64 7077594464397203390)) in
    let temp_2266 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_2254;
          temp_2256;
          temp_2258;
          temp_2260;
          temp_2262;
          temp_2264
        ]) in
    (temp_2266)).

Definition g2_ynum_k_2_r_v : (arr_fp_t) :=
  (let temp_2268 : int64 :=
      (secret (@repr U64 1249199078431693244)) in
    let temp_2270 : int64 :=
      (secret (@repr U64 3608069185647134863)) in
    let temp_2272 : int64 :=
      (secret (@repr U64 10975139998179658879)) in
    let temp_2274 : int64 :=
      (secret (@repr U64 11106031073612571672)) in
    let temp_2276 : int64 :=
      (secret (@repr U64 1473427674344805717)) in
    let temp_2278 : int64 :=
      (secret (@repr U64 2786039319482058524)) in
    let temp_2280 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_2268;
          temp_2270;
          temp_2272;
          temp_2274;
          temp_2276;
          temp_2278
        ]) in
    (temp_2280)).

Definition g2_ynum_k_2_i_v : (arr_fp_t) :=
  (let temp_2282 : int64 :=
      (secret (@repr U64 624599539215846622)) in
    let temp_2284 : int64 :=
      (secret (@repr U64 1804034592823567431)) in
    let temp_2286 : int64 :=
      (secret (@repr U64 14710942035944605247)) in
    let temp_2288 : int64 :=
      (secret (@repr U64 14776387573661061644)) in
    let temp_2290 : int64 :=
      (secret (@repr U64 736713837172402858)) in
    let temp_2292 : int64 :=
      (secret (@repr U64 10616391696595805071)) in
    let temp_2294 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_2282;
          temp_2284;
          temp_2286;
          temp_2288;
          temp_2290;
          temp_2292
        ]) in
    (temp_2294)).

Definition g2_ynum_k_3_r_v : (arr_fp_t) :=
  (let temp_2296 : int64 :=
      (secret (@repr U64 1318599027233453979)) in
    let temp_2298 : int64 :=
      (secret (@repr U64 18155985086623849168)) in
    let temp_2300 : int64 :=
      (secret (@repr U64 8510412652460270214)) in
    let temp_2302 : int64 :=
      (secret (@repr U64 12747851915130467410)) in
    let temp_2304 : int64 :=
      (secret (@repr U64 5654561228188306393)) in
    let temp_2306 : int64 :=
      (secret (@repr U64 16263467779354626832)) in
    let temp_2308 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_2296;
          temp_2298;
          temp_2300;
          temp_2302;
          temp_2304;
          temp_2306
        ]) in
    (temp_2308)).

Definition g2_yden_k_0_v : (arr_fp_t) :=
  (let temp_2310 : int64 :=
      (secret (@repr U64 1873798617647539866)) in
    let temp_2312 : int64 :=
      (secret (@repr U64 5412103778470702295)) in
    let temp_2314 : int64 :=
      (secret (@repr U64 7239337960414712511)) in
    let temp_2316 : int64 :=
      (secret (@repr U64 7435674573564081700)) in
    let temp_2318 : int64 :=
      (secret (@repr U64 2210141511517208575)) in
    let temp_2320 : int64 :=
      (secret (@repr U64 13402431016077863163)) in
    let temp_2322 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_2310;
          temp_2312;
          temp_2314;
          temp_2316;
          temp_2318;
          temp_2320
        ]) in
    (temp_2322)).

Definition g2_yden_k_1_i_v : (arr_fp_t) :=
  (let temp_2324 : int64 :=
      (secret (@repr U64 1873798617647539866)) in
    let temp_2326 : int64 :=
      (secret (@repr U64 5412103778470702295)) in
    let temp_2328 : int64 :=
      (secret (@repr U64 7239337960414712511)) in
    let temp_2330 : int64 :=
      (secret (@repr U64 7435674573564081700)) in
    let temp_2332 : int64 :=
      (secret (@repr U64 2210141511517208575)) in
    let temp_2334 : int64 :=
      (secret (@repr U64 13402431016077863379)) in
    let temp_2336 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_2324;
          temp_2326;
          temp_2328;
          temp_2330;
          temp_2332;
          temp_2334
        ]) in
    (temp_2336)).

Definition g2_yden_k_2_i_v : (arr_fp_t) :=
  (let temp_2338 : int64 :=
      (secret (@repr U64 1873798617647539866)) in
    let temp_2340 : int64 :=
      (secret (@repr U64 5412103778470702295)) in
    let temp_2342 : int64 :=
      (secret (@repr U64 7239337960414712511)) in
    let temp_2344 : int64 :=
      (secret (@repr U64 7435674573564081700)) in
    let temp_2346 : int64 :=
      (secret (@repr U64 2210141511517208575)) in
    let temp_2348 : int64 :=
      (secret (@repr U64 13402431016077863577)) in
    let temp_2350 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_2338;
          temp_2340;
          temp_2342;
          temp_2344;
          temp_2346;
          temp_2348
        ]) in
    (temp_2350)).

Definition y_2450_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 2460%nat)).
Definition x1_2412_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 2461%nat)).
Notation "'g2_simple_swu_iso_inp'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_simple_swu_iso_out'" := ((fp2_t '× fp2_t
  ) : choice_type) (in custom pack_type at level 2).
Definition G2_SIMPLE_SWU_ISO : nat :=
  (2462).
Program Definition g2_simple_swu_iso
   : package (CEfset ([x1_2412_loc ; y_2450_loc])) [interface
  #val #[ FP2_IS_SQUARE ] : fp2_is_square_inp → fp2_is_square_out ;
  #val #[ FP2_SGN0 ] : fp2_sgn0_inp → fp2_sgn0_out ;
  #val #[ FP2_SQRT ] : fp2_sqrt_inp → fp2_sqrt_out ;
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
  #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ;
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ] [interface
  #val #[ G2_SIMPLE_SWU_ISO ] : g2_simple_swu_iso_inp → g2_simple_swu_iso_out
  ] :=
  (
    [package #def #[ G2_SIMPLE_SWU_ISO ] (temp_inp : g2_simple_swu_iso_inp) : g2_simple_swu_iso_out { 
    let '(u_2368) := temp_inp : fp2_t in
    #import {sig #[ FP2_IS_SQUARE ] : fp2_is_square_inp → fp2_is_square_out } as  fp2_is_square ;;
    let fp2_is_square := fun x_0 => fp2_is_square (x_0) in
    #import {sig #[ FP2_SGN0 ] : fp2_sgn0_inp → fp2_sgn0_out } as  fp2_sgn0 ;;
    let fp2_sgn0 := fun x_0 => fp2_sgn0 (x_0) in
    #import {sig #[ FP2_SQRT ] : fp2_sqrt_inp → fp2_sqrt_out } as  fp2_sqrt ;;
    let fp2_sqrt := fun x_0 => fp2_sqrt (x_0) in
    #import {sig #[ FP2ADD ] : fp2add_inp → fp2add_out } as  fp2add ;;
    let fp2add := fun x_0 x_1 => fp2add (x_0,x_1) in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as  fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP2INV ] : fp2inv_inp → fp2inv_out } as  fp2inv ;;
    let fp2inv := fun x_0 => fp2inv (x_0) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as  fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    #import {sig #[ FP2NEG ] : fp2neg_inp → fp2neg_out } as  fp2neg ;;
    let fp2neg := fun x_0 => fp2neg (x_0) in
    #import {sig #[ FP2ZERO ] : fp2zero_inp → fp2zero_out } as  fp2zero ;;
    let fp2zero := fun  => fp2zero () in
    ({ code  '(z_2365 : (fp_t '× fp_t)) ←
        ( '(temp_2352 : fp_t) ←
            (nat_mod_two ) ;;
           '(temp_2354 : fp_t) ←
            (nat_mod_one ) ;;
           temp_2356 ←
            (fp2neg (prod_ce(temp_2352, temp_2354))) ;;
          ret (temp_2356)) ;;
       '(a_2388 : (fp_t '× fp_t)) ←
        ( '(temp_2358 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_2360 : fp_t) ←
            (nat_mod_from_literal (_) (@repr U128 240)) ;;
          ret (prod_ce(temp_2358, temp_2360))) ;;
       '(b_2385 : (fp_t '× fp_t)) ←
        ( '(temp_2362 : fp_t) ←
            (nat_mod_from_literal (_) (@repr U128 1012)) ;;
           '(temp_2364 : fp_t) ←
            (nat_mod_from_literal (_) (@repr U128 1012)) ;;
          ret (prod_ce(temp_2362, temp_2364))) ;;
       '(tv1_2397 : (fp_t '× fp_t)) ←
        ( temp_2367 ←
            (fp2mul (z_2365) (z_2365)) ;;
           temp_2370 ←
            (fp2mul (u_2368) (u_2368)) ;;
           temp_2372 ←
            (fp2mul (u_2368) (u_2368)) ;;
           temp_2374 ←
            (fp2mul (temp_2370) (temp_2372)) ;;
           temp_2376 ←
            (fp2mul (temp_2367) (temp_2374)) ;;
           temp_2378 ←
            (fp2mul (u_2368) (u_2368)) ;;
           temp_2380 ←
            (fp2mul (z_2365) (temp_2378)) ;;
           temp_2382 ←
            (fp2add (temp_2376) (temp_2380)) ;;
           temp_2384 ←
            (fp2inv (temp_2382)) ;;
          ret (temp_2384)) ;;
       '(x1_2412 : (fp_t '× fp_t)) ←
          ( temp_2387 ←
              (fp2neg (b_2385)) ;;
             temp_2390 ←
              (fp2inv (a_2388)) ;;
             temp_2392 ←
              (fp2mul (temp_2387) (temp_2390)) ;;
             '(temp_2394 : fp_t) ←
              (nat_mod_one ) ;;
             temp_2396 ←
              (fp2fromfp (temp_2394)) ;;
             temp_2399 ←
              (fp2add (temp_2396) (tv1_2397)) ;;
             temp_2401 ←
              (fp2mul (temp_2392) (temp_2399)) ;;
            ret (temp_2401)) ;;
        #put x1_2412_loc := x1_2412 ;;
       temp_2403 ←
        (fp2zero ) ;;
       '(temp_2405 : bool_ChoiceEquality) ←
        ((tv1_2397) =.? (temp_2403)) ;;
       '(x1_2412 : ((fp_t '× fp_t))) ←
        (if temp_2405:bool_ChoiceEquality
          then (({ code  '(x1_2412 : (fp_t '× fp_t)) ←
                  (( temp_2407 ←
                        (fp2mul (z_2365) (a_2388)) ;;
                       temp_2409 ←
                        (fp2inv (temp_2407)) ;;
                       temp_2411 ←
                        (fp2mul (b_2385) (temp_2409)) ;;
                      ret (temp_2411))) ;;
                #put x1_2412_loc := x1_2412 ;;
              
              @ret (((fp_t '× fp_t))) (x1_2412) } : code (CEfset (
                  [x1_2412_loc])) [interface
              #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] _))
          else @ret (((fp_t '× fp_t))) (x1_2412)) ;;
      
       '(gx1_2440 : (fp_t '× fp_t)) ←
        ( temp_2414 ←
            (fp2mul (x1_2412) (x1_2412)) ;;
           temp_2416 ←
            (fp2mul (temp_2414) (x1_2412)) ;;
           temp_2418 ←
            (fp2mul (a_2388) (x1_2412)) ;;
           temp_2420 ←
            (fp2add (temp_2416) (temp_2418)) ;;
           temp_2422 ←
            (fp2add (temp_2420) (b_2385)) ;;
          ret (temp_2422)) ;;
       '(x2_2429 : (fp_t '× fp_t)) ←
        ( temp_2424 ←
            (fp2mul (u_2368) (u_2368)) ;;
           temp_2426 ←
            (fp2mul (z_2365) (temp_2424)) ;;
           temp_2428 ←
            (fp2mul (temp_2426) (x1_2412)) ;;
          ret (temp_2428)) ;;
       '(gx2_2445 : (fp_t '× fp_t)) ←
        ( temp_2431 ←
            (fp2mul (x2_2429) (x2_2429)) ;;
           temp_2433 ←
            (fp2mul (temp_2431) (x2_2429)) ;;
           temp_2435 ←
            (fp2mul (a_2388) (x2_2429)) ;;
           temp_2437 ←
            (fp2add (temp_2433) (temp_2435)) ;;
           temp_2439 ←
            (fp2add (temp_2437) (b_2385)) ;;
          ret (temp_2439)) ;;
       temp_2459 ←
        ( '(temp_2442 : bool_ChoiceEquality) ←
            (fp2_is_square (gx1_2440)) ;;
           '(temp_2444 : fp2_t) ←
            (fp2_sqrt (gx1_2440)) ;;
           '(temp_2447 : fp2_t) ←
            (fp2_sqrt (gx2_2445)) ;;
          ret ((if (temp_2442):bool_ChoiceEquality then (prod_ce(
                  x1_2412,
                  temp_2444
                )) else (prod_ce(x2_2429, temp_2447))))) ;;
      let '(x_2457, y_2450) :=
        (temp_2459) : ((fp_t '× fp_t) '× fp2_t) in
       '(temp_2449 : bool_ChoiceEquality) ←
        (fp2_sgn0 (u_2368)) ;;
       '(temp_2452 : bool_ChoiceEquality) ←
        (fp2_sgn0 (y_2450)) ;;
       '(temp_2454 : bool_ChoiceEquality) ←
        ((temp_2449) !=.? (temp_2452)) ;;
       '(y_2450 : ((fp_t '× fp_t))) ←
        (if temp_2454:bool_ChoiceEquality
          then (({ code  '(y_2450 : (fp_t '× fp_t)) ←
                  (( temp_2456 ←
                        (fp2neg (y_2450)) ;;
                      ret (temp_2456))) ;;
                #put y_2450_loc := y_2450 ;;
              
              @ret (((fp_t '× fp_t))) (y_2450) } : code (CEfset (
                  [x1_2412_loc ; y_2450_loc])) [interface
              #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ] _))
          else @ret (((fp_t '× fp_t))) (y_2450)) ;;
      
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t))) (prod_ce(x_2457, y_2450
        )) } : code (CEfset ([x1_2412_loc ; y_2450_loc])) [interface
      #val #[ FP2_IS_SQUARE ] : fp2_is_square_inp → fp2_is_square_out ;
      #val #[ FP2_SGN0 ] : fp2_sgn0_inp → fp2_sgn0_out ;
      #val #[ FP2_SQRT ] : fp2_sqrt_inp → fp2_sqrt_out ;
      #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
      #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ;
      #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_g2_simple_swu_iso : package _ _ _ :=
  (seq_link g2_simple_swu_iso link_rest(
      package_fp2_is_square,package_fp2_sgn0,package_fp2_sqrt,package_fp2add,package_fp2fromfp,package_fp2inv,package_fp2mul,package_fp2neg,package_fp2zero)).
Fail Next Obligation.

Definition ynum_k_2581_loc : ChoiceEqualityLocation :=
  ((seq (fp_t '× fp_t) ; 2676%nat)).
Definition xx_2613_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 2677%nat)).
Definition inf_2665_loc : ChoiceEqualityLocation :=
  ((bool_ChoiceEquality ; 2678%nat)).
Definition xx_2632_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 2679%nat)).
Definition yden_k_2582_loc : ChoiceEqualityLocation :=
  ((seq (fp_t '× fp_t) ; 2680%nat)).
Definition ynum_2612_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 2681%nat)).
Definition xx_2592_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 2682%nat)).
Definition xnum_2568_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 2683%nat)).
Definition xnum_k_2565_loc : ChoiceEqualityLocation :=
  ((seq (fp_t '× fp_t) ; 2684%nat)).
Definition xden_2591_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 2685%nat)).
Definition yden_2631_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 2686%nat)).
Definition xx_2569_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 2687%nat)).
Definition xden_k_2580_loc : ChoiceEqualityLocation :=
  ((seq (fp_t '× fp_t) ; 2688%nat)).
Notation "'g2_isogeny_map_inp'" := (
  fp2_t '× fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_isogeny_map_out'" := (
  g2_t : choice_type) (in custom pack_type at level 2).
Definition G2_ISOGENY_MAP : nat :=
  (2689).
Program Definition g2_isogeny_map
   : package (CEfset (
      [xnum_k_2565_loc ; xden_k_2580_loc ; ynum_k_2581_loc ; yden_k_2582_loc ; xnum_2568_loc ; xx_2569_loc ; xden_2591_loc ; xx_2592_loc ; ynum_2612_loc ; xx_2613_loc ; yden_2631_loc ; xx_2632_loc ; inf_2665_loc])) [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ] [interface
  #val #[ G2_ISOGENY_MAP ] : g2_isogeny_map_inp → g2_isogeny_map_out ] :=
  (
    [package #def #[ G2_ISOGENY_MAP ] (temp_inp : g2_isogeny_map_inp) : g2_isogeny_map_out { 
    let '(x_2577 , y_2648) := temp_inp : fp2_t '× fp2_t in
    #import {sig #[ FP2ADD ] : fp2add_inp → fp2add_out } as  fp2add ;;
    let fp2add := fun x_0 x_1 => fp2add (x_0,x_1) in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as  fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP2INV ] : fp2inv_inp → fp2inv_out } as  fp2inv ;;
    let fp2inv := fun x_0 => fp2inv (x_0) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as  fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    #import {sig #[ FP2ZERO ] : fp2zero_inp → fp2zero_out } as  fp2zero ;;
    let fp2zero := fun  => fp2zero () in
    ({ code  '(xnum_k_2565 : seq (fp_t '× fp_t)) ←
          ( temp_2464 ←
              (seq_new_ (default : fp2_t) (usize 4)) ;;
            ret (temp_2464)) ;;
        #put xnum_k_2565_loc := xnum_k_2565 ;;
       '(xnum_k_2565 : seq (fp_t '× fp_t)) ←
        ( '(temp_2466 : seq int8) ←
            (array_to_be_bytes (g2_xnum_k_0_v)) ;;
           '(temp_2468 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_2466)) ;;
           '(temp_2470 : seq int8) ←
            (array_to_be_bytes (g2_xnum_k_0_v)) ;;
           '(temp_2472 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_2470)) ;;
          ret (seq_upd xnum_k_2565 (usize 0) (prod_ce(temp_2468, temp_2472
              )))) ;;
      
       '(xnum_k_2565 : seq (fp_t '× fp_t)) ←
        ( '(temp_2474 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_2476 : seq int8) ←
            (array_to_be_bytes (g2_xnum_k_1_i_v)) ;;
           '(temp_2478 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_2476)) ;;
          ret (seq_upd xnum_k_2565 (usize 1) (prod_ce(temp_2474, temp_2478
              )))) ;;
      
       '(xnum_k_2565 : seq (fp_t '× fp_t)) ←
        ( '(temp_2480 : seq int8) ←
            (array_to_be_bytes (g2_xnum_k_2_r_v)) ;;
           '(temp_2482 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_2480)) ;;
           '(temp_2484 : seq int8) ←
            (array_to_be_bytes (g2_xnum_k_2_i_v)) ;;
           '(temp_2486 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_2484)) ;;
          ret (seq_upd xnum_k_2565 (usize 2) (prod_ce(temp_2482, temp_2486
              )))) ;;
      
       '(xnum_k_2565 : seq (fp_t '× fp_t)) ←
        ( '(temp_2488 : seq int8) ←
            (array_to_be_bytes (g2_xnum_k_3_r_v)) ;;
           '(temp_2490 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_2488)) ;;
           '(temp_2492 : fp_t) ←
            (nat_mod_zero ) ;;
          ret (seq_upd xnum_k_2565 (usize 3) (prod_ce(temp_2490, temp_2492
              )))) ;;
      
       '(xden_k_2580 : seq (fp_t '× fp_t)) ←
          ( temp_2494 ←
              (seq_new_ (default : fp2_t) (usize 2)) ;;
            ret (temp_2494)) ;;
        #put xden_k_2580_loc := xden_k_2580 ;;
       '(xden_k_2580 : seq (fp_t '× fp_t)) ←
        ( '(temp_2496 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_2498 : seq int8) ←
            (array_to_be_bytes (g2_xden_k_0_i_v)) ;;
           '(temp_2500 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_2498)) ;;
          ret (seq_upd xden_k_2580 (usize 0) (prod_ce(temp_2496, temp_2500
              )))) ;;
      
       '(xden_k_2580 : seq (fp_t '× fp_t)) ←
        ( '(temp_2502 : fp_t) ←
            (nat_mod_from_literal (_) (@repr U128 12)) ;;
           '(temp_2504 : seq int8) ←
            (array_to_be_bytes (g2_xden_k_1_i_v)) ;;
           '(temp_2506 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_2504)) ;;
          ret (seq_upd xden_k_2580 (usize 1) (prod_ce(temp_2502, temp_2506
              )))) ;;
      
       '(ynum_k_2581 : seq (fp_t '× fp_t)) ←
          ( temp_2508 ←
              (seq_new_ (default : fp2_t) (usize 4)) ;;
            ret (temp_2508)) ;;
        #put ynum_k_2581_loc := ynum_k_2581 ;;
       '(ynum_k_2581 : seq (fp_t '× fp_t)) ←
        ( '(temp_2510 : seq int8) ←
            (array_to_be_bytes (g2_ynum_k_0_v)) ;;
           '(temp_2512 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_2510)) ;;
           '(temp_2514 : seq int8) ←
            (array_to_be_bytes (g2_ynum_k_0_v)) ;;
           '(temp_2516 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_2514)) ;;
          ret (seq_upd ynum_k_2581 (usize 0) (prod_ce(temp_2512, temp_2516
              )))) ;;
      
       '(ynum_k_2581 : seq (fp_t '× fp_t)) ←
        ( '(temp_2518 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_2520 : seq int8) ←
            (array_to_be_bytes (g2_ynum_k_1_i_v)) ;;
           '(temp_2522 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_2520)) ;;
          ret (seq_upd ynum_k_2581 (usize 1) (prod_ce(temp_2518, temp_2522
              )))) ;;
      
       '(ynum_k_2581 : seq (fp_t '× fp_t)) ←
        ( '(temp_2524 : seq int8) ←
            (array_to_be_bytes (g2_ynum_k_2_r_v)) ;;
           '(temp_2526 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_2524)) ;;
           '(temp_2528 : seq int8) ←
            (array_to_be_bytes (g2_ynum_k_2_i_v)) ;;
           '(temp_2530 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_2528)) ;;
          ret (seq_upd ynum_k_2581 (usize 2) (prod_ce(temp_2526, temp_2530
              )))) ;;
      
       '(ynum_k_2581 : seq (fp_t '× fp_t)) ←
        ( '(temp_2532 : seq int8) ←
            (array_to_be_bytes (g2_ynum_k_3_r_v)) ;;
           '(temp_2534 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_2532)) ;;
           '(temp_2536 : fp_t) ←
            (nat_mod_zero ) ;;
          ret (seq_upd ynum_k_2581 (usize 3) (prod_ce(temp_2534, temp_2536
              )))) ;;
      
       '(yden_k_2582 : seq (fp_t '× fp_t)) ←
          ( temp_2538 ←
              (seq_new_ (default : fp2_t) (usize 3)) ;;
            ret (temp_2538)) ;;
        #put yden_k_2582_loc := yden_k_2582 ;;
       '(yden_k_2582 : seq (fp_t '× fp_t)) ←
        ( '(temp_2540 : seq int8) ←
            (array_to_be_bytes (g2_yden_k_0_v)) ;;
           '(temp_2542 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_2540)) ;;
           '(temp_2544 : seq int8) ←
            (array_to_be_bytes (g2_yden_k_0_v)) ;;
           '(temp_2546 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_2544)) ;;
          ret (seq_upd yden_k_2582 (usize 0) (prod_ce(temp_2542, temp_2546
              )))) ;;
      
       '(yden_k_2582 : seq (fp_t '× fp_t)) ←
        ( '(temp_2548 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_2550 : seq int8) ←
            (array_to_be_bytes (g2_yden_k_1_i_v)) ;;
           '(temp_2552 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_2550)) ;;
          ret (seq_upd yden_k_2582 (usize 1) (prod_ce(temp_2548, temp_2552
              )))) ;;
      
       '(yden_k_2582 : seq (fp_t '× fp_t)) ←
        ( '(temp_2554 : fp_t) ←
            (nat_mod_from_literal (_) (@repr U128 18)) ;;
           '(temp_2556 : seq int8) ←
            (array_to_be_bytes (g2_yden_k_2_i_v)) ;;
           '(temp_2558 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_2556)) ;;
          ret (seq_upd yden_k_2582 (usize 2) (prod_ce(temp_2554, temp_2558
              )))) ;;
      
       '(xnum_2568 : (fp_t '× fp_t)) ←
          ( temp_2560 ←
              (fp2zero ) ;;
            ret (temp_2560)) ;;
        #put xnum_2568_loc := xnum_2568 ;;
       '(xx_2569 : (fp_t '× fp_t)) ←
          ( '(temp_2562 : fp_t) ←
              (nat_mod_one ) ;;
             temp_2564 ←
              (fp2fromfp (temp_2562)) ;;
            ret (temp_2564)) ;;
        #put xx_2569_loc := xx_2569 ;;
       '(temp_2567 : uint_size) ←
        (seq_len (xnum_k_2565)) ;;
       temp_2675 ←
        (foldi' (usize 0) (temp_2567) prod_ce(xnum_2568, xx_2569) (
              L2 := CEfset (
                [xnum_k_2565_loc ; xden_k_2580_loc ; ynum_k_2581_loc ; yden_k_2582_loc ; xnum_2568_loc ; xx_2569_loc ; xden_2591_loc ; xx_2592_loc ; ynum_2612_loc ; xx_2613_loc ; yden_2631_loc ; xx_2632_loc ; inf_2665_loc])) (
              I2 := [interface #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
              #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
              #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
              #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_2570 '(
              xnum_2568,
              xx_2569
            ) =>
            ({ code  '(xnum_2568 : (fp_t '× fp_t)) ←
                  (( '(temp_2572 : (fp_t '× fp_t)) ←
                        (seq_index (xnum_k_2565) (i_2570)) ;;
                       temp_2574 ←
                        (fp2mul (xx_2569) (temp_2572)) ;;
                       temp_2576 ←
                        (fp2add (xnum_2568) (temp_2574)) ;;
                      ret (temp_2576))) ;;
                #put xnum_2568_loc := xnum_2568 ;;
              
               '(xx_2569 : (fp_t '× fp_t)) ←
                  (( temp_2579 ←
                        (fp2mul (xx_2569) (x_2577)) ;;
                      ret (temp_2579))) ;;
                #put xx_2569_loc := xx_2569 ;;
              
              @ret (((fp_t '× fp_t) '× (fp_t '× fp_t))) (prod_ce(
                  xnum_2568,
                  xx_2569
                )) } : code (CEfset (
                  [xnum_k_2565_loc ; xden_k_2580_loc ; ynum_k_2581_loc ; yden_k_2582_loc ; xnum_2568_loc ; xx_2569_loc])) [interface
              #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] _))) ;;
      let '(xnum_2568, xx_2569) :=
        (temp_2675) : ((fp_t '× fp_t) '× (fp_t '× fp_t)) in
      
       '(xden_2591 : (fp_t '× fp_t)) ←
          ( temp_2584 ←
              (fp2zero ) ;;
            ret (temp_2584)) ;;
        #put xden_2591_loc := xden_2591 ;;
       '(xx_2592 : (fp_t '× fp_t)) ←
          ( '(temp_2586 : fp_t) ←
              (nat_mod_one ) ;;
             temp_2588 ←
              (fp2fromfp (temp_2586)) ;;
            ret (temp_2588)) ;;
        #put xx_2592_loc := xx_2592 ;;
       '(temp_2590 : uint_size) ←
        (seq_len (xden_k_2580)) ;;
       temp_2673 ←
        (foldi' (usize 0) (temp_2590) prod_ce(xden_2591, xx_2592) (
              L2 := CEfset (
                [xnum_k_2565_loc ; xden_k_2580_loc ; ynum_k_2581_loc ; yden_k_2582_loc ; xnum_2568_loc ; xx_2569_loc ; xden_2591_loc ; xx_2592_loc ; ynum_2612_loc ; xx_2613_loc ; yden_2631_loc ; xx_2632_loc ; inf_2665_loc])) (
              I2 := [interface #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
              #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
              #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
              #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_2593 '(
              xden_2591,
              xx_2592
            ) =>
            ({ code  '(xden_2591 : (fp_t '× fp_t)) ←
                  (( '(temp_2595 : (fp_t '× fp_t)) ←
                        (seq_index (xden_k_2580) (i_2593)) ;;
                       temp_2597 ←
                        (fp2mul (xx_2592) (temp_2595)) ;;
                       temp_2599 ←
                        (fp2add (xden_2591) (temp_2597)) ;;
                      ret (temp_2599))) ;;
                #put xden_2591_loc := xden_2591 ;;
              
               '(xx_2592 : (fp_t '× fp_t)) ←
                  (( temp_2601 ←
                        (fp2mul (xx_2592) (x_2577)) ;;
                      ret (temp_2601))) ;;
                #put xx_2592_loc := xx_2592 ;;
              
              @ret (((fp_t '× fp_t) '× (fp_t '× fp_t))) (prod_ce(
                  xden_2591,
                  xx_2592
                )) } : code (CEfset (
                  [xnum_k_2565_loc ; xden_k_2580_loc ; ynum_k_2581_loc ; yden_k_2582_loc ; xnum_2568_loc ; xx_2569_loc ; xden_2591_loc ; xx_2592_loc])) [interface
              #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] _))) ;;
      let '(xden_2591, xx_2592) :=
        (temp_2673) : ((fp_t '× fp_t) '× (fp_t '× fp_t)) in
      
       '(xden_2591 : (fp_t '× fp_t)) ←
          (( temp_2603 ←
                (fp2add (xden_2591) (xx_2592)) ;;
              ret (temp_2603))) ;;
        #put xden_2591_loc := xden_2591 ;;
      
       '(ynum_2612 : (fp_t '× fp_t)) ←
          ( temp_2605 ←
              (fp2zero ) ;;
            ret (temp_2605)) ;;
        #put ynum_2612_loc := ynum_2612 ;;
       '(xx_2613 : (fp_t '× fp_t)) ←
          ( '(temp_2607 : fp_t) ←
              (nat_mod_one ) ;;
             temp_2609 ←
              (fp2fromfp (temp_2607)) ;;
            ret (temp_2609)) ;;
        #put xx_2613_loc := xx_2613 ;;
       '(temp_2611 : uint_size) ←
        (seq_len (ynum_k_2581)) ;;
       temp_2671 ←
        (foldi' (usize 0) (temp_2611) prod_ce(ynum_2612, xx_2613) (
              L2 := CEfset (
                [xnum_k_2565_loc ; xden_k_2580_loc ; ynum_k_2581_loc ; yden_k_2582_loc ; xnum_2568_loc ; xx_2569_loc ; xden_2591_loc ; xx_2592_loc ; ynum_2612_loc ; xx_2613_loc ; yden_2631_loc ; xx_2632_loc ; inf_2665_loc])) (
              I2 := [interface #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
              #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
              #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
              #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_2614 '(
              ynum_2612,
              xx_2613
            ) =>
            ({ code  '(ynum_2612 : (fp_t '× fp_t)) ←
                  (( '(temp_2616 : (fp_t '× fp_t)) ←
                        (seq_index (ynum_k_2581) (i_2614)) ;;
                       temp_2618 ←
                        (fp2mul (xx_2613) (temp_2616)) ;;
                       temp_2620 ←
                        (fp2add (ynum_2612) (temp_2618)) ;;
                      ret (temp_2620))) ;;
                #put ynum_2612_loc := ynum_2612 ;;
              
               '(xx_2613 : (fp_t '× fp_t)) ←
                  (( temp_2622 ←
                        (fp2mul (xx_2613) (x_2577)) ;;
                      ret (temp_2622))) ;;
                #put xx_2613_loc := xx_2613 ;;
              
              @ret (((fp_t '× fp_t) '× (fp_t '× fp_t))) (prod_ce(
                  ynum_2612,
                  xx_2613
                )) } : code (CEfset (
                  [xnum_k_2565_loc ; xden_k_2580_loc ; ynum_k_2581_loc ; yden_k_2582_loc ; xnum_2568_loc ; xx_2569_loc ; xden_2591_loc ; xx_2592_loc ; ynum_2612_loc ; xx_2613_loc])) [interface
              #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] _))) ;;
      let '(ynum_2612, xx_2613) :=
        (temp_2671) : ((fp_t '× fp_t) '× (fp_t '× fp_t)) in
      
       '(yden_2631 : (fp_t '× fp_t)) ←
          ( temp_2624 ←
              (fp2zero ) ;;
            ret (temp_2624)) ;;
        #put yden_2631_loc := yden_2631 ;;
       '(xx_2632 : (fp_t '× fp_t)) ←
          ( '(temp_2626 : fp_t) ←
              (nat_mod_one ) ;;
             temp_2628 ←
              (fp2fromfp (temp_2626)) ;;
            ret (temp_2628)) ;;
        #put xx_2632_loc := xx_2632 ;;
       '(temp_2630 : uint_size) ←
        (seq_len (yden_k_2582)) ;;
       temp_2669 ←
        (foldi' (usize 0) (temp_2630) prod_ce(yden_2631, xx_2632) (
              L2 := CEfset (
                [xnum_k_2565_loc ; xden_k_2580_loc ; ynum_k_2581_loc ; yden_k_2582_loc ; xnum_2568_loc ; xx_2569_loc ; xden_2591_loc ; xx_2592_loc ; ynum_2612_loc ; xx_2613_loc ; yden_2631_loc ; xx_2632_loc ; inf_2665_loc])) (
              I2 := [interface #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
              #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
              #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
              #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_2633 '(
              yden_2631,
              xx_2632
            ) =>
            ({ code  '(yden_2631 : (fp_t '× fp_t)) ←
                  (( '(temp_2635 : (fp_t '× fp_t)) ←
                        (seq_index (yden_k_2582) (i_2633)) ;;
                       temp_2637 ←
                        (fp2mul (xx_2632) (temp_2635)) ;;
                       temp_2639 ←
                        (fp2add (yden_2631) (temp_2637)) ;;
                      ret (temp_2639))) ;;
                #put yden_2631_loc := yden_2631 ;;
              
               '(xx_2632 : (fp_t '× fp_t)) ←
                  (( temp_2641 ←
                        (fp2mul (xx_2632) (x_2577)) ;;
                      ret (temp_2641))) ;;
                #put xx_2632_loc := xx_2632 ;;
              
              @ret (((fp_t '× fp_t) '× (fp_t '× fp_t))) (prod_ce(
                  yden_2631,
                  xx_2632
                )) } : code (CEfset (
                  [xnum_k_2565_loc ; xden_k_2580_loc ; ynum_k_2581_loc ; yden_k_2582_loc ; xnum_2568_loc ; xx_2569_loc ; xden_2591_loc ; xx_2592_loc ; ynum_2612_loc ; xx_2613_loc ; yden_2631_loc ; xx_2632_loc])) [interface
              #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] _))) ;;
      let '(yden_2631, xx_2632) :=
        (temp_2669) : ((fp_t '× fp_t) '× (fp_t '× fp_t)) in
      
       '(yden_2631 : (fp_t '× fp_t)) ←
          (( temp_2643 ←
                (fp2add (yden_2631) (xx_2632)) ;;
              ret (temp_2643))) ;;
        #put yden_2631_loc := yden_2631 ;;
      
       '(xr_2666 : (fp_t '× fp_t)) ←
        ( temp_2645 ←
            (fp2inv (xden_2591)) ;;
           temp_2647 ←
            (fp2mul (xnum_2568) (temp_2645)) ;;
          ret (temp_2647)) ;;
       '(yr_2667 : (fp_t '× fp_t)) ←
        ( temp_2650 ←
            (fp2inv (yden_2631)) ;;
           temp_2652 ←
            (fp2mul (ynum_2612) (temp_2650)) ;;
           temp_2654 ←
            (fp2mul (y_2648) (temp_2652)) ;;
          ret (temp_2654)) ;;
       '(inf_2665 : bool_ChoiceEquality) ←
          (ret ((false : bool_ChoiceEquality))) ;;
        #put inf_2665_loc := inf_2665 ;;
       temp_2656 ←
        (fp2zero ) ;;
       '(temp_2658 : bool_ChoiceEquality) ←
        ((xden_2591) =.? (temp_2656)) ;;
       temp_2660 ←
        (fp2zero ) ;;
       '(temp_2662 : bool_ChoiceEquality) ←
        ((yden_2631) =.? (temp_2660)) ;;
       '(temp_2664 : bool_ChoiceEquality) ←
        ((temp_2658) || (temp_2662)) ;;
       '(inf_2665 : (bool_ChoiceEquality)) ←
        (if temp_2664:bool_ChoiceEquality
          then (({ code  '(inf_2665 : bool_ChoiceEquality) ←
                  ((ret ((true : bool_ChoiceEquality)))) ;;
                #put inf_2665_loc := inf_2665 ;;
              
              @ret ((bool_ChoiceEquality)) (inf_2665) } : code (CEfset (
                  [xnum_k_2565_loc ; xden_k_2580_loc ; ynum_k_2581_loc ; yden_k_2582_loc ; xnum_2568_loc ; xx_2569_loc ; xden_2591_loc ; xx_2592_loc ; ynum_2612_loc ; xx_2613_loc ; yden_2631_loc ; xx_2632_loc ; inf_2665_loc])) [interface
               ] _))
          else @ret ((bool_ChoiceEquality)) (inf_2665)) ;;
      
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality)) (
        prod_ce(xr_2666, yr_2667, inf_2665)) } : code (CEfset (
          [xnum_k_2565_loc ; xden_k_2580_loc ; ynum_k_2581_loc ; yden_k_2582_loc ; xnum_2568_loc ; xx_2569_loc ; xden_2591_loc ; xx_2592_loc ; ynum_2612_loc ; xx_2613_loc ; yden_2631_loc ; xx_2632_loc ; inf_2665_loc])) [interface
      #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
      #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_g2_isogeny_map : package _ _ _ :=
  (seq_link g2_isogeny_map link_rest(
      package_fp2add,package_fp2fromfp,package_fp2inv,package_fp2mul,package_fp2zero)).
Fail Next Obligation.


Notation "'g2_map_to_curve_sswu_inp'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_map_to_curve_sswu_out'" := (
  g2_t : choice_type) (in custom pack_type at level 2).
Definition G2_MAP_TO_CURVE_SSWU : nat :=
  (2700).
Program Definition g2_map_to_curve_sswu
   : package (CEfset ([])) [interface
  #val #[ G2_ISOGENY_MAP ] : g2_isogeny_map_inp → g2_isogeny_map_out ;
  #val #[ G2_SIMPLE_SWU_ISO ] : g2_simple_swu_iso_inp → g2_simple_swu_iso_out
  ] [interface
  #val #[ G2_MAP_TO_CURVE_SSWU ] : g2_map_to_curve_sswu_inp → g2_map_to_curve_sswu_out
  ] :=
  (
    [package #def #[ G2_MAP_TO_CURVE_SSWU ] (temp_inp : g2_map_to_curve_sswu_inp) : g2_map_to_curve_sswu_out { 
    let '(u_2690) := temp_inp : fp2_t in
    #import {sig #[ G2_ISOGENY_MAP ] : g2_isogeny_map_inp → g2_isogeny_map_out } as  g2_isogeny_map ;;
    let g2_isogeny_map := fun x_0 x_1 => g2_isogeny_map (x_0,x_1) in
    #import {sig #[ G2_SIMPLE_SWU_ISO ] : g2_simple_swu_iso_inp → g2_simple_swu_iso_out } as  g2_simple_swu_iso ;;
    let g2_simple_swu_iso := fun x_0 => g2_simple_swu_iso (x_0) in
    ({ code  temp_2699 ←
        ( '(temp_2692 : (fp2_t '× fp2_t)) ←
            (g2_simple_swu_iso (u_2690)) ;;
          ret (temp_2692)) ;;
      let '(xp_2693, yp_2694) :=
        (temp_2699) : (fp2_t '× fp2_t) in
       '(p_2697 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_2696 : g2_t) ←
            (g2_isogeny_map (xp_2693) (yp_2694)) ;;
          ret (temp_2696)) ;;
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality)) (
        p_2697) } : code (CEfset ([])) [interface
      #val #[ G2_ISOGENY_MAP ] : g2_isogeny_map_inp → g2_isogeny_map_out ;
      #val #[ G2_SIMPLE_SWU_ISO ] : g2_simple_swu_iso_inp → g2_simple_swu_iso_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_g2_map_to_curve_sswu : package _ _ _ :=
  (seq_link g2_map_to_curve_sswu link_rest(
      package_g2_isogeny_map,package_g2_simple_swu_iso)).
Fail Next Obligation.


Notation "'g2_hash_to_curve_sswu_inp'" := (
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g2_hash_to_curve_sswu_out'" := (
  g2_t : choice_type) (in custom pack_type at level 2).
Definition G2_HASH_TO_CURVE_SSWU : nat :=
  (2722).
Program Definition g2_hash_to_curve_sswu
   : package (CEfset ([])) [interface
  #val #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out ;
  #val #[ G2_CLEAR_COFACTOR ] : g2_clear_cofactor_inp → g2_clear_cofactor_out ;
  #val #[ G2_MAP_TO_CURVE_SSWU ] : g2_map_to_curve_sswu_inp → g2_map_to_curve_sswu_out ;
  #val #[ G2ADD ] : g2add_inp → g2add_out ] [interface
  #val #[ G2_HASH_TO_CURVE_SSWU ] : g2_hash_to_curve_sswu_inp → g2_hash_to_curve_sswu_out
  ] :=
  (
    [package #def #[ G2_HASH_TO_CURVE_SSWU ] (temp_inp : g2_hash_to_curve_sswu_inp) : g2_hash_to_curve_sswu_out { 
    let '(msg_2701 , dst_2702) := temp_inp : byte_seq '× byte_seq in
    #import {sig #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out } as  fp2_hash_to_field ;;
    let fp2_hash_to_field := fun x_0 x_1 x_2 => fp2_hash_to_field (
      x_0,x_1,x_2) in
    #import {sig #[ G2_CLEAR_COFACTOR ] : g2_clear_cofactor_inp → g2_clear_cofactor_out } as  g2_clear_cofactor ;;
    let g2_clear_cofactor := fun x_0 => g2_clear_cofactor (x_0) in
    #import {sig #[ G2_MAP_TO_CURVE_SSWU ] : g2_map_to_curve_sswu_inp → g2_map_to_curve_sswu_out } as  g2_map_to_curve_sswu ;;
    let g2_map_to_curve_sswu := fun x_0 => g2_map_to_curve_sswu (x_0) in
    #import {sig #[ G2ADD ] : g2add_inp → g2add_out } as  g2add ;;
    let g2add := fun x_0 x_1 => g2add (x_0,x_1) in
    ({ code  '(u_2706 : seq fp2_t) ←
        ( '(temp_2704 : seq fp2_t) ←
            (fp2_hash_to_field (msg_2701) (dst_2702) (usize 2)) ;;
          ret (temp_2704)) ;;
       '(q0_2714 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_2707 : fp2_t) ←
            (seq_index (u_2706) (usize 0)) ;;
           '(temp_2709 : g2_t) ←
            (g2_map_to_curve_sswu (temp_2707)) ;;
          ret (temp_2709)) ;;
       '(q1_2715 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_2711 : fp2_t) ←
            (seq_index (u_2706) (usize 1)) ;;
           '(temp_2713 : g2_t) ←
            (g2_map_to_curve_sswu (temp_2711)) ;;
          ret (temp_2713)) ;;
       '(r_2718 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( temp_2717 ←
            (g2add (q0_2714) (q1_2715)) ;;
          ret (temp_2717)) ;;
       '(p_2721 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_2720 : g2_t) ←
            (g2_clear_cofactor (r_2718)) ;;
          ret (temp_2720)) ;;
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality)) (
        p_2721) } : code (CEfset ([])) [interface
      #val #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out ;
      #val #[ G2_CLEAR_COFACTOR ] : g2_clear_cofactor_inp → g2_clear_cofactor_out ;
      #val #[ G2_MAP_TO_CURVE_SSWU ] : g2_map_to_curve_sswu_inp → g2_map_to_curve_sswu_out ;
      #val #[ G2ADD ] : g2add_inp → g2add_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_g2_hash_to_curve_sswu : package _ _ _ :=
  (seq_link g2_hash_to_curve_sswu link_rest(
      package_fp2_hash_to_field,package_g2_clear_cofactor,package_g2_map_to_curve_sswu,package_g2add)).
Fail Next Obligation.


Notation "'g2_encode_to_curve_sswu_inp'" := (
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g2_encode_to_curve_sswu_out'" := (
  g2_t : choice_type) (in custom pack_type at level 2).
Definition G2_ENCODE_TO_CURVE_SSWU : nat :=
  (2736).
Program Definition g2_encode_to_curve_sswu
   : package (CEfset ([])) [interface
  #val #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out ;
  #val #[ G2_CLEAR_COFACTOR ] : g2_clear_cofactor_inp → g2_clear_cofactor_out ;
  #val #[ G2_MAP_TO_CURVE_SSWU ] : g2_map_to_curve_sswu_inp → g2_map_to_curve_sswu_out
  ] [interface
  #val #[ G2_ENCODE_TO_CURVE_SSWU ] : g2_encode_to_curve_sswu_inp → g2_encode_to_curve_sswu_out
  ] :=
  (
    [package #def #[ G2_ENCODE_TO_CURVE_SSWU ] (temp_inp : g2_encode_to_curve_sswu_inp) : g2_encode_to_curve_sswu_out { 
    let '(msg_2723 , dst_2724) := temp_inp : byte_seq '× byte_seq in
    #import {sig #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out } as  fp2_hash_to_field ;;
    let fp2_hash_to_field := fun x_0 x_1 x_2 => fp2_hash_to_field (
      x_0,x_1,x_2) in
    #import {sig #[ G2_CLEAR_COFACTOR ] : g2_clear_cofactor_inp → g2_clear_cofactor_out } as  g2_clear_cofactor ;;
    let g2_clear_cofactor := fun x_0 => g2_clear_cofactor (x_0) in
    #import {sig #[ G2_MAP_TO_CURVE_SSWU ] : g2_map_to_curve_sswu_inp → g2_map_to_curve_sswu_out } as  g2_map_to_curve_sswu ;;
    let g2_map_to_curve_sswu := fun x_0 => g2_map_to_curve_sswu (x_0) in
    ({ code  '(u_2728 : seq fp2_t) ←
        ( '(temp_2726 : seq fp2_t) ←
            (fp2_hash_to_field (msg_2723) (dst_2724) (usize 1)) ;;
          ret (temp_2726)) ;;
       '(q_2732 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_2729 : fp2_t) ←
            (seq_index (u_2728) (usize 0)) ;;
           '(temp_2731 : g2_t) ←
            (g2_map_to_curve_sswu (temp_2729)) ;;
          ret (temp_2731)) ;;
       '(p_2735 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_2734 : g2_t) ←
            (g2_clear_cofactor (q_2732)) ;;
          ret (temp_2734)) ;;
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality)) (
        p_2735) } : code (CEfset ([])) [interface
      #val #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out ;
      #val #[ G2_CLEAR_COFACTOR ] : g2_clear_cofactor_inp → g2_clear_cofactor_out ;
      #val #[ G2_MAP_TO_CURVE_SSWU ] : g2_map_to_curve_sswu_inp → g2_map_to_curve_sswu_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_g2_encode_to_curve_sswu : package _ _ _ :=
  (seq_link g2_encode_to_curve_sswu link_rest(
      package_fp2_hash_to_field,package_g2_clear_cofactor,package_g2_map_to_curve_sswu)).
Fail Next Obligation.

