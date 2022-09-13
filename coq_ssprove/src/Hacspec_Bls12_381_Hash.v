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
Require Import Hacspec_Bls12_381.

Require Import Hacspec_Lib.

Require Import Hacspec_Sha256.

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
  (let temp_8744 : int64 :=
      (secret (@repr U64 936899308823769933)) in
    let temp_8746 : int64 :=
      (secret (@repr U64 2706051889235351147)) in
    let temp_8748 : int64 :=
      (secret (@repr U64 12843041017062132063)) in
    let temp_8750 : int64 :=
      (secret (@repr U64 12941209323636816658)) in
    let temp_8752 : int64 :=
      (secret (@repr U64 1105070755758604287)) in
    let temp_8754 : int64 :=
      (secret (@repr U64 15924587544893707605)) in
    let temp_8756 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_8744;
          temp_8746;
          temp_8748;
          temp_8750;
          temp_8752;
          temp_8754
        ]) in
    (temp_8756)).

Definition p_1_4_v : (arr_fp_t) :=
  (let temp_8758 : int64 :=
      (secret (@repr U64 468449654411884966)) in
    let temp_8760 : int64 :=
      (secret (@repr U64 10576397981472451381)) in
    let temp_8762 : int64 :=
      (secret (@repr U64 15644892545385841839)) in
    let temp_8764 : int64 :=
      (secret (@repr U64 15693976698673184137)) in
    let temp_8766 : int64 :=
      (secret (@repr U64 552535377879302143)) in
    let temp_8768 : int64 :=
      (secret (@repr U64 17185665809301629611)) in
    let temp_8770 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_8758;
          temp_8760;
          temp_8762;
          temp_8764;
          temp_8766;
          temp_8768
        ]) in
    (temp_8770)).

Definition p_3_4_v : (arr_fp_t) :=
  (let temp_8772 : int64 :=
      (secret (@repr U64 468449654411884966)) in
    let temp_8774 : int64 :=
      (secret (@repr U64 10576397981472451381)) in
    let temp_8776 : int64 :=
      (secret (@repr U64 15644892545385841839)) in
    let temp_8778 : int64 :=
      (secret (@repr U64 15693976698673184137)) in
    let temp_8780 : int64 :=
      (secret (@repr U64 552535377879302143)) in
    let temp_8782 : int64 :=
      (secret (@repr U64 17185665809301629610)) in
    let temp_8784 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_8772;
          temp_8774;
          temp_8776;
          temp_8778;
          temp_8780;
          temp_8782
        ]) in
    (temp_8784)).

Definition l_i_b_str_8813_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 8874%nat)).
Definition b_i_8843_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 8875%nat)).
Definition uniform_bytes_8867_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 8876%nat)).
Notation "'expand_message_xmd_inp'" := (
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'expand_message_xmd_out'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition EXPAND_MESSAGE_XMD : nat :=
  (8877).
Program Definition expand_message_xmd
   : package (CEfset (
      [l_i_b_str_8813_loc ; b_i_8843_loc ; uniform_bytes_8867_loc])) [interface
  #val #[ HASH ] : hash_inp → hash_out ] [interface
  #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
  ] :=
  (
    [package #def #[ EXPAND_MESSAGE_XMD ] (temp_inp : expand_message_xmd_inp) : expand_message_xmd_out { 
    let '(
      msg_8810 , dst_8792 , len_in_bytes_8785) := temp_inp : byte_seq '× byte_seq '× uint_size in
    #import {sig #[ HASH ] : hash_inp → hash_out } as hash ;;
    let hash := fun x_0 => hash (x_0) in
    ({ code  '(ell_8846 : uint_size) ←
        ( '(temp_8787 : uint_size) ←
            ((len_in_bytes_8785) .+ (b_in_bytes_v)) ;;
           '(temp_8789 : uint_size) ←
            ((temp_8787) .- (usize 1)) ;;
           '(temp_8791 : uint_size) ←
            ((temp_8789) ./ (b_in_bytes_v)) ;;
          ret (temp_8791)) ;;
       '(dst_prime_8820 : seq uint8) ←
        ( '(temp_8794 : uint_size) ←
            (seq_len (dst_8792)) ;;
           temp_8796 ←
            (uint8_from_usize (temp_8794)) ;;
           '(temp_8798 : byte_seq) ←
            (seq_push (dst_8792) (temp_8796)) ;;
          ret (temp_8798)) ;;
       '(z_pad_8809 : seq uint8) ←
        ( temp_8800 ←
            (seq_new_ (default : uint8) (s_in_bytes_v)) ;;
          ret (temp_8800)) ;;
       '(l_i_b_str_8813 : seq uint8) ←
          ( temp_8802 ←
              (seq_new_ (default : uint8) (usize 2)) ;;
            ret (temp_8802)) ;;
        #put l_i_b_str_8813_loc := l_i_b_str_8813 ;;
       '(l_i_b_str_8813 : seq uint8) ←
        ( '(temp_8804 : uint_size) ←
            ((len_in_bytes_8785) ./ (usize 256)) ;;
           temp_8806 ←
            (uint8_from_usize (temp_8804)) ;;
          ret (seq_upd l_i_b_str_8813 (usize 0) (temp_8806))) ;;
      
       '(l_i_b_str_8813 : seq uint8) ←
        ( temp_8808 ←
            (uint8_from_usize (len_in_bytes_8785)) ;;
          ret (seq_upd l_i_b_str_8813 (usize 1) (temp_8808))) ;;
      
       '(msg_prime_8823 : seq uint8) ←
        ( '(temp_8812 : seq uint8) ←
            (seq_concat (z_pad_8809) (msg_8810)) ;;
           '(temp_8815 : seq uint8) ←
            (seq_concat (temp_8812) (l_i_b_str_8813)) ;;
           temp_8817 ←
            (seq_new_ (default : uint8) (usize 1)) ;;
           '(temp_8819 : seq uint8) ←
            (seq_concat (temp_8815) (temp_8817)) ;;
           '(temp_8822 : seq uint8) ←
            (seq_concat (temp_8819) (dst_prime_8820)) ;;
          ret (temp_8822)) ;;
       '(b_0_8830 : seq uint8) ←
        ( temp_8825 ←
            (hash (msg_prime_8823)) ;;
           '(temp_8827 : seq uint8) ←
            (array_to_seq (temp_8825)) ;;
           '(temp_8829 : byte_seq) ←
            (seq_from_seq (temp_8827)) ;;
          ret (temp_8829)) ;;
       '(b_i_8843 : seq uint8) ←
          ( '(temp_8832 : int8) ←
              (secret (@repr U8 1)) ;;
             '(temp_8834 : seq uint8) ←
              (seq_push (b_0_8830) (temp_8832)) ;;
             '(temp_8836 : seq uint8) ←
              (seq_concat (temp_8834) (dst_prime_8820)) ;;
             temp_8838 ←
              (hash (temp_8836)) ;;
             '(temp_8840 : seq uint8) ←
              (array_to_seq (temp_8838)) ;;
             '(temp_8842 : byte_seq) ←
              (seq_from_seq (temp_8840)) ;;
            ret (temp_8842)) ;;
        #put b_i_8843_loc := b_i_8843 ;;
       '(uniform_bytes_8867 : seq uint8) ←
          ( '(temp_8845 : byte_seq) ←
              (seq_from_seq (b_i_8843)) ;;
            ret (temp_8845)) ;;
        #put uniform_bytes_8867_loc := uniform_bytes_8867 ;;
       '(temp_8848 : uint_size) ←
        ((ell_8846) .+ (usize 1)) ;;
       temp_8873 ←
        (foldi' (usize 2) (temp_8848) prod_ce(b_i_8843, uniform_bytes_8867) (
              L2 := CEfset (
                [l_i_b_str_8813_loc ; b_i_8843_loc ; uniform_bytes_8867_loc])) (
              I2 := [interface #val #[ HASH ] : hash_inp → hash_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_8854 '(
              b_i_8843,
              uniform_bytes_8867
            ) =>
            ({ code  '(t_8851 : seq uint8) ←
                ( '(temp_8850 : byte_seq) ←
                    (seq_from_seq (b_0_8830)) ;;
                  ret (temp_8850)) ;;
               '(b_i_8843 : seq uint8) ←
                  (( temp_8853 ←
                        ((t_8851) seq_xor (b_i_8843)) ;;
                       temp_8856 ←
                        (uint8_from_usize (i_8854)) ;;
                       '(temp_8858 : seq uint8) ←
                        (seq_push (temp_8853) (temp_8856)) ;;
                       '(temp_8860 : seq uint8) ←
                        (seq_concat (temp_8858) (dst_prime_8820)) ;;
                       temp_8862 ←
                        (hash (temp_8860)) ;;
                       '(temp_8864 : seq uint8) ←
                        (array_to_seq (temp_8862)) ;;
                       '(temp_8866 : byte_seq) ←
                        (seq_from_seq (temp_8864)) ;;
                      ret (temp_8866))) ;;
                #put b_i_8843_loc := b_i_8843 ;;
              
               '(uniform_bytes_8867 : seq uint8) ←
                  (( '(temp_8869 : seq uint8) ←
                        (seq_concat (uniform_bytes_8867) (b_i_8843)) ;;
                      ret (temp_8869))) ;;
                #put uniform_bytes_8867_loc := uniform_bytes_8867 ;;
              
              @ret ((seq uint8 '× seq uint8)) (prod_ce(
                  b_i_8843,
                  uniform_bytes_8867
                )) } : code (CEfset (
                  [l_i_b_str_8813_loc ; b_i_8843_loc ; uniform_bytes_8867_loc])) [interface
              #val #[ HASH ] : hash_inp → hash_out ] _))) ;;
      let '(b_i_8843, uniform_bytes_8867) :=
        (temp_8873) : (seq uint8 '× seq uint8) in
      
       temp_8871 ←
        (seq_truncate (uniform_bytes_8867) (len_in_bytes_8785)) ;;
      @ret (seq uint8) (temp_8871) } : code (CEfset (
          [l_i_b_str_8813_loc ; b_i_8843_loc ; uniform_bytes_8867_loc])) [interface
      #val #[ HASH ] : hash_inp → hash_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_expand_message_xmd : package _ _ _ :=
  (seq_link expand_message_xmd link_rest(package_hash)).
Fail Next Obligation.

Definition output_8905_loc : ChoiceEqualityLocation :=
  ((seq fp_t ; 8906%nat)).
Notation "'fp_hash_to_field_inp'" := (
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'fp_hash_to_field_out'" := (
  seq fp_t : choice_type) (in custom pack_type at level 2).
Definition FP_HASH_TO_FIELD : nat :=
  (8907).
Program Definition fp_hash_to_field
   : package (CEfset ([output_8905_loc])) [interface
  #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
  ] [interface
  #val #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out
  ] :=
  (
    [package #def #[ FP_HASH_TO_FIELD ] (temp_inp : fp_hash_to_field_inp) : fp_hash_to_field_out { 
    let '(
      msg_8881 , dst_8882 , count_8878) := temp_inp : byte_seq '× byte_seq '× uint_size in
    #import {sig #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out } as expand_message_xmd ;;
    let expand_message_xmd := fun x_0 x_1 x_2 => expand_message_xmd (
      x_0,x_1,x_2) in
    ({ code  '(len_in_bytes_8883 : uint_size) ←
        ( '(temp_8880 : uint_size) ←
            ((count_8878) .* (l_v)) ;;
          ret (temp_8880)) ;;
       '(uniform_bytes_8891 : seq uint8) ←
        ( '(temp_8885 : byte_seq) ←
            (expand_message_xmd (msg_8881) (dst_8882) (len_in_bytes_8883)) ;;
          ret (temp_8885)) ;;
       '(output_8905 : seq fp_t) ←
          ( temp_8887 ←
              (seq_new_ (default : fp_t) (count_8878)) ;;
            ret (temp_8887)) ;;
        #put output_8905_loc := output_8905 ;;
       '(output_8905 : (seq fp_t)) ←
        (foldi' (usize 0) (count_8878) output_8905 (L2 := CEfset (
                [output_8905_loc])) (I2 := [interface
              #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_8888 output_8905 =>
            ({ code  '(elm_offset_8892 : uint_size) ←
                ( '(temp_8890 : uint_size) ←
                    ((l_v) .* (i_8888)) ;;
                  ret (temp_8890)) ;;
               '(tv_8895 : seq uint8) ←
                ( '(temp_8894 : seq uint8) ←
                    (seq_slice (uniform_bytes_8891) (elm_offset_8892) (l_v)) ;;
                  ret (temp_8894)) ;;
               '(u_i_8904 : fp_t) ←
                ( '(temp_8897 : fp_hash_t) ←
                    (nat_mod_from_byte_seq_be (tv_8895)) ;;
                   temp_8899 ←
                    (nat_mod_to_byte_seq_be (temp_8897)) ;;
                   '(temp_8901 : seq uint8) ←
                    (seq_slice (temp_8899) (usize 16) (usize 48)) ;;
                   '(temp_8903 : fp_t) ←
                    (nat_mod_from_byte_seq_be (temp_8901)) ;;
                  ret (temp_8903)) ;;
               '(output_8905 : seq fp_t) ←
                (ret (seq_upd output_8905 (i_8888) (u_i_8904))) ;;
              
              @ret ((seq fp_t)) (output_8905) } : code (CEfset (
                  [output_8905_loc])) [interface] _))) ;;
      
      @ret (seq fp_t) (output_8905) } : code (CEfset (
          [output_8905_loc])) [interface
      #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp_hash_to_field : package _ _ _ :=
  (seq_link fp_hash_to_field link_rest(package_expand_message_xmd)).
Fail Next Obligation.


Notation "'fp_sgn0_inp'" := (
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_sgn0_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition FP_SGN0 : nat :=
  (8917).
Program Definition fp_sgn0
   : package (fset.fset0) [interface] [interface
  #val #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out ] :=
  ([package #def #[ FP_SGN0 ] (temp_inp : fp_sgn0_inp) : fp_sgn0_out { 
    let '(x_8908) := temp_inp : fp_t in
    ({ code  '(temp_8910 : fp_t) ←
        (nat_mod_two ) ;;
       '(temp_8912 : fp_t) ←
        ((x_8908) rem (temp_8910)) ;;
       '(temp_8914 : fp_t) ←
        (nat_mod_one ) ;;
       '(temp_8916 : bool_ChoiceEquality) ←
        ((temp_8912) =.? (temp_8914)) ;;
      @ret (bool_ChoiceEquality) (temp_8916) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_fp_sgn0 : package _ _ _ :=
  (fp_sgn0).
Fail Next Obligation.


Notation "'fp_is_square_inp'" := (
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_is_square_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition FP_IS_SQUARE : nat :=
  (8937).
Program Definition fp_is_square
   : package (fset.fset0) [interface] [interface
  #val #[ FP_IS_SQUARE ] : fp_is_square_inp → fp_is_square_out ] :=
  (
    [package #def #[ FP_IS_SQUARE ] (temp_inp : fp_is_square_inp) : fp_is_square_out { 
    let '(x_8922) := temp_inp : fp_t in
    ({ code  '(c1_8923 : fp_t) ←
        ( '(temp_8919 : seq int8) ←
            (array_to_be_bytes (p_1_2_v)) ;;
           '(temp_8921 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_8919)) ;;
          ret (temp_8921)) ;;
       '(tv_8926 : fp_t) ←
        ( temp_8925 ←
            (nat_mod_pow_self (x_8922) (c1_8923)) ;;
          ret (temp_8925)) ;;
       '(temp_8928 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_8930 : bool_ChoiceEquality) ←
        ((tv_8926) =.? (temp_8928)) ;;
       '(temp_8932 : fp_t) ←
        (nat_mod_one ) ;;
       '(temp_8934 : bool_ChoiceEquality) ←
        ((tv_8926) =.? (temp_8932)) ;;
       '(temp_8936 : bool_ChoiceEquality) ←
        ((temp_8930) || (temp_8934)) ;;
      @ret (bool_ChoiceEquality) (temp_8936) } : code (
        fset.fset0) [interface] _)
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
  (8946).
Program Definition fp_sqrt
   : package (fset.fset0) [interface] [interface
  #val #[ FP_SQRT ] : fp_sqrt_inp → fp_sqrt_out ] :=
  ([package #def #[ FP_SQRT ] (temp_inp : fp_sqrt_inp) : fp_sqrt_out { 
    let '(x_8942) := temp_inp : fp_t in
    ({ code  '(c1_8943 : fp_t) ←
        ( '(temp_8939 : seq int8) ←
            (array_to_be_bytes (p_1_4_v)) ;;
           '(temp_8941 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_8939)) ;;
          ret (temp_8941)) ;;
       temp_8945 ←
        (nat_mod_pow_self (x_8942) (c1_8943)) ;;
      @ret (fp_t) (temp_8945) } : code (fset.fset0) [interface] _)
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
  (8956).
Program Definition g1_curve_func
   : package (fset.fset0) [interface] [interface
  #val #[ G1_CURVE_FUNC ] : g1_curve_func_inp → g1_curve_func_out ] :=
  (
    [package #def #[ G1_CURVE_FUNC ] (temp_inp : g1_curve_func_inp) : g1_curve_func_out { 
    let '(x_8947) := temp_inp : fp_t in
    ({ code  '(temp_8949 : fp_t) ←
        ((x_8947) *% (x_8947)) ;;
       '(temp_8951 : fp_t) ←
        ((temp_8949) *% (x_8947)) ;;
       '(temp_8953 : fp_t) ←
        (nat_mod_from_literal (_) (@repr U128 4)) ;;
       '(temp_8955 : fp_t) ←
        ((temp_8951) +% (temp_8953)) ;;
      @ret (fp_t) (temp_8955) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_g1_curve_func : package _ _ _ :=
  (g1_curve_func).
Fail Next Obligation.

Definition y_9091_loc : ChoiceEqualityLocation :=
  ((fp_t ; 9100%nat)).
Definition tv4_9001_loc : ChoiceEqualityLocation :=
  ((fp_t ; 9101%nat)).
Notation "'g1_map_to_curve_svdw_inp'" := (
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_map_to_curve_svdw_out'" := (
  g1_t : choice_type) (in custom pack_type at level 2).
Definition G1_MAP_TO_CURVE_SVDW : nat :=
  (9102).
Program Definition g1_map_to_curve_svdw
   : package (CEfset ([tv4_9001_loc ; y_9091_loc])) [interface
  #val #[ FP_IS_SQUARE ] : fp_is_square_inp → fp_is_square_out ;
  #val #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out ;
  #val #[ FP_SQRT ] : fp_sqrt_inp → fp_sqrt_out ;
  #val #[ G1_CURVE_FUNC ] : g1_curve_func_inp → g1_curve_func_out ] [interface
  #val #[ G1_MAP_TO_CURVE_SVDW ] : g1_map_to_curve_svdw_inp → g1_map_to_curve_svdw_out
  ] :=
  (
    [package #def #[ G1_MAP_TO_CURVE_SVDW ] (temp_inp : g1_map_to_curve_svdw_inp) : g1_map_to_curve_svdw_out { 
    let '(u_8966) := temp_inp : fp_t in
    #import {sig #[ FP_IS_SQUARE ] : fp_is_square_inp → fp_is_square_out } as fp_is_square ;;
    let fp_is_square := fun x_0 => fp_is_square (x_0) in
    #import {sig #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out } as fp_sgn0 ;;
    let fp_sgn0 := fun x_0 => fp_sgn0 (x_0) in
    #import {sig #[ FP_SQRT ] : fp_sqrt_inp → fp_sqrt_out } as fp_sqrt ;;
    let fp_sqrt := fun x_0 => fp_sqrt (x_0) in
    #import {sig #[ G1_CURVE_FUNC ] : g1_curve_func_inp → g1_curve_func_out } as g1_curve_func ;;
    let g1_curve_func := fun x_0 => g1_curve_func (x_0) in
    ({ code  '(z_8963 : fp_t) ←
        ( '(temp_8958 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_8960 : fp_t) ←
            (nat_mod_from_literal (_) (@repr U128 3)) ;;
           '(temp_8962 : fp_t) ←
            ((temp_8958) -% (temp_8960)) ;;
          ret (temp_8962)) ;;
       '(gz_8969 : fp_t) ←
        ( '(temp_8965 : fp_t) ←
            (g1_curve_func (z_8963)) ;;
          ret (temp_8965)) ;;
       '(tv1_8974 : fp_t) ←
        ( '(temp_8968 : fp_t) ←
            ((u_8966) *% (u_8966)) ;;
           '(temp_8971 : fp_t) ←
            ((temp_8968) *% (gz_8969)) ;;
          ret (temp_8971)) ;;
       '(tv2_8982 : fp_t) ←
        ( '(temp_8973 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_8976 : fp_t) ←
            ((temp_8973) +% (tv1_8974)) ;;
          ret (temp_8976)) ;;
       '(tv1_8981 : fp_t) ←
        ( '(temp_8978 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_8980 : fp_t) ←
            ((temp_8978) -% (tv1_8974)) ;;
          ret (temp_8980)) ;;
       '(tv3_9010 : fp_t) ←
        ( '(temp_8984 : fp_t) ←
            ((tv1_8981) *% (tv2_8982)) ;;
           temp_8986 ←
            (nat_mod_inv (temp_8984)) ;;
          ret (temp_8986)) ;;
       '(tv4_9001 : fp_t) ←
          ( '(temp_8988 : fp_t) ←
              (nat_mod_zero ) ;;
             '(temp_8990 : fp_t) ←
              ((temp_8988) -% (gz_8969)) ;;
             '(temp_8992 : fp_t) ←
              (nat_mod_from_literal (_) (@repr U128 3)) ;;
             '(temp_8994 : fp_t) ←
              ((temp_8992) *% (z_8963)) ;;
             '(temp_8996 : fp_t) ←
              ((temp_8994) *% (z_8963)) ;;
             '(temp_8998 : fp_t) ←
              ((temp_8990) *% (temp_8996)) ;;
             '(temp_9000 : fp_t) ←
              (fp_sqrt (temp_8998)) ;;
            ret (temp_9000)) ;;
        #put tv4_9001_loc := tv4_9001 ;;
       '(temp_9003 : bool_ChoiceEquality) ←
        (fp_sgn0 (tv4_9001)) ;;
       '(tv4_9001 : (fp_t)) ←
        (if temp_9003:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(tv4_9001 : fp_t) ←
                (( '(temp_9005 : fp_t) ←
                      (nat_mod_zero ) ;;
                     '(temp_9007 : fp_t) ←
                      ((temp_9005) -% (tv4_9001)) ;;
                    ret (temp_9007))) ;;
              #put tv4_9001_loc := tv4_9001 ;;
            
            @ret ((fp_t)) (tv4_9001) in
            ({ code temp_then } : code (CEfset ([tv4_9001_loc])) [interface] _))
          else @ret ((fp_t)) (tv4_9001)) ;;
      
       '(tv5_9043 : fp_t) ←
        ( '(temp_9009 : fp_t) ←
            ((u_8966) *% (tv1_8981)) ;;
           '(temp_9012 : fp_t) ←
            ((temp_9009) *% (tv3_9010)) ;;
           '(temp_9014 : fp_t) ←
            ((temp_9012) *% (tv4_9001)) ;;
          ret (temp_9014)) ;;
       '(tv6_9058 : fp_t) ←
        ( '(temp_9016 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_9018 : fp_t) ←
            (nat_mod_from_literal (_) (@repr U128 4)) ;;
           '(temp_9020 : fp_t) ←
            ((temp_9016) -% (temp_9018)) ;;
           '(temp_9022 : fp_t) ←
            ((temp_9020) *% (gz_8969)) ;;
           '(temp_9024 : fp_t) ←
            (nat_mod_from_literal (_) (@repr U128 3)) ;;
           '(temp_9026 : fp_t) ←
            ((temp_9024) *% (z_8963)) ;;
           '(temp_9028 : fp_t) ←
            ((temp_9026) *% (z_8963)) ;;
           temp_9030 ←
            (nat_mod_inv (temp_9028)) ;;
           '(temp_9032 : fp_t) ←
            ((temp_9022) *% (temp_9030)) ;;
          ret (temp_9032)) ;;
       '(x1_9073 : fp_t) ←
        ( '(temp_9034 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_9036 : fp_t) ←
            ((temp_9034) -% (z_8963)) ;;
           '(temp_9038 : fp_t) ←
            (nat_mod_two ) ;;
           temp_9040 ←
            (nat_mod_inv (temp_9038)) ;;
           '(temp_9042 : fp_t) ←
            ((temp_9036) *% (temp_9040)) ;;
           '(temp_9045 : fp_t) ←
            ((temp_9042) -% (tv5_9043)) ;;
          ret (temp_9045)) ;;
       '(x2_9078 : fp_t) ←
        ( '(temp_9047 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_9049 : fp_t) ←
            ((temp_9047) -% (z_8963)) ;;
           '(temp_9051 : fp_t) ←
            (nat_mod_two ) ;;
           temp_9053 ←
            (nat_mod_inv (temp_9051)) ;;
           '(temp_9055 : fp_t) ←
            ((temp_9049) *% (temp_9053)) ;;
           '(temp_9057 : fp_t) ←
            ((temp_9055) +% (tv5_9043)) ;;
          ret (temp_9057)) ;;
       '(x3_9083 : fp_t) ←
        ( '(temp_9060 : fp_t) ←
            ((tv2_8982) *% (tv2_8982)) ;;
           '(temp_9062 : fp_t) ←
            ((temp_9060) *% (tv3_9010)) ;;
           '(temp_9064 : fp_t) ←
            ((tv6_9058) *% (temp_9062)) ;;
           '(temp_9066 : fp_t) ←
            ((tv2_8982) *% (tv2_8982)) ;;
           '(temp_9068 : fp_t) ←
            ((temp_9066) *% (tv3_9010)) ;;
           '(temp_9070 : fp_t) ←
            ((temp_9064) *% (temp_9068)) ;;
           '(temp_9072 : fp_t) ←
            ((z_8963) +% (temp_9070)) ;;
          ret (temp_9072)) ;;
       '(x_9084 : fp_t) ←
        ( '(temp_9075 : fp_t) ←
            (g1_curve_func (x1_9073)) ;;
           '(temp_9077 : bool_ChoiceEquality) ←
            (fp_is_square (temp_9075)) ;;
           '(temp_9080 : fp_t) ←
            (g1_curve_func (x2_9078)) ;;
           '(temp_9082 : bool_ChoiceEquality) ←
            (fp_is_square (temp_9080)) ;;
          ret ((if (temp_9077):bool_ChoiceEquality then (*inline*) (
                x1_9073) else ((if (
                    temp_9082):bool_ChoiceEquality then (*inline*) (
                    x2_9078) else (x3_9083)))))) ;;
       '(y_9091 : fp_t) ←
          ( '(temp_9086 : fp_t) ←
              (g1_curve_func (x_9084)) ;;
             '(temp_9088 : fp_t) ←
              (fp_sqrt (temp_9086)) ;;
            ret (temp_9088)) ;;
        #put y_9091_loc := y_9091 ;;
       '(temp_9090 : bool_ChoiceEquality) ←
        (fp_sgn0 (u_8966)) ;;
       '(temp_9093 : bool_ChoiceEquality) ←
        (fp_sgn0 (y_9091)) ;;
       '(temp_9095 : bool_ChoiceEquality) ←
        ((temp_9090) !=.? (temp_9093)) ;;
       '(y_9091 : (fp_t)) ←
        (if temp_9095:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(y_9091 : fp_t) ←
                (( '(temp_9097 : fp_t) ←
                      (nat_mod_zero ) ;;
                     '(temp_9099 : fp_t) ←
                      ((temp_9097) -% (y_9091)) ;;
                    ret (temp_9099))) ;;
              #put y_9091_loc := y_9091 ;;
            
            @ret ((fp_t)) (y_9091) in
            ({ code temp_then } : code (CEfset (
                  [tv4_9001_loc ; y_9091_loc])) [interface] _))
          else @ret ((fp_t)) (y_9091)) ;;
      
      @ret ((fp_t '× fp_t '× bool_ChoiceEquality)) (prod_ce(
          x_9084,
          y_9091,
          (false : bool_ChoiceEquality)
        )) } : code (CEfset ([tv4_9001_loc ; y_9091_loc])) [interface
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
  (9109).
Program Definition g1_clear_cofactor
   : package (fset.fset0) [interface #val #[ G1MUL ] : g1mul_inp → g1mul_out
  ] [interface
  #val #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out
  ] :=
  (
    [package #def #[ G1_CLEAR_COFACTOR ] (temp_inp : g1_clear_cofactor_inp) : g1_clear_cofactor_out { 
    let '(x_9106) := temp_inp : g1_t in
    #import {sig #[ G1MUL ] : g1mul_inp → g1mul_out } as g1mul ;;
    let g1mul := fun x_0 x_1 => g1mul (x_0,x_1) in
    ({ code  '(h_eff_9105 : scalar_t) ←
        ( '(temp_9104 : scalar_t) ←
            (nat_mod_from_literal (_) (@repr U128 15132376222941642753)) ;;
          ret (temp_9104)) ;;
       temp_9108 ←
        (g1mul (h_eff_9105) (x_9106)) ;;
      @ret ((fp_t '× fp_t '× bool_ChoiceEquality)) (temp_9108) } : code (
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
  (9131).
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
    let '(msg_9110 , dst_9111) := temp_inp : byte_seq '× byte_seq in
    #import {sig #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out } as fp_hash_to_field ;;
    let fp_hash_to_field := fun x_0 x_1 x_2 => fp_hash_to_field (x_0,x_1,x_2) in
    #import {sig #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out } as g1_clear_cofactor ;;
    let g1_clear_cofactor := fun x_0 => g1_clear_cofactor (x_0) in
    #import {sig #[ G1_MAP_TO_CURVE_SVDW ] : g1_map_to_curve_svdw_inp → g1_map_to_curve_svdw_out } as g1_map_to_curve_svdw ;;
    let g1_map_to_curve_svdw := fun x_0 => g1_map_to_curve_svdw (x_0) in
    #import {sig #[ G1ADD ] : g1add_inp → g1add_out } as g1add ;;
    let g1add := fun x_0 x_1 => g1add (x_0,x_1) in
    ({ code  '(u_9115 : seq fp_t) ←
        ( '(temp_9113 : seq fp_t) ←
            (fp_hash_to_field (msg_9110) (dst_9111) (usize 2)) ;;
          ret (temp_9113)) ;;
       '(q0_9123 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( '(temp_9116 : fp_t) ←
            (seq_index (u_9115) (usize 0)) ;;
           '(temp_9118 : g1_t) ←
            (g1_map_to_curve_svdw (temp_9116)) ;;
          ret (temp_9118)) ;;
       '(q1_9124 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( '(temp_9120 : fp_t) ←
            (seq_index (u_9115) (usize 1)) ;;
           '(temp_9122 : g1_t) ←
            (g1_map_to_curve_svdw (temp_9120)) ;;
          ret (temp_9122)) ;;
       '(r_9127 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( temp_9126 ←
            (g1add (q0_9123) (q1_9124)) ;;
          ret (temp_9126)) ;;
       '(p_9130 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( '(temp_9129 : g1_t) ←
            (g1_clear_cofactor (r_9127)) ;;
          ret (temp_9129)) ;;
      @ret ((fp_t '× fp_t '× bool_ChoiceEquality)) (p_9130) } : code (CEfset (
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
  (9145).
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
    let '(msg_9132 , dst_9133) := temp_inp : byte_seq '× byte_seq in
    #import {sig #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out } as fp_hash_to_field ;;
    let fp_hash_to_field := fun x_0 x_1 x_2 => fp_hash_to_field (x_0,x_1,x_2) in
    #import {sig #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out } as g1_clear_cofactor ;;
    let g1_clear_cofactor := fun x_0 => g1_clear_cofactor (x_0) in
    #import {sig #[ G1_MAP_TO_CURVE_SVDW ] : g1_map_to_curve_svdw_inp → g1_map_to_curve_svdw_out } as g1_map_to_curve_svdw ;;
    let g1_map_to_curve_svdw := fun x_0 => g1_map_to_curve_svdw (x_0) in
    ({ code  '(u_9137 : seq fp_t) ←
        ( '(temp_9135 : seq fp_t) ←
            (fp_hash_to_field (msg_9132) (dst_9133) (usize 1)) ;;
          ret (temp_9135)) ;;
       '(q_9141 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( '(temp_9138 : fp_t) ←
            (seq_index (u_9137) (usize 0)) ;;
           '(temp_9140 : g1_t) ←
            (g1_map_to_curve_svdw (temp_9138)) ;;
          ret (temp_9140)) ;;
       '(p_9144 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( '(temp_9143 : g1_t) ←
            (g1_clear_cofactor (q_9141)) ;;
          ret (temp_9143)) ;;
      @ret ((fp_t '× fp_t '× bool_ChoiceEquality)) (p_9144) } : code (CEfset (
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

Definition output_9196_loc : ChoiceEqualityLocation :=
  ((seq (fp_t '× fp_t) ; 9197%nat)).
Notation "'fp2_hash_to_field_inp'" := (
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'fp2_hash_to_field_out'" := (
  seq fp2_t : choice_type) (in custom pack_type at level 2).
Definition FP2_HASH_TO_FIELD : nat :=
  (9198).
Program Definition fp2_hash_to_field
   : package (CEfset ([output_9196_loc])) [interface
  #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
  ] [interface
  #val #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out
  ] :=
  (
    [package #def #[ FP2_HASH_TO_FIELD ] (temp_inp : fp2_hash_to_field_inp) : fp2_hash_to_field_out { 
    let '(
      msg_9151 , dst_9152 , count_9146) := temp_inp : byte_seq '× byte_seq '× uint_size in
    #import {sig #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out } as expand_message_xmd ;;
    let expand_message_xmd := fun x_0 x_1 x_2 => expand_message_xmd (
      x_0,x_1,x_2) in
    ({ code  '(len_in_bytes_9153 : uint_size) ←
        ( '(temp_9148 : uint_size) ←
            ((count_9146) .* (usize 2)) ;;
           '(temp_9150 : uint_size) ←
            ((temp_9148) .* (l_v)) ;;
          ret (temp_9150)) ;;
       '(uniform_bytes_9163 : seq uint8) ←
        ( '(temp_9155 : byte_seq) ←
            (expand_message_xmd (msg_9151) (dst_9152) (len_in_bytes_9153)) ;;
          ret (temp_9155)) ;;
       '(output_9196 : seq (fp_t '× fp_t)) ←
          ( temp_9157 ←
              (seq_new_ (default : fp2_t) (count_9146)) ;;
            ret (temp_9157)) ;;
        #put output_9196_loc := output_9196 ;;
       '(output_9196 : (seq (fp_t '× fp_t))) ←
        (foldi' (usize 0) (count_9146) output_9196 (L2 := CEfset (
                [output_9196_loc])) (I2 := [interface
              #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_9158 output_9196 =>
            ({ code  '(elm_offset_9164 : uint_size) ←
                ( '(temp_9160 : uint_size) ←
                    ((l_v) .* (i_9158)) ;;
                   '(temp_9162 : uint_size) ←
                    ((temp_9160) .* (usize 2)) ;;
                  ret (temp_9162)) ;;
               '(tv_9167 : seq uint8) ←
                ( '(temp_9166 : seq uint8) ←
                    (seq_slice (uniform_bytes_9163) (elm_offset_9164) (l_v)) ;;
                  ret (temp_9166)) ;;
               '(e_1_9194 : fp_t) ←
                ( '(temp_9169 : fp_hash_t) ←
                    (nat_mod_from_byte_seq_be (tv_9167)) ;;
                   temp_9171 ←
                    (nat_mod_to_byte_seq_be (temp_9169)) ;;
                   '(temp_9173 : seq uint8) ←
                    (seq_slice (temp_9171) (usize 16) (usize 48)) ;;
                   '(temp_9175 : fp_t) ←
                    (nat_mod_from_byte_seq_be (temp_9173)) ;;
                  ret (temp_9175)) ;;
               '(elm_offset_9182 : uint_size) ←
                ( '(temp_9177 : uint_size) ←
                    ((i_9158) .* (usize 2)) ;;
                   '(temp_9179 : uint_size) ←
                    ((usize 1) .+ (temp_9177)) ;;
                   '(temp_9181 : uint_size) ←
                    ((l_v) .* (temp_9179)) ;;
                  ret (temp_9181)) ;;
               '(tv_9185 : seq uint8) ←
                ( '(temp_9184 : seq uint8) ←
                    (seq_slice (uniform_bytes_9163) (elm_offset_9182) (l_v)) ;;
                  ret (temp_9184)) ;;
               '(e_2_9195 : fp_t) ←
                ( '(temp_9187 : fp_hash_t) ←
                    (nat_mod_from_byte_seq_be (tv_9185)) ;;
                   temp_9189 ←
                    (nat_mod_to_byte_seq_be (temp_9187)) ;;
                   '(temp_9191 : seq uint8) ←
                    (seq_slice (temp_9189) (usize 16) (usize 48)) ;;
                   '(temp_9193 : fp_t) ←
                    (nat_mod_from_byte_seq_be (temp_9191)) ;;
                  ret (temp_9193)) ;;
               '(output_9196 : seq (fp_t '× fp_t)) ←
                (ret (seq_upd output_9196 (i_9158) (prod_ce(e_1_9194, e_2_9195
                      )))) ;;
              
              @ret ((seq (fp_t '× fp_t))) (output_9196) } : code (CEfset (
                  [output_9196_loc])) [interface] _))) ;;
      
      @ret (seq (fp_t '× fp_t)) (output_9196) } : code (CEfset (
          [output_9196_loc])) [interface
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
  (9219).
Program Definition fp2_sgn0
   : package (fset.fset0) [interface
  #val #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out ] [interface
  #val #[ FP2_SGN0 ] : fp2_sgn0_inp → fp2_sgn0_out ] :=
  ([package #def #[ FP2_SGN0 ] (temp_inp : fp2_sgn0_inp) : fp2_sgn0_out { 
    let '(x_9199) := temp_inp : fp2_t in
    #import {sig #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out } as fp_sgn0 ;;
    let fp_sgn0 := fun x_0 => fp_sgn0 (x_0) in
    ({ code  temp_9218 ←
        (ret (x_9199)) ;;
      let '(x0_9200, x1_9207) :=
        (temp_9218) : (fp_t '× fp_t) in
       '(sign_0_9210 : bool_ChoiceEquality) ←
        ( '(temp_9202 : bool_ChoiceEquality) ←
            (fp_sgn0 (x0_9200)) ;;
          ret (temp_9202)) ;;
       '(zero_0_9211 : bool_ChoiceEquality) ←
        ( '(temp_9204 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_9206 : bool_ChoiceEquality) ←
            ((x0_9200) =.? (temp_9204)) ;;
          ret (temp_9206)) ;;
       '(sign_1_9212 : bool_ChoiceEquality) ←
        ( '(temp_9209 : bool_ChoiceEquality) ←
            (fp_sgn0 (x1_9207)) ;;
          ret (temp_9209)) ;;
       '(temp_9214 : bool_ChoiceEquality) ←
        ((zero_0_9211) && (sign_1_9212)) ;;
       '(temp_9216 : bool_ChoiceEquality) ←
        ((sign_0_9210) || (temp_9214)) ;;
      @ret (bool_ChoiceEquality) (temp_9216) } : code (fset.fset0) [interface
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
  (9251).
Program Definition fp2_is_square
   : package (fset.fset0) [interface] [interface
  #val #[ FP2_IS_SQUARE ] : fp2_is_square_inp → fp2_is_square_out ] :=
  (
    [package #def #[ FP2_IS_SQUARE ] (temp_inp : fp2_is_square_inp) : fp2_is_square_out { 
    let '(x_9224) := temp_inp : fp2_t in
    ({ code  '(c1_9236 : fp_t) ←
        ( '(temp_9221 : seq int8) ←
            (array_to_be_bytes (p_1_2_v)) ;;
           '(temp_9223 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_9221)) ;;
          ret (temp_9223)) ;;
       temp_9250 ←
        (ret (x_9224)) ;;
      let '(x1_9225, x2_9228) :=
        (temp_9250) : (fp_t '× fp_t) in
       '(tv1_9231 : fp_t) ←
        ( '(temp_9227 : fp_t) ←
            ((x1_9225) *% (x1_9225)) ;;
          ret (temp_9227)) ;;
       '(tv2_9232 : fp_t) ←
        ( '(temp_9230 : fp_t) ←
            ((x2_9228) *% (x2_9228)) ;;
          ret (temp_9230)) ;;
       '(tv1_9235 : fp_t) ←
        ( '(temp_9234 : fp_t) ←
            ((tv1_9231) +% (tv2_9232)) ;;
          ret (temp_9234)) ;;
       '(tv1_9245 : fp_t) ←
        ( temp_9238 ←
            (nat_mod_pow_self (tv1_9235) (c1_9236)) ;;
          ret (temp_9238)) ;;
       '(neg1_9246 : fp_t) ←
        ( '(temp_9240 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_9242 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_9244 : fp_t) ←
            ((temp_9240) -% (temp_9242)) ;;
          ret (temp_9244)) ;;
       '(temp_9248 : bool_ChoiceEquality) ←
        ((tv1_9245) !=.? (neg1_9246)) ;;
      @ret (bool_ChoiceEquality) (temp_9248) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_fp2_is_square : package _ _ _ :=
  (fp2_is_square).
Fail Next Obligation.

Definition c_9256_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 9268%nat)).
Notation "'fp2exp_inp'" := (
  fp2_t '× fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2exp_out'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Definition FP2EXP : nat :=
  (9269).
Program Definition fp2exp
   : package (CEfset ([c_9256_loc])) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] [interface
  #val #[ FP2EXP ] : fp2exp_inp → fp2exp_out ] :=
  ([package #def #[ FP2EXP ] (temp_inp : fp2exp_inp) : fp2exp_out { 
    let '(n_9265 , k_9259) := temp_inp : fp2_t '× fp_t in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    ({ code  '(c_9256 : (fp_t '× fp_t)) ←
          ( '(temp_9253 : fp_t) ←
              (nat_mod_one ) ;;
             temp_9255 ←
              (fp2fromfp (temp_9253)) ;;
            ret (temp_9255)) ;;
        #put c_9256_loc := c_9256 ;;
       '(c_9256 : ((fp_t '× fp_t))) ←
        (foldi' (usize 0) (usize 381) c_9256 (L2 := CEfset ([c_9256_loc])) (
              I2 := [interface
              #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_9260 c_9256 =>
            ({ code  '(c_9256 : (fp_t '× fp_t)) ←
                  (( temp_9258 ←
                        (fp2mul (c_9256) (c_9256)) ;;
                      ret (temp_9258))) ;;
                #put c_9256_loc := c_9256 ;;
              
               '(temp_9262 : uint_size) ←
                ((usize 380) .- (i_9260)) ;;
               temp_9264 ←
                (nat_mod_bit (k_9259) (temp_9262)) ;;
               '(c_9256 : ((fp_t '× fp_t))) ←
                (if temp_9264:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(c_9256 : (
                            fp_t '×
                            fp_t
                          )) ←
                        (( temp_9267 ←
                              (fp2mul (c_9256) (n_9265)) ;;
                            ret (temp_9267))) ;;
                      #put c_9256_loc := c_9256 ;;
                    
                    @ret (((fp_t '× fp_t))) (c_9256) in
                    ({ code temp_then } : code (CEfset (
                          [c_9256_loc])) [interface
                      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] _))
                  else @ret (((fp_t '× fp_t))) (c_9256)) ;;
              
              @ret (((fp_t '× fp_t))) (c_9256) } : code (CEfset (
                  [c_9256_loc])) [interface
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] _))) ;;
      
      @ret ((fp_t '× fp_t)) (c_9256) } : code (CEfset (
          [c_9256_loc])) [interface
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
  (9320).
Program Definition fp2_sqrt
   : package (CEfset ([])) [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
  #val #[ FP2EXP ] : fp2exp_inp → fp2exp_out ;
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] [interface
  #val #[ FP2_SQRT ] : fp2_sqrt_inp → fp2_sqrt_out ] :=
  ([package #def #[ FP2_SQRT ] (temp_inp : fp2_sqrt_inp) : fp2_sqrt_out { 
    let '(a_9278) := temp_inp : fp2_t in
    #import {sig #[ FP2ADD ] : fp2add_inp → fp2add_out } as fp2add ;;
    let fp2add := fun x_0 x_1 => fp2add (x_0,x_1) in
    #import {sig #[ FP2EXP ] : fp2exp_inp → fp2exp_out } as fp2exp ;;
    let fp2exp := fun x_0 x_1 => fp2exp (x_0,x_1) in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    ({ code  '(c1_9279 : fp_t) ←
        ( '(temp_9271 : seq int8) ←
            (array_to_be_bytes (p_3_4_v)) ;;
           '(temp_9273 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_9271)) ;;
          ret (temp_9273)) ;;
       '(c2_9304 : fp_t) ←
        ( '(temp_9275 : seq int8) ←
            (array_to_be_bytes (p_1_2_v)) ;;
           '(temp_9277 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_9275)) ;;
          ret (temp_9277)) ;;
       '(a1_9282 : (fp_t '× fp_t)) ←
        ( '(temp_9281 : fp2_t) ←
            (fp2exp (a_9278) (c1_9279)) ;;
          ret (temp_9281)) ;;
       '(alpha_9301 : (fp_t '× fp_t)) ←
        ( temp_9284 ←
            (fp2mul (a1_9282) (a_9278)) ;;
           temp_9286 ←
            (fp2mul (a1_9282) (temp_9284)) ;;
          ret (temp_9286)) ;;
       '(x0_9314 : (fp_t '× fp_t)) ←
        ( temp_9288 ←
            (fp2mul (a1_9282) (a_9278)) ;;
          ret (temp_9288)) ;;
       '(neg1_9307 : (fp_t '× fp_t)) ←
        ( '(temp_9290 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_9292 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_9294 : fp_t) ←
            ((temp_9290) -% (temp_9292)) ;;
           '(temp_9296 : fp_t) ←
            (nat_mod_zero ) ;;
          ret (prod_ce(temp_9294, temp_9296))) ;;
       '(b_9317 : (fp_t '× fp_t)) ←
        ( '(temp_9298 : fp_t) ←
            (nat_mod_one ) ;;
           temp_9300 ←
            (fp2fromfp (temp_9298)) ;;
           temp_9303 ←
            (fp2add (temp_9300) (alpha_9301)) ;;
           '(temp_9306 : fp2_t) ←
            (fp2exp (temp_9303) (c2_9304)) ;;
          ret (temp_9306)) ;;
       '(temp_9309 : bool_ChoiceEquality) ←
        ((alpha_9301) =.? (neg1_9307)) ;;
       '(temp_9311 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_9313 : fp_t) ←
        (nat_mod_one ) ;;
       temp_9316 ←
        (fp2mul (prod_ce(temp_9311, temp_9313)) (x0_9314)) ;;
       temp_9319 ←
        (fp2mul (b_9317) (x0_9314)) ;;
      @ret ((fp_t '× fp_t)) ((if (
            temp_9309):bool_ChoiceEquality then (*inline*) (temp_9316) else (
            temp_9319))) } : code (CEfset ([])) [interface
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
  (9332).
Program Definition g2_curve_func
   : package (fset.fset0) [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] [interface
  #val #[ G2_CURVE_FUNC ] : g2_curve_func_inp → g2_curve_func_out ] :=
  (
    [package #def #[ G2_CURVE_FUNC ] (temp_inp : g2_curve_func_inp) : g2_curve_func_out { 
    let '(x_9321) := temp_inp : fp2_t in
    #import {sig #[ FP2ADD ] : fp2add_inp → fp2add_out } as fp2add ;;
    let fp2add := fun x_0 x_1 => fp2add (x_0,x_1) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    ({ code  temp_9323 ←
        (fp2mul (x_9321) (x_9321)) ;;
       temp_9325 ←
        (fp2mul (x_9321) (temp_9323)) ;;
       '(temp_9327 : fp_t) ←
        (nat_mod_from_literal (_) (@repr U128 4)) ;;
       '(temp_9329 : fp_t) ←
        (nat_mod_from_literal (_) (@repr U128 4)) ;;
       temp_9331 ←
        (fp2add (temp_9325) (prod_ce(temp_9327, temp_9329))) ;;
      @ret ((fp_t '× fp_t)) (temp_9331) } : code (fset.fset0) [interface
      #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_g2_curve_func : package _ _ _ :=
  (seq_link g2_curve_func link_rest(package_fp2add,package_fp2mul)).
Fail Next Obligation.

Definition y_9468_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 9475%nat)).
Definition tv4_9381_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 9476%nat)).
Notation "'g2_map_to_curve_svdw_inp'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_map_to_curve_svdw_out'" := (
  g2_t : choice_type) (in custom pack_type at level 2).
Definition G2_MAP_TO_CURVE_SVDW : nat :=
  (9477).
Program Definition g2_map_to_curve_svdw
   : package (CEfset ([tv4_9381_loc ; y_9468_loc])) [interface
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
    let '(u_9342) := temp_inp : fp2_t in
    #import {sig #[ FP2_IS_SQUARE ] : fp2_is_square_inp → fp2_is_square_out } as fp2_is_square ;;
    let fp2_is_square := fun x_0 => fp2_is_square (x_0) in
    #import {sig #[ FP2_SGN0 ] : fp2_sgn0_inp → fp2_sgn0_out } as fp2_sgn0 ;;
    let fp2_sgn0 := fun x_0 => fp2_sgn0 (x_0) in
    #import {sig #[ FP2_SQRT ] : fp2_sqrt_inp → fp2_sqrt_out } as fp2_sqrt ;;
    let fp2_sqrt := fun x_0 => fp2_sqrt (x_0) in
    #import {sig #[ FP2ADD ] : fp2add_inp → fp2add_out } as fp2add ;;
    let fp2add := fun x_0 x_1 => fp2add (x_0,x_1) in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP2INV ] : fp2inv_inp → fp2inv_out } as fp2inv ;;
    let fp2inv := fun x_0 => fp2inv (x_0) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    #import {sig #[ FP2NEG ] : fp2neg_inp → fp2neg_out } as fp2neg ;;
    let fp2neg := fun x_0 => fp2neg (x_0) in
    #import {sig #[ FP2SUB ] : fp2sub_inp → fp2sub_out } as fp2sub ;;
    let fp2sub := fun x_0 x_1 => fp2sub (x_0,x_1) in
    #import {sig #[ G2_CURVE_FUNC ] : g2_curve_func_inp → g2_curve_func_out } as g2_curve_func ;;
    let g2_curve_func := fun x_0 => g2_curve_func (x_0) in
    ({ code  '(z_9339 : (fp_t '× fp_t)) ←
        ( '(temp_9334 : fp_t) ←
            (nat_mod_one ) ;;
           temp_9336 ←
            (fp2fromfp (temp_9334)) ;;
           temp_9338 ←
            (fp2neg (temp_9336)) ;;
          ret (temp_9338)) ;;
       '(gz_9345 : (fp_t '× fp_t)) ←
        ( '(temp_9341 : fp2_t) ←
            (g2_curve_func (z_9339)) ;;
          ret (temp_9341)) ;;
       '(tv1_9352 : (fp_t '× fp_t)) ←
        ( temp_9344 ←
            (fp2mul (u_9342) (u_9342)) ;;
           temp_9347 ←
            (fp2mul (temp_9344) (gz_9345)) ;;
          ret (temp_9347)) ;;
       '(tv2_9362 : (fp_t '× fp_t)) ←
        ( '(temp_9349 : fp_t) ←
            (nat_mod_one ) ;;
           temp_9351 ←
            (fp2fromfp (temp_9349)) ;;
           temp_9354 ←
            (fp2add (temp_9351) (tv1_9352)) ;;
          ret (temp_9354)) ;;
       '(tv1_9361 : (fp_t '× fp_t)) ←
        ( '(temp_9356 : fp_t) ←
            (nat_mod_one ) ;;
           temp_9358 ←
            (fp2fromfp (temp_9356)) ;;
           temp_9360 ←
            (fp2sub (temp_9358) (tv1_9352)) ;;
          ret (temp_9360)) ;;
       '(tv3_9388 : (fp_t '× fp_t)) ←
        ( temp_9364 ←
            (fp2mul (tv1_9361) (tv2_9362)) ;;
           temp_9366 ←
            (fp2inv (temp_9364)) ;;
          ret (temp_9366)) ;;
       '(tv4_9381 : (fp_t '× fp_t)) ←
          ( temp_9368 ←
              (fp2neg (gz_9345)) ;;
             '(temp_9370 : fp_t) ←
              (nat_mod_from_literal (_) (@repr U128 3)) ;;
             temp_9372 ←
              (fp2fromfp (temp_9370)) ;;
             temp_9374 ←
              (fp2mul (z_9339) (z_9339)) ;;
             temp_9376 ←
              (fp2mul (temp_9372) (temp_9374)) ;;
             temp_9378 ←
              (fp2mul (temp_9368) (temp_9376)) ;;
             '(temp_9380 : fp2_t) ←
              (fp2_sqrt (temp_9378)) ;;
            ret (temp_9380)) ;;
        #put tv4_9381_loc := tv4_9381 ;;
       '(temp_9383 : bool_ChoiceEquality) ←
        (fp2_sgn0 (tv4_9381)) ;;
       '(tv4_9381 : ((fp_t '× fp_t))) ←
        (if temp_9383:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(tv4_9381 : (fp_t '× fp_t
                  )) ←
                (( temp_9385 ←
                      (fp2neg (tv4_9381)) ;;
                    ret (temp_9385))) ;;
              #put tv4_9381_loc := tv4_9381 ;;
            
            @ret (((fp_t '× fp_t))) (tv4_9381) in
            ({ code temp_then } : code (CEfset ([tv4_9381_loc])) [interface
              #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ] _))
          else @ret (((fp_t '× fp_t))) (tv4_9381)) ;;
      
       '(tv5_9423 : (fp_t '× fp_t)) ←
        ( temp_9387 ←
            (fp2mul (u_9342) (tv1_9361)) ;;
           temp_9390 ←
            (fp2mul (temp_9387) (tv3_9388)) ;;
           temp_9392 ←
            (fp2mul (temp_9390) (tv4_9381)) ;;
          ret (temp_9392)) ;;
       '(tv6_9442 : (fp_t '× fp_t)) ←
        ( '(temp_9394 : fp_t) ←
            (nat_mod_from_literal (_) (@repr U128 4)) ;;
           temp_9396 ←
            (fp2fromfp (temp_9394)) ;;
           temp_9398 ←
            (fp2neg (temp_9396)) ;;
           temp_9400 ←
            (fp2mul (temp_9398) (gz_9345)) ;;
           '(temp_9402 : fp_t) ←
            (nat_mod_from_literal (_) (@repr U128 3)) ;;
           temp_9404 ←
            (fp2fromfp (temp_9402)) ;;
           temp_9406 ←
            (fp2mul (z_9339) (z_9339)) ;;
           temp_9408 ←
            (fp2mul (temp_9404) (temp_9406)) ;;
           temp_9410 ←
            (fp2inv (temp_9408)) ;;
           temp_9412 ←
            (fp2mul (temp_9400) (temp_9410)) ;;
          ret (temp_9412)) ;;
       '(x1_9450 : (fp_t '× fp_t)) ←
        ( temp_9414 ←
            (fp2neg (z_9339)) ;;
           '(temp_9416 : fp_t) ←
            (nat_mod_two ) ;;
           temp_9418 ←
            (fp2fromfp (temp_9416)) ;;
           temp_9420 ←
            (fp2inv (temp_9418)) ;;
           temp_9422 ←
            (fp2mul (temp_9414) (temp_9420)) ;;
           temp_9425 ←
            (fp2sub (temp_9422) (tv5_9423)) ;;
          ret (temp_9425)) ;;
       '(x2_9455 : (fp_t '× fp_t)) ←
        ( temp_9427 ←
            (fp2neg (z_9339)) ;;
           '(temp_9429 : fp_t) ←
            (nat_mod_two ) ;;
           temp_9431 ←
            (fp2fromfp (temp_9429)) ;;
           temp_9433 ←
            (fp2inv (temp_9431)) ;;
           temp_9435 ←
            (fp2mul (temp_9427) (temp_9433)) ;;
           temp_9437 ←
            (fp2add (temp_9435) (tv5_9423)) ;;
          ret (temp_9437)) ;;
       '(tv7_9443 : (fp_t '× fp_t)) ←
        ( temp_9439 ←
            (fp2mul (tv2_9362) (tv2_9362)) ;;
           temp_9441 ←
            (fp2mul (temp_9439) (tv3_9388)) ;;
          ret (temp_9441)) ;;
       '(x3_9460 : (fp_t '× fp_t)) ←
        ( temp_9445 ←
            (fp2mul (tv7_9443) (tv7_9443)) ;;
           temp_9447 ←
            (fp2mul (tv6_9442) (temp_9445)) ;;
           temp_9449 ←
            (fp2add (z_9339) (temp_9447)) ;;
          ret (temp_9449)) ;;
       '(x_9461 : (fp_t '× fp_t)) ←
        ( '(temp_9452 : fp2_t) ←
            (g2_curve_func (x1_9450)) ;;
           '(temp_9454 : bool_ChoiceEquality) ←
            (fp2_is_square (temp_9452)) ;;
           '(temp_9457 : fp2_t) ←
            (g2_curve_func (x2_9455)) ;;
           '(temp_9459 : bool_ChoiceEquality) ←
            (fp2_is_square (temp_9457)) ;;
          ret ((if (temp_9454):bool_ChoiceEquality then (*inline*) (
                x1_9450) else ((if (
                    temp_9459):bool_ChoiceEquality then (*inline*) (
                    x2_9455) else (x3_9460)))))) ;;
       '(y_9468 : (fp_t '× fp_t)) ←
          ( '(temp_9463 : fp2_t) ←
              (g2_curve_func (x_9461)) ;;
             '(temp_9465 : fp2_t) ←
              (fp2_sqrt (temp_9463)) ;;
            ret (temp_9465)) ;;
        #put y_9468_loc := y_9468 ;;
       '(temp_9467 : bool_ChoiceEquality) ←
        (fp2_sgn0 (u_9342)) ;;
       '(temp_9470 : bool_ChoiceEquality) ←
        (fp2_sgn0 (y_9468)) ;;
       '(temp_9472 : bool_ChoiceEquality) ←
        ((temp_9467) !=.? (temp_9470)) ;;
       '(y_9468 : ((fp_t '× fp_t))) ←
        (if temp_9472:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(y_9468 : (fp_t '× fp_t)) ←
                (( temp_9474 ←
                      (fp2neg (y_9468)) ;;
                    ret (temp_9474))) ;;
              #put y_9468_loc := y_9468 ;;
            
            @ret (((fp_t '× fp_t))) (y_9468) in
            ({ code temp_then } : code (CEfset (
                  [tv4_9381_loc ; y_9468_loc])) [interface
              #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ] _))
          else @ret (((fp_t '× fp_t))) (y_9468)) ;;
      
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality)) (
        prod_ce(x_9461, y_9468, (false : bool_ChoiceEquality))) } : code (
        CEfset ([tv4_9381_loc ; y_9468_loc])) [interface
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
  (9536).
Program Definition psi
   : package (CEfset ([])) [interface
  #val #[ FP2CONJUGATE ] : fp2conjugate_inp → fp2conjugate_out ;
  #val #[ FP2EXP ] : fp2exp_inp → fp2exp_out ;
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] [interface
  #val #[ PSI ] : psi_inp → psi_out ] :=
  ([package #def #[ PSI ] (temp_inp : psi_inp) : psi_out { 
    let '(p_9518) := temp_inp : g2_t in
    #import {sig #[ FP2CONJUGATE ] : fp2conjugate_inp → fp2conjugate_out } as fp2conjugate ;;
    let fp2conjugate := fun x_0 => fp2conjugate (x_0) in
    #import {sig #[ FP2EXP ] : fp2exp_inp → fp2exp_out } as fp2exp ;;
    let fp2exp := fun x_0 x_1 => fp2exp (x_0,x_1) in
    #import {sig #[ FP2INV ] : fp2inv_inp → fp2inv_out } as fp2inv ;;
    let fp2inv := fun x_0 => fp2inv (x_0) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    ({ code  '(c1_9519 : (fp_t '× fp_t)) ←
        ( '(temp_9479 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_9481 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_9483 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_9485 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_9487 : fp_t) ←
            ((temp_9483) -% (temp_9485)) ;;
           '(temp_9489 : fp_t) ←
            (nat_mod_from_literal (_) (@repr U128 3)) ;;
           temp_9491 ←
            (nat_mod_inv (temp_9489)) ;;
           '(temp_9493 : fp_t) ←
            ((temp_9487) *% (temp_9491)) ;;
           '(temp_9495 : fp2_t) ←
            (fp2exp (prod_ce(temp_9479, temp_9481)) (temp_9493)) ;;
           temp_9497 ←
            (fp2inv (temp_9495)) ;;
          ret (temp_9497)) ;;
       '(c2_9525 : (fp_t '× fp_t)) ←
        ( '(temp_9499 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_9501 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_9503 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_9505 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_9507 : fp_t) ←
            ((temp_9503) -% (temp_9505)) ;;
           '(temp_9509 : fp_t) ←
            (nat_mod_two ) ;;
           temp_9511 ←
            (nat_mod_inv (temp_9509)) ;;
           '(temp_9513 : fp_t) ←
            ((temp_9507) *% (temp_9511)) ;;
           '(temp_9515 : fp2_t) ←
            (fp2exp (prod_ce(temp_9499, temp_9501)) (temp_9513)) ;;
           temp_9517 ←
            (fp2inv (temp_9515)) ;;
          ret (temp_9517)) ;;
       temp_9535 ←
        (ret (p_9518)) ;;
      let '(x_9520, y_9526, inf_9533) :=
        (temp_9535) : (
        (fp_t '× fp_t) '×
        (fp_t '× fp_t) '×
        bool_ChoiceEquality
      ) in
       '(qx_9531 : (fp_t '× fp_t)) ←
        ( temp_9522 ←
            (fp2conjugate (x_9520)) ;;
           temp_9524 ←
            (fp2mul (c1_9519) (temp_9522)) ;;
          ret (temp_9524)) ;;
       '(qy_9532 : (fp_t '× fp_t)) ←
        ( temp_9528 ←
            (fp2conjugate (y_9526)) ;;
           temp_9530 ←
            (fp2mul (c2_9525) (temp_9528)) ;;
          ret (temp_9530)) ;;
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality)) (
        prod_ce(qx_9531, qy_9532, inf_9533)) } : code (CEfset ([])) [interface
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
  (9585).
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
    let '(p_9540) := temp_inp : g2_t in
    #import {sig #[ G2ADD ] : g2add_inp → g2add_out } as g2add ;;
    let g2add := fun x_0 x_1 => g2add (x_0,x_1) in
    #import {sig #[ G2DOUBLE ] : g2double_inp → g2double_out } as g2double ;;
    let g2double := fun x_0 => g2double (x_0) in
    #import {sig #[ G2MUL ] : g2mul_inp → g2mul_out } as g2mul ;;
    let g2mul := fun x_0 x_1 => g2mul (x_0,x_1) in
    #import {sig #[ G2NEG ] : g2neg_inp → g2neg_out } as g2neg ;;
    let g2neg := fun x_0 => g2neg (x_0) in
    #import {sig #[ PSI ] : psi_inp → psi_out } as psi ;;
    let psi := fun x_0 => psi (x_0) in
    ({ code  '(c1_9539 : scalar_t) ←
        ( '(temp_9538 : scalar_t) ←
            (nat_mod_from_literal (_) (@repr U128 15132376222941642752)) ;;
          ret (temp_9538)) ;;
       '(t1_9543 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( temp_9542 ←
            (g2mul (c1_9539) (p_9540)) ;;
          ret (temp_9542)) ;;
       '(t1_9561 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( temp_9545 ←
            (g2neg (t1_9543)) ;;
          ret (temp_9545)) ;;
       '(t2_9556 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_9547 : g2_t) ←
            (psi (p_9540)) ;;
          ret (temp_9547)) ;;
       '(t3_9550 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( temp_9549 ←
            (g2double (p_9540)) ;;
          ret (temp_9549)) ;;
       '(t3_9555 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_9552 : g2_t) ←
            (psi (t3_9550)) ;;
           '(temp_9554 : g2_t) ←
            (psi (temp_9552)) ;;
          ret (temp_9554)) ;;
       '(t3_9570 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( temp_9558 ←
            (g2neg (t2_9556)) ;;
           temp_9560 ←
            (g2add (t3_9555) (temp_9558)) ;;
          ret (temp_9560)) ;;
       '(t2_9564 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( temp_9563 ←
            (g2add (t1_9561) (t2_9556)) ;;
          ret (temp_9563)) ;;
       '(t2_9567 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( temp_9566 ←
            (g2mul (c1_9539) (t2_9564)) ;;
          ret (temp_9566)) ;;
       '(t2_9571 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( temp_9569 ←
            (g2neg (t2_9567)) ;;
          ret (temp_9569)) ;;
       '(t3_9574 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( temp_9573 ←
            (g2add (t3_9570) (t2_9571)) ;;
          ret (temp_9573)) ;;
       '(t3_9579 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( temp_9576 ←
            (g2neg (t1_9561)) ;;
           temp_9578 ←
            (g2add (t3_9574) (temp_9576)) ;;
          ret (temp_9578)) ;;
       '(q_9584 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( temp_9581 ←
            (g2neg (p_9540)) ;;
           temp_9583 ←
            (g2add (t3_9579) (temp_9581)) ;;
          ret (temp_9583)) ;;
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality)) (
        q_9584) } : code (CEfset ([])) [interface
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
  (9607).
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
    let '(msg_9586 , dst_9587) := temp_inp : byte_seq '× byte_seq in
    #import {sig #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out } as fp2_hash_to_field ;;
    let fp2_hash_to_field := fun x_0 x_1 x_2 => fp2_hash_to_field (
      x_0,x_1,x_2) in
    #import {sig #[ G2_CLEAR_COFACTOR ] : g2_clear_cofactor_inp → g2_clear_cofactor_out } as g2_clear_cofactor ;;
    let g2_clear_cofactor := fun x_0 => g2_clear_cofactor (x_0) in
    #import {sig #[ G2_MAP_TO_CURVE_SVDW ] : g2_map_to_curve_svdw_inp → g2_map_to_curve_svdw_out } as g2_map_to_curve_svdw ;;
    let g2_map_to_curve_svdw := fun x_0 => g2_map_to_curve_svdw (x_0) in
    #import {sig #[ G2ADD ] : g2add_inp → g2add_out } as g2add ;;
    let g2add := fun x_0 x_1 => g2add (x_0,x_1) in
    ({ code  '(u_9591 : seq fp2_t) ←
        ( '(temp_9589 : seq fp2_t) ←
            (fp2_hash_to_field (msg_9586) (dst_9587) (usize 2)) ;;
          ret (temp_9589)) ;;
       '(q0_9599 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_9592 : fp2_t) ←
            (seq_index (u_9591) (usize 0)) ;;
           '(temp_9594 : g2_t) ←
            (g2_map_to_curve_svdw (temp_9592)) ;;
          ret (temp_9594)) ;;
       '(q1_9600 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_9596 : fp2_t) ←
            (seq_index (u_9591) (usize 1)) ;;
           '(temp_9598 : g2_t) ←
            (g2_map_to_curve_svdw (temp_9596)) ;;
          ret (temp_9598)) ;;
       '(r_9603 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( temp_9602 ←
            (g2add (q0_9599) (q1_9600)) ;;
          ret (temp_9602)) ;;
       '(p_9606 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_9605 : g2_t) ←
            (g2_clear_cofactor (r_9603)) ;;
          ret (temp_9605)) ;;
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality)) (
        p_9606) } : code (CEfset ([])) [interface
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
  (9621).
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
    let '(msg_9608 , dst_9609) := temp_inp : byte_seq '× byte_seq in
    #import {sig #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out } as fp2_hash_to_field ;;
    let fp2_hash_to_field := fun x_0 x_1 x_2 => fp2_hash_to_field (
      x_0,x_1,x_2) in
    #import {sig #[ G2_CLEAR_COFACTOR ] : g2_clear_cofactor_inp → g2_clear_cofactor_out } as g2_clear_cofactor ;;
    let g2_clear_cofactor := fun x_0 => g2_clear_cofactor (x_0) in
    #import {sig #[ G2_MAP_TO_CURVE_SVDW ] : g2_map_to_curve_svdw_inp → g2_map_to_curve_svdw_out } as g2_map_to_curve_svdw ;;
    let g2_map_to_curve_svdw := fun x_0 => g2_map_to_curve_svdw (x_0) in
    ({ code  '(u_9613 : seq fp2_t) ←
        ( '(temp_9611 : seq fp2_t) ←
            (fp2_hash_to_field (msg_9608) (dst_9609) (usize 1)) ;;
          ret (temp_9611)) ;;
       '(q_9617 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_9614 : fp2_t) ←
            (seq_index (u_9613) (usize 0)) ;;
           '(temp_9616 : g2_t) ←
            (g2_map_to_curve_svdw (temp_9614)) ;;
          ret (temp_9616)) ;;
       '(p_9620 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_9619 : g2_t) ←
            (g2_clear_cofactor (q_9617)) ;;
          ret (temp_9619)) ;;
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality)) (
        p_9620) } : code (CEfset ([])) [interface
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
  (let temp_9623 : int64 :=
      (secret (@repr U64 5707120929990979)) in
    let temp_9625 : int64 :=
      (secret (@repr U64 4425131892511951234)) in
    let temp_9627 : int64 :=
      (secret (@repr U64 12748169179688756904)) in
    let temp_9629 : int64 :=
      (secret (@repr U64 15629909748249821612)) in
    let temp_9631 : int64 :=
      (secret (@repr U64 10994253769421683071)) in
    let temp_9633 : int64 :=
      (secret (@repr U64 6698022561392380957)) in
    let temp_9635 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9623;
          temp_9625;
          temp_9627;
          temp_9629;
          temp_9631;
          temp_9633
        ]) in
    (temp_9635)).

Definition g1_iso_b_v : (arr_fp_t) :=
  (let temp_9637 : int64 :=
      (secret (@repr U64 1360808972976160816)) in
    let temp_9639 : int64 :=
      (secret (@repr U64 111203405409480251)) in
    let temp_9641 : int64 :=
      (secret (@repr U64 2312248699302920304)) in
    let temp_9643 : int64 :=
      (secret (@repr U64 11581500465278574325)) in
    let temp_9645 : int64 :=
      (secret (@repr U64 6495071758858381989)) in
    let temp_9647 : int64 :=
      (secret (@repr U64 15117538217124375520)) in
    let temp_9649 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9637;
          temp_9639;
          temp_9641;
          temp_9643;
          temp_9645;
          temp_9647
        ]) in
    (temp_9649)).

Definition g1_xnum_k_0_v : (arr_fp_t) :=
  (let temp_9651 : int64 :=
      (secret (@repr U64 1270119733718627136)) in
    let temp_9653 : int64 :=
      (secret (@repr U64 13261148298159854981)) in
    let temp_9655 : int64 :=
      (secret (@repr U64 7723742117508874335)) in
    let temp_9657 : int64 :=
      (secret (@repr U64 17465657917644792520)) in
    let temp_9659 : int64 :=
      (secret (@repr U64 6201670911048166766)) in
    let temp_9661 : int64 :=
      (secret (@repr U64 12586459670690286007)) in
    let temp_9663 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9651;
          temp_9653;
          temp_9655;
          temp_9657;
          temp_9659;
          temp_9661
        ]) in
    (temp_9663)).

Definition g1_xnum_k_1_v : (arr_fp_t) :=
  (let temp_9665 : int64 :=
      (secret (@repr U64 1668951808976071471)) in
    let temp_9667 : int64 :=
      (secret (@repr U64 398773841247578140)) in
    let temp_9669 : int64 :=
      (secret (@repr U64 8941869963990959127)) in
    let temp_9671 : int64 :=
      (secret (@repr U64 17682789360670468203)) in
    let temp_9673 : int64 :=
      (secret (@repr U64 5204176168283587414)) in
    let temp_9675 : int64 :=
      (secret (@repr U64 16732261237459223483)) in
    let temp_9677 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9665;
          temp_9667;
          temp_9669;
          temp_9671;
          temp_9673;
          temp_9675
        ]) in
    (temp_9677)).

Definition g1_xnum_k_2_v : (arr_fp_t) :=
  (let temp_9679 : int64 :=
      (secret (@repr U64 960393023080265964)) in
    let temp_9681 : int64 :=
      (secret (@repr U64 2094253841180170779)) in
    let temp_9683 : int64 :=
      (secret (@repr U64 14844748873776858085)) in
    let temp_9685 : int64 :=
      (secret (@repr U64 7528018573573808732)) in
    let temp_9687 : int64 :=
      (secret (@repr U64 10776056440809943711)) in
    let temp_9689 : int64 :=
      (secret (@repr U64 16147550488514976944)) in
    let temp_9691 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9679;
          temp_9681;
          temp_9683;
          temp_9685;
          temp_9687;
          temp_9689
        ]) in
    (temp_9691)).

Definition g1_xnum_k_3_v : (arr_fp_t) :=
  (let temp_9693 : int64 :=
      (secret (@repr U64 1691355743628586423)) in
    let temp_9695 : int64 :=
      (secret (@repr U64 5622191986793862162)) in
    let temp_9697 : int64 :=
      (secret (@repr U64 15561595211679121189)) in
    let temp_9699 : int64 :=
      (secret (@repr U64 17416319752018800771)) in
    let temp_9701 : int64 :=
      (secret (@repr U64 5996228842464768403)) in
    let temp_9703 : int64 :=
      (secret (@repr U64 14245880009877842017)) in
    let temp_9705 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9693;
          temp_9695;
          temp_9697;
          temp_9699;
          temp_9701;
          temp_9703
        ]) in
    (temp_9705)).

Definition g1_xnum_k_4_v : (arr_fp_t) :=
  (let temp_9707 : int64 :=
      (secret (@repr U64 1051997788391994435)) in
    let temp_9709 : int64 :=
      (secret (@repr U64 7368650625050054228)) in
    let temp_9711 : int64 :=
      (secret (@repr U64 11086623519836470079)) in
    let temp_9713 : int64 :=
      (secret (@repr U64 607681821319080984)) in
    let temp_9715 : int64 :=
      (secret (@repr U64 10978131499682789316)) in
    let temp_9717 : int64 :=
      (secret (@repr U64 5842660658088809945)) in
    let temp_9719 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9707;
          temp_9709;
          temp_9711;
          temp_9713;
          temp_9715;
          temp_9717
        ]) in
    (temp_9719)).

Definition g1_xnum_k_5_v : (arr_fp_t) :=
  (let temp_9721 : int64 :=
      (secret (@repr U64 1598992431623377919)) in
    let temp_9723 : int64 :=
      (secret (@repr U64 130921168661596853)) in
    let temp_9725 : int64 :=
      (secret (@repr U64 15797696746983946651)) in
    let temp_9727 : int64 :=
      (secret (@repr U64 11444679715590672272)) in
    let temp_9729 : int64 :=
      (secret (@repr U64 11567228658253249817)) in
    let temp_9731 : int64 :=
      (secret (@repr U64 14777367860349315459)) in
    let temp_9733 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9721;
          temp_9723;
          temp_9725;
          temp_9727;
          temp_9729;
          temp_9731
        ]) in
    (temp_9733)).

Definition g1_xnum_k_6_v : (arr_fp_t) :=
  (let temp_9735 : int64 :=
      (secret (@repr U64 967946631563726121)) in
    let temp_9737 : int64 :=
      (secret (@repr U64 7653628713030275775)) in
    let temp_9739 : int64 :=
      (secret (@repr U64 12760252618317466849)) in
    let temp_9741 : int64 :=
      (secret (@repr U64 10378793938173061930)) in
    let temp_9743 : int64 :=
      (secret (@repr U64 10205808941053849290)) in
    let temp_9745 : int64 :=
      (secret (@repr U64 15985511645807504772)) in
    let temp_9747 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9735;
          temp_9737;
          temp_9739;
          temp_9741;
          temp_9743;
          temp_9745
        ]) in
    (temp_9747)).

Definition g1_xnum_k_7_v : (arr_fp_t) :=
  (let temp_9749 : int64 :=
      (secret (@repr U64 1709149555065084898)) in
    let temp_9751 : int64 :=
      (secret (@repr U64 16750075057192140371)) in
    let temp_9753 : int64 :=
      (secret (@repr U64 3849985779734105521)) in
    let temp_9755 : int64 :=
      (secret (@repr U64 11998370262181639475)) in
    let temp_9757 : int64 :=
      (secret (@repr U64 4159013751748851119)) in
    let temp_9759 : int64 :=
      (secret (@repr U64 11298218755092433038)) in
    let temp_9761 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9749;
          temp_9751;
          temp_9753;
          temp_9755;
          temp_9757;
          temp_9759
        ]) in
    (temp_9761)).

Definition g1_xnum_k_8_v : (arr_fp_t) :=
  (let temp_9763 : int64 :=
      (secret (@repr U64 580186936973955012)) in
    let temp_9765 : int64 :=
      (secret (@repr U64 8903813505199544589)) in
    let temp_9767 : int64 :=
      (secret (@repr U64 14140024565662700916)) in
    let temp_9769 : int64 :=
      (secret (@repr U64 11728946595272970718)) in
    let temp_9771 : int64 :=
      (secret (@repr U64 5738313744366653077)) in
    let temp_9773 : int64 :=
      (secret (@repr U64 7886252005760951063)) in
    let temp_9775 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9763;
          temp_9765;
          temp_9767;
          temp_9769;
          temp_9771;
          temp_9773
        ]) in
    (temp_9775)).

Definition g1_xnum_k_9_v : (arr_fp_t) :=
  (let temp_9777 : int64 :=
      (secret (@repr U64 1628930385436977092)) in
    let temp_9779 : int64 :=
      (secret (@repr U64 3318087848058654498)) in
    let temp_9781 : int64 :=
      (secret (@repr U64 15937899882900905113)) in
    let temp_9783 : int64 :=
      (secret (@repr U64 7449821001803307903)) in
    let temp_9785 : int64 :=
      (secret (@repr U64 11752436998487615353)) in
    let temp_9787 : int64 :=
      (secret (@repr U64 9161465579737517214)) in
    let temp_9789 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9777;
          temp_9779;
          temp_9781;
          temp_9783;
          temp_9785;
          temp_9787
        ]) in
    (temp_9789)).

Definition g1_xnum_k_10_v : (arr_fp_t) :=
  (let temp_9791 : int64 :=
      (secret (@repr U64 1167027828517898210)) in
    let temp_9793 : int64 :=
      (secret (@repr U64 8275623842221021965)) in
    let temp_9795 : int64 :=
      (secret (@repr U64 18049808134997311382)) in
    let temp_9797 : int64 :=
      (secret (@repr U64 15351349873550116966)) in
    let temp_9799 : int64 :=
      (secret (@repr U64 17769927732099571180)) in
    let temp_9801 : int64 :=
      (secret (@repr U64 14584871380308065147)) in
    let temp_9803 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9791;
          temp_9793;
          temp_9795;
          temp_9797;
          temp_9799;
          temp_9801
        ]) in
    (temp_9803)).

Definition g1_xnum_k_11_v : (arr_fp_t) :=
  (let temp_9805 : int64 :=
      (secret (@repr U64 495550047642324592)) in
    let temp_9807 : int64 :=
      (secret (@repr U64 13627494601717575229)) in
    let temp_9809 : int64 :=
      (secret (@repr U64 3591512392926246844)) in
    let temp_9811 : int64 :=
      (secret (@repr U64 2576269112800734056)) in
    let temp_9813 : int64 :=
      (secret (@repr U64 14000314106239596831)) in
    let temp_9815 : int64 :=
      (secret (@repr U64 12234233096825917993)) in
    let temp_9817 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9805;
          temp_9807;
          temp_9809;
          temp_9811;
          temp_9813;
          temp_9815
        ]) in
    (temp_9817)).

Definition g1_xden_k_0_v : (arr_fp_t) :=
  (let temp_9819 : int64 :=
      (secret (@repr U64 633474091881273774)) in
    let temp_9821 : int64 :=
      (secret (@repr U64 1779737893574802031)) in
    let temp_9823 : int64 :=
      (secret (@repr U64 132274872219551930)) in
    let temp_9825 : int64 :=
      (secret (@repr U64 11283074393783708770)) in
    let temp_9827 : int64 :=
      (secret (@repr U64 13067430171545714168)) in
    let temp_9829 : int64 :=
      (secret (@repr U64 11041975239630265116)) in
    let temp_9831 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9819;
          temp_9821;
          temp_9823;
          temp_9825;
          temp_9827;
          temp_9829
        ]) in
    (temp_9831)).

Definition g1_xden_k_1_v : (arr_fp_t) :=
  (let temp_9833 : int64 :=
      (secret (@repr U64 1321272531362356291)) in
    let temp_9835 : int64 :=
      (secret (@repr U64 5238936591227237942)) in
    let temp_9837 : int64 :=
      (secret (@repr U64 8089002360232247308)) in
    let temp_9839 : int64 :=
      (secret (@repr U64 82967328719421271)) in
    let temp_9841 : int64 :=
      (secret (@repr U64 1430641118356186857)) in
    let temp_9843 : int64 :=
      (secret (@repr U64 16557527386785790975)) in
    let temp_9845 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9833;
          temp_9835;
          temp_9837;
          temp_9839;
          temp_9841;
          temp_9843
        ]) in
    (temp_9845)).

Definition g1_xden_k_2_v : (arr_fp_t) :=
  (let temp_9847 : int64 :=
      (secret (@repr U64 804282852993868382)) in
    let temp_9849 : int64 :=
      (secret (@repr U64 9311163821600184607)) in
    let temp_9851 : int64 :=
      (secret (@repr U64 8037026956533927121)) in
    let temp_9853 : int64 :=
      (secret (@repr U64 18205324308570099372)) in
    let temp_9855 : int64 :=
      (secret (@repr U64 15466434890074226396)) in
    let temp_9857 : int64 :=
      (secret (@repr U64 18213183315621985817)) in
    let temp_9859 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9847;
          temp_9849;
          temp_9851;
          temp_9853;
          temp_9855;
          temp_9857
        ]) in
    (temp_9859)).

Definition g1_xden_k_3_v : (arr_fp_t) :=
  (let temp_9861 : int64 :=
      (secret (@repr U64 234844145893171966)) in
    let temp_9863 : int64 :=
      (secret (@repr U64 14428037799351479124)) in
    let temp_9865 : int64 :=
      (secret (@repr U64 6559532710647391569)) in
    let temp_9867 : int64 :=
      (secret (@repr U64 6110444250091843536)) in
    let temp_9869 : int64 :=
      (secret (@repr U64 5293652763671852484)) in
    let temp_9871 : int64 :=
      (secret (@repr U64 1373009181854280920)) in
    let temp_9873 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9861;
          temp_9863;
          temp_9865;
          temp_9867;
          temp_9869;
          temp_9871
        ]) in
    (temp_9873)).

Definition g1_xden_k_4_v : (arr_fp_t) :=
  (let temp_9875 : int64 :=
      (secret (@repr U64 1416629893867312296)) in
    let temp_9877 : int64 :=
      (secret (@repr U64 751851957792514173)) in
    let temp_9879 : int64 :=
      (secret (@repr U64 18437674587247370939)) in
    let temp_9881 : int64 :=
      (secret (@repr U64 10190314345946351322)) in
    let temp_9883 : int64 :=
      (secret (@repr U64 11228207967368476701)) in
    let temp_9885 : int64 :=
      (secret (@repr U64 6025034940388909598)) in
    let temp_9887 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9875;
          temp_9877;
          temp_9879;
          temp_9881;
          temp_9883;
          temp_9885
        ]) in
    (temp_9887)).

Definition g1_xden_k_5_v : (arr_fp_t) :=
  (let temp_9889 : int64 :=
      (secret (@repr U64 1041270466333271993)) in
    let temp_9891 : int64 :=
      (secret (@repr U64 6140956605115975401)) in
    let temp_9893 : int64 :=
      (secret (@repr U64 4131830461445745997)) in
    let temp_9895 : int64 :=
      (secret (@repr U64 739642499118176303)) in
    let temp_9897 : int64 :=
      (secret (@repr U64 8358912131254619921)) in
    let temp_9899 : int64 :=
      (secret (@repr U64 13847998906088228005)) in
    let temp_9901 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9889;
          temp_9891;
          temp_9893;
          temp_9895;
          temp_9897;
          temp_9899
        ]) in
    (temp_9901)).

Definition g1_xden_k_6_v : (arr_fp_t) :=
  (let temp_9903 : int64 :=
      (secret (@repr U64 536714149743900185)) in
    let temp_9905 : int64 :=
      (secret (@repr U64 1098328982230230817)) in
    let temp_9907 : int64 :=
      (secret (@repr U64 6273329123533496713)) in
    let temp_9909 : int64 :=
      (secret (@repr U64 5633448088282521244)) in
    let temp_9911 : int64 :=
      (secret (@repr U64 16894043798660571244)) in
    let temp_9913 : int64 :=
      (secret (@repr U64 17016134625831438906)) in
    let temp_9915 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9903;
          temp_9905;
          temp_9907;
          temp_9909;
          temp_9911;
          temp_9913
        ]) in
    (temp_9915)).

Definition g1_xden_k_7_v : (arr_fp_t) :=
  (let temp_9917 : int64 :=
      (secret (@repr U64 1488347500898461874)) in
    let temp_9919 : int64 :=
      (secret (@repr U64 3509418672874520985)) in
    let temp_9921 : int64 :=
      (secret (@repr U64 7962192351555381416)) in
    let temp_9923 : int64 :=
      (secret (@repr U64 1843909372225399896)) in
    let temp_9925 : int64 :=
      (secret (@repr U64 1127511003250156243)) in
    let temp_9927 : int64 :=
      (secret (@repr U64 1294742680819751518)) in
    let temp_9929 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9917;
          temp_9919;
          temp_9921;
          temp_9923;
          temp_9925;
          temp_9927
        ]) in
    (temp_9929)).

Definition g1_xden_k_8_v : (arr_fp_t) :=
  (let temp_9931 : int64 :=
      (secret (@repr U64 725340084226051970)) in
    let temp_9933 : int64 :=
      (secret (@repr U64 6814521545734988748)) in
    let temp_9935 : int64 :=
      (secret (@repr U64 16176803544133875307)) in
    let temp_9937 : int64 :=
      (secret (@repr U64 8363199516777220149)) in
    let temp_9939 : int64 :=
      (secret (@repr U64 252877309218538352)) in
    let temp_9941 : int64 :=
      (secret (@repr U64 5149562959837648449)) in
    let temp_9943 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9931;
          temp_9933;
          temp_9935;
          temp_9937;
          temp_9939;
          temp_9941
        ]) in
    (temp_9943)).

Definition g1_xden_k_9_v : (arr_fp_t) :=
  (let temp_9945 : int64 :=
      (secret (@repr U64 675470927100193492)) in
    let temp_9947 : int64 :=
      (secret (@repr U64 5146891164735334016)) in
    let temp_9949 : int64 :=
      (secret (@repr U64 17762958817130696759)) in
    let temp_9951 : int64 :=
      (secret (@repr U64 8565656522589412373)) in
    let temp_9953 : int64 :=
      (secret (@repr U64 10599026333335446784)) in
    let temp_9955 : int64 :=
      (secret (@repr U64 3270603789344496906)) in
    let temp_9957 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9945;
          temp_9947;
          temp_9949;
          temp_9951;
          temp_9953;
          temp_9955
        ]) in
    (temp_9957)).

Definition g1_ynum_k_0_v : (arr_fp_t) :=
  (let temp_9959 : int64 :=
      (secret (@repr U64 652344406751465184)) in
    let temp_9961 : int64 :=
      (secret (@repr U64 2710356675495255290)) in
    let temp_9963 : int64 :=
      (secret (@repr U64 1273695771440998738)) in
    let temp_9965 : int64 :=
      (secret (@repr U64 3121750372618945491)) in
    let temp_9967 : int64 :=
      (secret (@repr U64 14775319642720936898)) in
    let temp_9969 : int64 :=
      (secret (@repr U64 13733803417833814835)) in
    let temp_9971 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9959;
          temp_9961;
          temp_9963;
          temp_9965;
          temp_9967;
          temp_9969
        ]) in
    (temp_9971)).

Definition g1_ynum_k_1_v : (arr_fp_t) :=
  (let temp_9973 : int64 :=
      (secret (@repr U64 1389807578337138705)) in
    let temp_9975 : int64 :=
      (secret (@repr U64 15352831428748068483)) in
    let temp_9977 : int64 :=
      (secret (@repr U64 1307144967559264317)) in
    let temp_9979 : int64 :=
      (secret (@repr U64 1121505450578652468)) in
    let temp_9981 : int64 :=
      (secret (@repr U64 15475889019760388287)) in
    let temp_9983 : int64 :=
      (secret (@repr U64 16183658160488302230)) in
    let temp_9985 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9973;
          temp_9975;
          temp_9977;
          temp_9979;
          temp_9981;
          temp_9983
        ]) in
    (temp_9985)).

Definition g1_ynum_k_2_v : (arr_fp_t) :=
  (let temp_9987 : int64 :=
      (secret (@repr U64 57553299067792998)) in
    let temp_9989 : int64 :=
      (secret (@repr U64 17628079362768849300)) in
    let temp_9991 : int64 :=
      (secret (@repr U64 2689461337731570914)) in
    let temp_9993 : int64 :=
      (secret (@repr U64 14070580367580990887)) in
    let temp_9995 : int64 :=
      (secret (@repr U64 15162865775551710499)) in
    let temp_9997 : int64 :=
      (secret (@repr U64 13321614990632673782)) in
    let temp_9999 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_9987;
          temp_9989;
          temp_9991;
          temp_9993;
          temp_9995;
          temp_9997
        ]) in
    (temp_9999)).

Definition g1_ynum_k_3_v : (arr_fp_t) :=
  (let temp_10001 : int64 :=
      (secret (@repr U64 141972750621744161)) in
    let temp_10003 : int64 :=
      (secret (@repr U64 8689824239172478807)) in
    let temp_10005 : int64 :=
      (secret (@repr U64 15288216298323671324)) in
    let temp_10007 : int64 :=
      (secret (@repr U64 712874875091754233)) in
    let temp_10009 : int64 :=
      (secret (@repr U64 16014900032503684588)) in
    let temp_10011 : int64 :=
      (secret (@repr U64 11976580453200426187)) in
    let temp_10013 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10001;
          temp_10003;
          temp_10005;
          temp_10007;
          temp_10009;
          temp_10011
        ]) in
    (temp_10013)).

Definition g1_ynum_k_4_v : (arr_fp_t) :=
  (let temp_10015 : int64 :=
      (secret (@repr U64 633886036738506515)) in
    let temp_10017 : int64 :=
      (secret (@repr U64 6678644607214234052)) in
    let temp_10019 : int64 :=
      (secret (@repr U64 1825425679455244472)) in
    let temp_10021 : int64 :=
      (secret (@repr U64 8755912272271186652)) in
    let temp_10023 : int64 :=
      (secret (@repr U64 3379943669301788840)) in
    let temp_10025 : int64 :=
      (secret (@repr U64 4735212769449148123)) in
    let temp_10027 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10015;
          temp_10017;
          temp_10019;
          temp_10021;
          temp_10023;
          temp_10025
        ]) in
    (temp_10027)).

Definition g1_ynum_k_5_v : (arr_fp_t) :=
  (let temp_10029 : int64 :=
      (secret (@repr U64 1612358804494830442)) in
    let temp_10031 : int64 :=
      (secret (@repr U64 2454990789666711200)) in
    let temp_10033 : int64 :=
      (secret (@repr U64 8405916841409361853)) in
    let temp_10035 : int64 :=
      (secret (@repr U64 8525415512662168654)) in
    let temp_10037 : int64 :=
      (secret (@repr U64 2323684950984523890)) in
    let temp_10039 : int64 :=
      (secret (@repr U64 11074978966450447856)) in
    let temp_10041 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10029;
          temp_10031;
          temp_10033;
          temp_10035;
          temp_10037;
          temp_10039
        ]) in
    (temp_10041)).

Definition g1_ynum_k_6_v : (arr_fp_t) :=
  (let temp_10043 : int64 :=
      (secret (@repr U64 336375361001233340)) in
    let temp_10045 : int64 :=
      (secret (@repr U64 12882959944969186108)) in
    let temp_10047 : int64 :=
      (secret (@repr U64 16671121624101127371)) in
    let temp_10049 : int64 :=
      (secret (@repr U64 5922586712221110071)) in
    let temp_10051 : int64 :=
      (secret (@repr U64 5163511947597922654)) in
    let temp_10053 : int64 :=
      (secret (@repr U64 14511152726087948018)) in
    let temp_10055 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10043;
          temp_10045;
          temp_10047;
          temp_10049;
          temp_10051;
          temp_10053
        ]) in
    (temp_10055)).

Definition g1_ynum_k_7_v : (arr_fp_t) :=
  (let temp_10057 : int64 :=
      (secret (@repr U64 686738286210365551)) in
    let temp_10059 : int64 :=
      (secret (@repr U64 16039894141796533876)) in
    let temp_10061 : int64 :=
      (secret (@repr U64 1660145734357211167)) in
    let temp_10063 : int64 :=
      (secret (@repr U64 18231571463891878950)) in
    let temp_10065 : int64 :=
      (secret (@repr U64 4825120264949852469)) in
    let temp_10067 : int64 :=
      (secret (@repr U64 11627815551290637097)) in
    let temp_10069 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10057;
          temp_10059;
          temp_10061;
          temp_10063;
          temp_10065;
          temp_10067
        ]) in
    (temp_10069)).

Definition g1_ynum_k_8_v : (arr_fp_t) :=
  (let temp_10071 : int64 :=
      (secret (@repr U64 719520515476580427)) in
    let temp_10073 : int64 :=
      (secret (@repr U64 16756942182913253819)) in
    let temp_10075 : int64 :=
      (secret (@repr U64 10320769399998235244)) in
    let temp_10077 : int64 :=
      (secret (@repr U64 2200974244968450750)) in
    let temp_10079 : int64 :=
      (secret (@repr U64 7626373186594408355)) in
    let temp_10081 : int64 :=
      (secret (@repr U64 6933025920263103879)) in
    let temp_10083 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10071;
          temp_10073;
          temp_10075;
          temp_10077;
          temp_10079;
          temp_10081
        ]) in
    (temp_10083)).

Definition g1_ynum_k_9_v : (arr_fp_t) :=
  (let temp_10085 : int64 :=
      (secret (@repr U64 1016611174344998325)) in
    let temp_10087 : int64 :=
      (secret (@repr U64 2466492548686891555)) in
    let temp_10089 : int64 :=
      (secret (@repr U64 14135124294293452542)) in
    let temp_10091 : int64 :=
      (secret (@repr U64 475233659467912251)) in
    let temp_10093 : int64 :=
      (secret (@repr U64 11186783513499056751)) in
    let temp_10095 : int64 :=
      (secret (@repr U64 3147922594245844016)) in
    let temp_10097 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10085;
          temp_10087;
          temp_10089;
          temp_10091;
          temp_10093;
          temp_10095
        ]) in
    (temp_10097)).

Definition g1_ynum_k_10_v : (arr_fp_t) :=
  (let temp_10099 : int64 :=
      (secret (@repr U64 1833315000454533566)) in
    let temp_10101 : int64 :=
      (secret (@repr U64 1007974600900082579)) in
    let temp_10103 : int64 :=
      (secret (@repr U64 14785260176242854207)) in
    let temp_10105 : int64 :=
      (secret (@repr U64 15066861003931772432)) in
    let temp_10107 : int64 :=
      (secret (@repr U64 3584647998681889532)) in
    let temp_10109 : int64 :=
      (secret (@repr U64 16722834201330696498)) in
    let temp_10111 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10099;
          temp_10101;
          temp_10103;
          temp_10105;
          temp_10107;
          temp_10109
        ]) in
    (temp_10111)).

Definition g1_ynum_k_11_v : (arr_fp_t) :=
  (let temp_10113 : int64 :=
      (secret (@repr U64 1780164921828767454)) in
    let temp_10115 : int64 :=
      (secret (@repr U64 13337622794239929804)) in
    let temp_10117 : int64 :=
      (secret (@repr U64 5923739534552515142)) in
    let temp_10119 : int64 :=
      (secret (@repr U64 3345046972101780530)) in
    let temp_10121 : int64 :=
      (secret (@repr U64 5321510883028162054)) in
    let temp_10123 : int64 :=
      (secret (@repr U64 14846055306840460686)) in
    let temp_10125 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10113;
          temp_10115;
          temp_10117;
          temp_10119;
          temp_10121;
          temp_10123
        ]) in
    (temp_10125)).

Definition g1_ynum_k_12_v : (arr_fp_t) :=
  (let temp_10127 : int64 :=
      (secret (@repr U64 799438051374502809)) in
    let temp_10129 : int64 :=
      (secret (@repr U64 15083972834952036164)) in
    let temp_10131 : int64 :=
      (secret (@repr U64 8838227588559581326)) in
    let temp_10133 : int64 :=
      (secret (@repr U64 13846054168121598783)) in
    let temp_10135 : int64 :=
      (secret (@repr U64 488730451382505970)) in
    let temp_10137 : int64 :=
      (secret (@repr U64 958146249756188408)) in
    let temp_10139 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10127;
          temp_10129;
          temp_10131;
          temp_10133;
          temp_10135;
          temp_10137
        ]) in
    (temp_10139)).

Definition g1_ynum_k_13_v : (arr_fp_t) :=
  (let temp_10141 : int64 :=
      (secret (@repr U64 163716820423854747)) in
    let temp_10143 : int64 :=
      (secret (@repr U64 8285498163857659356)) in
    let temp_10145 : int64 :=
      (secret (@repr U64 8465424830341846400)) in
    let temp_10147 : int64 :=
      (secret (@repr U64 1433942577299613084)) in
    let temp_10149 : int64 :=
      (secret (@repr U64 14325828012864645732)) in
    let temp_10151 : int64 :=
      (secret (@repr U64 4817114329354076467)) in
    let temp_10153 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10141;
          temp_10143;
          temp_10145;
          temp_10147;
          temp_10149;
          temp_10151
        ]) in
    (temp_10153)).

Definition g1_ynum_k_14_v : (arr_fp_t) :=
  (let temp_10155 : int64 :=
      (secret (@repr U64 414658151749832465)) in
    let temp_10157 : int64 :=
      (secret (@repr U64 189531577938912252)) in
    let temp_10159 : int64 :=
      (secret (@repr U64 6802473390048830824)) in
    let temp_10161 : int64 :=
      (secret (@repr U64 15684647020317539556)) in
    let temp_10163 : int64 :=
      (secret (@repr U64 7755485098777620407)) in
    let temp_10165 : int64 :=
      (secret (@repr U64 9685868895687483979)) in
    let temp_10167 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10155;
          temp_10157;
          temp_10159;
          temp_10161;
          temp_10163;
          temp_10165
        ]) in
    (temp_10167)).

Definition g1_ynum_k_15_v : (arr_fp_t) :=
  (let temp_10169 : int64 :=
      (secret (@repr U64 1578157964224562126)) in
    let temp_10171 : int64 :=
      (secret (@repr U64 5666948055268535989)) in
    let temp_10173 : int64 :=
      (secret (@repr U64 14634479491382401593)) in
    let temp_10175 : int64 :=
      (secret (@repr U64 6317940024988860850)) in
    let temp_10177 : int64 :=
      (secret (@repr U64 13142913832013798519)) in
    let temp_10179 : int64 :=
      (secret (@repr U64 338991247778166276)) in
    let temp_10181 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10169;
          temp_10171;
          temp_10173;
          temp_10175;
          temp_10177;
          temp_10179
        ]) in
    (temp_10181)).

Definition g1_yden_k_0_v : (arr_fp_t) :=
  (let temp_10183 : int64 :=
      (secret (@repr U64 1590100849350973618)) in
    let temp_10185 : int64 :=
      (secret (@repr U64 5915497081334721257)) in
    let temp_10187 : int64 :=
      (secret (@repr U64 6924968209373727718)) in
    let temp_10189 : int64 :=
      (secret (@repr U64 17204633670617869946)) in
    let temp_10191 : int64 :=
      (secret (@repr U64 572916540828819565)) in
    let temp_10193 : int64 :=
      (secret (@repr U64 92203205520679873)) in
    let temp_10195 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10183;
          temp_10185;
          temp_10187;
          temp_10189;
          temp_10191;
          temp_10193
        ]) in
    (temp_10195)).

Definition g1_yden_k_1_v : (arr_fp_t) :=
  (let temp_10197 : int64 :=
      (secret (@repr U64 1829261189398470686)) in
    let temp_10199 : int64 :=
      (secret (@repr U64 1877083417397643448)) in
    let temp_10201 : int64 :=
      (secret (@repr U64 9640042925497046428)) in
    let temp_10203 : int64 :=
      (secret (@repr U64 11862766565471805471)) in
    let temp_10205 : int64 :=
      (secret (@repr U64 8693114993904885301)) in
    let temp_10207 : int64 :=
      (secret (@repr U64 3672140328108400701)) in
    let temp_10209 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10197;
          temp_10199;
          temp_10201;
          temp_10203;
          temp_10205;
          temp_10207
        ]) in
    (temp_10209)).

Definition g1_yden_k_2_v : (arr_fp_t) :=
  (let temp_10211 : int64 :=
      (secret (@repr U64 400243331105348135)) in
    let temp_10213 : int64 :=
      (secret (@repr U64 8046435537999802711)) in
    let temp_10215 : int64 :=
      (secret (@repr U64 8702226981475745585)) in
    let temp_10217 : int64 :=
      (secret (@repr U64 879791671491744492)) in
    let temp_10219 : int64 :=
      (secret (@repr U64 11994630442058346377)) in
    let temp_10221 : int64 :=
      (secret (@repr U64 2172204746352322546)) in
    let temp_10223 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10211;
          temp_10213;
          temp_10215;
          temp_10217;
          temp_10219;
          temp_10221
        ]) in
    (temp_10223)).

Definition g1_yden_k_3_v : (arr_fp_t) :=
  (let temp_10225 : int64 :=
      (secret (@repr U64 1637008473169220501)) in
    let temp_10227 : int64 :=
      (secret (@repr U64 17441636237435581649)) in
    let temp_10229 : int64 :=
      (secret (@repr U64 15066165676546511630)) in
    let temp_10231 : int64 :=
      (secret (@repr U64 1314387578457599809)) in
    let temp_10233 : int64 :=
      (secret (@repr U64 8247046336453711789)) in
    let temp_10235 : int64 :=
      (secret (@repr U64 12164906044230685718)) in
    let temp_10237 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10225;
          temp_10227;
          temp_10229;
          temp_10231;
          temp_10233;
          temp_10235
        ]) in
    (temp_10237)).

Definition g1_yden_k_4_v : (arr_fp_t) :=
  (let temp_10239 : int64 :=
      (secret (@repr U64 855930740911588324)) in
    let temp_10241 : int64 :=
      (secret (@repr U64 12685735333705453020)) in
    let temp_10243 : int64 :=
      (secret (@repr U64 14326404096614579120)) in
    let temp_10245 : int64 :=
      (secret (@repr U64 6066025509460822294)) in
    let temp_10247 : int64 :=
      (secret (@repr U64 11676450493790612973)) in
    let temp_10249 : int64 :=
      (secret (@repr U64 15724621714793234461)) in
    let temp_10251 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10239;
          temp_10241;
          temp_10243;
          temp_10245;
          temp_10247;
          temp_10249
        ]) in
    (temp_10251)).

Definition g1_yden_k_5_v : (arr_fp_t) :=
  (let temp_10253 : int64 :=
      (secret (@repr U64 637792788410719021)) in
    let temp_10255 : int64 :=
      (secret (@repr U64 11507373155986977154)) in
    let temp_10257 : int64 :=
      (secret (@repr U64 13186912195705886849)) in
    let temp_10259 : int64 :=
      (secret (@repr U64 14262012144631372388)) in
    let temp_10261 : int64 :=
      (secret (@repr U64 5328758613570342114)) in
    let temp_10263 : int64 :=
      (secret (@repr U64 199925847119476652)) in
    let temp_10265 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10253;
          temp_10255;
          temp_10257;
          temp_10259;
          temp_10261;
          temp_10263
        ]) in
    (temp_10265)).

Definition g1_yden_k_6_v : (arr_fp_t) :=
  (let temp_10267 : int64 :=
      (secret (@repr U64 1612297190139091759)) in
    let temp_10269 : int64 :=
      (secret (@repr U64 14103733843373163083)) in
    let temp_10271 : int64 :=
      (secret (@repr U64 6840121186619029743)) in
    let temp_10273 : int64 :=
      (secret (@repr U64 6760859324815900753)) in
    let temp_10275 : int64 :=
      (secret (@repr U64 15418807805142572985)) in
    let temp_10277 : int64 :=
      (secret (@repr U64 4402853133867972444)) in
    let temp_10279 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10267;
          temp_10269;
          temp_10271;
          temp_10273;
          temp_10275;
          temp_10277
        ]) in
    (temp_10279)).

Definition g1_yden_k_7_v : (arr_fp_t) :=
  (let temp_10281 : int64 :=
      (secret (@repr U64 1631410310868805610)) in
    let temp_10283 : int64 :=
      (secret (@repr U64 269334146695233390)) in
    let temp_10285 : int64 :=
      (secret (@repr U64 16547411811928854487)) in
    let temp_10287 : int64 :=
      (secret (@repr U64 18353100669930795314)) in
    let temp_10289 : int64 :=
      (secret (@repr U64 13339932232668798692)) in
    let temp_10291 : int64 :=
      (secret (@repr U64 6984591927261867737)) in
    let temp_10293 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10281;
          temp_10283;
          temp_10285;
          temp_10287;
          temp_10289;
          temp_10291
        ]) in
    (temp_10293)).

Definition g1_yden_k_8_v : (arr_fp_t) :=
  (let temp_10295 : int64 :=
      (secret (@repr U64 1758313625630302499)) in
    let temp_10297 : int64 :=
      (secret (@repr U64 1881349400343039172)) in
    let temp_10299 : int64 :=
      (secret (@repr U64 18013005311323887904)) in
    let temp_10301 : int64 :=
      (secret (@repr U64 12377427846571989832)) in
    let temp_10303 : int64 :=
      (secret (@repr U64 5967237584920922243)) in
    let temp_10305 : int64 :=
      (secret (@repr U64 7720081932193848650)) in
    let temp_10307 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10295;
          temp_10297;
          temp_10299;
          temp_10301;
          temp_10303;
          temp_10305
        ]) in
    (temp_10307)).

Definition g1_yden_k_9_v : (arr_fp_t) :=
  (let temp_10309 : int64 :=
      (secret (@repr U64 1619701357752249884)) in
    let temp_10311 : int64 :=
      (secret (@repr U64 16898074901591262352)) in
    let temp_10313 : int64 :=
      (secret (@repr U64 3609344159736760251)) in
    let temp_10315 : int64 :=
      (secret (@repr U64 5983130161189999867)) in
    let temp_10317 : int64 :=
      (secret (@repr U64 14355327869992416094)) in
    let temp_10319 : int64 :=
      (secret (@repr U64 3778226018344582997)) in
    let temp_10321 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10309;
          temp_10311;
          temp_10313;
          temp_10315;
          temp_10317;
          temp_10319
        ]) in
    (temp_10321)).

Definition g1_yden_k_10_v : (arr_fp_t) :=
  (let temp_10323 : int64 :=
      (secret (@repr U64 347606589330687421)) in
    let temp_10325 : int64 :=
      (secret (@repr U64 5255719044972187933)) in
    let temp_10327 : int64 :=
      (secret (@repr U64 11271894388753671721)) in
    let temp_10329 : int64 :=
      (secret (@repr U64 1033887512062764488)) in
    let temp_10331 : int64 :=
      (secret (@repr U64 8189165486932690436)) in
    let temp_10333 : int64 :=
      (secret (@repr U64 70004379462101672)) in
    let temp_10335 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10323;
          temp_10325;
          temp_10327;
          temp_10329;
          temp_10331;
          temp_10333
        ]) in
    (temp_10335)).

Definition g1_yden_k_11_v : (arr_fp_t) :=
  (let temp_10337 : int64 :=
      (secret (@repr U64 778202887894139711)) in
    let temp_10339 : int64 :=
      (secret (@repr U64 17691595219776375879)) in
    let temp_10341 : int64 :=
      (secret (@repr U64 9193253711563866834)) in
    let temp_10343 : int64 :=
      (secret (@repr U64 10092455202333888821)) in
    let temp_10345 : int64 :=
      (secret (@repr U64 1655469341950262250)) in
    let temp_10347 : int64 :=
      (secret (@repr U64 10845992994110574738)) in
    let temp_10349 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10337;
          temp_10339;
          temp_10341;
          temp_10343;
          temp_10345;
          temp_10347
        ]) in
    (temp_10349)).

Definition g1_yden_k_12_v : (arr_fp_t) :=
  (let temp_10351 : int64 :=
      (secret (@repr U64 781015344221683683)) in
    let temp_10353 : int64 :=
      (secret (@repr U64 14078588081290548374)) in
    let temp_10355 : int64 :=
      (secret (@repr U64 6067271023149908518)) in
    let temp_10357 : int64 :=
      (secret (@repr U64 9033357708497886086)) in
    let temp_10359 : int64 :=
      (secret (@repr U64 10592474449179118273)) in
    let temp_10361 : int64 :=
      (secret (@repr U64 2204988348113831372)) in
    let temp_10363 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10351;
          temp_10353;
          temp_10355;
          temp_10357;
          temp_10359;
          temp_10361
        ]) in
    (temp_10363)).

Definition g1_yden_k_13_v : (arr_fp_t) :=
  (let temp_10365 : int64 :=
      (secret (@repr U64 172830037692534587)) in
    let temp_10367 : int64 :=
      (secret (@repr U64 7101012286790006514)) in
    let temp_10369 : int64 :=
      (secret (@repr U64 13787308004332873665)) in
    let temp_10371 : int64 :=
      (secret (@repr U64 14660498759553796110)) in
    let temp_10373 : int64 :=
      (secret (@repr U64 4757234684169342080)) in
    let temp_10375 : int64 :=
      (secret (@repr U64 15130647872920159991)) in
    let temp_10377 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10365;
          temp_10367;
          temp_10369;
          temp_10371;
          temp_10373;
          temp_10375
        ]) in
    (temp_10377)).

Definition g1_yden_k_14_v : (arr_fp_t) :=
  (let temp_10379 : int64 :=
      (secret (@repr U64 1013206390650290238)) in
    let temp_10381 : int64 :=
      (secret (@repr U64 7720336747103001025)) in
    let temp_10383 : int64 :=
      (secret (@repr U64 8197694151986493523)) in
    let temp_10385 : int64 :=
      (secret (@repr U64 3625112747029342752)) in
    let temp_10387 : int64 :=
      (secret (@repr U64 6675167463148394368)) in
    let temp_10389 : int64 :=
      (secret (@repr U64 4905905684016745359)) in
    let temp_10391 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10379;
          temp_10381;
          temp_10383;
          temp_10385;
          temp_10387;
          temp_10389
        ]) in
    (temp_10391)).

Definition x1_10445_loc : ChoiceEqualityLocation :=
  ((fp_t ; 10491%nat)).
Definition y_10479_loc : ChoiceEqualityLocation :=
  ((fp_t ; 10492%nat)).
Notation "'g1_simple_swu_iso_inp'" := (
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_simple_swu_iso_out'" := ((fp_t '× fp_t
  ) : choice_type) (in custom pack_type at level 2).
Definition G1_SIMPLE_SWU_ISO : nat :=
  (10493).
Program Definition g1_simple_swu_iso
   : package (CEfset ([x1_10445_loc ; y_10479_loc])) [interface
  #val #[ FP_IS_SQUARE ] : fp_is_square_inp → fp_is_square_out ;
  #val #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out ;
  #val #[ FP_SQRT ] : fp_sqrt_inp → fp_sqrt_out ] [interface
  #val #[ G1_SIMPLE_SWU_ISO ] : g1_simple_swu_iso_inp → g1_simple_swu_iso_out
  ] :=
  (
    [package #def #[ G1_SIMPLE_SWU_ISO ] (temp_inp : g1_simple_swu_iso_inp) : g1_simple_swu_iso_out { 
    let '(u_10405) := temp_inp : fp_t in
    #import {sig #[ FP_IS_SQUARE ] : fp_is_square_inp → fp_is_square_out } as fp_is_square ;;
    let fp_is_square := fun x_0 => fp_is_square (x_0) in
    #import {sig #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out } as fp_sgn0 ;;
    let fp_sgn0 := fun x_0 => fp_sgn0 (x_0) in
    #import {sig #[ FP_SQRT ] : fp_sqrt_inp → fp_sqrt_out } as fp_sqrt ;;
    let fp_sqrt := fun x_0 => fp_sqrt (x_0) in
    ({ code  '(z_10402 : fp_t) ←
        ( '(temp_10393 : fp_t) ←
            (nat_mod_from_literal (_) (@repr U128 11)) ;;
          ret (temp_10393)) ;;
       '(a_10423 : fp_t) ←
        ( '(temp_10395 : seq int8) ←
            (array_to_be_bytes (g1_iso_a_v)) ;;
           '(temp_10397 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10395)) ;;
          ret (temp_10397)) ;;
       '(b_10420 : fp_t) ←
        ( '(temp_10399 : seq int8) ←
            (array_to_be_bytes (g1_iso_b_v)) ;;
           '(temp_10401 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10399)) ;;
          ret (temp_10401)) ;;
       '(tv1_10430 : fp_t) ←
        ( '(temp_10404 : fp_t) ←
            ((z_10402) *% (z_10402)) ;;
           temp_10407 ←
            (nat_mod_exp (u_10405) (@repr U32 4)) ;;
           '(temp_10409 : fp_t) ←
            ((temp_10404) *% (temp_10407)) ;;
           '(temp_10411 : fp_t) ←
            ((z_10402) *% (u_10405)) ;;
           '(temp_10413 : fp_t) ←
            ((temp_10411) *% (u_10405)) ;;
           '(temp_10415 : fp_t) ←
            ((temp_10409) +% (temp_10413)) ;;
           temp_10417 ←
            (nat_mod_inv (temp_10415)) ;;
          ret (temp_10417)) ;;
       '(x1_10445 : fp_t) ←
          ( '(temp_10419 : fp_t) ←
              (nat_mod_zero ) ;;
             '(temp_10422 : fp_t) ←
              ((temp_10419) -% (b_10420)) ;;
             temp_10425 ←
              (nat_mod_inv (a_10423)) ;;
             '(temp_10427 : fp_t) ←
              ((temp_10422) *% (temp_10425)) ;;
             '(temp_10429 : fp_t) ←
              (nat_mod_one ) ;;
             '(temp_10432 : fp_t) ←
              ((temp_10429) +% (tv1_10430)) ;;
             '(temp_10434 : fp_t) ←
              ((temp_10427) *% (temp_10432)) ;;
            ret (temp_10434)) ;;
        #put x1_10445_loc := x1_10445 ;;
       '(temp_10436 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_10438 : bool_ChoiceEquality) ←
        ((tv1_10430) =.? (temp_10436)) ;;
       '(x1_10445 : (fp_t)) ←
        (if temp_10438:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(x1_10445 : fp_t) ←
                (( '(temp_10440 : fp_t) ←
                      ((z_10402) *% (a_10423)) ;;
                     temp_10442 ←
                      (nat_mod_inv (temp_10440)) ;;
                     '(temp_10444 : fp_t) ←
                      ((b_10420) *% (temp_10442)) ;;
                    ret (temp_10444))) ;;
              #put x1_10445_loc := x1_10445 ;;
            
            @ret ((fp_t)) (x1_10445) in
            ({ code temp_then } : code (CEfset ([x1_10445_loc])) [interface] _))
          else @ret ((fp_t)) (x1_10445)) ;;
      
       '(gx1_10469 : fp_t) ←
        ( temp_10447 ←
            (nat_mod_exp (x1_10445) (@repr U32 3)) ;;
           '(temp_10449 : fp_t) ←
            ((a_10423) *% (x1_10445)) ;;
           '(temp_10451 : fp_t) ←
            ((temp_10447) +% (temp_10449)) ;;
           '(temp_10453 : fp_t) ←
            ((temp_10451) +% (b_10420)) ;;
          ret (temp_10453)) ;;
       '(x2_10460 : fp_t) ←
        ( '(temp_10455 : fp_t) ←
            ((z_10402) *% (u_10405)) ;;
           '(temp_10457 : fp_t) ←
            ((temp_10455) *% (u_10405)) ;;
           '(temp_10459 : fp_t) ←
            ((temp_10457) *% (x1_10445)) ;;
          ret (temp_10459)) ;;
       '(gx2_10474 : fp_t) ←
        ( temp_10462 ←
            (nat_mod_exp (x2_10460) (@repr U32 3)) ;;
           '(temp_10464 : fp_t) ←
            ((a_10423) *% (x2_10460)) ;;
           '(temp_10466 : fp_t) ←
            ((temp_10462) +% (temp_10464)) ;;
           '(temp_10468 : fp_t) ←
            ((temp_10466) +% (b_10420)) ;;
          ret (temp_10468)) ;;
       temp_10490 ←
        ( '(temp_10471 : bool_ChoiceEquality) ←
            (fp_is_square (gx1_10469)) ;;
           '(temp_10473 : fp_t) ←
            (fp_sqrt (gx1_10469)) ;;
           '(temp_10476 : fp_t) ←
            (fp_sqrt (gx2_10474)) ;;
          ret ((if (temp_10471):bool_ChoiceEquality then (*inline*) (prod_ce(
                  x1_10445,
                  temp_10473
                )) else (prod_ce(x2_10460, temp_10476))))) ;;
      let '(x_10488, y_10479) :=
        (temp_10490) : (fp_t '× fp_t) in
       '(temp_10478 : bool_ChoiceEquality) ←
        (fp_sgn0 (u_10405)) ;;
       '(temp_10481 : bool_ChoiceEquality) ←
        (fp_sgn0 (y_10479)) ;;
       '(temp_10483 : bool_ChoiceEquality) ←
        ((temp_10478) !=.? (temp_10481)) ;;
       '(y_10479 : (fp_t)) ←
        (if temp_10483:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(y_10479 : fp_t) ←
                (( '(temp_10485 : fp_t) ←
                      (nat_mod_zero ) ;;
                     '(temp_10487 : fp_t) ←
                      ((temp_10485) -% (y_10479)) ;;
                    ret (temp_10487))) ;;
              #put y_10479_loc := y_10479 ;;
            
            @ret ((fp_t)) (y_10479) in
            ({ code temp_then } : code (CEfset (
                  [x1_10445_loc ; y_10479_loc])) [interface] _))
          else @ret ((fp_t)) (y_10479)) ;;
      
      @ret ((fp_t '× fp_t)) (prod_ce(x_10488, y_10479)) } : code (CEfset (
          [x1_10445_loc ; y_10479_loc])) [interface
      #val #[ FP_IS_SQUARE ] : fp_is_square_inp → fp_is_square_out ;
      #val #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out ;
      #val #[ FP_SQRT ] : fp_sqrt_inp → fp_sqrt_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_g1_simple_swu_iso : package _ _ _ :=
  (seq_link g1_simple_swu_iso link_rest(
      package_fp_is_square,package_fp_sgn0,package_fp_sqrt)).
Fail Next Obligation.

Definition ynum_10761_loc : ChoiceEqualityLocation :=
  ((fp_t ; 10823%nat)).
Definition xden_k_10733_loc : ChoiceEqualityLocation :=
  ((seq fp_t ; 10824%nat)).
Definition ynum_k_10734_loc : ChoiceEqualityLocation :=
  ((seq fp_t ; 10825%nat)).
Definition inf_10812_loc : ChoiceEqualityLocation :=
  ((bool_ChoiceEquality ; 10826%nat)).
Definition xx_10779_loc : ChoiceEqualityLocation :=
  ((fp_t ; 10827%nat)).
Definition xx_10722_loc : ChoiceEqualityLocation :=
  ((fp_t ; 10828%nat)).
Definition xnum_k_10718_loc : ChoiceEqualityLocation :=
  ((seq fp_t ; 10829%nat)).
Definition yden_k_10735_loc : ChoiceEqualityLocation :=
  ((seq fp_t ; 10830%nat)).
Definition xx_10743_loc : ChoiceEqualityLocation :=
  ((fp_t ; 10831%nat)).
Definition xnum_10721_loc : ChoiceEqualityLocation :=
  ((fp_t ; 10832%nat)).
Definition yden_10778_loc : ChoiceEqualityLocation :=
  ((fp_t ; 10833%nat)).
Definition xden_10742_loc : ChoiceEqualityLocation :=
  ((fp_t ; 10834%nat)).
Definition xx_10762_loc : ChoiceEqualityLocation :=
  ((fp_t ; 10835%nat)).
Notation "'g1_isogeny_map_inp'" := (
  fp_t '× fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_isogeny_map_out'" := (
  g1_t : choice_type) (in custom pack_type at level 2).
Definition G1_ISOGENY_MAP : nat :=
  (10836).
Program Definition g1_isogeny_map
   : package (CEfset (
      [xnum_k_10718_loc ; xden_k_10733_loc ; ynum_k_10734_loc ; yden_k_10735_loc ; xnum_10721_loc ; xx_10722_loc ; xden_10742_loc ; xx_10743_loc ; ynum_10761_loc ; xx_10762_loc ; yden_10778_loc ; xx_10779_loc ; inf_10812_loc])) [interface] [interface
  #val #[ G1_ISOGENY_MAP ] : g1_isogeny_map_inp → g1_isogeny_map_out ] :=
  (
    [package #def #[ G1_ISOGENY_MAP ] (temp_inp : g1_isogeny_map_inp) : g1_isogeny_map_out { 
    let '(x_10730 , y_10795) := temp_inp : fp_t '× fp_t in
    ({ code  '(xnum_k_10718 : seq fp_t) ←
          ( temp_10495 ←
              (seq_new_ (default : fp_t) (usize 12)) ;;
            ret (temp_10495)) ;;
        #put xnum_k_10718_loc := xnum_k_10718 ;;
       '(xnum_k_10718 : seq fp_t) ←
        ( '(temp_10497 : seq int8) ←
            (array_to_be_bytes (g1_xnum_k_0_v)) ;;
           '(temp_10499 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10497)) ;;
          ret (seq_upd xnum_k_10718 (usize 0) (temp_10499))) ;;
      
       '(xnum_k_10718 : seq fp_t) ←
        ( '(temp_10501 : seq int8) ←
            (array_to_be_bytes (g1_xnum_k_1_v)) ;;
           '(temp_10503 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10501)) ;;
          ret (seq_upd xnum_k_10718 (usize 1) (temp_10503))) ;;
      
       '(xnum_k_10718 : seq fp_t) ←
        ( '(temp_10505 : seq int8) ←
            (array_to_be_bytes (g1_xnum_k_2_v)) ;;
           '(temp_10507 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10505)) ;;
          ret (seq_upd xnum_k_10718 (usize 2) (temp_10507))) ;;
      
       '(xnum_k_10718 : seq fp_t) ←
        ( '(temp_10509 : seq int8) ←
            (array_to_be_bytes (g1_xnum_k_3_v)) ;;
           '(temp_10511 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10509)) ;;
          ret (seq_upd xnum_k_10718 (usize 3) (temp_10511))) ;;
      
       '(xnum_k_10718 : seq fp_t) ←
        ( '(temp_10513 : seq int8) ←
            (array_to_be_bytes (g1_xnum_k_4_v)) ;;
           '(temp_10515 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10513)) ;;
          ret (seq_upd xnum_k_10718 (usize 4) (temp_10515))) ;;
      
       '(xnum_k_10718 : seq fp_t) ←
        ( '(temp_10517 : seq int8) ←
            (array_to_be_bytes (g1_xnum_k_5_v)) ;;
           '(temp_10519 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10517)) ;;
          ret (seq_upd xnum_k_10718 (usize 5) (temp_10519))) ;;
      
       '(xnum_k_10718 : seq fp_t) ←
        ( '(temp_10521 : seq int8) ←
            (array_to_be_bytes (g1_xnum_k_6_v)) ;;
           '(temp_10523 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10521)) ;;
          ret (seq_upd xnum_k_10718 (usize 6) (temp_10523))) ;;
      
       '(xnum_k_10718 : seq fp_t) ←
        ( '(temp_10525 : seq int8) ←
            (array_to_be_bytes (g1_xnum_k_7_v)) ;;
           '(temp_10527 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10525)) ;;
          ret (seq_upd xnum_k_10718 (usize 7) (temp_10527))) ;;
      
       '(xnum_k_10718 : seq fp_t) ←
        ( '(temp_10529 : seq int8) ←
            (array_to_be_bytes (g1_xnum_k_8_v)) ;;
           '(temp_10531 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10529)) ;;
          ret (seq_upd xnum_k_10718 (usize 8) (temp_10531))) ;;
      
       '(xnum_k_10718 : seq fp_t) ←
        ( '(temp_10533 : seq int8) ←
            (array_to_be_bytes (g1_xnum_k_9_v)) ;;
           '(temp_10535 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10533)) ;;
          ret (seq_upd xnum_k_10718 (usize 9) (temp_10535))) ;;
      
       '(xnum_k_10718 : seq fp_t) ←
        ( '(temp_10537 : seq int8) ←
            (array_to_be_bytes (g1_xnum_k_10_v)) ;;
           '(temp_10539 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10537)) ;;
          ret (seq_upd xnum_k_10718 (usize 10) (temp_10539))) ;;
      
       '(xnum_k_10718 : seq fp_t) ←
        ( '(temp_10541 : seq int8) ←
            (array_to_be_bytes (g1_xnum_k_11_v)) ;;
           '(temp_10543 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10541)) ;;
          ret (seq_upd xnum_k_10718 (usize 11) (temp_10543))) ;;
      
       '(xden_k_10733 : seq fp_t) ←
          ( temp_10545 ←
              (seq_new_ (default : fp_t) (usize 10)) ;;
            ret (temp_10545)) ;;
        #put xden_k_10733_loc := xden_k_10733 ;;
       '(xden_k_10733 : seq fp_t) ←
        ( '(temp_10547 : seq int8) ←
            (array_to_be_bytes (g1_xden_k_0_v)) ;;
           '(temp_10549 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10547)) ;;
          ret (seq_upd xden_k_10733 (usize 0) (temp_10549))) ;;
      
       '(xden_k_10733 : seq fp_t) ←
        ( '(temp_10551 : seq int8) ←
            (array_to_be_bytes (g1_xden_k_1_v)) ;;
           '(temp_10553 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10551)) ;;
          ret (seq_upd xden_k_10733 (usize 1) (temp_10553))) ;;
      
       '(xden_k_10733 : seq fp_t) ←
        ( '(temp_10555 : seq int8) ←
            (array_to_be_bytes (g1_xden_k_2_v)) ;;
           '(temp_10557 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10555)) ;;
          ret (seq_upd xden_k_10733 (usize 2) (temp_10557))) ;;
      
       '(xden_k_10733 : seq fp_t) ←
        ( '(temp_10559 : seq int8) ←
            (array_to_be_bytes (g1_xden_k_3_v)) ;;
           '(temp_10561 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10559)) ;;
          ret (seq_upd xden_k_10733 (usize 3) (temp_10561))) ;;
      
       '(xden_k_10733 : seq fp_t) ←
        ( '(temp_10563 : seq int8) ←
            (array_to_be_bytes (g1_xden_k_4_v)) ;;
           '(temp_10565 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10563)) ;;
          ret (seq_upd xden_k_10733 (usize 4) (temp_10565))) ;;
      
       '(xden_k_10733 : seq fp_t) ←
        ( '(temp_10567 : seq int8) ←
            (array_to_be_bytes (g1_xden_k_5_v)) ;;
           '(temp_10569 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10567)) ;;
          ret (seq_upd xden_k_10733 (usize 5) (temp_10569))) ;;
      
       '(xden_k_10733 : seq fp_t) ←
        ( '(temp_10571 : seq int8) ←
            (array_to_be_bytes (g1_xden_k_6_v)) ;;
           '(temp_10573 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10571)) ;;
          ret (seq_upd xden_k_10733 (usize 6) (temp_10573))) ;;
      
       '(xden_k_10733 : seq fp_t) ←
        ( '(temp_10575 : seq int8) ←
            (array_to_be_bytes (g1_xden_k_7_v)) ;;
           '(temp_10577 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10575)) ;;
          ret (seq_upd xden_k_10733 (usize 7) (temp_10577))) ;;
      
       '(xden_k_10733 : seq fp_t) ←
        ( '(temp_10579 : seq int8) ←
            (array_to_be_bytes (g1_xden_k_8_v)) ;;
           '(temp_10581 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10579)) ;;
          ret (seq_upd xden_k_10733 (usize 8) (temp_10581))) ;;
      
       '(xden_k_10733 : seq fp_t) ←
        ( '(temp_10583 : seq int8) ←
            (array_to_be_bytes (g1_xden_k_9_v)) ;;
           '(temp_10585 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10583)) ;;
          ret (seq_upd xden_k_10733 (usize 9) (temp_10585))) ;;
      
       '(ynum_k_10734 : seq fp_t) ←
          ( temp_10587 ←
              (seq_new_ (default : fp_t) (usize 16)) ;;
            ret (temp_10587)) ;;
        #put ynum_k_10734_loc := ynum_k_10734 ;;
       '(ynum_k_10734 : seq fp_t) ←
        ( '(temp_10589 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_0_v)) ;;
           '(temp_10591 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10589)) ;;
          ret (seq_upd ynum_k_10734 (usize 0) (temp_10591))) ;;
      
       '(ynum_k_10734 : seq fp_t) ←
        ( '(temp_10593 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_1_v)) ;;
           '(temp_10595 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10593)) ;;
          ret (seq_upd ynum_k_10734 (usize 1) (temp_10595))) ;;
      
       '(ynum_k_10734 : seq fp_t) ←
        ( '(temp_10597 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_2_v)) ;;
           '(temp_10599 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10597)) ;;
          ret (seq_upd ynum_k_10734 (usize 2) (temp_10599))) ;;
      
       '(ynum_k_10734 : seq fp_t) ←
        ( '(temp_10601 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_3_v)) ;;
           '(temp_10603 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10601)) ;;
          ret (seq_upd ynum_k_10734 (usize 3) (temp_10603))) ;;
      
       '(ynum_k_10734 : seq fp_t) ←
        ( '(temp_10605 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_4_v)) ;;
           '(temp_10607 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10605)) ;;
          ret (seq_upd ynum_k_10734 (usize 4) (temp_10607))) ;;
      
       '(ynum_k_10734 : seq fp_t) ←
        ( '(temp_10609 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_5_v)) ;;
           '(temp_10611 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10609)) ;;
          ret (seq_upd ynum_k_10734 (usize 5) (temp_10611))) ;;
      
       '(ynum_k_10734 : seq fp_t) ←
        ( '(temp_10613 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_6_v)) ;;
           '(temp_10615 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10613)) ;;
          ret (seq_upd ynum_k_10734 (usize 6) (temp_10615))) ;;
      
       '(ynum_k_10734 : seq fp_t) ←
        ( '(temp_10617 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_7_v)) ;;
           '(temp_10619 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10617)) ;;
          ret (seq_upd ynum_k_10734 (usize 7) (temp_10619))) ;;
      
       '(ynum_k_10734 : seq fp_t) ←
        ( '(temp_10621 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_8_v)) ;;
           '(temp_10623 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10621)) ;;
          ret (seq_upd ynum_k_10734 (usize 8) (temp_10623))) ;;
      
       '(ynum_k_10734 : seq fp_t) ←
        ( '(temp_10625 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_9_v)) ;;
           '(temp_10627 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10625)) ;;
          ret (seq_upd ynum_k_10734 (usize 9) (temp_10627))) ;;
      
       '(ynum_k_10734 : seq fp_t) ←
        ( '(temp_10629 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_10_v)) ;;
           '(temp_10631 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10629)) ;;
          ret (seq_upd ynum_k_10734 (usize 10) (temp_10631))) ;;
      
       '(ynum_k_10734 : seq fp_t) ←
        ( '(temp_10633 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_11_v)) ;;
           '(temp_10635 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10633)) ;;
          ret (seq_upd ynum_k_10734 (usize 11) (temp_10635))) ;;
      
       '(ynum_k_10734 : seq fp_t) ←
        ( '(temp_10637 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_12_v)) ;;
           '(temp_10639 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10637)) ;;
          ret (seq_upd ynum_k_10734 (usize 12) (temp_10639))) ;;
      
       '(ynum_k_10734 : seq fp_t) ←
        ( '(temp_10641 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_13_v)) ;;
           '(temp_10643 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10641)) ;;
          ret (seq_upd ynum_k_10734 (usize 13) (temp_10643))) ;;
      
       '(ynum_k_10734 : seq fp_t) ←
        ( '(temp_10645 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_14_v)) ;;
           '(temp_10647 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10645)) ;;
          ret (seq_upd ynum_k_10734 (usize 14) (temp_10647))) ;;
      
       '(ynum_k_10734 : seq fp_t) ←
        ( '(temp_10649 : seq int8) ←
            (array_to_be_bytes (g1_ynum_k_15_v)) ;;
           '(temp_10651 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10649)) ;;
          ret (seq_upd ynum_k_10734 (usize 15) (temp_10651))) ;;
      
       '(yden_k_10735 : seq fp_t) ←
          ( temp_10653 ←
              (seq_new_ (default : fp_t) (usize 15)) ;;
            ret (temp_10653)) ;;
        #put yden_k_10735_loc := yden_k_10735 ;;
       '(yden_k_10735 : seq fp_t) ←
        ( '(temp_10655 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_0_v)) ;;
           '(temp_10657 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10655)) ;;
          ret (seq_upd yden_k_10735 (usize 0) (temp_10657))) ;;
      
       '(yden_k_10735 : seq fp_t) ←
        ( '(temp_10659 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_1_v)) ;;
           '(temp_10661 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10659)) ;;
          ret (seq_upd yden_k_10735 (usize 1) (temp_10661))) ;;
      
       '(yden_k_10735 : seq fp_t) ←
        ( '(temp_10663 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_2_v)) ;;
           '(temp_10665 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10663)) ;;
          ret (seq_upd yden_k_10735 (usize 2) (temp_10665))) ;;
      
       '(yden_k_10735 : seq fp_t) ←
        ( '(temp_10667 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_3_v)) ;;
           '(temp_10669 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10667)) ;;
          ret (seq_upd yden_k_10735 (usize 3) (temp_10669))) ;;
      
       '(yden_k_10735 : seq fp_t) ←
        ( '(temp_10671 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_4_v)) ;;
           '(temp_10673 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10671)) ;;
          ret (seq_upd yden_k_10735 (usize 4) (temp_10673))) ;;
      
       '(yden_k_10735 : seq fp_t) ←
        ( '(temp_10675 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_5_v)) ;;
           '(temp_10677 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10675)) ;;
          ret (seq_upd yden_k_10735 (usize 5) (temp_10677))) ;;
      
       '(yden_k_10735 : seq fp_t) ←
        ( '(temp_10679 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_6_v)) ;;
           '(temp_10681 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10679)) ;;
          ret (seq_upd yden_k_10735 (usize 6) (temp_10681))) ;;
      
       '(yden_k_10735 : seq fp_t) ←
        ( '(temp_10683 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_7_v)) ;;
           '(temp_10685 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10683)) ;;
          ret (seq_upd yden_k_10735 (usize 7) (temp_10685))) ;;
      
       '(yden_k_10735 : seq fp_t) ←
        ( '(temp_10687 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_8_v)) ;;
           '(temp_10689 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10687)) ;;
          ret (seq_upd yden_k_10735 (usize 8) (temp_10689))) ;;
      
       '(yden_k_10735 : seq fp_t) ←
        ( '(temp_10691 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_9_v)) ;;
           '(temp_10693 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10691)) ;;
          ret (seq_upd yden_k_10735 (usize 9) (temp_10693))) ;;
      
       '(yden_k_10735 : seq fp_t) ←
        ( '(temp_10695 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_10_v)) ;;
           '(temp_10697 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10695)) ;;
          ret (seq_upd yden_k_10735 (usize 10) (temp_10697))) ;;
      
       '(yden_k_10735 : seq fp_t) ←
        ( '(temp_10699 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_11_v)) ;;
           '(temp_10701 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10699)) ;;
          ret (seq_upd yden_k_10735 (usize 11) (temp_10701))) ;;
      
       '(yden_k_10735 : seq fp_t) ←
        ( '(temp_10703 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_12_v)) ;;
           '(temp_10705 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10703)) ;;
          ret (seq_upd yden_k_10735 (usize 12) (temp_10705))) ;;
      
       '(yden_k_10735 : seq fp_t) ←
        ( '(temp_10707 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_13_v)) ;;
           '(temp_10709 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10707)) ;;
          ret (seq_upd yden_k_10735 (usize 13) (temp_10709))) ;;
      
       '(yden_k_10735 : seq fp_t) ←
        ( '(temp_10711 : seq int8) ←
            (array_to_be_bytes (g1_yden_k_14_v)) ;;
           '(temp_10713 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_10711)) ;;
          ret (seq_upd yden_k_10735 (usize 14) (temp_10713))) ;;
      
       '(xnum_10721 : fp_t) ←
          ( '(temp_10715 : fp_t) ←
              (nat_mod_zero ) ;;
            ret (temp_10715)) ;;
        #put xnum_10721_loc := xnum_10721 ;;
       '(xx_10722 : fp_t) ←
          ( '(temp_10717 : fp_t) ←
              (nat_mod_one ) ;;
            ret (temp_10717)) ;;
        #put xx_10722_loc := xx_10722 ;;
       '(temp_10720 : uint_size) ←
        (seq_len (xnum_k_10718)) ;;
       temp_10822 ←
        (foldi' (usize 0) (temp_10720) prod_ce(xnum_10721, xx_10722) (
              L2 := CEfset (
                [xnum_k_10718_loc ; xden_k_10733_loc ; ynum_k_10734_loc ; yden_k_10735_loc ; xnum_10721_loc ; xx_10722_loc ; xden_10742_loc ; xx_10743_loc ; ynum_10761_loc ; xx_10762_loc ; yden_10778_loc ; xx_10779_loc ; inf_10812_loc])) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_10723 '(
              xnum_10721,
              xx_10722
            ) =>
            ({ code  '(xnum_10721 : fp_t) ←
                  (( '(temp_10725 : fp_t) ←
                        (seq_index (xnum_k_10718) (i_10723)) ;;
                       '(temp_10727 : fp_t) ←
                        ((xx_10722) *% (temp_10725)) ;;
                       '(temp_10729 : fp_t) ←
                        ((xnum_10721) +% (temp_10727)) ;;
                      ret (temp_10729))) ;;
                #put xnum_10721_loc := xnum_10721 ;;
              
               '(xx_10722 : fp_t) ←
                  (( '(temp_10732 : fp_t) ←
                        ((xx_10722) *% (x_10730)) ;;
                      ret (temp_10732))) ;;
                #put xx_10722_loc := xx_10722 ;;
              
              @ret ((fp_t '× fp_t)) (prod_ce(xnum_10721, xx_10722)) } : code (
                CEfset (
                  [xnum_k_10718_loc ; xden_k_10733_loc ; ynum_k_10734_loc ; yden_k_10735_loc ; xnum_10721_loc ; xx_10722_loc])) [interface] _))) ;;
      let '(xnum_10721, xx_10722) :=
        (temp_10822) : (fp_t '× fp_t) in
      
       '(xden_10742 : fp_t) ←
          ( '(temp_10737 : fp_t) ←
              (nat_mod_zero ) ;;
            ret (temp_10737)) ;;
        #put xden_10742_loc := xden_10742 ;;
       '(xx_10743 : fp_t) ←
          ( '(temp_10739 : fp_t) ←
              (nat_mod_one ) ;;
            ret (temp_10739)) ;;
        #put xx_10743_loc := xx_10743 ;;
       '(temp_10741 : uint_size) ←
        (seq_len (xden_k_10733)) ;;
       temp_10820 ←
        (foldi' (usize 0) (temp_10741) prod_ce(xden_10742, xx_10743) (
              L2 := CEfset (
                [xnum_k_10718_loc ; xden_k_10733_loc ; ynum_k_10734_loc ; yden_k_10735_loc ; xnum_10721_loc ; xx_10722_loc ; xden_10742_loc ; xx_10743_loc ; ynum_10761_loc ; xx_10762_loc ; yden_10778_loc ; xx_10779_loc ; inf_10812_loc])) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_10744 '(
              xden_10742,
              xx_10743
            ) =>
            ({ code  '(xden_10742 : fp_t) ←
                  (( '(temp_10746 : fp_t) ←
                        (seq_index (xden_k_10733) (i_10744)) ;;
                       '(temp_10748 : fp_t) ←
                        ((xx_10743) *% (temp_10746)) ;;
                       '(temp_10750 : fp_t) ←
                        ((xden_10742) +% (temp_10748)) ;;
                      ret (temp_10750))) ;;
                #put xden_10742_loc := xden_10742 ;;
              
               '(xx_10743 : fp_t) ←
                  (( '(temp_10752 : fp_t) ←
                        ((xx_10743) *% (x_10730)) ;;
                      ret (temp_10752))) ;;
                #put xx_10743_loc := xx_10743 ;;
              
              @ret ((fp_t '× fp_t)) (prod_ce(xden_10742, xx_10743)) } : code (
                CEfset (
                  [xnum_k_10718_loc ; xden_k_10733_loc ; ynum_k_10734_loc ; yden_k_10735_loc ; xnum_10721_loc ; xx_10722_loc ; xden_10742_loc ; xx_10743_loc])) [interface] _))) ;;
      let '(xden_10742, xx_10743) :=
        (temp_10820) : (fp_t '× fp_t) in
      
       '(xden_10742 : fp_t) ←
          (( '(temp_10754 : fp_t) ←
                ((xden_10742) +% (xx_10743)) ;;
              ret (temp_10754))) ;;
        #put xden_10742_loc := xden_10742 ;;
      
       '(ynum_10761 : fp_t) ←
          ( '(temp_10756 : fp_t) ←
              (nat_mod_zero ) ;;
            ret (temp_10756)) ;;
        #put ynum_10761_loc := ynum_10761 ;;
       '(xx_10762 : fp_t) ←
          ( '(temp_10758 : fp_t) ←
              (nat_mod_one ) ;;
            ret (temp_10758)) ;;
        #put xx_10762_loc := xx_10762 ;;
       '(temp_10760 : uint_size) ←
        (seq_len (ynum_k_10734)) ;;
       temp_10818 ←
        (foldi' (usize 0) (temp_10760) prod_ce(ynum_10761, xx_10762) (
              L2 := CEfset (
                [xnum_k_10718_loc ; xden_k_10733_loc ; ynum_k_10734_loc ; yden_k_10735_loc ; xnum_10721_loc ; xx_10722_loc ; xden_10742_loc ; xx_10743_loc ; ynum_10761_loc ; xx_10762_loc ; yden_10778_loc ; xx_10779_loc ; inf_10812_loc])) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_10763 '(
              ynum_10761,
              xx_10762
            ) =>
            ({ code  '(ynum_10761 : fp_t) ←
                  (( '(temp_10765 : fp_t) ←
                        (seq_index (ynum_k_10734) (i_10763)) ;;
                       '(temp_10767 : fp_t) ←
                        ((xx_10762) *% (temp_10765)) ;;
                       '(temp_10769 : fp_t) ←
                        ((ynum_10761) +% (temp_10767)) ;;
                      ret (temp_10769))) ;;
                #put ynum_10761_loc := ynum_10761 ;;
              
               '(xx_10762 : fp_t) ←
                  (( '(temp_10771 : fp_t) ←
                        ((xx_10762) *% (x_10730)) ;;
                      ret (temp_10771))) ;;
                #put xx_10762_loc := xx_10762 ;;
              
              @ret ((fp_t '× fp_t)) (prod_ce(ynum_10761, xx_10762)) } : code (
                CEfset (
                  [xnum_k_10718_loc ; xden_k_10733_loc ; ynum_k_10734_loc ; yden_k_10735_loc ; xnum_10721_loc ; xx_10722_loc ; xden_10742_loc ; xx_10743_loc ; ynum_10761_loc ; xx_10762_loc])) [interface] _))) ;;
      let '(ynum_10761, xx_10762) :=
        (temp_10818) : (fp_t '× fp_t) in
      
       '(yden_10778 : fp_t) ←
          ( '(temp_10773 : fp_t) ←
              (nat_mod_zero ) ;;
            ret (temp_10773)) ;;
        #put yden_10778_loc := yden_10778 ;;
       '(xx_10779 : fp_t) ←
          ( '(temp_10775 : fp_t) ←
              (nat_mod_one ) ;;
            ret (temp_10775)) ;;
        #put xx_10779_loc := xx_10779 ;;
       '(temp_10777 : uint_size) ←
        (seq_len (yden_k_10735)) ;;
       temp_10816 ←
        (foldi' (usize 0) (temp_10777) prod_ce(yden_10778, xx_10779) (
              L2 := CEfset (
                [xnum_k_10718_loc ; xden_k_10733_loc ; ynum_k_10734_loc ; yden_k_10735_loc ; xnum_10721_loc ; xx_10722_loc ; xden_10742_loc ; xx_10743_loc ; ynum_10761_loc ; xx_10762_loc ; yden_10778_loc ; xx_10779_loc ; inf_10812_loc])) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_10780 '(
              yden_10778,
              xx_10779
            ) =>
            ({ code  '(yden_10778 : fp_t) ←
                  (( '(temp_10782 : fp_t) ←
                        (seq_index (yden_k_10735) (i_10780)) ;;
                       '(temp_10784 : fp_t) ←
                        ((xx_10779) *% (temp_10782)) ;;
                       '(temp_10786 : fp_t) ←
                        ((yden_10778) +% (temp_10784)) ;;
                      ret (temp_10786))) ;;
                #put yden_10778_loc := yden_10778 ;;
              
               '(xx_10779 : fp_t) ←
                  (( '(temp_10788 : fp_t) ←
                        ((xx_10779) *% (x_10730)) ;;
                      ret (temp_10788))) ;;
                #put xx_10779_loc := xx_10779 ;;
              
              @ret ((fp_t '× fp_t)) (prod_ce(yden_10778, xx_10779)) } : code (
                CEfset (
                  [xnum_k_10718_loc ; xden_k_10733_loc ; ynum_k_10734_loc ; yden_k_10735_loc ; xnum_10721_loc ; xx_10722_loc ; xden_10742_loc ; xx_10743_loc ; ynum_10761_loc ; xx_10762_loc ; yden_10778_loc ; xx_10779_loc])) [interface] _))) ;;
      let '(yden_10778, xx_10779) :=
        (temp_10816) : (fp_t '× fp_t) in
      
       '(yden_10778 : fp_t) ←
          (( '(temp_10790 : fp_t) ←
                ((yden_10778) +% (xx_10779)) ;;
              ret (temp_10790))) ;;
        #put yden_10778_loc := yden_10778 ;;
      
       '(xr_10813 : fp_t) ←
        ( temp_10792 ←
            (nat_mod_inv (xden_10742)) ;;
           '(temp_10794 : fp_t) ←
            ((xnum_10721) *% (temp_10792)) ;;
          ret (temp_10794)) ;;
       '(yr_10814 : fp_t) ←
        ( '(temp_10797 : fp_t) ←
            ((y_10795) *% (ynum_10761)) ;;
           temp_10799 ←
            (nat_mod_inv (yden_10778)) ;;
           '(temp_10801 : fp_t) ←
            ((temp_10797) *% (temp_10799)) ;;
          ret (temp_10801)) ;;
       '(inf_10812 : bool_ChoiceEquality) ←
          (ret ((false : bool_ChoiceEquality))) ;;
        #put inf_10812_loc := inf_10812 ;;
       '(temp_10803 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_10805 : bool_ChoiceEquality) ←
        ((xden_10742) =.? (temp_10803)) ;;
       '(temp_10807 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_10809 : bool_ChoiceEquality) ←
        ((yden_10778) =.? (temp_10807)) ;;
       '(temp_10811 : bool_ChoiceEquality) ←
        ((temp_10805) || (temp_10809)) ;;
       '(inf_10812 : (bool_ChoiceEquality)) ←
        (if temp_10811:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(
                  inf_10812 : bool_ChoiceEquality) ←
                ((ret ((true : bool_ChoiceEquality)))) ;;
              #put inf_10812_loc := inf_10812 ;;
            
            @ret ((bool_ChoiceEquality)) (inf_10812) in
            ({ code temp_then } : code (CEfset (
                  [xnum_k_10718_loc ; xden_k_10733_loc ; ynum_k_10734_loc ; yden_k_10735_loc ; xnum_10721_loc ; xx_10722_loc ; xden_10742_loc ; xx_10743_loc ; ynum_10761_loc ; xx_10762_loc ; yden_10778_loc ; xx_10779_loc ; inf_10812_loc])) [interface] _))
          else @ret ((bool_ChoiceEquality)) (inf_10812)) ;;
      
      @ret ((fp_t '× fp_t '× bool_ChoiceEquality)) (prod_ce(
          xr_10813,
          yr_10814,
          inf_10812
        )) } : code (CEfset (
          [xnum_k_10718_loc ; xden_k_10733_loc ; ynum_k_10734_loc ; yden_k_10735_loc ; xnum_10721_loc ; xx_10722_loc ; xden_10742_loc ; xx_10743_loc ; ynum_10761_loc ; xx_10762_loc ; yden_10778_loc ; xx_10779_loc ; inf_10812_loc])) [interface] _)
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
  (10847).
Program Definition g1_map_to_curve_sswu
   : package (CEfset ([])) [interface
  #val #[ G1_ISOGENY_MAP ] : g1_isogeny_map_inp → g1_isogeny_map_out ;
  #val #[ G1_SIMPLE_SWU_ISO ] : g1_simple_swu_iso_inp → g1_simple_swu_iso_out
  ] [interface
  #val #[ G1_MAP_TO_CURVE_SSWU ] : g1_map_to_curve_sswu_inp → g1_map_to_curve_sswu_out
  ] :=
  (
    [package #def #[ G1_MAP_TO_CURVE_SSWU ] (temp_inp : g1_map_to_curve_sswu_inp) : g1_map_to_curve_sswu_out { 
    let '(u_10837) := temp_inp : fp_t in
    #import {sig #[ G1_ISOGENY_MAP ] : g1_isogeny_map_inp → g1_isogeny_map_out } as g1_isogeny_map ;;
    let g1_isogeny_map := fun x_0 x_1 => g1_isogeny_map (x_0,x_1) in
    #import {sig #[ G1_SIMPLE_SWU_ISO ] : g1_simple_swu_iso_inp → g1_simple_swu_iso_out } as g1_simple_swu_iso ;;
    let g1_simple_swu_iso := fun x_0 => g1_simple_swu_iso (x_0) in
    ({ code  temp_10846 ←
        ( '(temp_10839 : (fp_t '× fp_t)) ←
            (g1_simple_swu_iso (u_10837)) ;;
          ret (temp_10839)) ;;
      let '(xp_10840, yp_10841) :=
        (temp_10846) : (fp_t '× fp_t) in
       '(p_10844 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( '(temp_10843 : g1_t) ←
            (g1_isogeny_map (xp_10840) (yp_10841)) ;;
          ret (temp_10843)) ;;
      @ret ((fp_t '× fp_t '× bool_ChoiceEquality)) (p_10844) } : code (
        CEfset ([])) [interface
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
  (10869).
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
    let '(msg_10848 , dst_10849) := temp_inp : byte_seq '× byte_seq in
    #import {sig #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out } as fp_hash_to_field ;;
    let fp_hash_to_field := fun x_0 x_1 x_2 => fp_hash_to_field (x_0,x_1,x_2) in
    #import {sig #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out } as g1_clear_cofactor ;;
    let g1_clear_cofactor := fun x_0 => g1_clear_cofactor (x_0) in
    #import {sig #[ G1_MAP_TO_CURVE_SSWU ] : g1_map_to_curve_sswu_inp → g1_map_to_curve_sswu_out } as g1_map_to_curve_sswu ;;
    let g1_map_to_curve_sswu := fun x_0 => g1_map_to_curve_sswu (x_0) in
    #import {sig #[ G1ADD ] : g1add_inp → g1add_out } as g1add ;;
    let g1add := fun x_0 x_1 => g1add (x_0,x_1) in
    ({ code  '(u_10853 : seq fp_t) ←
        ( '(temp_10851 : seq fp_t) ←
            (fp_hash_to_field (msg_10848) (dst_10849) (usize 2)) ;;
          ret (temp_10851)) ;;
       '(q0_10861 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( '(temp_10854 : fp_t) ←
            (seq_index (u_10853) (usize 0)) ;;
           '(temp_10856 : g1_t) ←
            (g1_map_to_curve_sswu (temp_10854)) ;;
          ret (temp_10856)) ;;
       '(q1_10862 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( '(temp_10858 : fp_t) ←
            (seq_index (u_10853) (usize 1)) ;;
           '(temp_10860 : g1_t) ←
            (g1_map_to_curve_sswu (temp_10858)) ;;
          ret (temp_10860)) ;;
       '(r_10865 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( temp_10864 ←
            (g1add (q0_10861) (q1_10862)) ;;
          ret (temp_10864)) ;;
       '(p_10868 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( '(temp_10867 : g1_t) ←
            (g1_clear_cofactor (r_10865)) ;;
          ret (temp_10867)) ;;
      @ret ((fp_t '× fp_t '× bool_ChoiceEquality)) (p_10868) } : code (
        CEfset ([])) [interface
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
  (10883).
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
    let '(msg_10870 , dst_10871) := temp_inp : byte_seq '× byte_seq in
    #import {sig #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out } as fp_hash_to_field ;;
    let fp_hash_to_field := fun x_0 x_1 x_2 => fp_hash_to_field (x_0,x_1,x_2) in
    #import {sig #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out } as g1_clear_cofactor ;;
    let g1_clear_cofactor := fun x_0 => g1_clear_cofactor (x_0) in
    #import {sig #[ G1_MAP_TO_CURVE_SSWU ] : g1_map_to_curve_sswu_inp → g1_map_to_curve_sswu_out } as g1_map_to_curve_sswu ;;
    let g1_map_to_curve_sswu := fun x_0 => g1_map_to_curve_sswu (x_0) in
    ({ code  '(u_10875 : seq fp_t) ←
        ( '(temp_10873 : seq fp_t) ←
            (fp_hash_to_field (msg_10870) (dst_10871) (usize 1)) ;;
          ret (temp_10873)) ;;
       '(q_10879 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( '(temp_10876 : fp_t) ←
            (seq_index (u_10875) (usize 0)) ;;
           '(temp_10878 : g1_t) ←
            (g1_map_to_curve_sswu (temp_10876)) ;;
          ret (temp_10878)) ;;
       '(p_10882 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
        ( '(temp_10881 : g1_t) ←
            (g1_clear_cofactor (q_10879)) ;;
          ret (temp_10881)) ;;
      @ret ((fp_t '× fp_t '× bool_ChoiceEquality)) (p_10882) } : code (
        CEfset ([])) [interface
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
  (let temp_10885 : int64 :=
      (secret (@repr U64 416399692810564414)) in
    let temp_10887 : int64 :=
      (secret (@repr U64 13500519111022079365)) in
    let temp_10889 : int64 :=
      (secret (@repr U64 3658379999393219626)) in
    let temp_10891 : int64 :=
      (secret (@repr U64 9850925049107374429)) in
    let temp_10893 : int64 :=
      (secret (@repr U64 6640057249351452444)) in
    let temp_10895 : int64 :=
      (secret (@repr U64 7077594464397203414)) in
    let temp_10897 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10885;
          temp_10887;
          temp_10889;
          temp_10891;
          temp_10893;
          temp_10895
        ]) in
    (temp_10897)).

Definition g2_xnum_k_1_i_v : (arr_fp_t) :=
  (let temp_10899 : int64 :=
      (secret (@repr U64 1249199078431693244)) in
    let temp_10901 : int64 :=
      (secret (@repr U64 3608069185647134863)) in
    let temp_10903 : int64 :=
      (secret (@repr U64 10975139998179658879)) in
    let temp_10905 : int64 :=
      (secret (@repr U64 11106031073612571672)) in
    let temp_10907 : int64 :=
      (secret (@repr U64 1473427674344805717)) in
    let temp_10909 : int64 :=
      (secret (@repr U64 2786039319482058522)) in
    let temp_10911 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10899;
          temp_10901;
          temp_10903;
          temp_10905;
          temp_10907;
          temp_10909
        ]) in
    (temp_10911)).

Definition g2_xnum_k_2_r_v : (arr_fp_t) :=
  (let temp_10913 : int64 :=
      (secret (@repr U64 1249199078431693244)) in
    let temp_10915 : int64 :=
      (secret (@repr U64 3608069185647134863)) in
    let temp_10917 : int64 :=
      (secret (@repr U64 10975139998179658879)) in
    let temp_10919 : int64 :=
      (secret (@repr U64 11106031073612571672)) in
    let temp_10921 : int64 :=
      (secret (@repr U64 1473427674344805717)) in
    let temp_10923 : int64 :=
      (secret (@repr U64 2786039319482058526)) in
    let temp_10925 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10913;
          temp_10915;
          temp_10917;
          temp_10919;
          temp_10921;
          temp_10923
        ]) in
    (temp_10925)).

Definition g2_xnum_k_2_i_v : (arr_fp_t) :=
  (let temp_10927 : int64 :=
      (secret (@repr U64 624599539215846622)) in
    let temp_10929 : int64 :=
      (secret (@repr U64 1804034592823567431)) in
    let temp_10931 : int64 :=
      (secret (@repr U64 14710942035944605247)) in
    let temp_10933 : int64 :=
      (secret (@repr U64 14776387573661061644)) in
    let temp_10935 : int64 :=
      (secret (@repr U64 736713837172402858)) in
    let temp_10937 : int64 :=
      (secret (@repr U64 10616391696595805069)) in
    let temp_10939 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10927;
          temp_10929;
          temp_10931;
          temp_10933;
          temp_10935;
          temp_10937
        ]) in
    (temp_10939)).

Definition g2_xnum_k_3_r_v : (arr_fp_t) :=
  (let temp_10941 : int64 :=
      (secret (@repr U64 1665598771242257658)) in
    let temp_10943 : int64 :=
      (secret (@repr U64 17108588296669214228)) in
    let temp_10945 : int64 :=
      (secret (@repr U64 14633519997572878506)) in
    let temp_10947 : int64 :=
      (secret (@repr U64 2510212049010394485)) in
    let temp_10949 : int64 :=
      (secret (@repr U64 8113484923696258161)) in
    let temp_10951 : int64 :=
      (secret (@repr U64 9863633783879261905)) in
    let temp_10953 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10941;
          temp_10943;
          temp_10945;
          temp_10947;
          temp_10949;
          temp_10951
        ]) in
    (temp_10953)).

Definition g2_xden_k_0_i_v : (arr_fp_t) :=
  (let temp_10955 : int64 :=
      (secret (@repr U64 1873798617647539866)) in
    let temp_10957 : int64 :=
      (secret (@repr U64 5412103778470702295)) in
    let temp_10959 : int64 :=
      (secret (@repr U64 7239337960414712511)) in
    let temp_10961 : int64 :=
      (secret (@repr U64 7435674573564081700)) in
    let temp_10963 : int64 :=
      (secret (@repr U64 2210141511517208575)) in
    let temp_10965 : int64 :=
      (secret (@repr U64 13402431016077863523)) in
    let temp_10967 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10955;
          temp_10957;
          temp_10959;
          temp_10961;
          temp_10963;
          temp_10965
        ]) in
    (temp_10967)).

Definition g2_xden_k_1_i_v : (arr_fp_t) :=
  (let temp_10969 : int64 :=
      (secret (@repr U64 1873798617647539866)) in
    let temp_10971 : int64 :=
      (secret (@repr U64 5412103778470702295)) in
    let temp_10973 : int64 :=
      (secret (@repr U64 7239337960414712511)) in
    let temp_10975 : int64 :=
      (secret (@repr U64 7435674573564081700)) in
    let temp_10977 : int64 :=
      (secret (@repr U64 2210141511517208575)) in
    let temp_10979 : int64 :=
      (secret (@repr U64 13402431016077863583)) in
    let temp_10981 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10969;
          temp_10971;
          temp_10973;
          temp_10975;
          temp_10977;
          temp_10979
        ]) in
    (temp_10981)).

Definition g2_ynum_k_0_v : (arr_fp_t) :=
  (let temp_10983 : int64 :=
      (secret (@repr U64 1526798873638736187)) in
    let temp_10985 : int64 :=
      (secret (@repr U64 6459500568425337235)) in
    let temp_10987 : int64 :=
      (secret (@repr U64 1116230615302104219)) in
    let temp_10989 : int64 :=
      (secret (@repr U64 17673314439684154624)) in
    let temp_10991 : int64 :=
      (secret (@repr U64 18197961889718808424)) in
    let temp_10993 : int64 :=
      (secret (@repr U64 1355520937843676934)) in
    let temp_10995 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10983;
          temp_10985;
          temp_10987;
          temp_10989;
          temp_10991;
          temp_10993
        ]) in
    (temp_10995)).

Definition g2_ynum_k_1_i_v : (arr_fp_t) :=
  (let temp_10997 : int64 :=
      (secret (@repr U64 416399692810564414)) in
    let temp_10999 : int64 :=
      (secret (@repr U64 13500519111022079365)) in
    let temp_11001 : int64 :=
      (secret (@repr U64 3658379999393219626)) in
    let temp_11003 : int64 :=
      (secret (@repr U64 9850925049107374429)) in
    let temp_11005 : int64 :=
      (secret (@repr U64 6640057249351452444)) in
    let temp_11007 : int64 :=
      (secret (@repr U64 7077594464397203390)) in
    let temp_11009 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_10997;
          temp_10999;
          temp_11001;
          temp_11003;
          temp_11005;
          temp_11007
        ]) in
    (temp_11009)).

Definition g2_ynum_k_2_r_v : (arr_fp_t) :=
  (let temp_11011 : int64 :=
      (secret (@repr U64 1249199078431693244)) in
    let temp_11013 : int64 :=
      (secret (@repr U64 3608069185647134863)) in
    let temp_11015 : int64 :=
      (secret (@repr U64 10975139998179658879)) in
    let temp_11017 : int64 :=
      (secret (@repr U64 11106031073612571672)) in
    let temp_11019 : int64 :=
      (secret (@repr U64 1473427674344805717)) in
    let temp_11021 : int64 :=
      (secret (@repr U64 2786039319482058524)) in
    let temp_11023 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_11011;
          temp_11013;
          temp_11015;
          temp_11017;
          temp_11019;
          temp_11021
        ]) in
    (temp_11023)).

Definition g2_ynum_k_2_i_v : (arr_fp_t) :=
  (let temp_11025 : int64 :=
      (secret (@repr U64 624599539215846622)) in
    let temp_11027 : int64 :=
      (secret (@repr U64 1804034592823567431)) in
    let temp_11029 : int64 :=
      (secret (@repr U64 14710942035944605247)) in
    let temp_11031 : int64 :=
      (secret (@repr U64 14776387573661061644)) in
    let temp_11033 : int64 :=
      (secret (@repr U64 736713837172402858)) in
    let temp_11035 : int64 :=
      (secret (@repr U64 10616391696595805071)) in
    let temp_11037 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_11025;
          temp_11027;
          temp_11029;
          temp_11031;
          temp_11033;
          temp_11035
        ]) in
    (temp_11037)).

Definition g2_ynum_k_3_r_v : (arr_fp_t) :=
  (let temp_11039 : int64 :=
      (secret (@repr U64 1318599027233453979)) in
    let temp_11041 : int64 :=
      (secret (@repr U64 18155985086623849168)) in
    let temp_11043 : int64 :=
      (secret (@repr U64 8510412652460270214)) in
    let temp_11045 : int64 :=
      (secret (@repr U64 12747851915130467410)) in
    let temp_11047 : int64 :=
      (secret (@repr U64 5654561228188306393)) in
    let temp_11049 : int64 :=
      (secret (@repr U64 16263467779354626832)) in
    let temp_11051 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_11039;
          temp_11041;
          temp_11043;
          temp_11045;
          temp_11047;
          temp_11049
        ]) in
    (temp_11051)).

Definition g2_yden_k_0_v : (arr_fp_t) :=
  (let temp_11053 : int64 :=
      (secret (@repr U64 1873798617647539866)) in
    let temp_11055 : int64 :=
      (secret (@repr U64 5412103778470702295)) in
    let temp_11057 : int64 :=
      (secret (@repr U64 7239337960414712511)) in
    let temp_11059 : int64 :=
      (secret (@repr U64 7435674573564081700)) in
    let temp_11061 : int64 :=
      (secret (@repr U64 2210141511517208575)) in
    let temp_11063 : int64 :=
      (secret (@repr U64 13402431016077863163)) in
    let temp_11065 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_11053;
          temp_11055;
          temp_11057;
          temp_11059;
          temp_11061;
          temp_11063
        ]) in
    (temp_11065)).

Definition g2_yden_k_1_i_v : (arr_fp_t) :=
  (let temp_11067 : int64 :=
      (secret (@repr U64 1873798617647539866)) in
    let temp_11069 : int64 :=
      (secret (@repr U64 5412103778470702295)) in
    let temp_11071 : int64 :=
      (secret (@repr U64 7239337960414712511)) in
    let temp_11073 : int64 :=
      (secret (@repr U64 7435674573564081700)) in
    let temp_11075 : int64 :=
      (secret (@repr U64 2210141511517208575)) in
    let temp_11077 : int64 :=
      (secret (@repr U64 13402431016077863379)) in
    let temp_11079 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_11067;
          temp_11069;
          temp_11071;
          temp_11073;
          temp_11075;
          temp_11077
        ]) in
    (temp_11079)).

Definition g2_yden_k_2_i_v : (arr_fp_t) :=
  (let temp_11081 : int64 :=
      (secret (@repr U64 1873798617647539866)) in
    let temp_11083 : int64 :=
      (secret (@repr U64 5412103778470702295)) in
    let temp_11085 : int64 :=
      (secret (@repr U64 7239337960414712511)) in
    let temp_11087 : int64 :=
      (secret (@repr U64 7435674573564081700)) in
    let temp_11089 : int64 :=
      (secret (@repr U64 2210141511517208575)) in
    let temp_11091 : int64 :=
      (secret (@repr U64 13402431016077863577)) in
    let temp_11093 : nseq uint64 6 :=
      (array_from_list uint64 [
          temp_11081;
          temp_11083;
          temp_11085;
          temp_11087;
          temp_11089;
          temp_11091
        ]) in
    (temp_11093)).

Definition y_11193_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 11203%nat)).
Definition x1_11155_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 11204%nat)).
Notation "'g2_simple_swu_iso_inp'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_simple_swu_iso_out'" := ((fp2_t '× fp2_t
  ) : choice_type) (in custom pack_type at level 2).
Definition G2_SIMPLE_SWU_ISO : nat :=
  (11205).
Program Definition g2_simple_swu_iso
   : package (CEfset ([x1_11155_loc ; y_11193_loc])) [interface
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
    let '(u_11111) := temp_inp : fp2_t in
    #import {sig #[ FP2_IS_SQUARE ] : fp2_is_square_inp → fp2_is_square_out } as fp2_is_square ;;
    let fp2_is_square := fun x_0 => fp2_is_square (x_0) in
    #import {sig #[ FP2_SGN0 ] : fp2_sgn0_inp → fp2_sgn0_out } as fp2_sgn0 ;;
    let fp2_sgn0 := fun x_0 => fp2_sgn0 (x_0) in
    #import {sig #[ FP2_SQRT ] : fp2_sqrt_inp → fp2_sqrt_out } as fp2_sqrt ;;
    let fp2_sqrt := fun x_0 => fp2_sqrt (x_0) in
    #import {sig #[ FP2ADD ] : fp2add_inp → fp2add_out } as fp2add ;;
    let fp2add := fun x_0 x_1 => fp2add (x_0,x_1) in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP2INV ] : fp2inv_inp → fp2inv_out } as fp2inv ;;
    let fp2inv := fun x_0 => fp2inv (x_0) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    #import {sig #[ FP2NEG ] : fp2neg_inp → fp2neg_out } as fp2neg ;;
    let fp2neg := fun x_0 => fp2neg (x_0) in
    #import {sig #[ FP2ZERO ] : fp2zero_inp → fp2zero_out } as fp2zero ;;
    let fp2zero := fp2zero tt in
    ({ code  '(z_11108 : (fp_t '× fp_t)) ←
        ( '(temp_11095 : fp_t) ←
            (nat_mod_two ) ;;
           '(temp_11097 : fp_t) ←
            (nat_mod_one ) ;;
           temp_11099 ←
            (fp2neg (prod_ce(temp_11095, temp_11097))) ;;
          ret (temp_11099)) ;;
       '(a_11131 : (fp_t '× fp_t)) ←
        ( '(temp_11101 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_11103 : fp_t) ←
            (nat_mod_from_literal (_) (@repr U128 240)) ;;
          ret (prod_ce(temp_11101, temp_11103))) ;;
       '(b_11128 : (fp_t '× fp_t)) ←
        ( '(temp_11105 : fp_t) ←
            (nat_mod_from_literal (_) (@repr U128 1012)) ;;
           '(temp_11107 : fp_t) ←
            (nat_mod_from_literal (_) (@repr U128 1012)) ;;
          ret (prod_ce(temp_11105, temp_11107))) ;;
       '(tv1_11140 : (fp_t '× fp_t)) ←
        ( temp_11110 ←
            (fp2mul (z_11108) (z_11108)) ;;
           temp_11113 ←
            (fp2mul (u_11111) (u_11111)) ;;
           temp_11115 ←
            (fp2mul (u_11111) (u_11111)) ;;
           temp_11117 ←
            (fp2mul (temp_11113) (temp_11115)) ;;
           temp_11119 ←
            (fp2mul (temp_11110) (temp_11117)) ;;
           temp_11121 ←
            (fp2mul (u_11111) (u_11111)) ;;
           temp_11123 ←
            (fp2mul (z_11108) (temp_11121)) ;;
           temp_11125 ←
            (fp2add (temp_11119) (temp_11123)) ;;
           temp_11127 ←
            (fp2inv (temp_11125)) ;;
          ret (temp_11127)) ;;
       '(x1_11155 : (fp_t '× fp_t)) ←
          ( temp_11130 ←
              (fp2neg (b_11128)) ;;
             temp_11133 ←
              (fp2inv (a_11131)) ;;
             temp_11135 ←
              (fp2mul (temp_11130) (temp_11133)) ;;
             '(temp_11137 : fp_t) ←
              (nat_mod_one ) ;;
             temp_11139 ←
              (fp2fromfp (temp_11137)) ;;
             temp_11142 ←
              (fp2add (temp_11139) (tv1_11140)) ;;
             temp_11144 ←
              (fp2mul (temp_11135) (temp_11142)) ;;
            ret (temp_11144)) ;;
        #put x1_11155_loc := x1_11155 ;;
       temp_11146 ←
        (fp2zero ) ;;
       '(temp_11148 : bool_ChoiceEquality) ←
        ((tv1_11140) =.? (temp_11146)) ;;
       '(x1_11155 : ((fp_t '× fp_t))) ←
        (if temp_11148:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(x1_11155 : (fp_t '× fp_t
                  )) ←
                (( temp_11150 ←
                      (fp2mul (z_11108) (a_11131)) ;;
                     temp_11152 ←
                      (fp2inv (temp_11150)) ;;
                     temp_11154 ←
                      (fp2mul (b_11128) (temp_11152)) ;;
                    ret (temp_11154))) ;;
              #put x1_11155_loc := x1_11155 ;;
            
            @ret (((fp_t '× fp_t))) (x1_11155) in
            ({ code temp_then } : code (CEfset ([x1_11155_loc])) [interface
              #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] _))
          else @ret (((fp_t '× fp_t))) (x1_11155)) ;;
      
       '(gx1_11183 : (fp_t '× fp_t)) ←
        ( temp_11157 ←
            (fp2mul (x1_11155) (x1_11155)) ;;
           temp_11159 ←
            (fp2mul (temp_11157) (x1_11155)) ;;
           temp_11161 ←
            (fp2mul (a_11131) (x1_11155)) ;;
           temp_11163 ←
            (fp2add (temp_11159) (temp_11161)) ;;
           temp_11165 ←
            (fp2add (temp_11163) (b_11128)) ;;
          ret (temp_11165)) ;;
       '(x2_11172 : (fp_t '× fp_t)) ←
        ( temp_11167 ←
            (fp2mul (u_11111) (u_11111)) ;;
           temp_11169 ←
            (fp2mul (z_11108) (temp_11167)) ;;
           temp_11171 ←
            (fp2mul (temp_11169) (x1_11155)) ;;
          ret (temp_11171)) ;;
       '(gx2_11188 : (fp_t '× fp_t)) ←
        ( temp_11174 ←
            (fp2mul (x2_11172) (x2_11172)) ;;
           temp_11176 ←
            (fp2mul (temp_11174) (x2_11172)) ;;
           temp_11178 ←
            (fp2mul (a_11131) (x2_11172)) ;;
           temp_11180 ←
            (fp2add (temp_11176) (temp_11178)) ;;
           temp_11182 ←
            (fp2add (temp_11180) (b_11128)) ;;
          ret (temp_11182)) ;;
       temp_11202 ←
        ( '(temp_11185 : bool_ChoiceEquality) ←
            (fp2_is_square (gx1_11183)) ;;
           '(temp_11187 : fp2_t) ←
            (fp2_sqrt (gx1_11183)) ;;
           '(temp_11190 : fp2_t) ←
            (fp2_sqrt (gx2_11188)) ;;
          ret ((if (temp_11185):bool_ChoiceEquality then (*inline*) (prod_ce(
                  x1_11155,
                  temp_11187
                )) else (prod_ce(x2_11172, temp_11190))))) ;;
      let '(x_11200, y_11193) :=
        (temp_11202) : ((fp_t '× fp_t) '× fp2_t) in
       '(temp_11192 : bool_ChoiceEquality) ←
        (fp2_sgn0 (u_11111)) ;;
       '(temp_11195 : bool_ChoiceEquality) ←
        (fp2_sgn0 (y_11193)) ;;
       '(temp_11197 : bool_ChoiceEquality) ←
        ((temp_11192) !=.? (temp_11195)) ;;
       '(y_11193 : ((fp_t '× fp_t))) ←
        (if temp_11197:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(y_11193 : (fp_t '× fp_t)) ←
                (( temp_11199 ←
                      (fp2neg (y_11193)) ;;
                    ret (temp_11199))) ;;
              #put y_11193_loc := y_11193 ;;
            
            @ret (((fp_t '× fp_t))) (y_11193) in
            ({ code temp_then } : code (CEfset (
                  [x1_11155_loc ; y_11193_loc])) [interface
              #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ] _))
          else @ret (((fp_t '× fp_t))) (y_11193)) ;;
      
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t))) (prod_ce(x_11200, y_11193
        )) } : code (CEfset ([x1_11155_loc ; y_11193_loc])) [interface
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

Definition xx_11375_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 11419%nat)).
Definition xden_k_11323_loc : ChoiceEqualityLocation :=
  ((seq (fp_t '× fp_t) ; 11420%nat)).
Definition yden_k_11325_loc : ChoiceEqualityLocation :=
  ((seq (fp_t '× fp_t) ; 11421%nat)).
Definition ynum_11355_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 11422%nat)).
Definition ynum_k_11324_loc : ChoiceEqualityLocation :=
  ((seq (fp_t '× fp_t) ; 11423%nat)).
Definition xx_11312_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 11424%nat)).
Definition xnum_k_11308_loc : ChoiceEqualityLocation :=
  ((seq (fp_t '× fp_t) ; 11425%nat)).
Definition yden_11374_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 11426%nat)).
Definition xx_11335_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 11427%nat)).
Definition xden_11334_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 11428%nat)).
Definition xx_11356_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 11429%nat)).
Definition xnum_11311_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t) ; 11430%nat)).
Definition inf_11408_loc : ChoiceEqualityLocation :=
  ((bool_ChoiceEquality ; 11431%nat)).
Notation "'g2_isogeny_map_inp'" := (
  fp2_t '× fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_isogeny_map_out'" := (
  g2_t : choice_type) (in custom pack_type at level 2).
Definition G2_ISOGENY_MAP : nat :=
  (11432).
Program Definition g2_isogeny_map
   : package (CEfset (
      [xnum_k_11308_loc ; xden_k_11323_loc ; ynum_k_11324_loc ; yden_k_11325_loc ; xnum_11311_loc ; xx_11312_loc ; xden_11334_loc ; xx_11335_loc ; ynum_11355_loc ; xx_11356_loc ; yden_11374_loc ; xx_11375_loc ; inf_11408_loc])) [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ] [interface
  #val #[ G2_ISOGENY_MAP ] : g2_isogeny_map_inp → g2_isogeny_map_out ] :=
  (
    [package #def #[ G2_ISOGENY_MAP ] (temp_inp : g2_isogeny_map_inp) : g2_isogeny_map_out { 
    let '(x_11320 , y_11391) := temp_inp : fp2_t '× fp2_t in
    #import {sig #[ FP2ADD ] : fp2add_inp → fp2add_out } as fp2add ;;
    let fp2add := fun x_0 x_1 => fp2add (x_0,x_1) in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP2INV ] : fp2inv_inp → fp2inv_out } as fp2inv ;;
    let fp2inv := fun x_0 => fp2inv (x_0) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    #import {sig #[ FP2ZERO ] : fp2zero_inp → fp2zero_out } as fp2zero ;;
    let fp2zero := fp2zero tt in
    ({ code  '(xnum_k_11308 : seq (fp_t '× fp_t)) ←
          ( temp_11207 ←
              (seq_new_ (default : fp2_t) (usize 4)) ;;
            ret (temp_11207)) ;;
        #put xnum_k_11308_loc := xnum_k_11308 ;;
       '(xnum_k_11308 : seq (fp_t '× fp_t)) ←
        ( '(temp_11209 : seq int8) ←
            (array_to_be_bytes (g2_xnum_k_0_v)) ;;
           '(temp_11211 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_11209)) ;;
           '(temp_11213 : seq int8) ←
            (array_to_be_bytes (g2_xnum_k_0_v)) ;;
           '(temp_11215 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_11213)) ;;
          ret (seq_upd xnum_k_11308 (usize 0) (prod_ce(temp_11211, temp_11215
              )))) ;;
      
       '(xnum_k_11308 : seq (fp_t '× fp_t)) ←
        ( '(temp_11217 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_11219 : seq int8) ←
            (array_to_be_bytes (g2_xnum_k_1_i_v)) ;;
           '(temp_11221 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_11219)) ;;
          ret (seq_upd xnum_k_11308 (usize 1) (prod_ce(temp_11217, temp_11221
              )))) ;;
      
       '(xnum_k_11308 : seq (fp_t '× fp_t)) ←
        ( '(temp_11223 : seq int8) ←
            (array_to_be_bytes (g2_xnum_k_2_r_v)) ;;
           '(temp_11225 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_11223)) ;;
           '(temp_11227 : seq int8) ←
            (array_to_be_bytes (g2_xnum_k_2_i_v)) ;;
           '(temp_11229 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_11227)) ;;
          ret (seq_upd xnum_k_11308 (usize 2) (prod_ce(temp_11225, temp_11229
              )))) ;;
      
       '(xnum_k_11308 : seq (fp_t '× fp_t)) ←
        ( '(temp_11231 : seq int8) ←
            (array_to_be_bytes (g2_xnum_k_3_r_v)) ;;
           '(temp_11233 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_11231)) ;;
           '(temp_11235 : fp_t) ←
            (nat_mod_zero ) ;;
          ret (seq_upd xnum_k_11308 (usize 3) (prod_ce(temp_11233, temp_11235
              )))) ;;
      
       '(xden_k_11323 : seq (fp_t '× fp_t)) ←
          ( temp_11237 ←
              (seq_new_ (default : fp2_t) (usize 2)) ;;
            ret (temp_11237)) ;;
        #put xden_k_11323_loc := xden_k_11323 ;;
       '(xden_k_11323 : seq (fp_t '× fp_t)) ←
        ( '(temp_11239 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_11241 : seq int8) ←
            (array_to_be_bytes (g2_xden_k_0_i_v)) ;;
           '(temp_11243 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_11241)) ;;
          ret (seq_upd xden_k_11323 (usize 0) (prod_ce(temp_11239, temp_11243
              )))) ;;
      
       '(xden_k_11323 : seq (fp_t '× fp_t)) ←
        ( '(temp_11245 : fp_t) ←
            (nat_mod_from_literal (_) (@repr U128 12)) ;;
           '(temp_11247 : seq int8) ←
            (array_to_be_bytes (g2_xden_k_1_i_v)) ;;
           '(temp_11249 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_11247)) ;;
          ret (seq_upd xden_k_11323 (usize 1) (prod_ce(temp_11245, temp_11249
              )))) ;;
      
       '(ynum_k_11324 : seq (fp_t '× fp_t)) ←
          ( temp_11251 ←
              (seq_new_ (default : fp2_t) (usize 4)) ;;
            ret (temp_11251)) ;;
        #put ynum_k_11324_loc := ynum_k_11324 ;;
       '(ynum_k_11324 : seq (fp_t '× fp_t)) ←
        ( '(temp_11253 : seq int8) ←
            (array_to_be_bytes (g2_ynum_k_0_v)) ;;
           '(temp_11255 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_11253)) ;;
           '(temp_11257 : seq int8) ←
            (array_to_be_bytes (g2_ynum_k_0_v)) ;;
           '(temp_11259 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_11257)) ;;
          ret (seq_upd ynum_k_11324 (usize 0) (prod_ce(temp_11255, temp_11259
              )))) ;;
      
       '(ynum_k_11324 : seq (fp_t '× fp_t)) ←
        ( '(temp_11261 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_11263 : seq int8) ←
            (array_to_be_bytes (g2_ynum_k_1_i_v)) ;;
           '(temp_11265 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_11263)) ;;
          ret (seq_upd ynum_k_11324 (usize 1) (prod_ce(temp_11261, temp_11265
              )))) ;;
      
       '(ynum_k_11324 : seq (fp_t '× fp_t)) ←
        ( '(temp_11267 : seq int8) ←
            (array_to_be_bytes (g2_ynum_k_2_r_v)) ;;
           '(temp_11269 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_11267)) ;;
           '(temp_11271 : seq int8) ←
            (array_to_be_bytes (g2_ynum_k_2_i_v)) ;;
           '(temp_11273 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_11271)) ;;
          ret (seq_upd ynum_k_11324 (usize 2) (prod_ce(temp_11269, temp_11273
              )))) ;;
      
       '(ynum_k_11324 : seq (fp_t '× fp_t)) ←
        ( '(temp_11275 : seq int8) ←
            (array_to_be_bytes (g2_ynum_k_3_r_v)) ;;
           '(temp_11277 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_11275)) ;;
           '(temp_11279 : fp_t) ←
            (nat_mod_zero ) ;;
          ret (seq_upd ynum_k_11324 (usize 3) (prod_ce(temp_11277, temp_11279
              )))) ;;
      
       '(yden_k_11325 : seq (fp_t '× fp_t)) ←
          ( temp_11281 ←
              (seq_new_ (default : fp2_t) (usize 3)) ;;
            ret (temp_11281)) ;;
        #put yden_k_11325_loc := yden_k_11325 ;;
       '(yden_k_11325 : seq (fp_t '× fp_t)) ←
        ( '(temp_11283 : seq int8) ←
            (array_to_be_bytes (g2_yden_k_0_v)) ;;
           '(temp_11285 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_11283)) ;;
           '(temp_11287 : seq int8) ←
            (array_to_be_bytes (g2_yden_k_0_v)) ;;
           '(temp_11289 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_11287)) ;;
          ret (seq_upd yden_k_11325 (usize 0) (prod_ce(temp_11285, temp_11289
              )))) ;;
      
       '(yden_k_11325 : seq (fp_t '× fp_t)) ←
        ( '(temp_11291 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_11293 : seq int8) ←
            (array_to_be_bytes (g2_yden_k_1_i_v)) ;;
           '(temp_11295 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_11293)) ;;
          ret (seq_upd yden_k_11325 (usize 1) (prod_ce(temp_11291, temp_11295
              )))) ;;
      
       '(yden_k_11325 : seq (fp_t '× fp_t)) ←
        ( '(temp_11297 : fp_t) ←
            (nat_mod_from_literal (_) (@repr U128 18)) ;;
           '(temp_11299 : seq int8) ←
            (array_to_be_bytes (g2_yden_k_2_i_v)) ;;
           '(temp_11301 : fp_t) ←
            (nat_mod_from_byte_seq_be (temp_11299)) ;;
          ret (seq_upd yden_k_11325 (usize 2) (prod_ce(temp_11297, temp_11301
              )))) ;;
      
       '(xnum_11311 : (fp_t '× fp_t)) ←
          ( temp_11303 ←
              (fp2zero ) ;;
            ret (temp_11303)) ;;
        #put xnum_11311_loc := xnum_11311 ;;
       '(xx_11312 : (fp_t '× fp_t)) ←
          ( '(temp_11305 : fp_t) ←
              (nat_mod_one ) ;;
             temp_11307 ←
              (fp2fromfp (temp_11305)) ;;
            ret (temp_11307)) ;;
        #put xx_11312_loc := xx_11312 ;;
       '(temp_11310 : uint_size) ←
        (seq_len (xnum_k_11308)) ;;
       temp_11418 ←
        (foldi' (usize 0) (temp_11310) prod_ce(xnum_11311, xx_11312) (
              L2 := CEfset (
                [xnum_k_11308_loc ; xden_k_11323_loc ; ynum_k_11324_loc ; yden_k_11325_loc ; xnum_11311_loc ; xx_11312_loc ; xden_11334_loc ; xx_11335_loc ; ynum_11355_loc ; xx_11356_loc ; yden_11374_loc ; xx_11375_loc ; inf_11408_loc])) (
              I2 := [interface #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
              #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
              #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
              #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_11313 '(
              xnum_11311,
              xx_11312
            ) =>
            ({ code  '(xnum_11311 : (fp_t '× fp_t)) ←
                  (( '(temp_11315 : (fp_t '× fp_t)) ←
                        (seq_index (xnum_k_11308) (i_11313)) ;;
                       temp_11317 ←
                        (fp2mul (xx_11312) (temp_11315)) ;;
                       temp_11319 ←
                        (fp2add (xnum_11311) (temp_11317)) ;;
                      ret (temp_11319))) ;;
                #put xnum_11311_loc := xnum_11311 ;;
              
               '(xx_11312 : (fp_t '× fp_t)) ←
                  (( temp_11322 ←
                        (fp2mul (xx_11312) (x_11320)) ;;
                      ret (temp_11322))) ;;
                #put xx_11312_loc := xx_11312 ;;
              
              @ret (((fp_t '× fp_t) '× (fp_t '× fp_t))) (prod_ce(
                  xnum_11311,
                  xx_11312
                )) } : code (CEfset (
                  [xnum_k_11308_loc ; xden_k_11323_loc ; ynum_k_11324_loc ; yden_k_11325_loc ; xnum_11311_loc ; xx_11312_loc])) [interface
              #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] _))) ;;
      let '(xnum_11311, xx_11312) :=
        (temp_11418) : ((fp_t '× fp_t) '× (fp_t '× fp_t)) in
      
       '(xden_11334 : (fp_t '× fp_t)) ←
          ( temp_11327 ←
              (fp2zero ) ;;
            ret (temp_11327)) ;;
        #put xden_11334_loc := xden_11334 ;;
       '(xx_11335 : (fp_t '× fp_t)) ←
          ( '(temp_11329 : fp_t) ←
              (nat_mod_one ) ;;
             temp_11331 ←
              (fp2fromfp (temp_11329)) ;;
            ret (temp_11331)) ;;
        #put xx_11335_loc := xx_11335 ;;
       '(temp_11333 : uint_size) ←
        (seq_len (xden_k_11323)) ;;
       temp_11416 ←
        (foldi' (usize 0) (temp_11333) prod_ce(xden_11334, xx_11335) (
              L2 := CEfset (
                [xnum_k_11308_loc ; xden_k_11323_loc ; ynum_k_11324_loc ; yden_k_11325_loc ; xnum_11311_loc ; xx_11312_loc ; xden_11334_loc ; xx_11335_loc ; ynum_11355_loc ; xx_11356_loc ; yden_11374_loc ; xx_11375_loc ; inf_11408_loc])) (
              I2 := [interface #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
              #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
              #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
              #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_11336 '(
              xden_11334,
              xx_11335
            ) =>
            ({ code  '(xden_11334 : (fp_t '× fp_t)) ←
                  (( '(temp_11338 : (fp_t '× fp_t)) ←
                        (seq_index (xden_k_11323) (i_11336)) ;;
                       temp_11340 ←
                        (fp2mul (xx_11335) (temp_11338)) ;;
                       temp_11342 ←
                        (fp2add (xden_11334) (temp_11340)) ;;
                      ret (temp_11342))) ;;
                #put xden_11334_loc := xden_11334 ;;
              
               '(xx_11335 : (fp_t '× fp_t)) ←
                  (( temp_11344 ←
                        (fp2mul (xx_11335) (x_11320)) ;;
                      ret (temp_11344))) ;;
                #put xx_11335_loc := xx_11335 ;;
              
              @ret (((fp_t '× fp_t) '× (fp_t '× fp_t))) (prod_ce(
                  xden_11334,
                  xx_11335
                )) } : code (CEfset (
                  [xnum_k_11308_loc ; xden_k_11323_loc ; ynum_k_11324_loc ; yden_k_11325_loc ; xnum_11311_loc ; xx_11312_loc ; xden_11334_loc ; xx_11335_loc])) [interface
              #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] _))) ;;
      let '(xden_11334, xx_11335) :=
        (temp_11416) : ((fp_t '× fp_t) '× (fp_t '× fp_t)) in
      
       '(xden_11334 : (fp_t '× fp_t)) ←
          (( temp_11346 ←
                (fp2add (xden_11334) (xx_11335)) ;;
              ret (temp_11346))) ;;
        #put xden_11334_loc := xden_11334 ;;
      
       '(ynum_11355 : (fp_t '× fp_t)) ←
          ( temp_11348 ←
              (fp2zero ) ;;
            ret (temp_11348)) ;;
        #put ynum_11355_loc := ynum_11355 ;;
       '(xx_11356 : (fp_t '× fp_t)) ←
          ( '(temp_11350 : fp_t) ←
              (nat_mod_one ) ;;
             temp_11352 ←
              (fp2fromfp (temp_11350)) ;;
            ret (temp_11352)) ;;
        #put xx_11356_loc := xx_11356 ;;
       '(temp_11354 : uint_size) ←
        (seq_len (ynum_k_11324)) ;;
       temp_11414 ←
        (foldi' (usize 0) (temp_11354) prod_ce(ynum_11355, xx_11356) (
              L2 := CEfset (
                [xnum_k_11308_loc ; xden_k_11323_loc ; ynum_k_11324_loc ; yden_k_11325_loc ; xnum_11311_loc ; xx_11312_loc ; xden_11334_loc ; xx_11335_loc ; ynum_11355_loc ; xx_11356_loc ; yden_11374_loc ; xx_11375_loc ; inf_11408_loc])) (
              I2 := [interface #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
              #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
              #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
              #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_11357 '(
              ynum_11355,
              xx_11356
            ) =>
            ({ code  '(ynum_11355 : (fp_t '× fp_t)) ←
                  (( '(temp_11359 : (fp_t '× fp_t)) ←
                        (seq_index (ynum_k_11324) (i_11357)) ;;
                       temp_11361 ←
                        (fp2mul (xx_11356) (temp_11359)) ;;
                       temp_11363 ←
                        (fp2add (ynum_11355) (temp_11361)) ;;
                      ret (temp_11363))) ;;
                #put ynum_11355_loc := ynum_11355 ;;
              
               '(xx_11356 : (fp_t '× fp_t)) ←
                  (( temp_11365 ←
                        (fp2mul (xx_11356) (x_11320)) ;;
                      ret (temp_11365))) ;;
                #put xx_11356_loc := xx_11356 ;;
              
              @ret (((fp_t '× fp_t) '× (fp_t '× fp_t))) (prod_ce(
                  ynum_11355,
                  xx_11356
                )) } : code (CEfset (
                  [xnum_k_11308_loc ; xden_k_11323_loc ; ynum_k_11324_loc ; yden_k_11325_loc ; xnum_11311_loc ; xx_11312_loc ; xden_11334_loc ; xx_11335_loc ; ynum_11355_loc ; xx_11356_loc])) [interface
              #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] _))) ;;
      let '(ynum_11355, xx_11356) :=
        (temp_11414) : ((fp_t '× fp_t) '× (fp_t '× fp_t)) in
      
       '(yden_11374 : (fp_t '× fp_t)) ←
          ( temp_11367 ←
              (fp2zero ) ;;
            ret (temp_11367)) ;;
        #put yden_11374_loc := yden_11374 ;;
       '(xx_11375 : (fp_t '× fp_t)) ←
          ( '(temp_11369 : fp_t) ←
              (nat_mod_one ) ;;
             temp_11371 ←
              (fp2fromfp (temp_11369)) ;;
            ret (temp_11371)) ;;
        #put xx_11375_loc := xx_11375 ;;
       '(temp_11373 : uint_size) ←
        (seq_len (yden_k_11325)) ;;
       temp_11412 ←
        (foldi' (usize 0) (temp_11373) prod_ce(yden_11374, xx_11375) (
              L2 := CEfset (
                [xnum_k_11308_loc ; xden_k_11323_loc ; ynum_k_11324_loc ; yden_k_11325_loc ; xnum_11311_loc ; xx_11312_loc ; xden_11334_loc ; xx_11335_loc ; ynum_11355_loc ; xx_11356_loc ; yden_11374_loc ; xx_11375_loc ; inf_11408_loc])) (
              I2 := [interface #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
              #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
              #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
              #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_11376 '(
              yden_11374,
              xx_11375
            ) =>
            ({ code  '(yden_11374 : (fp_t '× fp_t)) ←
                  (( '(temp_11378 : (fp_t '× fp_t)) ←
                        (seq_index (yden_k_11325) (i_11376)) ;;
                       temp_11380 ←
                        (fp2mul (xx_11375) (temp_11378)) ;;
                       temp_11382 ←
                        (fp2add (yden_11374) (temp_11380)) ;;
                      ret (temp_11382))) ;;
                #put yden_11374_loc := yden_11374 ;;
              
               '(xx_11375 : (fp_t '× fp_t)) ←
                  (( temp_11384 ←
                        (fp2mul (xx_11375) (x_11320)) ;;
                      ret (temp_11384))) ;;
                #put xx_11375_loc := xx_11375 ;;
              
              @ret (((fp_t '× fp_t) '× (fp_t '× fp_t))) (prod_ce(
                  yden_11374,
                  xx_11375
                )) } : code (CEfset (
                  [xnum_k_11308_loc ; xden_k_11323_loc ; ynum_k_11324_loc ; yden_k_11325_loc ; xnum_11311_loc ; xx_11312_loc ; xden_11334_loc ; xx_11335_loc ; ynum_11355_loc ; xx_11356_loc ; yden_11374_loc ; xx_11375_loc])) [interface
              #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] _))) ;;
      let '(yden_11374, xx_11375) :=
        (temp_11412) : ((fp_t '× fp_t) '× (fp_t '× fp_t)) in
      
       '(yden_11374 : (fp_t '× fp_t)) ←
          (( temp_11386 ←
                (fp2add (yden_11374) (xx_11375)) ;;
              ret (temp_11386))) ;;
        #put yden_11374_loc := yden_11374 ;;
      
       '(xr_11409 : (fp_t '× fp_t)) ←
        ( temp_11388 ←
            (fp2inv (xden_11334)) ;;
           temp_11390 ←
            (fp2mul (xnum_11311) (temp_11388)) ;;
          ret (temp_11390)) ;;
       '(yr_11410 : (fp_t '× fp_t)) ←
        ( temp_11393 ←
            (fp2inv (yden_11374)) ;;
           temp_11395 ←
            (fp2mul (ynum_11355) (temp_11393)) ;;
           temp_11397 ←
            (fp2mul (y_11391) (temp_11395)) ;;
          ret (temp_11397)) ;;
       '(inf_11408 : bool_ChoiceEquality) ←
          (ret ((false : bool_ChoiceEquality))) ;;
        #put inf_11408_loc := inf_11408 ;;
       temp_11399 ←
        (fp2zero ) ;;
       '(temp_11401 : bool_ChoiceEquality) ←
        ((xden_11334) =.? (temp_11399)) ;;
       temp_11403 ←
        (fp2zero ) ;;
       '(temp_11405 : bool_ChoiceEquality) ←
        ((yden_11374) =.? (temp_11403)) ;;
       '(temp_11407 : bool_ChoiceEquality) ←
        ((temp_11401) || (temp_11405)) ;;
       '(inf_11408 : (bool_ChoiceEquality)) ←
        (if temp_11407:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(
                  inf_11408 : bool_ChoiceEquality) ←
                ((ret ((true : bool_ChoiceEquality)))) ;;
              #put inf_11408_loc := inf_11408 ;;
            
            @ret ((bool_ChoiceEquality)) (inf_11408) in
            ({ code temp_then } : code (CEfset (
                  [xnum_k_11308_loc ; xden_k_11323_loc ; ynum_k_11324_loc ; yden_k_11325_loc ; xnum_11311_loc ; xx_11312_loc ; xden_11334_loc ; xx_11335_loc ; ynum_11355_loc ; xx_11356_loc ; yden_11374_loc ; xx_11375_loc ; inf_11408_loc])) [interface] _))
          else @ret ((bool_ChoiceEquality)) (inf_11408)) ;;
      
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality)) (
        prod_ce(xr_11409, yr_11410, inf_11408)) } : code (CEfset (
          [xnum_k_11308_loc ; xden_k_11323_loc ; ynum_k_11324_loc ; yden_k_11325_loc ; xnum_11311_loc ; xx_11312_loc ; xden_11334_loc ; xx_11335_loc ; ynum_11355_loc ; xx_11356_loc ; yden_11374_loc ; xx_11375_loc ; inf_11408_loc])) [interface
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
  (11443).
Program Definition g2_map_to_curve_sswu
   : package (CEfset ([])) [interface
  #val #[ G2_ISOGENY_MAP ] : g2_isogeny_map_inp → g2_isogeny_map_out ;
  #val #[ G2_SIMPLE_SWU_ISO ] : g2_simple_swu_iso_inp → g2_simple_swu_iso_out
  ] [interface
  #val #[ G2_MAP_TO_CURVE_SSWU ] : g2_map_to_curve_sswu_inp → g2_map_to_curve_sswu_out
  ] :=
  (
    [package #def #[ G2_MAP_TO_CURVE_SSWU ] (temp_inp : g2_map_to_curve_sswu_inp) : g2_map_to_curve_sswu_out { 
    let '(u_11433) := temp_inp : fp2_t in
    #import {sig #[ G2_ISOGENY_MAP ] : g2_isogeny_map_inp → g2_isogeny_map_out } as g2_isogeny_map ;;
    let g2_isogeny_map := fun x_0 x_1 => g2_isogeny_map (x_0,x_1) in
    #import {sig #[ G2_SIMPLE_SWU_ISO ] : g2_simple_swu_iso_inp → g2_simple_swu_iso_out } as g2_simple_swu_iso ;;
    let g2_simple_swu_iso := fun x_0 => g2_simple_swu_iso (x_0) in
    ({ code  temp_11442 ←
        ( '(temp_11435 : (fp2_t '× fp2_t)) ←
            (g2_simple_swu_iso (u_11433)) ;;
          ret (temp_11435)) ;;
      let '(xp_11436, yp_11437) :=
        (temp_11442) : (fp2_t '× fp2_t) in
       '(p_11440 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_11439 : g2_t) ←
            (g2_isogeny_map (xp_11436) (yp_11437)) ;;
          ret (temp_11439)) ;;
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality)) (
        p_11440) } : code (CEfset ([])) [interface
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
  (11465).
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
    let '(msg_11444 , dst_11445) := temp_inp : byte_seq '× byte_seq in
    #import {sig #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out } as fp2_hash_to_field ;;
    let fp2_hash_to_field := fun x_0 x_1 x_2 => fp2_hash_to_field (
      x_0,x_1,x_2) in
    #import {sig #[ G2_CLEAR_COFACTOR ] : g2_clear_cofactor_inp → g2_clear_cofactor_out } as g2_clear_cofactor ;;
    let g2_clear_cofactor := fun x_0 => g2_clear_cofactor (x_0) in
    #import {sig #[ G2_MAP_TO_CURVE_SSWU ] : g2_map_to_curve_sswu_inp → g2_map_to_curve_sswu_out } as g2_map_to_curve_sswu ;;
    let g2_map_to_curve_sswu := fun x_0 => g2_map_to_curve_sswu (x_0) in
    #import {sig #[ G2ADD ] : g2add_inp → g2add_out } as g2add ;;
    let g2add := fun x_0 x_1 => g2add (x_0,x_1) in
    ({ code  '(u_11449 : seq fp2_t) ←
        ( '(temp_11447 : seq fp2_t) ←
            (fp2_hash_to_field (msg_11444) (dst_11445) (usize 2)) ;;
          ret (temp_11447)) ;;
       '(q0_11457 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_11450 : fp2_t) ←
            (seq_index (u_11449) (usize 0)) ;;
           '(temp_11452 : g2_t) ←
            (g2_map_to_curve_sswu (temp_11450)) ;;
          ret (temp_11452)) ;;
       '(q1_11458 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_11454 : fp2_t) ←
            (seq_index (u_11449) (usize 1)) ;;
           '(temp_11456 : g2_t) ←
            (g2_map_to_curve_sswu (temp_11454)) ;;
          ret (temp_11456)) ;;
       '(r_11461 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( temp_11460 ←
            (g2add (q0_11457) (q1_11458)) ;;
          ret (temp_11460)) ;;
       '(p_11464 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_11463 : g2_t) ←
            (g2_clear_cofactor (r_11461)) ;;
          ret (temp_11463)) ;;
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality)) (
        p_11464) } : code (CEfset ([])) [interface
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
  (11479).
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
    let '(msg_11466 , dst_11467) := temp_inp : byte_seq '× byte_seq in
    #import {sig #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out } as fp2_hash_to_field ;;
    let fp2_hash_to_field := fun x_0 x_1 x_2 => fp2_hash_to_field (
      x_0,x_1,x_2) in
    #import {sig #[ G2_CLEAR_COFACTOR ] : g2_clear_cofactor_inp → g2_clear_cofactor_out } as g2_clear_cofactor ;;
    let g2_clear_cofactor := fun x_0 => g2_clear_cofactor (x_0) in
    #import {sig #[ G2_MAP_TO_CURVE_SSWU ] : g2_map_to_curve_sswu_inp → g2_map_to_curve_sswu_out } as g2_map_to_curve_sswu ;;
    let g2_map_to_curve_sswu := fun x_0 => g2_map_to_curve_sswu (x_0) in
    ({ code  '(u_11471 : seq fp2_t) ←
        ( '(temp_11469 : seq fp2_t) ←
            (fp2_hash_to_field (msg_11466) (dst_11467) (usize 1)) ;;
          ret (temp_11469)) ;;
       '(q_11475 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_11472 : fp2_t) ←
            (seq_index (u_11471) (usize 0)) ;;
           '(temp_11474 : g2_t) ←
            (g2_map_to_curve_sswu (temp_11472)) ;;
          ret (temp_11474)) ;;
       '(p_11478 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
          )) ←
        ( '(temp_11477 : g2_t) ←
            (g2_clear_cofactor (q_11475)) ;;
          ret (temp_11477)) ;;
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality)) (
        p_11478) } : code (CEfset ([])) [interface
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

