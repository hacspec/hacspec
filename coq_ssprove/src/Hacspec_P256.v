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

Obligation Tactic := try timeout 40 solve_ssprove_obligations.
Require Import Hacspec_Lib.

Definition error_t : ChoiceEquality :=
  (unit_ChoiceEquality).
Definition InvalidAddition : error_t :=
  ( tt).

Definition bits_v : (uint_size) :=
  ((usize 256)).

Definition field_canvas_t  :=
  (nseq (int8) (32)).
Definition p256_field_element_t  :=
  (nat_mod 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff).

Definition scalar_canvas_t  :=
  (nseq (int8) (32)).
Definition p256_scalar_t  :=
  (nat_mod 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551).

Notation "'affine_t'" := ((p256_field_element_t '× p256_field_element_t
)) : hacspec_scope.

Notation "'affine_result_t'" := ((result error_t affine_t)) : hacspec_scope.

Notation "'p256_jacobian_t'" := ((
  p256_field_element_t '×
  p256_field_element_t '×
  p256_field_element_t
)) : hacspec_scope.

Notation "'jacobian_result_t'" := ((
  result error_t p256_jacobian_t)) : hacspec_scope.

Definition element_t  :=
  ( nseq (uint8) (usize 32)).


Notation "'jacobian_to_affine_inp'" := (
  p256_jacobian_t : choice_type) (in custom pack_type at level 2).
Notation "'jacobian_to_affine_out'" := (
  affine_t : choice_type) (in custom pack_type at level 2).
Definition JACOBIAN_TO_AFFINE : nat :=
  (2936).
Program Definition jacobian_to_affine
   : package (fset.fset0) [interface] [interface
  #val #[ JACOBIAN_TO_AFFINE ] : jacobian_to_affine_inp → jacobian_to_affine_out
  ] :=
  (
    [package #def #[ JACOBIAN_TO_AFFINE ] (temp_inp : jacobian_to_affine_inp) : jacobian_to_affine_out { 
    let '(p_2912) := temp_inp : p256_jacobian_t in
    ({ code  temp_2935 ←
        (ret (p_2912)) ;;
      let '(x_2924, y_2928, z_2913) :=
        (temp_2935) : (
        p256_field_element_t '×
        p256_field_element_t '×
        p256_field_element_t
      ) in
       '(z2_2916 : p256_field_element_t) ←
        ( temp_2915 ←
            (nat_mod_exp (z_2913) (@repr U32 2)) ;;
          ret (temp_2915)) ;;
       '(z2i_2925 : p256_field_element_t) ←
        ( temp_2918 ←
            (nat_mod_inv (z2_2916)) ;;
          ret (temp_2918)) ;;
       '(z3_2921 : p256_field_element_t) ←
        ( '(temp_2920 : p256_field_element_t) ←
            ((z_2913) *% (z2_2916)) ;;
          ret (temp_2920)) ;;
       '(z3i_2929 : p256_field_element_t) ←
        ( temp_2923 ←
            (nat_mod_inv (z3_2921)) ;;
          ret (temp_2923)) ;;
       '(x_2932 : p256_field_element_t) ←
        ( '(temp_2927 : p256_field_element_t) ←
            ((x_2924) *% (z2i_2925)) ;;
          ret (temp_2927)) ;;
       '(y_2933 : p256_field_element_t) ←
        ( '(temp_2931 : p256_field_element_t) ←
            ((y_2928) *% (z3i_2929)) ;;
          ret (temp_2931)) ;;
      @ret ((p256_field_element_t '× p256_field_element_t)) (prod_ce(
          x_2932,
          y_2933
        )) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_jacobian_to_affine : package _ _ _ :=
  (jacobian_to_affine).
Fail Next Obligation.


Notation "'affine_to_jacobian_inp'" := (
  affine_t : choice_type) (in custom pack_type at level 2).
Notation "'affine_to_jacobian_out'" := (
  p256_jacobian_t : choice_type) (in custom pack_type at level 2).
Definition AFFINE_TO_JACOBIAN : nat :=
  (2944).
Program Definition affine_to_jacobian
   : package (fset.fset0) [interface] [interface
  #val #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out
  ] :=
  (
    [package #def #[ AFFINE_TO_JACOBIAN ] (temp_inp : affine_to_jacobian_inp) : affine_to_jacobian_out { 
    let '(p_2937) := temp_inp : affine_t in
    ({ code  temp_2943 ←
        (ret (p_2937)) ;;
      let '(x_2938, y_2939) :=
        (temp_2943) : (p256_field_element_t '× p256_field_element_t) in
       '(temp_2941 : p256_field_element_t) ←
        (nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            @repr U128 1)) ;;
      @ret ((
          p256_field_element_t '×
          p256_field_element_t '×
          p256_field_element_t
        )) (prod_ce(x_2938, y_2939, temp_2941)) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_affine_to_jacobian : package _ _ _ :=
  (affine_to_jacobian).
Fail Next Obligation.


Notation "'point_double_inp'" := (
  p256_jacobian_t : choice_type) (in custom pack_type at level 2).
Notation "'point_double_out'" := (
  p256_jacobian_t : choice_type) (in custom pack_type at level 2).
Definition POINT_DOUBLE : nat :=
  (3011).
Program Definition point_double
   : package (fset.fset0) [interface] [interface
  #val #[ POINT_DOUBLE ] : point_double_inp → point_double_out ] :=
  (
    [package #def #[ POINT_DOUBLE ] (temp_inp : point_double_inp) : point_double_out { 
    let '(p_2945) := temp_inp : p256_jacobian_t in
    ({ code  temp_3010 ←
        (ret (p_2945)) ;;
      let '(x1_2952, y1_2949, z1_2946) :=
        (temp_3010) : (
        p256_field_element_t '×
        p256_field_element_t '×
        p256_field_element_t
      ) in
       '(delta_2956 : p256_field_element_t) ←
        ( temp_2948 ←
            (nat_mod_exp (z1_2946) (@repr U32 2)) ;;
          ret (temp_2948)) ;;
       '(gamma_2953 : p256_field_element_t) ←
        ( temp_2951 ←
            (nat_mod_exp (y1_2949) (@repr U32 2)) ;;
          ret (temp_2951)) ;;
       '(beta_2974 : p256_field_element_t) ←
        ( '(temp_2955 : p256_field_element_t) ←
            ((x1_2952) *% (gamma_2953)) ;;
          ret (temp_2955)) ;;
       '(alpha_1_2963 : p256_field_element_t) ←
        ( '(temp_2958 : p256_field_element_t) ←
            ((x1_2952) -% (delta_2956)) ;;
          ret (temp_2958)) ;;
       '(alpha_2_2964 : p256_field_element_t) ←
        ( '(temp_2960 : p256_field_element_t) ←
            ((x1_2952) +% (delta_2956)) ;;
          ret (temp_2960)) ;;
       '(alpha_2969 : p256_field_element_t) ←
        ( '(temp_2962 : p256_field_element_t) ←
            (nat_mod_from_literal (
                0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                @repr U128 3)) ;;
           '(temp_2966 : p256_field_element_t) ←
            ((alpha_1_2963) *% (alpha_2_2964)) ;;
           '(temp_2968 : p256_field_element_t) ←
            ((temp_2962) *% (temp_2966)) ;;
          ret (temp_2968)) ;;
       '(x3_2992 : p256_field_element_t) ←
        ( temp_2971 ←
            (nat_mod_exp (alpha_2969) (@repr U32 2)) ;;
           '(temp_2973 : p256_field_element_t) ←
            (nat_mod_from_literal (
                0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                @repr U128 8)) ;;
           '(temp_2976 : p256_field_element_t) ←
            ((temp_2973) *% (beta_2974)) ;;
           '(temp_2978 : p256_field_element_t) ←
            ((temp_2971) -% (temp_2976)) ;;
          ret (temp_2978)) ;;
       '(z3_2983 : p256_field_element_t) ←
        ( '(temp_2980 : p256_field_element_t) ←
            ((y1_2949) +% (z1_2946)) ;;
           temp_2982 ←
            (nat_mod_exp (temp_2980) (@repr U32 2)) ;;
          ret (temp_2982)) ;;
       '(z3_3008 : p256_field_element_t) ←
        ( '(temp_2985 : p256_field_element_t) ←
            ((gamma_2953) +% (delta_2956)) ;;
           '(temp_2987 : p256_field_element_t) ←
            ((z3_2983) -% (temp_2985)) ;;
          ret (temp_2987)) ;;
       '(y3_1_3001 : p256_field_element_t) ←
        ( '(temp_2989 : p256_field_element_t) ←
            (nat_mod_from_literal (
                0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                @repr U128 4)) ;;
           '(temp_2991 : p256_field_element_t) ←
            ((temp_2989) *% (beta_2974)) ;;
           '(temp_2994 : p256_field_element_t) ←
            ((temp_2991) -% (x3_2992)) ;;
          ret (temp_2994)) ;;
       '(y3_2_3004 : p256_field_element_t) ←
        ( '(temp_2996 : p256_field_element_t) ←
            (nat_mod_from_literal (
                0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                @repr U128 8)) ;;
           '(temp_2998 : p256_field_element_t) ←
            ((gamma_2953) *% (gamma_2953)) ;;
           '(temp_3000 : p256_field_element_t) ←
            ((temp_2996) *% (temp_2998)) ;;
          ret (temp_3000)) ;;
       '(y3_3007 : p256_field_element_t) ←
        ( '(temp_3003 : p256_field_element_t) ←
            ((alpha_2969) *% (y3_1_3001)) ;;
           '(temp_3006 : p256_field_element_t) ←
            ((temp_3003) -% (y3_2_3004)) ;;
          ret (temp_3006)) ;;
      @ret ((
          p256_field_element_t '×
          p256_field_element_t '×
          p256_field_element_t
        )) (prod_ce(x3_2992, y3_3007, z3_3008)) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_point_double : package _ _ _ :=
  (point_double).
Fail Next Obligation.


Notation "'is_point_at_infinity_inp'" := (
  p256_jacobian_t : choice_type) (in custom pack_type at level 2).
Notation "'is_point_at_infinity_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition IS_POINT_AT_INFINITY : nat :=
  (3022).
Program Definition is_point_at_infinity
   : package (fset.fset0) [interface] [interface
  #val #[ IS_POINT_AT_INFINITY ] : is_point_at_infinity_inp → is_point_at_infinity_out
  ] :=
  (
    [package #def #[ IS_POINT_AT_INFINITY ] (temp_inp : is_point_at_infinity_inp) : is_point_at_infinity_out { 
    let '(p_3012) := temp_inp : p256_jacobian_t in
    ({ code  temp_3019 ←
        (ret (p_3012)) ;;
      let '(x_3020, y_3021, z_3013) :=
        (temp_3019) : (
        p256_field_element_t '×
        p256_field_element_t '×
        p256_field_element_t
      ) in
       '(temp_3015 : p256_field_element_t) ←
        (nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            @repr U128 0)) ;;
       temp_3017 ←
        (nat_mod_equal (z_3013) (temp_3015)) ;;
      @ret (bool_ChoiceEquality) (temp_3017) } : code (
        fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_is_point_at_infinity : package _ _ _ :=
  (is_point_at_infinity).
Fail Next Obligation.


Notation "'s1_equal_s2_inp'" := (
  p256_field_element_t '× p256_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'s1_equal_s2_out'" := (
  jacobian_result_t : choice_type) (in custom pack_type at level 2).
Definition S1_EQUAL_S2 : nat :=
  (3033).
Program Definition s1_equal_s2
   : package (fset.fset0) [interface] [interface
  #val #[ S1_EQUAL_S2 ] : s1_equal_s2_inp → s1_equal_s2_out ] :=
  (
    [package #def #[ S1_EQUAL_S2 ] (temp_inp : s1_equal_s2_inp) : s1_equal_s2_out { 
    let '(
      s1_3023 , s2_3024) := temp_inp : p256_field_element_t '× p256_field_element_t in
    ({ code  temp_3026 ←
        (nat_mod_equal (s1_3023) (s2_3024)) ;;
       '(temp_3028 : p256_field_element_t) ←
        (nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            @repr U128 0)) ;;
       '(temp_3030 : p256_field_element_t) ←
        (nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            @repr U128 1)) ;;
       '(temp_3032 : p256_field_element_t) ←
        (nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            @repr U128 0)) ;;
      @ret ((result error_t p256_jacobian_t)) ((if (
            temp_3026):bool_ChoiceEquality then (*inline*) (
            @inr p256_jacobian_t error_t (InvalidAddition)) else (
            @inl p256_jacobian_t error_t (prod_ce(
                temp_3028,
                temp_3030,
                temp_3032
              ))))) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_s1_equal_s2 : package _ _ _ :=
  (s1_equal_s2).
Fail Next Obligation.

Definition result_3040_loc : ChoiceEqualityLocation :=
  (((result error_t p256_jacobian_t) ; 3140%nat)).
Notation "'point_add_jacob_inp'" := (
  p256_jacobian_t '× p256_jacobian_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_jacob_out'" := (
  jacobian_result_t : choice_type) (in custom pack_type at level 2).
Definition POINT_ADD_JACOB : nat :=
  (3141).
Program Definition point_add_jacob
   : package (CEfset ([result_3040_loc])) [interface
  #val #[ IS_POINT_AT_INFINITY ] : is_point_at_infinity_inp → is_point_at_infinity_out ;
  #val #[ S1_EQUAL_S2 ] : s1_equal_s2_inp → s1_equal_s2_out ] [interface
  #val #[ POINT_ADD_JACOB ] : point_add_jacob_inp → point_add_jacob_out ] :=
  (
    [package #def #[ POINT_ADD_JACOB ] (temp_inp : point_add_jacob_inp) : point_add_jacob_out { 
    let '(p_3035 , q_3034) := temp_inp : p256_jacobian_t '× p256_jacobian_t in
    #import {sig #[ IS_POINT_AT_INFINITY ] : is_point_at_infinity_inp → is_point_at_infinity_out } as is_point_at_infinity ;;
    let is_point_at_infinity := fun x_0 => is_point_at_infinity (x_0) in
    #import {sig #[ S1_EQUAL_S2 ] : s1_equal_s2_inp → s1_equal_s2_out } as s1_equal_s2 ;;
    let s1_equal_s2 := fun x_0 x_1 => s1_equal_s2 (x_0,x_1) in
    ({ code  '(result_3040 : (result error_t p256_jacobian_t)) ←
             (ret (@inl p256_jacobian_t error_t (q_3034) : result error_t p256_jacobian_t)) ;;
        #put result_3040_loc := result_3040 ;;
       '(temp_3037 : bool_ChoiceEquality) ←
        (is_point_at_infinity (p_3035)) ;;
       '(result_3040 : ((result error_t p256_jacobian_t))) ←
        (if negb (temp_3037):bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(
                temp_3039 : bool_ChoiceEquality) ←
              (is_point_at_infinity (q_3034)) ;;
             '(result_3040 : ((result error_t p256_jacobian_t))) ←
              (if temp_3039:bool_ChoiceEquality
                then (*not state*) (let temp_then :=  '(result_3040 : (
                          result error_t p256_jacobian_t)) ←
                      ((ret (@inl p256_jacobian_t error_t (p_3035) : result error_t p256_jacobian_t))) ;;
                    #put result_3040_loc := result_3040 ;;
                  
                  @ret (((result error_t p256_jacobian_t))) (result_3040) in
                  ({ code temp_then } : code (CEfset (
                        [result_3040_loc])) [interface] _))
                else  (({ code  temp_3139 ←
                      (ret (p_3035)) ;;
                    let '(x1_3047, y1_3055, z1_3041) :=
                      (temp_3139) : (
                      p256_field_element_t '×
                      p256_field_element_t '×
                      p256_field_element_t
                    ) in
                     temp_3137 ←
                      (ret (q_3034)) ;;
                    let '(x2_3051, y2_3060, z2_3044) :=
                      (temp_3137) : (
                      p256_field_element_t '×
                      p256_field_element_t '×
                      p256_field_element_t
                    ) in
                     '(z1z1_3052 : p256_field_element_t) ←
                      ( temp_3043 ←
                          (nat_mod_exp (z1_3041) (@repr U32 2)) ;;
                        ret (temp_3043)) ;;
                     '(z2z2_3048 : p256_field_element_t) ←
                      ( temp_3046 ←
                          (nat_mod_exp (z2_3044) (@repr U32 2)) ;;
                        ret (temp_3046)) ;;
                     '(u1_3065 : p256_field_element_t) ←
                      ( '(temp_3050 : p256_field_element_t) ←
                          ((x1_3047) *% (z2z2_3048)) ;;
                        ret (temp_3050)) ;;
                     '(u2_3066 : p256_field_element_t) ←
                      ( '(temp_3054 : p256_field_element_t) ←
                          ((x2_3051) *% (z1z1_3052)) ;;
                        ret (temp_3054)) ;;
                     '(s1_3069 : p256_field_element_t) ←
                      ( '(temp_3057 : p256_field_element_t) ←
                          ((y1_3055) *% (z2_3044)) ;;
                         '(temp_3059 : p256_field_element_t) ←
                          ((temp_3057) *% (z2z2_3048)) ;;
                        ret (temp_3059)) ;;
                     '(s2_3070 : p256_field_element_t) ←
                      ( '(temp_3062 : p256_field_element_t) ←
                          ((y2_3060) *% (z1_3041)) ;;
                         '(temp_3064 : p256_field_element_t) ←
                          ((temp_3062) *% (z1z1_3052)) ;;
                        ret (temp_3064)) ;;
                     temp_3068 ←
                      (nat_mod_equal (u1_3065) (u2_3066)) ;;
                     '(result_3040 : ((result error_t p256_jacobian_t))) ←
                      (if temp_3068:bool_ChoiceEquality
                        then (*not state*) (let temp_then :=  '(result_3040 : (
                                  result error_t p256_jacobian_t)) ←
                              (( '(temp_3072 : jacobian_result_t) ←
                                    (s1_equal_s2 (s1_3069) (s2_3070)) ;;
                                  ret (temp_3072))) ;;
                            #put result_3040_loc := result_3040 ;;
                          
                          @ret (((result error_t p256_jacobian_t))) (
                            result_3040) in
                          ({ code temp_then } : code (CEfset (
                                [result_3040_loc])) [interface
                            #val #[ S1_EQUAL_S2 ] : s1_equal_s2_inp → s1_equal_s2_out
                            ] _))
                        else  (({ code  '(h_3077 : p256_field_element_t) ←
                              ( '(temp_3074 : p256_field_element_t) ←
                                  ((u2_3066) -% (u1_3065)) ;;
                                ret (temp_3074)) ;;
                             '(i_3082 : p256_field_element_t) ←
                              ( '(temp_3076 : p256_field_element_t) ←
                                  (nat_mod_from_literal (
                                      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                                      @repr U128 2)) ;;
                                 '(temp_3079 : p256_field_element_t) ←
                                  ((temp_3076) *% (h_3077)) ;;
                                 temp_3081 ←
                                  (nat_mod_exp (temp_3079) (@repr U32 2)) ;;
                                ret (temp_3081)) ;;
                             '(j_3101 : p256_field_element_t) ←
                              ( '(temp_3084 : p256_field_element_t) ←
                                  ((h_3077) *% (i_3082)) ;;
                                ret (temp_3084)) ;;
                             '(r_3098 : p256_field_element_t) ←
                              ( '(temp_3086 : p256_field_element_t) ←
                                  (nat_mod_from_literal (
                                      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                                      @repr U128 2)) ;;
                                 '(temp_3088 : p256_field_element_t) ←
                                  ((s2_3070) -% (s1_3069)) ;;
                                 '(temp_3090 : p256_field_element_t) ←
                                  ((temp_3086) *% (temp_3088)) ;;
                                ret (temp_3090)) ;;
                             '(v_3095 : p256_field_element_t) ←
                              ( '(temp_3092 : p256_field_element_t) ←
                                  ((u1_3065) *% (i_3082)) ;;
                                ret (temp_3092)) ;;
                             '(x3_1_3105 : p256_field_element_t) ←
                              ( '(temp_3094 : p256_field_element_t) ←
                                  (nat_mod_from_literal (
                                      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                                      @repr U128 2)) ;;
                                 '(temp_3097 : p256_field_element_t) ←
                                  ((temp_3094) *% (v_3095)) ;;
                                ret (temp_3097)) ;;
                             '(x3_2_3104 : p256_field_element_t) ←
                              ( temp_3100 ←
                                  (nat_mod_exp (r_3098) (@repr U32 2)) ;;
                                 '(temp_3103 : p256_field_element_t) ←
                                  ((temp_3100) -% (j_3101)) ;;
                                ret (temp_3103)) ;;
                             '(x3_3114 : p256_field_element_t) ←
                              ( '(temp_3107 : p256_field_element_t) ←
                                  ((x3_2_3104) -% (x3_1_3105)) ;;
                                ret (temp_3107)) ;;
                             '(y3_1_3120 : p256_field_element_t) ←
                              ( '(temp_3109 : p256_field_element_t) ←
                                  (nat_mod_from_literal (
                                      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                                      @repr U128 2)) ;;
                                 '(temp_3111 : p256_field_element_t) ←
                                  ((temp_3109) *% (s1_3069)) ;;
                                 '(temp_3113 : p256_field_element_t) ←
                                  ((temp_3111) *% (j_3101)) ;;
                                ret (temp_3113)) ;;
                             '(y3_2_3119 : p256_field_element_t) ←
                              ( '(temp_3116 : p256_field_element_t) ←
                                  ((v_3095) -% (x3_3114)) ;;
                                 '(temp_3118 : p256_field_element_t) ←
                                  ((r_3098) *% (temp_3116)) ;;
                                ret (temp_3118)) ;;
                             '(y3_3134 : p256_field_element_t) ←
                              ( '(temp_3122 : p256_field_element_t) ←
                                  ((y3_2_3119) -% (y3_1_3120)) ;;
                                ret (temp_3122)) ;;
                             '(z3_3127 : p256_field_element_t) ←
                              ( '(temp_3124 : p256_field_element_t) ←
                                  ((z1_3041) +% (z2_3044)) ;;
                                 temp_3126 ←
                                  (nat_mod_exp (temp_3124) (@repr U32 2)) ;;
                                ret (temp_3126)) ;;
                             '(z3_3135 : p256_field_element_t) ←
                              ( '(temp_3129 : p256_field_element_t) ←
                                  ((z1z1_3052) +% (z2z2_3048)) ;;
                                 '(temp_3131 : p256_field_element_t) ←
                                  ((z3_3127) -% (temp_3129)) ;;
                                 '(temp_3133 : p256_field_element_t) ←
                                  ((temp_3131) *% (h_3077)) ;;
                                ret (temp_3133)) ;;
                             '(result_3040 : (
                                    result error_t p256_jacobian_t)) ←
                                ((ret (@inl p256_jacobian_t error_t (prod_ce(
                                          x3_3114,
                                          y3_3134,
                                          z3_3135
                                        )) : result error_t p256_jacobian_t))) ;;
                              #put result_3040_loc := result_3040 ;;
                            
                            @ret (((result error_t p256_jacobian_t))) (
                              result_3040) } : code (CEfset (
                                [result_3040_loc])) [interface] _))) ;;
                    
                    @ret (((result error_t p256_jacobian_t))) (
                      result_3040) } : code (CEfset (
                        [result_3040_loc])) [interface
                    #val #[ S1_EQUAL_S2 ] : s1_equal_s2_inp → s1_equal_s2_out
                    ] _))) ;;
            
            @ret (((result error_t p256_jacobian_t))) (result_3040) in
            ({ code temp_then } : code (CEfset ([result_3040_loc])) [interface
              #val #[ IS_POINT_AT_INFINITY ] : is_point_at_infinity_inp → is_point_at_infinity_out ;
              #val #[ S1_EQUAL_S2 ] : s1_equal_s2_inp → s1_equal_s2_out ] _))
          else @ret (((result error_t p256_jacobian_t))) (result_3040)) ;;
      
      @ret ((result error_t p256_jacobian_t)) (result_3040) } : code (CEfset (
          [result_3040_loc])) [interface
      #val #[ IS_POINT_AT_INFINITY ] : is_point_at_infinity_inp → is_point_at_infinity_out ;
      #val #[ S1_EQUAL_S2 ] : s1_equal_s2_inp → s1_equal_s2_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_point_add_jacob : package _ _ _ :=
  (seq_link point_add_jacob link_rest(
      package_is_point_at_infinity,package_s1_equal_s2)).
Fail Next Obligation.

Definition q_3148_loc : ChoiceEqualityLocation :=
  (((p256_field_element_t '× p256_field_element_t '× p256_field_element_t
      ) ; 3166%nat)).
Notation "'ltr_mul_inp'" := (
  p256_scalar_t '× p256_jacobian_t : choice_type) (in custom pack_type at level 2).
Notation "'ltr_mul_out'" := (
  jacobian_result_t : choice_type) (in custom pack_type at level 2).
Definition LTR_MUL : nat :=
  (3167).
Program Definition ltr_mul
   : package (CEfset ([q_3148_loc])) [interface
  #val #[ POINT_ADD_JACOB ] : point_add_jacob_inp → point_add_jacob_out ;
  #val #[ POINT_DOUBLE ] : point_double_inp → point_double_out ] [interface
  #val #[ LTR_MUL ] : ltr_mul_inp → ltr_mul_out ] :=
  ([package #def #[ LTR_MUL ] (temp_inp : ltr_mul_inp) : ltr_mul_out { 
    let '(k_3151 , p_3163) := temp_inp : p256_scalar_t '× p256_jacobian_t in
    #import {sig #[ POINT_ADD_JACOB ] : point_add_jacob_inp → point_add_jacob_out } as point_add_jacob ;;
    let point_add_jacob := fun x_0 x_1 => point_add_jacob (x_0,x_1) in
    #import {sig #[ POINT_DOUBLE ] : point_double_inp → point_double_out } as point_double ;;
    let point_double := fun x_0 => point_double (x_0) in
    ({ code  '(q_3148 : (
              p256_field_element_t '×
              p256_field_element_t '×
              p256_field_element_t
            )) ←
          ( '(temp_3143 : p256_field_element_t) ←
              (nat_mod_from_literal (
                  0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                  @repr U128 0)) ;;
             '(temp_3145 : p256_field_element_t) ←
              (nat_mod_from_literal (
                  0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                  @repr U128 1)) ;;
             '(temp_3147 : p256_field_element_t) ←
              (nat_mod_from_literal (
                  0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                  @repr U128 0)) ;;
            ret (prod_ce(temp_3143, temp_3145, temp_3147))) ;;
        #put q_3148_loc := q_3148 ;;
      bnd(ChoiceEqualityMonad.result_bind_code error_t , (
          (
            p256_field_element_t '×
            p256_field_element_t '×
            p256_field_element_t
          )
        ) , _ , CEfset ([q_3148_loc])) q_3148 ⇠
      (foldi_bind_code' (usize 0) (bits_v) (q_3148) (fun i_3154 q_3148 =>
        ({ code  '(q_3148 : (
                  p256_field_element_t '×
                  p256_field_element_t '×
                  p256_field_element_t
                )) ←
              (( '(temp_3150 : p256_jacobian_t) ←
                    (point_double (q_3148)) ;;
                  ret (temp_3150))) ;;
            #put q_3148_loc := q_3148 ;;
          
           '(temp_3153 : uint_size) ←
            ((bits_v) .- (usize 1)) ;;
           '(temp_3156 : uint_size) ←
            ((temp_3153) .- (i_3154)) ;;
           temp_3158 ←
            (nat_mod_get_bit (k_3151) (temp_3156)) ;;
           '(temp_3160 : p256_scalar_t) ←
            (nat_mod_one ) ;;
           temp_3162 ←
            (nat_mod_equal (temp_3158) (temp_3160)) ;;
          bnd(ChoiceEqualityMonad.result_bind_code error_t , (
              (
                p256_field_element_t '×
                p256_field_element_t '×
                p256_field_element_t
              )
            ) , _ , CEfset ([q_3148_loc])) 'q_3148 ⇠
          (if temp_3162 : bool_ChoiceEquality
            then (*state*) (({ code bndm(
                  ChoiceEqualityMonad.result_bind_code error_t , (
                    p256_field_element_t '×
                    p256_field_element_t '×
                    p256_field_element_t
                  ) , _ , CEfset ([q_3148_loc])) q_3148 ⇠
                (({ code ( '(temp_3165 : jacobian_result_t) ←
                        (point_add_jacob (q_3148) (p_3163)) ;;
                      ret (temp_3165)) } : code _ _ _)) in
                ({ code @ret ((result error_t (
                        (
                          p256_field_element_t '×
                          p256_field_element_t '×
                          p256_field_element_t
                        )
                      ))) (@inl (
                      (
                        p256_field_element_t '×
                        p256_field_element_t '×
                        p256_field_element_t
                      )
                    ) error_t (q_3148)) } : code (CEfset (
                      [q_3148_loc])) [interface
                  #val #[ POINT_ADD_JACOB ] : point_add_jacob_inp → point_add_jacob_out
                  ] _) } : code (CEfset ([q_3148_loc])) [interface
                #val #[ POINT_ADD_JACOB ] : point_add_jacob_inp → point_add_jacob_out
                ] _))
            else ({ code @ret ((result error_t (
                    (
                      p256_field_element_t '×
                      p256_field_element_t '×
                      p256_field_element_t
                    )
                  ))) (@inl (
                  (
                    p256_field_element_t '×
                    p256_field_element_t '×
                    p256_field_element_t
                  )
                ) error_t (q_3148)) } : code _ _ _) ) in
          ({ code @ret ((result error_t (
                  (
                    p256_field_element_t '×
                    p256_field_element_t '×
                    p256_field_element_t
                  )
                ))) (@inl (
                (
                  p256_field_element_t '×
                  p256_field_element_t '×
                  p256_field_element_t
                )
              ) error_t (q_3148)) } : code (CEfset ([q_3148_loc])) [interface
            #val #[ POINT_ADD_JACOB ] : point_add_jacob_inp → point_add_jacob_out ;
            #val #[ POINT_DOUBLE ] : point_double_inp → point_double_out
            ] _) } : code (CEfset ([q_3148_loc])) [interface
          #val #[ POINT_ADD_JACOB ] : point_add_jacob_inp → point_add_jacob_out ;
          #val #[ POINT_DOUBLE ] : point_double_inp → point_double_out
          ] _))) in
      ({ code @ret ((result error_t p256_jacobian_t)) (
          @inl p256_jacobian_t error_t (q_3148)) } : code (CEfset (
            [q_3148_loc])) [interface
        #val #[ POINT_ADD_JACOB ] : point_add_jacob_inp → point_add_jacob_out ;
        #val #[ POINT_DOUBLE ] : point_double_inp → point_double_out
        ] _) } : code (CEfset ([q_3148_loc])) [interface
      #val #[ POINT_ADD_JACOB ] : point_add_jacob_inp → point_add_jacob_out ;
      #val #[ POINT_DOUBLE ] : point_double_inp → point_double_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_ltr_mul : package _ _ _ :=
  (seq_link ltr_mul link_rest(package_point_add_jacob,package_point_double)).
Fail Next Obligation.


Notation "'p256_point_mul_inp'" := (
  p256_scalar_t '× affine_t : choice_type) (in custom pack_type at level 2).
Notation "'p256_point_mul_out'" := (
  affine_result_t : choice_type) (in custom pack_type at level 2).
Definition P256_POINT_MUL : nat :=
  (3177).
Program Definition p256_point_mul
   : package (CEfset ([])) [interface
  #val #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out ;
  #val #[ JACOBIAN_TO_AFFINE ] : jacobian_to_affine_inp → jacobian_to_affine_out ;
  #val #[ LTR_MUL ] : ltr_mul_inp → ltr_mul_out ] [interface
  #val #[ P256_POINT_MUL ] : p256_point_mul_inp → p256_point_mul_out ] :=
  (
    [package #def #[ P256_POINT_MUL ] (temp_inp : p256_point_mul_inp) : p256_point_mul_out { 
    let '(k_3168 , p_3169) := temp_inp : p256_scalar_t '× affine_t in
    #import {sig #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out } as affine_to_jacobian ;;
    let affine_to_jacobian := fun x_0 => affine_to_jacobian (x_0) in
    #import {sig #[ JACOBIAN_TO_AFFINE ] : jacobian_to_affine_inp → jacobian_to_affine_out } as jacobian_to_affine ;;
    let jacobian_to_affine := fun x_0 => jacobian_to_affine (x_0) in
    #import {sig #[ LTR_MUL ] : ltr_mul_inp → ltr_mul_out } as ltr_mul ;;
    let ltr_mul := fun x_0 x_1 => ltr_mul (x_0,x_1) in
    ({ code bnd(
        ChoiceEqualityMonad.result_bind_code error_t , p256_jacobian_t , _ , CEfset (
          [])) jac_3174 ⇠
      (({ code  '(temp_3171 : p256_jacobian_t) ←
            (affine_to_jacobian (p_3169)) ;;
           '(temp_3173 : jacobian_result_t) ←
            (ltr_mul (k_3168) (temp_3171)) ;;
          @ret _ (temp_3173) } : code (CEfset ([])) [interface
          #val #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out ;
          #val #[ LTR_MUL ] : ltr_mul_inp → ltr_mul_out ] _)) in
      ({ code  '(temp_3176 : affine_t) ←
          (jacobian_to_affine (jac_3174)) ;;
        @ret ((result error_t affine_t)) (@inl affine_t error_t (
            temp_3176)) } : code (CEfset ([])) [interface
        #val #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out ;
        #val #[ JACOBIAN_TO_AFFINE ] : jacobian_to_affine_inp → jacobian_to_affine_out ;
        #val #[ LTR_MUL ] : ltr_mul_inp → ltr_mul_out ] _) } : code (CEfset (
          [])) [interface
      #val #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out ;
      #val #[ JACOBIAN_TO_AFFINE ] : jacobian_to_affine_inp → jacobian_to_affine_out ;
      #val #[ LTR_MUL ] : ltr_mul_inp → ltr_mul_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_p256_point_mul : package _ _ _ :=
  (seq_link p256_point_mul link_rest(
      package_affine_to_jacobian,package_jacobian_to_affine,package_ltr_mul)).
Fail Next Obligation.


Notation "'p256_point_mul_base_inp'" := (
  p256_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'p256_point_mul_base_out'" := (
  affine_result_t : choice_type) (in custom pack_type at level 2).
Definition P256_POINT_MUL_BASE : nat :=
  (3322).
Program Definition p256_point_mul_base
   : package (CEfset ([])) [interface
  #val #[ P256_POINT_MUL ] : p256_point_mul_inp → p256_point_mul_out
  ] [interface
  #val #[ P256_POINT_MUL_BASE ] : p256_point_mul_base_inp → p256_point_mul_base_out
  ] :=
  (
    [package #def #[ P256_POINT_MUL_BASE ] (temp_inp : p256_point_mul_base_inp) : p256_point_mul_base_out { 
    let '(k_3318) := temp_inp : p256_scalar_t in
    #import {sig #[ P256_POINT_MUL ] : p256_point_mul_inp → p256_point_mul_out } as p256_point_mul ;;
    let p256_point_mul := fun x_0 x_1 => p256_point_mul (x_0,x_1) in
    ({ code  '(base_point_3319 : (p256_field_element_t '× p256_field_element_t
          )) ←
        ( '(temp_3179 : int8) ←
            (secret (@repr U8 107)) ;;
           '(temp_3181 : int8) ←
            (secret (@repr U8 23)) ;;
           '(temp_3183 : int8) ←
            (secret (@repr U8 209)) ;;
           '(temp_3185 : int8) ←
            (secret (@repr U8 242)) ;;
           '(temp_3187 : int8) ←
            (secret (@repr U8 225)) ;;
           '(temp_3189 : int8) ←
            (secret (@repr U8 44)) ;;
           '(temp_3191 : int8) ←
            (secret (@repr U8 66)) ;;
           '(temp_3193 : int8) ←
            (secret (@repr U8 71)) ;;
           '(temp_3195 : int8) ←
            (secret (@repr U8 248)) ;;
           '(temp_3197 : int8) ←
            (secret (@repr U8 188)) ;;
           '(temp_3199 : int8) ←
            (secret (@repr U8 230)) ;;
           '(temp_3201 : int8) ←
            (secret (@repr U8 229)) ;;
           '(temp_3203 : int8) ←
            (secret (@repr U8 99)) ;;
           '(temp_3205 : int8) ←
            (secret (@repr U8 164)) ;;
           '(temp_3207 : int8) ←
            (secret (@repr U8 64)) ;;
           '(temp_3209 : int8) ←
            (secret (@repr U8 242)) ;;
           '(temp_3211 : int8) ←
            (secret (@repr U8 119)) ;;
           '(temp_3213 : int8) ←
            (secret (@repr U8 3)) ;;
           '(temp_3215 : int8) ←
            (secret (@repr U8 125)) ;;
           '(temp_3217 : int8) ←
            (secret (@repr U8 129)) ;;
           '(temp_3219 : int8) ←
            (secret (@repr U8 45)) ;;
           '(temp_3221 : int8) ←
            (secret (@repr U8 235)) ;;
           '(temp_3223 : int8) ←
            (secret (@repr U8 51)) ;;
           '(temp_3225 : int8) ←
            (secret (@repr U8 160)) ;;
           '(temp_3227 : int8) ←
            (secret (@repr U8 244)) ;;
           '(temp_3229 : int8) ←
            (secret (@repr U8 161)) ;;
           '(temp_3231 : int8) ←
            (secret (@repr U8 57)) ;;
           '(temp_3233 : int8) ←
            (secret (@repr U8 69)) ;;
           '(temp_3235 : int8) ←
            (secret (@repr U8 216)) ;;
           '(temp_3237 : int8) ←
            (secret (@repr U8 152)) ;;
           '(temp_3239 : int8) ←
            (secret (@repr U8 194)) ;;
           '(temp_3241 : int8) ←
            (secret (@repr U8 150)) ;;
           '(temp_3243 : nseq uint8 32) ←
            (array_from_list uint8 [
                temp_3179;
                temp_3181;
                temp_3183;
                temp_3185;
                temp_3187;
                temp_3189;
                temp_3191;
                temp_3193;
                temp_3195;
                temp_3197;
                temp_3199;
                temp_3201;
                temp_3203;
                temp_3205;
                temp_3207;
                temp_3209;
                temp_3211;
                temp_3213;
                temp_3215;
                temp_3217;
                temp_3219;
                temp_3221;
                temp_3223;
                temp_3225;
                temp_3227;
                temp_3229;
                temp_3231;
                temp_3233;
                temp_3235;
                temp_3237;
                temp_3239;
                temp_3241
              ]) ;;
           '(temp_3245 : seq uint8) ←
            (array_to_seq (temp_3243)) ;;
           '(temp_3247 : p256_field_element_t) ←
            (nat_mod_from_byte_seq_be (temp_3245)) ;;
           '(temp_3249 : int8) ←
            (secret (@repr U8 79)) ;;
           '(temp_3251 : int8) ←
            (secret (@repr U8 227)) ;;
           '(temp_3253 : int8) ←
            (secret (@repr U8 66)) ;;
           '(temp_3255 : int8) ←
            (secret (@repr U8 226)) ;;
           '(temp_3257 : int8) ←
            (secret (@repr U8 254)) ;;
           '(temp_3259 : int8) ←
            (secret (@repr U8 26)) ;;
           '(temp_3261 : int8) ←
            (secret (@repr U8 127)) ;;
           '(temp_3263 : int8) ←
            (secret (@repr U8 155)) ;;
           '(temp_3265 : int8) ←
            (secret (@repr U8 142)) ;;
           '(temp_3267 : int8) ←
            (secret (@repr U8 231)) ;;
           '(temp_3269 : int8) ←
            (secret (@repr U8 235)) ;;
           '(temp_3271 : int8) ←
            (secret (@repr U8 74)) ;;
           '(temp_3273 : int8) ←
            (secret (@repr U8 124)) ;;
           '(temp_3275 : int8) ←
            (secret (@repr U8 15)) ;;
           '(temp_3277 : int8) ←
            (secret (@repr U8 158)) ;;
           '(temp_3279 : int8) ←
            (secret (@repr U8 22)) ;;
           '(temp_3281 : int8) ←
            (secret (@repr U8 43)) ;;
           '(temp_3283 : int8) ←
            (secret (@repr U8 206)) ;;
           '(temp_3285 : int8) ←
            (secret (@repr U8 51)) ;;
           '(temp_3287 : int8) ←
            (secret (@repr U8 87)) ;;
           '(temp_3289 : int8) ←
            (secret (@repr U8 107)) ;;
           '(temp_3291 : int8) ←
            (secret (@repr U8 49)) ;;
           '(temp_3293 : int8) ←
            (secret (@repr U8 94)) ;;
           '(temp_3295 : int8) ←
            (secret (@repr U8 206)) ;;
           '(temp_3297 : int8) ←
            (secret (@repr U8 203)) ;;
           '(temp_3299 : int8) ←
            (secret (@repr U8 182)) ;;
           '(temp_3301 : int8) ←
            (secret (@repr U8 64)) ;;
           '(temp_3303 : int8) ←
            (secret (@repr U8 104)) ;;
           '(temp_3305 : int8) ←
            (secret (@repr U8 55)) ;;
           '(temp_3307 : int8) ←
            (secret (@repr U8 191)) ;;
           '(temp_3309 : int8) ←
            (secret (@repr U8 81)) ;;
           '(temp_3311 : int8) ←
            (secret (@repr U8 245)) ;;
           '(temp_3313 : nseq uint8 32) ←
            (array_from_list uint8 [
                temp_3249;
                temp_3251;
                temp_3253;
                temp_3255;
                temp_3257;
                temp_3259;
                temp_3261;
                temp_3263;
                temp_3265;
                temp_3267;
                temp_3269;
                temp_3271;
                temp_3273;
                temp_3275;
                temp_3277;
                temp_3279;
                temp_3281;
                temp_3283;
                temp_3285;
                temp_3287;
                temp_3289;
                temp_3291;
                temp_3293;
                temp_3295;
                temp_3297;
                temp_3299;
                temp_3301;
                temp_3303;
                temp_3305;
                temp_3307;
                temp_3309;
                temp_3311
              ]) ;;
           '(temp_3315 : seq uint8) ←
            (array_to_seq (temp_3313)) ;;
           '(temp_3317 : p256_field_element_t) ←
            (nat_mod_from_byte_seq_be (temp_3315)) ;;
          ret (prod_ce(temp_3247, temp_3317))) ;;
       '(temp_3321 : affine_result_t) ←
        (p256_point_mul (k_3318) (base_point_3319)) ;;
      @ret (affine_result_t) (temp_3321) } : code (CEfset ([])) [interface
      #val #[ P256_POINT_MUL ] : p256_point_mul_inp → p256_point_mul_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_p256_point_mul_base : package _ _ _ :=
  (seq_link p256_point_mul_base link_rest(package_p256_point_mul)).
Fail Next Obligation.


Notation "'point_add_distinct_inp'" := (
  affine_t '× affine_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_distinct_out'" := (
  affine_result_t : choice_type) (in custom pack_type at level 2).
Definition POINT_ADD_DISTINCT : nat :=
  (3334).
Program Definition point_add_distinct
   : package (CEfset ([])) [interface
  #val #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out ;
  #val #[ JACOBIAN_TO_AFFINE ] : jacobian_to_affine_inp → jacobian_to_affine_out ;
  #val #[ POINT_ADD_JACOB ] : point_add_jacob_inp → point_add_jacob_out
  ] [interface
  #val #[ POINT_ADD_DISTINCT ] : point_add_distinct_inp → point_add_distinct_out
  ] :=
  (
    [package #def #[ POINT_ADD_DISTINCT ] (temp_inp : point_add_distinct_inp) : point_add_distinct_out { 
    let '(p_3323 , q_3326) := temp_inp : affine_t '× affine_t in
    #import {sig #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out } as affine_to_jacobian ;;
    let affine_to_jacobian := fun x_0 => affine_to_jacobian (x_0) in
    #import {sig #[ JACOBIAN_TO_AFFINE ] : jacobian_to_affine_inp → jacobian_to_affine_out } as jacobian_to_affine ;;
    let jacobian_to_affine := fun x_0 => jacobian_to_affine (x_0) in
    #import {sig #[ POINT_ADD_JACOB ] : point_add_jacob_inp → point_add_jacob_out } as point_add_jacob ;;
    let point_add_jacob := fun x_0 x_1 => point_add_jacob (x_0,x_1) in
    ({ code bnd(
        ChoiceEqualityMonad.result_bind_code error_t , p256_jacobian_t , _ , CEfset (
          [])) r_3331 ⇠
      (({ code  '(temp_3325 : p256_jacobian_t) ←
            (affine_to_jacobian (p_3323)) ;;
           '(temp_3328 : p256_jacobian_t) ←
            (affine_to_jacobian (q_3326)) ;;
           '(temp_3330 : jacobian_result_t) ←
            (point_add_jacob (temp_3325) (temp_3328)) ;;
          @ret _ (temp_3330) } : code (CEfset ([])) [interface
          #val #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out ;
          #val #[ POINT_ADD_JACOB ] : point_add_jacob_inp → point_add_jacob_out
          ] _)) in
      ({ code  '(temp_3333 : affine_t) ←
          (jacobian_to_affine (r_3331)) ;;
        @ret ((result error_t affine_t)) (@inl affine_t error_t (
            temp_3333)) } : code (CEfset ([])) [interface
        #val #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out ;
        #val #[ JACOBIAN_TO_AFFINE ] : jacobian_to_affine_inp → jacobian_to_affine_out ;
        #val #[ POINT_ADD_JACOB ] : point_add_jacob_inp → point_add_jacob_out
        ] _) } : code (CEfset ([])) [interface
      #val #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out ;
      #val #[ JACOBIAN_TO_AFFINE ] : jacobian_to_affine_inp → jacobian_to_affine_out ;
      #val #[ POINT_ADD_JACOB ] : point_add_jacob_inp → point_add_jacob_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_point_add_distinct : package _ _ _ :=
  (seq_link point_add_distinct link_rest(
      package_affine_to_jacobian,package_jacobian_to_affine,package_point_add_jacob)).
Fail Next Obligation.


Notation "'point_add_inp'" := (
  affine_t '× affine_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_out'" := (
  affine_result_t : choice_type) (in custom pack_type at level 2).
Definition POINT_ADD : nat :=
  (3347).
Program Definition point_add
   : package (CEfset ([])) [interface
  #val #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out ;
  #val #[ JACOBIAN_TO_AFFINE ] : jacobian_to_affine_inp → jacobian_to_affine_out ;
  #val #[ POINT_ADD_DISTINCT ] : point_add_distinct_inp → point_add_distinct_out ;
  #val #[ POINT_DOUBLE ] : point_double_inp → point_double_out ] [interface
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ] :=
  ([package #def #[ POINT_ADD ] (temp_inp : point_add_inp) : point_add_out { 
    let '(p_3335 , q_3336) := temp_inp : affine_t '× affine_t in
    #import {sig #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out } as affine_to_jacobian ;;
    let affine_to_jacobian := fun x_0 => affine_to_jacobian (x_0) in
    #import {sig #[ JACOBIAN_TO_AFFINE ] : jacobian_to_affine_inp → jacobian_to_affine_out } as jacobian_to_affine ;;
    let jacobian_to_affine := fun x_0 => jacobian_to_affine (x_0) in
    #import {sig #[ POINT_ADD_DISTINCT ] : point_add_distinct_inp → point_add_distinct_out } as point_add_distinct ;;
    let point_add_distinct := fun x_0 x_1 => point_add_distinct (x_0,x_1) in
    #import {sig #[ POINT_DOUBLE ] : point_double_inp → point_double_out } as point_double ;;
    let point_double := fun x_0 => point_double (x_0) in
    ({ code  '(temp_3338 : bool_ChoiceEquality) ←
        ((p_3335) !=.? (q_3336)) ;;
       '(temp_3340 : affine_result_t) ←
        (point_add_distinct (p_3335) (q_3336)) ;;
       '(temp_3342 : p256_jacobian_t) ←
        (affine_to_jacobian (p_3335)) ;;
       '(temp_3344 : p256_jacobian_t) ←
        (point_double (temp_3342)) ;;
       '(temp_3346 : affine_t) ←
        (jacobian_to_affine (temp_3344)) ;;
      @ret (affine_result_t) ((if (
            temp_3338):bool_ChoiceEquality then (*inline*) (temp_3340) else (
            @inl affine_t error_t (temp_3346)))) } : code (CEfset (
          [])) [interface
      #val #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out ;
      #val #[ JACOBIAN_TO_AFFINE ] : jacobian_to_affine_inp → jacobian_to_affine_out ;
      #val #[ POINT_ADD_DISTINCT ] : point_add_distinct_inp → point_add_distinct_out ;
      #val #[ POINT_DOUBLE ] : point_double_inp → point_double_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_point_add : package _ _ _ :=
  (seq_link point_add link_rest(
      package_affine_to_jacobian,package_jacobian_to_affine,package_point_add_distinct,package_point_double)).
Fail Next Obligation.

Definition valid_3364_loc : ChoiceEqualityLocation :=
  ((bool_ChoiceEquality ; 3376%nat)).
Definition all_zero_3363_loc : ChoiceEqualityLocation :=
  ((bool_ChoiceEquality ; 3377%nat)).
Notation "'p256_validate_private_key_inp'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'p256_validate_private_key_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition P256_VALIDATE_PRIVATE_KEY : nat :=
  (3378).
Program Definition p256_validate_private_key
   : package (CEfset (
      [valid_3364_loc ; all_zero_3363_loc])) [interface] [interface
  #val #[ P256_VALIDATE_PRIVATE_KEY ] : p256_validate_private_key_inp → p256_validate_private_key_out
  ] :=
  (
    [package #def #[ P256_VALIDATE_PRIVATE_KEY ] (temp_inp : p256_validate_private_key_inp) : p256_validate_private_key_out { 
    let '(k_3348) := temp_inp : byte_seq in
    ({ code  '(valid_3364 : bool_ChoiceEquality) ←
          (ret ((true : bool_ChoiceEquality))) ;;
        #put valid_3364_loc := valid_3364 ;;
       '(k_element_3351 : p256_scalar_t) ←
        ( '(temp_3350 : p256_scalar_t) ←
            (nat_mod_from_byte_seq_be (k_3348)) ;;
          ret (temp_3350)) ;;
       '(k_element_bytes_3366 : seq uint8) ←
        ( temp_3353 ←
            (nat_mod_to_byte_seq_be (k_element_3351)) ;;
          ret (temp_3353)) ;;
       '(all_zero_3363 : bool_ChoiceEquality) ←
          (ret ((true : bool_ChoiceEquality))) ;;
        #put all_zero_3363_loc := all_zero_3363 ;;
       '(temp_3355 : uint_size) ←
        (seq_len (k_3348)) ;;
       temp_3375 ←
        (foldi' (usize 0) (temp_3355) prod_ce(valid_3364, all_zero_3363) (
              L2 := CEfset ([valid_3364_loc ; all_zero_3363_loc])) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_3356 '(
              valid_3364,
              all_zero_3363
            ) =>
            ({ code  temp_3358 ←
                (seq_index (k_3348) (i_3356)) ;;
               '(temp_3360 : int8) ←
                (secret (@repr U8 0)) ;;
               temp_3362 ←
                (uint8_equal (temp_3358) (temp_3360)) ;;
               '(all_zero_3363 : (bool_ChoiceEquality)) ←
                (if negb (temp_3362):bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(
                          all_zero_3363 : bool_ChoiceEquality) ←
                        ((ret ((false : bool_ChoiceEquality)))) ;;
                      #put all_zero_3363_loc := all_zero_3363 ;;
                    
                    @ret ((bool_ChoiceEquality)) (all_zero_3363) in
                    ({ code temp_then } : code (CEfset (
                          [valid_3364_loc ; all_zero_3363_loc])) [interface] _))
                  else @ret ((bool_ChoiceEquality)) (all_zero_3363)) ;;
              
               '(temp_3367 : uint8) ←
                (seq_index (k_element_bytes_3366) (i_3356)) ;;
               temp_3369 ←
                (seq_index (k_3348) (i_3356)) ;;
               temp_3371 ←
                (uint8_equal (temp_3367) (temp_3369)) ;;
               '(valid_3364 : (bool_ChoiceEquality)) ←
                (if negb (temp_3371):bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(
                          valid_3364 : bool_ChoiceEquality) ←
                        ((ret ((false : bool_ChoiceEquality)))) ;;
                      #put valid_3364_loc := valid_3364 ;;
                    
                    @ret ((bool_ChoiceEquality)) (valid_3364) in
                    ({ code temp_then } : code (CEfset (
                          [valid_3364_loc ; all_zero_3363_loc])) [interface] _))
                  else @ret ((bool_ChoiceEquality)) (valid_3364)) ;;
              
              @ret ((bool_ChoiceEquality '× bool_ChoiceEquality)) (prod_ce(
                  valid_3364,
                  all_zero_3363
                )) } : code (CEfset (
                  [valid_3364_loc ; all_zero_3363_loc])) [interface] _))) ;;
      let '(valid_3364, all_zero_3363) :=
        (temp_3375) : (bool_ChoiceEquality '× bool_ChoiceEquality) in
      
       '(temp_3373 : bool_ChoiceEquality) ←
        ((valid_3364) && (negb (all_zero_3363))) ;;
      @ret (bool_ChoiceEquality) (temp_3373) } : code (CEfset (
          [valid_3364_loc ; all_zero_3363_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_p256_validate_private_key : package _ _ _ :=
  (p256_validate_private_key).
Fail Next Obligation.


Notation "'p256_validate_public_key_inp'" := (
  affine_t : choice_type) (in custom pack_type at level 2).
Notation "'p256_validate_public_key_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition P256_VALIDATE_PUBLIC_KEY : nat :=
  (3475).
Program Definition p256_validate_public_key
   : package (fset.fset0) [interface
  #val #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out ;
  #val #[ IS_POINT_AT_INFINITY ] : is_point_at_infinity_inp → is_point_at_infinity_out
  ] [interface
  #val #[ P256_VALIDATE_PUBLIC_KEY ] : p256_validate_public_key_inp → p256_validate_public_key_out
  ] :=
  (
    [package #def #[ P256_VALIDATE_PUBLIC_KEY ] (temp_inp : p256_validate_public_key_inp) : p256_validate_public_key_out { 
    let '(p_3445) := temp_inp : affine_t in
    #import {sig #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out } as affine_to_jacobian ;;
    let affine_to_jacobian := fun x_0 => affine_to_jacobian (x_0) in
    #import {sig #[ IS_POINT_AT_INFINITY ] : is_point_at_infinity_inp → is_point_at_infinity_out } as is_point_at_infinity ;;
    let is_point_at_infinity := fun x_0 => is_point_at_infinity (x_0) in
    ({ code  '(b_3464 : p256_field_element_t) ←
        ( '(temp_3380 : int8) ←
            (secret (@repr U8 90)) ;;
           '(temp_3382 : int8) ←
            (secret (@repr U8 198)) ;;
           '(temp_3384 : int8) ←
            (secret (@repr U8 53)) ;;
           '(temp_3386 : int8) ←
            (secret (@repr U8 216)) ;;
           '(temp_3388 : int8) ←
            (secret (@repr U8 170)) ;;
           '(temp_3390 : int8) ←
            (secret (@repr U8 58)) ;;
           '(temp_3392 : int8) ←
            (secret (@repr U8 147)) ;;
           '(temp_3394 : int8) ←
            (secret (@repr U8 231)) ;;
           '(temp_3396 : int8) ←
            (secret (@repr U8 179)) ;;
           '(temp_3398 : int8) ←
            (secret (@repr U8 235)) ;;
           '(temp_3400 : int8) ←
            (secret (@repr U8 189)) ;;
           '(temp_3402 : int8) ←
            (secret (@repr U8 85)) ;;
           '(temp_3404 : int8) ←
            (secret (@repr U8 118)) ;;
           '(temp_3406 : int8) ←
            (secret (@repr U8 152)) ;;
           '(temp_3408 : int8) ←
            (secret (@repr U8 134)) ;;
           '(temp_3410 : int8) ←
            (secret (@repr U8 188)) ;;
           '(temp_3412 : int8) ←
            (secret (@repr U8 101)) ;;
           '(temp_3414 : int8) ←
            (secret (@repr U8 29)) ;;
           '(temp_3416 : int8) ←
            (secret (@repr U8 6)) ;;
           '(temp_3418 : int8) ←
            (secret (@repr U8 176)) ;;
           '(temp_3420 : int8) ←
            (secret (@repr U8 204)) ;;
           '(temp_3422 : int8) ←
            (secret (@repr U8 83)) ;;
           '(temp_3424 : int8) ←
            (secret (@repr U8 176)) ;;
           '(temp_3426 : int8) ←
            (secret (@repr U8 246)) ;;
           '(temp_3428 : int8) ←
            (secret (@repr U8 59)) ;;
           '(temp_3430 : int8) ←
            (secret (@repr U8 206)) ;;
           '(temp_3432 : int8) ←
            (secret (@repr U8 60)) ;;
           '(temp_3434 : int8) ←
            (secret (@repr U8 62)) ;;
           '(temp_3436 : int8) ←
            (secret (@repr U8 39)) ;;
           '(temp_3438 : int8) ←
            (secret (@repr U8 210)) ;;
           '(temp_3440 : int8) ←
            (secret (@repr U8 96)) ;;
           '(temp_3442 : int8) ←
            (secret (@repr U8 75)) ;;
           '(temp_3444 : p256_field_element_t) ←
            (nat_mod_from_byte_seq_be (seq_from_list _ [
                  temp_3380;
                  temp_3382;
                  temp_3384;
                  temp_3386;
                  temp_3388;
                  temp_3390;
                  temp_3392;
                  temp_3394;
                  temp_3396;
                  temp_3398;
                  temp_3400;
                  temp_3402;
                  temp_3404;
                  temp_3406;
                  temp_3408;
                  temp_3410;
                  temp_3412;
                  temp_3414;
                  temp_3416;
                  temp_3418;
                  temp_3420;
                  temp_3422;
                  temp_3424;
                  temp_3426;
                  temp_3428;
                  temp_3430;
                  temp_3432;
                  temp_3434;
                  temp_3436;
                  temp_3438;
                  temp_3440;
                  temp_3442
                ])) ;;
          ret (temp_3444)) ;;
       '(point_at_infinity_3469 : bool_ChoiceEquality) ←
        ( '(temp_3447 : p256_jacobian_t) ←
            (affine_to_jacobian (p_3445)) ;;
           '(temp_3449 : bool_ChoiceEquality) ←
            (is_point_at_infinity (temp_3447)) ;;
          ret (temp_3449)) ;;
       temp_3474 ←
        (ret (p_3445)) ;;
      let '(x_3453, y_3450) :=
        (temp_3474) : (p256_field_element_t '× p256_field_element_t) in
       '(on_curve_3470 : bool_ChoiceEquality) ←
        ( '(temp_3452 : p256_field_element_t) ←
            ((y_3450) *% (y_3450)) ;;
           '(temp_3455 : p256_field_element_t) ←
            ((x_3453) *% (x_3453)) ;;
           '(temp_3457 : p256_field_element_t) ←
            ((temp_3455) *% (x_3453)) ;;
           '(temp_3459 : p256_field_element_t) ←
            (nat_mod_from_literal (
                0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                @repr U128 3)) ;;
           '(temp_3461 : p256_field_element_t) ←
            ((temp_3459) *% (x_3453)) ;;
           '(temp_3463 : p256_field_element_t) ←
            ((temp_3457) -% (temp_3461)) ;;
           '(temp_3466 : p256_field_element_t) ←
            ((temp_3463) +% (b_3464)) ;;
           '(temp_3468 : bool_ChoiceEquality) ←
            ((temp_3452) =.? (temp_3466)) ;;
          ret (temp_3468)) ;;
       '(temp_3472 : bool_ChoiceEquality) ←
        ((negb (point_at_infinity_3469)) && (on_curve_3470)) ;;
      @ret (bool_ChoiceEquality) (temp_3472) } : code (fset.fset0) [interface
      #val #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out ;
      #val #[ IS_POINT_AT_INFINITY ] : is_point_at_infinity_inp → is_point_at_infinity_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_p256_validate_public_key : package _ _ _ :=
  (seq_link p256_validate_public_key link_rest(
      package_affine_to_jacobian,package_is_point_at_infinity)).
Fail Next Obligation.


Notation "'p256_calculate_w_inp'" := (
  p256_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'p256_calculate_w_out'" := (
  p256_field_element_t : choice_type) (in custom pack_type at level 2).
Definition P256_CALCULATE_W : nat :=
  (3627).
Program Definition p256_calculate_w
   : package (fset.fset0) [interface] [interface
  #val #[ P256_CALCULATE_W ] : p256_calculate_w_inp → p256_calculate_w_out
  ] :=
  (
    [package #def #[ P256_CALCULATE_W ] (temp_inp : p256_calculate_w_inp) : p256_calculate_w_out { 
    let '(x_3608) := temp_inp : p256_field_element_t in
    ({ code  '(b_3619 : p256_field_element_t) ←
        ( '(temp_3477 : int8) ←
            (secret (@repr U8 90)) ;;
           '(temp_3479 : int8) ←
            (secret (@repr U8 198)) ;;
           '(temp_3481 : int8) ←
            (secret (@repr U8 53)) ;;
           '(temp_3483 : int8) ←
            (secret (@repr U8 216)) ;;
           '(temp_3485 : int8) ←
            (secret (@repr U8 170)) ;;
           '(temp_3487 : int8) ←
            (secret (@repr U8 58)) ;;
           '(temp_3489 : int8) ←
            (secret (@repr U8 147)) ;;
           '(temp_3491 : int8) ←
            (secret (@repr U8 231)) ;;
           '(temp_3493 : int8) ←
            (secret (@repr U8 179)) ;;
           '(temp_3495 : int8) ←
            (secret (@repr U8 235)) ;;
           '(temp_3497 : int8) ←
            (secret (@repr U8 189)) ;;
           '(temp_3499 : int8) ←
            (secret (@repr U8 85)) ;;
           '(temp_3501 : int8) ←
            (secret (@repr U8 118)) ;;
           '(temp_3503 : int8) ←
            (secret (@repr U8 152)) ;;
           '(temp_3505 : int8) ←
            (secret (@repr U8 134)) ;;
           '(temp_3507 : int8) ←
            (secret (@repr U8 188)) ;;
           '(temp_3509 : int8) ←
            (secret (@repr U8 101)) ;;
           '(temp_3511 : int8) ←
            (secret (@repr U8 29)) ;;
           '(temp_3513 : int8) ←
            (secret (@repr U8 6)) ;;
           '(temp_3515 : int8) ←
            (secret (@repr U8 176)) ;;
           '(temp_3517 : int8) ←
            (secret (@repr U8 204)) ;;
           '(temp_3519 : int8) ←
            (secret (@repr U8 83)) ;;
           '(temp_3521 : int8) ←
            (secret (@repr U8 176)) ;;
           '(temp_3523 : int8) ←
            (secret (@repr U8 246)) ;;
           '(temp_3525 : int8) ←
            (secret (@repr U8 59)) ;;
           '(temp_3527 : int8) ←
            (secret (@repr U8 206)) ;;
           '(temp_3529 : int8) ←
            (secret (@repr U8 60)) ;;
           '(temp_3531 : int8) ←
            (secret (@repr U8 62)) ;;
           '(temp_3533 : int8) ←
            (secret (@repr U8 39)) ;;
           '(temp_3535 : int8) ←
            (secret (@repr U8 210)) ;;
           '(temp_3537 : int8) ←
            (secret (@repr U8 96)) ;;
           '(temp_3539 : int8) ←
            (secret (@repr U8 75)) ;;
           '(temp_3541 : p256_field_element_t) ←
            (nat_mod_from_byte_seq_be (seq_from_list _ [
                  temp_3477;
                  temp_3479;
                  temp_3481;
                  temp_3483;
                  temp_3485;
                  temp_3487;
                  temp_3489;
                  temp_3491;
                  temp_3493;
                  temp_3495;
                  temp_3497;
                  temp_3499;
                  temp_3501;
                  temp_3503;
                  temp_3505;
                  temp_3507;
                  temp_3509;
                  temp_3511;
                  temp_3513;
                  temp_3515;
                  temp_3517;
                  temp_3519;
                  temp_3521;
                  temp_3523;
                  temp_3525;
                  temp_3527;
                  temp_3529;
                  temp_3531;
                  temp_3533;
                  temp_3535;
                  temp_3537;
                  temp_3539
                ])) ;;
          ret (temp_3541)) ;;
       '(exp_3623 : p256_field_element_t) ←
        ( '(temp_3543 : int8) ←
            (secret (@repr U8 63)) ;;
           '(temp_3545 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_3547 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_3549 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_3551 : int8) ←
            (secret (@repr U8 192)) ;;
           '(temp_3553 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_3555 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_3557 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_3559 : int8) ←
            (secret (@repr U8 64)) ;;
           '(temp_3561 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_3563 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_3565 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_3567 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_3569 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_3571 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_3573 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_3575 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_3577 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_3579 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_3581 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_3583 : int8) ←
            (secret (@repr U8 64)) ;;
           '(temp_3585 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_3587 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_3589 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_3591 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_3593 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_3595 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_3597 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_3599 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_3601 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_3603 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_3605 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_3607 : p256_field_element_t) ←
            (nat_mod_from_byte_seq_be (seq_from_list _ [
                  temp_3543;
                  temp_3545;
                  temp_3547;
                  temp_3549;
                  temp_3551;
                  temp_3553;
                  temp_3555;
                  temp_3557;
                  temp_3559;
                  temp_3561;
                  temp_3563;
                  temp_3565;
                  temp_3567;
                  temp_3569;
                  temp_3571;
                  temp_3573;
                  temp_3575;
                  temp_3577;
                  temp_3579;
                  temp_3581;
                  temp_3583;
                  temp_3585;
                  temp_3587;
                  temp_3589;
                  temp_3591;
                  temp_3593;
                  temp_3595;
                  temp_3597;
                  temp_3599;
                  temp_3601;
                  temp_3603;
                  temp_3605
                ])) ;;
          ret (temp_3607)) ;;
       '(z_3622 : p256_field_element_t) ←
        ( '(temp_3610 : p256_field_element_t) ←
            ((x_3608) *% (x_3608)) ;;
           '(temp_3612 : p256_field_element_t) ←
            ((temp_3610) *% (x_3608)) ;;
           '(temp_3614 : p256_field_element_t) ←
            (nat_mod_from_literal (
                0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                @repr U128 3)) ;;
           '(temp_3616 : p256_field_element_t) ←
            ((temp_3614) *% (x_3608)) ;;
           '(temp_3618 : p256_field_element_t) ←
            ((temp_3612) -% (temp_3616)) ;;
           '(temp_3621 : p256_field_element_t) ←
            ((temp_3618) +% (b_3619)) ;;
          ret (temp_3621)) ;;
       '(w_3626 : p256_field_element_t) ←
        ( temp_3625 ←
            (nat_mod_pow_felem (z_3622) (exp_3623)) ;;
          ret (temp_3625)) ;;
      @ret (p256_field_element_t) (w_3626) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_p256_calculate_w : package _ _ _ :=
  (p256_calculate_w).
Fail Next Obligation.

