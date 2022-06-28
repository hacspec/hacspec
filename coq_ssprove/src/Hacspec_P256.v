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
  (24).
Program Definition jacobian_to_affine
   : package (fset.fset0) [interface] [interface
  #val #[ JACOBIAN_TO_AFFINE ] : jacobian_to_affine_inp → jacobian_to_affine_out
  ] :=
  (
    [package #def #[ JACOBIAN_TO_AFFINE ] (temp_inp : jacobian_to_affine_inp) : jacobian_to_affine_out { 
    let '(p_0) := temp_inp : p256_jacobian_t in
    ({ code  temp_23 ←
        (ret (p_0)) ;;
      let '(x_12, y_16, z_1) :=
        (temp_23) : (
        p256_field_element_t '×
        p256_field_element_t '×
        p256_field_element_t
      ) in
       '(z2_4 : p256_field_element_t) ←
        ( temp_3 ←
            (nat_mod_exp (z_1) (@repr U32 2)) ;;
          ret (temp_3)) ;;
       '(z2i_13 : p256_field_element_t) ←
        ( temp_6 ←
            (nat_mod_inv (z2_4)) ;;
          ret (temp_6)) ;;
       '(z3_9 : p256_field_element_t) ←
        ( '(temp_8 : p256_field_element_t) ←
            ((z_1) *% (z2_4)) ;;
          ret (temp_8)) ;;
       '(z3i_17 : p256_field_element_t) ←
        ( temp_11 ←
            (nat_mod_inv (z3_9)) ;;
          ret (temp_11)) ;;
       '(x_20 : p256_field_element_t) ←
        ( '(temp_15 : p256_field_element_t) ←
            ((x_12) *% (z2i_13)) ;;
          ret (temp_15)) ;;
       '(y_21 : p256_field_element_t) ←
        ( '(temp_19 : p256_field_element_t) ←
            ((y_16) *% (z3i_17)) ;;
          ret (temp_19)) ;;
      @ret ((p256_field_element_t '× p256_field_element_t)) (prod_ce(x_20, y_21
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
  (32).
Program Definition affine_to_jacobian
   : package (fset.fset0) [interface] [interface
  #val #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out
  ] :=
  (
    [package #def #[ AFFINE_TO_JACOBIAN ] (temp_inp : affine_to_jacobian_inp) : affine_to_jacobian_out { 
    let '(p_25) := temp_inp : affine_t in
    ({ code  temp_31 ←
        (ret (p_25)) ;;
      let '(x_26, y_27) :=
        (temp_31) : (p256_field_element_t '× p256_field_element_t) in
       '(temp_29 : p256_field_element_t) ←
        (nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            @repr U128 1)) ;;
      @ret ((
          p256_field_element_t '×
          p256_field_element_t '×
          p256_field_element_t
        )) (prod_ce(x_26, y_27, temp_29)) } : code (fset.fset0) [interface] _)
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
  (99).
Program Definition point_double
   : package (fset.fset0) [interface] [interface
  #val #[ POINT_DOUBLE ] : point_double_inp → point_double_out ] :=
  (
    [package #def #[ POINT_DOUBLE ] (temp_inp : point_double_inp) : point_double_out { 
    let '(p_33) := temp_inp : p256_jacobian_t in
    ({ code  temp_98 ←
        (ret (p_33)) ;;
      let '(x1_40, y1_37, z1_34) :=
        (temp_98) : (
        p256_field_element_t '×
        p256_field_element_t '×
        p256_field_element_t
      ) in
       '(delta_44 : p256_field_element_t) ←
        ( temp_36 ←
            (nat_mod_exp (z1_34) (@repr U32 2)) ;;
          ret (temp_36)) ;;
       '(gamma_41 : p256_field_element_t) ←
        ( temp_39 ←
            (nat_mod_exp (y1_37) (@repr U32 2)) ;;
          ret (temp_39)) ;;
       '(beta_62 : p256_field_element_t) ←
        ( '(temp_43 : p256_field_element_t) ←
            ((x1_40) *% (gamma_41)) ;;
          ret (temp_43)) ;;
       '(alpha_1_51 : p256_field_element_t) ←
        ( '(temp_46 : p256_field_element_t) ←
            ((x1_40) -% (delta_44)) ;;
          ret (temp_46)) ;;
       '(alpha_2_52 : p256_field_element_t) ←
        ( '(temp_48 : p256_field_element_t) ←
            ((x1_40) +% (delta_44)) ;;
          ret (temp_48)) ;;
       '(alpha_57 : p256_field_element_t) ←
        ( '(temp_50 : p256_field_element_t) ←
            (nat_mod_from_literal (
                0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                @repr U128 3)) ;;
           '(temp_54 : p256_field_element_t) ←
            ((alpha_1_51) *% (alpha_2_52)) ;;
           '(temp_56 : p256_field_element_t) ←
            ((temp_50) *% (temp_54)) ;;
          ret (temp_56)) ;;
       '(x3_80 : p256_field_element_t) ←
        ( temp_59 ←
            (nat_mod_exp (alpha_57) (@repr U32 2)) ;;
           '(temp_61 : p256_field_element_t) ←
            (nat_mod_from_literal (
                0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                @repr U128 8)) ;;
           '(temp_64 : p256_field_element_t) ←
            ((temp_61) *% (beta_62)) ;;
           '(temp_66 : p256_field_element_t) ←
            ((temp_59) -% (temp_64)) ;;
          ret (temp_66)) ;;
       '(z3_71 : p256_field_element_t) ←
        ( '(temp_68 : p256_field_element_t) ←
            ((y1_37) +% (z1_34)) ;;
           temp_70 ←
            (nat_mod_exp (temp_68) (@repr U32 2)) ;;
          ret (temp_70)) ;;
       '(z3_96 : p256_field_element_t) ←
        ( '(temp_73 : p256_field_element_t) ←
            ((gamma_41) +% (delta_44)) ;;
           '(temp_75 : p256_field_element_t) ←
            ((z3_71) -% (temp_73)) ;;
          ret (temp_75)) ;;
       '(y3_1_89 : p256_field_element_t) ←
        ( '(temp_77 : p256_field_element_t) ←
            (nat_mod_from_literal (
                0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                @repr U128 4)) ;;
           '(temp_79 : p256_field_element_t) ←
            ((temp_77) *% (beta_62)) ;;
           '(temp_82 : p256_field_element_t) ←
            ((temp_79) -% (x3_80)) ;;
          ret (temp_82)) ;;
       '(y3_2_92 : p256_field_element_t) ←
        ( '(temp_84 : p256_field_element_t) ←
            (nat_mod_from_literal (
                0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                @repr U128 8)) ;;
           '(temp_86 : p256_field_element_t) ←
            ((gamma_41) *% (gamma_41)) ;;
           '(temp_88 : p256_field_element_t) ←
            ((temp_84) *% (temp_86)) ;;
          ret (temp_88)) ;;
       '(y3_95 : p256_field_element_t) ←
        ( '(temp_91 : p256_field_element_t) ←
            ((alpha_57) *% (y3_1_89)) ;;
           '(temp_94 : p256_field_element_t) ←
            ((temp_91) -% (y3_2_92)) ;;
          ret (temp_94)) ;;
      @ret ((
          p256_field_element_t '×
          p256_field_element_t '×
          p256_field_element_t
        )) (prod_ce(x3_80, y3_95, z3_96)) } : code (fset.fset0) [interface] _)
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
  (110).
Program Definition is_point_at_infinity
   : package (fset.fset0) [interface] [interface
  #val #[ IS_POINT_AT_INFINITY ] : is_point_at_infinity_inp → is_point_at_infinity_out
  ] :=
  (
    [package #def #[ IS_POINT_AT_INFINITY ] (temp_inp : is_point_at_infinity_inp) : is_point_at_infinity_out { 
    let '(p_100) := temp_inp : p256_jacobian_t in
    ({ code  temp_107 ←
        (ret (p_100)) ;;
      let '(x_108, y_109, z_101) :=
        (temp_107) : (
        p256_field_element_t '×
        p256_field_element_t '×
        p256_field_element_t
      ) in
       '(temp_103 : p256_field_element_t) ←
        (nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            @repr U128 0)) ;;
       temp_105 ←
        (nat_mod_equal (z_101) (temp_103)) ;;
      @ret (bool_ChoiceEquality) (temp_105) } : code (fset.fset0) [interface] _)
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
  (121).
Program Definition s1_equal_s2
   : package (fset.fset0) [interface] [interface
  #val #[ S1_EQUAL_S2 ] : s1_equal_s2_inp → s1_equal_s2_out ] :=
  (
    [package #def #[ S1_EQUAL_S2 ] (temp_inp : s1_equal_s2_inp) : s1_equal_s2_out { 
    let '(
      s1_111 , s2_112) := temp_inp : p256_field_element_t '× p256_field_element_t in
    ({ code  temp_114 ←
        (nat_mod_equal (s1_111) (s2_112)) ;;
       '(temp_116 : p256_field_element_t) ←
        (nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            @repr U128 0)) ;;
       '(temp_118 : p256_field_element_t) ←
        (nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            @repr U128 1)) ;;
       '(temp_120 : p256_field_element_t) ←
        (nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            @repr U128 0)) ;;
      @ret ((result error_t p256_jacobian_t)) ((if (
            temp_114):bool_ChoiceEquality then (*inline*) (
            @Err p256_jacobian_t error_t (InvalidAddition)) else (
            @Ok p256_jacobian_t error_t (prod_ce(temp_116, temp_118, temp_120
              ))))) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_s1_equal_s2 : package _ _ _ :=
  (s1_equal_s2).
Fail Next Obligation.

Definition result_128_loc : ChoiceEqualityLocation :=
  (((result error_t p256_jacobian_t) ; 228%nat)).
Notation "'point_add_jacob_inp'" := (
  p256_jacobian_t '× p256_jacobian_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_jacob_out'" := (
  jacobian_result_t : choice_type) (in custom pack_type at level 2).
Definition POINT_ADD_JACOB : nat :=
  (229).
Program Definition point_add_jacob
   : package (CEfset ([result_128_loc])) [interface
  #val #[ IS_POINT_AT_INFINITY ] : is_point_at_infinity_inp → is_point_at_infinity_out ;
  #val #[ S1_EQUAL_S2 ] : s1_equal_s2_inp → s1_equal_s2_out ] [interface
  #val #[ POINT_ADD_JACOB ] : point_add_jacob_inp → point_add_jacob_out ] :=
  (
    [package #def #[ POINT_ADD_JACOB ] (temp_inp : point_add_jacob_inp) : point_add_jacob_out { 
    let '(p_123 , q_122) := temp_inp : p256_jacobian_t '× p256_jacobian_t in
    #import {sig #[ IS_POINT_AT_INFINITY ] : is_point_at_infinity_inp → is_point_at_infinity_out } as is_point_at_infinity ;;
    let is_point_at_infinity := fun x_0 => is_point_at_infinity (x_0) in
    #import {sig #[ S1_EQUAL_S2 ] : s1_equal_s2_inp → s1_equal_s2_out } as s1_equal_s2 ;;
    let s1_equal_s2 := fun x_0 x_1 => s1_equal_s2 (x_0,x_1) in
    ({ code  '(result_128 : (result error_t p256_jacobian_t)) ←
          (ret (@Ok p256_jacobian_t error_t (q_122))) ;;
        #put result_128_loc := result_128 ;;
       '(temp_125 : bool_ChoiceEquality) ←
        (is_point_at_infinity (p_123)) ;;
       '(result_128 : ((result error_t p256_jacobian_t))) ←
        (if negb (temp_125):bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(
                temp_127 : bool_ChoiceEquality) ←
              (is_point_at_infinity (q_122)) ;;
             '(result_128 : ((result error_t p256_jacobian_t))) ←
              (if temp_127:bool_ChoiceEquality
                then (*not state*) (let temp_then :=  '(result_128 : (
                          result error_t p256_jacobian_t)) ←
                      ((ret (@Ok p256_jacobian_t error_t (p_123)))) ;;
                    #put result_128_loc := result_128 ;;
                  
                  @ret (((result error_t p256_jacobian_t))) (result_128) in
                  ({ code temp_then } : code (CEfset (
                        [result_128_loc])) [interface] _))
                else  (({ code  temp_227 ←
                      (ret (p_123)) ;;
                    let '(x1_135, y1_143, z1_129) :=
                      (temp_227) : (
                      p256_field_element_t '×
                      p256_field_element_t '×
                      p256_field_element_t
                    ) in
                     temp_225 ←
                      (ret (q_122)) ;;
                    let '(x2_139, y2_148, z2_132) :=
                      (temp_225) : (
                      p256_field_element_t '×
                      p256_field_element_t '×
                      p256_field_element_t
                    ) in
                     '(z1z1_140 : p256_field_element_t) ←
                      ( temp_131 ←
                          (nat_mod_exp (z1_129) (@repr U32 2)) ;;
                        ret (temp_131)) ;;
                     '(z2z2_136 : p256_field_element_t) ←
                      ( temp_134 ←
                          (nat_mod_exp (z2_132) (@repr U32 2)) ;;
                        ret (temp_134)) ;;
                     '(u1_153 : p256_field_element_t) ←
                      ( '(temp_138 : p256_field_element_t) ←
                          ((x1_135) *% (z2z2_136)) ;;
                        ret (temp_138)) ;;
                     '(u2_154 : p256_field_element_t) ←
                      ( '(temp_142 : p256_field_element_t) ←
                          ((x2_139) *% (z1z1_140)) ;;
                        ret (temp_142)) ;;
                     '(s1_157 : p256_field_element_t) ←
                      ( '(temp_145 : p256_field_element_t) ←
                          ((y1_143) *% (z2_132)) ;;
                         '(temp_147 : p256_field_element_t) ←
                          ((temp_145) *% (z2z2_136)) ;;
                        ret (temp_147)) ;;
                     '(s2_158 : p256_field_element_t) ←
                      ( '(temp_150 : p256_field_element_t) ←
                          ((y2_148) *% (z1_129)) ;;
                         '(temp_152 : p256_field_element_t) ←
                          ((temp_150) *% (z1z1_140)) ;;
                        ret (temp_152)) ;;
                     temp_156 ←
                      (nat_mod_equal (u1_153) (u2_154)) ;;
                     '(result_128 : ((result error_t p256_jacobian_t))) ←
                      (if temp_156:bool_ChoiceEquality
                        then (*not state*) (let temp_then :=  '(result_128 : (
                                  result error_t p256_jacobian_t)) ←
                              (( '(temp_160 : jacobian_result_t) ←
                                    (s1_equal_s2 (s1_157) (s2_158)) ;;
                                  ret (temp_160))) ;;
                            #put result_128_loc := result_128 ;;
                          
                          @ret (((result error_t p256_jacobian_t))) (
                            result_128) in
                          ({ code temp_then } : code (CEfset (
                                [result_128_loc])) [interface
                            #val #[ S1_EQUAL_S2 ] : s1_equal_s2_inp → s1_equal_s2_out
                            ] _))
                        else  (({ code  '(h_165 : p256_field_element_t) ←
                              ( '(temp_162 : p256_field_element_t) ←
                                  ((u2_154) -% (u1_153)) ;;
                                ret (temp_162)) ;;
                             '(i_170 : p256_field_element_t) ←
                              ( '(temp_164 : p256_field_element_t) ←
                                  (nat_mod_from_literal (
                                      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                                      @repr U128 2)) ;;
                                 '(temp_167 : p256_field_element_t) ←
                                  ((temp_164) *% (h_165)) ;;
                                 temp_169 ←
                                  (nat_mod_exp (temp_167) (@repr U32 2)) ;;
                                ret (temp_169)) ;;
                             '(j_189 : p256_field_element_t) ←
                              ( '(temp_172 : p256_field_element_t) ←
                                  ((h_165) *% (i_170)) ;;
                                ret (temp_172)) ;;
                             '(r_186 : p256_field_element_t) ←
                              ( '(temp_174 : p256_field_element_t) ←
                                  (nat_mod_from_literal (
                                      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                                      @repr U128 2)) ;;
                                 '(temp_176 : p256_field_element_t) ←
                                  ((s2_158) -% (s1_157)) ;;
                                 '(temp_178 : p256_field_element_t) ←
                                  ((temp_174) *% (temp_176)) ;;
                                ret (temp_178)) ;;
                             '(v_183 : p256_field_element_t) ←
                              ( '(temp_180 : p256_field_element_t) ←
                                  ((u1_153) *% (i_170)) ;;
                                ret (temp_180)) ;;
                             '(x3_1_193 : p256_field_element_t) ←
                              ( '(temp_182 : p256_field_element_t) ←
                                  (nat_mod_from_literal (
                                      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                                      @repr U128 2)) ;;
                                 '(temp_185 : p256_field_element_t) ←
                                  ((temp_182) *% (v_183)) ;;
                                ret (temp_185)) ;;
                             '(x3_2_192 : p256_field_element_t) ←
                              ( temp_188 ←
                                  (nat_mod_exp (r_186) (@repr U32 2)) ;;
                                 '(temp_191 : p256_field_element_t) ←
                                  ((temp_188) -% (j_189)) ;;
                                ret (temp_191)) ;;
                             '(x3_202 : p256_field_element_t) ←
                              ( '(temp_195 : p256_field_element_t) ←
                                  ((x3_2_192) -% (x3_1_193)) ;;
                                ret (temp_195)) ;;
                             '(y3_1_208 : p256_field_element_t) ←
                              ( '(temp_197 : p256_field_element_t) ←
                                  (nat_mod_from_literal (
                                      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                                      @repr U128 2)) ;;
                                 '(temp_199 : p256_field_element_t) ←
                                  ((temp_197) *% (s1_157)) ;;
                                 '(temp_201 : p256_field_element_t) ←
                                  ((temp_199) *% (j_189)) ;;
                                ret (temp_201)) ;;
                             '(y3_2_207 : p256_field_element_t) ←
                              ( '(temp_204 : p256_field_element_t) ←
                                  ((v_183) -% (x3_202)) ;;
                                 '(temp_206 : p256_field_element_t) ←
                                  ((r_186) *% (temp_204)) ;;
                                ret (temp_206)) ;;
                             '(y3_222 : p256_field_element_t) ←
                              ( '(temp_210 : p256_field_element_t) ←
                                  ((y3_2_207) -% (y3_1_208)) ;;
                                ret (temp_210)) ;;
                             '(z3_215 : p256_field_element_t) ←
                              ( '(temp_212 : p256_field_element_t) ←
                                  ((z1_129) +% (z2_132)) ;;
                                 temp_214 ←
                                  (nat_mod_exp (temp_212) (@repr U32 2)) ;;
                                ret (temp_214)) ;;
                             '(z3_223 : p256_field_element_t) ←
                              ( '(temp_217 : p256_field_element_t) ←
                                  ((z1z1_140) +% (z2z2_136)) ;;
                                 '(temp_219 : p256_field_element_t) ←
                                  ((z3_215) -% (temp_217)) ;;
                                 '(temp_221 : p256_field_element_t) ←
                                  ((temp_219) *% (h_165)) ;;
                                ret (temp_221)) ;;
                             '(result_128 : (
                                    result error_t p256_jacobian_t)) ←
                                ((ret (@Ok p256_jacobian_t error_t (prod_ce(
                                          x3_202,
                                          y3_222,
                                          z3_223
                                        ))))) ;;
                              #put result_128_loc := result_128 ;;
                            
                            @ret (((result error_t p256_jacobian_t))) (
                              result_128) } : code (CEfset (
                                [result_128_loc])) [interface] _))) ;;
                    
                    @ret (((result error_t p256_jacobian_t))) (
                      result_128) } : code (CEfset (
                        [result_128_loc])) [interface
                    #val #[ S1_EQUAL_S2 ] : s1_equal_s2_inp → s1_equal_s2_out
                    ] _))) ;;
            
            @ret (((result error_t p256_jacobian_t))) (result_128) in
            ({ code temp_then } : code (CEfset ([result_128_loc])) [interface
              #val #[ IS_POINT_AT_INFINITY ] : is_point_at_infinity_inp → is_point_at_infinity_out ;
              #val #[ S1_EQUAL_S2 ] : s1_equal_s2_inp → s1_equal_s2_out ] _))
          else @ret (((result error_t p256_jacobian_t))) (result_128)) ;;
      
      @ret ((result error_t p256_jacobian_t)) (result_128) } : code (CEfset (
          [result_128_loc])) [interface
      #val #[ IS_POINT_AT_INFINITY ] : is_point_at_infinity_inp → is_point_at_infinity_out ;
      #val #[ S1_EQUAL_S2 ] : s1_equal_s2_inp → s1_equal_s2_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_point_add_jacob : package _ _ _ :=
  (seq_link point_add_jacob link_rest(
      package_is_point_at_infinity,package_s1_equal_s2)).
Fail Next Obligation.

Definition q_236_loc : ChoiceEqualityLocation :=
  (((p256_field_element_t '× p256_field_element_t '× p256_field_element_t
      ) ; 254%nat)).
Notation "'ltr_mul_inp'" := (
  p256_scalar_t '× p256_jacobian_t : choice_type) (in custom pack_type at level 2).
Notation "'ltr_mul_out'" := (
  jacobian_result_t : choice_type) (in custom pack_type at level 2).
Definition LTR_MUL : nat :=
  (255).
Program Definition ltr_mul
   : package (CEfset ([q_236_loc])) [interface
  #val #[ POINT_ADD_JACOB ] : point_add_jacob_inp → point_add_jacob_out ;
  #val #[ POINT_DOUBLE ] : point_double_inp → point_double_out ] [interface
  #val #[ LTR_MUL ] : ltr_mul_inp → ltr_mul_out ] :=
  ([package #def #[ LTR_MUL ] (temp_inp : ltr_mul_inp) : ltr_mul_out { 
    let '(k_239 , p_251) := temp_inp : p256_scalar_t '× p256_jacobian_t in
    #import {sig #[ POINT_ADD_JACOB ] : point_add_jacob_inp → point_add_jacob_out } as point_add_jacob ;;
    let point_add_jacob := fun x_0 x_1 => point_add_jacob (x_0,x_1) in
    #import {sig #[ POINT_DOUBLE ] : point_double_inp → point_double_out } as point_double ;;
    let point_double := fun x_0 => point_double (x_0) in
    ({ code  '(q_236 : (
              p256_field_element_t '×
              p256_field_element_t '×
              p256_field_element_t
            )) ←
          ( '(temp_231 : p256_field_element_t) ←
              (nat_mod_from_literal (
                  0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                  @repr U128 0)) ;;
             '(temp_233 : p256_field_element_t) ←
              (nat_mod_from_literal (
                  0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                  @repr U128 1)) ;;
             '(temp_235 : p256_field_element_t) ←
              (nat_mod_from_literal (
                  0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                  @repr U128 0)) ;;
            ret (prod_ce(temp_231, temp_233, temp_235))) ;;
        #put q_236_loc := q_236 ;;
      bnd(ChoiceEqualityMonad.result_bind_code error_t , (
          (
            p256_field_element_t '×
            p256_field_element_t '×
            p256_field_element_t
          )
        ) , _ , CEfset ([q_236_loc])) q_236 ⇠
      (foldi_bind_code' (usize 0) (bits_v) (q_236) (fun i_242 q_236 =>
        ({ code  '(q_236 : (
                  p256_field_element_t '×
                  p256_field_element_t '×
                  p256_field_element_t
                )) ←
              (( '(temp_238 : p256_jacobian_t) ←
                    (point_double (q_236)) ;;
                  ret (temp_238))) ;;
            #put q_236_loc := q_236 ;;
          
           '(temp_241 : uint_size) ←
            ((bits_v) .- (usize 1)) ;;
           '(temp_244 : uint_size) ←
            ((temp_241) .- (i_242)) ;;
           temp_246 ←
            (nat_mod_get_bit (k_239) (temp_244)) ;;
           '(temp_248 : p256_scalar_t) ←
            (nat_mod_one ) ;;
           temp_250 ←
            (nat_mod_equal (temp_246) (temp_248)) ;;
          bnd(ChoiceEqualityMonad.result_bind_code error_t , (
              (
                p256_field_element_t '×
                p256_field_element_t '×
                p256_field_element_t
              )
            ) , _ , CEfset ([q_236_loc])) 'q_236 ⇠
          (if temp_250 : bool_ChoiceEquality
            then (*state*) (({ code bndm(
                  ChoiceEqualityMonad.result_bind_code error_t , (
                    p256_field_element_t '×
                    p256_field_element_t '×
                    p256_field_element_t
                  ) , _ , CEfset ([q_236_loc])) q_236 ⇠
                (({ code ( '(temp_253 : jacobian_result_t) ←
                        (point_add_jacob (q_236) (p_251)) ;;
                      ret (temp_253)) } : code _ _ _)) in
                ({ code @ret ((result error_t (
                        (
                          p256_field_element_t '×
                          p256_field_element_t '×
                          p256_field_element_t
                        )
                      ))) (@Ok (
                      (
                        p256_field_element_t '×
                        p256_field_element_t '×
                        p256_field_element_t
                      )
                    ) error_t (q_236)) } : code (CEfset (
                      [q_236_loc])) [interface
                  #val #[ POINT_ADD_JACOB ] : point_add_jacob_inp → point_add_jacob_out
                  ] _) } : code (CEfset ([q_236_loc])) [interface
                #val #[ POINT_ADD_JACOB ] : point_add_jacob_inp → point_add_jacob_out
                ] _))
            else ({ code @ret ((result error_t (
                    (
                      p256_field_element_t '×
                      p256_field_element_t '×
                      p256_field_element_t
                    )
                  ))) (@Ok (
                  (
                    p256_field_element_t '×
                    p256_field_element_t '×
                    p256_field_element_t
                  )
                ) error_t (q_236)) } : code _ _ _) ) in
          ({ code @ret ((result error_t (
                  (
                    p256_field_element_t '×
                    p256_field_element_t '×
                    p256_field_element_t
                  )
                ))) (@Ok (
                (
                  p256_field_element_t '×
                  p256_field_element_t '×
                  p256_field_element_t
                )
              ) error_t (q_236)) } : code (CEfset ([q_236_loc])) [interface
            #val #[ POINT_ADD_JACOB ] : point_add_jacob_inp → point_add_jacob_out ;
            #val #[ POINT_DOUBLE ] : point_double_inp → point_double_out
            ] _) } : code (CEfset ([q_236_loc])) [interface
          #val #[ POINT_ADD_JACOB ] : point_add_jacob_inp → point_add_jacob_out ;
          #val #[ POINT_DOUBLE ] : point_double_inp → point_double_out
          ] _))) in
      ({ code @ret ((result error_t p256_jacobian_t)) (
          @Ok p256_jacobian_t error_t (q_236)) } : code (CEfset (
            [q_236_loc])) [interface
        #val #[ POINT_ADD_JACOB ] : point_add_jacob_inp → point_add_jacob_out ;
        #val #[ POINT_DOUBLE ] : point_double_inp → point_double_out
        ] _) } : code (CEfset ([q_236_loc])) [interface
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
  (265).
Program Definition p256_point_mul
   : package (CEfset ([])) [interface
  #val #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out ;
  #val #[ JACOBIAN_TO_AFFINE ] : jacobian_to_affine_inp → jacobian_to_affine_out ;
  #val #[ LTR_MUL ] : ltr_mul_inp → ltr_mul_out ] [interface
  #val #[ P256_POINT_MUL ] : p256_point_mul_inp → p256_point_mul_out ] :=
  (
    [package #def #[ P256_POINT_MUL ] (temp_inp : p256_point_mul_inp) : p256_point_mul_out { 
    let '(k_256 , p_257) := temp_inp : p256_scalar_t '× affine_t in
    #import {sig #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out } as affine_to_jacobian ;;
    let affine_to_jacobian := fun x_0 => affine_to_jacobian (x_0) in
    #import {sig #[ JACOBIAN_TO_AFFINE ] : jacobian_to_affine_inp → jacobian_to_affine_out } as jacobian_to_affine ;;
    let jacobian_to_affine := fun x_0 => jacobian_to_affine (x_0) in
    #import {sig #[ LTR_MUL ] : ltr_mul_inp → ltr_mul_out } as ltr_mul ;;
    let ltr_mul := fun x_0 x_1 => ltr_mul (x_0,x_1) in
    ({ code bnd(
        ChoiceEqualityMonad.result_bind_code error_t , p256_jacobian_t , _ , CEfset (
          [])) jac_262 ⇠
      (({ code  '(temp_259 : p256_jacobian_t) ←
            (affine_to_jacobian (p_257)) ;;
           '(temp_261 : jacobian_result_t) ←
            (ltr_mul (k_256) (temp_259)) ;;
          @ret _ (temp_261) } : code (CEfset ([])) [interface
          #val #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out ;
          #val #[ LTR_MUL ] : ltr_mul_inp → ltr_mul_out ] _)) in
      ({ code  '(temp_264 : affine_t) ←
          (jacobian_to_affine (jac_262)) ;;
        @ret ((result error_t affine_t)) (@Ok affine_t error_t (
            temp_264)) } : code (CEfset ([])) [interface
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
  (410).
Program Definition p256_point_mul_base
   : package (CEfset ([])) [interface
  #val #[ P256_POINT_MUL ] : p256_point_mul_inp → p256_point_mul_out
  ] [interface
  #val #[ P256_POINT_MUL_BASE ] : p256_point_mul_base_inp → p256_point_mul_base_out
  ] :=
  (
    [package #def #[ P256_POINT_MUL_BASE ] (temp_inp : p256_point_mul_base_inp) : p256_point_mul_base_out { 
    let '(k_406) := temp_inp : p256_scalar_t in
    #import {sig #[ P256_POINT_MUL ] : p256_point_mul_inp → p256_point_mul_out } as p256_point_mul ;;
    let p256_point_mul := fun x_0 x_1 => p256_point_mul (x_0,x_1) in
    ({ code  '(base_point_407 : (p256_field_element_t '× p256_field_element_t
          )) ←
        ( '(temp_267 : int8) ←
            (secret (@repr U8 107)) ;;
           '(temp_269 : int8) ←
            (secret (@repr U8 23)) ;;
           '(temp_271 : int8) ←
            (secret (@repr U8 209)) ;;
           '(temp_273 : int8) ←
            (secret (@repr U8 242)) ;;
           '(temp_275 : int8) ←
            (secret (@repr U8 225)) ;;
           '(temp_277 : int8) ←
            (secret (@repr U8 44)) ;;
           '(temp_279 : int8) ←
            (secret (@repr U8 66)) ;;
           '(temp_281 : int8) ←
            (secret (@repr U8 71)) ;;
           '(temp_283 : int8) ←
            (secret (@repr U8 248)) ;;
           '(temp_285 : int8) ←
            (secret (@repr U8 188)) ;;
           '(temp_287 : int8) ←
            (secret (@repr U8 230)) ;;
           '(temp_289 : int8) ←
            (secret (@repr U8 229)) ;;
           '(temp_291 : int8) ←
            (secret (@repr U8 99)) ;;
           '(temp_293 : int8) ←
            (secret (@repr U8 164)) ;;
           '(temp_295 : int8) ←
            (secret (@repr U8 64)) ;;
           '(temp_297 : int8) ←
            (secret (@repr U8 242)) ;;
           '(temp_299 : int8) ←
            (secret (@repr U8 119)) ;;
           '(temp_301 : int8) ←
            (secret (@repr U8 3)) ;;
           '(temp_303 : int8) ←
            (secret (@repr U8 125)) ;;
           '(temp_305 : int8) ←
            (secret (@repr U8 129)) ;;
           '(temp_307 : int8) ←
            (secret (@repr U8 45)) ;;
           '(temp_309 : int8) ←
            (secret (@repr U8 235)) ;;
           '(temp_311 : int8) ←
            (secret (@repr U8 51)) ;;
           '(temp_313 : int8) ←
            (secret (@repr U8 160)) ;;
           '(temp_315 : int8) ←
            (secret (@repr U8 244)) ;;
           '(temp_317 : int8) ←
            (secret (@repr U8 161)) ;;
           '(temp_319 : int8) ←
            (secret (@repr U8 57)) ;;
           '(temp_321 : int8) ←
            (secret (@repr U8 69)) ;;
           '(temp_323 : int8) ←
            (secret (@repr U8 216)) ;;
           '(temp_325 : int8) ←
            (secret (@repr U8 152)) ;;
           '(temp_327 : int8) ←
            (secret (@repr U8 194)) ;;
           '(temp_329 : int8) ←
            (secret (@repr U8 150)) ;;
           '(temp_331 : nseq uint8 32) ←
            (array_from_list uint8 [
                temp_267;
                temp_269;
                temp_271;
                temp_273;
                temp_275;
                temp_277;
                temp_279;
                temp_281;
                temp_283;
                temp_285;
                temp_287;
                temp_289;
                temp_291;
                temp_293;
                temp_295;
                temp_297;
                temp_299;
                temp_301;
                temp_303;
                temp_305;
                temp_307;
                temp_309;
                temp_311;
                temp_313;
                temp_315;
                temp_317;
                temp_319;
                temp_321;
                temp_323;
                temp_325;
                temp_327;
                temp_329
              ]) ;;
           '(temp_333 : seq uint8) ←
            (array_to_seq (temp_331)) ;;
           '(temp_335 : p256_field_element_t) ←
            (nat_mod_from_byte_seq_be (temp_333)) ;;
           '(temp_337 : int8) ←
            (secret (@repr U8 79)) ;;
           '(temp_339 : int8) ←
            (secret (@repr U8 227)) ;;
           '(temp_341 : int8) ←
            (secret (@repr U8 66)) ;;
           '(temp_343 : int8) ←
            (secret (@repr U8 226)) ;;
           '(temp_345 : int8) ←
            (secret (@repr U8 254)) ;;
           '(temp_347 : int8) ←
            (secret (@repr U8 26)) ;;
           '(temp_349 : int8) ←
            (secret (@repr U8 127)) ;;
           '(temp_351 : int8) ←
            (secret (@repr U8 155)) ;;
           '(temp_353 : int8) ←
            (secret (@repr U8 142)) ;;
           '(temp_355 : int8) ←
            (secret (@repr U8 231)) ;;
           '(temp_357 : int8) ←
            (secret (@repr U8 235)) ;;
           '(temp_359 : int8) ←
            (secret (@repr U8 74)) ;;
           '(temp_361 : int8) ←
            (secret (@repr U8 124)) ;;
           '(temp_363 : int8) ←
            (secret (@repr U8 15)) ;;
           '(temp_365 : int8) ←
            (secret (@repr U8 158)) ;;
           '(temp_367 : int8) ←
            (secret (@repr U8 22)) ;;
           '(temp_369 : int8) ←
            (secret (@repr U8 43)) ;;
           '(temp_371 : int8) ←
            (secret (@repr U8 206)) ;;
           '(temp_373 : int8) ←
            (secret (@repr U8 51)) ;;
           '(temp_375 : int8) ←
            (secret (@repr U8 87)) ;;
           '(temp_377 : int8) ←
            (secret (@repr U8 107)) ;;
           '(temp_379 : int8) ←
            (secret (@repr U8 49)) ;;
           '(temp_381 : int8) ←
            (secret (@repr U8 94)) ;;
           '(temp_383 : int8) ←
            (secret (@repr U8 206)) ;;
           '(temp_385 : int8) ←
            (secret (@repr U8 203)) ;;
           '(temp_387 : int8) ←
            (secret (@repr U8 182)) ;;
           '(temp_389 : int8) ←
            (secret (@repr U8 64)) ;;
           '(temp_391 : int8) ←
            (secret (@repr U8 104)) ;;
           '(temp_393 : int8) ←
            (secret (@repr U8 55)) ;;
           '(temp_395 : int8) ←
            (secret (@repr U8 191)) ;;
           '(temp_397 : int8) ←
            (secret (@repr U8 81)) ;;
           '(temp_399 : int8) ←
            (secret (@repr U8 245)) ;;
           '(temp_401 : nseq uint8 32) ←
            (array_from_list uint8 [
                temp_337;
                temp_339;
                temp_341;
                temp_343;
                temp_345;
                temp_347;
                temp_349;
                temp_351;
                temp_353;
                temp_355;
                temp_357;
                temp_359;
                temp_361;
                temp_363;
                temp_365;
                temp_367;
                temp_369;
                temp_371;
                temp_373;
                temp_375;
                temp_377;
                temp_379;
                temp_381;
                temp_383;
                temp_385;
                temp_387;
                temp_389;
                temp_391;
                temp_393;
                temp_395;
                temp_397;
                temp_399
              ]) ;;
           '(temp_403 : seq uint8) ←
            (array_to_seq (temp_401)) ;;
           '(temp_405 : p256_field_element_t) ←
            (nat_mod_from_byte_seq_be (temp_403)) ;;
          ret (prod_ce(temp_335, temp_405))) ;;
       '(temp_409 : affine_result_t) ←
        (p256_point_mul (k_406) (base_point_407)) ;;
      @ret (affine_result_t) (temp_409) } : code (CEfset ([])) [interface
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
  (422).
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
    let '(p_411 , q_414) := temp_inp : affine_t '× affine_t in
    #import {sig #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out } as affine_to_jacobian ;;
    let affine_to_jacobian := fun x_0 => affine_to_jacobian (x_0) in
    #import {sig #[ JACOBIAN_TO_AFFINE ] : jacobian_to_affine_inp → jacobian_to_affine_out } as jacobian_to_affine ;;
    let jacobian_to_affine := fun x_0 => jacobian_to_affine (x_0) in
    #import {sig #[ POINT_ADD_JACOB ] : point_add_jacob_inp → point_add_jacob_out } as point_add_jacob ;;
    let point_add_jacob := fun x_0 x_1 => point_add_jacob (x_0,x_1) in
    ({ code bnd(
        ChoiceEqualityMonad.result_bind_code error_t , p256_jacobian_t , _ , CEfset (
          [])) r_419 ⇠
      (({ code  '(temp_413 : p256_jacobian_t) ←
            (affine_to_jacobian (p_411)) ;;
           '(temp_416 : p256_jacobian_t) ←
            (affine_to_jacobian (q_414)) ;;
           '(temp_418 : jacobian_result_t) ←
            (point_add_jacob (temp_413) (temp_416)) ;;
          @ret _ (temp_418) } : code (CEfset ([])) [interface
          #val #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out ;
          #val #[ POINT_ADD_JACOB ] : point_add_jacob_inp → point_add_jacob_out
          ] _)) in
      ({ code  '(temp_421 : affine_t) ←
          (jacobian_to_affine (r_419)) ;;
        @ret ((result error_t affine_t)) (@Ok affine_t error_t (
            temp_421)) } : code (CEfset ([])) [interface
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
  (435).
Program Definition point_add
   : package (CEfset ([])) [interface
  #val #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out ;
  #val #[ JACOBIAN_TO_AFFINE ] : jacobian_to_affine_inp → jacobian_to_affine_out ;
  #val #[ POINT_ADD_DISTINCT ] : point_add_distinct_inp → point_add_distinct_out ;
  #val #[ POINT_DOUBLE ] : point_double_inp → point_double_out ] [interface
  #val #[ POINT_ADD ] : point_add_inp → point_add_out ] :=
  ([package #def #[ POINT_ADD ] (temp_inp : point_add_inp) : point_add_out { 
    let '(p_423 , q_424) := temp_inp : affine_t '× affine_t in
    #import {sig #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out } as affine_to_jacobian ;;
    let affine_to_jacobian := fun x_0 => affine_to_jacobian (x_0) in
    #import {sig #[ JACOBIAN_TO_AFFINE ] : jacobian_to_affine_inp → jacobian_to_affine_out } as jacobian_to_affine ;;
    let jacobian_to_affine := fun x_0 => jacobian_to_affine (x_0) in
    #import {sig #[ POINT_ADD_DISTINCT ] : point_add_distinct_inp → point_add_distinct_out } as point_add_distinct ;;
    let point_add_distinct := fun x_0 x_1 => point_add_distinct (x_0,x_1) in
    #import {sig #[ POINT_DOUBLE ] : point_double_inp → point_double_out } as point_double ;;
    let point_double := fun x_0 => point_double (x_0) in
    ({ code  '(temp_426 : bool_ChoiceEquality) ←
        ((p_423) !=.? (q_424)) ;;
       '(temp_428 : affine_result_t) ←
        (point_add_distinct (p_423) (q_424)) ;;
       '(temp_430 : p256_jacobian_t) ←
        (affine_to_jacobian (p_423)) ;;
       '(temp_432 : p256_jacobian_t) ←
        (point_double (temp_430)) ;;
       '(temp_434 : affine_t) ←
        (jacobian_to_affine (temp_432)) ;;
      @ret (affine_result_t) ((if (
            temp_426):bool_ChoiceEquality then (*inline*) (temp_428) else (
            @Ok affine_t error_t (temp_434)))) } : code (CEfset ([])) [interface
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

Definition valid_452_loc : ChoiceEqualityLocation :=
  ((bool_ChoiceEquality ; 464%nat)).
Definition all_zero_451_loc : ChoiceEqualityLocation :=
  ((bool_ChoiceEquality ; 465%nat)).
Notation "'p256_validate_private_key_inp'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'p256_validate_private_key_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition P256_VALIDATE_PRIVATE_KEY : nat :=
  (466).
Program Definition p256_validate_private_key
   : package (CEfset (
      [valid_452_loc ; all_zero_451_loc])) [interface] [interface
  #val #[ P256_VALIDATE_PRIVATE_KEY ] : p256_validate_private_key_inp → p256_validate_private_key_out
  ] :=
  (
    [package #def #[ P256_VALIDATE_PRIVATE_KEY ] (temp_inp : p256_validate_private_key_inp) : p256_validate_private_key_out { 
    let '(k_436) := temp_inp : byte_seq in
    ({ code  '(valid_452 : bool_ChoiceEquality) ←
          (ret ((true : bool_ChoiceEquality))) ;;
        #put valid_452_loc := valid_452 ;;
       '(k_element_439 : p256_scalar_t) ←
        ( '(temp_438 : p256_scalar_t) ←
            (nat_mod_from_byte_seq_be (k_436)) ;;
          ret (temp_438)) ;;
       '(k_element_bytes_454 : seq uint8) ←
        ( temp_441 ←
            (nat_mod_to_byte_seq_be (k_element_439)) ;;
          ret (temp_441)) ;;
       '(all_zero_451 : bool_ChoiceEquality) ←
          (ret ((true : bool_ChoiceEquality))) ;;
        #put all_zero_451_loc := all_zero_451 ;;
       '(temp_443 : uint_size) ←
        (seq_len (k_436)) ;;
       temp_463 ←
        (foldi' (usize 0) (temp_443) prod_ce(valid_452, all_zero_451) (
              L2 := CEfset ([valid_452_loc ; all_zero_451_loc])) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_444 '(
              valid_452,
              all_zero_451
            ) =>
            ({ code  temp_446 ←
                (seq_index (k_436) (i_444)) ;;
               '(temp_448 : int8) ←
                (secret (@repr U8 0)) ;;
               temp_450 ←
                (uint8_equal (temp_446) (temp_448)) ;;
               '(all_zero_451 : (bool_ChoiceEquality)) ←
                (if negb (temp_450):bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(
                          all_zero_451 : bool_ChoiceEquality) ←
                        ((ret ((false : bool_ChoiceEquality)))) ;;
                      #put all_zero_451_loc := all_zero_451 ;;
                    
                    @ret ((bool_ChoiceEquality)) (all_zero_451) in
                    ({ code temp_then } : code (CEfset (
                          [valid_452_loc ; all_zero_451_loc])) [interface] _))
                  else @ret ((bool_ChoiceEquality)) (all_zero_451)) ;;
              
               '(temp_455 : uint8) ←
                (seq_index (k_element_bytes_454) (i_444)) ;;
               temp_457 ←
                (seq_index (k_436) (i_444)) ;;
               temp_459 ←
                (uint8_equal (temp_455) (temp_457)) ;;
               '(valid_452 : (bool_ChoiceEquality)) ←
                (if negb (temp_459):bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(
                          valid_452 : bool_ChoiceEquality) ←
                        ((ret ((false : bool_ChoiceEquality)))) ;;
                      #put valid_452_loc := valid_452 ;;
                    
                    @ret ((bool_ChoiceEquality)) (valid_452) in
                    ({ code temp_then } : code (CEfset (
                          [valid_452_loc ; all_zero_451_loc])) [interface] _))
                  else @ret ((bool_ChoiceEquality)) (valid_452)) ;;
              
              @ret ((bool_ChoiceEquality '× bool_ChoiceEquality)) (prod_ce(
                  valid_452,
                  all_zero_451
                )) } : code (CEfset (
                  [valid_452_loc ; all_zero_451_loc])) [interface] _))) ;;
      let '(valid_452, all_zero_451) :=
        (temp_463) : (bool_ChoiceEquality '× bool_ChoiceEquality) in
      
       '(temp_461 : bool_ChoiceEquality) ←
        ((valid_452) && (negb (all_zero_451))) ;;
      @ret (bool_ChoiceEquality) (temp_461) } : code (CEfset (
          [valid_452_loc ; all_zero_451_loc])) [interface] _)
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
  (563).
Program Definition p256_validate_public_key
   : package (fset.fset0) [interface
  #val #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out ;
  #val #[ IS_POINT_AT_INFINITY ] : is_point_at_infinity_inp → is_point_at_infinity_out
  ] [interface
  #val #[ P256_VALIDATE_PUBLIC_KEY ] : p256_validate_public_key_inp → p256_validate_public_key_out
  ] :=
  (
    [package #def #[ P256_VALIDATE_PUBLIC_KEY ] (temp_inp : p256_validate_public_key_inp) : p256_validate_public_key_out { 
    let '(p_533) := temp_inp : affine_t in
    #import {sig #[ AFFINE_TO_JACOBIAN ] : affine_to_jacobian_inp → affine_to_jacobian_out } as affine_to_jacobian ;;
    let affine_to_jacobian := fun x_0 => affine_to_jacobian (x_0) in
    #import {sig #[ IS_POINT_AT_INFINITY ] : is_point_at_infinity_inp → is_point_at_infinity_out } as is_point_at_infinity ;;
    let is_point_at_infinity := fun x_0 => is_point_at_infinity (x_0) in
    ({ code  '(b_552 : p256_field_element_t) ←
        ( '(temp_468 : int8) ←
            (secret (@repr U8 90)) ;;
           '(temp_470 : int8) ←
            (secret (@repr U8 198)) ;;
           '(temp_472 : int8) ←
            (secret (@repr U8 53)) ;;
           '(temp_474 : int8) ←
            (secret (@repr U8 216)) ;;
           '(temp_476 : int8) ←
            (secret (@repr U8 170)) ;;
           '(temp_478 : int8) ←
            (secret (@repr U8 58)) ;;
           '(temp_480 : int8) ←
            (secret (@repr U8 147)) ;;
           '(temp_482 : int8) ←
            (secret (@repr U8 231)) ;;
           '(temp_484 : int8) ←
            (secret (@repr U8 179)) ;;
           '(temp_486 : int8) ←
            (secret (@repr U8 235)) ;;
           '(temp_488 : int8) ←
            (secret (@repr U8 189)) ;;
           '(temp_490 : int8) ←
            (secret (@repr U8 85)) ;;
           '(temp_492 : int8) ←
            (secret (@repr U8 118)) ;;
           '(temp_494 : int8) ←
            (secret (@repr U8 152)) ;;
           '(temp_496 : int8) ←
            (secret (@repr U8 134)) ;;
           '(temp_498 : int8) ←
            (secret (@repr U8 188)) ;;
           '(temp_500 : int8) ←
            (secret (@repr U8 101)) ;;
           '(temp_502 : int8) ←
            (secret (@repr U8 29)) ;;
           '(temp_504 : int8) ←
            (secret (@repr U8 6)) ;;
           '(temp_506 : int8) ←
            (secret (@repr U8 176)) ;;
           '(temp_508 : int8) ←
            (secret (@repr U8 204)) ;;
           '(temp_510 : int8) ←
            (secret (@repr U8 83)) ;;
           '(temp_512 : int8) ←
            (secret (@repr U8 176)) ;;
           '(temp_514 : int8) ←
            (secret (@repr U8 246)) ;;
           '(temp_516 : int8) ←
            (secret (@repr U8 59)) ;;
           '(temp_518 : int8) ←
            (secret (@repr U8 206)) ;;
           '(temp_520 : int8) ←
            (secret (@repr U8 60)) ;;
           '(temp_522 : int8) ←
            (secret (@repr U8 62)) ;;
           '(temp_524 : int8) ←
            (secret (@repr U8 39)) ;;
           '(temp_526 : int8) ←
            (secret (@repr U8 210)) ;;
           '(temp_528 : int8) ←
            (secret (@repr U8 96)) ;;
           '(temp_530 : int8) ←
            (secret (@repr U8 75)) ;;
           '(temp_532 : p256_field_element_t) ←
            (nat_mod_from_byte_seq_be (seq_from_list _ [
                  temp_468;
                  temp_470;
                  temp_472;
                  temp_474;
                  temp_476;
                  temp_478;
                  temp_480;
                  temp_482;
                  temp_484;
                  temp_486;
                  temp_488;
                  temp_490;
                  temp_492;
                  temp_494;
                  temp_496;
                  temp_498;
                  temp_500;
                  temp_502;
                  temp_504;
                  temp_506;
                  temp_508;
                  temp_510;
                  temp_512;
                  temp_514;
                  temp_516;
                  temp_518;
                  temp_520;
                  temp_522;
                  temp_524;
                  temp_526;
                  temp_528;
                  temp_530
                ])) ;;
          ret (temp_532)) ;;
       '(point_at_infinity_557 : bool_ChoiceEquality) ←
        ( '(temp_535 : p256_jacobian_t) ←
            (affine_to_jacobian (p_533)) ;;
           '(temp_537 : bool_ChoiceEquality) ←
            (is_point_at_infinity (temp_535)) ;;
          ret (temp_537)) ;;
       temp_562 ←
        (ret (p_533)) ;;
      let '(x_541, y_538) :=
        (temp_562) : (p256_field_element_t '× p256_field_element_t) in
       '(on_curve_558 : bool_ChoiceEquality) ←
        ( '(temp_540 : p256_field_element_t) ←
            ((y_538) *% (y_538)) ;;
           '(temp_543 : p256_field_element_t) ←
            ((x_541) *% (x_541)) ;;
           '(temp_545 : p256_field_element_t) ←
            ((temp_543) *% (x_541)) ;;
           '(temp_547 : p256_field_element_t) ←
            (nat_mod_from_literal (
                0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                @repr U128 3)) ;;
           '(temp_549 : p256_field_element_t) ←
            ((temp_547) *% (x_541)) ;;
           '(temp_551 : p256_field_element_t) ←
            ((temp_545) -% (temp_549)) ;;
           '(temp_554 : p256_field_element_t) ←
            ((temp_551) +% (b_552)) ;;
           '(temp_556 : bool_ChoiceEquality) ←
            ((temp_540) =.? (temp_554)) ;;
          ret (temp_556)) ;;
       '(temp_560 : bool_ChoiceEquality) ←
        ((negb (point_at_infinity_557)) && (on_curve_558)) ;;
      @ret (bool_ChoiceEquality) (temp_560) } : code (fset.fset0) [interface
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
  (715).
Program Definition p256_calculate_w
   : package (fset.fset0) [interface] [interface
  #val #[ P256_CALCULATE_W ] : p256_calculate_w_inp → p256_calculate_w_out
  ] :=
  (
    [package #def #[ P256_CALCULATE_W ] (temp_inp : p256_calculate_w_inp) : p256_calculate_w_out { 
    let '(x_696) := temp_inp : p256_field_element_t in
    ({ code  '(b_707 : p256_field_element_t) ←
        ( '(temp_565 : int8) ←
            (secret (@repr U8 90)) ;;
           '(temp_567 : int8) ←
            (secret (@repr U8 198)) ;;
           '(temp_569 : int8) ←
            (secret (@repr U8 53)) ;;
           '(temp_571 : int8) ←
            (secret (@repr U8 216)) ;;
           '(temp_573 : int8) ←
            (secret (@repr U8 170)) ;;
           '(temp_575 : int8) ←
            (secret (@repr U8 58)) ;;
           '(temp_577 : int8) ←
            (secret (@repr U8 147)) ;;
           '(temp_579 : int8) ←
            (secret (@repr U8 231)) ;;
           '(temp_581 : int8) ←
            (secret (@repr U8 179)) ;;
           '(temp_583 : int8) ←
            (secret (@repr U8 235)) ;;
           '(temp_585 : int8) ←
            (secret (@repr U8 189)) ;;
           '(temp_587 : int8) ←
            (secret (@repr U8 85)) ;;
           '(temp_589 : int8) ←
            (secret (@repr U8 118)) ;;
           '(temp_591 : int8) ←
            (secret (@repr U8 152)) ;;
           '(temp_593 : int8) ←
            (secret (@repr U8 134)) ;;
           '(temp_595 : int8) ←
            (secret (@repr U8 188)) ;;
           '(temp_597 : int8) ←
            (secret (@repr U8 101)) ;;
           '(temp_599 : int8) ←
            (secret (@repr U8 29)) ;;
           '(temp_601 : int8) ←
            (secret (@repr U8 6)) ;;
           '(temp_603 : int8) ←
            (secret (@repr U8 176)) ;;
           '(temp_605 : int8) ←
            (secret (@repr U8 204)) ;;
           '(temp_607 : int8) ←
            (secret (@repr U8 83)) ;;
           '(temp_609 : int8) ←
            (secret (@repr U8 176)) ;;
           '(temp_611 : int8) ←
            (secret (@repr U8 246)) ;;
           '(temp_613 : int8) ←
            (secret (@repr U8 59)) ;;
           '(temp_615 : int8) ←
            (secret (@repr U8 206)) ;;
           '(temp_617 : int8) ←
            (secret (@repr U8 60)) ;;
           '(temp_619 : int8) ←
            (secret (@repr U8 62)) ;;
           '(temp_621 : int8) ←
            (secret (@repr U8 39)) ;;
           '(temp_623 : int8) ←
            (secret (@repr U8 210)) ;;
           '(temp_625 : int8) ←
            (secret (@repr U8 96)) ;;
           '(temp_627 : int8) ←
            (secret (@repr U8 75)) ;;
           '(temp_629 : p256_field_element_t) ←
            (nat_mod_from_byte_seq_be (seq_from_list _ [
                  temp_565;
                  temp_567;
                  temp_569;
                  temp_571;
                  temp_573;
                  temp_575;
                  temp_577;
                  temp_579;
                  temp_581;
                  temp_583;
                  temp_585;
                  temp_587;
                  temp_589;
                  temp_591;
                  temp_593;
                  temp_595;
                  temp_597;
                  temp_599;
                  temp_601;
                  temp_603;
                  temp_605;
                  temp_607;
                  temp_609;
                  temp_611;
                  temp_613;
                  temp_615;
                  temp_617;
                  temp_619;
                  temp_621;
                  temp_623;
                  temp_625;
                  temp_627
                ])) ;;
          ret (temp_629)) ;;
       '(exp_711 : p256_field_element_t) ←
        ( '(temp_631 : int8) ←
            (secret (@repr U8 63)) ;;
           '(temp_633 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_635 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_637 : int8) ←
            (secret (@repr U8 255)) ;;
           '(temp_639 : int8) ←
            (secret (@repr U8 192)) ;;
           '(temp_641 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_643 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_645 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_647 : int8) ←
            (secret (@repr U8 64)) ;;
           '(temp_649 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_651 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_653 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_655 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_657 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_659 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_661 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_663 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_665 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_667 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_669 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_671 : int8) ←
            (secret (@repr U8 64)) ;;
           '(temp_673 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_675 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_677 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_679 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_681 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_683 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_685 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_687 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_689 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_691 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_693 : int8) ←
            (secret (@repr U8 0)) ;;
           '(temp_695 : p256_field_element_t) ←
            (nat_mod_from_byte_seq_be (seq_from_list _ [
                  temp_631;
                  temp_633;
                  temp_635;
                  temp_637;
                  temp_639;
                  temp_641;
                  temp_643;
                  temp_645;
                  temp_647;
                  temp_649;
                  temp_651;
                  temp_653;
                  temp_655;
                  temp_657;
                  temp_659;
                  temp_661;
                  temp_663;
                  temp_665;
                  temp_667;
                  temp_669;
                  temp_671;
                  temp_673;
                  temp_675;
                  temp_677;
                  temp_679;
                  temp_681;
                  temp_683;
                  temp_685;
                  temp_687;
                  temp_689;
                  temp_691;
                  temp_693
                ])) ;;
          ret (temp_695)) ;;
       '(z_710 : p256_field_element_t) ←
        ( '(temp_698 : p256_field_element_t) ←
            ((x_696) *% (x_696)) ;;
           '(temp_700 : p256_field_element_t) ←
            ((temp_698) *% (x_696)) ;;
           '(temp_702 : p256_field_element_t) ←
            (nat_mod_from_literal (
                0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                @repr U128 3)) ;;
           '(temp_704 : p256_field_element_t) ←
            ((temp_702) *% (x_696)) ;;
           '(temp_706 : p256_field_element_t) ←
            ((temp_700) -% (temp_704)) ;;
           '(temp_709 : p256_field_element_t) ←
            ((temp_706) +% (b_707)) ;;
          ret (temp_709)) ;;
       '(w_714 : p256_field_element_t) ←
        ( temp_713 ←
            (nat_mod_pow_felem (z_710) (exp_711)) ;;
          ret (temp_713)) ;;
      @ret (p256_field_element_t) (w_714) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_p256_calculate_w : package _ _ _ :=
  (p256_calculate_w).
Fail Next Obligation.

