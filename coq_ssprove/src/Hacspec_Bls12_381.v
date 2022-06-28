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

Definition fp_canvas_t  :=
  (nseq (int8) (48)).
Definition fp_t  :=
  (
    nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab).

Definition serialized_fp_t  :=
  ( nseq (uint8) (usize 48)).

Definition array_fp_t  :=
  ( nseq (uint64) (usize 6)).

Definition scalar_canvas_t  :=
  (nseq (int8) (32)).
Definition scalar_t  :=
  (nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000).

Notation "'g1_t'" := ((fp_t '× fp_t '× bool_ChoiceEquality)) : hacspec_scope.

Notation "'fp2_t'" := ((fp_t '× fp_t)) : hacspec_scope.

Notation "'g2_t'" := ((fp2_t '× fp2_t '× bool_ChoiceEquality
)) : hacspec_scope.

Notation "'fp6_t'" := ((fp2_t '× fp2_t '× fp2_t)) : hacspec_scope.

Notation "'fp12_t'" := ((fp6_t '× fp6_t)) : hacspec_scope.


Notation "'fp2fromfp_inp'" := (
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2fromfp_out'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Definition FP2FROMFP : nat :=
  (3).
Program Definition fp2fromfp
   : package (fset.fset0) [interface  ] [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ] :=
  ([package #def #[ FP2FROMFP ] (temp_inp : fp2fromfp_inp) : fp2fromfp_out { 
    let '(n_0) := temp_inp : fp_t in
    ({ code  '(temp_2 : fp_t) ←
        (nat_mod_zero ) ;;
      @ret ((fp_t '× fp_t)) (prod_ce(n_0, temp_2)) } : code (
        fset.fset0) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp2fromfp : package _ _ _ :=
  (fp2fromfp).
Fail Next Obligation.


Notation "'fp2zero_inp'" := (
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'fp2zero_out'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Definition FP2ZERO : nat :=
  (8).
Program Definition fp2zero
   : package (fset.fset0) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ] [interface
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ] :=
  ([package #def #[ FP2ZERO ] (temp_inp : fp2zero_inp) : fp2zero_out { 
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    ({ code  '(temp_5 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_7 : fp2_t) ←
        (fp2fromfp (temp_5)) ;;
      @ret (fp2_t) (temp_7) } : code (fset.fset0) [interface
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp2zero : package _ _ _ :=
  (seq_link fp2zero link_rest(package_fp2fromfp)).
Fail Next Obligation.


Notation "'fp2neg_inp'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2neg_out'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Definition FP2NEG : nat :=
  (22).
Program Definition fp2neg
   : package (fset.fset0) [interface  ] [interface
  #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ] :=
  ([package #def #[ FP2NEG ] (temp_inp : fp2neg_inp) : fp2neg_out { 
    let '(n_9) := temp_inp : fp2_t in
    ({ code  temp_21 ←
        (ret (n_9)) ;;
      let '(n1_12, n2_17) :=
        (temp_21) : (fp_t '× fp_t) in
       '(temp_11 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_14 : fp_t) ←
        ((temp_11) -% (n1_12)) ;;
       '(temp_16 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_19 : fp_t) ←
        ((temp_16) -% (n2_17)) ;;
      @ret ((fp_t '× fp_t)) (prod_ce(temp_14, temp_19)) } : code (
        fset.fset0) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp2neg : package _ _ _ :=
  (fp2neg).
Fail Next Obligation.


Notation "'fp2add_inp'" := (
  fp2_t '× fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2add_out'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Definition FP2ADD : nat :=
  (37).
Program Definition fp2add
   : package (fset.fset0) [interface  ] [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ] :=
  ([package #def #[ FP2ADD ] (temp_inp : fp2add_inp) : fp2add_out { 
    let '(n_23 , m_24) := temp_inp : fp2_t '× fp2_t in
    ({ code  temp_36 ←
        (ret (n_23)) ;;
      let '(n1_25, n2_29) :=
        (temp_36) : (fp_t '× fp_t) in
       temp_34 ←
        (ret (m_24)) ;;
      let '(m1_26, m2_30) :=
        (temp_34) : (fp_t '× fp_t) in
       '(temp_28 : fp_t) ←
        ((n1_25) +% (m1_26)) ;;
       '(temp_32 : fp_t) ←
        ((n2_29) +% (m2_30)) ;;
      @ret ((fp_t '× fp_t)) (prod_ce(temp_28, temp_32)) } : code (
        fset.fset0) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp2add : package _ _ _ :=
  (fp2add).
Fail Next Obligation.


Notation "'fp2sub_inp'" := (
  fp2_t '× fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2sub_out'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Definition FP2SUB : nat :=
  (44).
Program Definition fp2sub
   : package (fset.fset0) [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
  #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ] [interface
  #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ] :=
  ([package #def #[ FP2SUB ] (temp_inp : fp2sub_inp) : fp2sub_out { 
    let '(n_38 , m_39) := temp_inp : fp2_t '× fp2_t in
    #import {sig #[ FP2ADD ] : fp2add_inp → fp2add_out } as fp2add ;;
    let fp2add := fun x_0 x_1 => fp2add (x_0,x_1) in
    #import {sig #[ FP2NEG ] : fp2neg_inp → fp2neg_out } as fp2neg ;;
    let fp2neg := fun x_0 => fp2neg (x_0) in
    ({ code  '(temp_41 : fp2_t) ←
        (fp2neg (m_39)) ;;
       '(temp_43 : fp2_t) ←
        (fp2add (n_38) (temp_41)) ;;
      @ret (fp2_t) (temp_43) } : code (fset.fset0) [interface
      #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
      #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp2sub : package _ _ _ :=
  (seq_link fp2sub link_rest(package_fp2add,package_fp2neg)).
Fail Next Obligation.


Notation "'fp2mul_inp'" := (
  fp2_t '× fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2mul_out'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Definition FP2MUL : nat :=
  (69).
Program Definition fp2mul
   : package (fset.fset0) [interface  ] [interface
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] :=
  ([package #def #[ FP2MUL ] (temp_inp : fp2mul_inp) : fp2mul_out { 
    let '(n_45 , m_46) := temp_inp : fp2_t '× fp2_t in
    ({ code  temp_68 ←
        (ret (n_45)) ;;
      let '(n1_47, n2_51) :=
        (temp_68) : (fp_t '× fp_t) in
       temp_66 ←
        (ret (m_46)) ;;
      let '(m1_48, m2_52) :=
        (temp_66) : (fp_t '× fp_t) in
       '(x1_63 : fp_t) ←
        ( '(temp_50 : fp_t) ←
            ((n1_47) *% (m1_48)) ;;
           '(temp_54 : fp_t) ←
            ((n2_51) *% (m2_52)) ;;
           '(temp_56 : fp_t) ←
            ((temp_50) -% (temp_54)) ;;
          ret (temp_56)) ;;
       '(x2_64 : fp_t) ←
        ( '(temp_58 : fp_t) ←
            ((n1_47) *% (m2_52)) ;;
           '(temp_60 : fp_t) ←
            ((n2_51) *% (m1_48)) ;;
           '(temp_62 : fp_t) ←
            ((temp_58) +% (temp_60)) ;;
          ret (temp_62)) ;;
      @ret ((fp_t '× fp_t)) (prod_ce(x1_63, x2_64)) } : code (
        fset.fset0) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp2mul : package _ _ _ :=
  (fp2mul).
Fail Next Obligation.


Notation "'fp2inv_inp'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2inv_out'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Definition FP2INV : nat :=
  (95).
Program Definition fp2inv
   : package (fset.fset0) [interface  ] [interface
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ] :=
  ([package #def #[ FP2INV ] (temp_inp : fp2inv_inp) : fp2inv_out { 
    let '(n_70) := temp_inp : fp2_t in
    ({ code  temp_94 ←
        (ret (n_70)) ;;
      let '(n1_71, n2_74) :=
        (temp_94) : (fp_t '× fp_t) in
       '(t0_79 : fp_t) ←
        ( '(temp_73 : fp_t) ←
            ((n1_71) *% (n1_71)) ;;
           '(temp_76 : fp_t) ←
            ((n2_74) *% (n2_74)) ;;
           '(temp_78 : fp_t) ←
            ((temp_73) +% (temp_76)) ;;
          ret (temp_78)) ;;
       '(t1_82 : fp_t) ←
        ( temp_81 ←
            (nat_mod_inv (t0_79)) ;;
          ret (temp_81)) ;;
       '(x1_91 : fp_t) ←
        ( '(temp_84 : fp_t) ←
            ((n1_71) *% (t1_82)) ;;
          ret (temp_84)) ;;
       '(x2_92 : fp_t) ←
        ( '(temp_86 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_88 : fp_t) ←
            ((n2_74) *% (t1_82)) ;;
           '(temp_90 : fp_t) ←
            ((temp_86) -% (temp_88)) ;;
          ret (temp_90)) ;;
      @ret ((fp_t '× fp_t)) (prod_ce(x1_91, x2_92)) } : code (
        fset.fset0) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp2inv : package _ _ _ :=
  (fp2inv).
Fail Next Obligation.


Notation "'fp2conjugate_inp'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2conjugate_out'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Definition FP2CONJUGATE : nat :=
  (105).
Program Definition fp2conjugate
   : package (fset.fset0) [interface  ] [interface
  #val #[ FP2CONJUGATE ] : fp2conjugate_inp → fp2conjugate_out ] :=
  (
    [package #def #[ FP2CONJUGATE ] (temp_inp : fp2conjugate_inp) : fp2conjugate_out { 
    let '(n_96) := temp_inp : fp2_t in
    ({ code  temp_104 ←
        (ret (n_96)) ;;
      let '(n1_97, n2_100) :=
        (temp_104) : (fp_t '× fp_t) in
       '(temp_99 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_102 : fp_t) ←
        ((temp_99) -% (n2_100)) ;;
      @ret ((fp_t '× fp_t)) (prod_ce(n1_97, temp_102)) } : code (
        fset.fset0) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp2conjugate : package _ _ _ :=
  (fp2conjugate).
Fail Next Obligation.


Notation "'fp6fromfp2_inp'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6fromfp2_out'" := (
  fp6_t : choice_type) (in custom pack_type at level 2).
Definition FP6FROMFP2 : nat :=
  (111).
Program Definition fp6fromfp2
   : package (fset.fset0) [interface
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ] [interface
  #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ] :=
  ([package #def #[ FP6FROMFP2 ] (temp_inp : fp6fromfp2_inp) : fp6fromfp2_out { 
    let '(n_106) := temp_inp : fp2_t in
    #import {sig #[ FP2ZERO ] : fp2zero_inp → fp2zero_out } as fp2zero ;;
    let fp2zero := fp2zero tt in
    ({ code  '(temp_108 : fp2_t) ←
        (fp2zero ) ;;
       '(temp_110 : fp2_t) ←
        (fp2zero ) ;;
      @ret ((fp2_t '× fp2_t '× fp2_t)) (prod_ce(n_106, temp_108, temp_110
        )) } : code (fset.fset0) [interface
      #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp6fromfp2 : package _ _ _ :=
  (seq_link fp6fromfp2 link_rest(package_fp2zero)).
Fail Next Obligation.


Notation "'fp6zero_inp'" := (
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'fp6zero_out'" := (
  fp6_t : choice_type) (in custom pack_type at level 2).
Definition FP6ZERO : nat :=
  (116).
Program Definition fp6zero
   : package (fset.fset0) [interface
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
  #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ] [interface
  #val #[ FP6ZERO ] : fp6zero_inp → fp6zero_out ] :=
  ([package #def #[ FP6ZERO ] (temp_inp : fp6zero_inp) : fp6zero_out { 
    #import {sig #[ FP2ZERO ] : fp2zero_inp → fp2zero_out } as fp2zero ;;
    let fp2zero := fp2zero tt in
    #import {sig #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out } as fp6fromfp2 ;;
    let fp6fromfp2 := fun x_0 => fp6fromfp2 (x_0) in
    ({ code  '(temp_113 : fp2_t) ←
        (fp2zero ) ;;
       '(temp_115 : fp6_t) ←
        (fp6fromfp2 (temp_113)) ;;
      @ret (fp6_t) (temp_115) } : code (fset.fset0) [interface
      #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
      #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp6zero : package _ _ _ :=
  (seq_link fp6zero link_rest(package_fp2zero,package_fp6fromfp2)).
Fail Next Obligation.


Notation "'fp6neg_inp'" := (
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6neg_out'" := (
  fp6_t : choice_type) (in custom pack_type at level 2).
Definition FP6NEG : nat :=
  (135).
Program Definition fp6neg
   : package (fset.fset0) [interface
  #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ;
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ] [interface
  #val #[ FP6NEG ] : fp6neg_inp → fp6neg_out ] :=
  ([package #def #[ FP6NEG ] (temp_inp : fp6neg_inp) : fp6neg_out { 
    let '(n_117) := temp_inp : fp6_t in
    #import {sig #[ FP2SUB ] : fp2sub_inp → fp2sub_out } as fp2sub ;;
    let fp2sub := fun x_0 x_1 => fp2sub (x_0,x_1) in
    #import {sig #[ FP2ZERO ] : fp2zero_inp → fp2zero_out } as fp2zero ;;
    let fp2zero := fp2zero tt in
    ({ code  temp_134 ←
        (ret (n_117)) ;;
      let '(n1_120, n2_125, n3_130) :=
        (temp_134) : (fp2_t '× fp2_t '× fp2_t) in
       '(temp_119 : fp2_t) ←
        (fp2zero ) ;;
       '(temp_122 : fp2_t) ←
        (fp2sub (temp_119) (n1_120)) ;;
       '(temp_124 : fp2_t) ←
        (fp2zero ) ;;
       '(temp_127 : fp2_t) ←
        (fp2sub (temp_124) (n2_125)) ;;
       '(temp_129 : fp2_t) ←
        (fp2zero ) ;;
       '(temp_132 : fp2_t) ←
        (fp2sub (temp_129) (n3_130)) ;;
      @ret ((fp2_t '× fp2_t '× fp2_t)) (prod_ce(temp_122, temp_127, temp_132
        )) } : code (fset.fset0) [interface
      #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ;
      #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp6neg : package _ _ _ :=
  (seq_link fp6neg link_rest(package_fp2sub,package_fp2zero)).
Fail Next Obligation.


Notation "'fp6add_inp'" := (
  fp6_t '× fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6add_out'" := (
  fp6_t : choice_type) (in custom pack_type at level 2).
Definition FP6ADD : nat :=
  (154).
Program Definition fp6add
   : package (fset.fset0) [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ] [interface
  #val #[ FP6ADD ] : fp6add_inp → fp6add_out ] :=
  ([package #def #[ FP6ADD ] (temp_inp : fp6add_inp) : fp6add_out { 
    let '(n_136 , m_137) := temp_inp : fp6_t '× fp6_t in
    #import {sig #[ FP2ADD ] : fp2add_inp → fp2add_out } as fp2add ;;
    let fp2add := fun x_0 x_1 => fp2add (x_0,x_1) in
    ({ code  temp_153 ←
        (ret (n_136)) ;;
      let '(n1_138, n2_142, n3_146) :=
        (temp_153) : (fp2_t '× fp2_t '× fp2_t) in
       temp_151 ←
        (ret (m_137)) ;;
      let '(m1_139, m2_143, m3_147) :=
        (temp_151) : (fp2_t '× fp2_t '× fp2_t) in
       '(temp_141 : fp2_t) ←
        (fp2add (n1_138) (m1_139)) ;;
       '(temp_145 : fp2_t) ←
        (fp2add (n2_142) (m2_143)) ;;
       '(temp_149 : fp2_t) ←
        (fp2add (n3_146) (m3_147)) ;;
      @ret ((fp2_t '× fp2_t '× fp2_t)) (prod_ce(temp_141, temp_145, temp_149
        )) } : code (fset.fset0) [interface
      #val #[ FP2ADD ] : fp2add_inp → fp2add_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp6add : package _ _ _ :=
  (seq_link fp6add link_rest(package_fp2add)).
Fail Next Obligation.


Notation "'fp6sub_inp'" := (
  fp6_t '× fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6sub_out'" := (
  fp6_t : choice_type) (in custom pack_type at level 2).
Definition FP6SUB : nat :=
  (161).
Program Definition fp6sub
   : package (fset.fset0) [interface
  #val #[ FP6ADD ] : fp6add_inp → fp6add_out ;
  #val #[ FP6NEG ] : fp6neg_inp → fp6neg_out ] [interface
  #val #[ FP6SUB ] : fp6sub_inp → fp6sub_out ] :=
  ([package #def #[ FP6SUB ] (temp_inp : fp6sub_inp) : fp6sub_out { 
    let '(n_155 , m_156) := temp_inp : fp6_t '× fp6_t in
    #import {sig #[ FP6ADD ] : fp6add_inp → fp6add_out } as fp6add ;;
    let fp6add := fun x_0 x_1 => fp6add (x_0,x_1) in
    #import {sig #[ FP6NEG ] : fp6neg_inp → fp6neg_out } as fp6neg ;;
    let fp6neg := fun x_0 => fp6neg (x_0) in
    ({ code  '(temp_158 : fp6_t) ←
        (fp6neg (m_156)) ;;
       '(temp_160 : fp6_t) ←
        (fp6add (n_155) (temp_158)) ;;
      @ret (fp6_t) (temp_160) } : code (fset.fset0) [interface
      #val #[ FP6ADD ] : fp6add_inp → fp6add_out ;
      #val #[ FP6NEG ] : fp6neg_inp → fp6neg_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp6sub : package _ _ _ :=
  (seq_link fp6sub link_rest(package_fp6add,package_fp6neg)).
Fail Next Obligation.


Notation "'fp6mul_inp'" := (
  fp6_t '× fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6mul_out'" := (
  fp6_t : choice_type) (in custom pack_type at level 2).
Definition FP6MUL : nat :=
  (237).
Program Definition fp6mul
   : package (fset.fset0) [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
  #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ] [interface
  #val #[ FP6MUL ] : fp6mul_inp → fp6mul_out ] :=
  ([package #def #[ FP6MUL ] (temp_inp : fp6mul_inp) : fp6mul_out { 
    let '(n_162 , m_163) := temp_inp : fp6_t '× fp6_t in
    #import {sig #[ FP2ADD ] : fp2add_inp → fp2add_out } as fp2add ;;
    let fp2add := fun x_0 x_1 => fp2add (x_0,x_1) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    #import {sig #[ FP2SUB ] : fp2sub_inp → fp2sub_out } as fp2sub ;;
    let fp2sub := fun x_0 x_1 => fp2sub (x_0,x_1) in
    ({ code  temp_236 ←
        (ret (n_162)) ;;
      let '(n1_168, n2_172, n3_176) :=
        (temp_236) : (fp2_t '× fp2_t '× fp2_t) in
       temp_234 ←
        (ret (m_163)) ;;
      let '(m1_169, m2_173, m3_177) :=
        (temp_234) : (fp2_t '× fp2_t '× fp2_t) in
       '(eps_194 : (fp_t '× fp_t)) ←
        ( '(temp_165 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_167 : fp_t) ←
            (nat_mod_one ) ;;
          ret (prod_ce(temp_165, temp_167))) ;;
       '(t1_197 : (fp_t '× fp_t)) ←
        ( '(temp_171 : fp2_t) ←
            (fp2mul (n1_168) (m1_169)) ;;
          ret (temp_171)) ;;
       '(t2_187 : (fp_t '× fp_t)) ←
        ( '(temp_175 : fp2_t) ←
            (fp2mul (n2_172) (m2_173)) ;;
          ret (temp_175)) ;;
       '(t3_190 : (fp_t '× fp_t)) ←
        ( '(temp_179 : fp2_t) ←
            (fp2mul (n3_176) (m3_177)) ;;
          ret (temp_179)) ;;
       '(t4_186 : (fp_t '× fp_t)) ←
        ( '(temp_181 : fp2_t) ←
            (fp2add (n2_172) (n3_176)) ;;
           '(temp_183 : fp2_t) ←
            (fp2add (m2_173) (m3_177)) ;;
           '(temp_185 : fp2_t) ←
            (fp2mul (temp_181) (temp_183)) ;;
          ret (temp_185)) ;;
       '(t5_193 : (fp_t '× fp_t)) ←
        ( '(temp_189 : fp2_t) ←
            (fp2sub (t4_186) (t2_187)) ;;
           '(temp_192 : fp2_t) ←
            (fp2sub (temp_189) (t3_190)) ;;
          ret (temp_192)) ;;
       '(x_230 : (fp_t '× fp_t)) ←
        ( '(temp_196 : fp2_t) ←
            (fp2mul (t5_193) (eps_194)) ;;
           '(temp_199 : fp2_t) ←
            (fp2add (temp_196) (t1_197)) ;;
          ret (temp_199)) ;;
       '(t4_206 : (fp_t '× fp_t)) ←
        ( '(temp_201 : fp2_t) ←
            (fp2add (n1_168) (n2_172)) ;;
           '(temp_203 : fp2_t) ←
            (fp2add (m1_169) (m2_173)) ;;
           '(temp_205 : fp2_t) ←
            (fp2mul (temp_201) (temp_203)) ;;
          ret (temp_205)) ;;
       '(t5_211 : (fp_t '× fp_t)) ←
        ( '(temp_208 : fp2_t) ←
            (fp2sub (t4_206) (t1_197)) ;;
           '(temp_210 : fp2_t) ←
            (fp2sub (temp_208) (t2_187)) ;;
          ret (temp_210)) ;;
       '(y_231 : (fp_t '× fp_t)) ←
        ( '(temp_213 : fp2_t) ←
            (fp2mul (eps_194) (t3_190)) ;;
           '(temp_215 : fp2_t) ←
            (fp2add (t5_211) (temp_213)) ;;
          ret (temp_215)) ;;
       '(t4_222 : (fp_t '× fp_t)) ←
        ( '(temp_217 : fp2_t) ←
            (fp2add (n1_168) (n3_176)) ;;
           '(temp_219 : fp2_t) ←
            (fp2add (m1_169) (m3_177)) ;;
           '(temp_221 : fp2_t) ←
            (fp2mul (temp_217) (temp_219)) ;;
          ret (temp_221)) ;;
       '(t5_227 : (fp_t '× fp_t)) ←
        ( '(temp_224 : fp2_t) ←
            (fp2sub (t4_222) (t1_197)) ;;
           '(temp_226 : fp2_t) ←
            (fp2sub (temp_224) (t3_190)) ;;
          ret (temp_226)) ;;
       '(z_232 : (fp_t '× fp_t)) ←
        ( '(temp_229 : fp2_t) ←
            (fp2add (t5_227) (t2_187)) ;;
          ret (temp_229)) ;;
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× (fp_t '× fp_t))) (prod_ce(
          x_230,
          y_231,
          z_232
        )) } : code (fset.fset0) [interface
      #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
      #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp6mul : package _ _ _ :=
  (seq_link fp6mul link_rest(package_fp2add,package_fp2mul,package_fp2sub)).
Fail Next Obligation.


Notation "'fp6inv_inp'" := (
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp6inv_out'" := (
  fp6_t : choice_type) (in custom pack_type at level 2).
Definition FP6INV : nat :=
  (309).
Program Definition fp6inv
   : package (fset.fset0) [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
  #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ] [interface
  #val #[ FP6INV ] : fp6inv_inp → fp6inv_out ] :=
  ([package #def #[ FP6INV ] (temp_inp : fp6inv_inp) : fp6inv_out { 
    let '(n_238) := temp_inp : fp6_t in
    #import {sig #[ FP2ADD ] : fp2add_inp → fp2add_out } as fp2add ;;
    let fp2add := fun x_0 x_1 => fp2add (x_0,x_1) in
    #import {sig #[ FP2INV ] : fp2inv_inp → fp2inv_out } as fp2inv ;;
    let fp2inv := fun x_0 => fp2inv (x_0) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    #import {sig #[ FP2SUB ] : fp2sub_inp → fp2sub_out } as fp2sub ;;
    let fp2sub := fun x_0 x_1 => fp2sub (x_0,x_1) in
    ({ code  temp_308 ←
        (ret (n_238)) ;;
      let '(n1_243, n2_246, n3_249) :=
        (temp_308) : (fp2_t '× fp2_t '× fp2_t) in
       '(eps_259 : (fp_t '× fp_t)) ←
        ( '(temp_240 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_242 : fp_t) ←
            (nat_mod_one ) ;;
          ret (prod_ce(temp_240, temp_242))) ;;
       '(t1_258 : (fp_t '× fp_t)) ←
        ( '(temp_245 : fp2_t) ←
            (fp2mul (n1_243) (n1_243)) ;;
          ret (temp_245)) ;;
       '(t2_271 : (fp_t '× fp_t)) ←
        ( '(temp_248 : fp2_t) ←
            (fp2mul (n2_246) (n2_246)) ;;
          ret (temp_248)) ;;
       '(t3_265 : (fp_t '× fp_t)) ←
        ( '(temp_251 : fp2_t) ←
            (fp2mul (n3_249) (n3_249)) ;;
          ret (temp_251)) ;;
       '(t4_268 : (fp_t '× fp_t)) ←
        ( '(temp_253 : fp2_t) ←
            (fp2mul (n1_243) (n2_246)) ;;
          ret (temp_253)) ;;
       '(t5_272 : (fp_t '× fp_t)) ←
        ( '(temp_255 : fp2_t) ←
            (fp2mul (n1_243) (n3_249)) ;;
          ret (temp_255)) ;;
       '(t6_260 : (fp_t '× fp_t)) ←
        ( '(temp_257 : fp2_t) ←
            (fp2mul (n2_246) (n3_249)) ;;
          ret (temp_257)) ;;
       '(x0_275 : (fp_t '× fp_t)) ←
        ( '(temp_262 : fp2_t) ←
            (fp2mul (eps_259) (t6_260)) ;;
           '(temp_264 : fp2_t) ←
            (fp2sub (t1_258) (temp_262)) ;;
          ret (temp_264)) ;;
       '(y0_279 : (fp_t '× fp_t)) ←
        ( '(temp_267 : fp2_t) ←
            (fp2mul (eps_259) (t3_265)) ;;
           '(temp_270 : fp2_t) ←
            (fp2sub (temp_267) (t4_268)) ;;
          ret (temp_270)) ;;
       '(z0_287 : (fp_t '× fp_t)) ←
        ( '(temp_274 : fp2_t) ←
            (fp2sub (t2_271) (t5_272)) ;;
          ret (temp_274)) ;;
       '(t0_278 : (fp_t '× fp_t)) ←
        ( '(temp_277 : fp2_t) ←
            (fp2mul (n1_243) (x0_275)) ;;
          ret (temp_277)) ;;
       '(t0_286 : (fp_t '× fp_t)) ←
        ( '(temp_281 : fp2_t) ←
            (fp2mul (n3_249) (y0_279)) ;;
           '(temp_283 : fp2_t) ←
            (fp2mul (eps_259) (temp_281)) ;;
           '(temp_285 : fp2_t) ←
            (fp2add (t0_278) (temp_283)) ;;
          ret (temp_285)) ;;
       '(t0_294 : (fp_t '× fp_t)) ←
        ( '(temp_289 : fp2_t) ←
            (fp2mul (n2_246) (z0_287)) ;;
           '(temp_291 : fp2_t) ←
            (fp2mul (eps_259) (temp_289)) ;;
           '(temp_293 : fp2_t) ←
            (fp2add (t0_286) (temp_291)) ;;
          ret (temp_293)) ;;
       '(t0_297 : (fp_t '× fp_t)) ←
        ( '(temp_296 : fp2_t) ←
            (fp2inv (t0_294)) ;;
          ret (temp_296)) ;;
       '(x_304 : (fp_t '× fp_t)) ←
        ( '(temp_299 : fp2_t) ←
            (fp2mul (x0_275) (t0_297)) ;;
          ret (temp_299)) ;;
       '(y_305 : (fp_t '× fp_t)) ←
        ( '(temp_301 : fp2_t) ←
            (fp2mul (y0_279) (t0_297)) ;;
          ret (temp_301)) ;;
       '(z_306 : (fp_t '× fp_t)) ←
        ( '(temp_303 : fp2_t) ←
            (fp2mul (z0_287) (t0_297)) ;;
          ret (temp_303)) ;;
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× (fp_t '× fp_t))) (prod_ce(
          x_304,
          y_305,
          z_306
        )) } : code (fset.fset0) [interface
      #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
      #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
      #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp6inv : package _ _ _ :=
  (seq_link fp6inv link_rest(
      package_fp2add,package_fp2inv,package_fp2mul,package_fp2sub)).
Fail Next Obligation.


Notation "'fp12fromfp6_inp'" := (
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12fromfp6_out'" := (
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition FP12FROMFP6 : nat :=
  (313).
Program Definition fp12fromfp6
   : package (fset.fset0) [interface
  #val #[ FP6ZERO ] : fp6zero_inp → fp6zero_out ] [interface
  #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ] :=
  (
    [package #def #[ FP12FROMFP6 ] (temp_inp : fp12fromfp6_inp) : fp12fromfp6_out { 
    let '(n_310) := temp_inp : fp6_t in
    #import {sig #[ FP6ZERO ] : fp6zero_inp → fp6zero_out } as fp6zero ;;
    let fp6zero := fp6zero tt in
    ({ code  '(temp_312 : fp6_t) ←
        (fp6zero ) ;;
      @ret ((fp6_t '× fp6_t)) (prod_ce(n_310, temp_312)) } : code (
        fset.fset0) [interface #val #[ FP6ZERO ] : fp6zero_inp → fp6zero_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp12fromfp6 : package _ _ _ :=
  (seq_link fp12fromfp6 link_rest(package_fp6zero)).
Fail Next Obligation.


Notation "'fp12neg_inp'" := (
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12neg_out'" := (
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition FP12NEG : nat :=
  (327).
Program Definition fp12neg
   : package (fset.fset0) [interface
  #val #[ FP6SUB ] : fp6sub_inp → fp6sub_out ;
  #val #[ FP6ZERO ] : fp6zero_inp → fp6zero_out ] [interface
  #val #[ FP12NEG ] : fp12neg_inp → fp12neg_out ] :=
  ([package #def #[ FP12NEG ] (temp_inp : fp12neg_inp) : fp12neg_out { 
    let '(n_314) := temp_inp : fp12_t in
    #import {sig #[ FP6SUB ] : fp6sub_inp → fp6sub_out } as fp6sub ;;
    let fp6sub := fun x_0 x_1 => fp6sub (x_0,x_1) in
    #import {sig #[ FP6ZERO ] : fp6zero_inp → fp6zero_out } as fp6zero ;;
    let fp6zero := fp6zero tt in
    ({ code  temp_326 ←
        (ret (n_314)) ;;
      let '(n1_317, n2_322) :=
        (temp_326) : (fp6_t '× fp6_t) in
       '(temp_316 : fp6_t) ←
        (fp6zero ) ;;
       '(temp_319 : fp6_t) ←
        (fp6sub (temp_316) (n1_317)) ;;
       '(temp_321 : fp6_t) ←
        (fp6zero ) ;;
       '(temp_324 : fp6_t) ←
        (fp6sub (temp_321) (n2_322)) ;;
      @ret ((fp6_t '× fp6_t)) (prod_ce(temp_319, temp_324)) } : code (
        fset.fset0) [interface #val #[ FP6SUB ] : fp6sub_inp → fp6sub_out ;
      #val #[ FP6ZERO ] : fp6zero_inp → fp6zero_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp12neg : package _ _ _ :=
  (seq_link fp12neg link_rest(package_fp6sub,package_fp6zero)).
Fail Next Obligation.


Notation "'fp12add_inp'" := (
  fp12_t '× fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12add_out'" := (
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition FP12ADD : nat :=
  (342).
Program Definition fp12add
   : package (fset.fset0) [interface
  #val #[ FP6ADD ] : fp6add_inp → fp6add_out ] [interface
  #val #[ FP12ADD ] : fp12add_inp → fp12add_out ] :=
  ([package #def #[ FP12ADD ] (temp_inp : fp12add_inp) : fp12add_out { 
    let '(n_328 , m_329) := temp_inp : fp12_t '× fp12_t in
    #import {sig #[ FP6ADD ] : fp6add_inp → fp6add_out } as fp6add ;;
    let fp6add := fun x_0 x_1 => fp6add (x_0,x_1) in
    ({ code  temp_341 ←
        (ret (n_328)) ;;
      let '(n1_330, n2_334) :=
        (temp_341) : (fp6_t '× fp6_t) in
       temp_339 ←
        (ret (m_329)) ;;
      let '(m1_331, m2_335) :=
        (temp_339) : (fp6_t '× fp6_t) in
       '(temp_333 : fp6_t) ←
        (fp6add (n1_330) (m1_331)) ;;
       '(temp_337 : fp6_t) ←
        (fp6add (n2_334) (m2_335)) ;;
      @ret ((fp6_t '× fp6_t)) (prod_ce(temp_333, temp_337)) } : code (
        fset.fset0) [interface #val #[ FP6ADD ] : fp6add_inp → fp6add_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp12add : package _ _ _ :=
  (seq_link fp12add link_rest(package_fp6add)).
Fail Next Obligation.


Notation "'fp12sub_inp'" := (
  fp12_t '× fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12sub_out'" := (
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition FP12SUB : nat :=
  (349).
Program Definition fp12sub
   : package (fset.fset0) [interface
  #val #[ FP12ADD ] : fp12add_inp → fp12add_out ;
  #val #[ FP12NEG ] : fp12neg_inp → fp12neg_out ] [interface
  #val #[ FP12SUB ] : fp12sub_inp → fp12sub_out ] :=
  ([package #def #[ FP12SUB ] (temp_inp : fp12sub_inp) : fp12sub_out { 
    let '(n_343 , m_344) := temp_inp : fp12_t '× fp12_t in
    #import {sig #[ FP12ADD ] : fp12add_inp → fp12add_out } as fp12add ;;
    let fp12add := fun x_0 x_1 => fp12add (x_0,x_1) in
    #import {sig #[ FP12NEG ] : fp12neg_inp → fp12neg_out } as fp12neg ;;
    let fp12neg := fun x_0 => fp12neg (x_0) in
    ({ code  '(temp_346 : fp12_t) ←
        (fp12neg (m_344)) ;;
       '(temp_348 : fp12_t) ←
        (fp12add (n_343) (temp_346)) ;;
      @ret (fp12_t) (temp_348) } : code (fset.fset0) [interface
      #val #[ FP12ADD ] : fp12add_inp → fp12add_out ;
      #val #[ FP12NEG ] : fp12neg_inp → fp12neg_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp12sub : package _ _ _ :=
  (seq_link fp12sub link_rest(package_fp12add,package_fp12neg)).
Fail Next Obligation.


Notation "'fp12mul_inp'" := (
  fp12_t '× fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12mul_out'" := (
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition FP12MUL : nat :=
  (392).
Program Definition fp12mul
   : package (fset.fset0) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
  #val #[ FP6ADD ] : fp6add_inp → fp6add_out ;
  #val #[ FP6MUL ] : fp6mul_inp → fp6mul_out ;
  #val #[ FP6SUB ] : fp6sub_inp → fp6sub_out ] [interface
  #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ] :=
  ([package #def #[ FP12MUL ] (temp_inp : fp12mul_inp) : fp12mul_out { 
    let '(n_350 , m_351) := temp_inp : fp12_t '× fp12_t in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP2ZERO ] : fp2zero_inp → fp2zero_out } as fp2zero ;;
    let fp2zero := fp2zero tt in
    #import {sig #[ FP6ADD ] : fp6add_inp → fp6add_out } as fp6add ;;
    let fp6add := fun x_0 x_1 => fp6add (x_0,x_1) in
    #import {sig #[ FP6MUL ] : fp6mul_inp → fp6mul_out } as fp6mul ;;
    let fp6mul := fun x_0 x_1 => fp6mul (x_0,x_1) in
    #import {sig #[ FP6SUB ] : fp6sub_inp → fp6sub_out } as fp6sub ;;
    let fp6sub := fun x_0 x_1 => fp6sub (x_0,x_1) in
    ({ code  temp_391 ←
        (ret (n_350)) ;;
      let '(n1_360, n2_364) :=
        (temp_391) : (fp6_t '× fp6_t) in
       temp_389 ←
        (ret (m_351)) ;;
      let '(m1_361, m2_365) :=
        (temp_389) : (fp6_t '× fp6_t) in
       '(gamma_370 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_353 : fp2_t) ←
            (fp2zero ) ;;
           '(temp_355 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_357 : fp2_t) ←
            (fp2fromfp (temp_355)) ;;
           '(temp_359 : fp2_t) ←
            (fp2zero ) ;;
          ret (prod_ce(temp_353, temp_357, temp_359))) ;;
       '(t1_368 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_363 : fp6_t) ←
            (fp6mul (n1_360) (m1_361)) ;;
          ret (temp_363)) ;;
       '(t2_369 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_367 : fp6_t) ←
            (fp6mul (n2_364) (m2_365)) ;;
          ret (temp_367)) ;;
       '(x_386 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_372 : fp6_t) ←
            (fp6mul (t2_369) (gamma_370)) ;;
           '(temp_374 : fp6_t) ←
            (fp6add (t1_368) (temp_372)) ;;
          ret (temp_374)) ;;
       '(y_381 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_376 : fp6_t) ←
            (fp6add (n1_360) (n2_364)) ;;
           '(temp_378 : fp6_t) ←
            (fp6add (m1_361) (m2_365)) ;;
           '(temp_380 : fp6_t) ←
            (fp6mul (temp_376) (temp_378)) ;;
          ret (temp_380)) ;;
       '(y_387 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_383 : fp6_t) ←
            (fp6sub (y_381) (t1_368)) ;;
           '(temp_385 : fp6_t) ←
            (fp6sub (temp_383) (t2_369)) ;;
          ret (temp_385)) ;;
      @ret (((fp2_t '× fp2_t '× fp2_t) '× (fp2_t '× fp2_t '× fp2_t))) (
        prod_ce(x_386, y_387)) } : code (fset.fset0) [interface
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
      #val #[ FP6ADD ] : fp6add_inp → fp6add_out ;
      #val #[ FP6MUL ] : fp6mul_inp → fp6mul_out ;
      #val #[ FP6SUB ] : fp6sub_inp → fp6sub_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp12mul : package _ _ _ :=
  (seq_link fp12mul link_rest(
      package_fp2fromfp,package_fp2zero,package_fp6add,package_fp6mul,package_fp6sub)).
Fail Next Obligation.


Notation "'fp12inv_inp'" := (
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12inv_out'" := (
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition FP12INV : nat :=
  (429).
Program Definition fp12inv
   : package (fset.fset0) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
  #val #[ FP6INV ] : fp6inv_inp → fp6inv_out ;
  #val #[ FP6MUL ] : fp6mul_inp → fp6mul_out ;
  #val #[ FP6NEG ] : fp6neg_inp → fp6neg_out ;
  #val #[ FP6SUB ] : fp6sub_inp → fp6sub_out ] [interface
  #val #[ FP12INV ] : fp12inv_inp → fp12inv_out ] :=
  ([package #def #[ FP12INV ] (temp_inp : fp12inv_inp) : fp12inv_out { 
    let '(n_393) := temp_inp : fp12_t in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP2ZERO ] : fp2zero_inp → fp2zero_out } as fp2zero ;;
    let fp2zero := fp2zero tt in
    #import {sig #[ FP6INV ] : fp6inv_inp → fp6inv_out } as fp6inv ;;
    let fp6inv := fun x_0 => fp6inv (x_0) in
    #import {sig #[ FP6MUL ] : fp6mul_inp → fp6mul_out } as fp6mul ;;
    let fp6mul := fun x_0 x_1 => fp6mul (x_0,x_1) in
    #import {sig #[ FP6NEG ] : fp6neg_inp → fp6neg_out } as fp6neg ;;
    let fp6neg := fun x_0 => fp6neg (x_0) in
    #import {sig #[ FP6SUB ] : fp6sub_inp → fp6sub_out } as fp6sub ;;
    let fp6sub := fun x_0 x_1 => fp6sub (x_0,x_1) in
    ({ code  temp_428 ←
        (ret (n_393)) ;;
      let '(n1_402, n2_405) :=
        (temp_428) : (fp6_t '× fp6_t) in
       '(gamma_409 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_395 : fp2_t) ←
            (fp2zero ) ;;
           '(temp_397 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_399 : fp2_t) ←
            (fp2fromfp (temp_397)) ;;
           '(temp_401 : fp2_t) ←
            (fp2zero ) ;;
          ret (prod_ce(temp_395, temp_399, temp_401))) ;;
       '(t1_408 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_404 : fp6_t) ←
            (fp6mul (n1_402) (n1_402)) ;;
          ret (temp_404)) ;;
       '(t2_410 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_407 : fp6_t) ←
            (fp6mul (n2_405) (n2_405)) ;;
          ret (temp_407)) ;;
       '(t1_415 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_412 : fp6_t) ←
            (fp6mul (gamma_409) (t2_410)) ;;
           '(temp_414 : fp6_t) ←
            (fp6sub (t1_408) (temp_412)) ;;
          ret (temp_414)) ;;
       '(t2_418 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_417 : fp6_t) ←
            (fp6inv (t1_415)) ;;
          ret (temp_417)) ;;
       '(x_425 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_420 : fp6_t) ←
            (fp6mul (n1_402) (t2_418)) ;;
          ret (temp_420)) ;;
       '(y_426 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_422 : fp6_t) ←
            (fp6mul (n2_405) (t2_418)) ;;
           '(temp_424 : fp6_t) ←
            (fp6neg (temp_422)) ;;
          ret (temp_424)) ;;
      @ret (((fp2_t '× fp2_t '× fp2_t) '× (fp2_t '× fp2_t '× fp2_t))) (
        prod_ce(x_425, y_426)) } : code (fset.fset0) [interface
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
      #val #[ FP6INV ] : fp6inv_inp → fp6inv_out ;
      #val #[ FP6MUL ] : fp6mul_inp → fp6mul_out ;
      #val #[ FP6NEG ] : fp6neg_inp → fp6neg_out ;
      #val #[ FP6SUB ] : fp6sub_inp → fp6sub_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp12inv : package _ _ _ :=
  (seq_link fp12inv link_rest(
      package_fp2fromfp,package_fp2zero,package_fp6inv,package_fp6mul,package_fp6neg,package_fp6sub)).
Fail Next Obligation.

Definition c_438_loc : ChoiceEqualityLocation :=
  (((fp6_t '× fp6_t) ; 450%nat)).
Notation "'fp12exp_inp'" := (
  fp12_t '× scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12exp_out'" := (
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition FP12EXP : nat :=
  (451).
Program Definition fp12exp
   : package (CEfset ([c_438_loc])) [interface
  #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
  #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ] [interface
  #val #[ FP12EXP ] : fp12exp_inp → fp12exp_out ] :=
  ([package #def #[ FP12EXP ] (temp_inp : fp12exp_inp) : fp12exp_out { 
    let '(n_447 , k_441) := temp_inp : fp12_t '× scalar_t in
    #import {sig #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out } as fp12fromfp6 ;;
    let fp12fromfp6 := fun x_0 => fp12fromfp6 (x_0) in
    #import {sig #[ FP12MUL ] : fp12mul_inp → fp12mul_out } as fp12mul ;;
    let fp12mul := fun x_0 x_1 => fp12mul (x_0,x_1) in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out } as fp6fromfp2 ;;
    let fp6fromfp2 := fun x_0 => fp6fromfp2 (x_0) in
    ({ code  '(c_438 : (fp6_t '× fp6_t)) ←
          ( '(temp_431 : fp_t) ←
              (nat_mod_one ) ;;
             '(temp_433 : fp2_t) ←
              (fp2fromfp (temp_431)) ;;
             '(temp_435 : fp6_t) ←
              (fp6fromfp2 (temp_433)) ;;
             '(temp_437 : fp12_t) ←
              (fp12fromfp6 (temp_435)) ;;
            ret (temp_437)) ;;
        #put c_438_loc := c_438 ;;
       '(c_438 : ((fp6_t '× fp6_t))) ←
        (foldi' (usize 0) (usize 256) c_438 (L2 := CEfset ([c_438_loc])) (
              I2 := [interface
              #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
              #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
              #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
              #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_442 c_438 =>
            ({ code  '(c_438 : (fp6_t '× fp6_t)) ←
                  (( '(temp_440 : fp12_t) ←
                        (fp12mul (c_438) (c_438)) ;;
                      ret (temp_440))) ;;
                #put c_438_loc := c_438 ;;
              
               '(temp_444 : uint_size) ←
                ((usize 255) .- (i_442)) ;;
               temp_446 ←
                (nat_mod_bit (k_441) (temp_444)) ;;
               '(c_438 : ((fp6_t '× fp6_t))) ←
                (if temp_446:bool_ChoiceEquality
                  then (({ code  '(c_438 : (fp6_t '× fp6_t)) ←
                          (( '(temp_449 : fp12_t) ←
                                (fp12mul (c_438) (n_447)) ;;
                              ret (temp_449))) ;;
                        #put c_438_loc := c_438 ;;
                      
                      @ret (((fp6_t '× fp6_t))) (c_438) } : code (CEfset (
                          [c_438_loc])) [interface
                      #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ] _))
                  else @ret (((fp6_t '× fp6_t))) (c_438)) ;;
              
              @ret (((fp6_t '× fp6_t))) (c_438) } : code (CEfset (
                  [c_438_loc])) [interface
              #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ] _))) ;;
      
      @ret ((fp6_t '× fp6_t)) (c_438) } : code (CEfset (
          [c_438_loc])) [interface
      #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
      #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp12exp : package _ _ _ :=
  (seq_link fp12exp link_rest(
      package_fp12fromfp6,package_fp12mul,package_fp2fromfp,package_fp6fromfp2)).
Fail Next Obligation.


Notation "'fp12conjugate_inp'" := (
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12conjugate_out'" := (
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition FP12CONJUGATE : nat :=
  (459).
Program Definition fp12conjugate
   : package (fset.fset0) [interface
  #val #[ FP6NEG ] : fp6neg_inp → fp6neg_out ] [interface
  #val #[ FP12CONJUGATE ] : fp12conjugate_inp → fp12conjugate_out ] :=
  (
    [package #def #[ FP12CONJUGATE ] (temp_inp : fp12conjugate_inp) : fp12conjugate_out { 
    let '(n_452) := temp_inp : fp12_t in
    #import {sig #[ FP6NEG ] : fp6neg_inp → fp6neg_out } as fp6neg ;;
    let fp6neg := fun x_0 => fp6neg (x_0) in
    ({ code  temp_458 ←
        (ret (n_452)) ;;
      let '(n1_453, n2_454) :=
        (temp_458) : (fp6_t '× fp6_t) in
       '(temp_456 : fp6_t) ←
        (fp6neg (n2_454)) ;;
      @ret (((fp2_t '× fp2_t '× fp2_t) '× fp6_t)) (prod_ce(n1_453, temp_456
        )) } : code (fset.fset0) [interface
      #val #[ FP6NEG ] : fp6neg_inp → fp6neg_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp12conjugate : package _ _ _ :=
  (seq_link fp12conjugate link_rest(package_fp6neg)).
Fail Next Obligation.


Notation "'fp12zero_inp'" := (
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'fp12zero_out'" := (
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition FP12ZERO : nat :=
  (464).
Program Definition fp12zero
   : package (fset.fset0) [interface
  #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
  #val #[ FP6ZERO ] : fp6zero_inp → fp6zero_out ] [interface
  #val #[ FP12ZERO ] : fp12zero_inp → fp12zero_out ] :=
  ([package #def #[ FP12ZERO ] (temp_inp : fp12zero_inp) : fp12zero_out { 
    #import {sig #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out } as fp12fromfp6 ;;
    let fp12fromfp6 := fun x_0 => fp12fromfp6 (x_0) in
    #import {sig #[ FP6ZERO ] : fp6zero_inp → fp6zero_out } as fp6zero ;;
    let fp6zero := fp6zero tt in
    ({ code  '(temp_461 : fp6_t) ←
        (fp6zero ) ;;
       '(temp_463 : fp12_t) ←
        (fp12fromfp6 (temp_461)) ;;
      @ret (fp12_t) (temp_463) } : code (fset.fset0) [interface
      #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
      #val #[ FP6ZERO ] : fp6zero_inp → fp6zero_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_fp12zero : package _ _ _ :=
  (seq_link fp12zero link_rest(package_fp12fromfp6,package_fp6zero)).
Fail Next Obligation.


Notation "'g1add_a_inp'" := (
  g1_t '× g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1add_a_out'" := (
  g1_t : choice_type) (in custom pack_type at level 2).
Definition G1ADD_A : nat :=
  (500).
Program Definition g1add_a
   : package (fset.fset0) [interface  ] [interface
  #val #[ G1ADD_A ] : g1add_a_inp → g1add_a_out ] :=
  ([package #def #[ G1ADD_A ] (temp_inp : g1add_a_inp) : g1add_a_out { 
    let '(p_465 , q_466) := temp_inp : g1_t '× g1_t in
    ({ code  temp_499 ←
        (ret (p_465)) ;;
      let '(x1_468, y1_472, _) :=
        (temp_499) : (fp_t '× fp_t '× bool_ChoiceEquality) in
       temp_497 ←
        (ret (q_466)) ;;
      let '(x2_467, y2_471, _) :=
        (temp_497) : (fp_t '× fp_t '× bool_ChoiceEquality) in
       '(x_diff_476 : fp_t) ←
        ( '(temp_470 : fp_t) ←
            ((x2_467) -% (x1_468)) ;;
          ret (temp_470)) ;;
       '(y_diff_475 : fp_t) ←
        ( '(temp_474 : fp_t) ←
            ((y2_471) -% (y1_472)) ;;
          ret (temp_474)) ;;
       '(xovery_481 : fp_t) ←
        ( temp_478 ←
            (nat_mod_inv (x_diff_476)) ;;
           '(temp_480 : fp_t) ←
            ((y_diff_475) *% (temp_478)) ;;
          ret (temp_480)) ;;
       '(x3_488 : fp_t) ←
        ( temp_483 ←
            (nat_mod_exp (xovery_481) (@repr U32 2)) ;;
           '(temp_485 : fp_t) ←
            ((temp_483) -% (x1_468)) ;;
           '(temp_487 : fp_t) ←
            ((temp_485) -% (x2_467)) ;;
          ret (temp_487)) ;;
       '(y3_495 : fp_t) ←
        ( '(temp_490 : fp_t) ←
            ((x1_468) -% (x3_488)) ;;
           '(temp_492 : fp_t) ←
            ((xovery_481) *% (temp_490)) ;;
           '(temp_494 : fp_t) ←
            ((temp_492) -% (y1_472)) ;;
          ret (temp_494)) ;;
      @ret ((fp_t '× fp_t '× bool_ChoiceEquality)) (prod_ce(
          x3_488,
          y3_495,
          (false : bool_ChoiceEquality)
        )) } : code (fset.fset0) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_g1add_a : package _ _ _ :=
  (g1add_a).
Fail Next Obligation.


Notation "'g1double_a_inp'" := (
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1double_a_out'" := (
  g1_t : choice_type) (in custom pack_type at level 2).
Definition G1DOUBLE_A : nat :=
  (538).
Program Definition g1double_a
   : package (fset.fset0) [interface  ] [interface
  #val #[ G1DOUBLE_A ] : g1double_a_inp → g1double_a_out ] :=
  ([package #def #[ G1DOUBLE_A ] (temp_inp : g1double_a_inp) : g1double_a_out { 
    let '(p_501) := temp_inp : g1_t in
    ({ code  temp_537 ←
        (ret (p_501)) ;;
      let '(x1_502, y1_512, _) :=
        (temp_537) : (fp_t '× fp_t '× bool_ChoiceEquality) in
       '(x12_507 : fp_t) ←
        ( temp_504 ←
            (nat_mod_exp (x1_502) (@repr U32 2)) ;;
          ret (temp_504)) ;;
       '(xovery_519 : fp_t) ←
        ( '(temp_506 : fp_t) ←
            (nat_mod_from_literal (
                0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
                @repr U128 3)) ;;
           '(temp_509 : fp_t) ←
            ((temp_506) *% (x12_507)) ;;
           '(temp_511 : fp_t) ←
            (nat_mod_two ) ;;
           '(temp_514 : fp_t) ←
            ((temp_511) *% (y1_512)) ;;
           temp_516 ←
            (nat_mod_inv (temp_514)) ;;
           '(temp_518 : fp_t) ←
            ((temp_509) *% (temp_516)) ;;
          ret (temp_518)) ;;
       '(x3_528 : fp_t) ←
        ( temp_521 ←
            (nat_mod_exp (xovery_519) (@repr U32 2)) ;;
           '(temp_523 : fp_t) ←
            (nat_mod_two ) ;;
           '(temp_525 : fp_t) ←
            ((temp_523) *% (x1_502)) ;;
           '(temp_527 : fp_t) ←
            ((temp_521) -% (temp_525)) ;;
          ret (temp_527)) ;;
       '(y3_535 : fp_t) ←
        ( '(temp_530 : fp_t) ←
            ((x1_502) -% (x3_528)) ;;
           '(temp_532 : fp_t) ←
            ((xovery_519) *% (temp_530)) ;;
           '(temp_534 : fp_t) ←
            ((temp_532) -% (y1_512)) ;;
          ret (temp_534)) ;;
      @ret ((fp_t '× fp_t '× bool_ChoiceEquality)) (prod_ce(
          x3_528,
          y3_535,
          (false : bool_ChoiceEquality)
        )) } : code (fset.fset0) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_g1double_a : package _ _ _ :=
  (g1double_a).
Fail Next Obligation.


Notation "'g1double_inp'" := (
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1double_out'" := (
  g1_t : choice_type) (in custom pack_type at level 2).
Definition G1DOUBLE : nat :=
  (557).
Program Definition g1double
   : package (fset.fset0) [interface
  #val #[ G1DOUBLE_A ] : g1double_a_inp → g1double_a_out ] [interface
  #val #[ G1DOUBLE ] : g1double_inp → g1double_out ] :=
  ([package #def #[ G1DOUBLE ] (temp_inp : g1double_inp) : g1double_out { 
    let '(p_539) := temp_inp : g1_t in
    #import {sig #[ G1DOUBLE_A ] : g1double_a_inp → g1double_a_out } as g1double_a ;;
    let g1double_a := fun x_0 => g1double_a (x_0) in
    ({ code  temp_555 ←
        (ret (p_539)) ;;
      let '(x1_556, y1_540, inf1_545) :=
        (temp_555) : (fp_t '× fp_t '× bool_ChoiceEquality) in
       '(temp_542 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_544 : bool_ChoiceEquality) ←
        ((y1_540) !=.? (temp_542)) ;;
       '(temp_547 : bool_ChoiceEquality) ←
        ((temp_544) && (negb (inf1_545))) ;;
       '(temp_549 : g1_t) ←
        (g1double_a (p_539)) ;;
       '(temp_551 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_553 : fp_t) ←
        (nat_mod_zero ) ;;
      @ret (g1_t) ((if (temp_547):bool_ChoiceEquality then (temp_549) else (
            prod_ce(temp_551, temp_553, (true : bool_ChoiceEquality)
            )))) } : code (fset.fset0) [interface
      #val #[ G1DOUBLE_A ] : g1double_a_inp → g1double_a_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_g1double : package _ _ _ :=
  (seq_link g1double link_rest(package_g1double_a)).
Fail Next Obligation.


Notation "'g1add_inp'" := (
  g1_t '× g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1add_out'" := (g1_t : choice_type) (in custom pack_type at level 2).
Definition G1ADD : nat :=
  (590).
Program Definition g1add
   : package (fset.fset0) [interface
  #val #[ G1ADD_A ] : g1add_a_inp → g1add_a_out ;
  #val #[ G1DOUBLE ] : g1double_inp → g1double_out ] [interface
  #val #[ G1ADD ] : g1add_inp → g1add_out ] :=
  ([package #def #[ G1ADD ] (temp_inp : g1add_inp) : g1add_out { 
    let '(p_558 , q_559) := temp_inp : g1_t '× g1_t in
    #import {sig #[ G1ADD_A ] : g1add_a_inp → g1add_a_out } as g1add_a ;;
    let g1add_a := fun x_0 x_1 => g1add_a (x_0,x_1) in
    #import {sig #[ G1DOUBLE ] : g1double_inp → g1double_out } as g1double ;;
    let g1double := fun x_0 => g1double (x_0) in
    ({ code  temp_589 ←
        (ret (p_558)) ;;
      let '(x1_566, y1_570, inf1_560) :=
        (temp_589) : (fp_t '× fp_t '× bool_ChoiceEquality) in
       temp_587 ←
        (ret (q_559)) ;;
      let '(x2_567, y2_573, inf2_561) :=
        (temp_587) : (fp_t '× fp_t '× bool_ChoiceEquality) in
       '(temp_563 : bool_ChoiceEquality) ←
        ((p_558) =.? (q_559)) ;;
       '(temp_565 : g1_t) ←
        (g1double (p_558)) ;;
       '(temp_569 : bool_ChoiceEquality) ←
        ((x1_566) =.? (x2_567)) ;;
       '(temp_572 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_575 : fp_t) ←
        ((temp_572) -% (y2_573)) ;;
       '(temp_577 : bool_ChoiceEquality) ←
        ((y1_570) =.? (temp_575)) ;;
       '(temp_579 : bool_ChoiceEquality) ←
        ((temp_569) && (temp_577)) ;;
       '(temp_581 : g1_t) ←
        (g1add_a (p_558) (q_559)) ;;
       '(temp_583 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_585 : fp_t) ←
        (nat_mod_zero ) ;;
      @ret (g1_t) ((if (inf1_560):bool_ChoiceEquality then (q_559) else ((if (
                inf2_561):bool_ChoiceEquality then (p_558) else ((if (
                    temp_563):bool_ChoiceEquality then (temp_565) else ((if (
                        negb (temp_579)):bool_ChoiceEquality then (
                        temp_581) else (prod_ce(
                          temp_583,
                          temp_585,
                          (true : bool_ChoiceEquality)
                        )))))))))) } : code (fset.fset0) [interface
      #val #[ G1ADD_A ] : g1add_a_inp → g1add_a_out ;
      #val #[ G1DOUBLE ] : g1double_inp → g1double_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_g1add : package _ _ _ :=
  (seq_link g1add link_rest(package_g1add_a,package_g1double)).
Fail Next Obligation.

Definition t_595_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t '× bool_ChoiceEquality) ; 607%nat)).
Notation "'g1mul_inp'" := (
  scalar_t '× g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1mul_out'" := (g1_t : choice_type) (in custom pack_type at level 2).
Definition G1MUL : nat :=
  (608).
Program Definition g1mul
   : package (CEfset ([t_595_loc])) [interface
  #val #[ G1ADD ] : g1add_inp → g1add_out ;
  #val #[ G1DOUBLE ] : g1double_inp → g1double_out ] [interface
  #val #[ G1MUL ] : g1mul_inp → g1mul_out ] :=
  ([package #def #[ G1MUL ] (temp_inp : g1mul_inp) : g1mul_out { 
    let '(m_598 , p_604) := temp_inp : scalar_t '× g1_t in
    #import {sig #[ G1ADD ] : g1add_inp → g1add_out } as g1add ;;
    let g1add := fun x_0 x_1 => g1add (x_0,x_1) in
    #import {sig #[ G1DOUBLE ] : g1double_inp → g1double_out } as g1double ;;
    let g1double := fun x_0 => g1double (x_0) in
    ({ code  '(t_595 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
          ( '(temp_592 : fp_t) ←
              (nat_mod_zero ) ;;
             '(temp_594 : fp_t) ←
              (nat_mod_zero ) ;;
            ret (prod_ce(temp_592, temp_594, (true : bool_ChoiceEquality)))) ;;
        #put t_595_loc := t_595 ;;
       '(t_595 : ((fp_t '× fp_t '× bool_ChoiceEquality))) ←
        (foldi' (usize 0) (usize 256) t_595 (L2 := CEfset ([t_595_loc])) (
              I2 := [interface #val #[ G1ADD ] : g1add_inp → g1add_out ;
              #val #[ G1DOUBLE ] : g1double_inp → g1double_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_599 t_595 =>
            ({ code  '(t_595 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
                  (( '(temp_597 : g1_t) ←
                        (g1double (t_595)) ;;
                      ret (temp_597))) ;;
                #put t_595_loc := t_595 ;;
              
               '(temp_601 : uint_size) ←
                ((usize 255) .- (i_599)) ;;
               temp_603 ←
                (nat_mod_bit (m_598) (temp_601)) ;;
               '(t_595 : ((fp_t '× fp_t '× bool_ChoiceEquality))) ←
                (if temp_603:bool_ChoiceEquality
                  then (({ code  '(t_595 : (
                              fp_t '×
                              fp_t '×
                              bool_ChoiceEquality
                            )) ←
                          (( '(temp_606 : g1_t) ←
                                (g1add (t_595) (p_604)) ;;
                              ret (temp_606))) ;;
                        #put t_595_loc := t_595 ;;
                      
                      @ret (((fp_t '× fp_t '× bool_ChoiceEquality))) (
                        t_595) } : code (CEfset ([t_595_loc])) [interface
                      #val #[ G1ADD ] : g1add_inp → g1add_out ] _))
                  else @ret (((fp_t '× fp_t '× bool_ChoiceEquality))) (
                    t_595)) ;;
              
              @ret (((fp_t '× fp_t '× bool_ChoiceEquality))) (
                t_595) } : code (CEfset ([t_595_loc])) [interface
              #val #[ G1ADD ] : g1add_inp → g1add_out ;
              #val #[ G1DOUBLE ] : g1double_inp → g1double_out ] _))) ;;
      
      @ret ((fp_t '× fp_t '× bool_ChoiceEquality)) (t_595) } : code (CEfset (
          [t_595_loc])) [interface #val #[ G1ADD ] : g1add_inp → g1add_out ;
      #val #[ G1DOUBLE ] : g1double_inp → g1double_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_g1mul : package _ _ _ :=
  (seq_link g1mul link_rest(package_g1add,package_g1double)).
Fail Next Obligation.


Notation "'g1neg_inp'" := (g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1neg_out'" := (g1_t : choice_type) (in custom pack_type at level 2).
Definition G1NEG : nat :=
  (619).
Program Definition g1neg
   : package (fset.fset0) [interface  ] [interface
  #val #[ G1NEG ] : g1neg_inp → g1neg_out ] :=
  ([package #def #[ G1NEG ] (temp_inp : g1neg_inp) : g1neg_out { 
    let '(p_609) := temp_inp : g1_t in
    ({ code  temp_618 ←
        (ret (p_609)) ;;
      let '(x_610, y_613, inf_616) :=
        (temp_618) : (fp_t '× fp_t '× bool_ChoiceEquality) in
       '(temp_612 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_615 : fp_t) ←
        ((temp_612) -% (y_613)) ;;
      @ret ((fp_t '× fp_t '× bool_ChoiceEquality)) (prod_ce(
          x_610,
          temp_615,
          inf_616
        )) } : code (fset.fset0) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_g1neg : package _ _ _ :=
  (g1neg).
Fail Next Obligation.


Notation "'g2add_a_inp'" := (
  g2_t '× g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2add_a_out'" := (
  g2_t : choice_type) (in custom pack_type at level 2).
Definition G2ADD_A : nat :=
  (659).
Program Definition g2add_a
   : package (fset.fset0) [interface
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
  #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ] [interface
  #val #[ G2ADD_A ] : g2add_a_inp → g2add_a_out ] :=
  ([package #def #[ G2ADD_A ] (temp_inp : g2add_a_inp) : g2add_a_out { 
    let '(p_620 , q_621) := temp_inp : g2_t '× g2_t in
    #import {sig #[ FP2INV ] : fp2inv_inp → fp2inv_out } as fp2inv ;;
    let fp2inv := fun x_0 => fp2inv (x_0) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    #import {sig #[ FP2SUB ] : fp2sub_inp → fp2sub_out } as fp2sub ;;
    let fp2sub := fun x_0 x_1 => fp2sub (x_0,x_1) in
    ({ code  temp_658 ←
        (ret (p_620)) ;;
      let '(x1_623, y1_627, _) :=
        (temp_658) : (fp2_t '× fp2_t '× bool_ChoiceEquality) in
       temp_656 ←
        (ret (q_621)) ;;
      let '(x2_622, y2_626, _) :=
        (temp_656) : (fp2_t '× fp2_t '× bool_ChoiceEquality) in
       '(x_diff_631 : (fp_t '× fp_t)) ←
        ( '(temp_625 : fp2_t) ←
            (fp2sub (x2_622) (x1_623)) ;;
          ret (temp_625)) ;;
       '(y_diff_630 : (fp_t '× fp_t)) ←
        ( '(temp_629 : fp2_t) ←
            (fp2sub (y2_626) (y1_627)) ;;
          ret (temp_629)) ;;
       '(xovery_636 : (fp_t '× fp_t)) ←
        ( '(temp_633 : fp2_t) ←
            (fp2inv (x_diff_631)) ;;
           '(temp_635 : fp2_t) ←
            (fp2mul (y_diff_630) (temp_633)) ;;
          ret (temp_635)) ;;
       '(t1_639 : (fp_t '× fp_t)) ←
        ( '(temp_638 : fp2_t) ←
            (fp2mul (xovery_636) (xovery_636)) ;;
          ret (temp_638)) ;;
       '(t2_642 : (fp_t '× fp_t)) ←
        ( '(temp_641 : fp2_t) ←
            (fp2sub (t1_639) (x1_623)) ;;
          ret (temp_641)) ;;
       '(x3_645 : (fp_t '× fp_t)) ←
        ( '(temp_644 : fp2_t) ←
            (fp2sub (t2_642) (x2_622)) ;;
          ret (temp_644)) ;;
       '(t1_648 : (fp_t '× fp_t)) ←
        ( '(temp_647 : fp2_t) ←
            (fp2sub (x1_623) (x3_645)) ;;
          ret (temp_647)) ;;
       '(t2_651 : (fp_t '× fp_t)) ←
        ( '(temp_650 : fp2_t) ←
            (fp2mul (xovery_636) (t1_648)) ;;
          ret (temp_650)) ;;
       '(y3_654 : (fp_t '× fp_t)) ←
        ( '(temp_653 : fp2_t) ←
            (fp2sub (t2_651) (y1_627)) ;;
          ret (temp_653)) ;;
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality)) (
        prod_ce(x3_645, y3_654, (false : bool_ChoiceEquality))) } : code (
        fset.fset0) [interface #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
      #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_g2add_a : package _ _ _ :=
  (seq_link g2add_a link_rest(package_fp2inv,package_fp2mul,package_fp2sub)).
Fail Next Obligation.


Notation "'g2double_a_inp'" := (
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2double_a_out'" := (
  g2_t : choice_type) (in custom pack_type at level 2).
Definition G2DOUBLE_A : nat :=
  (709).
Program Definition g2double_a
   : package (fset.fset0) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
  #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ] [interface
  #val #[ G2DOUBLE_A ] : g2double_a_inp → g2double_a_out ] :=
  ([package #def #[ G2DOUBLE_A ] (temp_inp : g2double_a_inp) : g2double_a_out { 
    let '(p_660) := temp_inp : g2_t in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP2INV ] : fp2inv_inp → fp2inv_out } as fp2inv ;;
    let fp2inv := fun x_0 => fp2inv (x_0) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    #import {sig #[ FP2SUB ] : fp2sub_inp → fp2sub_out } as fp2sub ;;
    let fp2sub := fun x_0 x_1 => fp2sub (x_0,x_1) in
    ({ code  temp_708 ←
        (ret (p_660)) ;;
      let '(x1_661, y1_675, _) :=
        (temp_708) : (fp2_t '× fp2_t '× bool_ChoiceEquality) in
       '(x12_668 : (fp_t '× fp_t)) ←
        ( '(temp_663 : fp2_t) ←
            (fp2mul (x1_661) (x1_661)) ;;
          ret (temp_663)) ;;
       '(t1_680 : (fp_t '× fp_t)) ←
        ( '(temp_665 : fp_t) ←
            (nat_mod_from_literal (
                0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
                @repr U128 3)) ;;
           '(temp_667 : fp2_t) ←
            (fp2fromfp (temp_665)) ;;
           '(temp_670 : fp2_t) ←
            (fp2mul (temp_667) (x12_668)) ;;
          ret (temp_670)) ;;
       '(t2_681 : (fp_t '× fp_t)) ←
        ( '(temp_672 : fp_t) ←
            (nat_mod_two ) ;;
           '(temp_674 : fp2_t) ←
            (fp2fromfp (temp_672)) ;;
           '(temp_677 : fp2_t) ←
            (fp2mul (temp_674) (y1_675)) ;;
           '(temp_679 : fp2_t) ←
            (fp2inv (temp_677)) ;;
          ret (temp_679)) ;;
       '(xovery_684 : (fp_t '× fp_t)) ←
        ( '(temp_683 : fp2_t) ←
            (fp2mul (t1_680) (t2_681)) ;;
          ret (temp_683)) ;;
       '(t1_693 : (fp_t '× fp_t)) ←
        ( '(temp_686 : fp2_t) ←
            (fp2mul (xovery_684) (xovery_684)) ;;
          ret (temp_686)) ;;
       '(t2_694 : (fp_t '× fp_t)) ←
        ( '(temp_688 : fp_t) ←
            (nat_mod_two ) ;;
           '(temp_690 : fp2_t) ←
            (fp2fromfp (temp_688)) ;;
           '(temp_692 : fp2_t) ←
            (fp2mul (temp_690) (x1_661)) ;;
          ret (temp_692)) ;;
       '(x3_697 : (fp_t '× fp_t)) ←
        ( '(temp_696 : fp2_t) ←
            (fp2sub (t1_693) (t2_694)) ;;
          ret (temp_696)) ;;
       '(t1_700 : (fp_t '× fp_t)) ←
        ( '(temp_699 : fp2_t) ←
            (fp2sub (x1_661) (x3_697)) ;;
          ret (temp_699)) ;;
       '(t2_703 : (fp_t '× fp_t)) ←
        ( '(temp_702 : fp2_t) ←
            (fp2mul (xovery_684) (t1_700)) ;;
          ret (temp_702)) ;;
       '(y3_706 : (fp_t '× fp_t)) ←
        ( '(temp_705 : fp2_t) ←
            (fp2sub (t2_703) (y1_675)) ;;
          ret (temp_705)) ;;
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality)) (
        prod_ce(x3_697, y3_706, (false : bool_ChoiceEquality))) } : code (
        fset.fset0) [interface
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
      #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_g2double_a : package _ _ _ :=
  (seq_link g2double_a link_rest(
      package_fp2fromfp,package_fp2inv,package_fp2mul,package_fp2sub)).
Fail Next Obligation.


Notation "'g2double_inp'" := (
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2double_out'" := (
  g2_t : choice_type) (in custom pack_type at level 2).
Definition G2DOUBLE : nat :=
  (728).
Program Definition g2double
   : package (fset.fset0) [interface
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
  #val #[ G2DOUBLE_A ] : g2double_a_inp → g2double_a_out ] [interface
  #val #[ G2DOUBLE ] : g2double_inp → g2double_out ] :=
  ([package #def #[ G2DOUBLE ] (temp_inp : g2double_inp) : g2double_out { 
    let '(p_710) := temp_inp : g2_t in
    #import {sig #[ FP2ZERO ] : fp2zero_inp → fp2zero_out } as fp2zero ;;
    let fp2zero := fp2zero tt in
    #import {sig #[ G2DOUBLE_A ] : g2double_a_inp → g2double_a_out } as g2double_a ;;
    let g2double_a := fun x_0 => g2double_a (x_0) in
    ({ code  temp_726 ←
        (ret (p_710)) ;;
      let '(x1_727, y1_711, inf1_716) :=
        (temp_726) : (fp2_t '× fp2_t '× bool_ChoiceEquality) in
       '(temp_713 : fp2_t) ←
        (fp2zero ) ;;
       '(temp_715 : bool_ChoiceEquality) ←
        ((y1_711) !=.? (temp_713)) ;;
       '(temp_718 : bool_ChoiceEquality) ←
        ((temp_715) && (negb (inf1_716))) ;;
       '(temp_720 : g2_t) ←
        (g2double_a (p_710)) ;;
       '(temp_722 : fp2_t) ←
        (fp2zero ) ;;
       '(temp_724 : fp2_t) ←
        (fp2zero ) ;;
      @ret (g2_t) ((if (temp_718):bool_ChoiceEquality then (temp_720) else (
            prod_ce(temp_722, temp_724, (true : bool_ChoiceEquality)
            )))) } : code (fset.fset0) [interface
      #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
      #val #[ G2DOUBLE_A ] : g2double_a_inp → g2double_a_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_g2double : package _ _ _ :=
  (seq_link g2double link_rest(package_fp2zero,package_g2double_a)).
Fail Next Obligation.


Notation "'g2add_inp'" := (
  g2_t '× g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2add_out'" := (g2_t : choice_type) (in custom pack_type at level 2).
Definition G2ADD : nat :=
  (759).
Program Definition g2add
   : package (fset.fset0) [interface
  #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ;
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
  #val #[ G2ADD_A ] : g2add_a_inp → g2add_a_out ;
  #val #[ G2DOUBLE ] : g2double_inp → g2double_out ] [interface
  #val #[ G2ADD ] : g2add_inp → g2add_out ] :=
  ([package #def #[ G2ADD ] (temp_inp : g2add_inp) : g2add_out { 
    let '(p_729 , q_730) := temp_inp : g2_t '× g2_t in
    #import {sig #[ FP2NEG ] : fp2neg_inp → fp2neg_out } as fp2neg ;;
    let fp2neg := fun x_0 => fp2neg (x_0) in
    #import {sig #[ FP2ZERO ] : fp2zero_inp → fp2zero_out } as fp2zero ;;
    let fp2zero := fp2zero tt in
    #import {sig #[ G2ADD_A ] : g2add_a_inp → g2add_a_out } as g2add_a ;;
    let g2add_a := fun x_0 x_1 => g2add_a (x_0,x_1) in
    #import {sig #[ G2DOUBLE ] : g2double_inp → g2double_out } as g2double ;;
    let g2double := fun x_0 => g2double (x_0) in
    ({ code  temp_758 ←
        (ret (p_729)) ;;
      let '(x1_737, y1_741, inf1_731) :=
        (temp_758) : (fp2_t '× fp2_t '× bool_ChoiceEquality) in
       temp_756 ←
        (ret (q_730)) ;;
      let '(x2_738, y2_742, inf2_732) :=
        (temp_756) : (fp2_t '× fp2_t '× bool_ChoiceEquality) in
       '(temp_734 : bool_ChoiceEquality) ←
        ((p_729) =.? (q_730)) ;;
       '(temp_736 : g2_t) ←
        (g2double (p_729)) ;;
       '(temp_740 : bool_ChoiceEquality) ←
        ((x1_737) =.? (x2_738)) ;;
       '(temp_744 : fp2_t) ←
        (fp2neg (y2_742)) ;;
       '(temp_746 : bool_ChoiceEquality) ←
        ((y1_741) =.? (temp_744)) ;;
       '(temp_748 : bool_ChoiceEquality) ←
        ((temp_740) && (temp_746)) ;;
       '(temp_750 : g2_t) ←
        (g2add_a (p_729) (q_730)) ;;
       '(temp_752 : fp2_t) ←
        (fp2zero ) ;;
       '(temp_754 : fp2_t) ←
        (fp2zero ) ;;
      @ret (g2_t) ((if (inf1_731):bool_ChoiceEquality then (q_730) else ((if (
                inf2_732):bool_ChoiceEquality then (p_729) else ((if (
                    temp_734):bool_ChoiceEquality then (temp_736) else ((if (
                        negb (temp_748)):bool_ChoiceEquality then (
                        temp_750) else (prod_ce(
                          temp_752,
                          temp_754,
                          (true : bool_ChoiceEquality)
                        )))))))))) } : code (fset.fset0) [interface
      #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ;
      #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
      #val #[ G2ADD_A ] : g2add_a_inp → g2add_a_out ;
      #val #[ G2DOUBLE ] : g2double_inp → g2double_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_g2add : package _ _ _ :=
  (seq_link g2add link_rest(
      package_fp2neg,package_fp2zero,package_g2add_a,package_g2double)).
Fail Next Obligation.

Definition t_764_loc : ChoiceEqualityLocation :=
  (((fp2_t '× fp2_t '× bool_ChoiceEquality) ; 776%nat)).
Notation "'g2mul_inp'" := (
  scalar_t '× g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2mul_out'" := (g2_t : choice_type) (in custom pack_type at level 2).
Definition G2MUL : nat :=
  (777).
Program Definition g2mul
   : package (CEfset ([t_764_loc])) [interface
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
  #val #[ G2ADD ] : g2add_inp → g2add_out ;
  #val #[ G2DOUBLE ] : g2double_inp → g2double_out ] [interface
  #val #[ G2MUL ] : g2mul_inp → g2mul_out ] :=
  ([package #def #[ G2MUL ] (temp_inp : g2mul_inp) : g2mul_out { 
    let '(m_767 , p_773) := temp_inp : scalar_t '× g2_t in
    #import {sig #[ FP2ZERO ] : fp2zero_inp → fp2zero_out } as fp2zero ;;
    let fp2zero := fp2zero tt in
    #import {sig #[ G2ADD ] : g2add_inp → g2add_out } as g2add ;;
    let g2add := fun x_0 x_1 => g2add (x_0,x_1) in
    #import {sig #[ G2DOUBLE ] : g2double_inp → g2double_out } as g2double ;;
    let g2double := fun x_0 => g2double (x_0) in
    ({ code  '(t_764 : (fp2_t '× fp2_t '× bool_ChoiceEquality)) ←
          ( '(temp_761 : fp2_t) ←
              (fp2zero ) ;;
             '(temp_763 : fp2_t) ←
              (fp2zero ) ;;
            ret (prod_ce(temp_761, temp_763, (true : bool_ChoiceEquality)))) ;;
        #put t_764_loc := t_764 ;;
       '(t_764 : ((fp2_t '× fp2_t '× bool_ChoiceEquality))) ←
        (foldi' (usize 0) (usize 256) t_764 (L2 := CEfset ([t_764_loc])) (
              I2 := [interface #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
              #val #[ G2ADD ] : g2add_inp → g2add_out ;
              #val #[ G2DOUBLE ] : g2double_inp → g2double_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_768 t_764 =>
            ({ code  '(t_764 : (fp2_t '× fp2_t '× bool_ChoiceEquality)) ←
                  (( '(temp_766 : g2_t) ←
                        (g2double (t_764)) ;;
                      ret (temp_766))) ;;
                #put t_764_loc := t_764 ;;
              
               '(temp_770 : uint_size) ←
                ((usize 255) .- (i_768)) ;;
               temp_772 ←
                (nat_mod_bit (m_767) (temp_770)) ;;
               '(t_764 : ((fp2_t '× fp2_t '× bool_ChoiceEquality))) ←
                (if temp_772:bool_ChoiceEquality
                  then (({ code  '(t_764 : (
                              fp2_t '×
                              fp2_t '×
                              bool_ChoiceEquality
                            )) ←
                          (( '(temp_775 : g2_t) ←
                                (g2add (t_764) (p_773)) ;;
                              ret (temp_775))) ;;
                        #put t_764_loc := t_764 ;;
                      
                      @ret (((fp2_t '× fp2_t '× bool_ChoiceEquality))) (
                        t_764) } : code (CEfset ([t_764_loc])) [interface
                      #val #[ G2ADD ] : g2add_inp → g2add_out ] _))
                  else @ret (((fp2_t '× fp2_t '× bool_ChoiceEquality))) (
                    t_764)) ;;
              
              @ret (((fp2_t '× fp2_t '× bool_ChoiceEquality))) (
                t_764) } : code (CEfset ([t_764_loc])) [interface
              #val #[ G2ADD ] : g2add_inp → g2add_out ;
              #val #[ G2DOUBLE ] : g2double_inp → g2double_out ] _))) ;;
      
      @ret ((fp2_t '× fp2_t '× bool_ChoiceEquality)) (t_764) } : code (
        CEfset ([t_764_loc])) [interface
      #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
      #val #[ G2ADD ] : g2add_inp → g2add_out ;
      #val #[ G2DOUBLE ] : g2double_inp → g2double_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_g2mul : package _ _ _ :=
  (seq_link g2mul link_rest(package_fp2zero,package_g2add,package_g2double)).
Fail Next Obligation.


Notation "'g2neg_inp'" := (g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2neg_out'" := (g2_t : choice_type) (in custom pack_type at level 2).
Definition G2NEG : nat :=
  (786).
Program Definition g2neg
   : package (fset.fset0) [interface
  #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ] [interface
  #val #[ G2NEG ] : g2neg_inp → g2neg_out ] :=
  ([package #def #[ G2NEG ] (temp_inp : g2neg_inp) : g2neg_out { 
    let '(p_778) := temp_inp : g2_t in
    #import {sig #[ FP2NEG ] : fp2neg_inp → fp2neg_out } as fp2neg ;;
    let fp2neg := fun x_0 => fp2neg (x_0) in
    ({ code  temp_785 ←
        (ret (p_778)) ;;
      let '(x_779, y_780, inf_783) :=
        (temp_785) : (fp2_t '× fp2_t '× bool_ChoiceEquality) in
       '(temp_782 : fp2_t) ←
        (fp2neg (y_780)) ;;
      @ret (((fp_t '× fp_t) '× fp2_t '× bool_ChoiceEquality)) (prod_ce(
          x_779,
          temp_782,
          inf_783
        )) } : code (fset.fset0) [interface
      #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_g2neg : package _ _ _ :=
  (seq_link g2neg link_rest(package_fp2neg)).
Fail Next Obligation.


Notation "'twist_inp'" := (g1_t : choice_type) (in custom pack_type at level 2).
Notation "'twist_out'" := ((fp12_t '× fp12_t
  ) : choice_type) (in custom pack_type at level 2).
Definition TWIST : nat :=
  (810).
Program Definition twist
   : package (fset.fset0) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
  #val #[ FP6ZERO ] : fp6zero_inp → fp6zero_out ] [interface
  #val #[ TWIST ] : twist_inp → twist_out ] :=
  ([package #def #[ TWIST ] (temp_inp : twist_inp) : twist_out { 
    let '(p_787) := temp_inp : g1_t in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP2ZERO ] : fp2zero_inp → fp2zero_out } as fp2zero ;;
    let fp2zero := fp2zero tt in
    #import {sig #[ FP6ZERO ] : fp6zero_inp → fp6zero_out } as fp6zero ;;
    let fp6zero := fp6zero tt in
    ({ code  temp_809 ←
        (ret (p_787)) ;;
      let '(p0_790, p1_801, _) :=
        (temp_809) : (fp_t '× fp_t '× bool_ChoiceEquality) in
       '(x_806 : ((fp2_t '× fp2_t '× fp2_t) '× fp6_t)) ←
        ( '(temp_789 : fp2_t) ←
            (fp2zero ) ;;
           '(temp_792 : fp2_t) ←
            (fp2fromfp (p0_790)) ;;
           '(temp_794 : fp2_t) ←
            (fp2zero ) ;;
           '(temp_796 : fp6_t) ←
            (fp6zero ) ;;
          ret (prod_ce(prod_ce(temp_789, temp_792, temp_794), temp_796))) ;;
       '(y_807 : (fp6_t '× (fp2_t '× fp2_t '× fp2_t))) ←
        ( '(temp_798 : fp6_t) ←
            (fp6zero ) ;;
           '(temp_800 : fp2_t) ←
            (fp2zero ) ;;
           '(temp_803 : fp2_t) ←
            (fp2fromfp (p1_801)) ;;
           '(temp_805 : fp2_t) ←
            (fp2zero ) ;;
          ret (prod_ce(temp_798, prod_ce(temp_800, temp_803, temp_805)))) ;;
      @ret ((
          ((fp2_t '× fp2_t '× fp2_t) '× fp6_t) '×
          (fp6_t '× (fp2_t '× fp2_t '× fp2_t))
        )) (prod_ce(x_806, y_807)) } : code (fset.fset0) [interface
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
      #val #[ FP6ZERO ] : fp6zero_inp → fp6zero_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_twist : package _ _ _ :=
  (seq_link twist link_rest(package_fp2fromfp,package_fp2zero,package_fp6zero)).
Fail Next Obligation.


Notation "'line_double_p_inp'" := (
  g2_t '× g1_t : choice_type) (in custom pack_type at level 2).
Notation "'line_double_p_out'" := (
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition LINE_DOUBLE_P : nat :=
  (866).
Program Definition line_double_p
   : package (fset.fset0) [interface
  #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
  #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
  #val #[ FP12NEG ] : fp12neg_inp → fp12neg_out ;
  #val #[ FP12SUB ] : fp12sub_inp → fp12sub_out ;
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
  #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ;
  #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ;
  #val #[ TWIST ] : twist_inp → twist_out ] [interface
  #val #[ LINE_DOUBLE_P ] : line_double_p_inp → line_double_p_out ] :=
  (
    [package #def #[ LINE_DOUBLE_P ] (temp_inp : line_double_p_inp) : line_double_p_out { 
    let '(r_811 , p_847) := temp_inp : g2_t '× g1_t in
    #import {sig #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out } as fp12fromfp6 ;;
    let fp12fromfp6 := fun x_0 => fp12fromfp6 (x_0) in
    #import {sig #[ FP12MUL ] : fp12mul_inp → fp12mul_out } as fp12mul ;;
    let fp12mul := fun x_0 x_1 => fp12mul (x_0,x_1) in
    #import {sig #[ FP12NEG ] : fp12neg_inp → fp12neg_out } as fp12neg ;;
    let fp12neg := fun x_0 => fp12neg (x_0) in
    #import {sig #[ FP12SUB ] : fp12sub_inp → fp12sub_out } as fp12sub ;;
    let fp12sub := fun x_0 x_1 => fp12sub (x_0,x_1) in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP2INV ] : fp2inv_inp → fp2inv_out } as fp2inv ;;
    let fp2inv := fun x_0 => fp2inv (x_0) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    #import {sig #[ FP2SUB ] : fp2sub_inp → fp2sub_out } as fp2sub ;;
    let fp2sub := fun x_0 x_1 => fp2sub (x_0,x_1) in
    #import {sig #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out } as fp6fromfp2 ;;
    let fp6fromfp2 := fun x_0 => fp6fromfp2 (x_0) in
    #import {sig #[ TWIST ] : twist_inp → twist_out } as twist ;;
    let twist := fun x_0 => twist (x_0) in
    ({ code  temp_865 ←
        (ret (r_811)) ;;
      let '(r0_816, r1_826, _) :=
        (temp_865) : (fp2_t '× fp2_t '× bool_ChoiceEquality) in
       '(a_821 : (fp_t '× fp_t)) ←
        ( '(temp_813 : fp_t) ←
            (nat_mod_from_literal (
                0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
                @repr U128 3)) ;;
           '(temp_815 : fp2_t) ←
            (fp2fromfp (temp_813)) ;;
           '(temp_818 : fp2_t) ←
            (fp2mul (r0_816) (r0_816)) ;;
           '(temp_820 : fp2_t) ←
            (fp2mul (temp_815) (temp_818)) ;;
          ret (temp_820)) ;;
       '(a_833 : (fp_t '× fp_t)) ←
        ( '(temp_823 : fp_t) ←
            (nat_mod_two ) ;;
           '(temp_825 : fp2_t) ←
            (fp2fromfp (temp_823)) ;;
           '(temp_828 : fp2_t) ←
            (fp2mul (temp_825) (r1_826)) ;;
           '(temp_830 : fp2_t) ←
            (fp2inv (temp_828)) ;;
           '(temp_832 : fp2_t) ←
            (fp2mul (a_821) (temp_830)) ;;
          ret (temp_832)) ;;
       '(b_842 : (fp_t '× fp_t)) ←
        ( '(temp_835 : fp2_t) ←
            (fp2mul (a_833) (r0_816)) ;;
           '(temp_837 : fp2_t) ←
            (fp2sub (r1_826) (temp_835)) ;;
          ret (temp_837)) ;;
       '(a_851 : (fp6_t '× fp6_t)) ←
        ( '(temp_839 : fp6_t) ←
            (fp6fromfp2 (a_833)) ;;
           '(temp_841 : fp12_t) ←
            (fp12fromfp6 (temp_839)) ;;
          ret (temp_841)) ;;
       '(b_857 : (fp6_t '× fp6_t)) ←
        ( '(temp_844 : fp6_t) ←
            (fp6fromfp2 (b_842)) ;;
           '(temp_846 : fp12_t) ←
            (fp12fromfp6 (temp_844)) ;;
          ret (temp_846)) ;;
       temp_863 ←
        ( '(temp_849 : (fp12_t '× fp12_t)) ←
            (twist (p_847)) ;;
          ret (temp_849)) ;;
      let '(x_852, y_850) :=
        (temp_863) : (fp12_t '× fp12_t) in
       '(temp_854 : fp12_t) ←
        (fp12mul (a_851) (x_852)) ;;
       '(temp_856 : fp12_t) ←
        (fp12sub (y_850) (temp_854)) ;;
       '(temp_859 : fp12_t) ←
        (fp12sub (temp_856) (b_857)) ;;
       '(temp_861 : fp12_t) ←
        (fp12neg (temp_859)) ;;
      @ret (fp12_t) (temp_861) } : code (fset.fset0) [interface
      #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
      #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
      #val #[ FP12NEG ] : fp12neg_inp → fp12neg_out ;
      #val #[ FP12SUB ] : fp12sub_inp → fp12sub_out ;
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
      #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ;
      #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ;
      #val #[ TWIST ] : twist_inp → twist_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_line_double_p : package _ _ _ :=
  (seq_link line_double_p link_rest(
      package_fp12fromfp6,package_fp12mul,package_fp12neg,package_fp12sub,package_fp2fromfp,package_fp2inv,package_fp2mul,package_fp2sub,package_fp6fromfp2,package_twist)).
Fail Next Obligation.


Notation "'line_add_p_inp'" := (
  g2_t '× g2_t '× g1_t : choice_type) (in custom pack_type at level 2).
Notation "'line_add_p_out'" := (
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition LINE_ADD_P : nat :=
  (916).
Program Definition line_add_p
   : package (fset.fset0) [interface
  #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
  #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
  #val #[ FP12NEG ] : fp12neg_inp → fp12neg_out ;
  #val #[ FP12SUB ] : fp12sub_inp → fp12sub_out ;
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
  #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ;
  #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ;
  #val #[ TWIST ] : twist_inp → twist_out ] [interface
  #val #[ LINE_ADD_P ] : line_add_p_inp → line_add_p_out ] :=
  ([package #def #[ LINE_ADD_P ] (temp_inp : line_add_p_inp) : line_add_p_out { 
    let '(r_867 , q_868 , p_895) := temp_inp : g2_t '× g2_t '× g1_t in
    #import {sig #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out } as fp12fromfp6 ;;
    let fp12fromfp6 := fun x_0 => fp12fromfp6 (x_0) in
    #import {sig #[ FP12MUL ] : fp12mul_inp → fp12mul_out } as fp12mul ;;
    let fp12mul := fun x_0 x_1 => fp12mul (x_0,x_1) in
    #import {sig #[ FP12NEG ] : fp12neg_inp → fp12neg_out } as fp12neg ;;
    let fp12neg := fun x_0 => fp12neg (x_0) in
    #import {sig #[ FP12SUB ] : fp12sub_inp → fp12sub_out } as fp12sub ;;
    let fp12sub := fun x_0 x_1 => fp12sub (x_0,x_1) in
    #import {sig #[ FP2INV ] : fp2inv_inp → fp2inv_out } as fp2inv ;;
    let fp2inv := fun x_0 => fp2inv (x_0) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    #import {sig #[ FP2SUB ] : fp2sub_inp → fp2sub_out } as fp2sub ;;
    let fp2sub := fun x_0 x_1 => fp2sub (x_0,x_1) in
    #import {sig #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out } as fp6fromfp2 ;;
    let fp6fromfp2 := fun x_0 => fp6fromfp2 (x_0) in
    #import {sig #[ TWIST ] : twist_inp → twist_out } as twist ;;
    let twist := fun x_0 => twist (x_0) in
    ({ code  temp_915 ←
        (ret (r_867)) ;;
      let '(r0_874, r1_870, _) :=
        (temp_915) : (fp2_t '× fp2_t '× bool_ChoiceEquality) in
       temp_913 ←
        (ret (q_868)) ;;
      let '(q0_873, q1_869, _) :=
        (temp_913) : (fp2_t '× fp2_t '× bool_ChoiceEquality) in
       '(a_881 : (fp_t '× fp_t)) ←
        ( '(temp_872 : fp2_t) ←
            (fp2sub (q1_869) (r1_870)) ;;
           '(temp_876 : fp2_t) ←
            (fp2sub (q0_873) (r0_874)) ;;
           '(temp_878 : fp2_t) ←
            (fp2inv (temp_876)) ;;
           '(temp_880 : fp2_t) ←
            (fp2mul (temp_872) (temp_878)) ;;
          ret (temp_880)) ;;
       '(b_890 : (fp_t '× fp_t)) ←
        ( '(temp_883 : fp2_t) ←
            (fp2mul (a_881) (r0_874)) ;;
           '(temp_885 : fp2_t) ←
            (fp2sub (r1_870) (temp_883)) ;;
          ret (temp_885)) ;;
       '(a_899 : (fp6_t '× fp6_t)) ←
        ( '(temp_887 : fp6_t) ←
            (fp6fromfp2 (a_881)) ;;
           '(temp_889 : fp12_t) ←
            (fp12fromfp6 (temp_887)) ;;
          ret (temp_889)) ;;
       '(b_905 : (fp6_t '× fp6_t)) ←
        ( '(temp_892 : fp6_t) ←
            (fp6fromfp2 (b_890)) ;;
           '(temp_894 : fp12_t) ←
            (fp12fromfp6 (temp_892)) ;;
          ret (temp_894)) ;;
       temp_911 ←
        ( '(temp_897 : (fp12_t '× fp12_t)) ←
            (twist (p_895)) ;;
          ret (temp_897)) ;;
      let '(x_900, y_898) :=
        (temp_911) : (fp12_t '× fp12_t) in
       '(temp_902 : fp12_t) ←
        (fp12mul (a_899) (x_900)) ;;
       '(temp_904 : fp12_t) ←
        (fp12sub (y_898) (temp_902)) ;;
       '(temp_907 : fp12_t) ←
        (fp12sub (temp_904) (b_905)) ;;
       '(temp_909 : fp12_t) ←
        (fp12neg (temp_907)) ;;
      @ret (fp12_t) (temp_909) } : code (fset.fset0) [interface
      #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
      #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
      #val #[ FP12NEG ] : fp12neg_inp → fp12neg_out ;
      #val #[ FP12SUB ] : fp12sub_inp → fp12sub_out ;
      #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
      #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ;
      #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ;
      #val #[ TWIST ] : twist_inp → twist_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_line_add_p : package _ _ _ :=
  (seq_link line_add_p link_rest(
      package_fp12fromfp6,package_fp12mul,package_fp12neg,package_fp12sub,package_fp2inv,package_fp2mul,package_fp2sub,package_fp6fromfp2,package_twist)).
Fail Next Obligation.


Notation "'frobenius_inp'" := (
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'frobenius_out'" := (
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition FROBENIUS : nat :=
  (1014).
Program Definition frobenius
   : package (fset.fset0) [interface
  #val #[ FP2CONJUGATE ] : fp2conjugate_inp → fp2conjugate_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] [interface
  #val #[ FROBENIUS ] : frobenius_inp → frobenius_out ] :=
  ([package #def #[ FROBENIUS ] (temp_inp : frobenius_inp) : frobenius_out { 
    let '(f_917) := temp_inp : fp12_t in
    #import {sig #[ FP2CONJUGATE ] : fp2conjugate_inp → fp2conjugate_out } as fp2conjugate ;;
    let fp2conjugate := fun x_0 => fp2conjugate (x_0) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    ({ code  temp_1013 ←
        (ret (f_917)) ;;
      let '((g0_918, g1_924, g2_930), (h0_921, h1_927, h2_933)) :=
        (temp_1013) : (fp6_t '× fp6_t) in
       '(t1_1006 : (fp_t '× fp_t)) ←
        ( '(temp_920 : fp2_t) ←
            (fp2conjugate (g0_918)) ;;
          ret (temp_920)) ;;
       '(t2_990 : (fp_t '× fp_t)) ←
        ( '(temp_923 : fp2_t) ←
            (fp2conjugate (h0_921)) ;;
          ret (temp_923)) ;;
       '(t3_993 : (fp_t '× fp_t)) ←
        ( '(temp_926 : fp2_t) ←
            (fp2conjugate (g1_924)) ;;
          ret (temp_926)) ;;
       '(t4_996 : (fp_t '× fp_t)) ←
        ( '(temp_929 : fp2_t) ←
            (fp2conjugate (h1_927)) ;;
          ret (temp_929)) ;;
       '(t5_999 : (fp_t '× fp_t)) ←
        ( '(temp_932 : fp2_t) ←
            (fp2conjugate (g2_930)) ;;
          ret (temp_932)) ;;
       '(t6_1002 : (fp_t '× fp_t)) ←
        ( '(temp_935 : fp2_t) ←
            (fp2conjugate (h2_933)) ;;
          ret (temp_935)) ;;
       '(c1_950 : array_fp_t) ←
        ( '(temp_937 : int64) ←
            (secret (@repr U64 10162220747404304312)) ;;
           '(temp_939 : int64) ←
            (secret (@repr U64 17761815663483519293)) ;;
           '(temp_941 : int64) ←
            (secret (@repr U64 8873291758750579140)) ;;
           '(temp_943 : int64) ←
            (secret (@repr U64 1141103941765652303)) ;;
           '(temp_945 : int64) ←
            (secret (@repr U64 13993175198059990303)) ;;
           '(temp_947 : int64) ←
            (secret (@repr U64 1802798568193066599)) ;;
           '(temp_949 : nseq uint64 6) ←
            (array_from_list uint64 [
                temp_937;
                temp_939;
                temp_941;
                temp_943;
                temp_945;
                temp_947
              ]) ;;
          ret (temp_949)) ;;
       '(c1_953 : seq uint8) ←
        ( temp_952 ←
            (array_to_le_bytes (c1_950)) ;;
          ret (temp_952)) ;;
       '(c1_976 : fp_t) ←
        ( '(temp_955 : fp_t) ←
            (nat_mod_from_byte_seq_le (c1_953)) ;;
          ret (temp_955)) ;;
       '(c2_970 : array_fp_t) ←
        ( '(temp_957 : int64) ←
            (secret (@repr U64 3240210268673559283)) ;;
           '(temp_959 : int64) ←
            (secret (@repr U64 2895069921743240898)) ;;
           '(temp_961 : int64) ←
            (secret (@repr U64 17009126888523054175)) ;;
           '(temp_963 : int64) ←
            (secret (@repr U64 6098234018649060207)) ;;
           '(temp_965 : int64) ←
            (secret (@repr U64 9865672654120263608)) ;;
           '(temp_967 : int64) ←
            (secret (@repr U64 71000049454473266)) ;;
           '(temp_969 : nseq uint64 6) ←
            (array_from_list uint64 [
                temp_957;
                temp_959;
                temp_961;
                temp_963;
                temp_965;
                temp_967
              ]) ;;
          ret (temp_969)) ;;
       '(c2_973 : seq uint8) ←
        ( temp_972 ←
            (array_to_le_bytes (c2_970)) ;;
          ret (temp_972)) ;;
       '(c2_977 : fp_t) ←
        ( '(temp_975 : fp_t) ←
            (nat_mod_from_byte_seq_le (c2_973)) ;;
          ret (temp_975)) ;;
       '(gamma11_978 : (fp_t '× fp_t)) ←
        (ret (prod_ce(c1_976, c2_977))) ;;
       '(gamma12_981 : (fp_t '× fp_t)) ←
        ( '(temp_980 : fp2_t) ←
            (fp2mul (gamma11_978) (gamma11_978)) ;;
          ret (temp_980)) ;;
       '(gamma13_984 : (fp_t '× fp_t)) ←
        ( '(temp_983 : fp2_t) ←
            (fp2mul (gamma12_981) (gamma11_978)) ;;
          ret (temp_983)) ;;
       '(gamma14_987 : (fp_t '× fp_t)) ←
        ( '(temp_986 : fp2_t) ←
            (fp2mul (gamma13_984) (gamma11_978)) ;;
          ret (temp_986)) ;;
       '(gamma15_1003 : (fp_t '× fp_t)) ←
        ( '(temp_989 : fp2_t) ←
            (fp2mul (gamma14_987) (gamma11_978)) ;;
          ret (temp_989)) ;;
       '(t2_1009 : (fp_t '× fp_t)) ←
        ( '(temp_992 : fp2_t) ←
            (fp2mul (t2_990) (gamma11_978)) ;;
          ret (temp_992)) ;;
       '(t3_1007 : (fp_t '× fp_t)) ←
        ( '(temp_995 : fp2_t) ←
            (fp2mul (t3_993) (gamma12_981)) ;;
          ret (temp_995)) ;;
       '(t4_1010 : (fp_t '× fp_t)) ←
        ( '(temp_998 : fp2_t) ←
            (fp2mul (t4_996) (gamma13_984)) ;;
          ret (temp_998)) ;;
       '(t5_1008 : (fp_t '× fp_t)) ←
        ( '(temp_1001 : fp2_t) ←
            (fp2mul (t5_999) (gamma14_987)) ;;
          ret (temp_1001)) ;;
       '(t6_1011 : (fp_t '× fp_t)) ←
        ( '(temp_1005 : fp2_t) ←
            (fp2mul (t6_1002) (gamma15_1003)) ;;
          ret (temp_1005)) ;;
      @ret ((
          ((fp_t '× fp_t) '× (fp_t '× fp_t) '× (fp_t '× fp_t)) '×
          ((fp_t '× fp_t) '× (fp_t '× fp_t) '× (fp_t '× fp_t))
        )) (prod_ce(
          prod_ce(t1_1006, t3_1007, t5_1008),
          prod_ce(t2_1009, t4_1010, t6_1011)
        )) } : code (fset.fset0) [interface
      #val #[ FP2CONJUGATE ] : fp2conjugate_inp → fp2conjugate_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_frobenius : package _ _ _ :=
  (seq_link frobenius link_rest(package_fp2conjugate,package_fp2mul)).
Fail Next Obligation.

Notation "'final_exponentiation_inp'" := (
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'final_exponentiation_out'" := (
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition FINAL_EXPONENTIATION : nat :=
  (1124).
Program Definition final_exponentiation
   : package (CEfset ([])) [interface
  #val #[ FP12CONJUGATE ] : fp12conjugate_inp → fp12conjugate_out ;
  #val #[ FP12EXP ] : fp12exp_inp → fp12exp_out ;
  #val #[ FP12INV ] : fp12inv_inp → fp12inv_out ;
  #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
  #val #[ FROBENIUS ] : frobenius_inp → frobenius_out ] [interface
  #val #[ FINAL_EXPONENTIATION ] : final_exponentiation_inp → final_exponentiation_out
  ] :=
  (
    [package #def #[ FINAL_EXPONENTIATION ] (temp_inp : final_exponentiation_inp) : final_exponentiation_out { 
    let '(f_1015) := temp_inp : fp12_t in
    #import {sig #[ FP12CONJUGATE ] : fp12conjugate_inp → fp12conjugate_out } as fp12conjugate ;;
    let fp12conjugate := fun x_0 => fp12conjugate (x_0) in
    #import {sig #[ FP12EXP ] : fp12exp_inp → fp12exp_out } as fp12exp ;;
    let fp12exp := fun x_0 x_1 => fp12exp (x_0,x_1) in
    #import {sig #[ FP12INV ] : fp12inv_inp → fp12inv_out } as fp12inv ;;
    let fp12inv := fun x_0 => fp12inv (x_0) in
    #import {sig #[ FP12MUL ] : fp12mul_inp → fp12mul_out } as fp12mul ;;
    let fp12mul := fun x_0 x_1 => fp12mul (x_0,x_1) in
    #import {sig #[ FROBENIUS ] : frobenius_inp → frobenius_out } as frobenius ;;
    let frobenius := fun x_0 => frobenius (x_0) in
    ({ code  '(fp6_1020 : (fp6_t '× fp6_t)) ←
        ( '(temp_1017 : fp12_t) ←
            (fp12conjugate (f_1015)) ;;
          ret (temp_1017)) ;;
       '(finv_1021 : (fp6_t '× fp6_t)) ←
        ( '(temp_1019 : fp12_t) ←
            (fp12inv (f_1015)) ;;
          ret (temp_1019)) ;;
       '(fp6_1_1024 : (fp6_t '× fp6_t)) ←
        ( '(temp_1023 : fp12_t) ←
            (fp12mul (fp6_1020) (finv_1021)) ;;
          ret (temp_1023)) ;;
       '(fp8_1029 : (fp6_t '× fp6_t)) ←
        ( '(temp_1026 : fp12_t) ←
            (frobenius (fp6_1_1024)) ;;
           '(temp_1028 : fp12_t) ←
            (frobenius (temp_1026)) ;;
          ret (temp_1028)) ;;
       '(f_1034 : (fp6_t '× fp6_t)) ←
        ( '(temp_1031 : fp12_t) ←
            (fp12mul (fp8_1029) (fp6_1_1024)) ;;
          ret (temp_1031)) ;;
       '(u_1038 : scalar_t) ←
        ( '(temp_1033 : scalar_t) ←
            (nat_mod_from_literal (
                0x8000000000000000000000000000000000000000000000000000000000000000) (
                @repr U128 15132376222941642752)) ;;
          ret (temp_1033)) ;;
       '(t0_1037 : (fp6_t '× fp6_t)) ←
        ( '(temp_1036 : fp12_t) ←
            (fp12mul (f_1034) (f_1034)) ;;
          ret (temp_1036)) ;;
       '(t1_1041 : (fp6_t '× fp6_t)) ←
        ( '(temp_1040 : fp12_t) ←
            (fp12exp (t0_1037) (u_1038)) ;;
          ret (temp_1040)) ;;
       '(t1_1044 : (fp6_t '× fp6_t)) ←
        ( '(temp_1043 : fp12_t) ←
            (fp12conjugate (t1_1041)) ;;
          ret (temp_1043)) ;;
       '(t2_1051 : (fp6_t '× fp6_t)) ←
        ( '(temp_1046 : scalar_t) ←
            (nat_mod_two ) ;;
           '(temp_1048 : scalar_t) ←
            ((u_1038) /% (temp_1046)) ;;
           '(temp_1050 : fp12_t) ←
            (fp12exp (t1_1044) (temp_1048)) ;;
          ret (temp_1050)) ;;
       '(t2_1063 : (fp6_t '× fp6_t)) ←
        ( '(temp_1053 : fp12_t) ←
            (fp12conjugate (t2_1051)) ;;
          ret (temp_1053)) ;;
       '(t3_1056 : (fp6_t '× fp6_t)) ←
        ( '(temp_1055 : fp12_t) ←
            (fp12conjugate (f_1034)) ;;
          ret (temp_1055)) ;;
       '(t1_1059 : (fp6_t '× fp6_t)) ←
        ( '(temp_1058 : fp12_t) ←
            (fp12mul (t3_1056) (t1_1044)) ;;
          ret (temp_1058)) ;;
       '(t1_1062 : (fp6_t '× fp6_t)) ←
        ( '(temp_1061 : fp12_t) ←
            (fp12conjugate (t1_1059)) ;;
          ret (temp_1061)) ;;
       '(t1_1066 : (fp6_t '× fp6_t)) ←
        ( '(temp_1065 : fp12_t) ←
            (fp12mul (t1_1062) (t2_1063)) ;;
          ret (temp_1065)) ;;
       '(t2_1069 : (fp6_t '× fp6_t)) ←
        ( '(temp_1068 : fp12_t) ←
            (fp12exp (t1_1066) (u_1038)) ;;
          ret (temp_1068)) ;;
       '(t2_1072 : (fp6_t '× fp6_t)) ←
        ( '(temp_1071 : fp12_t) ←
            (fp12conjugate (t2_1069)) ;;
          ret (temp_1071)) ;;
       '(t3_1075 : (fp6_t '× fp6_t)) ←
        ( '(temp_1074 : fp12_t) ←
            (fp12exp (t2_1072) (u_1038)) ;;
          ret (temp_1074)) ;;
       '(t3_1081 : (fp6_t '× fp6_t)) ←
        ( '(temp_1077 : fp12_t) ←
            (fp12conjugate (t3_1075)) ;;
          ret (temp_1077)) ;;
       '(t1_1080 : (fp6_t '× fp6_t)) ←
        ( '(temp_1079 : fp12_t) ←
            (fp12conjugate (t1_1066)) ;;
          ret (temp_1079)) ;;
       '(t3_1101 : (fp6_t '× fp6_t)) ←
        ( '(temp_1083 : fp12_t) ←
            (fp12mul (t1_1080) (t3_1081)) ;;
          ret (temp_1083)) ;;
       '(t1_1086 : (fp6_t '× fp6_t)) ←
        ( '(temp_1085 : fp12_t) ←
            (fp12conjugate (t1_1080)) ;;
          ret (temp_1085)) ;;
       '(t1_1097 : (fp6_t '× fp6_t)) ←
        ( '(temp_1088 : fp12_t) ←
            (frobenius (t1_1086)) ;;
           '(temp_1090 : fp12_t) ←
            (frobenius (temp_1088)) ;;
           '(temp_1092 : fp12_t) ←
            (frobenius (temp_1090)) ;;
          ret (temp_1092)) ;;
       '(t2_1098 : (fp6_t '× fp6_t)) ←
        ( '(temp_1094 : fp12_t) ←
            (frobenius (t2_1072)) ;;
           '(temp_1096 : fp12_t) ←
            (frobenius (temp_1094)) ;;
          ret (temp_1096)) ;;
       '(t1_1113 : (fp6_t '× fp6_t)) ←
        ( '(temp_1100 : fp12_t) ←
            (fp12mul (t1_1097) (t2_1098)) ;;
          ret (temp_1100)) ;;
       '(t2_1104 : (fp6_t '× fp6_t)) ←
        ( '(temp_1103 : fp12_t) ←
            (fp12exp (t3_1101) (u_1038)) ;;
          ret (temp_1103)) ;;
       '(t2_1107 : (fp6_t '× fp6_t)) ←
        ( '(temp_1106 : fp12_t) ←
            (fp12conjugate (t2_1104)) ;;
          ret (temp_1106)) ;;
       '(t2_1110 : (fp6_t '× fp6_t)) ←
        ( '(temp_1109 : fp12_t) ←
            (fp12mul (t2_1107) (t0_1037)) ;;
          ret (temp_1109)) ;;
       '(t2_1114 : (fp6_t '× fp6_t)) ←
        ( '(temp_1112 : fp12_t) ←
            (fp12mul (t2_1110) (f_1034)) ;;
          ret (temp_1112)) ;;
       '(t1_1119 : (fp6_t '× fp6_t)) ←
        ( '(temp_1116 : fp12_t) ←
            (fp12mul (t1_1113) (t2_1114)) ;;
          ret (temp_1116)) ;;
       '(t2_1120 : (fp6_t '× fp6_t)) ←
        ( '(temp_1118 : fp12_t) ←
            (frobenius (t3_1101)) ;;
          ret (temp_1118)) ;;
       '(t1_1123 : (fp6_t '× fp6_t)) ←
        ( '(temp_1122 : fp12_t) ←
            (fp12mul (t1_1119) (t2_1120)) ;;
          ret (temp_1122)) ;;
      @ret ((fp6_t '× fp6_t)) (t1_1123) } : code (CEfset ([])) [interface
      #val #[ FP12CONJUGATE ] : fp12conjugate_inp → fp12conjugate_out ;
      #val #[ FP12EXP ] : fp12exp_inp → fp12exp_out ;
      #val #[ FP12INV ] : fp12inv_inp → fp12inv_out ;
      #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
      #val #[ FROBENIUS ] : frobenius_inp → frobenius_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_final_exponentiation : package _ _ _ :=
  (seq_link final_exponentiation link_rest(
      package_fp12conjugate,package_fp12exp,package_fp12inv,package_fp12mul,package_frobenius)).
Fail Next Obligation.

Definition r_1136_loc : ChoiceEqualityLocation :=
  (((fp2_t '× fp2_t '× bool_ChoiceEquality) ; 1171%nat)).
Definition f_1142_loc : ChoiceEqualityLocation :=
  (((fp6_t '× fp6_t) ; 1172%nat)).
Notation "'pairing_inp'" := (
  g1_t '× g2_t : choice_type) (in custom pack_type at level 2).
Notation "'pairing_out'" := (
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition PAIRING : nat :=
  (1173).
Program Definition pairing
   : package (CEfset ([r_1136_loc ; f_1142_loc])) [interface
  #val #[ FINAL_EXPONENTIATION ] : final_exponentiation_inp → final_exponentiation_out ;
  #val #[ FP12CONJUGATE ] : fp12conjugate_inp → fp12conjugate_out ;
  #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
  #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ;
  #val #[ G2ADD ] : g2add_inp → g2add_out ;
  #val #[ G2DOUBLE ] : g2double_inp → g2double_out ;
  #val #[ LINE_ADD_P ] : line_add_p_inp → line_add_p_out ;
  #val #[ LINE_DOUBLE_P ] : line_double_p_inp → line_double_p_out ] [interface
  #val #[ PAIRING ] : pairing_inp → pairing_out ] :=
  ([package #def #[ PAIRING ] (temp_inp : pairing_inp) : pairing_out { 
    let '(p_1137 , q_1127) := temp_inp : g1_t '× g2_t in
    #import {sig #[ FINAL_EXPONENTIATION ] : final_exponentiation_inp → final_exponentiation_out } as final_exponentiation ;;
    let final_exponentiation := fun x_0 => final_exponentiation (x_0) in
    #import {sig #[ FP12CONJUGATE ] : fp12conjugate_inp → fp12conjugate_out } as fp12conjugate ;;
    let fp12conjugate := fun x_0 => fp12conjugate (x_0) in
    #import {sig #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out } as fp12fromfp6 ;;
    let fp12fromfp6 := fun x_0 => fp12fromfp6 (x_0) in
    #import {sig #[ FP12MUL ] : fp12mul_inp → fp12mul_out } as fp12mul ;;
    let fp12mul := fun x_0 x_1 => fp12mul (x_0,x_1) in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out } as fp6fromfp2 ;;
    let fp6fromfp2 := fun x_0 => fp6fromfp2 (x_0) in
    #import {sig #[ G2ADD ] : g2add_inp → g2add_out } as g2add ;;
    let g2add := fun x_0 x_1 => g2add (x_0,x_1) in
    #import {sig #[ G2DOUBLE ] : g2double_inp → g2double_out } as g2double ;;
    let g2double := fun x_0 => g2double (x_0) in
    #import {sig #[ LINE_ADD_P ] : line_add_p_inp → line_add_p_out } as line_add_p ;;
    let line_add_p := fun x_0 x_1 x_2 => line_add_p (x_0,x_1,x_2) in
    #import {sig #[ LINE_DOUBLE_P ] : line_double_p_inp → line_double_p_out } as line_double_p ;;
    let line_double_p := fun x_0 x_1 => line_double_p (x_0,x_1) in
    ({ code  '(t_1148 : scalar_t) ←
        ( '(temp_1126 : scalar_t) ←
            (nat_mod_from_literal (
                0x8000000000000000000000000000000000000000000000000000000000000000) (
                @repr U128 15132376222941642752)) ;;
          ret (temp_1126)) ;;
       '(r_1136 : (fp2_t '× fp2_t '× bool_ChoiceEquality)) ←
          (ret (q_1127)) ;;
        #put r_1136_loc := r_1136 ;;
       '(f_1142 : (fp6_t '× fp6_t)) ←
          ( '(temp_1129 : fp_t) ←
              (nat_mod_one ) ;;
             '(temp_1131 : fp2_t) ←
              (fp2fromfp (temp_1129)) ;;
             '(temp_1133 : fp6_t) ←
              (fp6fromfp2 (temp_1131)) ;;
             '(temp_1135 : fp12_t) ←
              (fp12fromfp6 (temp_1133)) ;;
            ret (temp_1135)) ;;
        #put f_1142_loc := f_1142 ;;
       temp_1170 ←
        (foldi' (usize 1) (usize 64) prod_ce(r_1136, f_1142) (L2 := CEfset (
                [r_1136_loc ; f_1142_loc])) (I2 := [interface
              #val #[ FINAL_EXPONENTIATION ] : final_exponentiation_inp → final_exponentiation_out ;
              #val #[ FP12CONJUGATE ] : fp12conjugate_inp → fp12conjugate_out ;
              #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
              #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
              #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
              #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ;
              #val #[ G2ADD ] : g2add_inp → g2add_out ;
              #val #[ G2DOUBLE ] : g2double_inp → g2double_out ;
              #val #[ LINE_ADD_P ] : line_add_p_inp → line_add_p_out ;
              #val #[ LINE_DOUBLE_P ] : line_double_p_inp → line_double_p_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_1149 '(
              r_1136,
              f_1142
            ) =>
            ({ code  '(lrr_1145 : (fp6_t '× fp6_t)) ←
                ( '(temp_1139 : fp12_t) ←
                    (line_double_p (r_1136) (p_1137)) ;;
                  ret (temp_1139)) ;;
               '(r_1136 : (fp2_t '× fp2_t '× bool_ChoiceEquality)) ←
                  (( '(temp_1141 : g2_t) ←
                        (g2double (r_1136)) ;;
                      ret (temp_1141))) ;;
                #put r_1136_loc := r_1136 ;;
              
               '(f_1142 : (fp6_t '× fp6_t)) ←
                  (( '(temp_1144 : fp12_t) ←
                        (fp12mul (f_1142) (f_1142)) ;;
                       '(temp_1147 : fp12_t) ←
                        (fp12mul (temp_1144) (lrr_1145)) ;;
                      ret (temp_1147))) ;;
                #put f_1142_loc := f_1142 ;;
              
               '(temp_1151 : uint_size) ←
                ((usize 64) .- (i_1149)) ;;
               '(temp_1153 : uint_size) ←
                ((temp_1151) .- (usize 1)) ;;
               temp_1155 ←
                (nat_mod_bit (t_1148) (temp_1153)) ;;
               temp_1164 ←
                (if temp_1155:bool_ChoiceEquality
                  then (({ code  '(lrq_1160 : (fp6_t '× fp6_t)) ←
                        ( '(temp_1157 : fp12_t) ←
                            (line_add_p (r_1136) (q_1127) (p_1137)) ;;
                          ret (temp_1157)) ;;
                       '(r_1136 : (fp2_t '× fp2_t '× bool_ChoiceEquality)) ←
                          (( '(temp_1159 : g2_t) ←
                                (g2add (r_1136) (q_1127)) ;;
                              ret (temp_1159))) ;;
                        #put r_1136_loc := r_1136 ;;
                      
                       '(f_1142 : (fp6_t '× fp6_t)) ←
                          (( '(temp_1162 : fp12_t) ←
                                (fp12mul (f_1142) (lrq_1160)) ;;
                              ret (temp_1162))) ;;
                        #put f_1142_loc := f_1142 ;;
                      
                      @ret ((
                          (fp2_t '× fp2_t '× bool_ChoiceEquality) '×
                          (fp6_t '× fp6_t)
                        )) (prod_ce(r_1136, f_1142)) } : code (CEfset (
                          [r_1136_loc ; f_1142_loc])) [interface
                      #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
                      #val #[ G2ADD ] : g2add_inp → g2add_out ;
                      #val #[ LINE_ADD_P ] : line_add_p_inp → line_add_p_out
                      ] _))
                  else @ret ((
                      (fp2_t '× fp2_t '× bool_ChoiceEquality) '×
                      (fp6_t '× fp6_t)
                    )) (prod_ce(r_1136, f_1142))) ;;
              let '(r_1136, f_1142) :=
                (temp_1164) : (
                (fp2_t '× fp2_t '× bool_ChoiceEquality) '×
                (fp6_t '× fp6_t)
              ) in
              
              @ret ((
                  (fp2_t '× fp2_t '× bool_ChoiceEquality) '×
                  (fp6_t '× fp6_t)
                )) (prod_ce(r_1136, f_1142)) } : code (CEfset (
                  [r_1136_loc ; f_1142_loc])) [interface
              #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
              #val #[ G2ADD ] : g2add_inp → g2add_out ;
              #val #[ G2DOUBLE ] : g2double_inp → g2double_out ;
              #val #[ LINE_ADD_P ] : line_add_p_inp → line_add_p_out ;
              #val #[ LINE_DOUBLE_P ] : line_double_p_inp → line_double_p_out
              ] _))) ;;
      let '(r_1136, f_1142) :=
        (temp_1170) : (
        (fp2_t '× fp2_t '× bool_ChoiceEquality) '×
        (fp6_t '× fp6_t)
      ) in
      
       '(temp_1166 : fp12_t) ←
        (fp12conjugate (f_1142)) ;;
       '(temp_1168 : fp12_t) ←
        (final_exponentiation (temp_1166)) ;;
      @ret (fp12_t) (temp_1168) } : code (CEfset (
          [r_1136_loc ; f_1142_loc])) [interface
      #val #[ FINAL_EXPONENTIATION ] : final_exponentiation_inp → final_exponentiation_out ;
      #val #[ FP12CONJUGATE ] : fp12conjugate_inp → fp12conjugate_out ;
      #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
      #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ;
      #val #[ G2ADD ] : g2add_inp → g2add_out ;
      #val #[ G2DOUBLE ] : g2double_inp → g2double_out ;
      #val #[ LINE_ADD_P ] : line_add_p_inp → line_add_p_out ;
      #val #[ LINE_DOUBLE_P ] : line_double_p_inp → line_double_p_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_pairing : package _ _ _ :=
  (seq_link pairing link_rest(
      package_final_exponentiation,package_fp12conjugate,package_fp12fromfp6,package_fp12mul,package_fp2fromfp,package_fp6fromfp2,package_g2add,package_g2double,package_line_add_p,package_line_double_p)).
Fail Next Obligation.


Notation "'test_fp2_prop_add_neg_inp'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'test_fp2_prop_add_neg_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition TEST_FP2_PROP_ADD_NEG : nat :=
  (1186).
Program Definition test_fp2_prop_add_neg
   : package (fset.fset0) [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ] [interface
  #val #[ TEST_FP2_PROP_ADD_NEG ] : test_fp2_prop_add_neg_inp → test_fp2_prop_add_neg_out
  ] :=
  (
    [package #def #[ TEST_FP2_PROP_ADD_NEG ] (temp_inp : test_fp2_prop_add_neg_inp) : test_fp2_prop_add_neg_out { 
    let '(a_1174) := temp_inp : fp2_t in
    #import {sig #[ FP2ADD ] : fp2add_inp → fp2add_out } as fp2add ;;
    let fp2add := fun x_0 x_1 => fp2add (x_0,x_1) in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP2NEG ] : fp2neg_inp → fp2neg_out } as fp2neg ;;
    let fp2neg := fun x_0 => fp2neg (x_0) in
    ({ code  '(b_1181 : (fp_t '× fp_t)) ←
        ( '(temp_1176 : fp2_t) ←
            (fp2neg (a_1174)) ;;
          ret (temp_1176)) ;;
       '(temp_1178 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_1180 : fp2_t) ←
        (fp2fromfp (temp_1178)) ;;
       '(temp_1183 : fp2_t) ←
        (fp2add (a_1174) (b_1181)) ;;
       '(temp_1185 : bool_ChoiceEquality) ←
        ((temp_1180) =.? (temp_1183)) ;;
      @ret (bool_ChoiceEquality) (temp_1185) } : code (fset.fset0) [interface
      #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_test_fp2_prop_add_neg : package _ _ _ :=
  (seq_link test_fp2_prop_add_neg link_rest(
      package_fp2add,package_fp2fromfp,package_fp2neg)).
Fail Next Obligation.


Notation "'test_fp2_prop_mul_inv_inp'" := (
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'test_fp2_prop_mul_inv_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition TEST_FP2_PROP_MUL_INV : nat :=
  (1199).
Program Definition test_fp2_prop_mul_inv
   : package (fset.fset0) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] [interface
  #val #[ TEST_FP2_PROP_MUL_INV ] : test_fp2_prop_mul_inv_inp → test_fp2_prop_mul_inv_out
  ] :=
  (
    [package #def #[ TEST_FP2_PROP_MUL_INV ] (temp_inp : test_fp2_prop_mul_inv_inp) : test_fp2_prop_mul_inv_out { 
    let '(a_1187) := temp_inp : fp2_t in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP2INV ] : fp2inv_inp → fp2inv_out } as fp2inv ;;
    let fp2inv := fun x_0 => fp2inv (x_0) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    ({ code  '(b_1194 : (fp_t '× fp_t)) ←
        ( '(temp_1189 : fp2_t) ←
            (fp2inv (a_1187)) ;;
          ret (temp_1189)) ;;
       '(temp_1191 : fp_t) ←
        (nat_mod_one ) ;;
       '(temp_1193 : fp2_t) ←
        (fp2fromfp (temp_1191)) ;;
       '(temp_1196 : fp2_t) ←
        (fp2mul (a_1187) (b_1194)) ;;
       '(temp_1198 : bool_ChoiceEquality) ←
        ((temp_1193) =.? (temp_1196)) ;;
      @ret (bool_ChoiceEquality) (temp_1198) } : code (fset.fset0) [interface
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_test_fp2_prop_mul_inv : package _ _ _ :=
  (seq_link test_fp2_prop_mul_inv link_rest(
      package_fp2fromfp,package_fp2inv,package_fp2mul)).
Fail Next Obligation.


Notation "'test_extraction_issue_inp'" := (
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'test_extraction_issue_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition TEST_EXTRACTION_ISSUE : nat :=
  (1219).
Program Definition test_extraction_issue
   : package (fset.fset0) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] [interface
  #val #[ TEST_EXTRACTION_ISSUE ] : test_extraction_issue_inp → test_extraction_issue_out
  ] :=
  (
    [package #def #[ TEST_EXTRACTION_ISSUE ] (temp_inp : test_extraction_issue_inp) : test_extraction_issue_out { 
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP2INV ] : fp2inv_inp → fp2inv_out } as fp2inv ;;
    let fp2inv := fun x_0 => fp2inv (x_0) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    ({ code  '(b_1214 : (fp_t '× fp_t)) ←
        ( '(temp_1201 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_1203 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_1205 : fp2_t) ←
            (fp2inv (prod_ce(temp_1201, temp_1203))) ;;
          ret (temp_1205)) ;;
       '(temp_1207 : fp_t) ←
        (nat_mod_one ) ;;
       '(temp_1209 : fp2_t) ←
        (fp2fromfp (temp_1207)) ;;
       '(temp_1211 : fp_t) ←
        (nat_mod_one ) ;;
       '(temp_1213 : fp_t) ←
        (nat_mod_one ) ;;
       '(temp_1216 : fp2_t) ←
        (fp2mul (prod_ce(temp_1211, temp_1213)) (b_1214)) ;;
       '(temp_1218 : bool_ChoiceEquality) ←
        ((temp_1209) =.? (temp_1216)) ;;
      @ret (bool_ChoiceEquality) (temp_1218) } : code (fset.fset0) [interface
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_test_extraction_issue : package _ _ _ :=
  (seq_link test_extraction_issue link_rest(
      package_fp2fromfp,package_fp2inv,package_fp2mul)).
Fail Next Obligation.


Notation "'test_fp6_prop_mul_inv_inp'" := (
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'test_fp6_prop_mul_inv_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition TEST_FP6_PROP_MUL_INV : nat :=
  (1234).
Program Definition test_fp6_prop_mul_inv
   : package (fset.fset0) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ;
  #val #[ FP6INV ] : fp6inv_inp → fp6inv_out ;
  #val #[ FP6MUL ] : fp6mul_inp → fp6mul_out ] [interface
  #val #[ TEST_FP6_PROP_MUL_INV ] : test_fp6_prop_mul_inv_inp → test_fp6_prop_mul_inv_out
  ] :=
  (
    [package #def #[ TEST_FP6_PROP_MUL_INV ] (temp_inp : test_fp6_prop_mul_inv_inp) : test_fp6_prop_mul_inv_out { 
    let '(a_1220) := temp_inp : fp6_t in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out } as fp6fromfp2 ;;
    let fp6fromfp2 := fun x_0 => fp6fromfp2 (x_0) in
    #import {sig #[ FP6INV ] : fp6inv_inp → fp6inv_out } as fp6inv ;;
    let fp6inv := fun x_0 => fp6inv (x_0) in
    #import {sig #[ FP6MUL ] : fp6mul_inp → fp6mul_out } as fp6mul ;;
    let fp6mul := fun x_0 x_1 => fp6mul (x_0,x_1) in
    ({ code  '(b_1229 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_1222 : fp6_t) ←
            (fp6inv (a_1220)) ;;
          ret (temp_1222)) ;;
       '(temp_1224 : fp_t) ←
        (nat_mod_one ) ;;
       '(temp_1226 : fp2_t) ←
        (fp2fromfp (temp_1224)) ;;
       '(temp_1228 : fp6_t) ←
        (fp6fromfp2 (temp_1226)) ;;
       '(temp_1231 : fp6_t) ←
        (fp6mul (a_1220) (b_1229)) ;;
       '(temp_1233 : bool_ChoiceEquality) ←
        ((temp_1228) =.? (temp_1231)) ;;
      @ret (bool_ChoiceEquality) (temp_1233) } : code (fset.fset0) [interface
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ;
      #val #[ FP6INV ] : fp6inv_inp → fp6inv_out ;
      #val #[ FP6MUL ] : fp6mul_inp → fp6mul_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_test_fp6_prop_mul_inv : package _ _ _ :=
  (seq_link test_fp6_prop_mul_inv link_rest(
      package_fp2fromfp,package_fp6fromfp2,package_fp6inv,package_fp6mul)).
Fail Next Obligation.


Notation "'test_fp6_prop_add_neg_inp'" := (
  fp6_t : choice_type) (in custom pack_type at level 2).
Notation "'test_fp6_prop_add_neg_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition TEST_FP6_PROP_ADD_NEG : nat :=
  (1249).
Program Definition test_fp6_prop_add_neg
   : package (fset.fset0) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP6ADD ] : fp6add_inp → fp6add_out ;
  #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ;
  #val #[ FP6NEG ] : fp6neg_inp → fp6neg_out ] [interface
  #val #[ TEST_FP6_PROP_ADD_NEG ] : test_fp6_prop_add_neg_inp → test_fp6_prop_add_neg_out
  ] :=
  (
    [package #def #[ TEST_FP6_PROP_ADD_NEG ] (temp_inp : test_fp6_prop_add_neg_inp) : test_fp6_prop_add_neg_out { 
    let '(a_1235) := temp_inp : fp6_t in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP6ADD ] : fp6add_inp → fp6add_out } as fp6add ;;
    let fp6add := fun x_0 x_1 => fp6add (x_0,x_1) in
    #import {sig #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out } as fp6fromfp2 ;;
    let fp6fromfp2 := fun x_0 => fp6fromfp2 (x_0) in
    #import {sig #[ FP6NEG ] : fp6neg_inp → fp6neg_out } as fp6neg ;;
    let fp6neg := fun x_0 => fp6neg (x_0) in
    ({ code  '(b_1244 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_1237 : fp6_t) ←
            (fp6neg (a_1235)) ;;
          ret (temp_1237)) ;;
       '(temp_1239 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_1241 : fp2_t) ←
        (fp2fromfp (temp_1239)) ;;
       '(temp_1243 : fp6_t) ←
        (fp6fromfp2 (temp_1241)) ;;
       '(temp_1246 : fp6_t) ←
        (fp6add (a_1235) (b_1244)) ;;
       '(temp_1248 : bool_ChoiceEquality) ←
        ((temp_1243) =.? (temp_1246)) ;;
      @ret (bool_ChoiceEquality) (temp_1248) } : code (fset.fset0) [interface
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP6ADD ] : fp6add_inp → fp6add_out ;
      #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ;
      #val #[ FP6NEG ] : fp6neg_inp → fp6neg_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_test_fp6_prop_add_neg : package _ _ _ :=
  (seq_link test_fp6_prop_add_neg link_rest(
      package_fp2fromfp,package_fp6add,package_fp6fromfp2,package_fp6neg)).
Fail Next Obligation.


Notation "'test_fp12_prop_add_neg_inp'" := (
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'test_fp12_prop_add_neg_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition TEST_FP12_PROP_ADD_NEG : nat :=
  (1266).
Program Definition test_fp12_prop_add_neg
   : package (fset.fset0) [interface
  #val #[ FP12ADD ] : fp12add_inp → fp12add_out ;
  #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
  #val #[ FP12NEG ] : fp12neg_inp → fp12neg_out ;
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ] [interface
  #val #[ TEST_FP12_PROP_ADD_NEG ] : test_fp12_prop_add_neg_inp → test_fp12_prop_add_neg_out
  ] :=
  (
    [package #def #[ TEST_FP12_PROP_ADD_NEG ] (temp_inp : test_fp12_prop_add_neg_inp) : test_fp12_prop_add_neg_out { 
    let '(a_1250) := temp_inp : fp12_t in
    #import {sig #[ FP12ADD ] : fp12add_inp → fp12add_out } as fp12add ;;
    let fp12add := fun x_0 x_1 => fp12add (x_0,x_1) in
    #import {sig #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out } as fp12fromfp6 ;;
    let fp12fromfp6 := fun x_0 => fp12fromfp6 (x_0) in
    #import {sig #[ FP12NEG ] : fp12neg_inp → fp12neg_out } as fp12neg ;;
    let fp12neg := fun x_0 => fp12neg (x_0) in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out } as fp6fromfp2 ;;
    let fp6fromfp2 := fun x_0 => fp6fromfp2 (x_0) in
    ({ code  '(b_1261 : (fp6_t '× fp6_t)) ←
        ( '(temp_1252 : fp12_t) ←
            (fp12neg (a_1250)) ;;
          ret (temp_1252)) ;;
       '(temp_1254 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_1256 : fp2_t) ←
        (fp2fromfp (temp_1254)) ;;
       '(temp_1258 : fp6_t) ←
        (fp6fromfp2 (temp_1256)) ;;
       '(temp_1260 : fp12_t) ←
        (fp12fromfp6 (temp_1258)) ;;
       '(temp_1263 : fp12_t) ←
        (fp12add (a_1250) (b_1261)) ;;
       '(temp_1265 : bool_ChoiceEquality) ←
        ((temp_1260) =.? (temp_1263)) ;;
      @ret (bool_ChoiceEquality) (temp_1265) } : code (fset.fset0) [interface
      #val #[ FP12ADD ] : fp12add_inp → fp12add_out ;
      #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
      #val #[ FP12NEG ] : fp12neg_inp → fp12neg_out ;
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_test_fp12_prop_add_neg : package _ _ _ :=
  (seq_link test_fp12_prop_add_neg link_rest(
      package_fp12add,package_fp12fromfp6,package_fp12neg,package_fp2fromfp,package_fp6fromfp2)).
Fail Next Obligation.


Notation "'test_fp12_prop_mul_inv_inp'" := (
  fp12_t : choice_type) (in custom pack_type at level 2).
Notation "'test_fp12_prop_mul_inv_out'" := (
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition TEST_FP12_PROP_MUL_INV : nat :=
  (1283).
Program Definition test_fp12_prop_mul_inv
   : package (fset.fset0) [interface
  #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
  #val #[ FP12INV ] : fp12inv_inp → fp12inv_out ;
  #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ] [interface
  #val #[ TEST_FP12_PROP_MUL_INV ] : test_fp12_prop_mul_inv_inp → test_fp12_prop_mul_inv_out
  ] :=
  (
    [package #def #[ TEST_FP12_PROP_MUL_INV ] (temp_inp : test_fp12_prop_mul_inv_inp) : test_fp12_prop_mul_inv_out { 
    let '(a_1267) := temp_inp : fp12_t in
    #import {sig #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out } as fp12fromfp6 ;;
    let fp12fromfp6 := fun x_0 => fp12fromfp6 (x_0) in
    #import {sig #[ FP12INV ] : fp12inv_inp → fp12inv_out } as fp12inv ;;
    let fp12inv := fun x_0 => fp12inv (x_0) in
    #import {sig #[ FP12MUL ] : fp12mul_inp → fp12mul_out } as fp12mul ;;
    let fp12mul := fun x_0 x_1 => fp12mul (x_0,x_1) in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out } as fp6fromfp2 ;;
    let fp6fromfp2 := fun x_0 => fp6fromfp2 (x_0) in
    ({ code  '(b_1278 : (fp6_t '× fp6_t)) ←
        ( '(temp_1269 : fp12_t) ←
            (fp12inv (a_1267)) ;;
          ret (temp_1269)) ;;
       '(temp_1271 : fp_t) ←
        (nat_mod_one ) ;;
       '(temp_1273 : fp2_t) ←
        (fp2fromfp (temp_1271)) ;;
       '(temp_1275 : fp6_t) ←
        (fp6fromfp2 (temp_1273)) ;;
       '(temp_1277 : fp12_t) ←
        (fp12fromfp6 (temp_1275)) ;;
       '(temp_1280 : fp12_t) ←
        (fp12mul (a_1267) (b_1278)) ;;
       '(temp_1282 : bool_ChoiceEquality) ←
        ((temp_1277) =.? (temp_1280)) ;;
      @ret (bool_ChoiceEquality) (temp_1282) } : code (fset.fset0) [interface
      #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
      #val #[ FP12INV ] : fp12inv_inp → fp12inv_out ;
      #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_test_fp12_prop_mul_inv : package _ _ _ :=
  (seq_link test_fp12_prop_mul_inv link_rest(
      package_fp12fromfp6,package_fp12inv,package_fp12mul,package_fp2fromfp,package_fp6fromfp2)).
Fail Next Obligation.

