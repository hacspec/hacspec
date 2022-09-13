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
  (7462).
Program Definition fp2fromfp
   : package (fset.fset0) [interface] [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ] :=
  ([package #def #[ FP2FROMFP ] (temp_inp : fp2fromfp_inp) : fp2fromfp_out { 
    let '(n_7459) := temp_inp : fp_t in
    ({ code  '(temp_7461 : fp_t) ←
        (nat_mod_zero ) ;;
      @ret ((fp_t '× fp_t)) (prod_ce(n_7459, temp_7461)) } : code (
        fset.fset0) [interface] _)
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
  (7467).
Program Definition fp2zero
   : package (fset.fset0) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ] [interface
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ] :=
  ([package #def #[ FP2ZERO ] (temp_inp : fp2zero_inp) : fp2zero_out { 
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    ({ code  '(temp_7464 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_7466 : fp2_t) ←
        (fp2fromfp (temp_7464)) ;;
      @ret (fp2_t) (temp_7466) } : code (fset.fset0) [interface
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
  (7481).
Program Definition fp2neg
   : package (fset.fset0) [interface] [interface
  #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ] :=
  ([package #def #[ FP2NEG ] (temp_inp : fp2neg_inp) : fp2neg_out { 
    let '(n_7468) := temp_inp : fp2_t in
    ({ code  temp_7480 ←
        (ret (n_7468)) ;;
      let '(n1_7471, n2_7476) :=
        (temp_7480) : (fp_t '× fp_t) in
       '(temp_7470 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_7473 : fp_t) ←
        ((temp_7470) -% (n1_7471)) ;;
       '(temp_7475 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_7478 : fp_t) ←
        ((temp_7475) -% (n2_7476)) ;;
      @ret ((fp_t '× fp_t)) (prod_ce(temp_7473, temp_7478)) } : code (
        fset.fset0) [interface] _)
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
  (7496).
Program Definition fp2add
   : package (fset.fset0) [interface] [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ] :=
  ([package #def #[ FP2ADD ] (temp_inp : fp2add_inp) : fp2add_out { 
    let '(n_7482 , m_7483) := temp_inp : fp2_t '× fp2_t in
    ({ code  temp_7495 ←
        (ret (n_7482)) ;;
      let '(n1_7484, n2_7488) :=
        (temp_7495) : (fp_t '× fp_t) in
       temp_7493 ←
        (ret (m_7483)) ;;
      let '(m1_7485, m2_7489) :=
        (temp_7493) : (fp_t '× fp_t) in
       '(temp_7487 : fp_t) ←
        ((n1_7484) +% (m1_7485)) ;;
       '(temp_7491 : fp_t) ←
        ((n2_7488) +% (m2_7489)) ;;
      @ret ((fp_t '× fp_t)) (prod_ce(temp_7487, temp_7491)) } : code (
        fset.fset0) [interface] _)
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
  (7503).
Program Definition fp2sub
   : package (fset.fset0) [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
  #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ] [interface
  #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ] :=
  ([package #def #[ FP2SUB ] (temp_inp : fp2sub_inp) : fp2sub_out { 
    let '(n_7497 , m_7498) := temp_inp : fp2_t '× fp2_t in
    #import {sig #[ FP2ADD ] : fp2add_inp → fp2add_out } as fp2add ;;
    let fp2add := fun x_0 x_1 => fp2add (x_0,x_1) in
    #import {sig #[ FP2NEG ] : fp2neg_inp → fp2neg_out } as fp2neg ;;
    let fp2neg := fun x_0 => fp2neg (x_0) in
    ({ code  '(temp_7500 : fp2_t) ←
        (fp2neg (m_7498)) ;;
       '(temp_7502 : fp2_t) ←
        (fp2add (n_7497) (temp_7500)) ;;
      @ret (fp2_t) (temp_7502) } : code (fset.fset0) [interface
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
  (7528).
Program Definition fp2mul
   : package (fset.fset0) [interface] [interface
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] :=
  ([package #def #[ FP2MUL ] (temp_inp : fp2mul_inp) : fp2mul_out { 
    let '(n_7504 , m_7505) := temp_inp : fp2_t '× fp2_t in
    ({ code  temp_7527 ←
        (ret (n_7504)) ;;
      let '(n1_7506, n2_7510) :=
        (temp_7527) : (fp_t '× fp_t) in
       temp_7525 ←
        (ret (m_7505)) ;;
      let '(m1_7507, m2_7511) :=
        (temp_7525) : (fp_t '× fp_t) in
       '(x1_7522 : fp_t) ←
        ( '(temp_7509 : fp_t) ←
            ((n1_7506) *% (m1_7507)) ;;
           '(temp_7513 : fp_t) ←
            ((n2_7510) *% (m2_7511)) ;;
           '(temp_7515 : fp_t) ←
            ((temp_7509) -% (temp_7513)) ;;
          ret (temp_7515)) ;;
       '(x2_7523 : fp_t) ←
        ( '(temp_7517 : fp_t) ←
            ((n1_7506) *% (m2_7511)) ;;
           '(temp_7519 : fp_t) ←
            ((n2_7510) *% (m1_7507)) ;;
           '(temp_7521 : fp_t) ←
            ((temp_7517) +% (temp_7519)) ;;
          ret (temp_7521)) ;;
      @ret ((fp_t '× fp_t)) (prod_ce(x1_7522, x2_7523)) } : code (
        fset.fset0) [interface] _)
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
  (7554).
Program Definition fp2inv
   : package (fset.fset0) [interface] [interface
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ] :=
  ([package #def #[ FP2INV ] (temp_inp : fp2inv_inp) : fp2inv_out { 
    let '(n_7529) := temp_inp : fp2_t in
    ({ code  temp_7553 ←
        (ret (n_7529)) ;;
      let '(n1_7530, n2_7533) :=
        (temp_7553) : (fp_t '× fp_t) in
       '(t0_7538 : fp_t) ←
        ( '(temp_7532 : fp_t) ←
            ((n1_7530) *% (n1_7530)) ;;
           '(temp_7535 : fp_t) ←
            ((n2_7533) *% (n2_7533)) ;;
           '(temp_7537 : fp_t) ←
            ((temp_7532) +% (temp_7535)) ;;
          ret (temp_7537)) ;;
       '(t1_7541 : fp_t) ←
        ( temp_7540 ←
            (nat_mod_inv (t0_7538)) ;;
          ret (temp_7540)) ;;
       '(x1_7550 : fp_t) ←
        ( '(temp_7543 : fp_t) ←
            ((n1_7530) *% (t1_7541)) ;;
          ret (temp_7543)) ;;
       '(x2_7551 : fp_t) ←
        ( '(temp_7545 : fp_t) ←
            (nat_mod_zero ) ;;
           '(temp_7547 : fp_t) ←
            ((n2_7533) *% (t1_7541)) ;;
           '(temp_7549 : fp_t) ←
            ((temp_7545) -% (temp_7547)) ;;
          ret (temp_7549)) ;;
      @ret ((fp_t '× fp_t)) (prod_ce(x1_7550, x2_7551)) } : code (
        fset.fset0) [interface] _)
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
  (7564).
Program Definition fp2conjugate
   : package (fset.fset0) [interface] [interface
  #val #[ FP2CONJUGATE ] : fp2conjugate_inp → fp2conjugate_out ] :=
  (
    [package #def #[ FP2CONJUGATE ] (temp_inp : fp2conjugate_inp) : fp2conjugate_out { 
    let '(n_7555) := temp_inp : fp2_t in
    ({ code  temp_7563 ←
        (ret (n_7555)) ;;
      let '(n1_7556, n2_7559) :=
        (temp_7563) : (fp_t '× fp_t) in
       '(temp_7558 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_7561 : fp_t) ←
        ((temp_7558) -% (n2_7559)) ;;
      @ret ((fp_t '× fp_t)) (prod_ce(n1_7556, temp_7561)) } : code (
        fset.fset0) [interface] _)
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
  (7570).
Program Definition fp6fromfp2
   : package (fset.fset0) [interface
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ] [interface
  #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ] :=
  ([package #def #[ FP6FROMFP2 ] (temp_inp : fp6fromfp2_inp) : fp6fromfp2_out { 
    let '(n_7565) := temp_inp : fp2_t in
    #import {sig #[ FP2ZERO ] : fp2zero_inp → fp2zero_out } as fp2zero ;;
    let fp2zero := fp2zero tt in
    ({ code  '(temp_7567 : fp2_t) ←
        (fp2zero ) ;;
       '(temp_7569 : fp2_t) ←
        (fp2zero ) ;;
      @ret ((fp2_t '× fp2_t '× fp2_t)) (prod_ce(n_7565, temp_7567, temp_7569
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
  (7575).
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
    ({ code  '(temp_7572 : fp2_t) ←
        (fp2zero ) ;;
       '(temp_7574 : fp6_t) ←
        (fp6fromfp2 (temp_7572)) ;;
      @ret (fp6_t) (temp_7574) } : code (fset.fset0) [interface
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
  (7594).
Program Definition fp6neg
   : package (fset.fset0) [interface
  #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ;
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ] [interface
  #val #[ FP6NEG ] : fp6neg_inp → fp6neg_out ] :=
  ([package #def #[ FP6NEG ] (temp_inp : fp6neg_inp) : fp6neg_out { 
    let '(n_7576) := temp_inp : fp6_t in
    #import {sig #[ FP2SUB ] : fp2sub_inp → fp2sub_out } as fp2sub ;;
    let fp2sub := fun x_0 x_1 => fp2sub (x_0,x_1) in
    #import {sig #[ FP2ZERO ] : fp2zero_inp → fp2zero_out } as fp2zero ;;
    let fp2zero := fp2zero tt in
    ({ code  temp_7593 ←
        (ret (n_7576)) ;;
      let '(n1_7579, n2_7584, n3_7589) :=
        (temp_7593) : (fp2_t '× fp2_t '× fp2_t) in
       '(temp_7578 : fp2_t) ←
        (fp2zero ) ;;
       '(temp_7581 : fp2_t) ←
        (fp2sub (temp_7578) (n1_7579)) ;;
       '(temp_7583 : fp2_t) ←
        (fp2zero ) ;;
       '(temp_7586 : fp2_t) ←
        (fp2sub (temp_7583) (n2_7584)) ;;
       '(temp_7588 : fp2_t) ←
        (fp2zero ) ;;
       '(temp_7591 : fp2_t) ←
        (fp2sub (temp_7588) (n3_7589)) ;;
      @ret ((fp2_t '× fp2_t '× fp2_t)) (prod_ce(
          temp_7581,
          temp_7586,
          temp_7591
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
  (7613).
Program Definition fp6add
   : package (fset.fset0) [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ] [interface
  #val #[ FP6ADD ] : fp6add_inp → fp6add_out ] :=
  ([package #def #[ FP6ADD ] (temp_inp : fp6add_inp) : fp6add_out { 
    let '(n_7595 , m_7596) := temp_inp : fp6_t '× fp6_t in
    #import {sig #[ FP2ADD ] : fp2add_inp → fp2add_out } as fp2add ;;
    let fp2add := fun x_0 x_1 => fp2add (x_0,x_1) in
    ({ code  temp_7612 ←
        (ret (n_7595)) ;;
      let '(n1_7597, n2_7601, n3_7605) :=
        (temp_7612) : (fp2_t '× fp2_t '× fp2_t) in
       temp_7610 ←
        (ret (m_7596)) ;;
      let '(m1_7598, m2_7602, m3_7606) :=
        (temp_7610) : (fp2_t '× fp2_t '× fp2_t) in
       '(temp_7600 : fp2_t) ←
        (fp2add (n1_7597) (m1_7598)) ;;
       '(temp_7604 : fp2_t) ←
        (fp2add (n2_7601) (m2_7602)) ;;
       '(temp_7608 : fp2_t) ←
        (fp2add (n3_7605) (m3_7606)) ;;
      @ret ((fp2_t '× fp2_t '× fp2_t)) (prod_ce(
          temp_7600,
          temp_7604,
          temp_7608
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
  (7620).
Program Definition fp6sub
   : package (fset.fset0) [interface
  #val #[ FP6ADD ] : fp6add_inp → fp6add_out ;
  #val #[ FP6NEG ] : fp6neg_inp → fp6neg_out ] [interface
  #val #[ FP6SUB ] : fp6sub_inp → fp6sub_out ] :=
  ([package #def #[ FP6SUB ] (temp_inp : fp6sub_inp) : fp6sub_out { 
    let '(n_7614 , m_7615) := temp_inp : fp6_t '× fp6_t in
    #import {sig #[ FP6ADD ] : fp6add_inp → fp6add_out } as fp6add ;;
    let fp6add := fun x_0 x_1 => fp6add (x_0,x_1) in
    #import {sig #[ FP6NEG ] : fp6neg_inp → fp6neg_out } as fp6neg ;;
    let fp6neg := fun x_0 => fp6neg (x_0) in
    ({ code  '(temp_7617 : fp6_t) ←
        (fp6neg (m_7615)) ;;
       '(temp_7619 : fp6_t) ←
        (fp6add (n_7614) (temp_7617)) ;;
      @ret (fp6_t) (temp_7619) } : code (fset.fset0) [interface
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
  (7696).
Program Definition fp6mul
   : package (fset.fset0) [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
  #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ] [interface
  #val #[ FP6MUL ] : fp6mul_inp → fp6mul_out ] :=
  ([package #def #[ FP6MUL ] (temp_inp : fp6mul_inp) : fp6mul_out { 
    let '(n_7621 , m_7622) := temp_inp : fp6_t '× fp6_t in
    #import {sig #[ FP2ADD ] : fp2add_inp → fp2add_out } as fp2add ;;
    let fp2add := fun x_0 x_1 => fp2add (x_0,x_1) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    #import {sig #[ FP2SUB ] : fp2sub_inp → fp2sub_out } as fp2sub ;;
    let fp2sub := fun x_0 x_1 => fp2sub (x_0,x_1) in
    ({ code  temp_7695 ←
        (ret (n_7621)) ;;
      let '(n1_7627, n2_7631, n3_7635) :=
        (temp_7695) : (fp2_t '× fp2_t '× fp2_t) in
       temp_7693 ←
        (ret (m_7622)) ;;
      let '(m1_7628, m2_7632, m3_7636) :=
        (temp_7693) : (fp2_t '× fp2_t '× fp2_t) in
       '(eps_7653 : (fp_t '× fp_t)) ←
        ( '(temp_7624 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_7626 : fp_t) ←
            (nat_mod_one ) ;;
          ret (prod_ce(temp_7624, temp_7626))) ;;
       '(t1_7656 : (fp_t '× fp_t)) ←
        ( '(temp_7630 : fp2_t) ←
            (fp2mul (n1_7627) (m1_7628)) ;;
          ret (temp_7630)) ;;
       '(t2_7646 : (fp_t '× fp_t)) ←
        ( '(temp_7634 : fp2_t) ←
            (fp2mul (n2_7631) (m2_7632)) ;;
          ret (temp_7634)) ;;
       '(t3_7649 : (fp_t '× fp_t)) ←
        ( '(temp_7638 : fp2_t) ←
            (fp2mul (n3_7635) (m3_7636)) ;;
          ret (temp_7638)) ;;
       '(t4_7645 : (fp_t '× fp_t)) ←
        ( '(temp_7640 : fp2_t) ←
            (fp2add (n2_7631) (n3_7635)) ;;
           '(temp_7642 : fp2_t) ←
            (fp2add (m2_7632) (m3_7636)) ;;
           '(temp_7644 : fp2_t) ←
            (fp2mul (temp_7640) (temp_7642)) ;;
          ret (temp_7644)) ;;
       '(t5_7652 : (fp_t '× fp_t)) ←
        ( '(temp_7648 : fp2_t) ←
            (fp2sub (t4_7645) (t2_7646)) ;;
           '(temp_7651 : fp2_t) ←
            (fp2sub (temp_7648) (t3_7649)) ;;
          ret (temp_7651)) ;;
       '(x_7689 : (fp_t '× fp_t)) ←
        ( '(temp_7655 : fp2_t) ←
            (fp2mul (t5_7652) (eps_7653)) ;;
           '(temp_7658 : fp2_t) ←
            (fp2add (temp_7655) (t1_7656)) ;;
          ret (temp_7658)) ;;
       '(t4_7665 : (fp_t '× fp_t)) ←
        ( '(temp_7660 : fp2_t) ←
            (fp2add (n1_7627) (n2_7631)) ;;
           '(temp_7662 : fp2_t) ←
            (fp2add (m1_7628) (m2_7632)) ;;
           '(temp_7664 : fp2_t) ←
            (fp2mul (temp_7660) (temp_7662)) ;;
          ret (temp_7664)) ;;
       '(t5_7670 : (fp_t '× fp_t)) ←
        ( '(temp_7667 : fp2_t) ←
            (fp2sub (t4_7665) (t1_7656)) ;;
           '(temp_7669 : fp2_t) ←
            (fp2sub (temp_7667) (t2_7646)) ;;
          ret (temp_7669)) ;;
       '(y_7690 : (fp_t '× fp_t)) ←
        ( '(temp_7672 : fp2_t) ←
            (fp2mul (eps_7653) (t3_7649)) ;;
           '(temp_7674 : fp2_t) ←
            (fp2add (t5_7670) (temp_7672)) ;;
          ret (temp_7674)) ;;
       '(t4_7681 : (fp_t '× fp_t)) ←
        ( '(temp_7676 : fp2_t) ←
            (fp2add (n1_7627) (n3_7635)) ;;
           '(temp_7678 : fp2_t) ←
            (fp2add (m1_7628) (m3_7636)) ;;
           '(temp_7680 : fp2_t) ←
            (fp2mul (temp_7676) (temp_7678)) ;;
          ret (temp_7680)) ;;
       '(t5_7686 : (fp_t '× fp_t)) ←
        ( '(temp_7683 : fp2_t) ←
            (fp2sub (t4_7681) (t1_7656)) ;;
           '(temp_7685 : fp2_t) ←
            (fp2sub (temp_7683) (t3_7649)) ;;
          ret (temp_7685)) ;;
       '(z_7691 : (fp_t '× fp_t)) ←
        ( '(temp_7688 : fp2_t) ←
            (fp2add (t5_7686) (t2_7646)) ;;
          ret (temp_7688)) ;;
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× (fp_t '× fp_t))) (prod_ce(
          x_7689,
          y_7690,
          z_7691
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
  (7768).
Program Definition fp6inv
   : package (fset.fset0) [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
  #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ] [interface
  #val #[ FP6INV ] : fp6inv_inp → fp6inv_out ] :=
  ([package #def #[ FP6INV ] (temp_inp : fp6inv_inp) : fp6inv_out { 
    let '(n_7697) := temp_inp : fp6_t in
    #import {sig #[ FP2ADD ] : fp2add_inp → fp2add_out } as fp2add ;;
    let fp2add := fun x_0 x_1 => fp2add (x_0,x_1) in
    #import {sig #[ FP2INV ] : fp2inv_inp → fp2inv_out } as fp2inv ;;
    let fp2inv := fun x_0 => fp2inv (x_0) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    #import {sig #[ FP2SUB ] : fp2sub_inp → fp2sub_out } as fp2sub ;;
    let fp2sub := fun x_0 x_1 => fp2sub (x_0,x_1) in
    ({ code  temp_7767 ←
        (ret (n_7697)) ;;
      let '(n1_7702, n2_7705, n3_7708) :=
        (temp_7767) : (fp2_t '× fp2_t '× fp2_t) in
       '(eps_7718 : (fp_t '× fp_t)) ←
        ( '(temp_7699 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_7701 : fp_t) ←
            (nat_mod_one ) ;;
          ret (prod_ce(temp_7699, temp_7701))) ;;
       '(t1_7717 : (fp_t '× fp_t)) ←
        ( '(temp_7704 : fp2_t) ←
            (fp2mul (n1_7702) (n1_7702)) ;;
          ret (temp_7704)) ;;
       '(t2_7730 : (fp_t '× fp_t)) ←
        ( '(temp_7707 : fp2_t) ←
            (fp2mul (n2_7705) (n2_7705)) ;;
          ret (temp_7707)) ;;
       '(t3_7724 : (fp_t '× fp_t)) ←
        ( '(temp_7710 : fp2_t) ←
            (fp2mul (n3_7708) (n3_7708)) ;;
          ret (temp_7710)) ;;
       '(t4_7727 : (fp_t '× fp_t)) ←
        ( '(temp_7712 : fp2_t) ←
            (fp2mul (n1_7702) (n2_7705)) ;;
          ret (temp_7712)) ;;
       '(t5_7731 : (fp_t '× fp_t)) ←
        ( '(temp_7714 : fp2_t) ←
            (fp2mul (n1_7702) (n3_7708)) ;;
          ret (temp_7714)) ;;
       '(t6_7719 : (fp_t '× fp_t)) ←
        ( '(temp_7716 : fp2_t) ←
            (fp2mul (n2_7705) (n3_7708)) ;;
          ret (temp_7716)) ;;
       '(x0_7734 : (fp_t '× fp_t)) ←
        ( '(temp_7721 : fp2_t) ←
            (fp2mul (eps_7718) (t6_7719)) ;;
           '(temp_7723 : fp2_t) ←
            (fp2sub (t1_7717) (temp_7721)) ;;
          ret (temp_7723)) ;;
       '(y0_7738 : (fp_t '× fp_t)) ←
        ( '(temp_7726 : fp2_t) ←
            (fp2mul (eps_7718) (t3_7724)) ;;
           '(temp_7729 : fp2_t) ←
            (fp2sub (temp_7726) (t4_7727)) ;;
          ret (temp_7729)) ;;
       '(z0_7746 : (fp_t '× fp_t)) ←
        ( '(temp_7733 : fp2_t) ←
            (fp2sub (t2_7730) (t5_7731)) ;;
          ret (temp_7733)) ;;
       '(t0_7737 : (fp_t '× fp_t)) ←
        ( '(temp_7736 : fp2_t) ←
            (fp2mul (n1_7702) (x0_7734)) ;;
          ret (temp_7736)) ;;
       '(t0_7745 : (fp_t '× fp_t)) ←
        ( '(temp_7740 : fp2_t) ←
            (fp2mul (n3_7708) (y0_7738)) ;;
           '(temp_7742 : fp2_t) ←
            (fp2mul (eps_7718) (temp_7740)) ;;
           '(temp_7744 : fp2_t) ←
            (fp2add (t0_7737) (temp_7742)) ;;
          ret (temp_7744)) ;;
       '(t0_7753 : (fp_t '× fp_t)) ←
        ( '(temp_7748 : fp2_t) ←
            (fp2mul (n2_7705) (z0_7746)) ;;
           '(temp_7750 : fp2_t) ←
            (fp2mul (eps_7718) (temp_7748)) ;;
           '(temp_7752 : fp2_t) ←
            (fp2add (t0_7745) (temp_7750)) ;;
          ret (temp_7752)) ;;
       '(t0_7756 : (fp_t '× fp_t)) ←
        ( '(temp_7755 : fp2_t) ←
            (fp2inv (t0_7753)) ;;
          ret (temp_7755)) ;;
       '(x_7763 : (fp_t '× fp_t)) ←
        ( '(temp_7758 : fp2_t) ←
            (fp2mul (x0_7734) (t0_7756)) ;;
          ret (temp_7758)) ;;
       '(y_7764 : (fp_t '× fp_t)) ←
        ( '(temp_7760 : fp2_t) ←
            (fp2mul (y0_7738) (t0_7756)) ;;
          ret (temp_7760)) ;;
       '(z_7765 : (fp_t '× fp_t)) ←
        ( '(temp_7762 : fp2_t) ←
            (fp2mul (z0_7746) (t0_7756)) ;;
          ret (temp_7762)) ;;
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× (fp_t '× fp_t))) (prod_ce(
          x_7763,
          y_7764,
          z_7765
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
  (7772).
Program Definition fp12fromfp6
   : package (fset.fset0) [interface
  #val #[ FP6ZERO ] : fp6zero_inp → fp6zero_out ] [interface
  #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ] :=
  (
    [package #def #[ FP12FROMFP6 ] (temp_inp : fp12fromfp6_inp) : fp12fromfp6_out { 
    let '(n_7769) := temp_inp : fp6_t in
    #import {sig #[ FP6ZERO ] : fp6zero_inp → fp6zero_out } as fp6zero ;;
    let fp6zero := fp6zero tt in
    ({ code  '(temp_7771 : fp6_t) ←
        (fp6zero ) ;;
      @ret ((fp6_t '× fp6_t)) (prod_ce(n_7769, temp_7771)) } : code (
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
  (7786).
Program Definition fp12neg
   : package (fset.fset0) [interface
  #val #[ FP6SUB ] : fp6sub_inp → fp6sub_out ;
  #val #[ FP6ZERO ] : fp6zero_inp → fp6zero_out ] [interface
  #val #[ FP12NEG ] : fp12neg_inp → fp12neg_out ] :=
  ([package #def #[ FP12NEG ] (temp_inp : fp12neg_inp) : fp12neg_out { 
    let '(n_7773) := temp_inp : fp12_t in
    #import {sig #[ FP6SUB ] : fp6sub_inp → fp6sub_out } as fp6sub ;;
    let fp6sub := fun x_0 x_1 => fp6sub (x_0,x_1) in
    #import {sig #[ FP6ZERO ] : fp6zero_inp → fp6zero_out } as fp6zero ;;
    let fp6zero := fp6zero tt in
    ({ code  temp_7785 ←
        (ret (n_7773)) ;;
      let '(n1_7776, n2_7781) :=
        (temp_7785) : (fp6_t '× fp6_t) in
       '(temp_7775 : fp6_t) ←
        (fp6zero ) ;;
       '(temp_7778 : fp6_t) ←
        (fp6sub (temp_7775) (n1_7776)) ;;
       '(temp_7780 : fp6_t) ←
        (fp6zero ) ;;
       '(temp_7783 : fp6_t) ←
        (fp6sub (temp_7780) (n2_7781)) ;;
      @ret ((fp6_t '× fp6_t)) (prod_ce(temp_7778, temp_7783)) } : code (
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
  (7801).
Program Definition fp12add
   : package (fset.fset0) [interface
  #val #[ FP6ADD ] : fp6add_inp → fp6add_out ] [interface
  #val #[ FP12ADD ] : fp12add_inp → fp12add_out ] :=
  ([package #def #[ FP12ADD ] (temp_inp : fp12add_inp) : fp12add_out { 
    let '(n_7787 , m_7788) := temp_inp : fp12_t '× fp12_t in
    #import {sig #[ FP6ADD ] : fp6add_inp → fp6add_out } as fp6add ;;
    let fp6add := fun x_0 x_1 => fp6add (x_0,x_1) in
    ({ code  temp_7800 ←
        (ret (n_7787)) ;;
      let '(n1_7789, n2_7793) :=
        (temp_7800) : (fp6_t '× fp6_t) in
       temp_7798 ←
        (ret (m_7788)) ;;
      let '(m1_7790, m2_7794) :=
        (temp_7798) : (fp6_t '× fp6_t) in
       '(temp_7792 : fp6_t) ←
        (fp6add (n1_7789) (m1_7790)) ;;
       '(temp_7796 : fp6_t) ←
        (fp6add (n2_7793) (m2_7794)) ;;
      @ret ((fp6_t '× fp6_t)) (prod_ce(temp_7792, temp_7796)) } : code (
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
  (7808).
Program Definition fp12sub
   : package (fset.fset0) [interface
  #val #[ FP12ADD ] : fp12add_inp → fp12add_out ;
  #val #[ FP12NEG ] : fp12neg_inp → fp12neg_out ] [interface
  #val #[ FP12SUB ] : fp12sub_inp → fp12sub_out ] :=
  ([package #def #[ FP12SUB ] (temp_inp : fp12sub_inp) : fp12sub_out { 
    let '(n_7802 , m_7803) := temp_inp : fp12_t '× fp12_t in
    #import {sig #[ FP12ADD ] : fp12add_inp → fp12add_out } as fp12add ;;
    let fp12add := fun x_0 x_1 => fp12add (x_0,x_1) in
    #import {sig #[ FP12NEG ] : fp12neg_inp → fp12neg_out } as fp12neg ;;
    let fp12neg := fun x_0 => fp12neg (x_0) in
    ({ code  '(temp_7805 : fp12_t) ←
        (fp12neg (m_7803)) ;;
       '(temp_7807 : fp12_t) ←
        (fp12add (n_7802) (temp_7805)) ;;
      @ret (fp12_t) (temp_7807) } : code (fset.fset0) [interface
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
  (7851).
Program Definition fp12mul
   : package (fset.fset0) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
  #val #[ FP6ADD ] : fp6add_inp → fp6add_out ;
  #val #[ FP6MUL ] : fp6mul_inp → fp6mul_out ;
  #val #[ FP6SUB ] : fp6sub_inp → fp6sub_out ] [interface
  #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ] :=
  ([package #def #[ FP12MUL ] (temp_inp : fp12mul_inp) : fp12mul_out { 
    let '(n_7809 , m_7810) := temp_inp : fp12_t '× fp12_t in
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
    ({ code  temp_7850 ←
        (ret (n_7809)) ;;
      let '(n1_7819, n2_7823) :=
        (temp_7850) : (fp6_t '× fp6_t) in
       temp_7848 ←
        (ret (m_7810)) ;;
      let '(m1_7820, m2_7824) :=
        (temp_7848) : (fp6_t '× fp6_t) in
       '(gamma_7829 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_7812 : fp2_t) ←
            (fp2zero ) ;;
           '(temp_7814 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_7816 : fp2_t) ←
            (fp2fromfp (temp_7814)) ;;
           '(temp_7818 : fp2_t) ←
            (fp2zero ) ;;
          ret (prod_ce(temp_7812, temp_7816, temp_7818))) ;;
       '(t1_7827 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_7822 : fp6_t) ←
            (fp6mul (n1_7819) (m1_7820)) ;;
          ret (temp_7822)) ;;
       '(t2_7828 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_7826 : fp6_t) ←
            (fp6mul (n2_7823) (m2_7824)) ;;
          ret (temp_7826)) ;;
       '(x_7845 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_7831 : fp6_t) ←
            (fp6mul (t2_7828) (gamma_7829)) ;;
           '(temp_7833 : fp6_t) ←
            (fp6add (t1_7827) (temp_7831)) ;;
          ret (temp_7833)) ;;
       '(y_7840 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_7835 : fp6_t) ←
            (fp6add (n1_7819) (n2_7823)) ;;
           '(temp_7837 : fp6_t) ←
            (fp6add (m1_7820) (m2_7824)) ;;
           '(temp_7839 : fp6_t) ←
            (fp6mul (temp_7835) (temp_7837)) ;;
          ret (temp_7839)) ;;
       '(y_7846 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_7842 : fp6_t) ←
            (fp6sub (y_7840) (t1_7827)) ;;
           '(temp_7844 : fp6_t) ←
            (fp6sub (temp_7842) (t2_7828)) ;;
          ret (temp_7844)) ;;
      @ret (((fp2_t '× fp2_t '× fp2_t) '× (fp2_t '× fp2_t '× fp2_t))) (
        prod_ce(x_7845, y_7846)) } : code (fset.fset0) [interface
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
  (7888).
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
    let '(n_7852) := temp_inp : fp12_t in
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
    ({ code  temp_7887 ←
        (ret (n_7852)) ;;
      let '(n1_7861, n2_7864) :=
        (temp_7887) : (fp6_t '× fp6_t) in
       '(gamma_7868 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_7854 : fp2_t) ←
            (fp2zero ) ;;
           '(temp_7856 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_7858 : fp2_t) ←
            (fp2fromfp (temp_7856)) ;;
           '(temp_7860 : fp2_t) ←
            (fp2zero ) ;;
          ret (prod_ce(temp_7854, temp_7858, temp_7860))) ;;
       '(t1_7867 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_7863 : fp6_t) ←
            (fp6mul (n1_7861) (n1_7861)) ;;
          ret (temp_7863)) ;;
       '(t2_7869 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_7866 : fp6_t) ←
            (fp6mul (n2_7864) (n2_7864)) ;;
          ret (temp_7866)) ;;
       '(t1_7874 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_7871 : fp6_t) ←
            (fp6mul (gamma_7868) (t2_7869)) ;;
           '(temp_7873 : fp6_t) ←
            (fp6sub (t1_7867) (temp_7871)) ;;
          ret (temp_7873)) ;;
       '(t2_7877 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_7876 : fp6_t) ←
            (fp6inv (t1_7874)) ;;
          ret (temp_7876)) ;;
       '(x_7884 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_7879 : fp6_t) ←
            (fp6mul (n1_7861) (t2_7877)) ;;
          ret (temp_7879)) ;;
       '(y_7885 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_7881 : fp6_t) ←
            (fp6mul (n2_7864) (t2_7877)) ;;
           '(temp_7883 : fp6_t) ←
            (fp6neg (temp_7881)) ;;
          ret (temp_7883)) ;;
      @ret (((fp2_t '× fp2_t '× fp2_t) '× (fp2_t '× fp2_t '× fp2_t))) (
        prod_ce(x_7884, y_7885)) } : code (fset.fset0) [interface
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

Definition c_7897_loc : ChoiceEqualityLocation :=
  (((fp6_t '× fp6_t) ; 7909%nat)).
Notation "'fp12exp_inp'" := (
  fp12_t '× scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'fp12exp_out'" := (
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition FP12EXP : nat :=
  (7910).
Program Definition fp12exp
   : package (CEfset ([c_7897_loc])) [interface
  #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
  #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out ] [interface
  #val #[ FP12EXP ] : fp12exp_inp → fp12exp_out ] :=
  ([package #def #[ FP12EXP ] (temp_inp : fp12exp_inp) : fp12exp_out { 
    let '(n_7906 , k_7900) := temp_inp : fp12_t '× scalar_t in
    #import {sig #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out } as fp12fromfp6 ;;
    let fp12fromfp6 := fun x_0 => fp12fromfp6 (x_0) in
    #import {sig #[ FP12MUL ] : fp12mul_inp → fp12mul_out } as fp12mul ;;
    let fp12mul := fun x_0 x_1 => fp12mul (x_0,x_1) in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out } as fp6fromfp2 ;;
    let fp6fromfp2 := fun x_0 => fp6fromfp2 (x_0) in
    ({ code  '(c_7897 : (fp6_t '× fp6_t)) ←
          ( '(temp_7890 : fp_t) ←
              (nat_mod_one ) ;;
             '(temp_7892 : fp2_t) ←
              (fp2fromfp (temp_7890)) ;;
             '(temp_7894 : fp6_t) ←
              (fp6fromfp2 (temp_7892)) ;;
             '(temp_7896 : fp12_t) ←
              (fp12fromfp6 (temp_7894)) ;;
            ret (temp_7896)) ;;
        #put c_7897_loc := c_7897 ;;
       '(c_7897 : ((fp6_t '× fp6_t))) ←
        (foldi' (usize 0) (usize 256) c_7897 (L2 := CEfset ([c_7897_loc])) (
              I2 := [interface
              #val #[ FP12FROMFP6 ] : fp12fromfp6_inp → fp12fromfp6_out ;
              #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
              #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
              #val #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_7901 c_7897 =>
            ({ code  '(c_7897 : (fp6_t '× fp6_t)) ←
                  (( '(temp_7899 : fp12_t) ←
                        (fp12mul (c_7897) (c_7897)) ;;
                      ret (temp_7899))) ;;
                #put c_7897_loc := c_7897 ;;
              
               '(temp_7903 : uint_size) ←
                ((usize 255) .- (i_7901)) ;;
               temp_7905 ←
                (nat_mod_bit (k_7900) (temp_7903)) ;;
               '(c_7897 : ((fp6_t '× fp6_t))) ←
                (if temp_7905:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(c_7897 : (
                            fp6_t '×
                            fp6_t
                          )) ←
                        (( '(temp_7908 : fp12_t) ←
                              (fp12mul (c_7897) (n_7906)) ;;
                            ret (temp_7908))) ;;
                      #put c_7897_loc := c_7897 ;;
                    
                    @ret (((fp6_t '× fp6_t))) (c_7897) in
                    ({ code temp_then } : code (CEfset (
                          [c_7897_loc])) [interface
                      #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ] _))
                  else @ret (((fp6_t '× fp6_t))) (c_7897)) ;;
              
              @ret (((fp6_t '× fp6_t))) (c_7897) } : code (CEfset (
                  [c_7897_loc])) [interface
              #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ] _))) ;;
      
      @ret ((fp6_t '× fp6_t)) (c_7897) } : code (CEfset (
          [c_7897_loc])) [interface
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
  (7918).
Program Definition fp12conjugate
   : package (fset.fset0) [interface
  #val #[ FP6NEG ] : fp6neg_inp → fp6neg_out ] [interface
  #val #[ FP12CONJUGATE ] : fp12conjugate_inp → fp12conjugate_out ] :=
  (
    [package #def #[ FP12CONJUGATE ] (temp_inp : fp12conjugate_inp) : fp12conjugate_out { 
    let '(n_7911) := temp_inp : fp12_t in
    #import {sig #[ FP6NEG ] : fp6neg_inp → fp6neg_out } as fp6neg ;;
    let fp6neg := fun x_0 => fp6neg (x_0) in
    ({ code  temp_7917 ←
        (ret (n_7911)) ;;
      let '(n1_7912, n2_7913) :=
        (temp_7917) : (fp6_t '× fp6_t) in
       '(temp_7915 : fp6_t) ←
        (fp6neg (n2_7913)) ;;
      @ret (((fp2_t '× fp2_t '× fp2_t) '× fp6_t)) (prod_ce(n1_7912, temp_7915
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
  (7923).
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
    ({ code  '(temp_7920 : fp6_t) ←
        (fp6zero ) ;;
       '(temp_7922 : fp12_t) ←
        (fp12fromfp6 (temp_7920)) ;;
      @ret (fp12_t) (temp_7922) } : code (fset.fset0) [interface
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
  (7959).
Program Definition g1add_a
   : package (fset.fset0) [interface] [interface
  #val #[ G1ADD_A ] : g1add_a_inp → g1add_a_out ] :=
  ([package #def #[ G1ADD_A ] (temp_inp : g1add_a_inp) : g1add_a_out { 
    let '(p_7924 , q_7925) := temp_inp : g1_t '× g1_t in
    ({ code  temp_7958 ←
        (ret (p_7924)) ;;
      let '(x1_7927, y1_7931, _) :=
        (temp_7958) : (fp_t '× fp_t '× bool_ChoiceEquality) in
       temp_7956 ←
        (ret (q_7925)) ;;
      let '(x2_7926, y2_7930, _) :=
        (temp_7956) : (fp_t '× fp_t '× bool_ChoiceEquality) in
       '(x_diff_7935 : fp_t) ←
        ( '(temp_7929 : fp_t) ←
            ((x2_7926) -% (x1_7927)) ;;
          ret (temp_7929)) ;;
       '(y_diff_7934 : fp_t) ←
        ( '(temp_7933 : fp_t) ←
            ((y2_7930) -% (y1_7931)) ;;
          ret (temp_7933)) ;;
       '(xovery_7940 : fp_t) ←
        ( temp_7937 ←
            (nat_mod_inv (x_diff_7935)) ;;
           '(temp_7939 : fp_t) ←
            ((y_diff_7934) *% (temp_7937)) ;;
          ret (temp_7939)) ;;
       '(x3_7947 : fp_t) ←
        ( temp_7942 ←
            (nat_mod_exp (xovery_7940) (@repr U32 2)) ;;
           '(temp_7944 : fp_t) ←
            ((temp_7942) -% (x1_7927)) ;;
           '(temp_7946 : fp_t) ←
            ((temp_7944) -% (x2_7926)) ;;
          ret (temp_7946)) ;;
       '(y3_7954 : fp_t) ←
        ( '(temp_7949 : fp_t) ←
            ((x1_7927) -% (x3_7947)) ;;
           '(temp_7951 : fp_t) ←
            ((xovery_7940) *% (temp_7949)) ;;
           '(temp_7953 : fp_t) ←
            ((temp_7951) -% (y1_7931)) ;;
          ret (temp_7953)) ;;
      @ret ((fp_t '× fp_t '× bool_ChoiceEquality)) (prod_ce(
          x3_7947,
          y3_7954,
          (false : bool_ChoiceEquality)
        )) } : code (fset.fset0) [interface] _)
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
  (7997).
Program Definition g1double_a
   : package (fset.fset0) [interface] [interface
  #val #[ G1DOUBLE_A ] : g1double_a_inp → g1double_a_out ] :=
  ([package #def #[ G1DOUBLE_A ] (temp_inp : g1double_a_inp) : g1double_a_out { 
    let '(p_7960) := temp_inp : g1_t in
    ({ code  temp_7996 ←
        (ret (p_7960)) ;;
      let '(x1_7961, y1_7971, _) :=
        (temp_7996) : (fp_t '× fp_t '× bool_ChoiceEquality) in
       '(x12_7966 : fp_t) ←
        ( temp_7963 ←
            (nat_mod_exp (x1_7961) (@repr U32 2)) ;;
          ret (temp_7963)) ;;
       '(xovery_7978 : fp_t) ←
        ( '(temp_7965 : fp_t) ←
            (nat_mod_from_literal (
                0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
                @repr U128 3)) ;;
           '(temp_7968 : fp_t) ←
            ((temp_7965) *% (x12_7966)) ;;
           '(temp_7970 : fp_t) ←
            (nat_mod_two ) ;;
           '(temp_7973 : fp_t) ←
            ((temp_7970) *% (y1_7971)) ;;
           temp_7975 ←
            (nat_mod_inv (temp_7973)) ;;
           '(temp_7977 : fp_t) ←
            ((temp_7968) *% (temp_7975)) ;;
          ret (temp_7977)) ;;
       '(x3_7987 : fp_t) ←
        ( temp_7980 ←
            (nat_mod_exp (xovery_7978) (@repr U32 2)) ;;
           '(temp_7982 : fp_t) ←
            (nat_mod_two ) ;;
           '(temp_7984 : fp_t) ←
            ((temp_7982) *% (x1_7961)) ;;
           '(temp_7986 : fp_t) ←
            ((temp_7980) -% (temp_7984)) ;;
          ret (temp_7986)) ;;
       '(y3_7994 : fp_t) ←
        ( '(temp_7989 : fp_t) ←
            ((x1_7961) -% (x3_7987)) ;;
           '(temp_7991 : fp_t) ←
            ((xovery_7978) *% (temp_7989)) ;;
           '(temp_7993 : fp_t) ←
            ((temp_7991) -% (y1_7971)) ;;
          ret (temp_7993)) ;;
      @ret ((fp_t '× fp_t '× bool_ChoiceEquality)) (prod_ce(
          x3_7987,
          y3_7994,
          (false : bool_ChoiceEquality)
        )) } : code (fset.fset0) [interface] _)
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
  (8016).
Program Definition g1double
   : package (fset.fset0) [interface
  #val #[ G1DOUBLE_A ] : g1double_a_inp → g1double_a_out ] [interface
  #val #[ G1DOUBLE ] : g1double_inp → g1double_out ] :=
  ([package #def #[ G1DOUBLE ] (temp_inp : g1double_inp) : g1double_out { 
    let '(p_7998) := temp_inp : g1_t in
    #import {sig #[ G1DOUBLE_A ] : g1double_a_inp → g1double_a_out } as g1double_a ;;
    let g1double_a := fun x_0 => g1double_a (x_0) in
    ({ code  temp_8014 ←
        (ret (p_7998)) ;;
      let '(x1_8015, y1_7999, inf1_8004) :=
        (temp_8014) : (fp_t '× fp_t '× bool_ChoiceEquality) in
       '(temp_8001 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_8003 : bool_ChoiceEquality) ←
        ((y1_7999) !=.? (temp_8001)) ;;
       '(temp_8006 : bool_ChoiceEquality) ←
        ((temp_8003) && (negb (inf1_8004))) ;;
       '(temp_8008 : g1_t) ←
        (g1double_a (p_7998)) ;;
       '(temp_8010 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_8012 : fp_t) ←
        (nat_mod_zero ) ;;
      @ret (g1_t) ((if (temp_8006):bool_ChoiceEquality then (*inline*) (
            temp_8008) else (prod_ce(
              temp_8010,
              temp_8012,
              (true : bool_ChoiceEquality)
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
  (8049).
Program Definition g1add
   : package (fset.fset0) [interface
  #val #[ G1ADD_A ] : g1add_a_inp → g1add_a_out ;
  #val #[ G1DOUBLE ] : g1double_inp → g1double_out ] [interface
  #val #[ G1ADD ] : g1add_inp → g1add_out ] :=
  ([package #def #[ G1ADD ] (temp_inp : g1add_inp) : g1add_out { 
    let '(p_8017 , q_8018) := temp_inp : g1_t '× g1_t in
    #import {sig #[ G1ADD_A ] : g1add_a_inp → g1add_a_out } as g1add_a ;;
    let g1add_a := fun x_0 x_1 => g1add_a (x_0,x_1) in
    #import {sig #[ G1DOUBLE ] : g1double_inp → g1double_out } as g1double ;;
    let g1double := fun x_0 => g1double (x_0) in
    ({ code  temp_8048 ←
        (ret (p_8017)) ;;
      let '(x1_8025, y1_8029, inf1_8019) :=
        (temp_8048) : (fp_t '× fp_t '× bool_ChoiceEquality) in
       temp_8046 ←
        (ret (q_8018)) ;;
      let '(x2_8026, y2_8032, inf2_8020) :=
        (temp_8046) : (fp_t '× fp_t '× bool_ChoiceEquality) in
       '(temp_8022 : bool_ChoiceEquality) ←
        ((p_8017) =.? (q_8018)) ;;
       '(temp_8024 : g1_t) ←
        (g1double (p_8017)) ;;
       '(temp_8028 : bool_ChoiceEquality) ←
        ((x1_8025) =.? (x2_8026)) ;;
       '(temp_8031 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_8034 : fp_t) ←
        ((temp_8031) -% (y2_8032)) ;;
       '(temp_8036 : bool_ChoiceEquality) ←
        ((y1_8029) =.? (temp_8034)) ;;
       '(temp_8038 : bool_ChoiceEquality) ←
        ((temp_8028) && (temp_8036)) ;;
       '(temp_8040 : g1_t) ←
        (g1add_a (p_8017) (q_8018)) ;;
       '(temp_8042 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_8044 : fp_t) ←
        (nat_mod_zero ) ;;
      @ret (g1_t) ((if (inf1_8019):bool_ChoiceEquality then (*inline*) (
            q_8018) else ((if (inf2_8020):bool_ChoiceEquality then (*inline*) (
                p_8017) else ((if (
                    temp_8022):bool_ChoiceEquality then (*inline*) (
                    temp_8024) else ((if (negb (
                          temp_8038)):bool_ChoiceEquality then (*inline*) (
                        temp_8040) else (prod_ce(
                          temp_8042,
                          temp_8044,
                          (true : bool_ChoiceEquality)
                        )))))))))) } : code (fset.fset0) [interface
      #val #[ G1ADD_A ] : g1add_a_inp → g1add_a_out ;
      #val #[ G1DOUBLE ] : g1double_inp → g1double_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_g1add : package _ _ _ :=
  (seq_link g1add link_rest(package_g1add_a,package_g1double)).
Fail Next Obligation.

Definition t_8054_loc : ChoiceEqualityLocation :=
  (((fp_t '× fp_t '× bool_ChoiceEquality) ; 8066%nat)).
Notation "'g1mul_inp'" := (
  scalar_t '× g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1mul_out'" := (g1_t : choice_type) (in custom pack_type at level 2).
Definition G1MUL : nat :=
  (8067).
Program Definition g1mul
   : package (CEfset ([t_8054_loc])) [interface
  #val #[ G1ADD ] : g1add_inp → g1add_out ;
  #val #[ G1DOUBLE ] : g1double_inp → g1double_out ] [interface
  #val #[ G1MUL ] : g1mul_inp → g1mul_out ] :=
  ([package #def #[ G1MUL ] (temp_inp : g1mul_inp) : g1mul_out { 
    let '(m_8057 , p_8063) := temp_inp : scalar_t '× g1_t in
    #import {sig #[ G1ADD ] : g1add_inp → g1add_out } as g1add ;;
    let g1add := fun x_0 x_1 => g1add (x_0,x_1) in
    #import {sig #[ G1DOUBLE ] : g1double_inp → g1double_out } as g1double ;;
    let g1double := fun x_0 => g1double (x_0) in
    ({ code  '(t_8054 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
          ( '(temp_8051 : fp_t) ←
              (nat_mod_zero ) ;;
             '(temp_8053 : fp_t) ←
              (nat_mod_zero ) ;;
            ret (prod_ce(temp_8051, temp_8053, (true : bool_ChoiceEquality)
              ))) ;;
        #put t_8054_loc := t_8054 ;;
       '(t_8054 : ((fp_t '× fp_t '× bool_ChoiceEquality))) ←
        (foldi' (usize 0) (usize 256) t_8054 (L2 := CEfset ([t_8054_loc])) (
              I2 := [interface #val #[ G1ADD ] : g1add_inp → g1add_out ;
              #val #[ G1DOUBLE ] : g1double_inp → g1double_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_8058 t_8054 =>
            ({ code  '(t_8054 : (fp_t '× fp_t '× bool_ChoiceEquality)) ←
                  (( '(temp_8056 : g1_t) ←
                        (g1double (t_8054)) ;;
                      ret (temp_8056))) ;;
                #put t_8054_loc := t_8054 ;;
              
               '(temp_8060 : uint_size) ←
                ((usize 255) .- (i_8058)) ;;
               temp_8062 ←
                (nat_mod_bit (m_8057) (temp_8060)) ;;
               '(t_8054 : ((fp_t '× fp_t '× bool_ChoiceEquality))) ←
                (if temp_8062:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(t_8054 : (
                            fp_t '×
                            fp_t '×
                            bool_ChoiceEquality
                          )) ←
                        (( '(temp_8065 : g1_t) ←
                              (g1add (t_8054) (p_8063)) ;;
                            ret (temp_8065))) ;;
                      #put t_8054_loc := t_8054 ;;
                    
                    @ret (((fp_t '× fp_t '× bool_ChoiceEquality))) (t_8054) in
                    ({ code temp_then } : code (CEfset (
                          [t_8054_loc])) [interface
                      #val #[ G1ADD ] : g1add_inp → g1add_out ] _))
                  else @ret (((fp_t '× fp_t '× bool_ChoiceEquality))) (
                    t_8054)) ;;
              
              @ret (((fp_t '× fp_t '× bool_ChoiceEquality))) (
                t_8054) } : code (CEfset ([t_8054_loc])) [interface
              #val #[ G1ADD ] : g1add_inp → g1add_out ;
              #val #[ G1DOUBLE ] : g1double_inp → g1double_out ] _))) ;;
      
      @ret ((fp_t '× fp_t '× bool_ChoiceEquality)) (t_8054) } : code (CEfset (
          [t_8054_loc])) [interface #val #[ G1ADD ] : g1add_inp → g1add_out ;
      #val #[ G1DOUBLE ] : g1double_inp → g1double_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_g1mul : package _ _ _ :=
  (seq_link g1mul link_rest(package_g1add,package_g1double)).
Fail Next Obligation.


Notation "'g1neg_inp'" := (g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1neg_out'" := (g1_t : choice_type) (in custom pack_type at level 2).
Definition G1NEG : nat :=
  (8078).
Program Definition g1neg
   : package (fset.fset0) [interface] [interface
  #val #[ G1NEG ] : g1neg_inp → g1neg_out ] :=
  ([package #def #[ G1NEG ] (temp_inp : g1neg_inp) : g1neg_out { 
    let '(p_8068) := temp_inp : g1_t in
    ({ code  temp_8077 ←
        (ret (p_8068)) ;;
      let '(x_8069, y_8072, inf_8075) :=
        (temp_8077) : (fp_t '× fp_t '× bool_ChoiceEquality) in
       '(temp_8071 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_8074 : fp_t) ←
        ((temp_8071) -% (y_8072)) ;;
      @ret ((fp_t '× fp_t '× bool_ChoiceEquality)) (prod_ce(
          x_8069,
          temp_8074,
          inf_8075
        )) } : code (fset.fset0) [interface] _)
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
  (8118).
Program Definition g2add_a
   : package (fset.fset0) [interface
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
  #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ] [interface
  #val #[ G2ADD_A ] : g2add_a_inp → g2add_a_out ] :=
  ([package #def #[ G2ADD_A ] (temp_inp : g2add_a_inp) : g2add_a_out { 
    let '(p_8079 , q_8080) := temp_inp : g2_t '× g2_t in
    #import {sig #[ FP2INV ] : fp2inv_inp → fp2inv_out } as fp2inv ;;
    let fp2inv := fun x_0 => fp2inv (x_0) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    #import {sig #[ FP2SUB ] : fp2sub_inp → fp2sub_out } as fp2sub ;;
    let fp2sub := fun x_0 x_1 => fp2sub (x_0,x_1) in
    ({ code  temp_8117 ←
        (ret (p_8079)) ;;
      let '(x1_8082, y1_8086, _) :=
        (temp_8117) : (fp2_t '× fp2_t '× bool_ChoiceEquality) in
       temp_8115 ←
        (ret (q_8080)) ;;
      let '(x2_8081, y2_8085, _) :=
        (temp_8115) : (fp2_t '× fp2_t '× bool_ChoiceEquality) in
       '(x_diff_8090 : (fp_t '× fp_t)) ←
        ( '(temp_8084 : fp2_t) ←
            (fp2sub (x2_8081) (x1_8082)) ;;
          ret (temp_8084)) ;;
       '(y_diff_8089 : (fp_t '× fp_t)) ←
        ( '(temp_8088 : fp2_t) ←
            (fp2sub (y2_8085) (y1_8086)) ;;
          ret (temp_8088)) ;;
       '(xovery_8095 : (fp_t '× fp_t)) ←
        ( '(temp_8092 : fp2_t) ←
            (fp2inv (x_diff_8090)) ;;
           '(temp_8094 : fp2_t) ←
            (fp2mul (y_diff_8089) (temp_8092)) ;;
          ret (temp_8094)) ;;
       '(t1_8098 : (fp_t '× fp_t)) ←
        ( '(temp_8097 : fp2_t) ←
            (fp2mul (xovery_8095) (xovery_8095)) ;;
          ret (temp_8097)) ;;
       '(t2_8101 : (fp_t '× fp_t)) ←
        ( '(temp_8100 : fp2_t) ←
            (fp2sub (t1_8098) (x1_8082)) ;;
          ret (temp_8100)) ;;
       '(x3_8104 : (fp_t '× fp_t)) ←
        ( '(temp_8103 : fp2_t) ←
            (fp2sub (t2_8101) (x2_8081)) ;;
          ret (temp_8103)) ;;
       '(t1_8107 : (fp_t '× fp_t)) ←
        ( '(temp_8106 : fp2_t) ←
            (fp2sub (x1_8082) (x3_8104)) ;;
          ret (temp_8106)) ;;
       '(t2_8110 : (fp_t '× fp_t)) ←
        ( '(temp_8109 : fp2_t) ←
            (fp2mul (xovery_8095) (t1_8107)) ;;
          ret (temp_8109)) ;;
       '(y3_8113 : (fp_t '× fp_t)) ←
        ( '(temp_8112 : fp2_t) ←
            (fp2sub (t2_8110) (y1_8086)) ;;
          ret (temp_8112)) ;;
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality)) (
        prod_ce(x3_8104, y3_8113, (false : bool_ChoiceEquality))) } : code (
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
  (8168).
Program Definition g2double_a
   : package (fset.fset0) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
  #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ] [interface
  #val #[ G2DOUBLE_A ] : g2double_a_inp → g2double_a_out ] :=
  ([package #def #[ G2DOUBLE_A ] (temp_inp : g2double_a_inp) : g2double_a_out { 
    let '(p_8119) := temp_inp : g2_t in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP2INV ] : fp2inv_inp → fp2inv_out } as fp2inv ;;
    let fp2inv := fun x_0 => fp2inv (x_0) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    #import {sig #[ FP2SUB ] : fp2sub_inp → fp2sub_out } as fp2sub ;;
    let fp2sub := fun x_0 x_1 => fp2sub (x_0,x_1) in
    ({ code  temp_8167 ←
        (ret (p_8119)) ;;
      let '(x1_8120, y1_8134, _) :=
        (temp_8167) : (fp2_t '× fp2_t '× bool_ChoiceEquality) in
       '(x12_8127 : (fp_t '× fp_t)) ←
        ( '(temp_8122 : fp2_t) ←
            (fp2mul (x1_8120) (x1_8120)) ;;
          ret (temp_8122)) ;;
       '(t1_8139 : (fp_t '× fp_t)) ←
        ( '(temp_8124 : fp_t) ←
            (nat_mod_from_literal (
                0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
                @repr U128 3)) ;;
           '(temp_8126 : fp2_t) ←
            (fp2fromfp (temp_8124)) ;;
           '(temp_8129 : fp2_t) ←
            (fp2mul (temp_8126) (x12_8127)) ;;
          ret (temp_8129)) ;;
       '(t2_8140 : (fp_t '× fp_t)) ←
        ( '(temp_8131 : fp_t) ←
            (nat_mod_two ) ;;
           '(temp_8133 : fp2_t) ←
            (fp2fromfp (temp_8131)) ;;
           '(temp_8136 : fp2_t) ←
            (fp2mul (temp_8133) (y1_8134)) ;;
           '(temp_8138 : fp2_t) ←
            (fp2inv (temp_8136)) ;;
          ret (temp_8138)) ;;
       '(xovery_8143 : (fp_t '× fp_t)) ←
        ( '(temp_8142 : fp2_t) ←
            (fp2mul (t1_8139) (t2_8140)) ;;
          ret (temp_8142)) ;;
       '(t1_8152 : (fp_t '× fp_t)) ←
        ( '(temp_8145 : fp2_t) ←
            (fp2mul (xovery_8143) (xovery_8143)) ;;
          ret (temp_8145)) ;;
       '(t2_8153 : (fp_t '× fp_t)) ←
        ( '(temp_8147 : fp_t) ←
            (nat_mod_two ) ;;
           '(temp_8149 : fp2_t) ←
            (fp2fromfp (temp_8147)) ;;
           '(temp_8151 : fp2_t) ←
            (fp2mul (temp_8149) (x1_8120)) ;;
          ret (temp_8151)) ;;
       '(x3_8156 : (fp_t '× fp_t)) ←
        ( '(temp_8155 : fp2_t) ←
            (fp2sub (t1_8152) (t2_8153)) ;;
          ret (temp_8155)) ;;
       '(t1_8159 : (fp_t '× fp_t)) ←
        ( '(temp_8158 : fp2_t) ←
            (fp2sub (x1_8120) (x3_8156)) ;;
          ret (temp_8158)) ;;
       '(t2_8162 : (fp_t '× fp_t)) ←
        ( '(temp_8161 : fp2_t) ←
            (fp2mul (xovery_8143) (t1_8159)) ;;
          ret (temp_8161)) ;;
       '(y3_8165 : (fp_t '× fp_t)) ←
        ( '(temp_8164 : fp2_t) ←
            (fp2sub (t2_8162) (y1_8134)) ;;
          ret (temp_8164)) ;;
      @ret (((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality)) (
        prod_ce(x3_8156, y3_8165, (false : bool_ChoiceEquality))) } : code (
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
  (8187).
Program Definition g2double
   : package (fset.fset0) [interface
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
  #val #[ G2DOUBLE_A ] : g2double_a_inp → g2double_a_out ] [interface
  #val #[ G2DOUBLE ] : g2double_inp → g2double_out ] :=
  ([package #def #[ G2DOUBLE ] (temp_inp : g2double_inp) : g2double_out { 
    let '(p_8169) := temp_inp : g2_t in
    #import {sig #[ FP2ZERO ] : fp2zero_inp → fp2zero_out } as fp2zero ;;
    let fp2zero := fp2zero tt in
    #import {sig #[ G2DOUBLE_A ] : g2double_a_inp → g2double_a_out } as g2double_a ;;
    let g2double_a := fun x_0 => g2double_a (x_0) in
    ({ code  temp_8185 ←
        (ret (p_8169)) ;;
      let '(x1_8186, y1_8170, inf1_8175) :=
        (temp_8185) : (fp2_t '× fp2_t '× bool_ChoiceEquality) in
       '(temp_8172 : fp2_t) ←
        (fp2zero ) ;;
       '(temp_8174 : bool_ChoiceEquality) ←
        ((y1_8170) !=.? (temp_8172)) ;;
       '(temp_8177 : bool_ChoiceEquality) ←
        ((temp_8174) && (negb (inf1_8175))) ;;
       '(temp_8179 : g2_t) ←
        (g2double_a (p_8169)) ;;
       '(temp_8181 : fp2_t) ←
        (fp2zero ) ;;
       '(temp_8183 : fp2_t) ←
        (fp2zero ) ;;
      @ret (g2_t) ((if (temp_8177):bool_ChoiceEquality then (*inline*) (
            temp_8179) else (prod_ce(
              temp_8181,
              temp_8183,
              (true : bool_ChoiceEquality)
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
  (8218).
Program Definition g2add
   : package (fset.fset0) [interface
  #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ;
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
  #val #[ G2ADD_A ] : g2add_a_inp → g2add_a_out ;
  #val #[ G2DOUBLE ] : g2double_inp → g2double_out ] [interface
  #val #[ G2ADD ] : g2add_inp → g2add_out ] :=
  ([package #def #[ G2ADD ] (temp_inp : g2add_inp) : g2add_out { 
    let '(p_8188 , q_8189) := temp_inp : g2_t '× g2_t in
    #import {sig #[ FP2NEG ] : fp2neg_inp → fp2neg_out } as fp2neg ;;
    let fp2neg := fun x_0 => fp2neg (x_0) in
    #import {sig #[ FP2ZERO ] : fp2zero_inp → fp2zero_out } as fp2zero ;;
    let fp2zero := fp2zero tt in
    #import {sig #[ G2ADD_A ] : g2add_a_inp → g2add_a_out } as g2add_a ;;
    let g2add_a := fun x_0 x_1 => g2add_a (x_0,x_1) in
    #import {sig #[ G2DOUBLE ] : g2double_inp → g2double_out } as g2double ;;
    let g2double := fun x_0 => g2double (x_0) in
    ({ code  temp_8217 ←
        (ret (p_8188)) ;;
      let '(x1_8196, y1_8200, inf1_8190) :=
        (temp_8217) : (fp2_t '× fp2_t '× bool_ChoiceEquality) in
       temp_8215 ←
        (ret (q_8189)) ;;
      let '(x2_8197, y2_8201, inf2_8191) :=
        (temp_8215) : (fp2_t '× fp2_t '× bool_ChoiceEquality) in
       '(temp_8193 : bool_ChoiceEquality) ←
        ((p_8188) =.? (q_8189)) ;;
       '(temp_8195 : g2_t) ←
        (g2double (p_8188)) ;;
       '(temp_8199 : bool_ChoiceEquality) ←
        ((x1_8196) =.? (x2_8197)) ;;
       '(temp_8203 : fp2_t) ←
        (fp2neg (y2_8201)) ;;
       '(temp_8205 : bool_ChoiceEquality) ←
        ((y1_8200) =.? (temp_8203)) ;;
       '(temp_8207 : bool_ChoiceEquality) ←
        ((temp_8199) && (temp_8205)) ;;
       '(temp_8209 : g2_t) ←
        (g2add_a (p_8188) (q_8189)) ;;
       '(temp_8211 : fp2_t) ←
        (fp2zero ) ;;
       '(temp_8213 : fp2_t) ←
        (fp2zero ) ;;
      @ret (g2_t) ((if (inf1_8190):bool_ChoiceEquality then (*inline*) (
            q_8189) else ((if (inf2_8191):bool_ChoiceEquality then (*inline*) (
                p_8188) else ((if (
                    temp_8193):bool_ChoiceEquality then (*inline*) (
                    temp_8195) else ((if (negb (
                          temp_8207)):bool_ChoiceEquality then (*inline*) (
                        temp_8209) else (prod_ce(
                          temp_8211,
                          temp_8213,
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

Definition t_8223_loc : ChoiceEqualityLocation :=
  (((fp2_t '× fp2_t '× bool_ChoiceEquality) ; 8235%nat)).
Notation "'g2mul_inp'" := (
  scalar_t '× g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2mul_out'" := (g2_t : choice_type) (in custom pack_type at level 2).
Definition G2MUL : nat :=
  (8236).
Program Definition g2mul
   : package (CEfset ([t_8223_loc])) [interface
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
  #val #[ G2ADD ] : g2add_inp → g2add_out ;
  #val #[ G2DOUBLE ] : g2double_inp → g2double_out ] [interface
  #val #[ G2MUL ] : g2mul_inp → g2mul_out ] :=
  ([package #def #[ G2MUL ] (temp_inp : g2mul_inp) : g2mul_out { 
    let '(m_8226 , p_8232) := temp_inp : scalar_t '× g2_t in
    #import {sig #[ FP2ZERO ] : fp2zero_inp → fp2zero_out } as fp2zero ;;
    let fp2zero := fp2zero tt in
    #import {sig #[ G2ADD ] : g2add_inp → g2add_out } as g2add ;;
    let g2add := fun x_0 x_1 => g2add (x_0,x_1) in
    #import {sig #[ G2DOUBLE ] : g2double_inp → g2double_out } as g2double ;;
    let g2double := fun x_0 => g2double (x_0) in
    ({ code  '(t_8223 : (fp2_t '× fp2_t '× bool_ChoiceEquality)) ←
          ( '(temp_8220 : fp2_t) ←
              (fp2zero ) ;;
             '(temp_8222 : fp2_t) ←
              (fp2zero ) ;;
            ret (prod_ce(temp_8220, temp_8222, (true : bool_ChoiceEquality)
              ))) ;;
        #put t_8223_loc := t_8223 ;;
       '(t_8223 : ((fp2_t '× fp2_t '× bool_ChoiceEquality))) ←
        (foldi' (usize 0) (usize 256) t_8223 (L2 := CEfset ([t_8223_loc])) (
              I2 := [interface #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
              #val #[ G2ADD ] : g2add_inp → g2add_out ;
              #val #[ G2DOUBLE ] : g2double_inp → g2double_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_8227 t_8223 =>
            ({ code  '(t_8223 : (fp2_t '× fp2_t '× bool_ChoiceEquality)) ←
                  (( '(temp_8225 : g2_t) ←
                        (g2double (t_8223)) ;;
                      ret (temp_8225))) ;;
                #put t_8223_loc := t_8223 ;;
              
               '(temp_8229 : uint_size) ←
                ((usize 255) .- (i_8227)) ;;
               temp_8231 ←
                (nat_mod_bit (m_8226) (temp_8229)) ;;
               '(t_8223 : ((fp2_t '× fp2_t '× bool_ChoiceEquality))) ←
                (if temp_8231:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(t_8223 : (
                            fp2_t '×
                            fp2_t '×
                            bool_ChoiceEquality
                          )) ←
                        (( '(temp_8234 : g2_t) ←
                              (g2add (t_8223) (p_8232)) ;;
                            ret (temp_8234))) ;;
                      #put t_8223_loc := t_8223 ;;
                    
                    @ret (((fp2_t '× fp2_t '× bool_ChoiceEquality))) (
                      t_8223) in
                    ({ code temp_then } : code (CEfset (
                          [t_8223_loc])) [interface
                      #val #[ G2ADD ] : g2add_inp → g2add_out ] _))
                  else @ret (((fp2_t '× fp2_t '× bool_ChoiceEquality))) (
                    t_8223)) ;;
              
              @ret (((fp2_t '× fp2_t '× bool_ChoiceEquality))) (
                t_8223) } : code (CEfset ([t_8223_loc])) [interface
              #val #[ G2ADD ] : g2add_inp → g2add_out ;
              #val #[ G2DOUBLE ] : g2double_inp → g2double_out ] _))) ;;
      
      @ret ((fp2_t '× fp2_t '× bool_ChoiceEquality)) (t_8223) } : code (
        CEfset ([t_8223_loc])) [interface
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
  (8245).
Program Definition g2neg
   : package (fset.fset0) [interface
  #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ] [interface
  #val #[ G2NEG ] : g2neg_inp → g2neg_out ] :=
  ([package #def #[ G2NEG ] (temp_inp : g2neg_inp) : g2neg_out { 
    let '(p_8237) := temp_inp : g2_t in
    #import {sig #[ FP2NEG ] : fp2neg_inp → fp2neg_out } as fp2neg ;;
    let fp2neg := fun x_0 => fp2neg (x_0) in
    ({ code  temp_8244 ←
        (ret (p_8237)) ;;
      let '(x_8238, y_8239, inf_8242) :=
        (temp_8244) : (fp2_t '× fp2_t '× bool_ChoiceEquality) in
       '(temp_8241 : fp2_t) ←
        (fp2neg (y_8239)) ;;
      @ret (((fp_t '× fp_t) '× fp2_t '× bool_ChoiceEquality)) (prod_ce(
          x_8238,
          temp_8241,
          inf_8242
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
  (8269).
Program Definition twist
   : package (fset.fset0) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ;
  #val #[ FP6ZERO ] : fp6zero_inp → fp6zero_out ] [interface
  #val #[ TWIST ] : twist_inp → twist_out ] :=
  ([package #def #[ TWIST ] (temp_inp : twist_inp) : twist_out { 
    let '(p_8246) := temp_inp : g1_t in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP2ZERO ] : fp2zero_inp → fp2zero_out } as fp2zero ;;
    let fp2zero := fp2zero tt in
    #import {sig #[ FP6ZERO ] : fp6zero_inp → fp6zero_out } as fp6zero ;;
    let fp6zero := fp6zero tt in
    ({ code  temp_8268 ←
        (ret (p_8246)) ;;
      let '(p0_8249, p1_8260, _) :=
        (temp_8268) : (fp_t '× fp_t '× bool_ChoiceEquality) in
       '(x_8265 : ((fp2_t '× fp2_t '× fp2_t) '× fp6_t)) ←
        ( '(temp_8248 : fp2_t) ←
            (fp2zero ) ;;
           '(temp_8251 : fp2_t) ←
            (fp2fromfp (p0_8249)) ;;
           '(temp_8253 : fp2_t) ←
            (fp2zero ) ;;
           '(temp_8255 : fp6_t) ←
            (fp6zero ) ;;
          ret (prod_ce(prod_ce(temp_8248, temp_8251, temp_8253), temp_8255))) ;;
       '(y_8266 : (fp6_t '× (fp2_t '× fp2_t '× fp2_t))) ←
        ( '(temp_8257 : fp6_t) ←
            (fp6zero ) ;;
           '(temp_8259 : fp2_t) ←
            (fp2zero ) ;;
           '(temp_8262 : fp2_t) ←
            (fp2fromfp (p1_8260)) ;;
           '(temp_8264 : fp2_t) ←
            (fp2zero ) ;;
          ret (prod_ce(temp_8257, prod_ce(temp_8259, temp_8262, temp_8264)))) ;;
      @ret ((
          ((fp2_t '× fp2_t '× fp2_t) '× fp6_t) '×
          (fp6_t '× (fp2_t '× fp2_t '× fp2_t))
        )) (prod_ce(x_8265, y_8266)) } : code (fset.fset0) [interface
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
  (8325).
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
    let '(r_8270 , p_8306) := temp_inp : g2_t '× g1_t in
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
    ({ code  temp_8324 ←
        (ret (r_8270)) ;;
      let '(r0_8275, r1_8285, _) :=
        (temp_8324) : (fp2_t '× fp2_t '× bool_ChoiceEquality) in
       '(a_8280 : (fp_t '× fp_t)) ←
        ( '(temp_8272 : fp_t) ←
            (nat_mod_from_literal (
                0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
                @repr U128 3)) ;;
           '(temp_8274 : fp2_t) ←
            (fp2fromfp (temp_8272)) ;;
           '(temp_8277 : fp2_t) ←
            (fp2mul (r0_8275) (r0_8275)) ;;
           '(temp_8279 : fp2_t) ←
            (fp2mul (temp_8274) (temp_8277)) ;;
          ret (temp_8279)) ;;
       '(a_8292 : (fp_t '× fp_t)) ←
        ( '(temp_8282 : fp_t) ←
            (nat_mod_two ) ;;
           '(temp_8284 : fp2_t) ←
            (fp2fromfp (temp_8282)) ;;
           '(temp_8287 : fp2_t) ←
            (fp2mul (temp_8284) (r1_8285)) ;;
           '(temp_8289 : fp2_t) ←
            (fp2inv (temp_8287)) ;;
           '(temp_8291 : fp2_t) ←
            (fp2mul (a_8280) (temp_8289)) ;;
          ret (temp_8291)) ;;
       '(b_8301 : (fp_t '× fp_t)) ←
        ( '(temp_8294 : fp2_t) ←
            (fp2mul (a_8292) (r0_8275)) ;;
           '(temp_8296 : fp2_t) ←
            (fp2sub (r1_8285) (temp_8294)) ;;
          ret (temp_8296)) ;;
       '(a_8310 : (fp6_t '× fp6_t)) ←
        ( '(temp_8298 : fp6_t) ←
            (fp6fromfp2 (a_8292)) ;;
           '(temp_8300 : fp12_t) ←
            (fp12fromfp6 (temp_8298)) ;;
          ret (temp_8300)) ;;
       '(b_8316 : (fp6_t '× fp6_t)) ←
        ( '(temp_8303 : fp6_t) ←
            (fp6fromfp2 (b_8301)) ;;
           '(temp_8305 : fp12_t) ←
            (fp12fromfp6 (temp_8303)) ;;
          ret (temp_8305)) ;;
       temp_8322 ←
        ( '(temp_8308 : (fp12_t '× fp12_t)) ←
            (twist (p_8306)) ;;
          ret (temp_8308)) ;;
      let '(x_8311, y_8309) :=
        (temp_8322) : (fp12_t '× fp12_t) in
       '(temp_8313 : fp12_t) ←
        (fp12mul (a_8310) (x_8311)) ;;
       '(temp_8315 : fp12_t) ←
        (fp12sub (y_8309) (temp_8313)) ;;
       '(temp_8318 : fp12_t) ←
        (fp12sub (temp_8315) (b_8316)) ;;
       '(temp_8320 : fp12_t) ←
        (fp12neg (temp_8318)) ;;
      @ret (fp12_t) (temp_8320) } : code (fset.fset0) [interface
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
  (8375).
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
    let '(r_8326 , q_8327 , p_8354) := temp_inp : g2_t '× g2_t '× g1_t in
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
    ({ code  temp_8374 ←
        (ret (r_8326)) ;;
      let '(r0_8333, r1_8329, _) :=
        (temp_8374) : (fp2_t '× fp2_t '× bool_ChoiceEquality) in
       temp_8372 ←
        (ret (q_8327)) ;;
      let '(q0_8332, q1_8328, _) :=
        (temp_8372) : (fp2_t '× fp2_t '× bool_ChoiceEquality) in
       '(a_8340 : (fp_t '× fp_t)) ←
        ( '(temp_8331 : fp2_t) ←
            (fp2sub (q1_8328) (r1_8329)) ;;
           '(temp_8335 : fp2_t) ←
            (fp2sub (q0_8332) (r0_8333)) ;;
           '(temp_8337 : fp2_t) ←
            (fp2inv (temp_8335)) ;;
           '(temp_8339 : fp2_t) ←
            (fp2mul (temp_8331) (temp_8337)) ;;
          ret (temp_8339)) ;;
       '(b_8349 : (fp_t '× fp_t)) ←
        ( '(temp_8342 : fp2_t) ←
            (fp2mul (a_8340) (r0_8333)) ;;
           '(temp_8344 : fp2_t) ←
            (fp2sub (r1_8329) (temp_8342)) ;;
          ret (temp_8344)) ;;
       '(a_8358 : (fp6_t '× fp6_t)) ←
        ( '(temp_8346 : fp6_t) ←
            (fp6fromfp2 (a_8340)) ;;
           '(temp_8348 : fp12_t) ←
            (fp12fromfp6 (temp_8346)) ;;
          ret (temp_8348)) ;;
       '(b_8364 : (fp6_t '× fp6_t)) ←
        ( '(temp_8351 : fp6_t) ←
            (fp6fromfp2 (b_8349)) ;;
           '(temp_8353 : fp12_t) ←
            (fp12fromfp6 (temp_8351)) ;;
          ret (temp_8353)) ;;
       temp_8370 ←
        ( '(temp_8356 : (fp12_t '× fp12_t)) ←
            (twist (p_8354)) ;;
          ret (temp_8356)) ;;
      let '(x_8359, y_8357) :=
        (temp_8370) : (fp12_t '× fp12_t) in
       '(temp_8361 : fp12_t) ←
        (fp12mul (a_8358) (x_8359)) ;;
       '(temp_8363 : fp12_t) ←
        (fp12sub (y_8357) (temp_8361)) ;;
       '(temp_8366 : fp12_t) ←
        (fp12sub (temp_8363) (b_8364)) ;;
       '(temp_8368 : fp12_t) ←
        (fp12neg (temp_8366)) ;;
      @ret (fp12_t) (temp_8368) } : code (fset.fset0) [interface
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
  (8473).
Program Definition frobenius
   : package (fset.fset0) [interface
  #val #[ FP2CONJUGATE ] : fp2conjugate_inp → fp2conjugate_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] [interface
  #val #[ FROBENIUS ] : frobenius_inp → frobenius_out ] :=
  ([package #def #[ FROBENIUS ] (temp_inp : frobenius_inp) : frobenius_out { 
    let '(f_8376) := temp_inp : fp12_t in
    #import {sig #[ FP2CONJUGATE ] : fp2conjugate_inp → fp2conjugate_out } as fp2conjugate ;;
    let fp2conjugate := fun x_0 => fp2conjugate (x_0) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    ({ code  temp_8472 ←
        (ret (f_8376)) ;;
      let '((g0_8377, g1_8383, g2_8389), (h0_8380, h1_8386, h2_8392)) :=
        (temp_8472) : (fp6_t '× fp6_t) in
       '(t1_8465 : (fp_t '× fp_t)) ←
        ( '(temp_8379 : fp2_t) ←
            (fp2conjugate (g0_8377)) ;;
          ret (temp_8379)) ;;
       '(t2_8449 : (fp_t '× fp_t)) ←
        ( '(temp_8382 : fp2_t) ←
            (fp2conjugate (h0_8380)) ;;
          ret (temp_8382)) ;;
       '(t3_8452 : (fp_t '× fp_t)) ←
        ( '(temp_8385 : fp2_t) ←
            (fp2conjugate (g1_8383)) ;;
          ret (temp_8385)) ;;
       '(t4_8455 : (fp_t '× fp_t)) ←
        ( '(temp_8388 : fp2_t) ←
            (fp2conjugate (h1_8386)) ;;
          ret (temp_8388)) ;;
       '(t5_8458 : (fp_t '× fp_t)) ←
        ( '(temp_8391 : fp2_t) ←
            (fp2conjugate (g2_8389)) ;;
          ret (temp_8391)) ;;
       '(t6_8461 : (fp_t '× fp_t)) ←
        ( '(temp_8394 : fp2_t) ←
            (fp2conjugate (h2_8392)) ;;
          ret (temp_8394)) ;;
       '(c1_8409 : array_fp_t) ←
        ( '(temp_8396 : int64) ←
            (secret (@repr U64 10162220747404304312)) ;;
           '(temp_8398 : int64) ←
            (secret (@repr U64 17761815663483519293)) ;;
           '(temp_8400 : int64) ←
            (secret (@repr U64 8873291758750579140)) ;;
           '(temp_8402 : int64) ←
            (secret (@repr U64 1141103941765652303)) ;;
           '(temp_8404 : int64) ←
            (secret (@repr U64 13993175198059990303)) ;;
           '(temp_8406 : int64) ←
            (secret (@repr U64 1802798568193066599)) ;;
           '(temp_8408 : nseq uint64 6) ←
            (array_from_list uint64 [
                temp_8396;
                temp_8398;
                temp_8400;
                temp_8402;
                temp_8404;
                temp_8406
              ]) ;;
          ret (temp_8408)) ;;
       '(c1_8412 : seq uint8) ←
        ( temp_8411 ←
            (array_to_le_bytes (c1_8409)) ;;
          ret (temp_8411)) ;;
       '(c1_8435 : fp_t) ←
        ( '(temp_8414 : fp_t) ←
            (nat_mod_from_byte_seq_le (c1_8412)) ;;
          ret (temp_8414)) ;;
       '(c2_8429 : array_fp_t) ←
        ( '(temp_8416 : int64) ←
            (secret (@repr U64 3240210268673559283)) ;;
           '(temp_8418 : int64) ←
            (secret (@repr U64 2895069921743240898)) ;;
           '(temp_8420 : int64) ←
            (secret (@repr U64 17009126888523054175)) ;;
           '(temp_8422 : int64) ←
            (secret (@repr U64 6098234018649060207)) ;;
           '(temp_8424 : int64) ←
            (secret (@repr U64 9865672654120263608)) ;;
           '(temp_8426 : int64) ←
            (secret (@repr U64 71000049454473266)) ;;
           '(temp_8428 : nseq uint64 6) ←
            (array_from_list uint64 [
                temp_8416;
                temp_8418;
                temp_8420;
                temp_8422;
                temp_8424;
                temp_8426
              ]) ;;
          ret (temp_8428)) ;;
       '(c2_8432 : seq uint8) ←
        ( temp_8431 ←
            (array_to_le_bytes (c2_8429)) ;;
          ret (temp_8431)) ;;
       '(c2_8436 : fp_t) ←
        ( '(temp_8434 : fp_t) ←
            (nat_mod_from_byte_seq_le (c2_8432)) ;;
          ret (temp_8434)) ;;
       '(gamma11_8437 : (fp_t '× fp_t)) ←
        (ret (prod_ce(c1_8435, c2_8436))) ;;
       '(gamma12_8440 : (fp_t '× fp_t)) ←
        ( '(temp_8439 : fp2_t) ←
            (fp2mul (gamma11_8437) (gamma11_8437)) ;;
          ret (temp_8439)) ;;
       '(gamma13_8443 : (fp_t '× fp_t)) ←
        ( '(temp_8442 : fp2_t) ←
            (fp2mul (gamma12_8440) (gamma11_8437)) ;;
          ret (temp_8442)) ;;
       '(gamma14_8446 : (fp_t '× fp_t)) ←
        ( '(temp_8445 : fp2_t) ←
            (fp2mul (gamma13_8443) (gamma11_8437)) ;;
          ret (temp_8445)) ;;
       '(gamma15_8462 : (fp_t '× fp_t)) ←
        ( '(temp_8448 : fp2_t) ←
            (fp2mul (gamma14_8446) (gamma11_8437)) ;;
          ret (temp_8448)) ;;
       '(t2_8468 : (fp_t '× fp_t)) ←
        ( '(temp_8451 : fp2_t) ←
            (fp2mul (t2_8449) (gamma11_8437)) ;;
          ret (temp_8451)) ;;
       '(t3_8466 : (fp_t '× fp_t)) ←
        ( '(temp_8454 : fp2_t) ←
            (fp2mul (t3_8452) (gamma12_8440)) ;;
          ret (temp_8454)) ;;
       '(t4_8469 : (fp_t '× fp_t)) ←
        ( '(temp_8457 : fp2_t) ←
            (fp2mul (t4_8455) (gamma13_8443)) ;;
          ret (temp_8457)) ;;
       '(t5_8467 : (fp_t '× fp_t)) ←
        ( '(temp_8460 : fp2_t) ←
            (fp2mul (t5_8458) (gamma14_8446)) ;;
          ret (temp_8460)) ;;
       '(t6_8470 : (fp_t '× fp_t)) ←
        ( '(temp_8464 : fp2_t) ←
            (fp2mul (t6_8461) (gamma15_8462)) ;;
          ret (temp_8464)) ;;
      @ret ((
          ((fp_t '× fp_t) '× (fp_t '× fp_t) '× (fp_t '× fp_t)) '×
          ((fp_t '× fp_t) '× (fp_t '× fp_t) '× (fp_t '× fp_t))
        )) (prod_ce(
          prod_ce(t1_8465, t3_8466, t5_8467),
          prod_ce(t2_8468, t4_8469, t6_8470)
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
  (8583).
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
    let '(f_8474) := temp_inp : fp12_t in
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
    ({ code  '(fp6_8479 : (fp6_t '× fp6_t)) ←
        ( '(temp_8476 : fp12_t) ←
            (fp12conjugate (f_8474)) ;;
          ret (temp_8476)) ;;
       '(finv_8480 : (fp6_t '× fp6_t)) ←
        ( '(temp_8478 : fp12_t) ←
            (fp12inv (f_8474)) ;;
          ret (temp_8478)) ;;
       '(fp6_1_8483 : (fp6_t '× fp6_t)) ←
        ( '(temp_8482 : fp12_t) ←
            (fp12mul (fp6_8479) (finv_8480)) ;;
          ret (temp_8482)) ;;
       '(fp8_8488 : (fp6_t '× fp6_t)) ←
        ( '(temp_8485 : fp12_t) ←
            (frobenius (fp6_1_8483)) ;;
           '(temp_8487 : fp12_t) ←
            (frobenius (temp_8485)) ;;
          ret (temp_8487)) ;;
       '(f_8493 : (fp6_t '× fp6_t)) ←
        ( '(temp_8490 : fp12_t) ←
            (fp12mul (fp8_8488) (fp6_1_8483)) ;;
          ret (temp_8490)) ;;
       '(u_8497 : scalar_t) ←
        ( '(temp_8492 : scalar_t) ←
            (nat_mod_from_literal (
                0x8000000000000000000000000000000000000000000000000000000000000000) (
                @repr U128 15132376222941642752)) ;;
          ret (temp_8492)) ;;
       '(t0_8496 : (fp6_t '× fp6_t)) ←
        ( '(temp_8495 : fp12_t) ←
            (fp12mul (f_8493) (f_8493)) ;;
          ret (temp_8495)) ;;
       '(t1_8500 : (fp6_t '× fp6_t)) ←
        ( '(temp_8499 : fp12_t) ←
            (fp12exp (t0_8496) (u_8497)) ;;
          ret (temp_8499)) ;;
       '(t1_8503 : (fp6_t '× fp6_t)) ←
        ( '(temp_8502 : fp12_t) ←
            (fp12conjugate (t1_8500)) ;;
          ret (temp_8502)) ;;
       '(t2_8510 : (fp6_t '× fp6_t)) ←
        ( '(temp_8505 : scalar_t) ←
            (nat_mod_two ) ;;
           '(temp_8507 : scalar_t) ←
            ((u_8497) /% (temp_8505)) ;;
           '(temp_8509 : fp12_t) ←
            (fp12exp (t1_8503) (temp_8507)) ;;
          ret (temp_8509)) ;;
       '(t2_8522 : (fp6_t '× fp6_t)) ←
        ( '(temp_8512 : fp12_t) ←
            (fp12conjugate (t2_8510)) ;;
          ret (temp_8512)) ;;
       '(t3_8515 : (fp6_t '× fp6_t)) ←
        ( '(temp_8514 : fp12_t) ←
            (fp12conjugate (f_8493)) ;;
          ret (temp_8514)) ;;
       '(t1_8518 : (fp6_t '× fp6_t)) ←
        ( '(temp_8517 : fp12_t) ←
            (fp12mul (t3_8515) (t1_8503)) ;;
          ret (temp_8517)) ;;
       '(t1_8521 : (fp6_t '× fp6_t)) ←
        ( '(temp_8520 : fp12_t) ←
            (fp12conjugate (t1_8518)) ;;
          ret (temp_8520)) ;;
       '(t1_8525 : (fp6_t '× fp6_t)) ←
        ( '(temp_8524 : fp12_t) ←
            (fp12mul (t1_8521) (t2_8522)) ;;
          ret (temp_8524)) ;;
       '(t2_8528 : (fp6_t '× fp6_t)) ←
        ( '(temp_8527 : fp12_t) ←
            (fp12exp (t1_8525) (u_8497)) ;;
          ret (temp_8527)) ;;
       '(t2_8531 : (fp6_t '× fp6_t)) ←
        ( '(temp_8530 : fp12_t) ←
            (fp12conjugate (t2_8528)) ;;
          ret (temp_8530)) ;;
       '(t3_8534 : (fp6_t '× fp6_t)) ←
        ( '(temp_8533 : fp12_t) ←
            (fp12exp (t2_8531) (u_8497)) ;;
          ret (temp_8533)) ;;
       '(t3_8540 : (fp6_t '× fp6_t)) ←
        ( '(temp_8536 : fp12_t) ←
            (fp12conjugate (t3_8534)) ;;
          ret (temp_8536)) ;;
       '(t1_8539 : (fp6_t '× fp6_t)) ←
        ( '(temp_8538 : fp12_t) ←
            (fp12conjugate (t1_8525)) ;;
          ret (temp_8538)) ;;
       '(t3_8560 : (fp6_t '× fp6_t)) ←
        ( '(temp_8542 : fp12_t) ←
            (fp12mul (t1_8539) (t3_8540)) ;;
          ret (temp_8542)) ;;
       '(t1_8545 : (fp6_t '× fp6_t)) ←
        ( '(temp_8544 : fp12_t) ←
            (fp12conjugate (t1_8539)) ;;
          ret (temp_8544)) ;;
       '(t1_8556 : (fp6_t '× fp6_t)) ←
        ( '(temp_8547 : fp12_t) ←
            (frobenius (t1_8545)) ;;
           '(temp_8549 : fp12_t) ←
            (frobenius (temp_8547)) ;;
           '(temp_8551 : fp12_t) ←
            (frobenius (temp_8549)) ;;
          ret (temp_8551)) ;;
       '(t2_8557 : (fp6_t '× fp6_t)) ←
        ( '(temp_8553 : fp12_t) ←
            (frobenius (t2_8531)) ;;
           '(temp_8555 : fp12_t) ←
            (frobenius (temp_8553)) ;;
          ret (temp_8555)) ;;
       '(t1_8572 : (fp6_t '× fp6_t)) ←
        ( '(temp_8559 : fp12_t) ←
            (fp12mul (t1_8556) (t2_8557)) ;;
          ret (temp_8559)) ;;
       '(t2_8563 : (fp6_t '× fp6_t)) ←
        ( '(temp_8562 : fp12_t) ←
            (fp12exp (t3_8560) (u_8497)) ;;
          ret (temp_8562)) ;;
       '(t2_8566 : (fp6_t '× fp6_t)) ←
        ( '(temp_8565 : fp12_t) ←
            (fp12conjugate (t2_8563)) ;;
          ret (temp_8565)) ;;
       '(t2_8569 : (fp6_t '× fp6_t)) ←
        ( '(temp_8568 : fp12_t) ←
            (fp12mul (t2_8566) (t0_8496)) ;;
          ret (temp_8568)) ;;
       '(t2_8573 : (fp6_t '× fp6_t)) ←
        ( '(temp_8571 : fp12_t) ←
            (fp12mul (t2_8569) (f_8493)) ;;
          ret (temp_8571)) ;;
       '(t1_8578 : (fp6_t '× fp6_t)) ←
        ( '(temp_8575 : fp12_t) ←
            (fp12mul (t1_8572) (t2_8573)) ;;
          ret (temp_8575)) ;;
       '(t2_8579 : (fp6_t '× fp6_t)) ←
        ( '(temp_8577 : fp12_t) ←
            (frobenius (t3_8560)) ;;
          ret (temp_8577)) ;;
       '(t1_8582 : (fp6_t '× fp6_t)) ←
        ( '(temp_8581 : fp12_t) ←
            (fp12mul (t1_8578) (t2_8579)) ;;
          ret (temp_8581)) ;;
      @ret ((fp6_t '× fp6_t)) (t1_8582) } : code (CEfset ([])) [interface
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

Definition r_8595_loc : ChoiceEqualityLocation :=
  (((fp2_t '× fp2_t '× bool_ChoiceEquality) ; 8630%nat)).
Definition f_8601_loc : ChoiceEqualityLocation :=
  (((fp6_t '× fp6_t) ; 8631%nat)).
Notation "'pairing_inp'" := (
  g1_t '× g2_t : choice_type) (in custom pack_type at level 2).
Notation "'pairing_out'" := (
  fp12_t : choice_type) (in custom pack_type at level 2).
Definition PAIRING : nat :=
  (8632).
Program Definition pairing
   : package (CEfset ([r_8595_loc ; f_8601_loc])) [interface
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
    let '(p_8596 , q_8586) := temp_inp : g1_t '× g2_t in
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
    ({ code  '(t_8607 : scalar_t) ←
        ( '(temp_8585 : scalar_t) ←
            (nat_mod_from_literal (
                0x8000000000000000000000000000000000000000000000000000000000000000) (
                @repr U128 15132376222941642752)) ;;
          ret (temp_8585)) ;;
       '(r_8595 : (fp2_t '× fp2_t '× bool_ChoiceEquality)) ←
          (ret (q_8586)) ;;
        #put r_8595_loc := r_8595 ;;
       '(f_8601 : (fp6_t '× fp6_t)) ←
          ( '(temp_8588 : fp_t) ←
              (nat_mod_one ) ;;
             '(temp_8590 : fp2_t) ←
              (fp2fromfp (temp_8588)) ;;
             '(temp_8592 : fp6_t) ←
              (fp6fromfp2 (temp_8590)) ;;
             '(temp_8594 : fp12_t) ←
              (fp12fromfp6 (temp_8592)) ;;
            ret (temp_8594)) ;;
        #put f_8601_loc := f_8601 ;;
       temp_8629 ←
        (foldi' (usize 1) (usize 64) prod_ce(r_8595, f_8601) (L2 := CEfset (
                [r_8595_loc ; f_8601_loc])) (I2 := [interface
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
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_8608 '(
              r_8595,
              f_8601
            ) =>
            ({ code  '(lrr_8604 : (fp6_t '× fp6_t)) ←
                ( '(temp_8598 : fp12_t) ←
                    (line_double_p (r_8595) (p_8596)) ;;
                  ret (temp_8598)) ;;
               '(r_8595 : (fp2_t '× fp2_t '× bool_ChoiceEquality)) ←
                  (( '(temp_8600 : g2_t) ←
                        (g2double (r_8595)) ;;
                      ret (temp_8600))) ;;
                #put r_8595_loc := r_8595 ;;
              
               '(f_8601 : (fp6_t '× fp6_t)) ←
                  (( '(temp_8603 : fp12_t) ←
                        (fp12mul (f_8601) (f_8601)) ;;
                       '(temp_8606 : fp12_t) ←
                        (fp12mul (temp_8603) (lrr_8604)) ;;
                      ret (temp_8606))) ;;
                #put f_8601_loc := f_8601 ;;
              
               '(temp_8610 : uint_size) ←
                ((usize 64) .- (i_8608)) ;;
               '(temp_8612 : uint_size) ←
                ((temp_8610) .- (usize 1)) ;;
               temp_8614 ←
                (nat_mod_bit (t_8607) (temp_8612)) ;;
               temp_8623 ←
                (if temp_8614:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(lrq_8619 : (
                          fp6_t '×
                          fp6_t
                        )) ←
                      ( '(temp_8616 : fp12_t) ←
                          (line_add_p (r_8595) (q_8586) (p_8596)) ;;
                        ret (temp_8616)) ;;
                     '(r_8595 : (fp2_t '× fp2_t '× bool_ChoiceEquality)) ←
                        (( '(temp_8618 : g2_t) ←
                              (g2add (r_8595) (q_8586)) ;;
                            ret (temp_8618))) ;;
                      #put r_8595_loc := r_8595 ;;
                    
                     '(f_8601 : (fp6_t '× fp6_t)) ←
                        (( '(temp_8621 : fp12_t) ←
                              (fp12mul (f_8601) (lrq_8619)) ;;
                            ret (temp_8621))) ;;
                      #put f_8601_loc := f_8601 ;;
                    
                    @ret ((
                        (fp2_t '× fp2_t '× bool_ChoiceEquality) '×
                        (fp6_t '× fp6_t)
                      )) (prod_ce(r_8595, f_8601)) in
                    ({ code temp_then } : code (CEfset (
                          [r_8595_loc ; f_8601_loc])) [interface
                      #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
                      #val #[ G2ADD ] : g2add_inp → g2add_out ;
                      #val #[ LINE_ADD_P ] : line_add_p_inp → line_add_p_out
                      ] _))
                  else @ret ((
                      (fp2_t '× fp2_t '× bool_ChoiceEquality) '×
                      (fp6_t '× fp6_t)
                    )) (prod_ce(r_8595, f_8601))) ;;
              let '(r_8595, f_8601) :=
                (temp_8623) : (
                (fp2_t '× fp2_t '× bool_ChoiceEquality) '×
                (fp6_t '× fp6_t)
              ) in
              
              @ret ((
                  (fp2_t '× fp2_t '× bool_ChoiceEquality) '×
                  (fp6_t '× fp6_t)
                )) (prod_ce(r_8595, f_8601)) } : code (CEfset (
                  [r_8595_loc ; f_8601_loc])) [interface
              #val #[ FP12MUL ] : fp12mul_inp → fp12mul_out ;
              #val #[ G2ADD ] : g2add_inp → g2add_out ;
              #val #[ G2DOUBLE ] : g2double_inp → g2double_out ;
              #val #[ LINE_ADD_P ] : line_add_p_inp → line_add_p_out ;
              #val #[ LINE_DOUBLE_P ] : line_double_p_inp → line_double_p_out
              ] _))) ;;
      let '(r_8595, f_8601) :=
        (temp_8629) : (
        (fp2_t '× fp2_t '× bool_ChoiceEquality) '×
        (fp6_t '× fp6_t)
      ) in
      
       '(temp_8625 : fp12_t) ←
        (fp12conjugate (f_8601)) ;;
       '(temp_8627 : fp12_t) ←
        (final_exponentiation (temp_8625)) ;;
      @ret (fp12_t) (temp_8627) } : code (CEfset (
          [r_8595_loc ; f_8601_loc])) [interface
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
  (8645).
Program Definition test_fp2_prop_add_neg
   : package (fset.fset0) [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ] [interface
  #val #[ TEST_FP2_PROP_ADD_NEG ] : test_fp2_prop_add_neg_inp → test_fp2_prop_add_neg_out
  ] :=
  (
    [package #def #[ TEST_FP2_PROP_ADD_NEG ] (temp_inp : test_fp2_prop_add_neg_inp) : test_fp2_prop_add_neg_out { 
    let '(a_8633) := temp_inp : fp2_t in
    #import {sig #[ FP2ADD ] : fp2add_inp → fp2add_out } as fp2add ;;
    let fp2add := fun x_0 x_1 => fp2add (x_0,x_1) in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP2NEG ] : fp2neg_inp → fp2neg_out } as fp2neg ;;
    let fp2neg := fun x_0 => fp2neg (x_0) in
    ({ code  '(b_8640 : (fp_t '× fp_t)) ←
        ( '(temp_8635 : fp2_t) ←
            (fp2neg (a_8633)) ;;
          ret (temp_8635)) ;;
       '(temp_8637 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_8639 : fp2_t) ←
        (fp2fromfp (temp_8637)) ;;
       '(temp_8642 : fp2_t) ←
        (fp2add (a_8633) (b_8640)) ;;
       '(temp_8644 : bool_ChoiceEquality) ←
        ((temp_8639) =.? (temp_8642)) ;;
      @ret (bool_ChoiceEquality) (temp_8644) } : code (fset.fset0) [interface
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
  (8658).
Program Definition test_fp2_prop_mul_inv
   : package (fset.fset0) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] [interface
  #val #[ TEST_FP2_PROP_MUL_INV ] : test_fp2_prop_mul_inv_inp → test_fp2_prop_mul_inv_out
  ] :=
  (
    [package #def #[ TEST_FP2_PROP_MUL_INV ] (temp_inp : test_fp2_prop_mul_inv_inp) : test_fp2_prop_mul_inv_out { 
    let '(a_8646) := temp_inp : fp2_t in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP2INV ] : fp2inv_inp → fp2inv_out } as fp2inv ;;
    let fp2inv := fun x_0 => fp2inv (x_0) in
    #import {sig #[ FP2MUL ] : fp2mul_inp → fp2mul_out } as fp2mul ;;
    let fp2mul := fun x_0 x_1 => fp2mul (x_0,x_1) in
    ({ code  '(b_8653 : (fp_t '× fp_t)) ←
        ( '(temp_8648 : fp2_t) ←
            (fp2inv (a_8646)) ;;
          ret (temp_8648)) ;;
       '(temp_8650 : fp_t) ←
        (nat_mod_one ) ;;
       '(temp_8652 : fp2_t) ←
        (fp2fromfp (temp_8650)) ;;
       '(temp_8655 : fp2_t) ←
        (fp2mul (a_8646) (b_8653)) ;;
       '(temp_8657 : bool_ChoiceEquality) ←
        ((temp_8652) =.? (temp_8655)) ;;
      @ret (bool_ChoiceEquality) (temp_8657) } : code (fset.fset0) [interface
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
  (8678).
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
    ({ code  '(b_8673 : (fp_t '× fp_t)) ←
        ( '(temp_8660 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_8662 : fp_t) ←
            (nat_mod_one ) ;;
           '(temp_8664 : fp2_t) ←
            (fp2inv (prod_ce(temp_8660, temp_8662))) ;;
          ret (temp_8664)) ;;
       '(temp_8666 : fp_t) ←
        (nat_mod_one ) ;;
       '(temp_8668 : fp2_t) ←
        (fp2fromfp (temp_8666)) ;;
       '(temp_8670 : fp_t) ←
        (nat_mod_one ) ;;
       '(temp_8672 : fp_t) ←
        (nat_mod_one ) ;;
       '(temp_8675 : fp2_t) ←
        (fp2mul (prod_ce(temp_8670, temp_8672)) (b_8673)) ;;
       '(temp_8677 : bool_ChoiceEquality) ←
        ((temp_8668) =.? (temp_8675)) ;;
      @ret (bool_ChoiceEquality) (temp_8677) } : code (fset.fset0) [interface
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
  (8693).
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
    let '(a_8679) := temp_inp : fp6_t in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out } as fp6fromfp2 ;;
    let fp6fromfp2 := fun x_0 => fp6fromfp2 (x_0) in
    #import {sig #[ FP6INV ] : fp6inv_inp → fp6inv_out } as fp6inv ;;
    let fp6inv := fun x_0 => fp6inv (x_0) in
    #import {sig #[ FP6MUL ] : fp6mul_inp → fp6mul_out } as fp6mul ;;
    let fp6mul := fun x_0 x_1 => fp6mul (x_0,x_1) in
    ({ code  '(b_8688 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_8681 : fp6_t) ←
            (fp6inv (a_8679)) ;;
          ret (temp_8681)) ;;
       '(temp_8683 : fp_t) ←
        (nat_mod_one ) ;;
       '(temp_8685 : fp2_t) ←
        (fp2fromfp (temp_8683)) ;;
       '(temp_8687 : fp6_t) ←
        (fp6fromfp2 (temp_8685)) ;;
       '(temp_8690 : fp6_t) ←
        (fp6mul (a_8679) (b_8688)) ;;
       '(temp_8692 : bool_ChoiceEquality) ←
        ((temp_8687) =.? (temp_8690)) ;;
      @ret (bool_ChoiceEquality) (temp_8692) } : code (fset.fset0) [interface
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
  (8708).
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
    let '(a_8694) := temp_inp : fp6_t in
    #import {sig #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out } as fp2fromfp ;;
    let fp2fromfp := fun x_0 => fp2fromfp (x_0) in
    #import {sig #[ FP6ADD ] : fp6add_inp → fp6add_out } as fp6add ;;
    let fp6add := fun x_0 x_1 => fp6add (x_0,x_1) in
    #import {sig #[ FP6FROMFP2 ] : fp6fromfp2_inp → fp6fromfp2_out } as fp6fromfp2 ;;
    let fp6fromfp2 := fun x_0 => fp6fromfp2 (x_0) in
    #import {sig #[ FP6NEG ] : fp6neg_inp → fp6neg_out } as fp6neg ;;
    let fp6neg := fun x_0 => fp6neg (x_0) in
    ({ code  '(b_8703 : (fp2_t '× fp2_t '× fp2_t)) ←
        ( '(temp_8696 : fp6_t) ←
            (fp6neg (a_8694)) ;;
          ret (temp_8696)) ;;
       '(temp_8698 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_8700 : fp2_t) ←
        (fp2fromfp (temp_8698)) ;;
       '(temp_8702 : fp6_t) ←
        (fp6fromfp2 (temp_8700)) ;;
       '(temp_8705 : fp6_t) ←
        (fp6add (a_8694) (b_8703)) ;;
       '(temp_8707 : bool_ChoiceEquality) ←
        ((temp_8702) =.? (temp_8705)) ;;
      @ret (bool_ChoiceEquality) (temp_8707) } : code (fset.fset0) [interface
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
  (8725).
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
    let '(a_8709) := temp_inp : fp12_t in
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
    ({ code  '(b_8720 : (fp6_t '× fp6_t)) ←
        ( '(temp_8711 : fp12_t) ←
            (fp12neg (a_8709)) ;;
          ret (temp_8711)) ;;
       '(temp_8713 : fp_t) ←
        (nat_mod_zero ) ;;
       '(temp_8715 : fp2_t) ←
        (fp2fromfp (temp_8713)) ;;
       '(temp_8717 : fp6_t) ←
        (fp6fromfp2 (temp_8715)) ;;
       '(temp_8719 : fp12_t) ←
        (fp12fromfp6 (temp_8717)) ;;
       '(temp_8722 : fp12_t) ←
        (fp12add (a_8709) (b_8720)) ;;
       '(temp_8724 : bool_ChoiceEquality) ←
        ((temp_8719) =.? (temp_8722)) ;;
      @ret (bool_ChoiceEquality) (temp_8724) } : code (fset.fset0) [interface
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
  (8742).
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
    let '(a_8726) := temp_inp : fp12_t in
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
    ({ code  '(b_8737 : (fp6_t '× fp6_t)) ←
        ( '(temp_8728 : fp12_t) ←
            (fp12inv (a_8726)) ;;
          ret (temp_8728)) ;;
       '(temp_8730 : fp_t) ←
        (nat_mod_one ) ;;
       '(temp_8732 : fp2_t) ←
        (fp2fromfp (temp_8730)) ;;
       '(temp_8734 : fp6_t) ←
        (fp6fromfp2 (temp_8732)) ;;
       '(temp_8736 : fp12_t) ←
        (fp12fromfp6 (temp_8734)) ;;
       '(temp_8739 : fp12_t) ←
        (fp12mul (a_8726) (b_8737)) ;;
       '(temp_8741 : bool_ChoiceEquality) ←
        ((temp_8736) =.? (temp_8739)) ;;
      @ret (bool_ChoiceEquality) (temp_8741) } : code (fset.fset0) [interface
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

