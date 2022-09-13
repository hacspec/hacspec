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

Definition r_1_loc : ChoiceEqualityLocation :=
  ((int64 ; 5%nat)).
Notation "'xor_inp'" := (
  int64 '× int64 : choice_type) (in custom pack_type at level 2).
Notation "'xor_out'" := (int64 : choice_type) (in custom pack_type at level 2).
Definition XOR : nat :=
  (6).
Program Definition xor
   : package (CEfset ([r_1_loc])) [interface] [interface
  #val #[ XOR ] : xor_inp → xor_out ] :=
  ([package #def #[ XOR ] (temp_inp : xor_inp) : xor_out { 
    let '(x_0 , y_2) := temp_inp : int64 '× int64 in
    ({ code  '(r_1 : int64) ←
          (ret (x_0)) ;;
        #put r_1_loc := r_1 ;;
       '(r_1 : int64) ←
          (( temp_4 ←
                ((r_1) .^ (y_2)) ;;
              ret (temp_4))) ;;
        #put r_1_loc := r_1 ;;
      
      @ret (int64) (r_1) } : code (CEfset ([r_1_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_xor : package _ _ _ :=
  (xor).
Fail Next Obligation.

Definition z_28_loc : ChoiceEqualityLocation :=
  ((seq int64 ; 29%nat)).
Notation "'otp_inp'" := (
  seq int64 '× seq int64 : choice_type) (in custom pack_type at level 2).
Notation "'otp_out'" := ((result (unit_ChoiceEquality) (
      seq int64)) : choice_type) (in custom pack_type at level 2).
Definition OTP : nat :=
  (30).
Program Definition otp
   : package (CEfset ([z_28_loc])) [interface
  #val #[ XOR ] : xor_inp → xor_out ] [interface
  #val #[ OTP ] : otp_inp → otp_out ] :=
  ([package #def #[ OTP ] (temp_inp : otp_inp) : otp_out { 
    let '(x_7 , y_10) := temp_inp : seq int64 '× seq int64 in
    #import {sig #[ XOR ] : xor_inp → xor_out } as xor ;;
    let xor := fun x_0 x_1 => xor (x_0,x_1) in
    ({ code  '(temp_9 : uint_size) ←
        (seq_len (x_7)) ;;
       '(temp_12 : uint_size) ←
        (seq_len (y_10)) ;;
       '(temp_14 : bool_ChoiceEquality) ←
        ((temp_9) !=.? (temp_12)) ;;
      bnd(
        ChoiceEqualityMonad.result_bind_code unit_ChoiceEquality , unit_ChoiceEquality , _ , CEfset (
          [z_28_loc])) 'tt ⇠
      (if temp_14 : bool_ChoiceEquality
        then (*state*) (({ code bnd(
              ChoiceEqualityMonad.result_bind_code unit_ChoiceEquality , seq int64 , _ , fset.fset0) _ ⇠
            (({ code @ret _ (@inr (seq int64) (unit_ChoiceEquality) (
                    tt)) } : code (fset.fset0) [interface] _)) in
            ({ code @ret ((result (unit_ChoiceEquality) (
                    unit_ChoiceEquality))) (@inl (unit_ChoiceEquality) (
                  unit_ChoiceEquality) ((tt : unit_ChoiceEquality))) } : code (
                fset.fset0) [interface] _) } : code (fset.fset0) [interface] _))
        else ({ code @ret ((result (unit_ChoiceEquality) (
                unit_ChoiceEquality))) (@inl (unit_ChoiceEquality) (
              unit_ChoiceEquality) (
              (tt : unit_ChoiceEquality))) } : code _ _ _) ) in
      ({ code  '(z_28 : seq int64) ←
            ( '(temp_16 : uint_size) ←
                (seq_len (x_7)) ;;
               temp_18 ←
                (seq_new_ (default : int64) (temp_16)) ;;
              ret (temp_18)) ;;
          #put z_28_loc := z_28 ;;
         '(temp_20 : uint_size) ←
          (seq_len (x_7)) ;;
         '(z_28 : (seq int64)) ←
          (foldi' (usize 1) (temp_20) z_28 (L2 := CEfset ([z_28_loc])) (
                I2 := [interface #val #[ XOR ] : xor_inp → xor_out
                ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_21 z_28 =>
              ({ code  '(z_28 : seq int64) ←
                  ( '(temp_23 : int64) ←
                      (seq_index (x_7) (i_21)) ;;
                     '(temp_25 : int64) ←
                      (seq_index (y_10) (i_21)) ;;
                     '(temp_27 : int64) ←
                      (xor (temp_23) (temp_25)) ;;
                    ret (seq_upd z_28 (i_21) (temp_27))) ;;
                
                @ret ((seq int64)) (z_28) } : code (CEfset (
                    [z_28_loc])) [interface #val #[ XOR ] : xor_inp → xor_out
                ] _))) ;;
        
        @ret ((result (unit_ChoiceEquality) (seq int64))) (@inl (seq int64) (
            unit_ChoiceEquality) (z_28)) } : code (CEfset (
            [z_28_loc])) [interface #val #[ XOR ] : xor_inp → xor_out
        ] _) } : code (CEfset ([z_28_loc])) [interface
      #val #[ XOR ] : xor_inp → xor_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_otp : package _ _ _ :=
  (seq_link otp link_rest(package_xor)).
Fail Next Obligation.

