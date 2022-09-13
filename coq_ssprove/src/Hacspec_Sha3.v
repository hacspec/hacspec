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

Definition rounds_v : (uint_size) :=
  ((usize 24)).

Definition sha3224_rate_v : (uint_size) :=
  ((usize 144)).

Definition sha3256_rate_v : (uint_size) :=
  ((usize 136)).

Definition sha3384_rate_v : (uint_size) :=
  ((usize 104)).

Definition sha3512_rate_v : (uint_size) :=
  ((usize 72)).

Definition shake128_rate_v : (uint_size) :=
  ((usize 168)).

Definition shake256_rate_v : (uint_size) :=
  ((usize 136)).

Definition state_t  :=
  ( nseq (uint64) (usize 25)).

Definition row_t  :=
  ( nseq (uint64) (usize 5)).

Definition digest224_t  :=
  ( nseq (uint8) (usize 28)).

Definition digest256_t  :=
  ( nseq (uint8) (usize 32)).

Definition digest384_t  :=
  ( nseq (uint8) (usize 48)).

Definition digest512_t  :=
  ( nseq (uint8) (usize 64)).

Definition round_constants_t  :=
  ( nseq (int64) (rounds_v)).

Definition rotation_constants_t  :=
  ( nseq (uint_size) (usize 25)).

Definition roundconstants_v : (round_constants_t) :=
  (let temp_6628 : nseq int64 24 :=
      (array_from_list int64 [
          @repr U64 1;
          @repr U64 32898;
          @repr U64 9223372036854808714;
          @repr U64 9223372039002292224;
          @repr U64 32907;
          @repr U64 2147483649;
          @repr U64 9223372039002292353;
          @repr U64 9223372036854808585;
          @repr U64 138;
          @repr U64 136;
          @repr U64 2147516425;
          @repr U64 2147483658;
          @repr U64 2147516555;
          @repr U64 9223372036854775947;
          @repr U64 9223372036854808713;
          @repr U64 9223372036854808579;
          @repr U64 9223372036854808578;
          @repr U64 9223372036854775936;
          @repr U64 32778;
          @repr U64 9223372039002259466;
          @repr U64 9223372039002292353;
          @repr U64 9223372036854808704;
          @repr U64 2147483649;
          @repr U64 9223372039002292232
        ]) in
    (temp_6628)).

Definition rotc_v : (rotation_constants_t) :=
  (let temp_6630 : nseq uint_size 25 :=
      (array_from_list uint_size [
          usize 0;
          usize 1;
          usize 62;
          usize 28;
          usize 27;
          usize 36;
          usize 44;
          usize 6;
          usize 55;
          usize 20;
          usize 3;
          usize 10;
          usize 43;
          usize 25;
          usize 39;
          usize 41;
          usize 45;
          usize 15;
          usize 21;
          usize 8;
          usize 18;
          usize 2;
          usize 61;
          usize 56;
          usize 14
        ]) in
    (temp_6630)).

Definition pi_v : (rotation_constants_t) :=
  (let temp_6632 : nseq uint_size 25 :=
      (array_from_list uint_size [
          usize 0;
          usize 6;
          usize 12;
          usize 18;
          usize 24;
          usize 3;
          usize 9;
          usize 10;
          usize 16;
          usize 22;
          usize 1;
          usize 7;
          usize 13;
          usize 19;
          usize 20;
          usize 4;
          usize 5;
          usize 11;
          usize 17;
          usize 23;
          usize 2;
          usize 8;
          usize 14;
          usize 15;
          usize 21
        ]) in
    (temp_6632)).

Definition b_6663_loc : ChoiceEqualityLocation :=
  ((row_t ; 6696%nat)).
Notation "'theta_inp'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'theta_out'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Definition THETA : nat :=
  (6697).
Program Definition theta
   : package (CEfset ([b_6663_loc])) [interface] [interface
  #val #[ THETA ] : theta_inp → theta_out ] :=
  ([package #def #[ THETA ] (temp_inp : theta_inp) : theta_out { 
    let '(s_6637) := temp_inp : state_t in
    ({ code  '(b_6663 : row_t) ←
          ( '(temp_6634 : row_t) ←
              (array_new_ (default : uint64) (5)) ;;
            ret (temp_6634)) ;;
        #put b_6663_loc := b_6663 ;;
       '(b_6663 : (row_t)) ←
        (foldi' (usize 0) (usize 5) b_6663 (L2 := CEfset ([b_6663_loc])) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_6635 b_6663 =>
            ({ code  '(b_6663 : row_t) ←
                ( temp_6638 ←
                    (array_index (s_6637) (i_6635)) ;;
                   '(temp_6640 : uint_size) ←
                    ((i_6635) .+ (usize 5)) ;;
                   temp_6642 ←
                    (array_index (s_6637) (temp_6640)) ;;
                   temp_6644 ←
                    ((temp_6638) .^ (temp_6642)) ;;
                   '(temp_6646 : uint_size) ←
                    ((i_6635) .+ (usize 10)) ;;
                   temp_6648 ←
                    (array_index (s_6637) (temp_6646)) ;;
                   temp_6650 ←
                    ((temp_6644) .^ (temp_6648)) ;;
                   '(temp_6652 : uint_size) ←
                    ((i_6635) .+ (usize 15)) ;;
                   temp_6654 ←
                    (array_index (s_6637) (temp_6652)) ;;
                   temp_6656 ←
                    ((temp_6650) .^ (temp_6654)) ;;
                   '(temp_6658 : uint_size) ←
                    ((i_6635) .+ (usize 20)) ;;
                   temp_6660 ←
                    (array_index (s_6637) (temp_6658)) ;;
                   temp_6662 ←
                    ((temp_6656) .^ (temp_6660)) ;;
                  ret (array_upd b_6663 (i_6635) (temp_6662))) ;;
              
              @ret ((row_t)) (b_6663) } : code (CEfset (
                  [b_6663_loc])) [interface] _))) ;;
      
       '(s_6637 : (state_t)) ←
        (foldi' (usize 0) (usize 5) s_6637 (L2 := CEfset ([b_6663_loc])) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_6664 s_6637 =>
            ({ code  '(u_6677 : uint64) ←
                ( '(temp_6666 : uint_size) ←
                    ((i_6664) .+ (usize 1)) ;;
                   '(temp_6668 : uint_size) ←
                    ((temp_6666) %% (usize 5)) ;;
                   temp_6670 ←
                    (array_index (b_6663) (temp_6668)) ;;
                  ret (temp_6670)) ;;
               '(t_6693 : uint64) ←
                ( '(temp_6672 : uint_size) ←
                    ((i_6664) .+ (usize 4)) ;;
                   '(temp_6674 : uint_size) ←
                    ((temp_6672) %% (usize 5)) ;;
                   temp_6676 ←
                    (array_index (b_6663) (temp_6674)) ;;
                   temp_6679 ←
                    (uint64_rotate_left (u_6677) (usize 1)) ;;
                   temp_6681 ←
                    ((temp_6676) .^ (temp_6679)) ;;
                  ret (temp_6681)) ;;
               '(s_6637 : (state_t)) ←
                (foldi' (usize 0) (usize 5) s_6637 (L2 := CEfset (
                        [b_6663_loc])) (
                      I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun j_6682 s_6637 =>
                    ({ code  '(s_6637 : state_t) ←
                        ( '(temp_6684 : uint_size) ←
                            ((usize 5) .* (j_6682)) ;;
                           '(temp_6686 : uint_size) ←
                            ((temp_6684) .+ (i_6664)) ;;
                           '(temp_6688 : uint_size) ←
                            ((usize 5) .* (j_6682)) ;;
                           '(temp_6690 : uint_size) ←
                            ((temp_6688) .+ (i_6664)) ;;
                           temp_6692 ←
                            (array_index (s_6637) (temp_6690)) ;;
                           temp_6695 ←
                            ((temp_6692) .^ (t_6693)) ;;
                          ret (array_upd s_6637 (temp_6686) (temp_6695))) ;;
                      
                      @ret ((state_t)) (s_6637) } : code (CEfset (
                          [b_6663_loc])) [interface] _))) ;;
              
              @ret ((state_t)) (s_6637) } : code (CEfset (
                  [b_6663_loc])) [interface] _))) ;;
      
      @ret (state_t) (s_6637) } : code (CEfset ([b_6663_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_theta : package _ _ _ :=
  (theta).
Fail Next Obligation.


Notation "'rho_inp'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'rho_out'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Definition RHO : nat :=
  (6707).
Program Definition rho
   : package (fset.fset0) [interface] [interface
  #val #[ RHO ] : rho_inp → rho_out ] :=
  ([package #def #[ RHO ] (temp_inp : rho_inp) : rho_out { 
    let '(s_6700) := temp_inp : state_t in
    ({ code  '(s_6700 : (state_t)) ←
        (foldi' (usize 0) (usize 25) s_6700 (L2 := fset.fset0) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_6698 s_6700 =>
            ({ code  '(u_6702 : uint64) ←
                ( temp_6701 ←
                    (array_index (s_6700) (i_6698)) ;;
                  ret (temp_6701)) ;;
               '(s_6700 : state_t) ←
                ( temp_6704 ←
                    (array_index (rotc_v) (i_6698)) ;;
                   temp_6706 ←
                    (uint64_rotate_left (u_6702) (temp_6704)) ;;
                  ret (array_upd s_6700 (i_6698) (temp_6706))) ;;
              
              @ret ((state_t)) (s_6700) } : code (
                fset.fset0) [interface] _))) ;;
      
      @ret (state_t) (s_6700) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_rho : package _ _ _ :=
  (rho).
Fail Next Obligation.

Definition v_6716_loc : ChoiceEqualityLocation :=
  ((state_t ; 6717%nat)).
Notation "'pi_inp'" := (state_t : choice_type) (in custom pack_type at level 2).
Notation "'pi_out'" := (state_t : choice_type) (in custom pack_type at level 2).
Definition PI : nat :=
  (6718).
Program Definition pi
   : package (CEfset ([v_6716_loc])) [interface] [interface
  #val #[ PI ] : pi_inp → pi_out ] :=
  ([package #def #[ PI ] (temp_inp : pi_inp) : pi_out { 
    let '(s_6714) := temp_inp : state_t in
    ({ code  '(v_6716 : state_t) ←
          ( '(temp_6709 : state_t) ←
              (array_new_ (default : uint64) (25)) ;;
            ret (temp_6709)) ;;
        #put v_6716_loc := v_6716 ;;
       '(v_6716 : (state_t)) ←
        (foldi' (usize 0) (usize 25) v_6716 (L2 := CEfset ([v_6716_loc])) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_6710 v_6716 =>
            ({ code  '(v_6716 : state_t) ←
                ( temp_6712 ←
                    (array_index (pi_v) (i_6710)) ;;
                   temp_6715 ←
                    (array_index (s_6714) (temp_6712)) ;;
                  ret (array_upd v_6716 (i_6710) (temp_6715))) ;;
              
              @ret ((state_t)) (v_6716) } : code (CEfset (
                  [v_6716_loc])) [interface] _))) ;;
      
      @ret (state_t) (v_6716) } : code (CEfset ([v_6716_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_pi : package _ _ _ :=
  (pi).
Fail Next Obligation.

Definition b_6730_loc : ChoiceEqualityLocation :=
  ((row_t ; 6761%nat)).
Notation "'chi_inp'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'chi_out'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Definition CHI : nat :=
  (6762).
Program Definition chi
   : package (CEfset ([b_6730_loc])) [interface] [interface
  #val #[ CHI ] : chi_inp → chi_out ] :=
  ([package #def #[ CHI ] (temp_inp : chi_inp) : chi_out { 
    let '(s_6728) := temp_inp : state_t in
    ({ code  '(b_6730 : row_t) ←
          ( '(temp_6720 : row_t) ←
              (array_new_ (default : uint64) (5)) ;;
            ret (temp_6720)) ;;
        #put b_6730_loc := b_6730 ;;
       temp_6760 ←
        (foldi' (usize 0) (usize 5) prod_ce(s_6728, b_6730) (L2 := CEfset (
                [b_6730_loc])) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_6722 '(
              s_6728,
              b_6730
            ) =>
            ({ code  '(b_6730 : (row_t)) ←
                (foldi' (usize 0) (usize 5) b_6730 (L2 := CEfset (
                        [b_6730_loc])) (
                      I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun j_6721 b_6730 =>
                    ({ code  '(b_6730 : row_t) ←
                        ( '(temp_6724 : uint_size) ←
                            ((usize 5) .* (i_6722)) ;;
                           '(temp_6726 : uint_size) ←
                            ((temp_6724) .+ (j_6721)) ;;
                           temp_6729 ←
                            (array_index (s_6728) (temp_6726)) ;;
                          ret (array_upd b_6730 (j_6721) (temp_6729))) ;;
                      
                      @ret ((row_t)) (b_6730) } : code (CEfset (
                          [b_6730_loc])) [interface] _))) ;;
              
               '(s_6728 : (state_t)) ←
                (foldi' (usize 0) (usize 5) s_6728 (L2 := CEfset (
                        [b_6730_loc])) (
                      I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun j_6731 s_6728 =>
                    ({ code  '(u_6748 : uint64) ←
                        ( '(temp_6733 : uint_size) ←
                            ((j_6731) .+ (usize 1)) ;;
                           '(temp_6735 : uint_size) ←
                            ((temp_6733) %% (usize 5)) ;;
                           temp_6737 ←
                            (array_index (b_6730) (temp_6735)) ;;
                          ret (temp_6737)) ;;
                       '(s_6728 : state_t) ←
                        ( '(temp_6739 : uint_size) ←
                            ((usize 5) .* (i_6722)) ;;
                           '(temp_6741 : uint_size) ←
                            ((temp_6739) .+ (j_6731)) ;;
                           '(temp_6743 : uint_size) ←
                            ((usize 5) .* (i_6722)) ;;
                           '(temp_6745 : uint_size) ←
                            ((temp_6743) .+ (j_6731)) ;;
                           temp_6747 ←
                            (array_index (s_6728) (temp_6745)) ;;
                           '(temp_6750 : uint_size) ←
                            ((j_6731) .+ (usize 2)) ;;
                           '(temp_6752 : uint_size) ←
                            ((temp_6750) %% (usize 5)) ;;
                           temp_6754 ←
                            (array_index (b_6730) (temp_6752)) ;;
                           temp_6756 ←
                            ((not (u_6748)) .& (temp_6754)) ;;
                           temp_6758 ←
                            ((temp_6747) .^ (temp_6756)) ;;
                          ret (array_upd s_6728 (temp_6741) (temp_6758))) ;;
                      
                      @ret ((state_t)) (s_6728) } : code (CEfset (
                          [b_6730_loc])) [interface] _))) ;;
              
              @ret ((state_t '× row_t)) (prod_ce(s_6728, b_6730)) } : code (
                CEfset ([b_6730_loc])) [interface] _))) ;;
      let '(s_6728, b_6730) :=
        (temp_6760) : (state_t '× row_t) in
      
      @ret (state_t) (s_6728) } : code (CEfset ([b_6730_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_chi : package _ _ _ :=
  (chi).
Fail Next Obligation.


Notation "'iota_inp'" := (
  state_t '× int64 : choice_type) (in custom pack_type at level 2).
Notation "'iota_out'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Definition IOTA : nat :=
  (6771).
Program Definition iota
   : package (fset.fset0) [interface] [interface
  #val #[ IOTA ] : iota_inp → iota_out ] :=
  ([package #def #[ IOTA ] (temp_inp : iota_inp) : iota_out { 
    let '(s_6764 , rndconst_6766) := temp_inp : state_t '× int64 in
    ({ code  '(s_6764 : state_t) ←
        ( temp_6765 ←
            (array_index (s_6764) (usize 0)) ;;
           temp_6768 ←
            (uint64_classify (rndconst_6766)) ;;
           temp_6770 ←
            ((temp_6765) .^ (temp_6768)) ;;
          ret (array_upd s_6764 (usize 0) (temp_6770))) ;;
      
      @ret (state_t) (s_6764) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_iota : package _ _ _ :=
  (iota).
Fail Next Obligation.


Notation "'keccakf1600_inp'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'keccakf1600_out'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Definition KECCAKF1600 : nat :=
  (6786).
Program Definition keccakf1600
   : package (CEfset ([])) [interface #val #[ CHI ] : chi_inp → chi_out ;
  #val #[ IOTA ] : iota_inp → iota_out ; #val #[ PI ] : pi_inp → pi_out ;
  #val #[ RHO ] : rho_inp → rho_out ;
  #val #[ THETA ] : theta_inp → theta_out ] [interface
  #val #[ KECCAKF1600 ] : keccakf1600_inp → keccakf1600_out ] :=
  (
    [package #def #[ KECCAKF1600 ] (temp_inp : keccakf1600_inp) : keccakf1600_out { 
    let '(s_6772) := temp_inp : state_t in
    #import {sig #[ CHI ] : chi_inp → chi_out } as chi ;;
    let chi := fun x_0 => chi (x_0) in
    #import {sig #[ IOTA ] : iota_inp → iota_out } as iota ;;
    let iota := fun x_0 x_1 => iota (x_0,x_1) in
    #import {sig #[ PI ] : pi_inp → pi_out } as pi ;;
    let pi := fun x_0 => pi (x_0) in
    #import {sig #[ RHO ] : rho_inp → rho_out } as rho ;;
    let rho := fun x_0 => rho (x_0) in
    #import {sig #[ THETA ] : theta_inp → theta_out } as theta ;;
    let theta := fun x_0 => theta (x_0) in
    ({ code  '(s_6772 : (state_t)) ←
        (foldi' (usize 0) (rounds_v) s_6772 (L2 := CEfset ([])) (
              I2 := [interface #val #[ CHI ] : chi_inp → chi_out ;
              #val #[ IOTA ] : iota_inp → iota_out ;
              #val #[ PI ] : pi_inp → pi_out ;
              #val #[ RHO ] : rho_inp → rho_out ;
              #val #[ THETA ] : theta_inp → theta_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_6781 s_6772 =>
            ({ code  '(s_6772 : state_t) ←
                  (( '(temp_6774 : state_t) ←
                        (theta (s_6772)) ;;
                      ret (temp_6774))) ;;
                #put s_6772_loc := s_6772 ;;
              
               '(s_6772 : state_t) ←
                  (( '(temp_6776 : state_t) ←
                        (rho (s_6772)) ;;
                      ret (temp_6776))) ;;
                #put s_6772_loc := s_6772 ;;
              
               '(s_6772 : state_t) ←
                  (( '(temp_6778 : state_t) ←
                        (pi (s_6772)) ;;
                      ret (temp_6778))) ;;
                #put s_6772_loc := s_6772 ;;
              
               '(s_6772 : state_t) ←
                  (( '(temp_6780 : state_t) ←
                        (chi (s_6772)) ;;
                      ret (temp_6780))) ;;
                #put s_6772_loc := s_6772 ;;
              
               '(s_6772 : state_t) ←
                  (( temp_6783 ←
                        (array_index (roundconstants_v) (i_6781)) ;;
                       '(temp_6785 : state_t) ←
                        (iota (s_6772) (temp_6783)) ;;
                      ret (temp_6785))) ;;
                #put s_6772_loc := s_6772 ;;
              
              @ret ((state_t)) (s_6772) } : code (CEfset ([])) [interface
              #val #[ CHI ] : chi_inp → chi_out ;
              #val #[ IOTA ] : iota_inp → iota_out ;
              #val #[ PI ] : pi_inp → pi_out ;
              #val #[ RHO ] : rho_inp → rho_out ;
              #val #[ THETA ] : theta_inp → theta_out ] _))) ;;
      
      @ret (state_t) (s_6772) } : code (CEfset ([])) [interface
      #val #[ CHI ] : chi_inp → chi_out ;
      #val #[ IOTA ] : iota_inp → iota_out ;
      #val #[ PI ] : pi_inp → pi_out ; #val #[ RHO ] : rho_inp → rho_out ;
      #val #[ THETA ] : theta_inp → theta_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_keccakf1600 : package _ _ _ :=
  (seq_link keccakf1600 link_rest(
      package_chi,package_iota,package_pi,package_rho,package_theta)).
Fail Next Obligation.


Notation "'absorb_block_inp'" := (
  state_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'absorb_block_out'" := (
  state_t : choice_type) (in custom pack_type at level 2).
Definition ABSORB_BLOCK : nat :=
  (6812).
Program Definition absorb_block
   : package (CEfset ([])) [interface
  #val #[ U64_FROM_U8 ] : uint64_from_uint8_inp → uint64_from_uint8_out ;
  #val #[ KECCAKF1600 ] : keccakf1600_inp → keccakf1600_out ] [interface
  #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out ] :=
  (
    [package #def #[ ABSORB_BLOCK ] (temp_inp : absorb_block_inp) : absorb_block_out { 
    let '(s_6799 , block_6787) := temp_inp : state_t '× byte_seq in
    #import {sig #[ U64_FROM_U8 ] : uint64_from_uint8_inp → uint64_from_uint8_out } as uint64_from_uint8 ;;
    let uint64_from_uint8 := fun x_0 => uint64_from_uint8 (x_0) in
    #import {sig #[ KECCAKF1600 ] : keccakf1600_inp → keccakf1600_out } as keccakf1600 ;;
    let keccakf1600 := fun x_0 => keccakf1600 (x_0) in
    ({ code  '(temp_6789 : uint_size) ←
        (seq_len (block_6787)) ;;
       '(s_6799 : (state_t)) ←
        (foldi' (usize 0) (temp_6789) s_6799 (L2 := CEfset ([])) (
              I2 := [interface
              #val #[ U64_FROM_U8 ] : uint64_from_uint8_inp → uint64_from_uint8_out ;
              #val #[ KECCAKF1600 ] : keccakf1600_inp → keccakf1600_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_6790 s_6799 =>
            ({ code  '(w_6797 : uint_size) ←
                ( temp_6792 ←
                    ((i_6790) usize_shift_right (@repr U32 3)) ;;
                  ret (temp_6792)) ;;
               '(o_6805 : uint_size) ←
                ( temp_6794 ←
                    ((i_6790) .& (usize 7)) ;;
                   '(temp_6796 : uint_size) ←
                    ((usize 8) .* (temp_6794)) ;;
                  ret (temp_6796)) ;;
               '(s_6799 : state_t) ←
                ( temp_6800 ←
                    (array_index (s_6799) (w_6797)) ;;
                   temp_6802 ←
                    (seq_index (block_6787) (i_6790)) ;;
                   temp_6804 ←
                    (uint64_from_uint8 (temp_6802)) ;;
                   temp_6807 ←
                    ((temp_6804) shift_left (o_6805)) ;;
                   temp_6809 ←
                    ((temp_6800) .^ (temp_6807)) ;;
                  ret (array_upd s_6799 (w_6797) (temp_6809))) ;;
              
              @ret ((state_t)) (s_6799) } : code (fset.fset0) [interface
              #val #[ U64_FROM_U8 ] : uint64_from_uint8_inp → uint64_from_uint8_out
              ] _))) ;;
      
       '(temp_6811 : state_t) ←
        (keccakf1600 (s_6799)) ;;
      @ret (state_t) (temp_6811) } : code (CEfset ([])) [interface
      #val #[ U64_FROM_U8 ] : uint64_from_uint8_inp → uint64_from_uint8_out ;
      #val #[ KECCAKF1600 ] : keccakf1600_inp → keccakf1600_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_absorb_block : package _ _ _ :=
  (seq_link absorb_block link_rest(
      package_uint64_from_uint8,package_keccakf1600)).
Fail Next Obligation.

Definition out_6849_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 6852%nat)).
Notation "'squeeze_inp'" := (
  state_t '× uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'squeeze_out'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition SQUEEZE : nat :=
  (6853).
Program Definition squeeze
   : package (CEfset ([out_6849_loc])) [interface
  #val #[ U8_FROM_U64 ] : uint8_from_uint64_inp → uint8_from_uint64_out ;
  #val #[ KECCAKF1600 ] : keccakf1600_inp → keccakf1600_out ] [interface
  #val #[ SQUEEZE ] : squeeze_inp → squeeze_out ] :=
  ([package #def #[ SQUEEZE ] (temp_inp : squeeze_inp) : squeeze_out { 
    let '(
      s_6829 , nbytes_6813 , rate_6817) := temp_inp : state_t '× uint_size '× uint_size in
    #import {sig #[ U8_FROM_U64 ] : uint8_from_uint64_inp → uint8_from_uint64_out } as uint8_from_uint64 ;;
    let uint8_from_uint64 := fun x_0 => uint8_from_uint64 (x_0) in
    #import {sig #[ KECCAKF1600 ] : keccakf1600_inp → keccakf1600_out } as keccakf1600 ;;
    let keccakf1600 := fun x_0 => keccakf1600 (x_0) in
    ({ code  '(out_6849 : seq uint8) ←
          ( temp_6815 ←
              (seq_new_ (default : uint8) (nbytes_6813)) ;;
            ret (temp_6815)) ;;
        #put out_6849_loc := out_6849 ;;
       temp_6851 ←
        (foldi' (usize 0) (nbytes_6813) prod_ce(s_6829, out_6849) (
              L2 := CEfset ([out_6849_loc])) (I2 := [interface
              #val #[ U8_FROM_U64 ] : uint8_from_uint64_inp → uint8_from_uint64_out ;
              #val #[ KECCAKF1600 ] : keccakf1600_inp → keccakf1600_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_6816 '(
              s_6829,
              out_6849
            ) =>
            ({ code  '(pos_6820 : uint_size) ←
                ( '(temp_6819 : uint_size) ←
                    ((i_6816) %% (rate_6817)) ;;
                  ret (temp_6819)) ;;
               '(w_6827 : uint_size) ←
                ( temp_6822 ←
                    ((pos_6820) usize_shift_right (@repr U32 3)) ;;
                  ret (temp_6822)) ;;
               '(o_6831 : uint_size) ←
                ( temp_6824 ←
                    ((pos_6820) .& (usize 7)) ;;
                   '(temp_6826 : uint_size) ←
                    ((usize 8) .* (temp_6824)) ;;
                  ret (temp_6826)) ;;
               '(b_6838 : uint64) ←
                ( temp_6830 ←
                    (array_index (s_6829) (w_6827)) ;;
                   temp_6833 ←
                    ((temp_6830) shift_right (o_6831)) ;;
                   temp_6835 ←
                    (uint64_classify (@repr U64 255)) ;;
                   temp_6837 ←
                    ((temp_6833) .& (temp_6835)) ;;
                  ret (temp_6837)) ;;
               '(out_6849 : seq uint8) ←
                ( temp_6840 ←
                    (uint8_from_uint64 (b_6838)) ;;
                  ret (seq_upd out_6849 (i_6816) (temp_6840))) ;;
              
               '(temp_6842 : uint_size) ←
                ((i_6816) .+ (usize 1)) ;;
               '(temp_6844 : uint_size) ←
                ((temp_6842) %% (rate_6817)) ;;
               '(temp_6846 : bool_ChoiceEquality) ←
                ((temp_6844) =.? (usize 0)) ;;
               '(s_6829 : (state_t)) ←
                (if temp_6846:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(s_6829 : state_t) ←
                        (( '(temp_6848 : state_t) ←
                              (keccakf1600 (s_6829)) ;;
                            ret (temp_6848))) ;;
                      #put s_6829_loc := s_6829 ;;
                    
                    @ret ((state_t)) (s_6829) in
                    ({ code temp_then } : code (CEfset (
                          [out_6849_loc])) [interface
                      #val #[ KECCAKF1600 ] : keccakf1600_inp → keccakf1600_out
                      ] _))
                  else @ret ((state_t)) (s_6829)) ;;
              
              @ret ((state_t '× seq uint8)) (prod_ce(s_6829, out_6849
                )) } : code (CEfset ([out_6849_loc])) [interface
              #val #[ U8_FROM_U64 ] : uint8_from_uint64_inp → uint8_from_uint64_out ;
              #val #[ KECCAKF1600 ] : keccakf1600_inp → keccakf1600_out
              ] _))) ;;
      let '(s_6829, out_6849) :=
        (temp_6851) : (state_t '× seq uint8) in
      
      @ret (seq uint8) (out_6849) } : code (CEfset ([out_6849_loc])) [interface
      #val #[ U8_FROM_U64 ] : uint8_from_uint64_inp → uint8_from_uint64_out ;
      #val #[ KECCAKF1600 ] : keccakf1600_inp → keccakf1600_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_squeeze : package _ _ _ :=
  (seq_link squeeze link_rest(package_uint8_from_uint64,package_keccakf1600)).
Fail Next Obligation.

Definition s_6868_loc : ChoiceEqualityLocation :=
  ((state_t ; 6900%nat)).
Definition last_block_len_6873_loc : ChoiceEqualityLocation :=
  ((uint_size ; 6901%nat)).
Definition buf_6872_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 6902%nat)).
Notation "'keccak_inp'" := (
  uint_size '× byte_seq '× int8 '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'keccak_out'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition KECCAK : nat :=
  (6903).
Program Definition keccak
   : package (CEfset (
      [buf_6872_loc ; last_block_len_6873_loc ; s_6868_loc])) [interface
  #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out ;
  #val #[ SQUEEZE ] : squeeze_inp → squeeze_out ] [interface
  #val #[ KECCAK ] : keccak_inp → keccak_out ] :=
  ([package #def #[ KECCAK ] (temp_inp : keccak_inp) : keccak_out { 
    let '(
      rate_6854 , data_6859 , p_6880 , outbytes_6895) := temp_inp : uint_size '× byte_seq '× int8 '× uint_size in
    #import {sig #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out } as absorb_block ;;
    let absorb_block := fun x_0 x_1 => absorb_block (x_0,x_1) in
    #import {sig #[ SQUEEZE ] : squeeze_inp → squeeze_out } as squeeze ;;
    let squeeze := fun x_0 x_1 x_2 => squeeze (x_0,x_1,x_2) in
    ({ code  '(buf_6872 : seq uint8) ←
          ( temp_6856 ←
              (seq_new_ (default : uint8) (rate_6854)) ;;
            ret (temp_6856)) ;;
        #put buf_6872_loc := buf_6872 ;;
       '(last_block_len_6873 : uint_size) ←
          (ret (usize 0)) ;;
        #put last_block_len_6873_loc := last_block_len_6873 ;;
       '(s_6868 : state_t) ←
          ( '(temp_6858 : state_t) ←
              (array_new_ (default : uint64) (25)) ;;
            ret (temp_6858)) ;;
        #put s_6868_loc := s_6868 ;;
       '(temp_6861 : uint_size) ←
        (seq_num_chunks (data_6859) (rate_6854)) ;;
       temp_6899 ←
        (foldi' (usize 0) (temp_6861) prod_ce(
              buf_6872,
              last_block_len_6873,
              s_6868
            ) (L2 := CEfset (
                [buf_6872_loc ; last_block_len_6873_loc ; s_6868_loc])) (
              I2 := [interface
              #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out ;
              #val #[ SQUEEZE ] : squeeze_inp → squeeze_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_6862 '(
              buf_6872,
              last_block_len_6873,
              s_6868
            ) =>
            ({ code  temp_6879 ←
                ( '(temp_6864 : (uint_size '× seq uint8)) ←
                    (seq_get_chunk (data_6859) (rate_6854) (i_6862)) ;;
                  ret (temp_6864)) ;;
              let '(block_len_6865, block_6869) :=
                (temp_6879) : (uint_size '× seq uint8) in
               '(temp_6867 : bool_ChoiceEquality) ←
                ((block_len_6865) =.? (rate_6854)) ;;
               temp_6877 ←
                (if temp_6867:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(s_6868 : state_t) ←
                        (( '(temp_6871 : state_t) ←
                              (absorb_block (s_6868) (block_6869)) ;;
                            ret (temp_6871))) ;;
                      #put s_6868_loc := s_6868 ;;
                    
                    @ret ((seq uint8 '× uint_size '× state_t)) (prod_ce(
                        buf_6872,
                        last_block_len_6873,
                        s_6868
                      )) in
                    ({ code temp_then } : code (CEfset (
                          [buf_6872_loc ; last_block_len_6873_loc ; s_6868_loc])) [interface
                      #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out
                      ] _))
                  else  (({ code  '(buf_6872 : seq uint8) ←
                          (( '(temp_6875 : seq uint8) ←
                                (seq_update_start (buf_6872) (block_6869)) ;;
                              ret (temp_6875))) ;;
                        #put buf_6872_loc := buf_6872 ;;
                      
                       '(last_block_len_6873 : uint_size) ←
                          ((ret (block_len_6865))) ;;
                        #put last_block_len_6873_loc := last_block_len_6873 ;;
                      
                      @ret ((seq uint8 '× uint_size '× state_t)) (prod_ce(
                          buf_6872,
                          last_block_len_6873,
                          s_6868
                        )) } : code (CEfset (
                          [buf_6872_loc ; last_block_len_6873_loc ; s_6868_loc])) [interface] _))) ;;
              let '(buf_6872, last_block_len_6873, s_6868) :=
                (temp_6877) : (seq uint8 '× uint_size '× state_t) in
              
              @ret ((seq uint8 '× uint_size '× state_t)) (prod_ce(
                  buf_6872,
                  last_block_len_6873,
                  s_6868
                )) } : code (CEfset (
                  [buf_6872_loc ; last_block_len_6873_loc ; s_6868_loc])) [interface
              #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out
              ] _))) ;;
      let '(buf_6872, last_block_len_6873, s_6868) :=
        (temp_6899) : (seq uint8 '× uint_size '× state_t) in
      
       '(buf_6872 : seq uint8) ←
        ( '(temp_6882 : int8) ←
            (secret (p_6880)) ;;
          ret (seq_upd buf_6872 (last_block_len_6873) (temp_6882))) ;;
      
       '(buf_6872 : seq uint8) ←
        ( '(temp_6884 : uint_size) ←
            ((rate_6854) .- (usize 1)) ;;
           '(temp_6886 : uint_size) ←
            ((rate_6854) .- (usize 1)) ;;
           '(temp_6888 : uint8) ←
            (seq_index (buf_6872) (temp_6886)) ;;
           '(temp_6890 : int8) ←
            (secret (@repr U8 128)) ;;
           temp_6892 ←
            ((temp_6888) .| (temp_6890)) ;;
          ret (seq_upd buf_6872 (temp_6884) (temp_6892))) ;;
      
       '(s_6868 : state_t) ←
          (( '(temp_6894 : state_t) ←
                (absorb_block (s_6868) (buf_6872)) ;;
              ret (temp_6894))) ;;
        #put s_6868_loc := s_6868 ;;
      
       '(temp_6897 : byte_seq) ←
        (squeeze (s_6868) (outbytes_6895) (rate_6854)) ;;
      @ret (byte_seq) (temp_6897) } : code (CEfset (
          [buf_6872_loc ; last_block_len_6873_loc ; s_6868_loc])) [interface
      #val #[ ABSORB_BLOCK ] : absorb_block_inp → absorb_block_out ;
      #val #[ SQUEEZE ] : squeeze_inp → squeeze_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_keccak : package _ _ _ :=
  (seq_link keccak link_rest(package_absorb_block,package_squeeze)).
Fail Next Obligation.


Notation "'sha3224_inp'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sha3224_out'" := (
  digest224_t : choice_type) (in custom pack_type at level 2).
Definition SHA3224 : nat :=
  (6910).
Program Definition sha3224
   : package (CEfset ([])) [interface
  #val #[ KECCAK ] : keccak_inp → keccak_out ] [interface
  #val #[ SHA3224 ] : sha3224_inp → sha3224_out ] :=
  ([package #def #[ SHA3224 ] (temp_inp : sha3224_inp) : sha3224_out { 
    let '(data_6904) := temp_inp : byte_seq in
    #import {sig #[ KECCAK ] : keccak_inp → keccak_out } as keccak ;;
    let keccak := fun x_0 x_1 x_2 x_3 => keccak (x_0,x_1,x_2,x_3) in
    ({ code  '(t_6907 : seq uint8) ←
        ( '(temp_6906 : byte_seq) ←
            (keccak (sha3224_rate_v) (data_6904) (@repr U8 6) (usize 28)) ;;
          ret (temp_6906)) ;;
       '(temp_6909 : digest224_t) ←
        (array_from_seq (28) (t_6907)) ;;
      @ret (digest224_t) (temp_6909) } : code (CEfset ([])) [interface
      #val #[ KECCAK ] : keccak_inp → keccak_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_sha3224 : package _ _ _ :=
  (seq_link sha3224 link_rest(package_keccak)).
Fail Next Obligation.


Notation "'sha3256_inp'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sha3256_out'" := (
  digest256_t : choice_type) (in custom pack_type at level 2).
Definition SHA3256 : nat :=
  (6917).
Program Definition sha3256
   : package (CEfset ([])) [interface
  #val #[ KECCAK ] : keccak_inp → keccak_out ] [interface
  #val #[ SHA3256 ] : sha3256_inp → sha3256_out ] :=
  ([package #def #[ SHA3256 ] (temp_inp : sha3256_inp) : sha3256_out { 
    let '(data_6911) := temp_inp : byte_seq in
    #import {sig #[ KECCAK ] : keccak_inp → keccak_out } as keccak ;;
    let keccak := fun x_0 x_1 x_2 x_3 => keccak (x_0,x_1,x_2,x_3) in
    ({ code  '(t_6914 : seq uint8) ←
        ( '(temp_6913 : byte_seq) ←
            (keccak (sha3256_rate_v) (data_6911) (@repr U8 6) (usize 32)) ;;
          ret (temp_6913)) ;;
       '(temp_6916 : digest256_t) ←
        (array_from_seq (32) (t_6914)) ;;
      @ret (digest256_t) (temp_6916) } : code (CEfset ([])) [interface
      #val #[ KECCAK ] : keccak_inp → keccak_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_sha3256 : package _ _ _ :=
  (seq_link sha3256 link_rest(package_keccak)).
Fail Next Obligation.


Notation "'sha3384_inp'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sha3384_out'" := (
  digest384_t : choice_type) (in custom pack_type at level 2).
Definition SHA3384 : nat :=
  (6924).
Program Definition sha3384
   : package (CEfset ([])) [interface
  #val #[ KECCAK ] : keccak_inp → keccak_out ] [interface
  #val #[ SHA3384 ] : sha3384_inp → sha3384_out ] :=
  ([package #def #[ SHA3384 ] (temp_inp : sha3384_inp) : sha3384_out { 
    let '(data_6918) := temp_inp : byte_seq in
    #import {sig #[ KECCAK ] : keccak_inp → keccak_out } as keccak ;;
    let keccak := fun x_0 x_1 x_2 x_3 => keccak (x_0,x_1,x_2,x_3) in
    ({ code  '(t_6921 : seq uint8) ←
        ( '(temp_6920 : byte_seq) ←
            (keccak (sha3384_rate_v) (data_6918) (@repr U8 6) (usize 48)) ;;
          ret (temp_6920)) ;;
       '(temp_6923 : digest384_t) ←
        (array_from_seq (48) (t_6921)) ;;
      @ret (digest384_t) (temp_6923) } : code (CEfset ([])) [interface
      #val #[ KECCAK ] : keccak_inp → keccak_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_sha3384 : package _ _ _ :=
  (seq_link sha3384 link_rest(package_keccak)).
Fail Next Obligation.


Notation "'sha3512_inp'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sha3512_out'" := (
  digest512_t : choice_type) (in custom pack_type at level 2).
Definition SHA3512 : nat :=
  (6931).
Program Definition sha3512
   : package (CEfset ([])) [interface
  #val #[ KECCAK ] : keccak_inp → keccak_out ] [interface
  #val #[ SHA3512 ] : sha3512_inp → sha3512_out ] :=
  ([package #def #[ SHA3512 ] (temp_inp : sha3512_inp) : sha3512_out { 
    let '(data_6925) := temp_inp : byte_seq in
    #import {sig #[ KECCAK ] : keccak_inp → keccak_out } as keccak ;;
    let keccak := fun x_0 x_1 x_2 x_3 => keccak (x_0,x_1,x_2,x_3) in
    ({ code  '(t_6928 : seq uint8) ←
        ( '(temp_6927 : byte_seq) ←
            (keccak (sha3512_rate_v) (data_6925) (@repr U8 6) (usize 64)) ;;
          ret (temp_6927)) ;;
       '(temp_6930 : digest512_t) ←
        (array_from_seq (64) (t_6928)) ;;
      @ret (digest512_t) (temp_6930) } : code (CEfset ([])) [interface
      #val #[ KECCAK ] : keccak_inp → keccak_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_sha3512 : package _ _ _ :=
  (seq_link sha3512 link_rest(package_keccak)).
Fail Next Obligation.


Notation "'shake128_inp'" := (
  byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'shake128_out'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition SHAKE128 : nat :=
  (6936).
Program Definition shake128
   : package (CEfset ([])) [interface
  #val #[ KECCAK ] : keccak_inp → keccak_out ] [interface
  #val #[ SHAKE128 ] : shake128_inp → shake128_out ] :=
  ([package #def #[ SHAKE128 ] (temp_inp : shake128_inp) : shake128_out { 
    let '(data_6932 , outlen_6933) := temp_inp : byte_seq '× uint_size in
    #import {sig #[ KECCAK ] : keccak_inp → keccak_out } as keccak ;;
    let keccak := fun x_0 x_1 x_2 x_3 => keccak (x_0,x_1,x_2,x_3) in
    ({ code  '(temp_6935 : byte_seq) ←
        (keccak (shake128_rate_v) (data_6932) (@repr U8 31) (outlen_6933)) ;;
      @ret (byte_seq) (temp_6935) } : code (CEfset ([])) [interface
      #val #[ KECCAK ] : keccak_inp → keccak_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_shake128 : package _ _ _ :=
  (seq_link shake128 link_rest(package_keccak)).
Fail Next Obligation.


Notation "'shake256_inp'" := (
  byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'shake256_out'" := (
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition SHAKE256 : nat :=
  (6941).
Program Definition shake256
   : package (CEfset ([])) [interface
  #val #[ KECCAK ] : keccak_inp → keccak_out ] [interface
  #val #[ SHAKE256 ] : shake256_inp → shake256_out ] :=
  ([package #def #[ SHAKE256 ] (temp_inp : shake256_inp) : shake256_out { 
    let '(data_6937 , outlen_6938) := temp_inp : byte_seq '× uint_size in
    #import {sig #[ KECCAK ] : keccak_inp → keccak_out } as keccak ;;
    let keccak := fun x_0 x_1 x_2 x_3 => keccak (x_0,x_1,x_2,x_3) in
    ({ code  '(temp_6940 : byte_seq) ←
        (keccak (shake256_rate_v) (data_6937) (@repr U8 31) (outlen_6938)) ;;
      @ret (byte_seq) (temp_6940) } : code (CEfset ([])) [interface
      #val #[ KECCAK ] : keccak_inp → keccak_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_shake256 : package _ _ _ :=
  (seq_link shake256 link_rest(package_keccak)).
Fail Next Obligation.

