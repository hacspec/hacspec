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


Definition blocksize_v : uint_size :=
  usize 16.

Definition gf128_block_t := nseq (uint8) (blocksize_v).

Definition gf128_key_t := nseq (uint8) (blocksize_v).

Definition gf128_tag_t := nseq (uint8) (blocksize_v).

Notation "'element_t'" := (uint128) : hacspec_scope.

Definition irred_v : element_t :=
  secret (@repr U128 299076299051606071403356588563077529600).

Definition fadd_pure (x_777 : element_t) (y_778 : element_t) : element_t :=
  ((x_777) .^ (y_778)).
Definition fadd_pure_code
  (x_777 : element_t)
  (y_778 : element_t)
  : code fset.fset0 [interface] (@ct (element_t)) :=
  lift_to_code (fadd_pure x_777 y_778).


Notation "'fadd_state_inp'" := (
  element_t '× element_t : choice_type) (in custom pack_type at level 2).
Notation "'fadd_state_out'" := (
  element_t : choice_type) (in custom pack_type at level 2).
Definition FADD_STATE : nat :=
  (781).
Program Definition fadd_state
   : package (fset.fset0) [interface] [interface
  #val #[ FADD_STATE ] : fadd_state_inp → fadd_state_out ] :=
  ([package #def #[ FADD_STATE ] (temp_inp : fadd_state_inp) : fadd_state_out { 
    let '(x_777 , y_778) := temp_inp : element_t '× element_t in
    ({ code  temp_780 ←
        ((x_777) .^ (y_778)) ;;
      @ret (element_t) (temp_780) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_fadd_state : package _ _ _ :=
  (fadd_state).
Fail Next Obligation.

Notation "'fadd_inp'" :=(
  element_t '× element_t : choice_type) (in custom pack_type at level 2).
Notation "'fadd_out'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Definition FADD : nat :=
  (782).
Program Definition fadd
  (x_777 : element_t)
  (y_778 : element_t)
  :both (fset.fset0) [interface] (element_t) :=
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((lift_to_both0 x_777) .^ (
      lift_to_both0 y_778))
  .
Fail Next Obligation.

Definition fmul_pure (x_787 : element_t) (y_788 : element_t) : element_t :=
  let res_783 : element_t :=
    secret (@repr U128 0) in 
  let sh_784 : uint128 :=
    x_787 in 
  let '(res_783, sh_784) :=
    Hacspec_Lib_Pre.foldi (usize 0) (usize 128) (res_783, sh_784)
      (fun i_789 '(res_783, sh_784) =>
      let '(res_783) :=
        ((if (((uint128_declassify (((y_788) .& (((secret (
                              @repr U128 1)) shift_left (((usize 127) .- (
                                i_789)))))))) !=.? (uint128_declassify (secret (
                      @repr U128 0))))):bool_ChoiceEquality
            then (let res_783 :=
                ((res_783) .^ (sh_784)) in 
              (res_783))
            else ((res_783))) : T _) in 
      let '(sh_784) :=
        ((if (((uint128_declassify (((sh_784) .& (secret (
                          @repr U128 1))))) !=.? (uint128_declassify (secret (
                      @repr U128 0))))):bool_ChoiceEquality
            then (let sh_784 :=
                ((((sh_784) shift_right (usize 1))) .^ (irred_v)) in 
              (sh_784))
            else (let sh_784 :=
                ((sh_784) shift_right (usize 1)) in 
              (sh_784))) : T _) in 
      prod_ce(res_783, sh_784)) in 
  res_783.
Definition fmul_pure_code
  (x_787 : element_t)
  (y_788 : element_t)
  : code fset.fset0 [interface] (@ct (element_t)) :=
  lift_to_code (fmul_pure x_787 y_788).

Definition sh_784_loc : ChoiceEqualityLocation :=
  ((uint128 ; 830%nat)).
Definition res_783_loc : ChoiceEqualityLocation :=
  ((element_t ; 831%nat)).
Notation "'fmul_state_inp'" := (
  element_t '× element_t : choice_type) (in custom pack_type at level 2).
Notation "'fmul_state_out'" := (
  element_t : choice_type) (in custom pack_type at level 2).
Definition FMUL_STATE : nat :=
  (832).
Program Definition fmul_state
   : package (CEfset ([res_783_loc ; sh_784_loc])) [interface] [interface
  #val #[ FMUL_STATE ] : fmul_state_inp → fmul_state_out ] :=
  ([package #def #[ FMUL_STATE ] (temp_inp : fmul_state_inp) : fmul_state_out { 
    let '(x_787 , y_788) := temp_inp : element_t '× element_t in
    ({ code  '(res_783 : element_t) ←
          ( '(temp_791 : int128) ←
              (secret (@repr U128 0)) ;;
            ret (temp_791)) ;;
        #put res_783_loc := res_783 ;;
       '(sh_784 : uint128) ←
          (ret (x_787)) ;;
        #put sh_784_loc := sh_784 ;;
       temp_829 ←
        (foldi' (usize 0) (usize 128) prod_ce(res_783, sh_784) (L2 := CEfset (
                [res_783_loc ; sh_784_loc])) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_789 '(
              res_783,
              sh_784
            ) =>
            ({ code  '(temp_793 : int128) ←
                (secret (@repr U128 1)) ;;
               '(temp_795 : uint_size) ←
                ((usize 127) .- (i_789)) ;;
               temp_797 ←
                ((temp_793) shift_left (temp_795)) ;;
               temp_799 ←
                ((y_788) .& (temp_797)) ;;
               '(temp_801 : element_t) ←
                (uint128_declassify (temp_799)) ;;
               '(temp_803 : int128) ←
                (secret (@repr U128 0)) ;;
               '(temp_805 : uint128) ←
                (uint128_declassify (temp_803)) ;;
               '(temp_807 : bool_ChoiceEquality) ←
                ((temp_801) !=.? (temp_805)) ;;
               '(res_783 : (uint128)) ←
                (if temp_807:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(res_783 : uint128) ←
                        (( temp_809 ←
                              ((res_783) .^ (sh_784)) ;;
                            ret (temp_809))) ;;
                      #put res_783_loc := res_783 ;;
                    
                    @ret ((uint128)) (res_783) in
                    ({ code temp_then } : code (CEfset (
                          [res_783_loc ; sh_784_loc])) [interface] _))
                  else @ret ((uint128)) (res_783)) ;;
              
               '(temp_811 : int128) ←
                (secret (@repr U128 1)) ;;
               temp_813 ←
                ((sh_784) .& (temp_811)) ;;
               '(temp_815 : uint128) ←
                (uint128_declassify (temp_813)) ;;
               '(temp_817 : int128) ←
                (secret (@repr U128 0)) ;;
               '(temp_819 : uint128) ←
                (uint128_declassify (temp_817)) ;;
               '(temp_821 : bool_ChoiceEquality) ←
                ((temp_815) !=.? (temp_819)) ;;
               '(sh_784 : (uint128)) ←
                (if temp_821:bool_ChoiceEquality
                  then (*not state*) (let temp_then :=  '(sh_784 : uint128) ←
                        (( temp_823 ←
                              ((sh_784) shift_right (usize 1)) ;;
                             temp_825 ←
                              ((temp_823) .^ (irred_v)) ;;
                            ret (temp_825))) ;;
                      #put sh_784_loc := sh_784 ;;
                    
                    @ret ((uint128)) (sh_784) in
                    ({ code temp_then } : code (CEfset (
                          [res_783_loc ; sh_784_loc])) [interface] _))
                  else  (({ code  '(sh_784 : uint128) ←
                          (( temp_827 ←
                                ((sh_784) shift_right (usize 1)) ;;
                              ret (temp_827))) ;;
                        #put sh_784_loc := sh_784 ;;
                      
                      @ret ((uint128)) (sh_784) } : code (CEfset (
                          [res_783_loc ; sh_784_loc])) [interface] _))) ;;
              
              @ret ((uint128 '× uint128)) (prod_ce(res_783, sh_784)) } : code (
                CEfset ([res_783_loc ; sh_784_loc])) [interface] _))) ;;
      let '(res_783, sh_784) :=
        (temp_829) : (uint128 '× uint128) in
      
      @ret (uint128) (res_783) } : code (CEfset (
          [res_783_loc ; sh_784_loc])) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_fmul_state : package _ _ _ :=
  (fmul_state).
Fail Next Obligation.

Notation "'fmul_inp'" :=(
  element_t '× element_t : choice_type) (in custom pack_type at level 2).
Notation "'fmul_out'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Definition FMUL : nat :=
  (833).
Program Definition fmul
  (x_787 : element_t)
  (y_788 : element_t)
  :both (CEfset ([res_783_loc ; sh_784_loc])) [interface] (element_t) :=
  letbm res_783 : element_t loc( res_783_loc ) :=
    secret (lift_to_both0 (@repr U128 0)) in
  letbm sh_784 : uint128 loc( sh_784_loc ) := lift_to_both0 x_787 in
  letb '(res_783, sh_784) :=
    foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (usize 128)) prod_ce(
        res_783,
        sh_784
      ) (L := (CEfset ([res_783_loc ; sh_784_loc]))) (I := (
        [interface])) (fun i_789 '(res_783, sh_784) =>
      letb 'res_783 :=
        if (uint128_declassify ((lift_to_both0 y_788) .& ((secret (
                  lift_to_both0 (@repr U128 1))) shift_left ((lift_to_both0 (
                    usize 127)) .- (lift_to_both0 i_789))))) !=.? (
          uint128_declassify (secret (lift_to_both0 (
                @repr U128 0)))) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
          [res_783_loc ; sh_784_loc])) (L2 := CEfset (
          [res_783_loc ; sh_784_loc])) (H_loc_incl := _) (H_opsig_incl := _)a (
          letbm res_783 loc( res_783_loc ) :=
            (lift_to_both0 res_783) .^ (lift_to_both0 sh_784) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 res_783)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 res_783)
         in
      letb 'sh_784 :=
        if (uint128_declassify ((lift_to_both0 sh_784) .& (secret (
                lift_to_both0 (@repr U128 1))))) !=.? (uint128_declassify (
            secret (lift_to_both0 (@repr U128 0)))) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
          [res_783_loc ; sh_784_loc])) (L2 := CEfset (
          [res_783_loc ; sh_784_loc])) (H_loc_incl := _) (H_opsig_incl := _)a (
          letbm sh_784 loc( sh_784_loc ) :=
            ((lift_to_both0 sh_784) shift_right (lift_to_both0 (usize 1))) .^ (
              lift_to_both0 irred_v) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 sh_784)
          )
        else  lift_scope (L1 := CEfset (
          [res_783_loc ; sh_784_loc])) (L2 := CEfset (
          [res_783_loc ; sh_784_loc])) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm sh_784 loc( sh_784_loc ) :=
            (lift_to_both0 sh_784) shift_right (lift_to_both0 (usize 1)) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 sh_784)
          ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 res_783,
          lift_to_both0 sh_784
        ))
      ) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 res_783)
  .
Fail Next Obligation.

Definition encode_pure (block_834 : gf128_block_t) : element_t :=
  uint128_from_be_bytes (array_from_seq (16) (array_to_seq (block_834))).
Definition encode_pure_code
  (block_834 : gf128_block_t)
  : code fset.fset0 [interface] (@ct (element_t)) :=
  lift_to_code (encode_pure block_834).


Notation "'encode_state_inp'" := (
  gf128_block_t : choice_type) (in custom pack_type at level 2).
Notation "'encode_state_out'" := (
  element_t : choice_type) (in custom pack_type at level 2).
Definition ENCODE_STATE : nat :=
  (841).
Program Definition encode_state
   : package (fset.fset0) [interface] [interface
  #val #[ ENCODE_STATE ] : encode_state_inp → encode_state_out ] :=
  (
    [package #def #[ ENCODE_STATE ] (temp_inp : encode_state_inp) : encode_state_out { 
    let '(block_834) := temp_inp : gf128_block_t in
    ({ code  '(temp_836 : seq uint8) ←
        (array_to_seq (block_834)) ;;
       '(temp_838 : uint128_word_t) ←
        (array_from_seq (16) (temp_836)) ;;
       '(temp_840 : int128) ←
        (uint128_from_be_bytes (temp_838)) ;;
      @ret (uint128) (temp_840) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_encode_state : package _ _ _ :=
  (encode_state).
Fail Next Obligation.

Notation "'encode_inp'" :=(
  gf128_block_t : choice_type) (in custom pack_type at level 2).
Notation "'encode_out'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Definition ENCODE : nat :=
  (842).
Program Definition encode
  (block_834 : gf128_block_t)
  :both (fset.fset0) [interface] (element_t) :=
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (uint128_from_be_bytes (
      array_from_seq (16) (array_to_seq (lift_to_both0 block_834))))
  .
Fail Next Obligation.

Definition decode_pure (e_843 : element_t) : gf128_block_t :=
  array_from_seq (blocksize_v) (array_to_seq (uint128_to_be_bytes (e_843))).
Definition decode_pure_code
  (e_843 : element_t)
  : code fset.fset0 [interface] (@ct (gf128_block_t)) :=
  lift_to_code (decode_pure e_843).


Notation "'decode_state_inp'" := (
  element_t : choice_type) (in custom pack_type at level 2).
Notation "'decode_state_out'" := (
  gf128_block_t : choice_type) (in custom pack_type at level 2).
Definition DECODE_STATE : nat :=
  (850).
Program Definition decode_state
   : package (fset.fset0) [interface] [interface
  #val #[ DECODE_STATE ] : decode_state_inp → decode_state_out ] :=
  (
    [package #def #[ DECODE_STATE ] (temp_inp : decode_state_inp) : decode_state_out { 
    let '(e_843) := temp_inp : element_t in
    ({ code  '(temp_845 : uint128_word_t) ←
        (uint128_to_be_bytes (e_843)) ;;
       '(temp_847 : seq uint8) ←
        (array_to_seq (temp_845)) ;;
       '(temp_849 : gf128_block_t) ←
        (array_from_seq (blocksize_v) (temp_847)) ;;
      @ret (gf128_block_t) (temp_849) } : code (fset.fset0) [interface] _)
    }]).
Fail Next Obligation.
Program Definition package_decode_state : package _ _ _ :=
  (decode_state).
Fail Next Obligation.

Notation "'decode_inp'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Notation "'decode_out'" :=(
  gf128_block_t : choice_type) (in custom pack_type at level 2).
Definition DECODE : nat :=
  (851).
Program Definition decode
  (e_843 : element_t)
  :both (fset.fset0) [interface] (gf128_block_t) :=
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (
      blocksize_v) (array_to_seq (uint128_to_be_bytes (lift_to_both0 e_843))))
  .
Fail Next Obligation.

Definition update_pure
  (r_852 : element_t)
  (block_853 : gf128_block_t)
  (acc_854 : element_t)
  : element_t :=
  fmul (fadd (encode (block_853)) (acc_854)) (r_852).
Definition update_pure_code
  (r_852 : element_t)
  (block_853 : gf128_block_t)
  (acc_854 : element_t)
  : code fset.fset0 [interface] (@ct (element_t)) :=
  lift_to_code (update_pure r_852 block_853 acc_854).


Notation "'update_state_inp'" := (
  element_t '× gf128_block_t '× element_t : choice_type) (in custom pack_type at level 2).
Notation "'update_state_out'" := (
  element_t : choice_type) (in custom pack_type at level 2).
Definition UPDATE_STATE : nat :=
  (861).
Program Definition update_state
   : package (CEfset ([])) [interface
  #val #[ ENCODE_STATE ] : encode_state_inp → encode_state_out ;
  #val #[ FADD_STATE ] : fadd_state_inp → fadd_state_out ;
  #val #[ FMUL_STATE ] : fmul_state_inp → fmul_state_out ] [interface
  #val #[ UPDATE_STATE ] : update_state_inp → update_state_out ] :=
  (
    [package #def #[ UPDATE_STATE ] (temp_inp : update_state_inp) : update_state_out { 
    let '(
      r_852 , block_853 , acc_854) := temp_inp : element_t '× gf128_block_t '× element_t in
    #import {sig #[ ENCODE_STATE ] : encode_state_inp → encode_state_out } as encode_state ;;
    let encode_state := fun x_0 => encode_state (x_0) in
    #import {sig #[ FADD_STATE ] : fadd_state_inp → fadd_state_out } as fadd_state ;;
    let fadd_state := fun x_0 x_1 => fadd_state (x_0,x_1) in
    #import {sig #[ FMUL_STATE ] : fmul_state_inp → fmul_state_out } as fmul_state ;;
    let fmul_state := fun x_0 x_1 => fmul_state (x_0,x_1) in
    ({ code  temp_856 ←
        (encode (block_853)) ;;
       temp_858 ←
        (fadd (temp_856) (acc_854)) ;;
       temp_860 ←
        (fmul (temp_858) (r_852)) ;;
      @ret (element_t) (temp_860) } : code (CEfset ([])) [interface
      #val #[ ENCODE_STATE ] : encode_state_inp → encode_state_out ;
      #val #[ FADD_STATE ] : fadd_state_inp → fadd_state_out ;
      #val #[ FMUL_STATE ] : fmul_state_inp → fmul_state_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_update_state : package _ _ _ :=
  (seq_link update_state link_rest(
      package_encode_state,package_fadd_state,package_fmul_state)).
Fail Next Obligation.

Notation "'update_inp'" :=(
  element_t '× gf128_block_t '× element_t : choice_type) (in custom pack_type at level 2).
Notation "'update_out'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Definition UPDATE : nat :=
  (862).
Program Definition update
  (r_852 : element_t)
  (block_853 : gf128_block_t)
  (acc_854 : element_t)
  :both (CEfset ([])) [interface #val #[ ENCODE ] : encode_inp → encode_out ;
  #val #[ FADD ] : fadd_inp → fadd_out ;
  #val #[ FMUL ] : fmul_inp → fmul_out ] (element_t) :=
  #import {sig #[ ENCODE ] : encode_inp → encode_out } as encode ;;
  let encode := fun x_0 => encode (x_0) in
  #import {sig #[ FADD ] : fadd_inp → fadd_out } as fadd ;;
  let fadd := fun x_0 x_1 => fadd (x_0,x_1) in
  #import {sig #[ FMUL ] : fmul_inp → fmul_out } as fmul ;;
  let fmul := fun x_0 x_1 => fmul (x_0,x_1) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fmul (fadd (encode (
          lift_to_both0 block_853)) (lift_to_both0 acc_854)) (
      lift_to_both0 r_852))
  .
Fail Next Obligation.

Definition poly_pure (msg_869 : byte_seq) (r_870 : element_t) : element_t :=
  let l_871 : uint_size :=
    seq_len (msg_869) in 
  let n_blocks_872 : uint_size :=
    ((l_871) ./ (blocksize_v)) in 
  let rem_873 : uint_size :=
    ((l_871) %% (blocksize_v)) in 
  let acc_863 : uint128 :=
    secret (@repr U128 0) in 
  let acc_863 :=
    Hacspec_Lib_Pre.foldi (usize 0) (n_blocks_872) acc_863
      (fun i_874 acc_863 =>
      let k_875 : uint_size :=
        ((i_874) .* (blocksize_v)) in 
      let block_864 : gf128_block_t :=
        array_new_ (default : uint8) (blocksize_v) in 
      let block_864 :=
        array_update_start (block_864) (seq_slice_range (msg_869) (prod_ce(
              k_875,
              ((k_875) .+ (blocksize_v))
            ))) in 
      let acc_863 :=
        update (r_870) (block_864) (acc_863) in 
      (acc_863)) in 
  let '(acc_863) :=
    ((if (((rem_873) !=.? (usize 0))):bool_ChoiceEquality
        then (let k_876 : uint_size :=
            ((n_blocks_872) .* (blocksize_v)) in 
          let last_block_865 : gf128_block_t :=
            array_new_ (default : uint8) (blocksize_v) in 
          let last_block_865 :=
            array_update_slice (last_block_865) (usize 0) (msg_869) (k_876) (
              rem_873) in 
          let acc_863 :=
            update (r_870) (last_block_865) (acc_863) in 
          (acc_863))
        else ((acc_863))) : T _) in 
  acc_863.
Definition poly_pure_code
  (msg_869 : byte_seq)
  (r_870 : element_t)
  : code fset.fset0 [interface] (@ct (element_t)) :=
  lift_to_code (poly_pure msg_869 r_870).

Definition last_block_865_loc : ChoiceEqualityLocation :=
  ((gf128_block_t ; 907%nat)).
Definition acc_863_loc : ChoiceEqualityLocation :=
  ((uint128 ; 908%nat)).
Definition block_864_loc : ChoiceEqualityLocation :=
  ((gf128_block_t ; 909%nat)).
Notation "'poly_state_inp'" := (
  byte_seq '× element_t : choice_type) (in custom pack_type at level 2).
Notation "'poly_state_out'" := (
  element_t : choice_type) (in custom pack_type at level 2).
Definition POLY_STATE : nat :=
  (910).
Program Definition poly_state
   : package (CEfset (
      [acc_863_loc ; block_864_loc ; last_block_865_loc])) [interface
  #val #[ UPDATE_STATE ] : update_state_inp → update_state_out ] [interface
  #val #[ POLY_STATE ] : poly_state_inp → poly_state_out ] :=
  ([package #def #[ POLY_STATE ] (temp_inp : poly_state_inp) : poly_state_out { 
    let '(msg_869 , r_870) := temp_inp : byte_seq '× element_t in
    #import {sig #[ UPDATE_STATE ] : update_state_inp → update_state_out } as update_state ;;
    let update_state := fun x_0 x_1 x_2 => update_state (x_0,x_1,x_2) in
    ({ code  '(l_871 : uint_size) ←
        ( '(temp_878 : uint_size) ←
            (seq_len (msg_869)) ;;
          ret (temp_878)) ;;
       '(n_blocks_872 : uint_size) ←
        ( '(temp_880 : uint_size) ←
            ((l_871) ./ (blocksize_v)) ;;
          ret (temp_880)) ;;
       '(rem_873 : uint_size) ←
        ( '(temp_882 : uint_size) ←
            ((l_871) %% (blocksize_v)) ;;
          ret (temp_882)) ;;
       '(acc_863 : uint128) ←
          ( '(temp_884 : int128) ←
              (secret (@repr U128 0)) ;;
            ret (temp_884)) ;;
        #put acc_863_loc := acc_863 ;;
       '(acc_863 : (uint128)) ←
        (foldi' (usize 0) (n_blocks_872) acc_863 (L2 := CEfset (
                [acc_863_loc ; block_864_loc ; last_block_865_loc])) (
              I2 := [interface
              #val #[ UPDATE_STATE ] : update_state_inp → update_state_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_874 acc_863 =>
            ({ code  '(k_875 : uint_size) ←
                ( '(temp_886 : uint_size) ←
                    ((i_874) .* (blocksize_v)) ;;
                  ret (temp_886)) ;;
               '(block_864 : gf128_block_t) ←
                  ( '(temp_888 : gf128_block_t) ←
                      (array_new_ (default : uint8) (blocksize_v)) ;;
                    ret (temp_888)) ;;
                #put block_864_loc := block_864 ;;
               '(block_864 : gf128_block_t) ←
                  (( '(temp_890 : uint_size) ←
                        ((k_875) .+ (blocksize_v)) ;;
                       '(temp_892 : byte_seq) ←
                        (seq_slice_range (msg_869) (prod_ce(k_875, temp_890
                            ))) ;;
                       '(temp_894 : gf128_block_t) ←
                        (array_update_start (block_864) (temp_892)) ;;
                      ret (temp_894))) ;;
                #put block_864_loc := block_864 ;;
              
               '(acc_863 : uint128) ←
                  (( temp_896 ←
                        (update (r_870) (block_864) (acc_863)) ;;
                      ret (temp_896))) ;;
                #put acc_863_loc := acc_863 ;;
              
              @ret ((uint128)) (acc_863) } : code (CEfset (
                  [acc_863_loc ; block_864_loc])) [interface] _))) ;;
      
       '(temp_898 : bool_ChoiceEquality) ←
        ((rem_873) !=.? (usize 0)) ;;
       '(acc_863 : (uint128)) ←
        (if temp_898:bool_ChoiceEquality
          then (*not state*) (let temp_then :=  '(k_876 : uint_size) ←
              ( '(temp_900 : uint_size) ←
                  ((n_blocks_872) .* (blocksize_v)) ;;
                ret (temp_900)) ;;
             '(last_block_865 : gf128_block_t) ←
                ( '(temp_902 : gf128_block_t) ←
                    (array_new_ (default : uint8) (blocksize_v)) ;;
                  ret (temp_902)) ;;
              #put last_block_865_loc := last_block_865 ;;
             '(last_block_865 : gf128_block_t) ←
                (( '(temp_904 : gf128_block_t) ←
                      (array_update_slice (last_block_865) (usize 0) (msg_869) (
                          k_876) (rem_873)) ;;
                    ret (temp_904))) ;;
              #put last_block_865_loc := last_block_865 ;;
            
             '(acc_863 : uint128) ←
                (( temp_906 ←
                      (update (r_870) (last_block_865) (acc_863)) ;;
                    ret (temp_906))) ;;
              #put acc_863_loc := acc_863 ;;
            
            @ret ((uint128)) (acc_863) in
            ({ code temp_then } : code (CEfset (
                  [acc_863_loc ; block_864_loc ; last_block_865_loc])) [interface] _))
          else @ret ((uint128)) (acc_863)) ;;
      
      @ret (uint128) (acc_863) } : code (CEfset (
          [acc_863_loc ; block_864_loc ; last_block_865_loc])) [interface
      #val #[ UPDATE_STATE ] : update_state_inp → update_state_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_poly_state : package _ _ _ :=
  (seq_link poly_state link_rest(package_update_state)).
Fail Next Obligation.

Notation "'poly_inp'" :=(
  byte_seq '× element_t : choice_type) (in custom pack_type at level 2).
Notation "'poly_out'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Definition POLY : nat :=
  (911).
Program Definition poly
  (msg_869 : byte_seq)
  (r_870 : element_t)
  :both (CEfset ([acc_863_loc ; block_864_loc ; last_block_865_loc])) [interface
  #val #[ UPDATE ] : update_inp → update_out ] (element_t) :=
  #import {sig #[ UPDATE ] : update_inp → update_out } as update ;;
  let update := fun x_0 x_1 x_2 => update (x_0,x_1,x_2) in
  letb l_871 : uint_size := seq_len (lift_to_both0 msg_869) in
  letb n_blocks_872 : uint_size :=
    (lift_to_both0 l_871) ./ (lift_to_both0 blocksize_v) in
  letb rem_873 : uint_size :=
    (lift_to_both0 l_871) %% (lift_to_both0 blocksize_v) in
  letbm acc_863 : uint128 loc( acc_863_loc ) :=
    secret (lift_to_both0 (@repr U128 0)) in
  letb acc_863 :=
    foldi_both' (lift_to_both0 (usize 0)) (
        lift_to_both0 n_blocks_872) acc_863 (L := (CEfset (
          [acc_863_loc ; block_864_loc ; last_block_865_loc]))) (I := (
        [interface #val #[ UPDATE ] : update_inp → update_out
        ])) (fun i_874 acc_863 =>
      letb k_875 : uint_size :=
        (lift_to_both0 i_874) .* (lift_to_both0 blocksize_v) in
      letbm block_864 : gf128_block_t loc( block_864_loc ) :=
        array_new_ (default : uint8) (blocksize_v) in
      letbm block_864 loc( block_864_loc ) :=
        array_update_start (lift_to_both0 block_864) (seq_slice_range (
            lift_to_both0 msg_869) (prod_b(
              lift_to_both0 k_875,
              (lift_to_both0 k_875) .+ (lift_to_both0 blocksize_v)
            ))) in
      letbm acc_863 loc( acc_863_loc ) :=
        update (lift_to_both0 r_870) (lift_to_both0 block_864) (
          lift_to_both0 acc_863) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 acc_863)
      ) in
  letb 'acc_863 :=
    if (lift_to_both0 rem_873) !=.? (lift_to_both0 (
        usize 0)) :bool_ChoiceEquality
    then lift_scope (L1 := CEfset (
      [acc_863_loc ; block_864_loc ; last_block_865_loc])) (L2 := CEfset (
      [acc_863_loc ; block_864_loc ; last_block_865_loc])) (H_loc_incl := _) (H_opsig_incl := _)a (
      letb k_876 : uint_size :=
        (lift_to_both0 n_blocks_872) .* (lift_to_both0 blocksize_v) in
      letbm last_block_865 : gf128_block_t loc( last_block_865_loc ) :=
        array_new_ (default : uint8) (blocksize_v) in
      letbm last_block_865 loc( last_block_865_loc ) :=
        array_update_slice (lift_to_both0 last_block_865) (lift_to_both0 (
            usize 0)) (lift_to_both0 msg_869) (lift_to_both0 k_876) (
          lift_to_both0 rem_873) in
      letbm acc_863 loc( acc_863_loc ) :=
        update (lift_to_both0 r_870) (lift_to_both0 last_block_865) (
          lift_to_both0 acc_863) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 acc_863)
      )
    else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
      lift_to_both0 acc_863)
     in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 acc_863)
  .
Fail Next Obligation.

Definition gmac_pure
  (text_912 : byte_seq)
  (k_913 : gf128_key_t)
  : gf128_tag_t :=
  let s_914 : gf128_block_t :=
    array_new_ (default : uint8) (blocksize_v) in 
  let r_915 : uint128 :=
    encode (array_from_seq (blocksize_v) (array_to_seq (k_913))) in 
  let a_916 : uint128 :=
    poly (text_912) (r_915) in 
  array_from_seq (blocksize_v) (array_to_seq (decode (fadd (a_916) (encode (
          s_914))))).
Definition gmac_pure_code
  (text_912 : byte_seq)
  (k_913 : gf128_key_t)
  : code fset.fset0 [interface] (@ct (gf128_tag_t)) :=
  lift_to_code (gmac_pure text_912 k_913).


Notation "'gmac_state_inp'" := (
  byte_seq '× gf128_key_t : choice_type) (in custom pack_type at level 2).
Notation "'gmac_state_out'" := (
  gf128_tag_t : choice_type) (in custom pack_type at level 2).
Definition GMAC_STATE : nat :=
  (937).
Program Definition gmac_state
   : package (CEfset ([])) [interface
  #val #[ DECODE_STATE ] : decode_state_inp → decode_state_out ;
  #val #[ ENCODE_STATE ] : encode_state_inp → encode_state_out ;
  #val #[ FADD_STATE ] : fadd_state_inp → fadd_state_out ;
  #val #[ POLY_STATE ] : poly_state_inp → poly_state_out ] [interface
  #val #[ GMAC_STATE ] : gmac_state_inp → gmac_state_out ] :=
  ([package #def #[ GMAC_STATE ] (temp_inp : gmac_state_inp) : gmac_state_out { 
    let '(text_912 , k_913) := temp_inp : byte_seq '× gf128_key_t in
    #import {sig #[ DECODE_STATE ] : decode_state_inp → decode_state_out } as decode_state ;;
    let decode_state := fun x_0 => decode_state (x_0) in
    #import {sig #[ ENCODE_STATE ] : encode_state_inp → encode_state_out } as encode_state ;;
    let encode_state := fun x_0 => encode_state (x_0) in
    #import {sig #[ FADD_STATE ] : fadd_state_inp → fadd_state_out } as fadd_state ;;
    let fadd_state := fun x_0 x_1 => fadd_state (x_0,x_1) in
    #import {sig #[ POLY_STATE ] : poly_state_inp → poly_state_out } as poly_state ;;
    let poly_state := fun x_0 x_1 => poly_state (x_0,x_1) in
    ({ code  '(s_914 : gf128_block_t) ←
        ( '(temp_918 : gf128_block_t) ←
            (array_new_ (default : uint8) (blocksize_v)) ;;
          ret (temp_918)) ;;
       '(r_915 : uint128) ←
        ( '(temp_920 : seq uint8) ←
            (array_to_seq (k_913)) ;;
           '(temp_922 : gf128_block_t) ←
            (array_from_seq (blocksize_v) (temp_920)) ;;
           temp_924 ←
            (encode (temp_922)) ;;
          ret (temp_924)) ;;
       '(a_916 : uint128) ←
        ( temp_926 ←
            (poly (text_912) (r_915)) ;;
          ret (temp_926)) ;;
       temp_928 ←
        (encode (s_914)) ;;
       temp_930 ←
        (fadd (a_916) (temp_928)) ;;
       temp_932 ←
        (decode (temp_930)) ;;
       '(temp_934 : seq uint8) ←
        (array_to_seq (temp_932)) ;;
       '(temp_936 : gf128_tag_t) ←
        (array_from_seq (blocksize_v) (temp_934)) ;;
      @ret (gf128_tag_t) (temp_936) } : code (CEfset ([])) [interface
      #val #[ DECODE_STATE ] : decode_state_inp → decode_state_out ;
      #val #[ ENCODE_STATE ] : encode_state_inp → encode_state_out ;
      #val #[ FADD_STATE ] : fadd_state_inp → fadd_state_out ;
      #val #[ POLY_STATE ] : poly_state_inp → poly_state_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_gmac_state : package _ _ _ :=
  (seq_link gmac_state link_rest(
      package_decode_state,package_encode_state,package_fadd_state,package_poly_state)).
Fail Next Obligation.

Notation "'gmac_inp'" :=(
  byte_seq '× gf128_key_t : choice_type) (in custom pack_type at level 2).
Notation "'gmac_out'" :=(
  gf128_tag_t : choice_type) (in custom pack_type at level 2).
Definition GMAC : nat :=
  (938).
Program Definition gmac
  (text_912 : byte_seq)
  (k_913 : gf128_key_t)
  :both (CEfset ([])) [interface #val #[ DECODE ] : decode_inp → decode_out ;
  #val #[ ENCODE ] : encode_inp → encode_out ;
  #val #[ FADD ] : fadd_inp → fadd_out ;
  #val #[ POLY ] : poly_inp → poly_out ] (gf128_tag_t) :=
  #import {sig #[ DECODE ] : decode_inp → decode_out } as decode ;;
  let decode := fun x_0 => decode (x_0) in
  #import {sig #[ ENCODE ] : encode_inp → encode_out } as encode ;;
  let encode := fun x_0 => encode (x_0) in
  #import {sig #[ FADD ] : fadd_inp → fadd_out } as fadd ;;
  let fadd := fun x_0 x_1 => fadd (x_0,x_1) in
  #import {sig #[ POLY ] : poly_inp → poly_out } as poly ;;
  let poly := fun x_0 x_1 => poly (x_0,x_1) in
  letb s_914 : gf128_block_t := array_new_ (default : uint8) (blocksize_v) in
  letb r_915 : uint128 :=
    encode (array_from_seq (blocksize_v) (
        array_to_seq (lift_to_both0 k_913))) in
  letb a_916 : uint128 := poly (lift_to_both0 text_912) (lift_to_both0 r_915) in
  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (
      blocksize_v) (array_to_seq (decode (fadd (lift_to_both0 a_916) (encode (
            lift_to_both0 s_914))))))
  .
Fail Next Obligation.

