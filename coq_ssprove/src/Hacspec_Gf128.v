(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp Require Import ssrZ word.
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


Notation "'fadd_inp'" :=(
  element_t '× element_t : choice_type) (in custom pack_type at level 2).
Notation "'fadd_inp'" :=(element_t '× element_t : ChoiceEquality) (at level 2).
Notation "'fadd_out'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Notation "'fadd_out'" :=(element_t : ChoiceEquality) (at level 2).
Definition FADD : nat :=
  398.
Program Definition fadd (x_396 : element_t) (y_397 : element_t)
  : both (fset.fset0) [interface] (element_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((lift_to_both0 x_396) .^ (
          lift_to_both0 y_397))
      ) : both (fset.fset0) [interface] (element_t)).
Fail Next Obligation.

Definition res_399_loc : ChoiceEqualityLocation :=
  (element_t ; 401%nat).
Definition sh_400_loc : ChoiceEqualityLocation :=
  (uint128 ; 402%nat).
Notation "'fmul_inp'" :=(
  element_t '× element_t : choice_type) (in custom pack_type at level 2).
Notation "'fmul_inp'" :=(element_t '× element_t : ChoiceEquality) (at level 2).
Notation "'fmul_out'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Notation "'fmul_out'" :=(element_t : ChoiceEquality) (at level 2).
Definition FMUL : nat :=
  406.
Program Definition fmul (x_403 : element_t) (y_405 : element_t)
  : both (CEfset ([res_399_loc ; sh_400_loc])) [interface] (element_t) :=
  ((letbm res_399 : element_t loc( res_399_loc ) :=
        secret (lift_to_both0 (@repr U128 0)) in
      letbm sh_400 : uint128 loc( sh_400_loc ) := lift_to_both0 x_403 in
      letb '(res_399, sh_400) :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 128)) prod_ce(res_399, sh_400) (L := (CEfset (
                [res_399_loc ; sh_400_loc]))) (I := [interface]) (fun i_404 '(
              res_399,
              sh_400
            ) =>
            letb '(res_399) :=
              if (uint128_declassify ((lift_to_both0 y_405) .& ((secret (
                        lift_to_both0 (@repr U128 1))) shift_left ((
                        lift_to_both0 (usize 127)) .- (
                        lift_to_both0 i_404))))) !=.? (uint128_declassify (
                  secret (lift_to_both0 (@repr U128 0)))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([res_399_loc ; sh_400_loc])) (
                L2 := CEfset ([res_399_loc ; sh_400_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm res_399 loc( res_399_loc ) :=
                  (lift_to_both0 res_399) .^ (lift_to_both0 sh_400) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 res_399)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 res_399)
               in
            letb '(sh_400) :=
              if (uint128_declassify ((lift_to_both0 sh_400) .& (secret (
                      lift_to_both0 (@repr U128 1))))) !=.? (
                uint128_declassify (secret (lift_to_both0 (
                      @repr U128 0)))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([res_399_loc ; sh_400_loc])) (
                L2 := CEfset ([res_399_loc ; sh_400_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm sh_400 loc( sh_400_loc ) :=
                  ((lift_to_both0 sh_400) shift_right (lift_to_both0 (
                        usize 1))) .^ (lift_to_both0 irred_v) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 sh_400)
                )
              else  lift_scope (L1 := CEfset ([res_399_loc ; sh_400_loc])) (
                L2 := CEfset ([res_399_loc ; sh_400_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm sh_400 loc( sh_400_loc ) :=
                  (lift_to_both0 sh_400) shift_right (lift_to_both0 (
                      usize 1)) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 sh_400)
                ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 res_399,
                lift_to_both0 sh_400
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 res_399)
      ) : both (CEfset ([res_399_loc ; sh_400_loc])) [interface] (element_t)).
Fail Next Obligation.


Notation "'encode_inp'" :=(
  gf128_block_t : choice_type) (in custom pack_type at level 2).
Notation "'encode_inp'" :=(gf128_block_t : ChoiceEquality) (at level 2).
Notation "'encode_out'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Notation "'encode_out'" :=(element_t : ChoiceEquality) (at level 2).
Definition ENCODE : nat :=
  408.
Program Definition encode (block_407 : gf128_block_t)
  : both (fset.fset0) [interface] (element_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (uint128_from_be_bytes (
          array_from_seq (16) (array_to_seq (lift_to_both0 block_407))))
      ) : both (fset.fset0) [interface] (element_t)).
Fail Next Obligation.


Notation "'decode_inp'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Notation "'decode_inp'" :=(element_t : ChoiceEquality) (at level 2).
Notation "'decode_out'" :=(
  gf128_block_t : choice_type) (in custom pack_type at level 2).
Notation "'decode_out'" :=(gf128_block_t : ChoiceEquality) (at level 2).
Definition DECODE : nat :=
  410.
Program Definition decode (e_409 : element_t)
  : both (fset.fset0) [interface] (gf128_block_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (
          blocksize_v) (array_to_seq (uint128_to_be_bytes (
            lift_to_both0 e_409))))
      ) : both (fset.fset0) [interface] (gf128_block_t)).
Fail Next Obligation.


Notation "'update_inp'" :=(
  element_t '× gf128_block_t '× element_t : choice_type) (in custom pack_type at level 2).
Notation "'update_inp'" :=(
  element_t '× gf128_block_t '× element_t : ChoiceEquality) (at level 2).
Notation "'update_out'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Notation "'update_out'" :=(element_t : ChoiceEquality) (at level 2).
Definition UPDATE : nat :=
  414.
Program Definition update (r_413 : element_t) (block_411 : gf128_block_t) (
    acc_412 : element_t)
  : both (CEfset ([res_399_loc ; sh_400_loc])) [interface] (element_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fmul (fadd (encode (
              lift_to_both0 block_411)) (lift_to_both0 acc_412)) (
          lift_to_both0 r_413))
      ) : both (CEfset ([res_399_loc ; sh_400_loc])) [interface] (element_t)).
Fail Next Obligation.

Definition acc_415_loc : ChoiceEqualityLocation :=
  (uint128 ; 418%nat).
Definition block_416_loc : ChoiceEqualityLocation :=
  (gf128_block_t ; 419%nat).
Definition last_block_417_loc : ChoiceEqualityLocation :=
  (gf128_block_t ; 420%nat).
Notation "'poly_inp'" :=(
  byte_seq '× element_t : choice_type) (in custom pack_type at level 2).
Notation "'poly_inp'" :=(byte_seq '× element_t : ChoiceEquality) (at level 2).
Notation "'poly_out'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Notation "'poly_out'" :=(element_t : ChoiceEquality) (at level 2).
Definition POLY : nat :=
  429.
Program Definition poly (msg_421 : byte_seq) (r_427 : element_t)
  : both (CEfset (
      [res_399_loc ; sh_400_loc ; acc_415_loc ; block_416_loc ; last_block_417_loc])) [interface] (
    element_t) :=
  ((letb l_422 : uint_size := seq_len (lift_to_both0 msg_421) in
      letb n_blocks_423 : uint_size :=
        (lift_to_both0 l_422) ./ (lift_to_both0 blocksize_v) in
      letb rem_424 : uint_size :=
        (lift_to_both0 l_422) %% (lift_to_both0 blocksize_v) in
      letbm acc_415 : uint128 loc( acc_415_loc ) :=
        secret (lift_to_both0 (@repr U128 0)) in
      letb acc_415 :=
        foldi_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 n_blocks_423) acc_415 (L := (CEfset (
                [res_399_loc ; sh_400_loc ; acc_415_loc ; block_416_loc ; last_block_417_loc]))) (
            I := [interface]) (fun i_425 acc_415 =>
            letb k_426 : uint_size :=
              (lift_to_both0 i_425) .* (lift_to_both0 blocksize_v) in
            letbm block_416 : gf128_block_t loc( block_416_loc ) :=
              array_new_ (default : uint8) (blocksize_v) in
            letbm block_416 loc( block_416_loc ) :=
              array_update_start (lift_to_both0 block_416) (seq_slice_range (
                  lift_to_both0 msg_421) (prod_b(
                    lift_to_both0 k_426,
                    (lift_to_both0 k_426) .+ (lift_to_both0 blocksize_v)
                  ))) in
            letbm acc_415 loc( acc_415_loc ) :=
              update (lift_to_both0 r_427) (lift_to_both0 block_416) (
                lift_to_both0 acc_415) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 acc_415)
            ) in
      letb '(acc_415) :=
        if (lift_to_both0 rem_424) !=.? (lift_to_both0 (
            usize 0)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [res_399_loc ; sh_400_loc ; acc_415_loc ; block_416_loc ; last_block_417_loc])) (
          L2 := CEfset (
            [res_399_loc ; sh_400_loc ; acc_415_loc ; block_416_loc ; last_block_417_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb k_428 : uint_size :=
            (lift_to_both0 n_blocks_423) .* (lift_to_both0 blocksize_v) in
          letbm last_block_417 : gf128_block_t loc( last_block_417_loc ) :=
            array_new_ (default : uint8) (blocksize_v) in
          letbm last_block_417 loc( last_block_417_loc ) :=
            array_update_slice (lift_to_both0 last_block_417) (lift_to_both0 (
                usize 0)) (lift_to_both0 msg_421) (lift_to_both0 k_428) (
              lift_to_both0 rem_424) in
          letbm acc_415 loc( acc_415_loc ) :=
            update (lift_to_both0 r_427) (lift_to_both0 last_block_417) (
              lift_to_both0 acc_415) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 acc_415)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 acc_415)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 acc_415)
      ) : both (CEfset (
        [res_399_loc ; sh_400_loc ; acc_415_loc ; block_416_loc ; last_block_417_loc])) [interface] (
      element_t)).
Fail Next Obligation.


Notation "'gmac_inp'" :=(
  byte_seq '× gf128_key_t : choice_type) (in custom pack_type at level 2).
Notation "'gmac_inp'" :=(
  byte_seq '× gf128_key_t : ChoiceEquality) (at level 2).
Notation "'gmac_out'" :=(
  gf128_tag_t : choice_type) (in custom pack_type at level 2).
Notation "'gmac_out'" :=(gf128_tag_t : ChoiceEquality) (at level 2).
Definition GMAC : nat :=
  435.
Program Definition gmac (text_433 : byte_seq) (k_431 : gf128_key_t)
  : both (CEfset (
      [res_399_loc ; sh_400_loc ; acc_415_loc ; block_416_loc ; last_block_417_loc])) [interface] (
    gf128_tag_t) :=
  ((letb s_430 : gf128_block_t := array_new_ (default : uint8) (blocksize_v) in
      letb r_432 : uint128 :=
        encode (array_from_seq (blocksize_v) (
            array_to_seq (lift_to_both0 k_431))) in
      letb a_434 : uint128 :=
        poly (lift_to_both0 text_433) (lift_to_both0 r_432) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (
          blocksize_v) (array_to_seq (decode (fadd (lift_to_both0 a_434) (
              encode (lift_to_both0 s_430))))))
      ) : both (CEfset (
        [res_399_loc ; sh_400_loc ; acc_415_loc ; block_416_loc ; last_block_417_loc])) [interface] (
      gf128_tag_t)).
Fail Next Obligation.

