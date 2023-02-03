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


Notation "'fadd_inp'" :=(
  element_t '× element_t : choice_type) (in custom pack_type at level 2).
Notation "'fadd_inp'" :=(element_t '× element_t : ChoiceEquality) (at level 2).
Notation "'fadd_out'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Notation "'fadd_out'" :=(element_t : ChoiceEquality) (at level 2).
Definition FADD : nat :=
  2.
Program Definition fadd (x_0 : element_t) (y_1 : element_t)
  : both (fset.fset0) [interface] (element_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((lift_to_both0 x_0) .^ (
          lift_to_both0 y_1))
      ) : both (fset.fset0) [interface] (element_t)).
Fail Next Obligation.

Definition sh_4_loc : ChoiceEqualityLocation :=
  (uint128 ; 5%nat).
Definition res_3_loc : ChoiceEqualityLocation :=
  (element_t ; 6%nat).
Notation "'fmul_inp'" :=(
  element_t '× element_t : choice_type) (in custom pack_type at level 2).
Notation "'fmul_inp'" :=(element_t '× element_t : ChoiceEquality) (at level 2).
Notation "'fmul_out'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Notation "'fmul_out'" :=(element_t : ChoiceEquality) (at level 2).
Definition FMUL : nat :=
  10.
Program Definition fmul (x_7 : element_t) (y_9 : element_t)
  : both (CEfset ([res_3_loc ; sh_4_loc])) [interface] (element_t) :=
  ((letbm res_3 : element_t loc( res_3_loc ) :=
        secret (lift_to_both0 (@repr U128 0)) in
      letbm sh_4 : uint128 loc( sh_4_loc ) := lift_to_both0 x_7 in
      letb '(res_3, sh_4) :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 128)) prod_ce(res_3, sh_4) (L := (CEfset (
                [res_3_loc ; sh_4_loc]))) (I := [interface]) (fun i_8 '(
              res_3,
              sh_4
            ) =>
            letb '(res_3) :=
              if (uint128_declassify ((lift_to_both0 y_9) .& ((secret (
                        lift_to_both0 (@repr U128 1))) shift_left ((
                        lift_to_both0 (usize 127)) .- (
                        lift_to_both0 i_8))))) !=.? (uint128_declassify (
                  secret (lift_to_both0 (@repr U128 0)))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([res_3_loc ; sh_4_loc])) (
                L2 := CEfset ([res_3_loc ; sh_4_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm res_3 loc( res_3_loc ) :=
                  (lift_to_both0 res_3) .^ (lift_to_both0 sh_4) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 res_3)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 res_3)
               in
            letb '(sh_4) :=
              if (uint128_declassify ((lift_to_both0 sh_4) .& (secret (
                      lift_to_both0 (@repr U128 1))))) !=.? (
                uint128_declassify (secret (lift_to_both0 (
                      @repr U128 0)))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([res_3_loc ; sh_4_loc])) (
                L2 := CEfset ([res_3_loc ; sh_4_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm sh_4 loc( sh_4_loc ) :=
                  ((lift_to_both0 sh_4) shift_right (lift_to_both0 (
                        usize 1))) .^ (lift_to_both0 irred_v) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 sh_4)
                )
              else  lift_scope (L1 := CEfset ([res_3_loc ; sh_4_loc])) (
                L2 := CEfset ([res_3_loc ; sh_4_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm sh_4 loc( sh_4_loc ) :=
                  (lift_to_both0 sh_4) shift_right (lift_to_both0 (usize 1)) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 sh_4)
                ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 res_3,
                lift_to_both0 sh_4
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 res_3)
      ) : both (CEfset ([res_3_loc ; sh_4_loc])) [interface] (element_t)).
Fail Next Obligation.


Notation "'encode_inp'" :=(
  gf128_block_t : choice_type) (in custom pack_type at level 2).
Notation "'encode_inp'" :=(gf128_block_t : ChoiceEquality) (at level 2).
Notation "'encode_out'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Notation "'encode_out'" :=(element_t : ChoiceEquality) (at level 2).
Definition ENCODE : nat :=
  12.
Program Definition encode (block_11 : gf128_block_t)
  : both (fset.fset0) [interface] (element_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (uint128_from_be_bytes (
          array_from_seq (16) (array_to_seq (lift_to_both0 block_11))))
      ) : both (fset.fset0) [interface] (element_t)).
Fail Next Obligation.


Notation "'decode_inp'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Notation "'decode_inp'" :=(element_t : ChoiceEquality) (at level 2).
Notation "'decode_out'" :=(
  gf128_block_t : choice_type) (in custom pack_type at level 2).
Notation "'decode_out'" :=(gf128_block_t : ChoiceEquality) (at level 2).
Definition DECODE : nat :=
  14.
Program Definition decode (e_13 : element_t)
  : both (fset.fset0) [interface] (gf128_block_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (
          blocksize_v) (array_to_seq (uint128_to_be_bytes (
            lift_to_both0 e_13))))
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
  18.
Program Definition update (r_17 : element_t) (block_15 : gf128_block_t) (
    acc_16 : element_t)
  : both (CEfset ([res_3_loc ; sh_4_loc])) [interface] (element_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fmul (fadd (encode (
              lift_to_both0 block_15)) (lift_to_both0 acc_16)) (
          lift_to_both0 r_17))
      ) : both (CEfset ([res_3_loc ; sh_4_loc])) [interface] (element_t)).
Fail Next Obligation.

Definition last_block_21_loc : ChoiceEqualityLocation :=
  (gf128_block_t ; 22%nat).
Definition acc_19_loc : ChoiceEqualityLocation :=
  (uint128 ; 23%nat).
Definition block_20_loc : ChoiceEqualityLocation :=
  (gf128_block_t ; 24%nat).
Notation "'poly_inp'" :=(
  byte_seq '× element_t : choice_type) (in custom pack_type at level 2).
Notation "'poly_inp'" :=(byte_seq '× element_t : ChoiceEquality) (at level 2).
Notation "'poly_out'" :=(
  element_t : choice_type) (in custom pack_type at level 2).
Notation "'poly_out'" :=(element_t : ChoiceEquality) (at level 2).
Definition POLY : nat :=
  33.
Program Definition poly (msg_25 : byte_seq) (r_31 : element_t)
  : both (CEfset (
      [res_3_loc ; sh_4_loc ; acc_19_loc ; block_20_loc ; last_block_21_loc])) [interface] (
    element_t) :=
  ((letb l_26 : uint_size := seq_len (lift_to_both0 msg_25) in
      letb n_blocks_27 : uint_size :=
        (lift_to_both0 l_26) ./ (lift_to_both0 blocksize_v) in
      letb rem_28 : uint_size :=
        (lift_to_both0 l_26) .% (lift_to_both0 blocksize_v) in
      letbm acc_19 : uint128 loc( acc_19_loc ) :=
        secret (lift_to_both0 (@repr U128 0)) in
      letb acc_19 :=
        foldi_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 n_blocks_27) acc_19 (L := (CEfset (
                [res_3_loc ; sh_4_loc ; acc_19_loc ; block_20_loc ; last_block_21_loc]))) (
            I := [interface]) (fun i_29 acc_19 =>
            letb k_30 : uint_size :=
              (lift_to_both0 i_29) .* (lift_to_both0 blocksize_v) in
            letbm block_20 : gf128_block_t loc( block_20_loc ) :=
              array_new_ (default : uint8) (blocksize_v) in
            letbm block_20 loc( block_20_loc ) :=
              array_update_start (lift_to_both0 block_20) (seq_slice_range (
                  lift_to_both0 msg_25) (prod_b(
                    lift_to_both0 k_30,
                    (lift_to_both0 k_30) .+ (lift_to_both0 blocksize_v)
                  ))) in
            letbm acc_19 loc( acc_19_loc ) :=
              update (lift_to_both0 r_31) (lift_to_both0 block_20) (
                lift_to_both0 acc_19) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 acc_19)
            ) in
      letb '(acc_19) :=
        if (lift_to_both0 rem_28) !=.? (lift_to_both0 (
            usize 0)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [res_3_loc ; sh_4_loc ; acc_19_loc ; block_20_loc ; last_block_21_loc])) (
          L2 := CEfset (
            [res_3_loc ; sh_4_loc ; acc_19_loc ; block_20_loc ; last_block_21_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb k_32 : uint_size :=
            (lift_to_both0 n_blocks_27) .* (lift_to_both0 blocksize_v) in
          letbm last_block_21 : gf128_block_t loc( last_block_21_loc ) :=
            array_new_ (default : uint8) (blocksize_v) in
          letbm last_block_21 loc( last_block_21_loc ) :=
            array_update_slice (lift_to_both0 last_block_21) (lift_to_both0 (
                usize 0)) (lift_to_both0 msg_25) (lift_to_both0 k_32) (
              lift_to_both0 rem_28) in
          letbm acc_19 loc( acc_19_loc ) :=
            update (lift_to_both0 r_31) (lift_to_both0 last_block_21) (
              lift_to_both0 acc_19) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 acc_19)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 acc_19)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 acc_19)
      ) : both (CEfset (
        [res_3_loc ; sh_4_loc ; acc_19_loc ; block_20_loc ; last_block_21_loc])) [interface] (
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
  39.
Program Definition gmac (text_37 : byte_seq) (k_35 : gf128_key_t)
  : both (CEfset (
      [res_3_loc ; sh_4_loc ; acc_19_loc ; block_20_loc ; last_block_21_loc])) [interface] (
    gf128_tag_t) :=
  ((letb s_34 : gf128_block_t := array_new_ (default : uint8) (blocksize_v) in
      letb r_36 : uint128 :=
        encode (array_from_seq (blocksize_v) (
            array_to_seq (lift_to_both0 k_35))) in
      letb a_38 : uint128 :=
        poly (lift_to_both0 text_37) (lift_to_both0 r_36) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (
          blocksize_v) (array_to_seq (decode (fadd (lift_to_both0 a_38) (
              encode (lift_to_both0 s_34))))))
      ) : both (CEfset (
        [res_3_loc ; sh_4_loc ; acc_19_loc ; block_20_loc ; last_block_21_loc])) [interface] (
      gf128_tag_t)).
Fail Next Obligation.

