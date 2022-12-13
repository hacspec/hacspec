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


Definition rounds_v : uint_size :=
  usize 24.

Definition sha3224_rate_v : uint_size :=
  usize 144.

Definition sha3256_rate_v : uint_size :=
  usize 136.

Definition sha3384_rate_v : uint_size :=
  usize 104.

Definition sha3512_rate_v : uint_size :=
  usize 72.

Definition shake128_rate_v : uint_size :=
  usize 168.

Definition shake256_rate_v : uint_size :=
  usize 136.

Definition state_t := nseq (uint64) (usize 25).

Definition row_t := nseq (uint64) (usize 5).

Definition digest224_t := nseq (uint8) (usize 28).

Definition digest256_t := nseq (uint8) (usize 32).

Definition digest384_t := nseq (uint8) (usize 48).

Definition digest512_t := nseq (uint8) (usize 64).

Definition round_constants_t := nseq (int64) (rounds_v).

Definition rotation_constants_t := nseq (uint_size) (usize 25).

Definition roundconstants_v : round_constants_t :=
  array_from_list int64 [
    (@repr U64 1) : int64;
    (@repr U64 32898) : int64;
    (@repr U64 9223372036854808714) : int64;
    (@repr U64 9223372039002292224) : int64;
    (@repr U64 32907) : int64;
    (@repr U64 2147483649) : int64;
    (@repr U64 9223372039002292353) : int64;
    (@repr U64 9223372036854808585) : int64;
    (@repr U64 138) : int64;
    (@repr U64 136) : int64;
    (@repr U64 2147516425) : int64;
    (@repr U64 2147483658) : int64;
    (@repr U64 2147516555) : int64;
    (@repr U64 9223372036854775947) : int64;
    (@repr U64 9223372036854808713) : int64;
    (@repr U64 9223372036854808579) : int64;
    (@repr U64 9223372036854808578) : int64;
    (@repr U64 9223372036854775936) : int64;
    (@repr U64 32778) : int64;
    (@repr U64 9223372039002259466) : int64;
    (@repr U64 9223372039002292353) : int64;
    (@repr U64 9223372036854808704) : int64;
    (@repr U64 2147483649) : int64;
    (@repr U64 9223372039002292232) : int64
  ].

Definition rotc_v : rotation_constants_t :=
  array_from_list uint_size [
    (usize 0) : uint_size;
    (usize 1) : uint_size;
    (usize 62) : uint_size;
    (usize 28) : uint_size;
    (usize 27) : uint_size;
    (usize 36) : uint_size;
    (usize 44) : uint_size;
    (usize 6) : uint_size;
    (usize 55) : uint_size;
    (usize 20) : uint_size;
    (usize 3) : uint_size;
    (usize 10) : uint_size;
    (usize 43) : uint_size;
    (usize 25) : uint_size;
    (usize 39) : uint_size;
    (usize 41) : uint_size;
    (usize 45) : uint_size;
    (usize 15) : uint_size;
    (usize 21) : uint_size;
    (usize 8) : uint_size;
    (usize 18) : uint_size;
    (usize 2) : uint_size;
    (usize 61) : uint_size;
    (usize 56) : uint_size;
    (usize 14) : uint_size
  ].

Definition pi_v : rotation_constants_t :=
  array_from_list uint_size [
    (usize 0) : uint_size;
    (usize 6) : uint_size;
    (usize 12) : uint_size;
    (usize 18) : uint_size;
    (usize 24) : uint_size;
    (usize 3) : uint_size;
    (usize 9) : uint_size;
    (usize 10) : uint_size;
    (usize 16) : uint_size;
    (usize 22) : uint_size;
    (usize 1) : uint_size;
    (usize 7) : uint_size;
    (usize 13) : uint_size;
    (usize 19) : uint_size;
    (usize 20) : uint_size;
    (usize 4) : uint_size;
    (usize 5) : uint_size;
    (usize 11) : uint_size;
    (usize 17) : uint_size;
    (usize 23) : uint_size;
    (usize 2) : uint_size;
    (usize 8) : uint_size;
    (usize 14) : uint_size;
    (usize 15) : uint_size;
    (usize 21) : uint_size
  ].

Definition b_1370_loc : ChoiceEqualityLocation :=
  (row_t ; 1371%nat).
Notation "'theta_inp'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'theta_inp'" :=(state_t : ChoiceEquality) (at level 2).
Notation "'theta_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'theta_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition THETA : nat :=
  1378.
Program Definition theta (s_1373 : state_t)
  : both (CEfset ([b_1370_loc])) [interface] (state_t) :=
  ((letbm b_1370 : row_t loc( b_1370_loc ) :=
        array_new_ (default : uint64) (5) in
      letb b_1370 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (usize 5)) b_1370 (
            L := (CEfset ([b_1370_loc]))) (I := [interface]) (
            fun i_1372 b_1370 =>
            letb b_1370 : row_t :=
              array_upd b_1370 (lift_to_both0 i_1372) (is_pure (((((
                          array_index (s_1373) (lift_to_both0 i_1372)) .^ (
                          array_index (s_1373) ((lift_to_both0 i_1372) .+ (
                              lift_to_both0 (usize 5))))) .^ (array_index (
                          s_1373) ((lift_to_both0 i_1372) .+ (lift_to_both0 (
                              usize 10))))) .^ (array_index (s_1373) ((
                          lift_to_both0 i_1372) .+ (lift_to_both0 (
                            usize 15))))) .^ (array_index (s_1373) ((
                        lift_to_both0 i_1372) .+ (lift_to_both0 (
                          usize 20)))))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 b_1370)
            ) in
      letb s_1373 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (usize 5)) s_1373 (
            L := (CEfset ([b_1370_loc]))) (I := [interface]) (
            fun i_1374 s_1373 =>
            letb u_1375 : uint64 :=
              array_index (b_1370) (((lift_to_both0 i_1374) .+ (lift_to_both0 (
                      usize 1))) %% (lift_to_both0 (usize 5))) in
            letb t_1376 : uint64 :=
              (array_index (b_1370) (((lift_to_both0 i_1374) .+ (lift_to_both0 (
                        usize 4))) %% (lift_to_both0 (usize 5)))) .^ (
                uint64_rotate_left (lift_to_both0 u_1375) (lift_to_both0 (
                    usize 1))) in
            letb s_1373 :=
              foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                    usize 5)) s_1373 (L := (CEfset ([b_1370_loc]))) (
                  I := [interface]) (fun j_1377 s_1373 =>
                  letb s_1373 : state_t :=
                    array_upd s_1373 (((lift_to_both0 (usize 5)) .* (
                          lift_to_both0 j_1377)) .+ (lift_to_both0 i_1374)) (
                      is_pure ((array_index (s_1373) (((lift_to_both0 (
                                  usize 5)) .* (lift_to_both0 j_1377)) .+ (
                              lift_to_both0 i_1374))) .^ (
                          lift_to_both0 t_1376))) in
                  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                    lift_to_both0 s_1373)
                  ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_1373)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1373)
      ) : both (CEfset ([b_1370_loc])) [interface] (state_t)).
Fail Next Obligation.


Notation "'rho_inp'" :=(state_t : choice_type) (in custom pack_type at level 2).
Notation "'rho_inp'" :=(state_t : ChoiceEquality) (at level 2).
Notation "'rho_out'" :=(state_t : choice_type) (in custom pack_type at level 2).
Notation "'rho_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition RHO : nat :=
  1382.
Program Definition rho (s_1379 : state_t)
  : both (fset.fset0) [interface] (state_t) :=
  ((letb s_1379 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 25)) s_1379 (L := (fset.fset0)) (I := [interface]) (
            fun i_1380 s_1379 =>
            letb u_1381 : uint64 :=
              array_index (s_1379) (lift_to_both0 i_1380) in
            letb s_1379 : state_t :=
              array_upd s_1379 (lift_to_both0 i_1380) (is_pure (
                  uint64_rotate_left (lift_to_both0 u_1381) (array_index (
                      rotc_v) (lift_to_both0 i_1380)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_1379)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1379)
      ) : both (fset.fset0) [interface] (state_t)).
Fail Next Obligation.

Definition v_1383_loc : ChoiceEqualityLocation :=
  (state_t ; 1384%nat).
Notation "'pi_inp'" :=(state_t : choice_type) (in custom pack_type at level 2).
Notation "'pi_inp'" :=(state_t : ChoiceEquality) (at level 2).
Notation "'pi_out'" :=(state_t : choice_type) (in custom pack_type at level 2).
Notation "'pi_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition PI : nat :=
  1387.
Program Definition pi (s_1386 : state_t)
  : both (CEfset ([v_1383_loc])) [interface] (state_t) :=
  ((letbm v_1383 : state_t loc( v_1383_loc ) :=
        array_new_ (default : uint64) (25) in
      letb v_1383 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 25)) v_1383 (L := (CEfset ([v_1383_loc]))) (
            I := [interface]) (fun i_1385 v_1383 =>
            letb v_1383 : state_t :=
              array_upd v_1383 (lift_to_both0 i_1385) (is_pure (array_index (
                    s_1386) (array_index (pi_v) (lift_to_both0 i_1385)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 v_1383)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 v_1383)
      ) : both (CEfset ([v_1383_loc])) [interface] (state_t)).
Fail Next Obligation.

Definition b_1388_loc : ChoiceEqualityLocation :=
  (row_t ; 1389%nat).
Notation "'chi_inp'" :=(state_t : choice_type) (in custom pack_type at level 2).
Notation "'chi_inp'" :=(state_t : ChoiceEquality) (at level 2).
Notation "'chi_out'" :=(state_t : choice_type) (in custom pack_type at level 2).
Notation "'chi_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition CHI : nat :=
  1395.
Program Definition chi (s_1390 : state_t)
  : both (CEfset ([b_1388_loc])) [interface] (state_t) :=
  ((letbm b_1388 : row_t loc( b_1388_loc ) :=
        array_new_ (default : uint64) (5) in
      letb '(s_1390, b_1388) :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (usize 5)) prod_ce(
            s_1390,
            b_1388
          ) (L := (CEfset ([b_1388_loc]))) (I := [interface]) (fun i_1391 '(
              s_1390,
              b_1388
            ) =>
            letb b_1388 :=
              foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                    usize 5)) b_1388 (L := (CEfset ([b_1388_loc]))) (
                  I := [interface]) (fun j_1392 b_1388 =>
                  letb b_1388 : row_t :=
                    array_upd b_1388 (lift_to_both0 j_1392) (is_pure (
                        array_index (s_1390) (((lift_to_both0 (usize 5)) .* (
                              lift_to_both0 i_1391)) .+ (
                            lift_to_both0 j_1392)))) in
                  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                    lift_to_both0 b_1388)
                  ) in
            letb s_1390 :=
              foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                    usize 5)) s_1390 (L := (CEfset ([b_1388_loc]))) (
                  I := [interface]) (fun j_1393 s_1390 =>
                  letb u_1394 : uint64 :=
                    array_index (b_1388) (((lift_to_both0 j_1393) .+ (
                          lift_to_both0 (usize 1))) %% (lift_to_both0 (
                          usize 5))) in
                  letb s_1390 : state_t :=
                    array_upd s_1390 (((lift_to_both0 (usize 5)) .* (
                          lift_to_both0 i_1391)) .+ (lift_to_both0 j_1393)) (
                      is_pure ((array_index (s_1390) (((lift_to_both0 (
                                  usize 5)) .* (lift_to_both0 i_1391)) .+ (
                              lift_to_both0 j_1393))) .^ ((not (
                              lift_to_both0 u_1394)) .& (array_index (b_1388) ((
                                (lift_to_both0 j_1393) .+ (lift_to_both0 (
                                    usize 2))) %% (lift_to_both0 (
                                  usize 5))))))) in
                  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                    lift_to_both0 s_1390)
                  ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 s_1390,
                lift_to_both0 b_1388
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1390)
      ) : both (CEfset ([b_1388_loc])) [interface] (state_t)).
Fail Next Obligation.


Notation "'iota_inp'" :=(
  state_t '× int64 : choice_type) (in custom pack_type at level 2).
Notation "'iota_inp'" :=(state_t '× int64 : ChoiceEquality) (at level 2).
Notation "'iota_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'iota_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition IOTA : nat :=
  1398.
Program Definition iota (s_1396 : state_t) (rndconst_1397 : int64)
  : both (fset.fset0) [interface] (state_t) :=
  ((letb s_1396 : state_t :=
        array_upd s_1396 (lift_to_both0 (usize 0)) (is_pure ((array_index (
                s_1396) (lift_to_both0 (usize 0))) .^ (uint64_classify (
                lift_to_both0 rndconst_1397)))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1396)
      ) : both (fset.fset0) [interface] (state_t)).
Fail Next Obligation.


Notation "'keccakf1600_inp'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'keccakf1600_inp'" :=(state_t : ChoiceEquality) (at level 2).
Notation "'keccakf1600_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'keccakf1600_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition KECCAKF1600 : nat :=
  1401.
Program Definition keccakf1600 (s_1399 : state_t)
  : both (CEfset ([b_1370_loc ; v_1383_loc ; b_1388_loc])) [interface] (
    state_t) :=
  ((letb s_1399 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 rounds_v) s_1399 (
            L := (CEfset ([b_1370_loc ; v_1383_loc ; b_1388_loc]))) (
            I := [interface]) (fun i_1400 s_1399 =>
            letbm s_1399 loc( s_1399_loc ) := theta (lift_to_both0 s_1399) in
            letbm s_1399 loc( s_1399_loc ) := rho (lift_to_both0 s_1399) in
            letbm s_1399 loc( s_1399_loc ) := pi (lift_to_both0 s_1399) in
            letbm s_1399 loc( s_1399_loc ) := chi (lift_to_both0 s_1399) in
            letbm s_1399 loc( s_1399_loc ) :=
              iota (lift_to_both0 s_1399) (array_index (roundconstants_v) (
                  lift_to_both0 i_1400)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_1399)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1399)
      ) : both (CEfset ([b_1370_loc ; v_1383_loc ; b_1388_loc])) [interface] (
      state_t)).
Fail Next Obligation.


Notation "'absorb_block_inp'" :=(
  state_t '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'absorb_block_inp'" :=(
  state_t '× byte_seq : ChoiceEquality) (at level 2).
Notation "'absorb_block_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'absorb_block_out'" :=(state_t : ChoiceEquality) (at level 2).
Definition ABSORB_BLOCK : nat :=
  1407.
Program Definition absorb_block (s_1403 : state_t) (block_1402 : byte_seq)
  : both (CEfset ([b_1370_loc ; v_1383_loc ; b_1388_loc])) [interface] (
    state_t) :=
  ((letb s_1403 :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 block_1402)) s_1403 (L := (CEfset (
                [b_1370_loc ; v_1383_loc ; b_1388_loc]))) (I := [interface]) (
            fun i_1404 s_1403 =>
            letb w_1405 : uint_size :=
              (lift_to_both0 i_1404) usize_shift_right (lift_to_both0 (
                  @repr U32 3)) in
            letb o_1406 : uint_size :=
              (lift_to_both0 (usize 8)) .* ((lift_to_both0 i_1404) .& (
                  lift_to_both0 (usize 7))) in
            letb s_1403 : state_t :=
              array_upd s_1403 (lift_to_both0 w_1405) (is_pure ((array_index (
                      s_1403) (lift_to_both0 w_1405)) .^ ((uint64_from_uint8 (
                        seq_index (block_1402) (
                          lift_to_both0 i_1404))) shift_left (
                      lift_to_both0 o_1406)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_1403)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (keccakf1600 (
          lift_to_both0 s_1403))
      ) : both (CEfset ([b_1370_loc ; v_1383_loc ; b_1388_loc])) [interface] (
      state_t)).
Fail Next Obligation.

Definition out_1408_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 1409%nat).
Notation "'squeeze_inp'" :=(
  state_t '× uint_size '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'squeeze_inp'" :=(
  state_t '× uint_size '× uint_size : ChoiceEquality) (at level 2).
Notation "'squeeze_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'squeeze_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition SQUEEZE : nat :=
  1418.
Program Definition squeeze (s_1411 : state_t) (nbytes_1410 : uint_size) (
    rate_1413 : uint_size)
  : both (CEfset (
      [b_1370_loc ; v_1383_loc ; b_1388_loc ; out_1408_loc])) [interface] (
    byte_seq) :=
  ((letbm out_1408 : seq uint8 loc( out_1408_loc ) :=
        seq_new_ (default : uint8) (lift_to_both0 nbytes_1410) in
      letb '(s_1411, out_1408) :=
        foldi_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 nbytes_1410) prod_ce(s_1411, out_1408) (L := (CEfset (
                [b_1370_loc ; v_1383_loc ; b_1388_loc ; out_1408_loc]))) (
            I := [interface]) (fun i_1412 '(s_1411, out_1408) =>
            letb pos_1414 : uint_size :=
              (lift_to_both0 i_1412) %% (lift_to_both0 rate_1413) in
            letb w_1415 : uint_size :=
              (lift_to_both0 pos_1414) usize_shift_right (lift_to_both0 (
                  @repr U32 3)) in
            letb o_1416 : uint_size :=
              (lift_to_both0 (usize 8)) .* ((lift_to_both0 pos_1414) .& (
                  lift_to_both0 (usize 7))) in
            letb b_1417 : uint64 :=
              ((array_index (s_1411) (lift_to_both0 w_1415)) shift_right (
                  lift_to_both0 o_1416)) .& (uint64_classify (lift_to_both0 (
                    @repr U64 255))) in
            letb out_1408 : seq uint8 :=
              seq_upd out_1408 (lift_to_both0 i_1412) (is_pure (
                  uint8_from_uint64 (lift_to_both0 b_1417))) in
            letb '(s_1411) :=
              if (((lift_to_both0 i_1412) .+ (lift_to_both0 (usize 1))) %% (
                  lift_to_both0 rate_1413)) =.? (lift_to_both0 (
                  usize 0)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [b_1370_loc ; v_1383_loc ; b_1388_loc ; out_1408_loc])) (
                L2 := CEfset (
                  [b_1370_loc ; v_1383_loc ; b_1388_loc ; out_1408_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm s_1411 loc( s_1411_loc ) :=
                  keccakf1600 (lift_to_both0 s_1411) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 s_1411)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 s_1411)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 s_1411,
                lift_to_both0 out_1408
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 out_1408)
      ) : both (CEfset (
        [b_1370_loc ; v_1383_loc ; b_1388_loc ; out_1408_loc])) [interface] (
      byte_seq)).
Fail Next Obligation.

Definition buf_1419_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 1422%nat).
Definition last_block_len_1420_loc : ChoiceEqualityLocation :=
  (uint_size ; 1423%nat).
Definition s_1421_loc : ChoiceEqualityLocation :=
  (state_t ; 1424%nat).
Notation "'keccak_inp'" :=(
  uint_size '× byte_seq '× int8 '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'keccak_inp'" :=(
  uint_size '× byte_seq '× int8 '× uint_size : ChoiceEquality) (at level 2).
Notation "'keccak_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'keccak_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition KECCAK : nat :=
  1432.
Program Definition keccak (rate_1425 : uint_size) (data_1426 : byte_seq) (
    p_1430 : int8) (outbytes_1431 : uint_size)
  : both (CEfset (
      [b_1370_loc ; v_1383_loc ; b_1388_loc ; out_1408_loc ; buf_1419_loc ; last_block_len_1420_loc ; s_1421_loc])) [interface] (
    byte_seq) :=
  ((letbm buf_1419 : seq uint8 loc( buf_1419_loc ) :=
        seq_new_ (default : uint8) (lift_to_both0 rate_1425) in
      letbm last_block_len_1420 : uint_size loc( last_block_len_1420_loc ) :=
        lift_to_both0 (usize 0) in
      letbm s_1421 : state_t loc( s_1421_loc ) :=
        array_new_ (default : uint64) (25) in
      letb '(buf_1419, last_block_len_1420, s_1421) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_num_chunks (
              lift_to_both0 data_1426) (lift_to_both0 rate_1425)) prod_ce(
            buf_1419,
            last_block_len_1420,
            s_1421
          ) (L := (CEfset (
                [b_1370_loc ; v_1383_loc ; b_1388_loc ; out_1408_loc ; buf_1419_loc ; last_block_len_1420_loc ; s_1421_loc]))) (
            I := [interface]) (fun i_1427 '(
              buf_1419,
              last_block_len_1420,
              s_1421
            ) =>
            letb '(block_len_1428, block_1429) : (uint_size '× seq uint8) :=
              seq_get_chunk (lift_to_both0 data_1426) (
                lift_to_both0 rate_1425) (lift_to_both0 i_1427) in
            letb '(buf_1419, last_block_len_1420, s_1421) :=
              if (lift_to_both0 block_len_1428) =.? (
                lift_to_both0 rate_1425) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [b_1370_loc ; v_1383_loc ; b_1388_loc ; buf_1419_loc ; last_block_len_1420_loc ; s_1421_loc])) (
                L2 := CEfset (
                  [b_1370_loc ; v_1383_loc ; b_1388_loc ; buf_1419_loc ; last_block_len_1420_loc ; s_1421_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm s_1421 loc( s_1421_loc ) :=
                  absorb_block (lift_to_both0 s_1421) (
                    lift_to_both0 block_1429) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 buf_1419,
                    lift_to_both0 last_block_len_1420,
                    lift_to_both0 s_1421
                  ))
                )
              else  lift_scope (L1 := CEfset (
                  [buf_1419_loc ; last_block_len_1420_loc ; s_1421_loc])) (
                L2 := CEfset (
                  [b_1370_loc ; v_1383_loc ; b_1388_loc ; buf_1419_loc ; last_block_len_1420_loc ; s_1421_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm buf_1419 loc( buf_1419_loc ) :=
                  seq_update_start (lift_to_both0 buf_1419) (
                    lift_to_both0 block_1429) in
                letbm last_block_len_1420 loc( last_block_len_1420_loc ) :=
                  lift_to_both0 block_len_1428 in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 buf_1419,
                    lift_to_both0 last_block_len_1420,
                    lift_to_both0 s_1421
                  ))
                ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 buf_1419,
                lift_to_both0 last_block_len_1420,
                lift_to_both0 s_1421
              ))
            ) in
      letb buf_1419 : seq uint8 :=
        seq_upd buf_1419 (lift_to_both0 last_block_len_1420) (is_pure (secret (
              lift_to_both0 p_1430))) in
      letb buf_1419 : seq uint8 :=
        seq_upd buf_1419 ((lift_to_both0 rate_1425) .- (lift_to_both0 (
              usize 1))) (is_pure ((seq_index (buf_1419) ((
                  lift_to_both0 rate_1425) .- (lift_to_both0 (usize 1)))) .| (
              secret (lift_to_both0 (@repr U8 128))))) in
      letbm s_1421 loc( s_1421_loc ) :=
        absorb_block (lift_to_both0 s_1421) (lift_to_both0 buf_1419) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (squeeze (
          lift_to_both0 s_1421) (lift_to_both0 outbytes_1431) (
          lift_to_both0 rate_1425))
      ) : both (CEfset (
        [b_1370_loc ; v_1383_loc ; b_1388_loc ; out_1408_loc ; buf_1419_loc ; last_block_len_1420_loc ; s_1421_loc])) [interface] (
      byte_seq)).
Fail Next Obligation.


Notation "'sha3224_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sha3224_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'sha3224_out'" :=(
  digest224_t : choice_type) (in custom pack_type at level 2).
Notation "'sha3224_out'" :=(digest224_t : ChoiceEquality) (at level 2).
Definition SHA3224 : nat :=
  1435.
Program Definition sha3224 (data_1433 : byte_seq)
  : both (CEfset (
      [b_1370_loc ; v_1383_loc ; b_1388_loc ; out_1408_loc ; buf_1419_loc ; last_block_len_1420_loc ; s_1421_loc])) [interface] (
    digest224_t) :=
  ((letb t_1434 : seq uint8 :=
        keccak (lift_to_both0 sha3224_rate_v) (lift_to_both0 data_1433) (
          lift_to_both0 (@repr U8 6)) (lift_to_both0 (usize 28)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (28) (
          lift_to_both0 t_1434))
      ) : both (CEfset (
        [b_1370_loc ; v_1383_loc ; b_1388_loc ; out_1408_loc ; buf_1419_loc ; last_block_len_1420_loc ; s_1421_loc])) [interface] (
      digest224_t)).
Fail Next Obligation.


Notation "'sha3256_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sha3256_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'sha3256_out'" :=(
  digest256_t : choice_type) (in custom pack_type at level 2).
Notation "'sha3256_out'" :=(digest256_t : ChoiceEquality) (at level 2).
Definition SHA3256 : nat :=
  1438.
Program Definition sha3256 (data_1436 : byte_seq)
  : both (CEfset (
      [b_1370_loc ; v_1383_loc ; b_1388_loc ; out_1408_loc ; buf_1419_loc ; last_block_len_1420_loc ; s_1421_loc])) [interface] (
    digest256_t) :=
  ((letb t_1437 : seq uint8 :=
        keccak (lift_to_both0 sha3256_rate_v) (lift_to_both0 data_1436) (
          lift_to_both0 (@repr U8 6)) (lift_to_both0 (usize 32)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (32) (
          lift_to_both0 t_1437))
      ) : both (CEfset (
        [b_1370_loc ; v_1383_loc ; b_1388_loc ; out_1408_loc ; buf_1419_loc ; last_block_len_1420_loc ; s_1421_loc])) [interface] (
      digest256_t)).
Fail Next Obligation.


Notation "'sha3384_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sha3384_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'sha3384_out'" :=(
  digest384_t : choice_type) (in custom pack_type at level 2).
Notation "'sha3384_out'" :=(digest384_t : ChoiceEquality) (at level 2).
Definition SHA3384 : nat :=
  1441.
Program Definition sha3384 (data_1439 : byte_seq)
  : both (CEfset (
      [b_1370_loc ; v_1383_loc ; b_1388_loc ; out_1408_loc ; buf_1419_loc ; last_block_len_1420_loc ; s_1421_loc])) [interface] (
    digest384_t) :=
  ((letb t_1440 : seq uint8 :=
        keccak (lift_to_both0 sha3384_rate_v) (lift_to_both0 data_1439) (
          lift_to_both0 (@repr U8 6)) (lift_to_both0 (usize 48)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (48) (
          lift_to_both0 t_1440))
      ) : both (CEfset (
        [b_1370_loc ; v_1383_loc ; b_1388_loc ; out_1408_loc ; buf_1419_loc ; last_block_len_1420_loc ; s_1421_loc])) [interface] (
      digest384_t)).
Fail Next Obligation.


Notation "'sha3512_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sha3512_inp'" :=(byte_seq : ChoiceEquality) (at level 2).
Notation "'sha3512_out'" :=(
  digest512_t : choice_type) (in custom pack_type at level 2).
Notation "'sha3512_out'" :=(digest512_t : ChoiceEquality) (at level 2).
Definition SHA3512 : nat :=
  1444.
Program Definition sha3512 (data_1442 : byte_seq)
  : both (CEfset (
      [b_1370_loc ; v_1383_loc ; b_1388_loc ; out_1408_loc ; buf_1419_loc ; last_block_len_1420_loc ; s_1421_loc])) [interface] (
    digest512_t) :=
  ((letb t_1443 : seq uint8 :=
        keccak (lift_to_both0 sha3512_rate_v) (lift_to_both0 data_1442) (
          lift_to_both0 (@repr U8 6)) (lift_to_both0 (usize 64)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (64) (
          lift_to_both0 t_1443))
      ) : both (CEfset (
        [b_1370_loc ; v_1383_loc ; b_1388_loc ; out_1408_loc ; buf_1419_loc ; last_block_len_1420_loc ; s_1421_loc])) [interface] (
      digest512_t)).
Fail Next Obligation.


Notation "'shake128_inp'" :=(
  byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'shake128_inp'" :=(
  byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'shake128_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'shake128_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition SHAKE128 : nat :=
  1447.
Program Definition shake128 (data_1445 : byte_seq) (outlen_1446 : uint_size)
  : both (CEfset (
      [b_1370_loc ; v_1383_loc ; b_1388_loc ; out_1408_loc ; buf_1419_loc ; last_block_len_1420_loc ; s_1421_loc])) [interface] (
    byte_seq) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (keccak (
          lift_to_both0 shake128_rate_v) (lift_to_both0 data_1445) (
          lift_to_both0 (@repr U8 31)) (lift_to_both0 outlen_1446))
      ) : both (CEfset (
        [b_1370_loc ; v_1383_loc ; b_1388_loc ; out_1408_loc ; buf_1419_loc ; last_block_len_1420_loc ; s_1421_loc])) [interface] (
      byte_seq)).
Fail Next Obligation.


Notation "'shake256_inp'" :=(
  byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'shake256_inp'" :=(
  byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'shake256_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'shake256_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition SHAKE256 : nat :=
  1450.
Program Definition shake256 (data_1448 : byte_seq) (outlen_1449 : uint_size)
  : both (CEfset (
      [b_1370_loc ; v_1383_loc ; b_1388_loc ; out_1408_loc ; buf_1419_loc ; last_block_len_1420_loc ; s_1421_loc])) [interface] (
    byte_seq) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (keccak (
          lift_to_both0 shake256_rate_v) (lift_to_both0 data_1448) (
          lift_to_both0 (@repr U8 31)) (lift_to_both0 outlen_1449))
      ) : both (CEfset (
        [b_1370_loc ; v_1383_loc ; b_1388_loc ; out_1408_loc ; buf_1419_loc ; last_block_len_1420_loc ; s_1421_loc])) [interface] (
      byte_seq)).
Fail Next Obligation.

