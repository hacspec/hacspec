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
Require Import Hacspec_Bls12_381.



Require Import Hacspec_Sha256.

Definition fp_hash_canvas_t := nseq (int8) (usize 64).
Definition fp_hash_t :=
  nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.

Definition arr_fp_t := nseq (uint64) (usize 6).

Definition b_in_bytes_v : uint_size :=
  usize 32.

Definition s_in_bytes_v : uint_size :=
  usize 64.

Definition l_v : uint_size :=
  usize 64.

Definition p_1_2_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 936899308823769933)) : uint64;
    (secret (@repr U64 2706051889235351147)) : uint64;
    (secret (@repr U64 12843041017062132063)) : uint64;
    (secret (@repr U64 12941209323636816658)) : uint64;
    (secret (@repr U64 1105070755758604287)) : uint64;
    (secret (@repr U64 15924587544893707605)) : uint64
  ].

Definition p_1_4_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 468449654411884966)) : uint64;
    (secret (@repr U64 10576397981472451381)) : uint64;
    (secret (@repr U64 15644892545385841839)) : uint64;
    (secret (@repr U64 15693976698673184137)) : uint64;
    (secret (@repr U64 552535377879302143)) : uint64;
    (secret (@repr U64 17185665809301629611)) : uint64
  ].

Definition p_3_4_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 468449654411884966)) : uint64;
    (secret (@repr U64 10576397981472451381)) : uint64;
    (secret (@repr U64 15644892545385841839)) : uint64;
    (secret (@repr U64 15693976698673184137)) : uint64;
    (secret (@repr U64 552535377879302143)) : uint64;
    (secret (@repr U64 17185665809301629610)) : uint64
  ].

Definition b_i_2332_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2334%nat).
Definition l_i_b_str_2331_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2335%nat).
Definition uniform_bytes_2333_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2336%nat).
Notation "'expand_message_xmd_inp'" :=(
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'expand_message_xmd_inp'" :=(
  byte_seq '× byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'expand_message_xmd_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'expand_message_xmd_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition EXPAND_MESSAGE_XMD : nat :=
  2347.
Program Definition expand_message_xmd (msg_2342 : byte_seq) (
    dst_2339 : byte_seq) (len_in_bytes_2337 : uint_size)
  : both (CEfset (
      [l_i_b_str_2331_loc ; b_i_2332_loc ; uniform_bytes_2333_loc])) [interface] (
    byte_seq) :=
  ((letb ell_2338 : uint_size :=
        (((lift_to_both0 len_in_bytes_2337) .+ (
              lift_to_both0 b_in_bytes_v)) .- (lift_to_both0 (usize 1))) ./ (
          lift_to_both0 b_in_bytes_v) in
      letb dst_prime_2340 : seq uint8 :=
        seq_push (lift_to_both0 dst_2339) (uint8_from_usize (seq_len (
              lift_to_both0 dst_2339))) in
      letb z_pad_2341 : seq uint8 :=
        seq_new_ (default : uint8) (lift_to_both0 s_in_bytes_v) in
      letbm l_i_b_str_2331 : seq uint8 loc( l_i_b_str_2331_loc ) :=
        seq_new_ (default : uint8) (lift_to_both0 (usize 2)) in
      letb l_i_b_str_2331 : seq uint8 :=
        seq_upd l_i_b_str_2331 (lift_to_both0 (usize 0)) (is_pure (
            uint8_from_usize ((lift_to_both0 len_in_bytes_2337) ./ (
                lift_to_both0 (usize 256))))) in
      letb l_i_b_str_2331 : seq uint8 :=
        seq_upd l_i_b_str_2331 (lift_to_both0 (usize 1)) (is_pure (
            uint8_from_usize (lift_to_both0 len_in_bytes_2337))) in
      letb msg_prime_2343 : seq uint8 :=
        seq_concat (seq_concat (seq_concat (seq_concat (
                lift_to_both0 z_pad_2341) (lift_to_both0 msg_2342)) (
              lift_to_both0 l_i_b_str_2331)) (seq_new_ (default : uint8) (
              lift_to_both0 (usize 1)))) (lift_to_both0 dst_prime_2340) in
      letb b_0_2344 : seq uint8 :=
        seq_from_seq (array_to_seq (hash (lift_to_both0 msg_prime_2343))) in
      letbm b_i_2332 : seq uint8 loc( b_i_2332_loc ) :=
        seq_from_seq (array_to_seq (hash (seq_concat (seq_push (
                lift_to_both0 b_0_2344) (secret (lift_to_both0 (@repr U8 1)))) (
              lift_to_both0 dst_prime_2340)))) in
      letbm uniform_bytes_2333 : seq uint8 loc( uniform_bytes_2333_loc ) :=
        seq_from_seq (lift_to_both0 b_i_2332) in
      letb '(b_i_2332, uniform_bytes_2333) :=
        foldi_both' (lift_to_both0 (usize 2)) ((lift_to_both0 ell_2338) .+ (
              lift_to_both0 (usize 1))) prod_ce(b_i_2332, uniform_bytes_2333) (
            L := (CEfset (
                [l_i_b_str_2331_loc ; b_i_2332_loc ; uniform_bytes_2333_loc]))) (
            I := [interface]) (fun i_2345 '(b_i_2332, uniform_bytes_2333) =>
            letb t_2346 : seq uint8 := seq_from_seq (lift_to_both0 b_0_2344) in
            letbm b_i_2332 loc( b_i_2332_loc ) :=
              seq_from_seq (array_to_seq (hash (seq_concat (seq_push ((
                        lift_to_both0 t_2346) seq_xor (
                        lift_to_both0 b_i_2332)) (uint8_from_usize (
                        lift_to_both0 i_2345))) (
                    lift_to_both0 dst_prime_2340)))) in
            letbm uniform_bytes_2333 loc( uniform_bytes_2333_loc ) :=
              seq_concat (lift_to_both0 uniform_bytes_2333) (
                lift_to_both0 b_i_2332) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 b_i_2332,
                lift_to_both0 uniform_bytes_2333
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (seq_truncate (
          lift_to_both0 uniform_bytes_2333) (lift_to_both0 len_in_bytes_2337))
      ) : both (CEfset (
        [l_i_b_str_2331_loc ; b_i_2332_loc ; uniform_bytes_2333_loc])) [interface] (
      byte_seq)).
Fail Next Obligation.

Definition output_2348_loc : ChoiceEqualityLocation :=
  (seq fp_t ; 2349%nat).
Notation "'fp_hash_to_field_inp'" :=(
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'fp_hash_to_field_inp'" :=(
  byte_seq '× byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'fp_hash_to_field_out'" :=(
  seq fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_hash_to_field_out'" :=(seq fp_t : ChoiceEquality) (at level 2).
Definition FP_HASH_TO_FIELD : nat :=
  2359.
Program Definition fp_hash_to_field (msg_2352 : byte_seq) (
    dst_2353 : byte_seq) (count_2350 : uint_size)
  : both (CEfset (
      [l_i_b_str_2331_loc ; b_i_2332_loc ; uniform_bytes_2333_loc ; output_2348_loc])) [interface] (
    seq fp_t) :=
  ((letb len_in_bytes_2351 : uint_size :=
        (lift_to_both0 count_2350) .* (lift_to_both0 l_v) in
      letb uniform_bytes_2354 : seq uint8 :=
        expand_message_xmd (lift_to_both0 msg_2352) (lift_to_both0 dst_2353) (
          lift_to_both0 len_in_bytes_2351) in
      letbm output_2348 : seq fp_t loc( output_2348_loc ) :=
        seq_new_ (default : fp_t) (lift_to_both0 count_2350) in
      letb output_2348 :=
        foldi_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 count_2350) output_2348 (L := (CEfset (
                [l_i_b_str_2331_loc ; b_i_2332_loc ; uniform_bytes_2333_loc ; output_2348_loc]))) (
            I := [interface]) (fun i_2355 output_2348 =>
            letb elm_offset_2356 : uint_size :=
              (lift_to_both0 l_v) .* (lift_to_both0 i_2355) in
            letb tv_2357 : seq uint8 :=
              seq_slice (lift_to_both0 uniform_bytes_2354) (
                lift_to_both0 elm_offset_2356) (lift_to_both0 l_v) in
            letb u_i_2358 : fp_t :=
              nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
                    nat_mod_from_byte_seq_be (lift_to_both0 tv_2357))) (
                  lift_to_both0 (usize 16)) (lift_to_both0 (usize 48))) in
            letb output_2348 : seq fp_t :=
              seq_upd output_2348 (lift_to_both0 i_2355) (is_pure (
                  lift_to_both0 u_i_2358)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 output_2348)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 output_2348)
      ) : both (CEfset (
        [l_i_b_str_2331_loc ; b_i_2332_loc ; uniform_bytes_2333_loc ; output_2348_loc])) [interface] (
      seq fp_t)).
Fail Next Obligation.


Notation "'fp_sgn0_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_sgn0_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'fp_sgn0_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'fp_sgn0_out'" :=(bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition FP_SGN0 : nat :=
  2361.
Program Definition fp_sgn0 (x_2360 : fp_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 x_2360) rem (nat_mod_two )) =.? (nat_mod_one ))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'fp_is_square_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_is_square_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'fp_is_square_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'fp_is_square_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition FP_IS_SQUARE : nat :=
  2365.
Program Definition fp_is_square (x_2363 : fp_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb c1_2362 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_1_2_v)) in
      letb tv_2364 : fp_t :=
        nat_mod_pow_self (lift_to_both0 x_2363) (lift_to_both0 c1_2362) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 tv_2364) =.? (nat_mod_zero )) || ((
            lift_to_both0 tv_2364) =.? (nat_mod_one )))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'fp_sqrt_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_sqrt_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'fp_sqrt_out'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_sqrt_out'" :=(fp_t : ChoiceEquality) (at level 2).
Definition FP_SQRT : nat :=
  2368.
Program Definition fp_sqrt (x_2367 : fp_t)
  : both (fset.fset0) [interface] (fp_t) :=
  ((letb c1_2366 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_1_4_v)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (nat_mod_pow_self (
          lift_to_both0 x_2367) (lift_to_both0 c1_2366))
      ) : both (fset.fset0) [interface] (fp_t)).
Fail Next Obligation.


Notation "'g1_curve_func_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_curve_func_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'g1_curve_func_out'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_curve_func_out'" :=(fp_t : ChoiceEquality) (at level 2).
Definition G1_CURVE_FUNC : nat :=
  2370.
Program Definition g1_curve_func (x_2369 : fp_t)
  : both (fset.fset0) [interface] (fp_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((((
              lift_to_both0 x_2369) *% (lift_to_both0 x_2369)) *% (
            lift_to_both0 x_2369)) +% (nat_mod_from_literal (_) (lift_to_both0 (
              @repr U128 4))))
      ) : both (fset.fset0) [interface] (fp_t)).
Fail Next Obligation.

Definition y_2372_loc : ChoiceEqualityLocation :=
  (fp_t ; 2373%nat).
Definition tv4_2371_loc : ChoiceEqualityLocation :=
  (fp_t ; 2374%nat).
Notation "'g1_map_to_curve_svdw_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_map_to_curve_svdw_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'g1_map_to_curve_svdw_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_map_to_curve_svdw_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1_MAP_TO_CURVE_SVDW : nat :=
  2388.
Program Definition g1_map_to_curve_svdw (u_2377 : fp_t)
  : both (CEfset ([tv4_2371_loc ; y_2372_loc])) [interface] (g1_t) :=
  ((letb z_2375 : fp_t :=
        (nat_mod_zero ) -% (nat_mod_from_literal (_) (lift_to_both0 (
              @repr U128 3))) in
      letb gz_2376 : fp_t := g1_curve_func (lift_to_both0 z_2375) in
      letb tv1_2378 : fp_t :=
        ((lift_to_both0 u_2377) *% (lift_to_both0 u_2377)) *% (
          lift_to_both0 gz_2376) in
      letb tv2_2379 : fp_t := (nat_mod_one ) +% (lift_to_both0 tv1_2378) in
      letb tv1_2380 : fp_t := (nat_mod_one ) -% (lift_to_both0 tv1_2378) in
      letb tv3_2381 : fp_t :=
        nat_mod_inv ((lift_to_both0 tv1_2380) *% (lift_to_both0 tv2_2379)) in
      letbm tv4_2371 : fp_t loc( tv4_2371_loc ) :=
        fp_sqrt (((nat_mod_zero ) -% (lift_to_both0 gz_2376)) *% (((
                nat_mod_from_literal (_) (lift_to_both0 (@repr U128 3))) *% (
                lift_to_both0 z_2375)) *% (lift_to_both0 z_2375))) in
      letb '(tv4_2371) :=
        if fp_sgn0 (lift_to_both0 tv4_2371) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([tv4_2371_loc])) (L2 := CEfset (
            [tv4_2371_loc ; y_2372_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm tv4_2371 loc( tv4_2371_loc ) :=
            (nat_mod_zero ) -% (lift_to_both0 tv4_2371) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 tv4_2371)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 tv4_2371)
         in
      letb tv5_2382 : fp_t :=
        (((lift_to_both0 u_2377) *% (lift_to_both0 tv1_2380)) *% (
            lift_to_both0 tv3_2381)) *% (lift_to_both0 tv4_2371) in
      letb tv6_2383 : fp_t :=
        (((nat_mod_zero ) -% (nat_mod_from_literal (_) (lift_to_both0 (
                  @repr U128 4)))) *% (lift_to_both0 gz_2376)) *% (nat_mod_inv (
            ((nat_mod_from_literal (_) (lift_to_both0 (@repr U128 3))) *% (
                lift_to_both0 z_2375)) *% (lift_to_both0 z_2375))) in
      letb x1_2384 : fp_t :=
        (((nat_mod_zero ) -% (lift_to_both0 z_2375)) *% (nat_mod_inv (
              nat_mod_two ))) -% (lift_to_both0 tv5_2382) in
      letb x2_2385 : fp_t :=
        (((nat_mod_zero ) -% (lift_to_both0 z_2375)) *% (nat_mod_inv (
              nat_mod_two ))) +% (lift_to_both0 tv5_2382) in
      letb x3_2386 : fp_t :=
        (lift_to_both0 z_2375) +% (((lift_to_both0 tv6_2383) *% (((
                  lift_to_both0 tv2_2379) *% (lift_to_both0 tv2_2379)) *% (
                lift_to_both0 tv3_2381))) *% (((lift_to_both0 tv2_2379) *% (
                lift_to_both0 tv2_2379)) *% (lift_to_both0 tv3_2381))) in
      letb x_2387 : fp_t :=
        if is_pure (I := [interface]) (fp_is_square (g1_curve_func (
              lift_to_both0 x1_2384)))
        then lift_to_both0 x1_2384
        else if is_pure (I := [interface]) (fp_is_square (g1_curve_func (
              lift_to_both0 x2_2385)))
        then lift_to_both0 x2_2385
        else lift_to_both0 x3_2386 in
      letbm y_2372 : fp_t loc( y_2372_loc ) :=
        fp_sqrt (g1_curve_func (lift_to_both0 x_2387)) in
      letb '(y_2372) :=
        if (fp_sgn0 (lift_to_both0 u_2377)) !=.? (fp_sgn0 (
            lift_to_both0 y_2372)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([tv4_2371_loc ; y_2372_loc])) (
          L2 := CEfset ([tv4_2371_loc ; y_2372_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm y_2372 loc( y_2372_loc ) :=
            (nat_mod_zero ) -% (lift_to_both0 y_2372) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 y_2372)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 y_2372)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_2387,
          lift_to_both0 y_2372,
          lift_to_both0 ((false : bool_ChoiceEquality))
        ))
      ) : both (CEfset ([tv4_2371_loc ; y_2372_loc])) [interface] (g1_t)).
Fail Next Obligation.


Notation "'g1_clear_cofactor_inp'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_clear_cofactor_inp'" :=(g1_t : ChoiceEquality) (at level 2).
Notation "'g1_clear_cofactor_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_clear_cofactor_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1_CLEAR_COFACTOR : nat :=
  2391.
Program Definition g1_clear_cofactor (x_2390 : g1_t)
  : both (fset.fset0) [interface] (g1_t) :=
  ((letb h_eff_2389 : scalar_t :=
        nat_mod_from_literal (_) (lift_to_both0 (
            @repr U128 15132376222941642753)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (g1mul (
          lift_to_both0 h_eff_2389) (lift_to_both0 x_2390))
      ) : both (fset.fset0) [interface] (g1_t)).
Fail Next Obligation.


Notation "'g1_hash_to_curve_svdw_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g1_hash_to_curve_svdw_inp'" :=(
  byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'g1_hash_to_curve_svdw_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_hash_to_curve_svdw_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1_HASH_TO_CURVE_SVDW : nat :=
  2399.
Program Definition g1_hash_to_curve_svdw (msg_2392 : byte_seq) (
    dst_2393 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2331_loc ; b_i_2332_loc ; uniform_bytes_2333_loc ; output_2348_loc ; tv4_2371_loc ; y_2372_loc])) [interface] (
    g1_t) :=
  ((letb u_2394 : seq fp_t :=
        fp_hash_to_field (lift_to_both0 msg_2392) (lift_to_both0 dst_2393) (
          lift_to_both0 (usize 2)) in
      letb q0_2395 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_map_to_curve_svdw (seq_index (u_2394) (lift_to_both0 (usize 0))) in
      letb q1_2396 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_map_to_curve_svdw (seq_index (u_2394) (lift_to_both0 (usize 1))) in
      letb r_2397 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1add (lift_to_both0 q0_2395) (lift_to_both0 q1_2396) in
      letb p_2398 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_clear_cofactor (lift_to_both0 r_2397) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2398)
      ) : both (CEfset (
        [l_i_b_str_2331_loc ; b_i_2332_loc ; uniform_bytes_2333_loc ; output_2348_loc ; tv4_2371_loc ; y_2372_loc])) [interface] (
      g1_t)).
Fail Next Obligation.


Notation "'g1_encode_to_curve_svdw_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g1_encode_to_curve_svdw_inp'" :=(
  byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'g1_encode_to_curve_svdw_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_encode_to_curve_svdw_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1_ENCODE_TO_CURVE_SVDW : nat :=
  2405.
Program Definition g1_encode_to_curve_svdw (msg_2400 : byte_seq) (
    dst_2401 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2331_loc ; b_i_2332_loc ; uniform_bytes_2333_loc ; output_2348_loc ; tv4_2371_loc ; y_2372_loc])) [interface] (
    g1_t) :=
  ((letb u_2402 : seq fp_t :=
        fp_hash_to_field (lift_to_both0 msg_2400) (lift_to_both0 dst_2401) (
          lift_to_both0 (usize 1)) in
      letb q_2403 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_map_to_curve_svdw (seq_index (u_2402) (lift_to_both0 (usize 0))) in
      letb p_2404 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_clear_cofactor (lift_to_both0 q_2403) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2404)
      ) : both (CEfset (
        [l_i_b_str_2331_loc ; b_i_2332_loc ; uniform_bytes_2333_loc ; output_2348_loc ; tv4_2371_loc ; y_2372_loc])) [interface] (
      g1_t)).
Fail Next Obligation.

Definition output_2406_loc : ChoiceEqualityLocation :=
  (seq (fp_t '× fp_t) ; 2407%nat).
Notation "'fp2_hash_to_field_inp'" :=(
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'fp2_hash_to_field_inp'" :=(
  byte_seq '× byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'fp2_hash_to_field_out'" :=(
  seq fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2_hash_to_field_out'" :=(seq fp2_t : ChoiceEquality) (at level 2).
Definition FP2_HASH_TO_FIELD : nat :=
  2420.
Program Definition fp2_hash_to_field (msg_2410 : byte_seq) (
    dst_2411 : byte_seq) (count_2408 : uint_size)
  : both (CEfset (
      [l_i_b_str_2331_loc ; b_i_2332_loc ; uniform_bytes_2333_loc ; output_2406_loc])) [interface] (
    seq fp2_t) :=
  ((letb len_in_bytes_2409 : uint_size :=
        ((lift_to_both0 count_2408) .* (lift_to_both0 (usize 2))) .* (
          lift_to_both0 l_v) in
      letb uniform_bytes_2412 : seq uint8 :=
        expand_message_xmd (lift_to_both0 msg_2410) (lift_to_both0 dst_2411) (
          lift_to_both0 len_in_bytes_2409) in
      letbm output_2406 : seq (fp_t '× fp_t) loc( output_2406_loc ) :=
        seq_new_ (default : fp2_t) (lift_to_both0 count_2408) in
      letb output_2406 :=
        foldi_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 count_2408) output_2406 (L := (CEfset (
                [l_i_b_str_2331_loc ; b_i_2332_loc ; uniform_bytes_2333_loc ; output_2406_loc]))) (
            I := [interface]) (fun i_2413 output_2406 =>
            letb elm_offset_2414 : uint_size :=
              ((lift_to_both0 l_v) .* (lift_to_both0 i_2413)) .* (
                lift_to_both0 (usize 2)) in
            letb tv_2415 : seq uint8 :=
              seq_slice (lift_to_both0 uniform_bytes_2412) (
                lift_to_both0 elm_offset_2414) (lift_to_both0 l_v) in
            letb e_1_2416 : fp_t :=
              nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
                    nat_mod_from_byte_seq_be (lift_to_both0 tv_2415))) (
                  lift_to_both0 (usize 16)) (lift_to_both0 (usize 48))) in
            letb elm_offset_2417 : uint_size :=
              (lift_to_both0 l_v) .* ((lift_to_both0 (usize 1)) .+ ((
                    lift_to_both0 i_2413) .* (lift_to_both0 (usize 2)))) in
            letb tv_2418 : seq uint8 :=
              seq_slice (lift_to_both0 uniform_bytes_2412) (
                lift_to_both0 elm_offset_2417) (lift_to_both0 l_v) in
            letb e_2_2419 : fp_t :=
              nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
                    nat_mod_from_byte_seq_be (lift_to_both0 tv_2418))) (
                  lift_to_both0 (usize 16)) (lift_to_both0 (usize 48))) in
            letb output_2406 : seq (fp_t '× fp_t) :=
              seq_upd output_2406 (lift_to_both0 i_2413) (is_pure (prod_b(
                    lift_to_both0 e_1_2416,
                    lift_to_both0 e_2_2419
                  ))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 output_2406)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 output_2406)
      ) : both (CEfset (
        [l_i_b_str_2331_loc ; b_i_2332_loc ; uniform_bytes_2333_loc ; output_2406_loc])) [interface] (
      seq fp2_t)).
Fail Next Obligation.


Notation "'fp2_sgn0_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2_sgn0_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'fp2_sgn0_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'fp2_sgn0_out'" :=(bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition FP2_SGN0 : nat :=
  2427.
Program Definition fp2_sgn0 (x_2421 : fp2_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb '(x0_2422, x1_2423) : (fp_t '× fp_t) := lift_to_both0 x_2421 in
      letb sign_0_2424 : bool_ChoiceEquality :=
        fp_sgn0 (lift_to_both0 x0_2422) in
      letb zero_0_2425 : bool_ChoiceEquality :=
        (lift_to_both0 x0_2422) =.? (nat_mod_zero ) in
      letb sign_1_2426 : bool_ChoiceEquality :=
        fp_sgn0 (lift_to_both0 x1_2423) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 sign_0_2424) || ((lift_to_both0 zero_0_2425) && (
            lift_to_both0 sign_1_2426)))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'fp2_is_square_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2_is_square_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'fp2_is_square_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'fp2_is_square_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition FP2_IS_SQUARE : nat :=
  2437.
Program Definition fp2_is_square (x_2429 : fp2_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb c1_2428 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_1_2_v)) in
      letb '(x1_2430, x2_2431) : (fp_t '× fp_t) := lift_to_both0 x_2429 in
      letb tv1_2432 : fp_t :=
        (lift_to_both0 x1_2430) *% (lift_to_both0 x1_2430) in
      letb tv2_2433 : fp_t :=
        (lift_to_both0 x2_2431) *% (lift_to_both0 x2_2431) in
      letb tv1_2434 : fp_t :=
        (lift_to_both0 tv1_2432) +% (lift_to_both0 tv2_2433) in
      letb tv1_2435 : fp_t :=
        nat_mod_pow_self (lift_to_both0 tv1_2434) (lift_to_both0 c1_2428) in
      letb neg1_2436 : fp_t := (nat_mod_zero ) -% (nat_mod_one ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 tv1_2435) !=.? (lift_to_both0 neg1_2436))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.

Definition c_2438_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2439%nat).
Notation "'fp2exp_inp'" :=(
  fp2_t '× fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2exp_inp'" :=(fp2_t '× fp_t : ChoiceEquality) (at level 2).
Notation "'fp2exp_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2exp_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition FP2EXP : nat :=
  2443.
Program Definition fp2exp (n_2442 : fp2_t) (k_2441 : fp_t)
  : both (CEfset ([c_2438_loc])) [interface] (fp2_t) :=
  ((letbm c_2438 : (fp_t '× fp_t) loc( c_2438_loc ) :=
        fp2fromfp (nat_mod_one ) in
      letb c_2438 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 381)) c_2438 (L := (CEfset ([c_2438_loc]))) (
            I := [interface]) (fun i_2440 c_2438 =>
            letbm c_2438 loc( c_2438_loc ) :=
              fp2mul (lift_to_both0 c_2438) (lift_to_both0 c_2438) in
            letb '(c_2438) :=
              if nat_mod_bit (lift_to_both0 k_2441) ((lift_to_both0 (
                    usize 380)) .- (lift_to_both0 i_2440)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([c_2438_loc])) (L2 := CEfset (
                  [c_2438_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm c_2438 loc( c_2438_loc ) :=
                  fp2mul (lift_to_both0 c_2438) (lift_to_both0 n_2442) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 c_2438)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 c_2438)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 c_2438)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 c_2438)
      ) : both (CEfset ([c_2438_loc])) [interface] (fp2_t)).
Fail Next Obligation.


Notation "'fp2_sqrt_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2_sqrt_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'fp2_sqrt_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2_sqrt_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition FP2_SQRT : nat :=
  2452.
Program Definition fp2_sqrt (a_2446 : fp2_t)
  : both (CEfset ([c_2438_loc])) [interface] (fp2_t) :=
  ((letb c1_2444 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_3_4_v)) in
      letb c2_2445 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_1_2_v)) in
      letb a1_2447 : (fp_t '× fp_t) :=
        fp2exp (lift_to_both0 a_2446) (lift_to_both0 c1_2444) in
      letb alpha_2448 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 a1_2447) (fp2mul (lift_to_both0 a1_2447) (
            lift_to_both0 a_2446)) in
      letb x0_2449 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 a1_2447) (lift_to_both0 a_2446) in
      letb neg1_2450 : (fp_t '× fp_t) :=
        prod_b((nat_mod_zero ) -% (nat_mod_one ), nat_mod_zero ) in
      letb b_2451 : (fp_t '× fp_t) :=
        fp2exp (fp2add (fp2fromfp (nat_mod_one )) (lift_to_both0 alpha_2448)) (
          lift_to_both0 c2_2445) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 alpha_2448) =.? (
            lift_to_both0 neg1_2450))
        then fp2mul (prod_b(nat_mod_zero , nat_mod_one )) (
          lift_to_both0 x0_2449)
        else fp2mul (lift_to_both0 b_2451) (lift_to_both0 x0_2449))
      ) : both (CEfset ([c_2438_loc])) [interface] (fp2_t)).
Fail Next Obligation.


Notation "'g2_curve_func_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_curve_func_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'g2_curve_func_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_curve_func_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition G2_CURVE_FUNC : nat :=
  2454.
Program Definition g2_curve_func (x_2453 : fp2_t)
  : both (fset.fset0) [interface] (fp2_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp2add (fp2mul (
            lift_to_both0 x_2453) (fp2mul (lift_to_both0 x_2453) (
              lift_to_both0 x_2453))) (prod_b(
            nat_mod_from_literal (_) (lift_to_both0 (@repr U128 4)),
            nat_mod_from_literal (_) (lift_to_both0 (@repr U128 4))
          )))
      ) : both (fset.fset0) [interface] (fp2_t)).
Fail Next Obligation.

Definition y_2456_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2457%nat).
Definition tv4_2455_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2458%nat).
Notation "'g2_map_to_curve_svdw_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_map_to_curve_svdw_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'g2_map_to_curve_svdw_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_map_to_curve_svdw_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_MAP_TO_CURVE_SVDW : nat :=
  2473.
Program Definition g2_map_to_curve_svdw (u_2461 : fp2_t)
  : both (CEfset ([c_2438_loc ; tv4_2455_loc ; y_2456_loc])) [interface] (
    g2_t) :=
  ((letb z_2459 : (fp_t '× fp_t) := fp2neg (fp2fromfp (nat_mod_one )) in
      letb gz_2460 : (fp_t '× fp_t) := g2_curve_func (lift_to_both0 z_2459) in
      letb tv1_2462 : (fp_t '× fp_t) :=
        fp2mul (fp2mul (lift_to_both0 u_2461) (lift_to_both0 u_2461)) (
          lift_to_both0 gz_2460) in
      letb tv2_2463 : (fp_t '× fp_t) :=
        fp2add (fp2fromfp (nat_mod_one )) (lift_to_both0 tv1_2462) in
      letb tv1_2464 : (fp_t '× fp_t) :=
        fp2sub (fp2fromfp (nat_mod_one )) (lift_to_both0 tv1_2462) in
      letb tv3_2465 : (fp_t '× fp_t) :=
        fp2inv (fp2mul (lift_to_both0 tv1_2464) (lift_to_both0 tv2_2463)) in
      letbm tv4_2455 : (fp_t '× fp_t) loc( tv4_2455_loc ) :=
        fp2_sqrt (fp2mul (fp2neg (lift_to_both0 gz_2460)) (fp2mul (fp2fromfp (
                nat_mod_from_literal (_) (lift_to_both0 (@repr U128 3)))) (
              fp2mul (lift_to_both0 z_2459) (lift_to_both0 z_2459)))) in
      letb '(tv4_2455) :=
        if fp2_sgn0 (lift_to_both0 tv4_2455) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([c_2438_loc ; tv4_2455_loc])) (
          L2 := CEfset ([c_2438_loc ; tv4_2455_loc ; y_2456_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm tv4_2455 loc( tv4_2455_loc ) :=
            fp2neg (lift_to_both0 tv4_2455) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 tv4_2455)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 tv4_2455)
         in
      letb tv5_2466 : (fp_t '× fp_t) :=
        fp2mul (fp2mul (fp2mul (lift_to_both0 u_2461) (
              lift_to_both0 tv1_2464)) (lift_to_both0 tv3_2465)) (
          lift_to_both0 tv4_2455) in
      letb tv6_2467 : (fp_t '× fp_t) :=
        fp2mul (fp2mul (fp2neg (fp2fromfp (nat_mod_from_literal (_) (
                  lift_to_both0 (@repr U128 4))))) (lift_to_both0 gz_2460)) (
          fp2inv (fp2mul (fp2fromfp (nat_mod_from_literal (_) (lift_to_both0 (
                    @repr U128 3)))) (fp2mul (lift_to_both0 z_2459) (
                lift_to_both0 z_2459)))) in
      letb x1_2468 : (fp_t '× fp_t) :=
        fp2sub (fp2mul (fp2neg (lift_to_both0 z_2459)) (fp2inv (fp2fromfp (
                nat_mod_two )))) (lift_to_both0 tv5_2466) in
      letb x2_2469 : (fp_t '× fp_t) :=
        fp2add (fp2mul (fp2neg (lift_to_both0 z_2459)) (fp2inv (fp2fromfp (
                nat_mod_two )))) (lift_to_both0 tv5_2466) in
      letb tv7_2470 : (fp_t '× fp_t) :=
        fp2mul (fp2mul (lift_to_both0 tv2_2463) (lift_to_both0 tv2_2463)) (
          lift_to_both0 tv3_2465) in
      letb x3_2471 : (fp_t '× fp_t) :=
        fp2add (lift_to_both0 z_2459) (fp2mul (lift_to_both0 tv6_2467) (fp2mul (
              lift_to_both0 tv7_2470) (lift_to_both0 tv7_2470))) in
      letb x_2472 : (fp_t '× fp_t) :=
        if is_pure (I := [interface]) (fp2_is_square (g2_curve_func (
              lift_to_both0 x1_2468)))
        then lift_to_both0 x1_2468
        else if is_pure (I := [interface]) (fp2_is_square (g2_curve_func (
              lift_to_both0 x2_2469)))
        then lift_to_both0 x2_2469
        else lift_to_both0 x3_2471 in
      letbm y_2456 : (fp_t '× fp_t) loc( y_2456_loc ) :=
        fp2_sqrt (g2_curve_func (lift_to_both0 x_2472)) in
      letb '(y_2456) :=
        if (fp2_sgn0 (lift_to_both0 u_2461)) !=.? (fp2_sgn0 (
            lift_to_both0 y_2456)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [c_2438_loc ; tv4_2455_loc ; y_2456_loc])) (L2 := CEfset (
            [c_2438_loc ; tv4_2455_loc ; y_2456_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm y_2456 loc( y_2456_loc ) := fp2neg (lift_to_both0 y_2456) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 y_2456)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 y_2456)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_2472,
          lift_to_both0 y_2456,
          lift_to_both0 ((false : bool_ChoiceEquality))
        ))
      ) : both (CEfset ([c_2438_loc ; tv4_2455_loc ; y_2456_loc])) [interface] (
      g2_t)).
Fail Next Obligation.


Notation "'psi_inp'" :=(g2_t : choice_type) (in custom pack_type at level 2).
Notation "'psi_inp'" :=(g2_t : ChoiceEquality) (at level 2).
Notation "'psi_out'" :=(g2_t : choice_type) (in custom pack_type at level 2).
Notation "'psi_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition PSI : nat :=
  2482.
Program Definition psi (p_2476 : g2_t)
  : both (CEfset ([c_2438_loc])) [interface] (g2_t) :=
  ((letb c1_2474 : (fp_t '× fp_t) :=
        fp2inv (fp2exp (prod_b(nat_mod_one , nat_mod_one )) (((
                nat_mod_zero ) -% (nat_mod_one )) *% (nat_mod_inv (
                nat_mod_from_literal (_) (lift_to_both0 (@repr U128 3)))))) in
      letb c2_2475 : (fp_t '× fp_t) :=
        fp2inv (fp2exp (prod_b(nat_mod_one , nat_mod_one )) (((
                nat_mod_zero ) -% (nat_mod_one )) *% (nat_mod_inv (
                nat_mod_two )))) in
      letb '(x_2477, y_2478, inf_2479) : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        lift_to_both0 p_2476 in
      letb qx_2480 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 c1_2474) (fp2conjugate (lift_to_both0 x_2477)) in
      letb qy_2481 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 c2_2475) (fp2conjugate (lift_to_both0 y_2478)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 qx_2480,
          lift_to_both0 qy_2481,
          lift_to_both0 inf_2479
        ))
      ) : both (CEfset ([c_2438_loc])) [interface] (g2_t)).
Fail Next Obligation.


Notation "'g2_clear_cofactor_inp'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_clear_cofactor_inp'" :=(g2_t : ChoiceEquality) (at level 2).
Notation "'g2_clear_cofactor_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_clear_cofactor_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_CLEAR_COFACTOR : nat :=
  2497.
Program Definition g2_clear_cofactor (p_2484 : g2_t)
  : both (CEfset ([c_2438_loc])) [interface] (g2_t) :=
  ((letb c1_2483 : scalar_t :=
        nat_mod_from_literal (_) (lift_to_both0 (
            @repr U128 15132376222941642752)) in
      letb t1_2485 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2mul (lift_to_both0 c1_2483) (lift_to_both0 p_2484) in
      letb t1_2486 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2neg (lift_to_both0 t1_2485) in
      letb t2_2487 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        psi (lift_to_both0 p_2484) in
      letb t3_2488 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2double (lift_to_both0 p_2484) in
      letb t3_2489 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        psi (psi (lift_to_both0 t3_2488)) in
      letb t3_2490 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 t3_2489) (g2neg (lift_to_both0 t2_2487)) in
      letb t2_2491 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 t1_2486) (lift_to_both0 t2_2487) in
      letb t2_2492 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2mul (lift_to_both0 c1_2483) (lift_to_both0 t2_2491) in
      letb t2_2493 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2neg (lift_to_both0 t2_2492) in
      letb t3_2494 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 t3_2490) (lift_to_both0 t2_2493) in
      letb t3_2495 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 t3_2494) (g2neg (lift_to_both0 t1_2486)) in
      letb q_2496 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 t3_2495) (g2neg (lift_to_both0 p_2484)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 q_2496)
      ) : both (CEfset ([c_2438_loc])) [interface] (g2_t)).
Fail Next Obligation.


Notation "'g2_hash_to_curve_svdw_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g2_hash_to_curve_svdw_inp'" :=(
  byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'g2_hash_to_curve_svdw_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_hash_to_curve_svdw_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_HASH_TO_CURVE_SVDW : nat :=
  2505.
Program Definition g2_hash_to_curve_svdw (msg_2498 : byte_seq) (
    dst_2499 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2331_loc ; b_i_2332_loc ; uniform_bytes_2333_loc ; output_2406_loc ; c_2438_loc ; tv4_2455_loc ; y_2456_loc])) [interface] (
    g2_t) :=
  ((letb u_2500 : seq fp2_t :=
        fp2_hash_to_field (lift_to_both0 msg_2498) (lift_to_both0 dst_2499) (
          lift_to_both0 (usize 2)) in
      letb q0_2501 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2_map_to_curve_svdw (seq_index (u_2500) (lift_to_both0 (usize 0))) in
      letb q1_2502 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2_map_to_curve_svdw (seq_index (u_2500) (lift_to_both0 (usize 1))) in
      letb r_2503 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 q0_2501) (lift_to_both0 q1_2502) in
      letb p_2504 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_clear_cofactor (lift_to_both0 r_2503) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2504)
      ) : both (CEfset (
        [l_i_b_str_2331_loc ; b_i_2332_loc ; uniform_bytes_2333_loc ; output_2406_loc ; c_2438_loc ; tv4_2455_loc ; y_2456_loc])) [interface] (
      g2_t)).
Fail Next Obligation.


Notation "'g2_encode_to_curve_svdw_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g2_encode_to_curve_svdw_inp'" :=(
  byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'g2_encode_to_curve_svdw_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_encode_to_curve_svdw_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_ENCODE_TO_CURVE_SVDW : nat :=
  2511.
Program Definition g2_encode_to_curve_svdw (msg_2506 : byte_seq) (
    dst_2507 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2331_loc ; b_i_2332_loc ; uniform_bytes_2333_loc ; output_2406_loc ; c_2438_loc ; tv4_2455_loc ; y_2456_loc])) [interface] (
    g2_t) :=
  ((letb u_2508 : seq fp2_t :=
        fp2_hash_to_field (lift_to_both0 msg_2506) (lift_to_both0 dst_2507) (
          lift_to_both0 (usize 1)) in
      letb q_2509 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_map_to_curve_svdw (seq_index (u_2508) (lift_to_both0 (usize 0))) in
      letb p_2510 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_clear_cofactor (lift_to_both0 q_2509) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2510)
      ) : both (CEfset (
        [l_i_b_str_2331_loc ; b_i_2332_loc ; uniform_bytes_2333_loc ; output_2406_loc ; c_2438_loc ; tv4_2455_loc ; y_2456_loc])) [interface] (
      g2_t)).
Fail Next Obligation.

Definition g1_iso_a_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 5707120929990979)) : uint64;
    (secret (@repr U64 4425131892511951234)) : uint64;
    (secret (@repr U64 12748169179688756904)) : uint64;
    (secret (@repr U64 15629909748249821612)) : uint64;
    (secret (@repr U64 10994253769421683071)) : uint64;
    (secret (@repr U64 6698022561392380957)) : uint64
  ].

Definition g1_iso_b_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1360808972976160816)) : uint64;
    (secret (@repr U64 111203405409480251)) : uint64;
    (secret (@repr U64 2312248699302920304)) : uint64;
    (secret (@repr U64 11581500465278574325)) : uint64;
    (secret (@repr U64 6495071758858381989)) : uint64;
    (secret (@repr U64 15117538217124375520)) : uint64
  ].

Definition g1_xnum_k_0_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1270119733718627136)) : uint64;
    (secret (@repr U64 13261148298159854981)) : uint64;
    (secret (@repr U64 7723742117508874335)) : uint64;
    (secret (@repr U64 17465657917644792520)) : uint64;
    (secret (@repr U64 6201670911048166766)) : uint64;
    (secret (@repr U64 12586459670690286007)) : uint64
  ].

Definition g1_xnum_k_1_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1668951808976071471)) : uint64;
    (secret (@repr U64 398773841247578140)) : uint64;
    (secret (@repr U64 8941869963990959127)) : uint64;
    (secret (@repr U64 17682789360670468203)) : uint64;
    (secret (@repr U64 5204176168283587414)) : uint64;
    (secret (@repr U64 16732261237459223483)) : uint64
  ].

Definition g1_xnum_k_2_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 960393023080265964)) : uint64;
    (secret (@repr U64 2094253841180170779)) : uint64;
    (secret (@repr U64 14844748873776858085)) : uint64;
    (secret (@repr U64 7528018573573808732)) : uint64;
    (secret (@repr U64 10776056440809943711)) : uint64;
    (secret (@repr U64 16147550488514976944)) : uint64
  ].

Definition g1_xnum_k_3_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1691355743628586423)) : uint64;
    (secret (@repr U64 5622191986793862162)) : uint64;
    (secret (@repr U64 15561595211679121189)) : uint64;
    (secret (@repr U64 17416319752018800771)) : uint64;
    (secret (@repr U64 5996228842464768403)) : uint64;
    (secret (@repr U64 14245880009877842017)) : uint64
  ].

Definition g1_xnum_k_4_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1051997788391994435)) : uint64;
    (secret (@repr U64 7368650625050054228)) : uint64;
    (secret (@repr U64 11086623519836470079)) : uint64;
    (secret (@repr U64 607681821319080984)) : uint64;
    (secret (@repr U64 10978131499682789316)) : uint64;
    (secret (@repr U64 5842660658088809945)) : uint64
  ].

Definition g1_xnum_k_5_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1598992431623377919)) : uint64;
    (secret (@repr U64 130921168661596853)) : uint64;
    (secret (@repr U64 15797696746983946651)) : uint64;
    (secret (@repr U64 11444679715590672272)) : uint64;
    (secret (@repr U64 11567228658253249817)) : uint64;
    (secret (@repr U64 14777367860349315459)) : uint64
  ].

Definition g1_xnum_k_6_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 967946631563726121)) : uint64;
    (secret (@repr U64 7653628713030275775)) : uint64;
    (secret (@repr U64 12760252618317466849)) : uint64;
    (secret (@repr U64 10378793938173061930)) : uint64;
    (secret (@repr U64 10205808941053849290)) : uint64;
    (secret (@repr U64 15985511645807504772)) : uint64
  ].

Definition g1_xnum_k_7_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1709149555065084898)) : uint64;
    (secret (@repr U64 16750075057192140371)) : uint64;
    (secret (@repr U64 3849985779734105521)) : uint64;
    (secret (@repr U64 11998370262181639475)) : uint64;
    (secret (@repr U64 4159013751748851119)) : uint64;
    (secret (@repr U64 11298218755092433038)) : uint64
  ].

Definition g1_xnum_k_8_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 580186936973955012)) : uint64;
    (secret (@repr U64 8903813505199544589)) : uint64;
    (secret (@repr U64 14140024565662700916)) : uint64;
    (secret (@repr U64 11728946595272970718)) : uint64;
    (secret (@repr U64 5738313744366653077)) : uint64;
    (secret (@repr U64 7886252005760951063)) : uint64
  ].

Definition g1_xnum_k_9_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1628930385436977092)) : uint64;
    (secret (@repr U64 3318087848058654498)) : uint64;
    (secret (@repr U64 15937899882900905113)) : uint64;
    (secret (@repr U64 7449821001803307903)) : uint64;
    (secret (@repr U64 11752436998487615353)) : uint64;
    (secret (@repr U64 9161465579737517214)) : uint64
  ].

Definition g1_xnum_k_10_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1167027828517898210)) : uint64;
    (secret (@repr U64 8275623842221021965)) : uint64;
    (secret (@repr U64 18049808134997311382)) : uint64;
    (secret (@repr U64 15351349873550116966)) : uint64;
    (secret (@repr U64 17769927732099571180)) : uint64;
    (secret (@repr U64 14584871380308065147)) : uint64
  ].

Definition g1_xnum_k_11_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 495550047642324592)) : uint64;
    (secret (@repr U64 13627494601717575229)) : uint64;
    (secret (@repr U64 3591512392926246844)) : uint64;
    (secret (@repr U64 2576269112800734056)) : uint64;
    (secret (@repr U64 14000314106239596831)) : uint64;
    (secret (@repr U64 12234233096825917993)) : uint64
  ].

Definition g1_xden_k_0_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 633474091881273774)) : uint64;
    (secret (@repr U64 1779737893574802031)) : uint64;
    (secret (@repr U64 132274872219551930)) : uint64;
    (secret (@repr U64 11283074393783708770)) : uint64;
    (secret (@repr U64 13067430171545714168)) : uint64;
    (secret (@repr U64 11041975239630265116)) : uint64
  ].

Definition g1_xden_k_1_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1321272531362356291)) : uint64;
    (secret (@repr U64 5238936591227237942)) : uint64;
    (secret (@repr U64 8089002360232247308)) : uint64;
    (secret (@repr U64 82967328719421271)) : uint64;
    (secret (@repr U64 1430641118356186857)) : uint64;
    (secret (@repr U64 16557527386785790975)) : uint64
  ].

Definition g1_xden_k_2_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 804282852993868382)) : uint64;
    (secret (@repr U64 9311163821600184607)) : uint64;
    (secret (@repr U64 8037026956533927121)) : uint64;
    (secret (@repr U64 18205324308570099372)) : uint64;
    (secret (@repr U64 15466434890074226396)) : uint64;
    (secret (@repr U64 18213183315621985817)) : uint64
  ].

Definition g1_xden_k_3_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 234844145893171966)) : uint64;
    (secret (@repr U64 14428037799351479124)) : uint64;
    (secret (@repr U64 6559532710647391569)) : uint64;
    (secret (@repr U64 6110444250091843536)) : uint64;
    (secret (@repr U64 5293652763671852484)) : uint64;
    (secret (@repr U64 1373009181854280920)) : uint64
  ].

Definition g1_xden_k_4_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1416629893867312296)) : uint64;
    (secret (@repr U64 751851957792514173)) : uint64;
    (secret (@repr U64 18437674587247370939)) : uint64;
    (secret (@repr U64 10190314345946351322)) : uint64;
    (secret (@repr U64 11228207967368476701)) : uint64;
    (secret (@repr U64 6025034940388909598)) : uint64
  ].

Definition g1_xden_k_5_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1041270466333271993)) : uint64;
    (secret (@repr U64 6140956605115975401)) : uint64;
    (secret (@repr U64 4131830461445745997)) : uint64;
    (secret (@repr U64 739642499118176303)) : uint64;
    (secret (@repr U64 8358912131254619921)) : uint64;
    (secret (@repr U64 13847998906088228005)) : uint64
  ].

Definition g1_xden_k_6_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 536714149743900185)) : uint64;
    (secret (@repr U64 1098328982230230817)) : uint64;
    (secret (@repr U64 6273329123533496713)) : uint64;
    (secret (@repr U64 5633448088282521244)) : uint64;
    (secret (@repr U64 16894043798660571244)) : uint64;
    (secret (@repr U64 17016134625831438906)) : uint64
  ].

Definition g1_xden_k_7_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1488347500898461874)) : uint64;
    (secret (@repr U64 3509418672874520985)) : uint64;
    (secret (@repr U64 7962192351555381416)) : uint64;
    (secret (@repr U64 1843909372225399896)) : uint64;
    (secret (@repr U64 1127511003250156243)) : uint64;
    (secret (@repr U64 1294742680819751518)) : uint64
  ].

Definition g1_xden_k_8_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 725340084226051970)) : uint64;
    (secret (@repr U64 6814521545734988748)) : uint64;
    (secret (@repr U64 16176803544133875307)) : uint64;
    (secret (@repr U64 8363199516777220149)) : uint64;
    (secret (@repr U64 252877309218538352)) : uint64;
    (secret (@repr U64 5149562959837648449)) : uint64
  ].

Definition g1_xden_k_9_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 675470927100193492)) : uint64;
    (secret (@repr U64 5146891164735334016)) : uint64;
    (secret (@repr U64 17762958817130696759)) : uint64;
    (secret (@repr U64 8565656522589412373)) : uint64;
    (secret (@repr U64 10599026333335446784)) : uint64;
    (secret (@repr U64 3270603789344496906)) : uint64
  ].

Definition g1_ynum_k_0_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 652344406751465184)) : uint64;
    (secret (@repr U64 2710356675495255290)) : uint64;
    (secret (@repr U64 1273695771440998738)) : uint64;
    (secret (@repr U64 3121750372618945491)) : uint64;
    (secret (@repr U64 14775319642720936898)) : uint64;
    (secret (@repr U64 13733803417833814835)) : uint64
  ].

Definition g1_ynum_k_1_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1389807578337138705)) : uint64;
    (secret (@repr U64 15352831428748068483)) : uint64;
    (secret (@repr U64 1307144967559264317)) : uint64;
    (secret (@repr U64 1121505450578652468)) : uint64;
    (secret (@repr U64 15475889019760388287)) : uint64;
    (secret (@repr U64 16183658160488302230)) : uint64
  ].

Definition g1_ynum_k_2_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 57553299067792998)) : uint64;
    (secret (@repr U64 17628079362768849300)) : uint64;
    (secret (@repr U64 2689461337731570914)) : uint64;
    (secret (@repr U64 14070580367580990887)) : uint64;
    (secret (@repr U64 15162865775551710499)) : uint64;
    (secret (@repr U64 13321614990632673782)) : uint64
  ].

Definition g1_ynum_k_3_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 141972750621744161)) : uint64;
    (secret (@repr U64 8689824239172478807)) : uint64;
    (secret (@repr U64 15288216298323671324)) : uint64;
    (secret (@repr U64 712874875091754233)) : uint64;
    (secret (@repr U64 16014900032503684588)) : uint64;
    (secret (@repr U64 11976580453200426187)) : uint64
  ].

Definition g1_ynum_k_4_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 633886036738506515)) : uint64;
    (secret (@repr U64 6678644607214234052)) : uint64;
    (secret (@repr U64 1825425679455244472)) : uint64;
    (secret (@repr U64 8755912272271186652)) : uint64;
    (secret (@repr U64 3379943669301788840)) : uint64;
    (secret (@repr U64 4735212769449148123)) : uint64
  ].

Definition g1_ynum_k_5_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1612358804494830442)) : uint64;
    (secret (@repr U64 2454990789666711200)) : uint64;
    (secret (@repr U64 8405916841409361853)) : uint64;
    (secret (@repr U64 8525415512662168654)) : uint64;
    (secret (@repr U64 2323684950984523890)) : uint64;
    (secret (@repr U64 11074978966450447856)) : uint64
  ].

Definition g1_ynum_k_6_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 336375361001233340)) : uint64;
    (secret (@repr U64 12882959944969186108)) : uint64;
    (secret (@repr U64 16671121624101127371)) : uint64;
    (secret (@repr U64 5922586712221110071)) : uint64;
    (secret (@repr U64 5163511947597922654)) : uint64;
    (secret (@repr U64 14511152726087948018)) : uint64
  ].

Definition g1_ynum_k_7_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 686738286210365551)) : uint64;
    (secret (@repr U64 16039894141796533876)) : uint64;
    (secret (@repr U64 1660145734357211167)) : uint64;
    (secret (@repr U64 18231571463891878950)) : uint64;
    (secret (@repr U64 4825120264949852469)) : uint64;
    (secret (@repr U64 11627815551290637097)) : uint64
  ].

Definition g1_ynum_k_8_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 719520515476580427)) : uint64;
    (secret (@repr U64 16756942182913253819)) : uint64;
    (secret (@repr U64 10320769399998235244)) : uint64;
    (secret (@repr U64 2200974244968450750)) : uint64;
    (secret (@repr U64 7626373186594408355)) : uint64;
    (secret (@repr U64 6933025920263103879)) : uint64
  ].

Definition g1_ynum_k_9_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1016611174344998325)) : uint64;
    (secret (@repr U64 2466492548686891555)) : uint64;
    (secret (@repr U64 14135124294293452542)) : uint64;
    (secret (@repr U64 475233659467912251)) : uint64;
    (secret (@repr U64 11186783513499056751)) : uint64;
    (secret (@repr U64 3147922594245844016)) : uint64
  ].

Definition g1_ynum_k_10_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1833315000454533566)) : uint64;
    (secret (@repr U64 1007974600900082579)) : uint64;
    (secret (@repr U64 14785260176242854207)) : uint64;
    (secret (@repr U64 15066861003931772432)) : uint64;
    (secret (@repr U64 3584647998681889532)) : uint64;
    (secret (@repr U64 16722834201330696498)) : uint64
  ].

Definition g1_ynum_k_11_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1780164921828767454)) : uint64;
    (secret (@repr U64 13337622794239929804)) : uint64;
    (secret (@repr U64 5923739534552515142)) : uint64;
    (secret (@repr U64 3345046972101780530)) : uint64;
    (secret (@repr U64 5321510883028162054)) : uint64;
    (secret (@repr U64 14846055306840460686)) : uint64
  ].

Definition g1_ynum_k_12_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 799438051374502809)) : uint64;
    (secret (@repr U64 15083972834952036164)) : uint64;
    (secret (@repr U64 8838227588559581326)) : uint64;
    (secret (@repr U64 13846054168121598783)) : uint64;
    (secret (@repr U64 488730451382505970)) : uint64;
    (secret (@repr U64 958146249756188408)) : uint64
  ].

Definition g1_ynum_k_13_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 163716820423854747)) : uint64;
    (secret (@repr U64 8285498163857659356)) : uint64;
    (secret (@repr U64 8465424830341846400)) : uint64;
    (secret (@repr U64 1433942577299613084)) : uint64;
    (secret (@repr U64 14325828012864645732)) : uint64;
    (secret (@repr U64 4817114329354076467)) : uint64
  ].

Definition g1_ynum_k_14_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 414658151749832465)) : uint64;
    (secret (@repr U64 189531577938912252)) : uint64;
    (secret (@repr U64 6802473390048830824)) : uint64;
    (secret (@repr U64 15684647020317539556)) : uint64;
    (secret (@repr U64 7755485098777620407)) : uint64;
    (secret (@repr U64 9685868895687483979)) : uint64
  ].

Definition g1_ynum_k_15_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1578157964224562126)) : uint64;
    (secret (@repr U64 5666948055268535989)) : uint64;
    (secret (@repr U64 14634479491382401593)) : uint64;
    (secret (@repr U64 6317940024988860850)) : uint64;
    (secret (@repr U64 13142913832013798519)) : uint64;
    (secret (@repr U64 338991247778166276)) : uint64
  ].

Definition g1_yden_k_0_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1590100849350973618)) : uint64;
    (secret (@repr U64 5915497081334721257)) : uint64;
    (secret (@repr U64 6924968209373727718)) : uint64;
    (secret (@repr U64 17204633670617869946)) : uint64;
    (secret (@repr U64 572916540828819565)) : uint64;
    (secret (@repr U64 92203205520679873)) : uint64
  ].

Definition g1_yden_k_1_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1829261189398470686)) : uint64;
    (secret (@repr U64 1877083417397643448)) : uint64;
    (secret (@repr U64 9640042925497046428)) : uint64;
    (secret (@repr U64 11862766565471805471)) : uint64;
    (secret (@repr U64 8693114993904885301)) : uint64;
    (secret (@repr U64 3672140328108400701)) : uint64
  ].

Definition g1_yden_k_2_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 400243331105348135)) : uint64;
    (secret (@repr U64 8046435537999802711)) : uint64;
    (secret (@repr U64 8702226981475745585)) : uint64;
    (secret (@repr U64 879791671491744492)) : uint64;
    (secret (@repr U64 11994630442058346377)) : uint64;
    (secret (@repr U64 2172204746352322546)) : uint64
  ].

Definition g1_yden_k_3_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1637008473169220501)) : uint64;
    (secret (@repr U64 17441636237435581649)) : uint64;
    (secret (@repr U64 15066165676546511630)) : uint64;
    (secret (@repr U64 1314387578457599809)) : uint64;
    (secret (@repr U64 8247046336453711789)) : uint64;
    (secret (@repr U64 12164906044230685718)) : uint64
  ].

Definition g1_yden_k_4_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 855930740911588324)) : uint64;
    (secret (@repr U64 12685735333705453020)) : uint64;
    (secret (@repr U64 14326404096614579120)) : uint64;
    (secret (@repr U64 6066025509460822294)) : uint64;
    (secret (@repr U64 11676450493790612973)) : uint64;
    (secret (@repr U64 15724621714793234461)) : uint64
  ].

Definition g1_yden_k_5_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 637792788410719021)) : uint64;
    (secret (@repr U64 11507373155986977154)) : uint64;
    (secret (@repr U64 13186912195705886849)) : uint64;
    (secret (@repr U64 14262012144631372388)) : uint64;
    (secret (@repr U64 5328758613570342114)) : uint64;
    (secret (@repr U64 199925847119476652)) : uint64
  ].

Definition g1_yden_k_6_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1612297190139091759)) : uint64;
    (secret (@repr U64 14103733843373163083)) : uint64;
    (secret (@repr U64 6840121186619029743)) : uint64;
    (secret (@repr U64 6760859324815900753)) : uint64;
    (secret (@repr U64 15418807805142572985)) : uint64;
    (secret (@repr U64 4402853133867972444)) : uint64
  ].

Definition g1_yden_k_7_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1631410310868805610)) : uint64;
    (secret (@repr U64 269334146695233390)) : uint64;
    (secret (@repr U64 16547411811928854487)) : uint64;
    (secret (@repr U64 18353100669930795314)) : uint64;
    (secret (@repr U64 13339932232668798692)) : uint64;
    (secret (@repr U64 6984591927261867737)) : uint64
  ].

Definition g1_yden_k_8_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1758313625630302499)) : uint64;
    (secret (@repr U64 1881349400343039172)) : uint64;
    (secret (@repr U64 18013005311323887904)) : uint64;
    (secret (@repr U64 12377427846571989832)) : uint64;
    (secret (@repr U64 5967237584920922243)) : uint64;
    (secret (@repr U64 7720081932193848650)) : uint64
  ].

Definition g1_yden_k_9_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1619701357752249884)) : uint64;
    (secret (@repr U64 16898074901591262352)) : uint64;
    (secret (@repr U64 3609344159736760251)) : uint64;
    (secret (@repr U64 5983130161189999867)) : uint64;
    (secret (@repr U64 14355327869992416094)) : uint64;
    (secret (@repr U64 3778226018344582997)) : uint64
  ].

Definition g1_yden_k_10_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 347606589330687421)) : uint64;
    (secret (@repr U64 5255719044972187933)) : uint64;
    (secret (@repr U64 11271894388753671721)) : uint64;
    (secret (@repr U64 1033887512062764488)) : uint64;
    (secret (@repr U64 8189165486932690436)) : uint64;
    (secret (@repr U64 70004379462101672)) : uint64
  ].

Definition g1_yden_k_11_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 778202887894139711)) : uint64;
    (secret (@repr U64 17691595219776375879)) : uint64;
    (secret (@repr U64 9193253711563866834)) : uint64;
    (secret (@repr U64 10092455202333888821)) : uint64;
    (secret (@repr U64 1655469341950262250)) : uint64;
    (secret (@repr U64 10845992994110574738)) : uint64
  ].

Definition g1_yden_k_12_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 781015344221683683)) : uint64;
    (secret (@repr U64 14078588081290548374)) : uint64;
    (secret (@repr U64 6067271023149908518)) : uint64;
    (secret (@repr U64 9033357708497886086)) : uint64;
    (secret (@repr U64 10592474449179118273)) : uint64;
    (secret (@repr U64 2204988348113831372)) : uint64
  ].

Definition g1_yden_k_13_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 172830037692534587)) : uint64;
    (secret (@repr U64 7101012286790006514)) : uint64;
    (secret (@repr U64 13787308004332873665)) : uint64;
    (secret (@repr U64 14660498759553796110)) : uint64;
    (secret (@repr U64 4757234684169342080)) : uint64;
    (secret (@repr U64 15130647872920159991)) : uint64
  ].

Definition g1_yden_k_14_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1013206390650290238)) : uint64;
    (secret (@repr U64 7720336747103001025)) : uint64;
    (secret (@repr U64 8197694151986493523)) : uint64;
    (secret (@repr U64 3625112747029342752)) : uint64;
    (secret (@repr U64 6675167463148394368)) : uint64;
    (secret (@repr U64 4905905684016745359)) : uint64
  ].

Definition y_2513_loc : ChoiceEqualityLocation :=
  (fp_t ; 2514%nat).
Definition x1_2512_loc : ChoiceEqualityLocation :=
  (fp_t ; 2515%nat).
Notation "'g1_simple_swu_iso_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_simple_swu_iso_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'g1_simple_swu_iso_out'" :=((fp_t '× fp_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'g1_simple_swu_iso_out'" :=((fp_t '× fp_t
  ) : ChoiceEquality) (at level 2).
Definition G1_SIMPLE_SWU_ISO : nat :=
  2525.
Program Definition g1_simple_swu_iso (u_2519 : fp_t)
  : both (CEfset ([x1_2512_loc ; y_2513_loc])) [interface] ((fp_t '× fp_t)) :=
  ((letb z_2516 : fp_t :=
        nat_mod_from_literal (_) (lift_to_both0 (@repr U128 11)) in
      letb a_2517 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (
            lift_to_both0 g1_iso_a_v)) in
      letb b_2518 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (
            lift_to_both0 g1_iso_b_v)) in
      letb tv1_2520 : fp_t :=
        nat_mod_inv ((((lift_to_both0 z_2516) *% (lift_to_both0 z_2516)) *% (
              nat_mod_exp (lift_to_both0 u_2519) (lift_to_both0 (
                  @repr U32 4)))) +% (((lift_to_both0 z_2516) *% (
                lift_to_both0 u_2519)) *% (lift_to_both0 u_2519))) in
      letbm x1_2512 : fp_t loc( x1_2512_loc ) :=
        (((nat_mod_zero ) -% (lift_to_both0 b_2518)) *% (nat_mod_inv (
              lift_to_both0 a_2517))) *% ((nat_mod_one ) +% (
            lift_to_both0 tv1_2520)) in
      letb '(x1_2512) :=
        if (lift_to_both0 tv1_2520) =.? (nat_mod_zero ) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([x1_2512_loc])) (L2 := CEfset (
            [x1_2512_loc ; y_2513_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x1_2512 loc( x1_2512_loc ) :=
            (lift_to_both0 b_2518) *% (nat_mod_inv ((lift_to_both0 z_2516) *% (
                  lift_to_both0 a_2517))) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 x1_2512)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 x1_2512)
         in
      letb gx1_2521 : fp_t :=
        ((nat_mod_exp (lift_to_both0 x1_2512) (lift_to_both0 (
                @repr U32 3))) +% ((lift_to_both0 a_2517) *% (
              lift_to_both0 x1_2512))) +% (lift_to_both0 b_2518) in
      letb x2_2522 : fp_t :=
        (((lift_to_both0 z_2516) *% (lift_to_both0 u_2519)) *% (
            lift_to_both0 u_2519)) *% (lift_to_both0 x1_2512) in
      letb gx2_2523 : fp_t :=
        ((nat_mod_exp (lift_to_both0 x2_2522) (lift_to_both0 (
                @repr U32 3))) +% ((lift_to_both0 a_2517) *% (
              lift_to_both0 x2_2522))) +% (lift_to_both0 b_2518) in
      letb '(x_2524, y_2513) : (fp_t '× fp_t) :=
        if is_pure (I := [interface]) (fp_is_square (lift_to_both0 gx1_2521))
        then prod_b(lift_to_both0 x1_2512, fp_sqrt (lift_to_both0 gx1_2521))
        else prod_b(lift_to_both0 x2_2522, fp_sqrt (lift_to_both0 gx2_2523)) in
      letb '(y_2513) :=
        if (fp_sgn0 (lift_to_both0 u_2519)) !=.? (fp_sgn0 (
            lift_to_both0 y_2513)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([x1_2512_loc ; y_2513_loc])) (
          L2 := CEfset ([x1_2512_loc ; y_2513_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm y_2513 loc( y_2513_loc ) :=
            (nat_mod_zero ) -% (lift_to_both0 y_2513) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 y_2513)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 y_2513)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_2524,
          lift_to_both0 y_2513
        ))
      ) : both (CEfset ([x1_2512_loc ; y_2513_loc])) [interface] ((fp_t '× fp_t
      ))).
Fail Next Obligation.

Definition xden_2532_loc : ChoiceEqualityLocation :=
  (fp_t ; 2539%nat).
Definition xnum_2530_loc : ChoiceEqualityLocation :=
  (fp_t ; 2540%nat).
Definition xx_2537_loc : ChoiceEqualityLocation :=
  (fp_t ; 2541%nat).
Definition xx_2531_loc : ChoiceEqualityLocation :=
  (fp_t ; 2542%nat).
Definition xx_2533_loc : ChoiceEqualityLocation :=
  (fp_t ; 2543%nat).
Definition xx_2535_loc : ChoiceEqualityLocation :=
  (fp_t ; 2544%nat).
Definition xnum_k_2526_loc : ChoiceEqualityLocation :=
  (seq fp_t ; 2545%nat).
Definition yden_2536_loc : ChoiceEqualityLocation :=
  (fp_t ; 2546%nat).
Definition ynum_k_2528_loc : ChoiceEqualityLocation :=
  (seq fp_t ; 2547%nat).
Definition yden_k_2529_loc : ChoiceEqualityLocation :=
  (seq fp_t ; 2548%nat).
Definition xden_k_2527_loc : ChoiceEqualityLocation :=
  (seq fp_t ; 2549%nat).
Definition ynum_2534_loc : ChoiceEqualityLocation :=
  (fp_t ; 2550%nat).
Definition inf_2538_loc : ChoiceEqualityLocation :=
  (bool_ChoiceEquality ; 2551%nat).
Notation "'g1_isogeny_map_inp'" :=(
  fp_t '× fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_isogeny_map_inp'" :=(fp_t '× fp_t : ChoiceEquality) (at level 2).
Notation "'g1_isogeny_map_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_isogeny_map_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1_ISOGENY_MAP : nat :=
  2560.
Program Definition g1_isogeny_map (x_2553 : fp_t) (y_2558 : fp_t)
  : both (CEfset (
      [xnum_k_2526_loc ; xden_k_2527_loc ; ynum_k_2528_loc ; yden_k_2529_loc ; xnum_2530_loc ; xx_2531_loc ; xden_2532_loc ; xx_2533_loc ; ynum_2534_loc ; xx_2535_loc ; yden_2536_loc ; xx_2537_loc ; inf_2538_loc])) [interface] (
    g1_t) :=
  ((letbm xnum_k_2526 : seq fp_t loc( xnum_k_2526_loc ) :=
        seq_new_ (default : fp_t) (lift_to_both0 (usize 12)) in
      letb xnum_k_2526 : seq fp_t :=
        seq_upd xnum_k_2526 (lift_to_both0 (usize 0)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_0_v)))) in
      letb xnum_k_2526 : seq fp_t :=
        seq_upd xnum_k_2526 (lift_to_both0 (usize 1)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_1_v)))) in
      letb xnum_k_2526 : seq fp_t :=
        seq_upd xnum_k_2526 (lift_to_both0 (usize 2)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_2_v)))) in
      letb xnum_k_2526 : seq fp_t :=
        seq_upd xnum_k_2526 (lift_to_both0 (usize 3)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_3_v)))) in
      letb xnum_k_2526 : seq fp_t :=
        seq_upd xnum_k_2526 (lift_to_both0 (usize 4)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_4_v)))) in
      letb xnum_k_2526 : seq fp_t :=
        seq_upd xnum_k_2526 (lift_to_both0 (usize 5)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_5_v)))) in
      letb xnum_k_2526 : seq fp_t :=
        seq_upd xnum_k_2526 (lift_to_both0 (usize 6)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_6_v)))) in
      letb xnum_k_2526 : seq fp_t :=
        seq_upd xnum_k_2526 (lift_to_both0 (usize 7)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_7_v)))) in
      letb xnum_k_2526 : seq fp_t :=
        seq_upd xnum_k_2526 (lift_to_both0 (usize 8)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_8_v)))) in
      letb xnum_k_2526 : seq fp_t :=
        seq_upd xnum_k_2526 (lift_to_both0 (usize 9)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_9_v)))) in
      letb xnum_k_2526 : seq fp_t :=
        seq_upd xnum_k_2526 (lift_to_both0 (usize 10)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_10_v)))) in
      letb xnum_k_2526 : seq fp_t :=
        seq_upd xnum_k_2526 (lift_to_both0 (usize 11)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_11_v)))) in
      letbm xden_k_2527 : seq fp_t loc( xden_k_2527_loc ) :=
        seq_new_ (default : fp_t) (lift_to_both0 (usize 10)) in
      letb xden_k_2527 : seq fp_t :=
        seq_upd xden_k_2527 (lift_to_both0 (usize 0)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_0_v)))) in
      letb xden_k_2527 : seq fp_t :=
        seq_upd xden_k_2527 (lift_to_both0 (usize 1)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_1_v)))) in
      letb xden_k_2527 : seq fp_t :=
        seq_upd xden_k_2527 (lift_to_both0 (usize 2)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_2_v)))) in
      letb xden_k_2527 : seq fp_t :=
        seq_upd xden_k_2527 (lift_to_both0 (usize 3)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_3_v)))) in
      letb xden_k_2527 : seq fp_t :=
        seq_upd xden_k_2527 (lift_to_both0 (usize 4)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_4_v)))) in
      letb xden_k_2527 : seq fp_t :=
        seq_upd xden_k_2527 (lift_to_both0 (usize 5)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_5_v)))) in
      letb xden_k_2527 : seq fp_t :=
        seq_upd xden_k_2527 (lift_to_both0 (usize 6)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_6_v)))) in
      letb xden_k_2527 : seq fp_t :=
        seq_upd xden_k_2527 (lift_to_both0 (usize 7)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_7_v)))) in
      letb xden_k_2527 : seq fp_t :=
        seq_upd xden_k_2527 (lift_to_both0 (usize 8)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_8_v)))) in
      letb xden_k_2527 : seq fp_t :=
        seq_upd xden_k_2527 (lift_to_both0 (usize 9)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_9_v)))) in
      letbm ynum_k_2528 : seq fp_t loc( ynum_k_2528_loc ) :=
        seq_new_ (default : fp_t) (lift_to_both0 (usize 16)) in
      letb ynum_k_2528 : seq fp_t :=
        seq_upd ynum_k_2528 (lift_to_both0 (usize 0)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_0_v)))) in
      letb ynum_k_2528 : seq fp_t :=
        seq_upd ynum_k_2528 (lift_to_both0 (usize 1)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_1_v)))) in
      letb ynum_k_2528 : seq fp_t :=
        seq_upd ynum_k_2528 (lift_to_both0 (usize 2)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_2_v)))) in
      letb ynum_k_2528 : seq fp_t :=
        seq_upd ynum_k_2528 (lift_to_both0 (usize 3)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_3_v)))) in
      letb ynum_k_2528 : seq fp_t :=
        seq_upd ynum_k_2528 (lift_to_both0 (usize 4)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_4_v)))) in
      letb ynum_k_2528 : seq fp_t :=
        seq_upd ynum_k_2528 (lift_to_both0 (usize 5)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_5_v)))) in
      letb ynum_k_2528 : seq fp_t :=
        seq_upd ynum_k_2528 (lift_to_both0 (usize 6)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_6_v)))) in
      letb ynum_k_2528 : seq fp_t :=
        seq_upd ynum_k_2528 (lift_to_both0 (usize 7)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_7_v)))) in
      letb ynum_k_2528 : seq fp_t :=
        seq_upd ynum_k_2528 (lift_to_both0 (usize 8)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_8_v)))) in
      letb ynum_k_2528 : seq fp_t :=
        seq_upd ynum_k_2528 (lift_to_both0 (usize 9)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_9_v)))) in
      letb ynum_k_2528 : seq fp_t :=
        seq_upd ynum_k_2528 (lift_to_both0 (usize 10)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_10_v)))) in
      letb ynum_k_2528 : seq fp_t :=
        seq_upd ynum_k_2528 (lift_to_both0 (usize 11)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_11_v)))) in
      letb ynum_k_2528 : seq fp_t :=
        seq_upd ynum_k_2528 (lift_to_both0 (usize 12)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_12_v)))) in
      letb ynum_k_2528 : seq fp_t :=
        seq_upd ynum_k_2528 (lift_to_both0 (usize 13)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_13_v)))) in
      letb ynum_k_2528 : seq fp_t :=
        seq_upd ynum_k_2528 (lift_to_both0 (usize 14)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_14_v)))) in
      letb ynum_k_2528 : seq fp_t :=
        seq_upd ynum_k_2528 (lift_to_both0 (usize 15)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_15_v)))) in
      letbm yden_k_2529 : seq fp_t loc( yden_k_2529_loc ) :=
        seq_new_ (default : fp_t) (lift_to_both0 (usize 15)) in
      letb yden_k_2529 : seq fp_t :=
        seq_upd yden_k_2529 (lift_to_both0 (usize 0)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_0_v)))) in
      letb yden_k_2529 : seq fp_t :=
        seq_upd yden_k_2529 (lift_to_both0 (usize 1)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_1_v)))) in
      letb yden_k_2529 : seq fp_t :=
        seq_upd yden_k_2529 (lift_to_both0 (usize 2)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_2_v)))) in
      letb yden_k_2529 : seq fp_t :=
        seq_upd yden_k_2529 (lift_to_both0 (usize 3)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_3_v)))) in
      letb yden_k_2529 : seq fp_t :=
        seq_upd yden_k_2529 (lift_to_both0 (usize 4)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_4_v)))) in
      letb yden_k_2529 : seq fp_t :=
        seq_upd yden_k_2529 (lift_to_both0 (usize 5)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_5_v)))) in
      letb yden_k_2529 : seq fp_t :=
        seq_upd yden_k_2529 (lift_to_both0 (usize 6)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_6_v)))) in
      letb yden_k_2529 : seq fp_t :=
        seq_upd yden_k_2529 (lift_to_both0 (usize 7)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_7_v)))) in
      letb yden_k_2529 : seq fp_t :=
        seq_upd yden_k_2529 (lift_to_both0 (usize 8)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_8_v)))) in
      letb yden_k_2529 : seq fp_t :=
        seq_upd yden_k_2529 (lift_to_both0 (usize 9)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_9_v)))) in
      letb yden_k_2529 : seq fp_t :=
        seq_upd yden_k_2529 (lift_to_both0 (usize 10)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_10_v)))) in
      letb yden_k_2529 : seq fp_t :=
        seq_upd yden_k_2529 (lift_to_both0 (usize 11)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_11_v)))) in
      letb yden_k_2529 : seq fp_t :=
        seq_upd yden_k_2529 (lift_to_both0 (usize 12)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_12_v)))) in
      letb yden_k_2529 : seq fp_t :=
        seq_upd yden_k_2529 (lift_to_both0 (usize 13)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_13_v)))) in
      letb yden_k_2529 : seq fp_t :=
        seq_upd yden_k_2529 (lift_to_both0 (usize 14)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_14_v)))) in
      letbm xnum_2530 : fp_t loc( xnum_2530_loc ) := nat_mod_zero  in
      letbm xx_2531 : fp_t loc( xx_2531_loc ) := nat_mod_one  in
      letb '(xnum_2530, xx_2531) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 xnum_k_2526)) prod_ce(xnum_2530, xx_2531) (L := (
              CEfset (
                [xnum_k_2526_loc ; xden_k_2527_loc ; ynum_k_2528_loc ; yden_k_2529_loc ; xnum_2530_loc ; xx_2531_loc ; xden_2532_loc ; xx_2533_loc ; ynum_2534_loc ; xx_2535_loc ; yden_2536_loc ; xx_2537_loc ; inf_2538_loc]))) (
            I := [interface]) (fun i_2552 '(xnum_2530, xx_2531) =>
            letbm xnum_2530 loc( xnum_2530_loc ) :=
              (lift_to_both0 xnum_2530) +% ((lift_to_both0 xx_2531) *% (
                  seq_index (xnum_k_2526) (lift_to_both0 i_2552))) in
            letbm xx_2531 loc( xx_2531_loc ) :=
              (lift_to_both0 xx_2531) *% (lift_to_both0 x_2553) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 xnum_2530,
                lift_to_both0 xx_2531
              ))
            ) in
      letbm xden_2532 : fp_t loc( xden_2532_loc ) := nat_mod_zero  in
      letbm xx_2533 : fp_t loc( xx_2533_loc ) := nat_mod_one  in
      letb '(xden_2532, xx_2533) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 xden_k_2527)) prod_ce(xden_2532, xx_2533) (L := (
              CEfset (
                [xnum_k_2526_loc ; xden_k_2527_loc ; ynum_k_2528_loc ; yden_k_2529_loc ; xnum_2530_loc ; xx_2531_loc ; xden_2532_loc ; xx_2533_loc ; ynum_2534_loc ; xx_2535_loc ; yden_2536_loc ; xx_2537_loc ; inf_2538_loc]))) (
            I := [interface]) (fun i_2554 '(xden_2532, xx_2533) =>
            letbm xden_2532 loc( xden_2532_loc ) :=
              (lift_to_both0 xden_2532) +% ((lift_to_both0 xx_2533) *% (
                  seq_index (xden_k_2527) (lift_to_both0 i_2554))) in
            letbm xx_2533 loc( xx_2533_loc ) :=
              (lift_to_both0 xx_2533) *% (lift_to_both0 x_2553) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 xden_2532,
                lift_to_both0 xx_2533
              ))
            ) in
      letbm xden_2532 loc( xden_2532_loc ) :=
        (lift_to_both0 xden_2532) +% (lift_to_both0 xx_2533) in
      letbm ynum_2534 : fp_t loc( ynum_2534_loc ) := nat_mod_zero  in
      letbm xx_2535 : fp_t loc( xx_2535_loc ) := nat_mod_one  in
      letb '(ynum_2534, xx_2535) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 ynum_k_2528)) prod_ce(ynum_2534, xx_2535) (L := (
              CEfset (
                [xnum_k_2526_loc ; xden_k_2527_loc ; ynum_k_2528_loc ; yden_k_2529_loc ; xnum_2530_loc ; xx_2531_loc ; xden_2532_loc ; xx_2533_loc ; ynum_2534_loc ; xx_2535_loc ; yden_2536_loc ; xx_2537_loc ; inf_2538_loc]))) (
            I := [interface]) (fun i_2555 '(ynum_2534, xx_2535) =>
            letbm ynum_2534 loc( ynum_2534_loc ) :=
              (lift_to_both0 ynum_2534) +% ((lift_to_both0 xx_2535) *% (
                  seq_index (ynum_k_2528) (lift_to_both0 i_2555))) in
            letbm xx_2535 loc( xx_2535_loc ) :=
              (lift_to_both0 xx_2535) *% (lift_to_both0 x_2553) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 ynum_2534,
                lift_to_both0 xx_2535
              ))
            ) in
      letbm yden_2536 : fp_t loc( yden_2536_loc ) := nat_mod_zero  in
      letbm xx_2537 : fp_t loc( xx_2537_loc ) := nat_mod_one  in
      letb '(yden_2536, xx_2537) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 yden_k_2529)) prod_ce(yden_2536, xx_2537) (L := (
              CEfset (
                [xnum_k_2526_loc ; xden_k_2527_loc ; ynum_k_2528_loc ; yden_k_2529_loc ; xnum_2530_loc ; xx_2531_loc ; xden_2532_loc ; xx_2533_loc ; ynum_2534_loc ; xx_2535_loc ; yden_2536_loc ; xx_2537_loc ; inf_2538_loc]))) (
            I := [interface]) (fun i_2556 '(yden_2536, xx_2537) =>
            letbm yden_2536 loc( yden_2536_loc ) :=
              (lift_to_both0 yden_2536) +% ((lift_to_both0 xx_2537) *% (
                  seq_index (yden_k_2529) (lift_to_both0 i_2556))) in
            letbm xx_2537 loc( xx_2537_loc ) :=
              (lift_to_both0 xx_2537) *% (lift_to_both0 x_2553) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 yden_2536,
                lift_to_both0 xx_2537
              ))
            ) in
      letbm yden_2536 loc( yden_2536_loc ) :=
        (lift_to_both0 yden_2536) +% (lift_to_both0 xx_2537) in
      letb xr_2557 : fp_t :=
        (lift_to_both0 xnum_2530) *% (nat_mod_inv (lift_to_both0 xden_2532)) in
      letb yr_2559 : fp_t :=
        ((lift_to_both0 y_2558) *% (lift_to_both0 ynum_2534)) *% (nat_mod_inv (
            lift_to_both0 yden_2536)) in
      letbm inf_2538 : bool_ChoiceEquality loc( inf_2538_loc ) :=
        lift_to_both0 ((false : bool_ChoiceEquality)) in
      letb '(inf_2538) :=
        if ((lift_to_both0 xden_2532) =.? (nat_mod_zero )) || ((
            lift_to_both0 yden_2536) =.? (nat_mod_zero )) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [xnum_k_2526_loc ; xden_k_2527_loc ; ynum_k_2528_loc ; yden_k_2529_loc ; xnum_2530_loc ; xx_2531_loc ; xden_2532_loc ; xx_2533_loc ; ynum_2534_loc ; xx_2535_loc ; yden_2536_loc ; xx_2537_loc ; inf_2538_loc])) (
          L2 := CEfset (
            [xnum_k_2526_loc ; xden_k_2527_loc ; ynum_k_2528_loc ; yden_k_2529_loc ; xnum_2530_loc ; xx_2531_loc ; xden_2532_loc ; xx_2533_loc ; ynum_2534_loc ; xx_2535_loc ; yden_2536_loc ; xx_2537_loc ; inf_2538_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm inf_2538 loc( inf_2538_loc ) :=
            lift_to_both0 ((true : bool_ChoiceEquality)) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 inf_2538)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 inf_2538)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 xr_2557,
          lift_to_both0 yr_2559,
          lift_to_both0 inf_2538
        ))
      ) : both (CEfset (
        [xnum_k_2526_loc ; xden_k_2527_loc ; ynum_k_2528_loc ; yden_k_2529_loc ; xnum_2530_loc ; xx_2531_loc ; xden_2532_loc ; xx_2533_loc ; ynum_2534_loc ; xx_2535_loc ; yden_2536_loc ; xx_2537_loc ; inf_2538_loc])) [interface] (
      g1_t)).
Fail Next Obligation.


Notation "'g1_map_to_curve_sswu_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_map_to_curve_sswu_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'g1_map_to_curve_sswu_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_map_to_curve_sswu_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1_MAP_TO_CURVE_SSWU : nat :=
  2565.
Program Definition g1_map_to_curve_sswu (u_2561 : fp_t)
  : both (CEfset (
      [x1_2512_loc ; y_2513_loc ; xnum_k_2526_loc ; xden_k_2527_loc ; ynum_k_2528_loc ; yden_k_2529_loc ; xnum_2530_loc ; xx_2531_loc ; xden_2532_loc ; xx_2533_loc ; ynum_2534_loc ; xx_2535_loc ; yden_2536_loc ; xx_2537_loc ; inf_2538_loc])) [interface] (
    g1_t) :=
  ((letb '(xp_2562, yp_2563) : (fp_t '× fp_t) :=
        g1_simple_swu_iso (lift_to_both0 u_2561) in
      letb p_2564 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_isogeny_map (lift_to_both0 xp_2562) (lift_to_both0 yp_2563) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2564)
      ) : both (CEfset (
        [x1_2512_loc ; y_2513_loc ; xnum_k_2526_loc ; xden_k_2527_loc ; ynum_k_2528_loc ; yden_k_2529_loc ; xnum_2530_loc ; xx_2531_loc ; xden_2532_loc ; xx_2533_loc ; ynum_2534_loc ; xx_2535_loc ; yden_2536_loc ; xx_2537_loc ; inf_2538_loc])) [interface] (
      g1_t)).
Fail Next Obligation.


Notation "'g1_hash_to_curve_sswu_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g1_hash_to_curve_sswu_inp'" :=(
  byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'g1_hash_to_curve_sswu_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_hash_to_curve_sswu_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1_HASH_TO_CURVE_SSWU : nat :=
  2573.
Program Definition g1_hash_to_curve_sswu (msg_2566 : byte_seq) (
    dst_2567 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2331_loc ; b_i_2332_loc ; uniform_bytes_2333_loc ; output_2348_loc ; x1_2512_loc ; y_2513_loc ; xnum_k_2526_loc ; xden_k_2527_loc ; ynum_k_2528_loc ; yden_k_2529_loc ; xnum_2530_loc ; xx_2531_loc ; xden_2532_loc ; xx_2533_loc ; ynum_2534_loc ; xx_2535_loc ; yden_2536_loc ; xx_2537_loc ; inf_2538_loc])) [interface] (
    g1_t) :=
  ((letb u_2568 : seq fp_t :=
        fp_hash_to_field (lift_to_both0 msg_2566) (lift_to_both0 dst_2567) (
          lift_to_both0 (usize 2)) in
      letb q0_2569 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_map_to_curve_sswu (seq_index (u_2568) (lift_to_both0 (usize 0))) in
      letb q1_2570 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_map_to_curve_sswu (seq_index (u_2568) (lift_to_both0 (usize 1))) in
      letb r_2571 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1add (lift_to_both0 q0_2569) (lift_to_both0 q1_2570) in
      letb p_2572 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_clear_cofactor (lift_to_both0 r_2571) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2572)
      ) : both (CEfset (
        [l_i_b_str_2331_loc ; b_i_2332_loc ; uniform_bytes_2333_loc ; output_2348_loc ; x1_2512_loc ; y_2513_loc ; xnum_k_2526_loc ; xden_k_2527_loc ; ynum_k_2528_loc ; yden_k_2529_loc ; xnum_2530_loc ; xx_2531_loc ; xden_2532_loc ; xx_2533_loc ; ynum_2534_loc ; xx_2535_loc ; yden_2536_loc ; xx_2537_loc ; inf_2538_loc])) [interface] (
      g1_t)).
Fail Next Obligation.


Notation "'g1_encode_to_curve_sswu_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g1_encode_to_curve_sswu_inp'" :=(
  byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'g1_encode_to_curve_sswu_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_encode_to_curve_sswu_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1_ENCODE_TO_CURVE_SSWU : nat :=
  2579.
Program Definition g1_encode_to_curve_sswu (msg_2574 : byte_seq) (
    dst_2575 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2331_loc ; b_i_2332_loc ; uniform_bytes_2333_loc ; output_2348_loc ; x1_2512_loc ; y_2513_loc ; xnum_k_2526_loc ; xden_k_2527_loc ; ynum_k_2528_loc ; yden_k_2529_loc ; xnum_2530_loc ; xx_2531_loc ; xden_2532_loc ; xx_2533_loc ; ynum_2534_loc ; xx_2535_loc ; yden_2536_loc ; xx_2537_loc ; inf_2538_loc])) [interface] (
    g1_t) :=
  ((letb u_2576 : seq fp_t :=
        fp_hash_to_field (lift_to_both0 msg_2574) (lift_to_both0 dst_2575) (
          lift_to_both0 (usize 1)) in
      letb q_2577 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_map_to_curve_sswu (seq_index (u_2576) (lift_to_both0 (usize 0))) in
      letb p_2578 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_clear_cofactor (lift_to_both0 q_2577) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2578)
      ) : both (CEfset (
        [l_i_b_str_2331_loc ; b_i_2332_loc ; uniform_bytes_2333_loc ; output_2348_loc ; x1_2512_loc ; y_2513_loc ; xnum_k_2526_loc ; xden_k_2527_loc ; ynum_k_2528_loc ; yden_k_2529_loc ; xnum_2530_loc ; xx_2531_loc ; xden_2532_loc ; xx_2533_loc ; ynum_2534_loc ; xx_2535_loc ; yden_2536_loc ; xx_2537_loc ; inf_2538_loc])) [interface] (
      g1_t)).
Fail Next Obligation.

Definition g2_xnum_k_0_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 416399692810564414)) : uint64;
    (secret (@repr U64 13500519111022079365)) : uint64;
    (secret (@repr U64 3658379999393219626)) : uint64;
    (secret (@repr U64 9850925049107374429)) : uint64;
    (secret (@repr U64 6640057249351452444)) : uint64;
    (secret (@repr U64 7077594464397203414)) : uint64
  ].

Definition g2_xnum_k_1_i_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1249199078431693244)) : uint64;
    (secret (@repr U64 3608069185647134863)) : uint64;
    (secret (@repr U64 10975139998179658879)) : uint64;
    (secret (@repr U64 11106031073612571672)) : uint64;
    (secret (@repr U64 1473427674344805717)) : uint64;
    (secret (@repr U64 2786039319482058522)) : uint64
  ].

Definition g2_xnum_k_2_r_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1249199078431693244)) : uint64;
    (secret (@repr U64 3608069185647134863)) : uint64;
    (secret (@repr U64 10975139998179658879)) : uint64;
    (secret (@repr U64 11106031073612571672)) : uint64;
    (secret (@repr U64 1473427674344805717)) : uint64;
    (secret (@repr U64 2786039319482058526)) : uint64
  ].

Definition g2_xnum_k_2_i_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 624599539215846622)) : uint64;
    (secret (@repr U64 1804034592823567431)) : uint64;
    (secret (@repr U64 14710942035944605247)) : uint64;
    (secret (@repr U64 14776387573661061644)) : uint64;
    (secret (@repr U64 736713837172402858)) : uint64;
    (secret (@repr U64 10616391696595805069)) : uint64
  ].

Definition g2_xnum_k_3_r_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1665598771242257658)) : uint64;
    (secret (@repr U64 17108588296669214228)) : uint64;
    (secret (@repr U64 14633519997572878506)) : uint64;
    (secret (@repr U64 2510212049010394485)) : uint64;
    (secret (@repr U64 8113484923696258161)) : uint64;
    (secret (@repr U64 9863633783879261905)) : uint64
  ].

Definition g2_xden_k_0_i_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1873798617647539866)) : uint64;
    (secret (@repr U64 5412103778470702295)) : uint64;
    (secret (@repr U64 7239337960414712511)) : uint64;
    (secret (@repr U64 7435674573564081700)) : uint64;
    (secret (@repr U64 2210141511517208575)) : uint64;
    (secret (@repr U64 13402431016077863523)) : uint64
  ].

Definition g2_xden_k_1_i_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1873798617647539866)) : uint64;
    (secret (@repr U64 5412103778470702295)) : uint64;
    (secret (@repr U64 7239337960414712511)) : uint64;
    (secret (@repr U64 7435674573564081700)) : uint64;
    (secret (@repr U64 2210141511517208575)) : uint64;
    (secret (@repr U64 13402431016077863583)) : uint64
  ].

Definition g2_ynum_k_0_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1526798873638736187)) : uint64;
    (secret (@repr U64 6459500568425337235)) : uint64;
    (secret (@repr U64 1116230615302104219)) : uint64;
    (secret (@repr U64 17673314439684154624)) : uint64;
    (secret (@repr U64 18197961889718808424)) : uint64;
    (secret (@repr U64 1355520937843676934)) : uint64
  ].

Definition g2_ynum_k_1_i_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 416399692810564414)) : uint64;
    (secret (@repr U64 13500519111022079365)) : uint64;
    (secret (@repr U64 3658379999393219626)) : uint64;
    (secret (@repr U64 9850925049107374429)) : uint64;
    (secret (@repr U64 6640057249351452444)) : uint64;
    (secret (@repr U64 7077594464397203390)) : uint64
  ].

Definition g2_ynum_k_2_r_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1249199078431693244)) : uint64;
    (secret (@repr U64 3608069185647134863)) : uint64;
    (secret (@repr U64 10975139998179658879)) : uint64;
    (secret (@repr U64 11106031073612571672)) : uint64;
    (secret (@repr U64 1473427674344805717)) : uint64;
    (secret (@repr U64 2786039319482058524)) : uint64
  ].

Definition g2_ynum_k_2_i_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 624599539215846622)) : uint64;
    (secret (@repr U64 1804034592823567431)) : uint64;
    (secret (@repr U64 14710942035944605247)) : uint64;
    (secret (@repr U64 14776387573661061644)) : uint64;
    (secret (@repr U64 736713837172402858)) : uint64;
    (secret (@repr U64 10616391696595805071)) : uint64
  ].

Definition g2_ynum_k_3_r_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1318599027233453979)) : uint64;
    (secret (@repr U64 18155985086623849168)) : uint64;
    (secret (@repr U64 8510412652460270214)) : uint64;
    (secret (@repr U64 12747851915130467410)) : uint64;
    (secret (@repr U64 5654561228188306393)) : uint64;
    (secret (@repr U64 16263467779354626832)) : uint64
  ].

Definition g2_yden_k_0_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1873798617647539866)) : uint64;
    (secret (@repr U64 5412103778470702295)) : uint64;
    (secret (@repr U64 7239337960414712511)) : uint64;
    (secret (@repr U64 7435674573564081700)) : uint64;
    (secret (@repr U64 2210141511517208575)) : uint64;
    (secret (@repr U64 13402431016077863163)) : uint64
  ].

Definition g2_yden_k_1_i_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1873798617647539866)) : uint64;
    (secret (@repr U64 5412103778470702295)) : uint64;
    (secret (@repr U64 7239337960414712511)) : uint64;
    (secret (@repr U64 7435674573564081700)) : uint64;
    (secret (@repr U64 2210141511517208575)) : uint64;
    (secret (@repr U64 13402431016077863379)) : uint64
  ].

Definition g2_yden_k_2_i_v : arr_fp_t :=
  @array_from_list uint64 [
    (secret (@repr U64 1873798617647539866)) : uint64;
    (secret (@repr U64 5412103778470702295)) : uint64;
    (secret (@repr U64 7239337960414712511)) : uint64;
    (secret (@repr U64 7435674573564081700)) : uint64;
    (secret (@repr U64 2210141511517208575)) : uint64;
    (secret (@repr U64 13402431016077863577)) : uint64
  ].

Definition x1_2580_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2582%nat).
Definition y_2581_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2583%nat).
Notation "'g2_simple_swu_iso_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_simple_swu_iso_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'g2_simple_swu_iso_out'" :=((fp2_t '× fp2_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'g2_simple_swu_iso_out'" :=((fp2_t '× fp2_t
  ) : ChoiceEquality) (at level 2).
Definition G2_SIMPLE_SWU_ISO : nat :=
  2593.
Program Definition g2_simple_swu_iso (u_2587 : fp2_t)
  : both (CEfset ([c_2438_loc ; x1_2580_loc ; y_2581_loc])) [interface] ((
      fp2_t '×
      fp2_t
    )) :=
  ((letb z_2584 : (fp_t '× fp_t) :=
        fp2neg (prod_b(nat_mod_two , nat_mod_one )) in
      letb a_2585 : (fp_t '× fp_t) :=
        prod_b(
          nat_mod_zero ,
          nat_mod_from_literal (_) (lift_to_both0 (@repr U128 240))
        ) in
      letb b_2586 : (fp_t '× fp_t) :=
        prod_b(
          nat_mod_from_literal (_) (lift_to_both0 (@repr U128 1012)),
          nat_mod_from_literal (_) (lift_to_both0 (@repr U128 1012))
        ) in
      letb tv1_2588 : (fp_t '× fp_t) :=
        fp2inv (fp2add (fp2mul (fp2mul (lift_to_both0 z_2584) (
                lift_to_both0 z_2584)) (fp2mul (fp2mul (lift_to_both0 u_2587) (
                  lift_to_both0 u_2587)) (fp2mul (lift_to_both0 u_2587) (
                  lift_to_both0 u_2587)))) (fp2mul (lift_to_both0 z_2584) (
              fp2mul (lift_to_both0 u_2587) (lift_to_both0 u_2587)))) in
      letbm x1_2580 : (fp_t '× fp_t) loc( x1_2580_loc ) :=
        fp2mul (fp2mul (fp2neg (lift_to_both0 b_2586)) (fp2inv (
              lift_to_both0 a_2585))) (fp2add (fp2fromfp (nat_mod_one )) (
            lift_to_both0 tv1_2588)) in
      letb '(x1_2580) :=
        if (lift_to_both0 tv1_2588) =.? (fp2zero ) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([x1_2580_loc])) (L2 := CEfset (
            [c_2438_loc ; x1_2580_loc ; y_2581_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x1_2580 loc( x1_2580_loc ) :=
            fp2mul (lift_to_both0 b_2586) (fp2inv (fp2mul (
                  lift_to_both0 z_2584) (lift_to_both0 a_2585))) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 x1_2580)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 x1_2580)
         in
      letb gx1_2589 : (fp_t '× fp_t) :=
        fp2add (fp2add (fp2mul (fp2mul (lift_to_both0 x1_2580) (
                lift_to_both0 x1_2580)) (lift_to_both0 x1_2580)) (fp2mul (
              lift_to_both0 a_2585) (lift_to_both0 x1_2580))) (
          lift_to_both0 b_2586) in
      letb x2_2590 : (fp_t '× fp_t) :=
        fp2mul (fp2mul (lift_to_both0 z_2584) (fp2mul (lift_to_both0 u_2587) (
              lift_to_both0 u_2587))) (lift_to_both0 x1_2580) in
      letb gx2_2591 : (fp_t '× fp_t) :=
        fp2add (fp2add (fp2mul (fp2mul (lift_to_both0 x2_2590) (
                lift_to_both0 x2_2590)) (lift_to_both0 x2_2590)) (fp2mul (
              lift_to_both0 a_2585) (lift_to_both0 x2_2590))) (
          lift_to_both0 b_2586) in
      letb '(x_2592, y_2581) : ((fp_t '× fp_t) '× fp2_t) :=
        if is_pure (I := [interface]) (fp2_is_square (lift_to_both0 gx1_2589))
        then prod_b(lift_to_both0 x1_2580, fp2_sqrt (lift_to_both0 gx1_2589))
        else prod_b(lift_to_both0 x2_2590, fp2_sqrt (lift_to_both0 gx2_2591)) in
      letb '(y_2581) :=
        if (fp2_sgn0 (lift_to_both0 u_2587)) !=.? (fp2_sgn0 (
            lift_to_both0 y_2581)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [c_2438_loc ; x1_2580_loc ; y_2581_loc])) (L2 := CEfset (
            [c_2438_loc ; x1_2580_loc ; y_2581_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm y_2581 loc( y_2581_loc ) := fp2neg (lift_to_both0 y_2581) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 y_2581)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 y_2581)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_2592,
          lift_to_both0 y_2581
        ))
      ) : both (CEfset ([c_2438_loc ; x1_2580_loc ; y_2581_loc])) [interface] ((
        fp2_t '×
        fp2_t
      ))).
Fail Next Obligation.

Definition xx_2601_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2607%nat).
Definition xden_2600_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2608%nat).
Definition inf_2606_loc : ChoiceEqualityLocation :=
  (bool_ChoiceEquality ; 2609%nat).
Definition xnum_2598_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2610%nat).
Definition xden_k_2595_loc : ChoiceEqualityLocation :=
  (seq (fp_t '× fp_t) ; 2611%nat).
Definition xx_2599_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2612%nat).
Definition xx_2605_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2613%nat).
Definition yden_k_2597_loc : ChoiceEqualityLocation :=
  (seq (fp_t '× fp_t) ; 2614%nat).
Definition yden_2604_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2615%nat).
Definition xnum_k_2594_loc : ChoiceEqualityLocation :=
  (seq (fp_t '× fp_t) ; 2616%nat).
Definition ynum_k_2596_loc : ChoiceEqualityLocation :=
  (seq (fp_t '× fp_t) ; 2617%nat).
Definition ynum_2602_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2618%nat).
Definition xx_2603_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2619%nat).
Notation "'g2_isogeny_map_inp'" :=(
  fp2_t '× fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_isogeny_map_inp'" :=(
  fp2_t '× fp2_t : ChoiceEquality) (at level 2).
Notation "'g2_isogeny_map_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_isogeny_map_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_ISOGENY_MAP : nat :=
  2628.
Program Definition g2_isogeny_map (x_2621 : fp2_t) (y_2626 : fp2_t)
  : both (CEfset (
      [xnum_k_2594_loc ; xden_k_2595_loc ; ynum_k_2596_loc ; yden_k_2597_loc ; xnum_2598_loc ; xx_2599_loc ; xden_2600_loc ; xx_2601_loc ; ynum_2602_loc ; xx_2603_loc ; yden_2604_loc ; xx_2605_loc ; inf_2606_loc])) [interface] (
    g2_t) :=
  ((letbm xnum_k_2594 : seq (fp_t '× fp_t) loc( xnum_k_2594_loc ) :=
        seq_new_ (default : fp2_t) (lift_to_both0 (usize 4)) in
      letb xnum_k_2594 : seq (fp_t '× fp_t) :=
        seq_upd xnum_k_2594 (lift_to_both0 (usize 0)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xnum_k_0_v)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xnum_k_0_v))
            ))) in
      letb xnum_k_2594 : seq (fp_t '× fp_t) :=
        seq_upd xnum_k_2594 (lift_to_both0 (usize 1)) (is_pure (prod_b(
              nat_mod_zero ,
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xnum_k_1_i_v))
            ))) in
      letb xnum_k_2594 : seq (fp_t '× fp_t) :=
        seq_upd xnum_k_2594 (lift_to_both0 (usize 2)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xnum_k_2_r_v)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xnum_k_2_i_v))
            ))) in
      letb xnum_k_2594 : seq (fp_t '× fp_t) :=
        seq_upd xnum_k_2594 (lift_to_both0 (usize 3)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xnum_k_3_r_v)),
              nat_mod_zero 
            ))) in
      letbm xden_k_2595 : seq (fp_t '× fp_t) loc( xden_k_2595_loc ) :=
        seq_new_ (default : fp2_t) (lift_to_both0 (usize 2)) in
      letb xden_k_2595 : seq (fp_t '× fp_t) :=
        seq_upd xden_k_2595 (lift_to_both0 (usize 0)) (is_pure (prod_b(
              nat_mod_zero ,
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xden_k_0_i_v))
            ))) in
      letb xden_k_2595 : seq (fp_t '× fp_t) :=
        seq_upd xden_k_2595 (lift_to_both0 (usize 1)) (is_pure (prod_b(
              nat_mod_from_literal (_) (lift_to_both0 (@repr U128 12)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xden_k_1_i_v))
            ))) in
      letbm ynum_k_2596 : seq (fp_t '× fp_t) loc( ynum_k_2596_loc ) :=
        seq_new_ (default : fp2_t) (lift_to_both0 (usize 4)) in
      letb ynum_k_2596 : seq (fp_t '× fp_t) :=
        seq_upd ynum_k_2596 (lift_to_both0 (usize 0)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_ynum_k_0_v)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_ynum_k_0_v))
            ))) in
      letb ynum_k_2596 : seq (fp_t '× fp_t) :=
        seq_upd ynum_k_2596 (lift_to_both0 (usize 1)) (is_pure (prod_b(
              nat_mod_zero ,
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_ynum_k_1_i_v))
            ))) in
      letb ynum_k_2596 : seq (fp_t '× fp_t) :=
        seq_upd ynum_k_2596 (lift_to_both0 (usize 2)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_ynum_k_2_r_v)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_ynum_k_2_i_v))
            ))) in
      letb ynum_k_2596 : seq (fp_t '× fp_t) :=
        seq_upd ynum_k_2596 (lift_to_both0 (usize 3)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_ynum_k_3_r_v)),
              nat_mod_zero 
            ))) in
      letbm yden_k_2597 : seq (fp_t '× fp_t) loc( yden_k_2597_loc ) :=
        seq_new_ (default : fp2_t) (lift_to_both0 (usize 3)) in
      letb yden_k_2597 : seq (fp_t '× fp_t) :=
        seq_upd yden_k_2597 (lift_to_both0 (usize 0)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_yden_k_0_v)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_yden_k_0_v))
            ))) in
      letb yden_k_2597 : seq (fp_t '× fp_t) :=
        seq_upd yden_k_2597 (lift_to_both0 (usize 1)) (is_pure (prod_b(
              nat_mod_zero ,
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_yden_k_1_i_v))
            ))) in
      letb yden_k_2597 : seq (fp_t '× fp_t) :=
        seq_upd yden_k_2597 (lift_to_both0 (usize 2)) (is_pure (prod_b(
              nat_mod_from_literal (_) (lift_to_both0 (@repr U128 18)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_yden_k_2_i_v))
            ))) in
      letbm xnum_2598 : (fp_t '× fp_t) loc( xnum_2598_loc ) := fp2zero  in
      letbm xx_2599 : (fp_t '× fp_t) loc( xx_2599_loc ) :=
        fp2fromfp (nat_mod_one ) in
      letb '(xnum_2598, xx_2599) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 xnum_k_2594)) prod_ce(xnum_2598, xx_2599) (L := (
              CEfset (
                [xnum_k_2594_loc ; xden_k_2595_loc ; ynum_k_2596_loc ; yden_k_2597_loc ; xnum_2598_loc ; xx_2599_loc ; xden_2600_loc ; xx_2601_loc ; ynum_2602_loc ; xx_2603_loc ; yden_2604_loc ; xx_2605_loc ; inf_2606_loc]))) (
            I := [interface]) (fun i_2620 '(xnum_2598, xx_2599) =>
            letbm xnum_2598 loc( xnum_2598_loc ) :=
              fp2add (lift_to_both0 xnum_2598) (fp2mul (lift_to_both0 xx_2599) (
                  seq_index (xnum_k_2594) (lift_to_both0 i_2620))) in
            letbm xx_2599 loc( xx_2599_loc ) :=
              fp2mul (lift_to_both0 xx_2599) (lift_to_both0 x_2621) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 xnum_2598,
                lift_to_both0 xx_2599
              ))
            ) in
      letbm xden_2600 : (fp_t '× fp_t) loc( xden_2600_loc ) := fp2zero  in
      letbm xx_2601 : (fp_t '× fp_t) loc( xx_2601_loc ) :=
        fp2fromfp (nat_mod_one ) in
      letb '(xden_2600, xx_2601) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 xden_k_2595)) prod_ce(xden_2600, xx_2601) (L := (
              CEfset (
                [xnum_k_2594_loc ; xden_k_2595_loc ; ynum_k_2596_loc ; yden_k_2597_loc ; xnum_2598_loc ; xx_2599_loc ; xden_2600_loc ; xx_2601_loc ; ynum_2602_loc ; xx_2603_loc ; yden_2604_loc ; xx_2605_loc ; inf_2606_loc]))) (
            I := [interface]) (fun i_2622 '(xden_2600, xx_2601) =>
            letbm xden_2600 loc( xden_2600_loc ) :=
              fp2add (lift_to_both0 xden_2600) (fp2mul (lift_to_both0 xx_2601) (
                  seq_index (xden_k_2595) (lift_to_both0 i_2622))) in
            letbm xx_2601 loc( xx_2601_loc ) :=
              fp2mul (lift_to_both0 xx_2601) (lift_to_both0 x_2621) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 xden_2600,
                lift_to_both0 xx_2601
              ))
            ) in
      letbm xden_2600 loc( xden_2600_loc ) :=
        fp2add (lift_to_both0 xden_2600) (lift_to_both0 xx_2601) in
      letbm ynum_2602 : (fp_t '× fp_t) loc( ynum_2602_loc ) := fp2zero  in
      letbm xx_2603 : (fp_t '× fp_t) loc( xx_2603_loc ) :=
        fp2fromfp (nat_mod_one ) in
      letb '(ynum_2602, xx_2603) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 ynum_k_2596)) prod_ce(ynum_2602, xx_2603) (L := (
              CEfset (
                [xnum_k_2594_loc ; xden_k_2595_loc ; ynum_k_2596_loc ; yden_k_2597_loc ; xnum_2598_loc ; xx_2599_loc ; xden_2600_loc ; xx_2601_loc ; ynum_2602_loc ; xx_2603_loc ; yden_2604_loc ; xx_2605_loc ; inf_2606_loc]))) (
            I := [interface]) (fun i_2623 '(ynum_2602, xx_2603) =>
            letbm ynum_2602 loc( ynum_2602_loc ) :=
              fp2add (lift_to_both0 ynum_2602) (fp2mul (lift_to_both0 xx_2603) (
                  seq_index (ynum_k_2596) (lift_to_both0 i_2623))) in
            letbm xx_2603 loc( xx_2603_loc ) :=
              fp2mul (lift_to_both0 xx_2603) (lift_to_both0 x_2621) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 ynum_2602,
                lift_to_both0 xx_2603
              ))
            ) in
      letbm yden_2604 : (fp_t '× fp_t) loc( yden_2604_loc ) := fp2zero  in
      letbm xx_2605 : (fp_t '× fp_t) loc( xx_2605_loc ) :=
        fp2fromfp (nat_mod_one ) in
      letb '(yden_2604, xx_2605) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 yden_k_2597)) prod_ce(yden_2604, xx_2605) (L := (
              CEfset (
                [xnum_k_2594_loc ; xden_k_2595_loc ; ynum_k_2596_loc ; yden_k_2597_loc ; xnum_2598_loc ; xx_2599_loc ; xden_2600_loc ; xx_2601_loc ; ynum_2602_loc ; xx_2603_loc ; yden_2604_loc ; xx_2605_loc ; inf_2606_loc]))) (
            I := [interface]) (fun i_2624 '(yden_2604, xx_2605) =>
            letbm yden_2604 loc( yden_2604_loc ) :=
              fp2add (lift_to_both0 yden_2604) (fp2mul (lift_to_both0 xx_2605) (
                  seq_index (yden_k_2597) (lift_to_both0 i_2624))) in
            letbm xx_2605 loc( xx_2605_loc ) :=
              fp2mul (lift_to_both0 xx_2605) (lift_to_both0 x_2621) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 yden_2604,
                lift_to_both0 xx_2605
              ))
            ) in
      letbm yden_2604 loc( yden_2604_loc ) :=
        fp2add (lift_to_both0 yden_2604) (lift_to_both0 xx_2605) in
      letb xr_2625 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 xnum_2598) (fp2inv (lift_to_both0 xden_2600)) in
      letb yr_2627 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 y_2626) (fp2mul (lift_to_both0 ynum_2602) (
            fp2inv (lift_to_both0 yden_2604))) in
      letbm inf_2606 : bool_ChoiceEquality loc( inf_2606_loc ) :=
        lift_to_both0 ((false : bool_ChoiceEquality)) in
      letb '(inf_2606) :=
        if ((lift_to_both0 xden_2600) =.? (fp2zero )) || ((
            lift_to_both0 yden_2604) =.? (fp2zero )) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [xnum_k_2594_loc ; xden_k_2595_loc ; ynum_k_2596_loc ; yden_k_2597_loc ; xnum_2598_loc ; xx_2599_loc ; xden_2600_loc ; xx_2601_loc ; ynum_2602_loc ; xx_2603_loc ; yden_2604_loc ; xx_2605_loc ; inf_2606_loc])) (
          L2 := CEfset (
            [xnum_k_2594_loc ; xden_k_2595_loc ; ynum_k_2596_loc ; yden_k_2597_loc ; xnum_2598_loc ; xx_2599_loc ; xden_2600_loc ; xx_2601_loc ; ynum_2602_loc ; xx_2603_loc ; yden_2604_loc ; xx_2605_loc ; inf_2606_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm inf_2606 loc( inf_2606_loc ) :=
            lift_to_both0 ((true : bool_ChoiceEquality)) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 inf_2606)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 inf_2606)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 xr_2625,
          lift_to_both0 yr_2627,
          lift_to_both0 inf_2606
        ))
      ) : both (CEfset (
        [xnum_k_2594_loc ; xden_k_2595_loc ; ynum_k_2596_loc ; yden_k_2597_loc ; xnum_2598_loc ; xx_2599_loc ; xden_2600_loc ; xx_2601_loc ; ynum_2602_loc ; xx_2603_loc ; yden_2604_loc ; xx_2605_loc ; inf_2606_loc])) [interface] (
      g2_t)).
Fail Next Obligation.


Notation "'g2_map_to_curve_sswu_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_map_to_curve_sswu_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'g2_map_to_curve_sswu_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_map_to_curve_sswu_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_MAP_TO_CURVE_SSWU : nat :=
  2633.
Program Definition g2_map_to_curve_sswu (u_2629 : fp2_t)
  : both (CEfset (
      [c_2438_loc ; x1_2580_loc ; y_2581_loc ; xnum_k_2594_loc ; xden_k_2595_loc ; ynum_k_2596_loc ; yden_k_2597_loc ; xnum_2598_loc ; xx_2599_loc ; xden_2600_loc ; xx_2601_loc ; ynum_2602_loc ; xx_2603_loc ; yden_2604_loc ; xx_2605_loc ; inf_2606_loc])) [interface] (
    g2_t) :=
  ((letb '(xp_2630, yp_2631) : (fp2_t '× fp2_t) :=
        g2_simple_swu_iso (lift_to_both0 u_2629) in
      letb p_2632 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_isogeny_map (lift_to_both0 xp_2630) (lift_to_both0 yp_2631) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2632)
      ) : both (CEfset (
        [c_2438_loc ; x1_2580_loc ; y_2581_loc ; xnum_k_2594_loc ; xden_k_2595_loc ; ynum_k_2596_loc ; yden_k_2597_loc ; xnum_2598_loc ; xx_2599_loc ; xden_2600_loc ; xx_2601_loc ; ynum_2602_loc ; xx_2603_loc ; yden_2604_loc ; xx_2605_loc ; inf_2606_loc])) [interface] (
      g2_t)).
Fail Next Obligation.


Notation "'g2_hash_to_curve_sswu_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g2_hash_to_curve_sswu_inp'" :=(
  byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'g2_hash_to_curve_sswu_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_hash_to_curve_sswu_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_HASH_TO_CURVE_SSWU : nat :=
  2641.
Program Definition g2_hash_to_curve_sswu (msg_2634 : byte_seq) (
    dst_2635 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2331_loc ; b_i_2332_loc ; uniform_bytes_2333_loc ; output_2406_loc ; c_2438_loc ; x1_2580_loc ; y_2581_loc ; xnum_k_2594_loc ; xden_k_2595_loc ; ynum_k_2596_loc ; yden_k_2597_loc ; xnum_2598_loc ; xx_2599_loc ; xden_2600_loc ; xx_2601_loc ; ynum_2602_loc ; xx_2603_loc ; yden_2604_loc ; xx_2605_loc ; inf_2606_loc])) [interface] (
    g2_t) :=
  ((letb u_2636 : seq fp2_t :=
        fp2_hash_to_field (lift_to_both0 msg_2634) (lift_to_both0 dst_2635) (
          lift_to_both0 (usize 2)) in
      letb q0_2637 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2_map_to_curve_sswu (seq_index (u_2636) (lift_to_both0 (usize 0))) in
      letb q1_2638 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2_map_to_curve_sswu (seq_index (u_2636) (lift_to_both0 (usize 1))) in
      letb r_2639 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 q0_2637) (lift_to_both0 q1_2638) in
      letb p_2640 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_clear_cofactor (lift_to_both0 r_2639) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2640)
      ) : both (CEfset (
        [l_i_b_str_2331_loc ; b_i_2332_loc ; uniform_bytes_2333_loc ; output_2406_loc ; c_2438_loc ; x1_2580_loc ; y_2581_loc ; xnum_k_2594_loc ; xden_k_2595_loc ; ynum_k_2596_loc ; yden_k_2597_loc ; xnum_2598_loc ; xx_2599_loc ; xden_2600_loc ; xx_2601_loc ; ynum_2602_loc ; xx_2603_loc ; yden_2604_loc ; xx_2605_loc ; inf_2606_loc])) [interface] (
      g2_t)).
Fail Next Obligation.


Notation "'g2_encode_to_curve_sswu_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g2_encode_to_curve_sswu_inp'" :=(
  byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'g2_encode_to_curve_sswu_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_encode_to_curve_sswu_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_ENCODE_TO_CURVE_SSWU : nat :=
  2647.
Program Definition g2_encode_to_curve_sswu (msg_2642 : byte_seq) (
    dst_2643 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2331_loc ; b_i_2332_loc ; uniform_bytes_2333_loc ; output_2406_loc ; c_2438_loc ; x1_2580_loc ; y_2581_loc ; xnum_k_2594_loc ; xden_k_2595_loc ; ynum_k_2596_loc ; yden_k_2597_loc ; xnum_2598_loc ; xx_2599_loc ; xden_2600_loc ; xx_2601_loc ; ynum_2602_loc ; xx_2603_loc ; yden_2604_loc ; xx_2605_loc ; inf_2606_loc])) [interface] (
    g2_t) :=
  ((letb u_2644 : seq fp2_t :=
        fp2_hash_to_field (lift_to_both0 msg_2642) (lift_to_both0 dst_2643) (
          lift_to_both0 (usize 1)) in
      letb q_2645 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_map_to_curve_sswu (seq_index (u_2644) (lift_to_both0 (usize 0))) in
      letb p_2646 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_clear_cofactor (lift_to_both0 q_2645) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2646)
      ) : both (CEfset (
        [l_i_b_str_2331_loc ; b_i_2332_loc ; uniform_bytes_2333_loc ; output_2406_loc ; c_2438_loc ; x1_2580_loc ; y_2581_loc ; xnum_k_2594_loc ; xden_k_2595_loc ; ynum_k_2596_loc ; yden_k_2597_loc ; xnum_2598_loc ; xx_2599_loc ; xden_2600_loc ; xx_2601_loc ; ynum_2602_loc ; xx_2603_loc ; yden_2604_loc ; xx_2605_loc ; inf_2606_loc])) [interface] (
      g2_t)).
Fail Next Obligation.

