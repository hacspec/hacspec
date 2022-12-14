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
  array_from_list uint64 [
    (secret (@repr U64 936899308823769933)) : uint64;
    (secret (@repr U64 2706051889235351147)) : uint64;
    (secret (@repr U64 12843041017062132063)) : uint64;
    (secret (@repr U64 12941209323636816658)) : uint64;
    (secret (@repr U64 1105070755758604287)) : uint64;
    (secret (@repr U64 15924587544893707605)) : uint64
  ].

Definition p_1_4_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 468449654411884966)) : uint64;
    (secret (@repr U64 10576397981472451381)) : uint64;
    (secret (@repr U64 15644892545385841839)) : uint64;
    (secret (@repr U64 15693976698673184137)) : uint64;
    (secret (@repr U64 552535377879302143)) : uint64;
    (secret (@repr U64 17185665809301629611)) : uint64
  ].

Definition p_3_4_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 468449654411884966)) : uint64;
    (secret (@repr U64 10576397981472451381)) : uint64;
    (secret (@repr U64 15644892545385841839)) : uint64;
    (secret (@repr U64 15693976698673184137)) : uint64;
    (secret (@repr U64 552535377879302143)) : uint64;
    (secret (@repr U64 17185665809301629610)) : uint64
  ].

Definition uniform_bytes_2253_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2254%nat).
Definition l_i_b_str_2251_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2255%nat).
Definition b_i_2252_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2256%nat).
Notation "'expand_message_xmd_inp'" :=(
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'expand_message_xmd_inp'" :=(
  byte_seq '× byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'expand_message_xmd_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'expand_message_xmd_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition EXPAND_MESSAGE_XMD : nat :=
  2267.
Program Definition expand_message_xmd (msg_2262 : byte_seq) (
    dst_2259 : byte_seq) (len_in_bytes_2257 : uint_size)
  : both (CEfset (
      [l_i_b_str_2251_loc ; b_i_2252_loc ; uniform_bytes_2253_loc])) [interface] (
    byte_seq) :=
  ((letb ell_2258 : uint_size :=
        (((lift_to_both0 len_in_bytes_2257) .+ (
              lift_to_both0 b_in_bytes_v)) .- (lift_to_both0 (usize 1))) ./ (
          lift_to_both0 b_in_bytes_v) in
      letb dst_prime_2260 : seq uint8 :=
        seq_push (lift_to_both0 dst_2259) (uint8_from_usize (seq_len (
              lift_to_both0 dst_2259))) in
      letb z_pad_2261 : seq uint8 :=
        seq_new_ (default : uint8) (lift_to_both0 s_in_bytes_v) in
      letbm l_i_b_str_2251 : seq uint8 loc( l_i_b_str_2251_loc ) :=
        seq_new_ (default : uint8) (lift_to_both0 (usize 2)) in
      letb l_i_b_str_2251 : seq uint8 :=
        seq_upd l_i_b_str_2251 (lift_to_both0 (usize 0)) (is_pure (
            uint8_from_usize ((lift_to_both0 len_in_bytes_2257) ./ (
                lift_to_both0 (usize 256))))) in
      letb l_i_b_str_2251 : seq uint8 :=
        seq_upd l_i_b_str_2251 (lift_to_both0 (usize 1)) (is_pure (
            uint8_from_usize (lift_to_both0 len_in_bytes_2257))) in
      letb msg_prime_2263 : seq uint8 :=
        seq_concat (seq_concat (seq_concat (seq_concat (
                lift_to_both0 z_pad_2261) (lift_to_both0 msg_2262)) (
              lift_to_both0 l_i_b_str_2251)) (seq_new_ (default : uint8) (
              lift_to_both0 (usize 1)))) (lift_to_both0 dst_prime_2260) in
      letb b_0_2264 : seq uint8 :=
        seq_from_seq (array_to_seq (hash (lift_to_both0 msg_prime_2263))) in
      letbm b_i_2252 : seq uint8 loc( b_i_2252_loc ) :=
        seq_from_seq (array_to_seq (hash (seq_concat (seq_push (
                lift_to_both0 b_0_2264) (secret (lift_to_both0 (@repr U8 1)))) (
              lift_to_both0 dst_prime_2260)))) in
      letbm uniform_bytes_2253 : seq uint8 loc( uniform_bytes_2253_loc ) :=
        seq_from_seq (lift_to_both0 b_i_2252) in
      letb '(b_i_2252, uniform_bytes_2253) :=
        foldi_both' (lift_to_both0 (usize 2)) ((lift_to_both0 ell_2258) .+ (
              lift_to_both0 (usize 1))) prod_ce(b_i_2252, uniform_bytes_2253) (
            L := (CEfset (
                [l_i_b_str_2251_loc ; b_i_2252_loc ; uniform_bytes_2253_loc]))) (
            I := [interface]) (fun i_2265 '(b_i_2252, uniform_bytes_2253) =>
            letb t_2266 : seq uint8 := seq_from_seq (lift_to_both0 b_0_2264) in
            letbm b_i_2252 loc( b_i_2252_loc ) :=
              seq_from_seq (array_to_seq (hash (seq_concat (seq_push ((
                        lift_to_both0 t_2266) seq_xor (
                        lift_to_both0 b_i_2252)) (uint8_from_usize (
                        lift_to_both0 i_2265))) (
                    lift_to_both0 dst_prime_2260)))) in
            letbm uniform_bytes_2253 loc( uniform_bytes_2253_loc ) :=
              seq_concat (lift_to_both0 uniform_bytes_2253) (
                lift_to_both0 b_i_2252) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 b_i_2252,
                lift_to_both0 uniform_bytes_2253
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (seq_truncate (
          lift_to_both0 uniform_bytes_2253) (lift_to_both0 len_in_bytes_2257))
      ) : both (CEfset (
        [l_i_b_str_2251_loc ; b_i_2252_loc ; uniform_bytes_2253_loc])) [interface] (
      byte_seq)).
Fail Next Obligation.

Definition output_2268_loc : ChoiceEqualityLocation :=
  (seq fp_t ; 2269%nat).
Notation "'fp_hash_to_field_inp'" :=(
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'fp_hash_to_field_inp'" :=(
  byte_seq '× byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'fp_hash_to_field_out'" :=(
  seq fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_hash_to_field_out'" :=(seq fp_t : ChoiceEquality) (at level 2).
Definition FP_HASH_TO_FIELD : nat :=
  2279.
Program Definition fp_hash_to_field (msg_2272 : byte_seq) (
    dst_2273 : byte_seq) (count_2270 : uint_size)
  : both (CEfset (
      [l_i_b_str_2251_loc ; b_i_2252_loc ; uniform_bytes_2253_loc ; output_2268_loc])) [interface] (
    seq fp_t) :=
  ((letb len_in_bytes_2271 : uint_size :=
        (lift_to_both0 count_2270) .* (lift_to_both0 l_v) in
      letb uniform_bytes_2274 : seq uint8 :=
        expand_message_xmd (lift_to_both0 msg_2272) (lift_to_both0 dst_2273) (
          lift_to_both0 len_in_bytes_2271) in
      letbm output_2268 : seq fp_t loc( output_2268_loc ) :=
        seq_new_ (default : fp_t) (lift_to_both0 count_2270) in
      letb output_2268 :=
        foldi_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 count_2270) output_2268 (L := (CEfset (
                [l_i_b_str_2251_loc ; b_i_2252_loc ; uniform_bytes_2253_loc ; output_2268_loc]))) (
            I := [interface]) (fun i_2275 output_2268 =>
            letb elm_offset_2276 : uint_size :=
              (lift_to_both0 l_v) .* (lift_to_both0 i_2275) in
            letb tv_2277 : seq uint8 :=
              seq_slice (lift_to_both0 uniform_bytes_2274) (
                lift_to_both0 elm_offset_2276) (lift_to_both0 l_v) in
            letb u_i_2278 : fp_t :=
              nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
                    nat_mod_from_byte_seq_be (lift_to_both0 tv_2277))) (
                  lift_to_both0 (usize 16)) (lift_to_both0 (usize 48))) in
            letb output_2268 : seq fp_t :=
              seq_upd output_2268 (lift_to_both0 i_2275) (is_pure (
                  lift_to_both0 u_i_2278)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 output_2268)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 output_2268)
      ) : both (CEfset (
        [l_i_b_str_2251_loc ; b_i_2252_loc ; uniform_bytes_2253_loc ; output_2268_loc])) [interface] (
      seq fp_t)).
Fail Next Obligation.


Notation "'fp_sgn0_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_sgn0_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'fp_sgn0_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'fp_sgn0_out'" :=(bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition FP_SGN0 : nat :=
  2281.
Program Definition fp_sgn0 (x_2280 : fp_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 x_2280) rem (nat_mod_two )) =.? (nat_mod_one ))
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
  2285.
Program Definition fp_is_square (x_2283 : fp_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb c1_2282 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_1_2_v)) in
      letb tv_2284 : fp_t :=
        nat_mod_pow_self (lift_to_both0 x_2283) (lift_to_both0 c1_2282) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 tv_2284) =.? (nat_mod_zero )) || ((
            lift_to_both0 tv_2284) =.? (nat_mod_one )))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'fp_sqrt_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_sqrt_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'fp_sqrt_out'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_sqrt_out'" :=(fp_t : ChoiceEquality) (at level 2).
Definition FP_SQRT : nat :=
  2288.
Program Definition fp_sqrt (x_2287 : fp_t)
  : both (fset.fset0) [interface] (fp_t) :=
  ((letb c1_2286 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_1_4_v)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (nat_mod_pow_self (
          lift_to_both0 x_2287) (lift_to_both0 c1_2286))
      ) : both (fset.fset0) [interface] (fp_t)).
Fail Next Obligation.


Notation "'g1_curve_func_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_curve_func_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'g1_curve_func_out'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_curve_func_out'" :=(fp_t : ChoiceEquality) (at level 2).
Definition G1_CURVE_FUNC : nat :=
  2290.
Program Definition g1_curve_func (x_2289 : fp_t)
  : both (fset.fset0) [interface] (fp_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((((
              lift_to_both0 x_2289) *% (lift_to_both0 x_2289)) *% (
            lift_to_both0 x_2289)) +% (nat_mod_from_literal (_) (lift_to_both0 (
              @repr U128 4))))
      ) : both (fset.fset0) [interface] (fp_t)).
Fail Next Obligation.

Definition y_2292_loc : ChoiceEqualityLocation :=
  (fp_t ; 2293%nat).
Definition tv4_2291_loc : ChoiceEqualityLocation :=
  (fp_t ; 2294%nat).
Notation "'g1_map_to_curve_svdw_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_map_to_curve_svdw_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'g1_map_to_curve_svdw_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_map_to_curve_svdw_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1_MAP_TO_CURVE_SVDW : nat :=
  2308.
Program Definition g1_map_to_curve_svdw (u_2297 : fp_t)
  : both (CEfset ([tv4_2291_loc ; y_2292_loc])) [interface] (g1_t) :=
  ((letb z_2295 : fp_t :=
        (nat_mod_zero ) -% (nat_mod_from_literal (_) (lift_to_both0 (
              @repr U128 3))) in
      letb gz_2296 : fp_t := g1_curve_func (lift_to_both0 z_2295) in
      letb tv1_2298 : fp_t :=
        ((lift_to_both0 u_2297) *% (lift_to_both0 u_2297)) *% (
          lift_to_both0 gz_2296) in
      letb tv2_2299 : fp_t := (nat_mod_one ) +% (lift_to_both0 tv1_2298) in
      letb tv1_2300 : fp_t := (nat_mod_one ) -% (lift_to_both0 tv1_2298) in
      letb tv3_2301 : fp_t :=
        nat_mod_inv ((lift_to_both0 tv1_2300) *% (lift_to_both0 tv2_2299)) in
      letbm tv4_2291 : fp_t loc( tv4_2291_loc ) :=
        fp_sqrt (((nat_mod_zero ) -% (lift_to_both0 gz_2296)) *% (((
                nat_mod_from_literal (_) (lift_to_both0 (@repr U128 3))) *% (
                lift_to_both0 z_2295)) *% (lift_to_both0 z_2295))) in
      letb '(tv4_2291) :=
        if fp_sgn0 (lift_to_both0 tv4_2291) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([tv4_2291_loc])) (L2 := CEfset (
            [tv4_2291_loc ; y_2292_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm tv4_2291 loc( tv4_2291_loc ) :=
            (nat_mod_zero ) -% (lift_to_both0 tv4_2291) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 tv4_2291)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 tv4_2291)
         in
      letb tv5_2302 : fp_t :=
        (((lift_to_both0 u_2297) *% (lift_to_both0 tv1_2300)) *% (
            lift_to_both0 tv3_2301)) *% (lift_to_both0 tv4_2291) in
      letb tv6_2303 : fp_t :=
        (((nat_mod_zero ) -% (nat_mod_from_literal (_) (lift_to_both0 (
                  @repr U128 4)))) *% (lift_to_both0 gz_2296)) *% (nat_mod_inv (
            ((nat_mod_from_literal (_) (lift_to_both0 (@repr U128 3))) *% (
                lift_to_both0 z_2295)) *% (lift_to_both0 z_2295))) in
      letb x1_2304 : fp_t :=
        (((nat_mod_zero ) -% (lift_to_both0 z_2295)) *% (nat_mod_inv (
              nat_mod_two ))) -% (lift_to_both0 tv5_2302) in
      letb x2_2305 : fp_t :=
        (((nat_mod_zero ) -% (lift_to_both0 z_2295)) *% (nat_mod_inv (
              nat_mod_two ))) +% (lift_to_both0 tv5_2302) in
      letb x3_2306 : fp_t :=
        (lift_to_both0 z_2295) +% (((lift_to_both0 tv6_2303) *% (((
                  lift_to_both0 tv2_2299) *% (lift_to_both0 tv2_2299)) *% (
                lift_to_both0 tv3_2301))) *% (((lift_to_both0 tv2_2299) *% (
                lift_to_both0 tv2_2299)) *% (lift_to_both0 tv3_2301))) in
      letb x_2307 : fp_t :=
        if is_pure (I := [interface]) (fp_is_square (g1_curve_func (
              lift_to_both0 x1_2304)))
        then lift_to_both0 x1_2304
        else if is_pure (I := [interface]) (fp_is_square (g1_curve_func (
              lift_to_both0 x2_2305)))
        then lift_to_both0 x2_2305
        else lift_to_both0 x3_2306 in
      letbm y_2292 : fp_t loc( y_2292_loc ) :=
        fp_sqrt (g1_curve_func (lift_to_both0 x_2307)) in
      letb '(y_2292) :=
        if (fp_sgn0 (lift_to_both0 u_2297)) !=.? (fp_sgn0 (
            lift_to_both0 y_2292)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([tv4_2291_loc ; y_2292_loc])) (
          L2 := CEfset ([tv4_2291_loc ; y_2292_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm y_2292 loc( y_2292_loc ) :=
            (nat_mod_zero ) -% (lift_to_both0 y_2292) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 y_2292)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 y_2292)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_2307,
          lift_to_both0 y_2292,
          lift_to_both0 ((false : bool_ChoiceEquality))
        ))
      ) : both (CEfset ([tv4_2291_loc ; y_2292_loc])) [interface] (g1_t)).
Fail Next Obligation.


Notation "'g1_clear_cofactor_inp'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_clear_cofactor_inp'" :=(g1_t : ChoiceEquality) (at level 2).
Notation "'g1_clear_cofactor_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_clear_cofactor_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1_CLEAR_COFACTOR : nat :=
  2311.
Program Definition g1_clear_cofactor (x_2310 : g1_t)
  : both (fset.fset0) [interface] (g1_t) :=
  ((letb h_eff_2309 : scalar_t :=
        nat_mod_from_literal (_) (lift_to_both0 (
            @repr U128 15132376222941642753)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (g1mul (
          lift_to_both0 h_eff_2309) (lift_to_both0 x_2310))
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
  2319.
Program Definition g1_hash_to_curve_svdw (msg_2312 : byte_seq) (
    dst_2313 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2251_loc ; b_i_2252_loc ; uniform_bytes_2253_loc ; output_2268_loc ; tv4_2291_loc ; y_2292_loc])) [interface] (
    g1_t) :=
  ((letb u_2314 : seq fp_t :=
        fp_hash_to_field (lift_to_both0 msg_2312) (lift_to_both0 dst_2313) (
          lift_to_both0 (usize 2)) in
      letb q0_2315 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_map_to_curve_svdw (seq_index (u_2314) (lift_to_both0 (usize 0))) in
      letb q1_2316 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_map_to_curve_svdw (seq_index (u_2314) (lift_to_both0 (usize 1))) in
      letb r_2317 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1add (lift_to_both0 q0_2315) (lift_to_both0 q1_2316) in
      letb p_2318 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_clear_cofactor (lift_to_both0 r_2317) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2318)
      ) : both (CEfset (
        [l_i_b_str_2251_loc ; b_i_2252_loc ; uniform_bytes_2253_loc ; output_2268_loc ; tv4_2291_loc ; y_2292_loc])) [interface] (
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
  2325.
Program Definition g1_encode_to_curve_svdw (msg_2320 : byte_seq) (
    dst_2321 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2251_loc ; b_i_2252_loc ; uniform_bytes_2253_loc ; output_2268_loc ; tv4_2291_loc ; y_2292_loc])) [interface] (
    g1_t) :=
  ((letb u_2322 : seq fp_t :=
        fp_hash_to_field (lift_to_both0 msg_2320) (lift_to_both0 dst_2321) (
          lift_to_both0 (usize 1)) in
      letb q_2323 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_map_to_curve_svdw (seq_index (u_2322) (lift_to_both0 (usize 0))) in
      letb p_2324 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_clear_cofactor (lift_to_both0 q_2323) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2324)
      ) : both (CEfset (
        [l_i_b_str_2251_loc ; b_i_2252_loc ; uniform_bytes_2253_loc ; output_2268_loc ; tv4_2291_loc ; y_2292_loc])) [interface] (
      g1_t)).
Fail Next Obligation.

Definition output_2326_loc : ChoiceEqualityLocation :=
  (seq (fp_t '× fp_t) ; 2327%nat).
Notation "'fp2_hash_to_field_inp'" :=(
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'fp2_hash_to_field_inp'" :=(
  byte_seq '× byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'fp2_hash_to_field_out'" :=(
  seq fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2_hash_to_field_out'" :=(seq fp2_t : ChoiceEquality) (at level 2).
Definition FP2_HASH_TO_FIELD : nat :=
  2340.
Program Definition fp2_hash_to_field (msg_2330 : byte_seq) (
    dst_2331 : byte_seq) (count_2328 : uint_size)
  : both (CEfset (
      [l_i_b_str_2251_loc ; b_i_2252_loc ; uniform_bytes_2253_loc ; output_2326_loc])) [interface] (
    seq fp2_t) :=
  ((letb len_in_bytes_2329 : uint_size :=
        ((lift_to_both0 count_2328) .* (lift_to_both0 (usize 2))) .* (
          lift_to_both0 l_v) in
      letb uniform_bytes_2332 : seq uint8 :=
        expand_message_xmd (lift_to_both0 msg_2330) (lift_to_both0 dst_2331) (
          lift_to_both0 len_in_bytes_2329) in
      letbm output_2326 : seq (fp_t '× fp_t) loc( output_2326_loc ) :=
        seq_new_ (default : fp2_t) (lift_to_both0 count_2328) in
      letb output_2326 :=
        foldi_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 count_2328) output_2326 (L := (CEfset (
                [l_i_b_str_2251_loc ; b_i_2252_loc ; uniform_bytes_2253_loc ; output_2326_loc]))) (
            I := [interface]) (fun i_2333 output_2326 =>
            letb elm_offset_2334 : uint_size :=
              ((lift_to_both0 l_v) .* (lift_to_both0 i_2333)) .* (
                lift_to_both0 (usize 2)) in
            letb tv_2335 : seq uint8 :=
              seq_slice (lift_to_both0 uniform_bytes_2332) (
                lift_to_both0 elm_offset_2334) (lift_to_both0 l_v) in
            letb e_1_2336 : fp_t :=
              nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
                    nat_mod_from_byte_seq_be (lift_to_both0 tv_2335))) (
                  lift_to_both0 (usize 16)) (lift_to_both0 (usize 48))) in
            letb elm_offset_2337 : uint_size :=
              (lift_to_both0 l_v) .* ((lift_to_both0 (usize 1)) .+ ((
                    lift_to_both0 i_2333) .* (lift_to_both0 (usize 2)))) in
            letb tv_2338 : seq uint8 :=
              seq_slice (lift_to_both0 uniform_bytes_2332) (
                lift_to_both0 elm_offset_2337) (lift_to_both0 l_v) in
            letb e_2_2339 : fp_t :=
              nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
                    nat_mod_from_byte_seq_be (lift_to_both0 tv_2338))) (
                  lift_to_both0 (usize 16)) (lift_to_both0 (usize 48))) in
            letb output_2326 : seq (fp_t '× fp_t) :=
              seq_upd output_2326 (lift_to_both0 i_2333) (is_pure (prod_b(
                    lift_to_both0 e_1_2336,
                    lift_to_both0 e_2_2339
                  ))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 output_2326)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 output_2326)
      ) : both (CEfset (
        [l_i_b_str_2251_loc ; b_i_2252_loc ; uniform_bytes_2253_loc ; output_2326_loc])) [interface] (
      seq fp2_t)).
Fail Next Obligation.


Notation "'fp2_sgn0_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2_sgn0_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'fp2_sgn0_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'fp2_sgn0_out'" :=(bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition FP2_SGN0 : nat :=
  2347.
Program Definition fp2_sgn0 (x_2341 : fp2_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb '(x0_2342, x1_2343) : (fp_t '× fp_t) := lift_to_both0 x_2341 in
      letb sign_0_2344 : bool_ChoiceEquality :=
        fp_sgn0 (lift_to_both0 x0_2342) in
      letb zero_0_2345 : bool_ChoiceEquality :=
        (lift_to_both0 x0_2342) =.? (nat_mod_zero ) in
      letb sign_1_2346 : bool_ChoiceEquality :=
        fp_sgn0 (lift_to_both0 x1_2343) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 sign_0_2344) || ((lift_to_both0 zero_0_2345) && (
            lift_to_both0 sign_1_2346)))
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
  2357.
Program Definition fp2_is_square (x_2349 : fp2_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb c1_2348 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_1_2_v)) in
      letb '(x1_2350, x2_2351) : (fp_t '× fp_t) := lift_to_both0 x_2349 in
      letb tv1_2352 : fp_t :=
        (lift_to_both0 x1_2350) *% (lift_to_both0 x1_2350) in
      letb tv2_2353 : fp_t :=
        (lift_to_both0 x2_2351) *% (lift_to_both0 x2_2351) in
      letb tv1_2354 : fp_t :=
        (lift_to_both0 tv1_2352) +% (lift_to_both0 tv2_2353) in
      letb tv1_2355 : fp_t :=
        nat_mod_pow_self (lift_to_both0 tv1_2354) (lift_to_both0 c1_2348) in
      letb neg1_2356 : fp_t := (nat_mod_zero ) -% (nat_mod_one ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 tv1_2355) !=.? (lift_to_both0 neg1_2356))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.

Definition c_2358_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2359%nat).
Notation "'fp2exp_inp'" :=(
  fp2_t '× fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2exp_inp'" :=(fp2_t '× fp_t : ChoiceEquality) (at level 2).
Notation "'fp2exp_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2exp_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition FP2EXP : nat :=
  2363.
Program Definition fp2exp (n_2362 : fp2_t) (k_2361 : fp_t)
  : both (CEfset ([c_2358_loc])) [interface] (fp2_t) :=
  ((letbm c_2358 : (fp_t '× fp_t) loc( c_2358_loc ) :=
        fp2fromfp (nat_mod_one ) in
      letb c_2358 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 381)) c_2358 (L := (CEfset ([c_2358_loc]))) (
            I := [interface]) (fun i_2360 c_2358 =>
            letbm c_2358 loc( c_2358_loc ) :=
              fp2mul (lift_to_both0 c_2358) (lift_to_both0 c_2358) in
            letb '(c_2358) :=
              if nat_mod_bit (lift_to_both0 k_2361) ((lift_to_both0 (
                    usize 380)) .- (lift_to_both0 i_2360)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([c_2358_loc])) (L2 := CEfset (
                  [c_2358_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm c_2358 loc( c_2358_loc ) :=
                  fp2mul (lift_to_both0 c_2358) (lift_to_both0 n_2362) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 c_2358)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 c_2358)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 c_2358)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 c_2358)
      ) : both (CEfset ([c_2358_loc])) [interface] (fp2_t)).
Fail Next Obligation.


Notation "'fp2_sqrt_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2_sqrt_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'fp2_sqrt_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2_sqrt_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition FP2_SQRT : nat :=
  2372.
Program Definition fp2_sqrt (a_2366 : fp2_t)
  : both (CEfset ([c_2358_loc])) [interface] (fp2_t) :=
  ((letb c1_2364 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_3_4_v)) in
      letb c2_2365 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_1_2_v)) in
      letb a1_2367 : (fp_t '× fp_t) :=
        fp2exp (lift_to_both0 a_2366) (lift_to_both0 c1_2364) in
      letb alpha_2368 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 a1_2367) (fp2mul (lift_to_both0 a1_2367) (
            lift_to_both0 a_2366)) in
      letb x0_2369 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 a1_2367) (lift_to_both0 a_2366) in
      letb neg1_2370 : (fp_t '× fp_t) :=
        prod_b((nat_mod_zero ) -% (nat_mod_one ), nat_mod_zero ) in
      letb b_2371 : (fp_t '× fp_t) :=
        fp2exp (fp2add (fp2fromfp (nat_mod_one )) (lift_to_both0 alpha_2368)) (
          lift_to_both0 c2_2365) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 alpha_2368) =.? (
            lift_to_both0 neg1_2370))
        then fp2mul (prod_b(nat_mod_zero , nat_mod_one )) (
          lift_to_both0 x0_2369)
        else fp2mul (lift_to_both0 b_2371) (lift_to_both0 x0_2369))
      ) : both (CEfset ([c_2358_loc])) [interface] (fp2_t)).
Fail Next Obligation.


Notation "'g2_curve_func_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_curve_func_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'g2_curve_func_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_curve_func_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition G2_CURVE_FUNC : nat :=
  2374.
Program Definition g2_curve_func (x_2373 : fp2_t)
  : both (fset.fset0) [interface] (fp2_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp2add (fp2mul (
            lift_to_both0 x_2373) (fp2mul (lift_to_both0 x_2373) (
              lift_to_both0 x_2373))) (prod_b(
            nat_mod_from_literal (_) (lift_to_both0 (@repr U128 4)),
            nat_mod_from_literal (_) (lift_to_both0 (@repr U128 4))
          )))
      ) : both (fset.fset0) [interface] (fp2_t)).
Fail Next Obligation.

Definition y_2376_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2377%nat).
Definition tv4_2375_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2378%nat).
Notation "'g2_map_to_curve_svdw_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_map_to_curve_svdw_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'g2_map_to_curve_svdw_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_map_to_curve_svdw_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_MAP_TO_CURVE_SVDW : nat :=
  2393.
Program Definition g2_map_to_curve_svdw (u_2381 : fp2_t)
  : both (CEfset ([c_2358_loc ; tv4_2375_loc ; y_2376_loc])) [interface] (
    g2_t) :=
  ((letb z_2379 : (fp_t '× fp_t) := fp2neg (fp2fromfp (nat_mod_one )) in
      letb gz_2380 : (fp_t '× fp_t) := g2_curve_func (lift_to_both0 z_2379) in
      letb tv1_2382 : (fp_t '× fp_t) :=
        fp2mul (fp2mul (lift_to_both0 u_2381) (lift_to_both0 u_2381)) (
          lift_to_both0 gz_2380) in
      letb tv2_2383 : (fp_t '× fp_t) :=
        fp2add (fp2fromfp (nat_mod_one )) (lift_to_both0 tv1_2382) in
      letb tv1_2384 : (fp_t '× fp_t) :=
        fp2sub (fp2fromfp (nat_mod_one )) (lift_to_both0 tv1_2382) in
      letb tv3_2385 : (fp_t '× fp_t) :=
        fp2inv (fp2mul (lift_to_both0 tv1_2384) (lift_to_both0 tv2_2383)) in
      letbm tv4_2375 : (fp_t '× fp_t) loc( tv4_2375_loc ) :=
        fp2_sqrt (fp2mul (fp2neg (lift_to_both0 gz_2380)) (fp2mul (fp2fromfp (
                nat_mod_from_literal (_) (lift_to_both0 (@repr U128 3)))) (
              fp2mul (lift_to_both0 z_2379) (lift_to_both0 z_2379)))) in
      letb '(tv4_2375) :=
        if fp2_sgn0 (lift_to_both0 tv4_2375) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([c_2358_loc ; tv4_2375_loc])) (
          L2 := CEfset ([c_2358_loc ; tv4_2375_loc ; y_2376_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm tv4_2375 loc( tv4_2375_loc ) :=
            fp2neg (lift_to_both0 tv4_2375) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 tv4_2375)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 tv4_2375)
         in
      letb tv5_2386 : (fp_t '× fp_t) :=
        fp2mul (fp2mul (fp2mul (lift_to_both0 u_2381) (
              lift_to_both0 tv1_2384)) (lift_to_both0 tv3_2385)) (
          lift_to_both0 tv4_2375) in
      letb tv6_2387 : (fp_t '× fp_t) :=
        fp2mul (fp2mul (fp2neg (fp2fromfp (nat_mod_from_literal (_) (
                  lift_to_both0 (@repr U128 4))))) (lift_to_both0 gz_2380)) (
          fp2inv (fp2mul (fp2fromfp (nat_mod_from_literal (_) (lift_to_both0 (
                    @repr U128 3)))) (fp2mul (lift_to_both0 z_2379) (
                lift_to_both0 z_2379)))) in
      letb x1_2388 : (fp_t '× fp_t) :=
        fp2sub (fp2mul (fp2neg (lift_to_both0 z_2379)) (fp2inv (fp2fromfp (
                nat_mod_two )))) (lift_to_both0 tv5_2386) in
      letb x2_2389 : (fp_t '× fp_t) :=
        fp2add (fp2mul (fp2neg (lift_to_both0 z_2379)) (fp2inv (fp2fromfp (
                nat_mod_two )))) (lift_to_both0 tv5_2386) in
      letb tv7_2390 : (fp_t '× fp_t) :=
        fp2mul (fp2mul (lift_to_both0 tv2_2383) (lift_to_both0 tv2_2383)) (
          lift_to_both0 tv3_2385) in
      letb x3_2391 : (fp_t '× fp_t) :=
        fp2add (lift_to_both0 z_2379) (fp2mul (lift_to_both0 tv6_2387) (fp2mul (
              lift_to_both0 tv7_2390) (lift_to_both0 tv7_2390))) in
      letb x_2392 : (fp_t '× fp_t) :=
        if is_pure (I := [interface]) (fp2_is_square (g2_curve_func (
              lift_to_both0 x1_2388)))
        then lift_to_both0 x1_2388
        else if is_pure (I := [interface]) (fp2_is_square (g2_curve_func (
              lift_to_both0 x2_2389)))
        then lift_to_both0 x2_2389
        else lift_to_both0 x3_2391 in
      letbm y_2376 : (fp_t '× fp_t) loc( y_2376_loc ) :=
        fp2_sqrt (g2_curve_func (lift_to_both0 x_2392)) in
      letb '(y_2376) :=
        if (fp2_sgn0 (lift_to_both0 u_2381)) !=.? (fp2_sgn0 (
            lift_to_both0 y_2376)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [c_2358_loc ; tv4_2375_loc ; y_2376_loc])) (L2 := CEfset (
            [c_2358_loc ; tv4_2375_loc ; y_2376_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm y_2376 loc( y_2376_loc ) := fp2neg (lift_to_both0 y_2376) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 y_2376)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 y_2376)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_2392,
          lift_to_both0 y_2376,
          lift_to_both0 ((false : bool_ChoiceEquality))
        ))
      ) : both (CEfset ([c_2358_loc ; tv4_2375_loc ; y_2376_loc])) [interface] (
      g2_t)).
Fail Next Obligation.


Notation "'psi_inp'" :=(g2_t : choice_type) (in custom pack_type at level 2).
Notation "'psi_inp'" :=(g2_t : ChoiceEquality) (at level 2).
Notation "'psi_out'" :=(g2_t : choice_type) (in custom pack_type at level 2).
Notation "'psi_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition PSI : nat :=
  2402.
Program Definition psi (p_2396 : g2_t)
  : both (CEfset ([c_2358_loc])) [interface] (g2_t) :=
  ((letb c1_2394 : (fp_t '× fp_t) :=
        fp2inv (fp2exp (prod_b(nat_mod_one , nat_mod_one )) (((
                nat_mod_zero ) -% (nat_mod_one )) *% (nat_mod_inv (
                nat_mod_from_literal (_) (lift_to_both0 (@repr U128 3)))))) in
      letb c2_2395 : (fp_t '× fp_t) :=
        fp2inv (fp2exp (prod_b(nat_mod_one , nat_mod_one )) (((
                nat_mod_zero ) -% (nat_mod_one )) *% (nat_mod_inv (
                nat_mod_two )))) in
      letb '(x_2397, y_2398, inf_2399) : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        lift_to_both0 p_2396 in
      letb qx_2400 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 c1_2394) (fp2conjugate (lift_to_both0 x_2397)) in
      letb qy_2401 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 c2_2395) (fp2conjugate (lift_to_both0 y_2398)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 qx_2400,
          lift_to_both0 qy_2401,
          lift_to_both0 inf_2399
        ))
      ) : both (CEfset ([c_2358_loc])) [interface] (g2_t)).
Fail Next Obligation.


Notation "'g2_clear_cofactor_inp'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_clear_cofactor_inp'" :=(g2_t : ChoiceEquality) (at level 2).
Notation "'g2_clear_cofactor_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_clear_cofactor_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_CLEAR_COFACTOR : nat :=
  2417.
Program Definition g2_clear_cofactor (p_2404 : g2_t)
  : both (CEfset ([c_2358_loc])) [interface] (g2_t) :=
  ((letb c1_2403 : scalar_t :=
        nat_mod_from_literal (_) (lift_to_both0 (
            @repr U128 15132376222941642752)) in
      letb t1_2405 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2mul (lift_to_both0 c1_2403) (lift_to_both0 p_2404) in
      letb t1_2406 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2neg (lift_to_both0 t1_2405) in
      letb t2_2407 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        psi (lift_to_both0 p_2404) in
      letb t3_2408 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2double (lift_to_both0 p_2404) in
      letb t3_2409 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        psi (psi (lift_to_both0 t3_2408)) in
      letb t3_2410 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 t3_2409) (g2neg (lift_to_both0 t2_2407)) in
      letb t2_2411 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 t1_2406) (lift_to_both0 t2_2407) in
      letb t2_2412 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2mul (lift_to_both0 c1_2403) (lift_to_both0 t2_2411) in
      letb t2_2413 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2neg (lift_to_both0 t2_2412) in
      letb t3_2414 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 t3_2410) (lift_to_both0 t2_2413) in
      letb t3_2415 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 t3_2414) (g2neg (lift_to_both0 t1_2406)) in
      letb q_2416 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 t3_2415) (g2neg (lift_to_both0 p_2404)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 q_2416)
      ) : both (CEfset ([c_2358_loc])) [interface] (g2_t)).
Fail Next Obligation.


Notation "'g2_hash_to_curve_svdw_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g2_hash_to_curve_svdw_inp'" :=(
  byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'g2_hash_to_curve_svdw_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_hash_to_curve_svdw_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_HASH_TO_CURVE_SVDW : nat :=
  2425.
Program Definition g2_hash_to_curve_svdw (msg_2418 : byte_seq) (
    dst_2419 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2251_loc ; b_i_2252_loc ; uniform_bytes_2253_loc ; output_2326_loc ; c_2358_loc ; tv4_2375_loc ; y_2376_loc])) [interface] (
    g2_t) :=
  ((letb u_2420 : seq fp2_t :=
        fp2_hash_to_field (lift_to_both0 msg_2418) (lift_to_both0 dst_2419) (
          lift_to_both0 (usize 2)) in
      letb q0_2421 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2_map_to_curve_svdw (seq_index (u_2420) (lift_to_both0 (usize 0))) in
      letb q1_2422 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2_map_to_curve_svdw (seq_index (u_2420) (lift_to_both0 (usize 1))) in
      letb r_2423 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 q0_2421) (lift_to_both0 q1_2422) in
      letb p_2424 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_clear_cofactor (lift_to_both0 r_2423) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2424)
      ) : both (CEfset (
        [l_i_b_str_2251_loc ; b_i_2252_loc ; uniform_bytes_2253_loc ; output_2326_loc ; c_2358_loc ; tv4_2375_loc ; y_2376_loc])) [interface] (
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
  2431.
Program Definition g2_encode_to_curve_svdw (msg_2426 : byte_seq) (
    dst_2427 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2251_loc ; b_i_2252_loc ; uniform_bytes_2253_loc ; output_2326_loc ; c_2358_loc ; tv4_2375_loc ; y_2376_loc])) [interface] (
    g2_t) :=
  ((letb u_2428 : seq fp2_t :=
        fp2_hash_to_field (lift_to_both0 msg_2426) (lift_to_both0 dst_2427) (
          lift_to_both0 (usize 1)) in
      letb q_2429 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_map_to_curve_svdw (seq_index (u_2428) (lift_to_both0 (usize 0))) in
      letb p_2430 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_clear_cofactor (lift_to_both0 q_2429) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2430)
      ) : both (CEfset (
        [l_i_b_str_2251_loc ; b_i_2252_loc ; uniform_bytes_2253_loc ; output_2326_loc ; c_2358_loc ; tv4_2375_loc ; y_2376_loc])) [interface] (
      g2_t)).
Fail Next Obligation.

Definition g1_iso_a_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 5707120929990979)) : uint64;
    (secret (@repr U64 4425131892511951234)) : uint64;
    (secret (@repr U64 12748169179688756904)) : uint64;
    (secret (@repr U64 15629909748249821612)) : uint64;
    (secret (@repr U64 10994253769421683071)) : uint64;
    (secret (@repr U64 6698022561392380957)) : uint64
  ].

Definition g1_iso_b_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1360808972976160816)) : uint64;
    (secret (@repr U64 111203405409480251)) : uint64;
    (secret (@repr U64 2312248699302920304)) : uint64;
    (secret (@repr U64 11581500465278574325)) : uint64;
    (secret (@repr U64 6495071758858381989)) : uint64;
    (secret (@repr U64 15117538217124375520)) : uint64
  ].

Definition g1_xnum_k_0_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1270119733718627136)) : uint64;
    (secret (@repr U64 13261148298159854981)) : uint64;
    (secret (@repr U64 7723742117508874335)) : uint64;
    (secret (@repr U64 17465657917644792520)) : uint64;
    (secret (@repr U64 6201670911048166766)) : uint64;
    (secret (@repr U64 12586459670690286007)) : uint64
  ].

Definition g1_xnum_k_1_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1668951808976071471)) : uint64;
    (secret (@repr U64 398773841247578140)) : uint64;
    (secret (@repr U64 8941869963990959127)) : uint64;
    (secret (@repr U64 17682789360670468203)) : uint64;
    (secret (@repr U64 5204176168283587414)) : uint64;
    (secret (@repr U64 16732261237459223483)) : uint64
  ].

Definition g1_xnum_k_2_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 960393023080265964)) : uint64;
    (secret (@repr U64 2094253841180170779)) : uint64;
    (secret (@repr U64 14844748873776858085)) : uint64;
    (secret (@repr U64 7528018573573808732)) : uint64;
    (secret (@repr U64 10776056440809943711)) : uint64;
    (secret (@repr U64 16147550488514976944)) : uint64
  ].

Definition g1_xnum_k_3_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1691355743628586423)) : uint64;
    (secret (@repr U64 5622191986793862162)) : uint64;
    (secret (@repr U64 15561595211679121189)) : uint64;
    (secret (@repr U64 17416319752018800771)) : uint64;
    (secret (@repr U64 5996228842464768403)) : uint64;
    (secret (@repr U64 14245880009877842017)) : uint64
  ].

Definition g1_xnum_k_4_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1051997788391994435)) : uint64;
    (secret (@repr U64 7368650625050054228)) : uint64;
    (secret (@repr U64 11086623519836470079)) : uint64;
    (secret (@repr U64 607681821319080984)) : uint64;
    (secret (@repr U64 10978131499682789316)) : uint64;
    (secret (@repr U64 5842660658088809945)) : uint64
  ].

Definition g1_xnum_k_5_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1598992431623377919)) : uint64;
    (secret (@repr U64 130921168661596853)) : uint64;
    (secret (@repr U64 15797696746983946651)) : uint64;
    (secret (@repr U64 11444679715590672272)) : uint64;
    (secret (@repr U64 11567228658253249817)) : uint64;
    (secret (@repr U64 14777367860349315459)) : uint64
  ].

Definition g1_xnum_k_6_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 967946631563726121)) : uint64;
    (secret (@repr U64 7653628713030275775)) : uint64;
    (secret (@repr U64 12760252618317466849)) : uint64;
    (secret (@repr U64 10378793938173061930)) : uint64;
    (secret (@repr U64 10205808941053849290)) : uint64;
    (secret (@repr U64 15985511645807504772)) : uint64
  ].

Definition g1_xnum_k_7_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1709149555065084898)) : uint64;
    (secret (@repr U64 16750075057192140371)) : uint64;
    (secret (@repr U64 3849985779734105521)) : uint64;
    (secret (@repr U64 11998370262181639475)) : uint64;
    (secret (@repr U64 4159013751748851119)) : uint64;
    (secret (@repr U64 11298218755092433038)) : uint64
  ].

Definition g1_xnum_k_8_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 580186936973955012)) : uint64;
    (secret (@repr U64 8903813505199544589)) : uint64;
    (secret (@repr U64 14140024565662700916)) : uint64;
    (secret (@repr U64 11728946595272970718)) : uint64;
    (secret (@repr U64 5738313744366653077)) : uint64;
    (secret (@repr U64 7886252005760951063)) : uint64
  ].

Definition g1_xnum_k_9_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1628930385436977092)) : uint64;
    (secret (@repr U64 3318087848058654498)) : uint64;
    (secret (@repr U64 15937899882900905113)) : uint64;
    (secret (@repr U64 7449821001803307903)) : uint64;
    (secret (@repr U64 11752436998487615353)) : uint64;
    (secret (@repr U64 9161465579737517214)) : uint64
  ].

Definition g1_xnum_k_10_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1167027828517898210)) : uint64;
    (secret (@repr U64 8275623842221021965)) : uint64;
    (secret (@repr U64 18049808134997311382)) : uint64;
    (secret (@repr U64 15351349873550116966)) : uint64;
    (secret (@repr U64 17769927732099571180)) : uint64;
    (secret (@repr U64 14584871380308065147)) : uint64
  ].

Definition g1_xnum_k_11_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 495550047642324592)) : uint64;
    (secret (@repr U64 13627494601717575229)) : uint64;
    (secret (@repr U64 3591512392926246844)) : uint64;
    (secret (@repr U64 2576269112800734056)) : uint64;
    (secret (@repr U64 14000314106239596831)) : uint64;
    (secret (@repr U64 12234233096825917993)) : uint64
  ].

Definition g1_xden_k_0_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 633474091881273774)) : uint64;
    (secret (@repr U64 1779737893574802031)) : uint64;
    (secret (@repr U64 132274872219551930)) : uint64;
    (secret (@repr U64 11283074393783708770)) : uint64;
    (secret (@repr U64 13067430171545714168)) : uint64;
    (secret (@repr U64 11041975239630265116)) : uint64
  ].

Definition g1_xden_k_1_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1321272531362356291)) : uint64;
    (secret (@repr U64 5238936591227237942)) : uint64;
    (secret (@repr U64 8089002360232247308)) : uint64;
    (secret (@repr U64 82967328719421271)) : uint64;
    (secret (@repr U64 1430641118356186857)) : uint64;
    (secret (@repr U64 16557527386785790975)) : uint64
  ].

Definition g1_xden_k_2_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 804282852993868382)) : uint64;
    (secret (@repr U64 9311163821600184607)) : uint64;
    (secret (@repr U64 8037026956533927121)) : uint64;
    (secret (@repr U64 18205324308570099372)) : uint64;
    (secret (@repr U64 15466434890074226396)) : uint64;
    (secret (@repr U64 18213183315621985817)) : uint64
  ].

Definition g1_xden_k_3_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 234844145893171966)) : uint64;
    (secret (@repr U64 14428037799351479124)) : uint64;
    (secret (@repr U64 6559532710647391569)) : uint64;
    (secret (@repr U64 6110444250091843536)) : uint64;
    (secret (@repr U64 5293652763671852484)) : uint64;
    (secret (@repr U64 1373009181854280920)) : uint64
  ].

Definition g1_xden_k_4_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1416629893867312296)) : uint64;
    (secret (@repr U64 751851957792514173)) : uint64;
    (secret (@repr U64 18437674587247370939)) : uint64;
    (secret (@repr U64 10190314345946351322)) : uint64;
    (secret (@repr U64 11228207967368476701)) : uint64;
    (secret (@repr U64 6025034940388909598)) : uint64
  ].

Definition g1_xden_k_5_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1041270466333271993)) : uint64;
    (secret (@repr U64 6140956605115975401)) : uint64;
    (secret (@repr U64 4131830461445745997)) : uint64;
    (secret (@repr U64 739642499118176303)) : uint64;
    (secret (@repr U64 8358912131254619921)) : uint64;
    (secret (@repr U64 13847998906088228005)) : uint64
  ].

Definition g1_xden_k_6_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 536714149743900185)) : uint64;
    (secret (@repr U64 1098328982230230817)) : uint64;
    (secret (@repr U64 6273329123533496713)) : uint64;
    (secret (@repr U64 5633448088282521244)) : uint64;
    (secret (@repr U64 16894043798660571244)) : uint64;
    (secret (@repr U64 17016134625831438906)) : uint64
  ].

Definition g1_xden_k_7_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1488347500898461874)) : uint64;
    (secret (@repr U64 3509418672874520985)) : uint64;
    (secret (@repr U64 7962192351555381416)) : uint64;
    (secret (@repr U64 1843909372225399896)) : uint64;
    (secret (@repr U64 1127511003250156243)) : uint64;
    (secret (@repr U64 1294742680819751518)) : uint64
  ].

Definition g1_xden_k_8_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 725340084226051970)) : uint64;
    (secret (@repr U64 6814521545734988748)) : uint64;
    (secret (@repr U64 16176803544133875307)) : uint64;
    (secret (@repr U64 8363199516777220149)) : uint64;
    (secret (@repr U64 252877309218538352)) : uint64;
    (secret (@repr U64 5149562959837648449)) : uint64
  ].

Definition g1_xden_k_9_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 675470927100193492)) : uint64;
    (secret (@repr U64 5146891164735334016)) : uint64;
    (secret (@repr U64 17762958817130696759)) : uint64;
    (secret (@repr U64 8565656522589412373)) : uint64;
    (secret (@repr U64 10599026333335446784)) : uint64;
    (secret (@repr U64 3270603789344496906)) : uint64
  ].

Definition g1_ynum_k_0_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 652344406751465184)) : uint64;
    (secret (@repr U64 2710356675495255290)) : uint64;
    (secret (@repr U64 1273695771440998738)) : uint64;
    (secret (@repr U64 3121750372618945491)) : uint64;
    (secret (@repr U64 14775319642720936898)) : uint64;
    (secret (@repr U64 13733803417833814835)) : uint64
  ].

Definition g1_ynum_k_1_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1389807578337138705)) : uint64;
    (secret (@repr U64 15352831428748068483)) : uint64;
    (secret (@repr U64 1307144967559264317)) : uint64;
    (secret (@repr U64 1121505450578652468)) : uint64;
    (secret (@repr U64 15475889019760388287)) : uint64;
    (secret (@repr U64 16183658160488302230)) : uint64
  ].

Definition g1_ynum_k_2_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 57553299067792998)) : uint64;
    (secret (@repr U64 17628079362768849300)) : uint64;
    (secret (@repr U64 2689461337731570914)) : uint64;
    (secret (@repr U64 14070580367580990887)) : uint64;
    (secret (@repr U64 15162865775551710499)) : uint64;
    (secret (@repr U64 13321614990632673782)) : uint64
  ].

Definition g1_ynum_k_3_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 141972750621744161)) : uint64;
    (secret (@repr U64 8689824239172478807)) : uint64;
    (secret (@repr U64 15288216298323671324)) : uint64;
    (secret (@repr U64 712874875091754233)) : uint64;
    (secret (@repr U64 16014900032503684588)) : uint64;
    (secret (@repr U64 11976580453200426187)) : uint64
  ].

Definition g1_ynum_k_4_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 633886036738506515)) : uint64;
    (secret (@repr U64 6678644607214234052)) : uint64;
    (secret (@repr U64 1825425679455244472)) : uint64;
    (secret (@repr U64 8755912272271186652)) : uint64;
    (secret (@repr U64 3379943669301788840)) : uint64;
    (secret (@repr U64 4735212769449148123)) : uint64
  ].

Definition g1_ynum_k_5_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1612358804494830442)) : uint64;
    (secret (@repr U64 2454990789666711200)) : uint64;
    (secret (@repr U64 8405916841409361853)) : uint64;
    (secret (@repr U64 8525415512662168654)) : uint64;
    (secret (@repr U64 2323684950984523890)) : uint64;
    (secret (@repr U64 11074978966450447856)) : uint64
  ].

Definition g1_ynum_k_6_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 336375361001233340)) : uint64;
    (secret (@repr U64 12882959944969186108)) : uint64;
    (secret (@repr U64 16671121624101127371)) : uint64;
    (secret (@repr U64 5922586712221110071)) : uint64;
    (secret (@repr U64 5163511947597922654)) : uint64;
    (secret (@repr U64 14511152726087948018)) : uint64
  ].

Definition g1_ynum_k_7_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 686738286210365551)) : uint64;
    (secret (@repr U64 16039894141796533876)) : uint64;
    (secret (@repr U64 1660145734357211167)) : uint64;
    (secret (@repr U64 18231571463891878950)) : uint64;
    (secret (@repr U64 4825120264949852469)) : uint64;
    (secret (@repr U64 11627815551290637097)) : uint64
  ].

Definition g1_ynum_k_8_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 719520515476580427)) : uint64;
    (secret (@repr U64 16756942182913253819)) : uint64;
    (secret (@repr U64 10320769399998235244)) : uint64;
    (secret (@repr U64 2200974244968450750)) : uint64;
    (secret (@repr U64 7626373186594408355)) : uint64;
    (secret (@repr U64 6933025920263103879)) : uint64
  ].

Definition g1_ynum_k_9_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1016611174344998325)) : uint64;
    (secret (@repr U64 2466492548686891555)) : uint64;
    (secret (@repr U64 14135124294293452542)) : uint64;
    (secret (@repr U64 475233659467912251)) : uint64;
    (secret (@repr U64 11186783513499056751)) : uint64;
    (secret (@repr U64 3147922594245844016)) : uint64
  ].

Definition g1_ynum_k_10_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1833315000454533566)) : uint64;
    (secret (@repr U64 1007974600900082579)) : uint64;
    (secret (@repr U64 14785260176242854207)) : uint64;
    (secret (@repr U64 15066861003931772432)) : uint64;
    (secret (@repr U64 3584647998681889532)) : uint64;
    (secret (@repr U64 16722834201330696498)) : uint64
  ].

Definition g1_ynum_k_11_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1780164921828767454)) : uint64;
    (secret (@repr U64 13337622794239929804)) : uint64;
    (secret (@repr U64 5923739534552515142)) : uint64;
    (secret (@repr U64 3345046972101780530)) : uint64;
    (secret (@repr U64 5321510883028162054)) : uint64;
    (secret (@repr U64 14846055306840460686)) : uint64
  ].

Definition g1_ynum_k_12_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 799438051374502809)) : uint64;
    (secret (@repr U64 15083972834952036164)) : uint64;
    (secret (@repr U64 8838227588559581326)) : uint64;
    (secret (@repr U64 13846054168121598783)) : uint64;
    (secret (@repr U64 488730451382505970)) : uint64;
    (secret (@repr U64 958146249756188408)) : uint64
  ].

Definition g1_ynum_k_13_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 163716820423854747)) : uint64;
    (secret (@repr U64 8285498163857659356)) : uint64;
    (secret (@repr U64 8465424830341846400)) : uint64;
    (secret (@repr U64 1433942577299613084)) : uint64;
    (secret (@repr U64 14325828012864645732)) : uint64;
    (secret (@repr U64 4817114329354076467)) : uint64
  ].

Definition g1_ynum_k_14_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 414658151749832465)) : uint64;
    (secret (@repr U64 189531577938912252)) : uint64;
    (secret (@repr U64 6802473390048830824)) : uint64;
    (secret (@repr U64 15684647020317539556)) : uint64;
    (secret (@repr U64 7755485098777620407)) : uint64;
    (secret (@repr U64 9685868895687483979)) : uint64
  ].

Definition g1_ynum_k_15_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1578157964224562126)) : uint64;
    (secret (@repr U64 5666948055268535989)) : uint64;
    (secret (@repr U64 14634479491382401593)) : uint64;
    (secret (@repr U64 6317940024988860850)) : uint64;
    (secret (@repr U64 13142913832013798519)) : uint64;
    (secret (@repr U64 338991247778166276)) : uint64
  ].

Definition g1_yden_k_0_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1590100849350973618)) : uint64;
    (secret (@repr U64 5915497081334721257)) : uint64;
    (secret (@repr U64 6924968209373727718)) : uint64;
    (secret (@repr U64 17204633670617869946)) : uint64;
    (secret (@repr U64 572916540828819565)) : uint64;
    (secret (@repr U64 92203205520679873)) : uint64
  ].

Definition g1_yden_k_1_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1829261189398470686)) : uint64;
    (secret (@repr U64 1877083417397643448)) : uint64;
    (secret (@repr U64 9640042925497046428)) : uint64;
    (secret (@repr U64 11862766565471805471)) : uint64;
    (secret (@repr U64 8693114993904885301)) : uint64;
    (secret (@repr U64 3672140328108400701)) : uint64
  ].

Definition g1_yden_k_2_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 400243331105348135)) : uint64;
    (secret (@repr U64 8046435537999802711)) : uint64;
    (secret (@repr U64 8702226981475745585)) : uint64;
    (secret (@repr U64 879791671491744492)) : uint64;
    (secret (@repr U64 11994630442058346377)) : uint64;
    (secret (@repr U64 2172204746352322546)) : uint64
  ].

Definition g1_yden_k_3_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1637008473169220501)) : uint64;
    (secret (@repr U64 17441636237435581649)) : uint64;
    (secret (@repr U64 15066165676546511630)) : uint64;
    (secret (@repr U64 1314387578457599809)) : uint64;
    (secret (@repr U64 8247046336453711789)) : uint64;
    (secret (@repr U64 12164906044230685718)) : uint64
  ].

Definition g1_yden_k_4_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 855930740911588324)) : uint64;
    (secret (@repr U64 12685735333705453020)) : uint64;
    (secret (@repr U64 14326404096614579120)) : uint64;
    (secret (@repr U64 6066025509460822294)) : uint64;
    (secret (@repr U64 11676450493790612973)) : uint64;
    (secret (@repr U64 15724621714793234461)) : uint64
  ].

Definition g1_yden_k_5_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 637792788410719021)) : uint64;
    (secret (@repr U64 11507373155986977154)) : uint64;
    (secret (@repr U64 13186912195705886849)) : uint64;
    (secret (@repr U64 14262012144631372388)) : uint64;
    (secret (@repr U64 5328758613570342114)) : uint64;
    (secret (@repr U64 199925847119476652)) : uint64
  ].

Definition g1_yden_k_6_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1612297190139091759)) : uint64;
    (secret (@repr U64 14103733843373163083)) : uint64;
    (secret (@repr U64 6840121186619029743)) : uint64;
    (secret (@repr U64 6760859324815900753)) : uint64;
    (secret (@repr U64 15418807805142572985)) : uint64;
    (secret (@repr U64 4402853133867972444)) : uint64
  ].

Definition g1_yden_k_7_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1631410310868805610)) : uint64;
    (secret (@repr U64 269334146695233390)) : uint64;
    (secret (@repr U64 16547411811928854487)) : uint64;
    (secret (@repr U64 18353100669930795314)) : uint64;
    (secret (@repr U64 13339932232668798692)) : uint64;
    (secret (@repr U64 6984591927261867737)) : uint64
  ].

Definition g1_yden_k_8_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1758313625630302499)) : uint64;
    (secret (@repr U64 1881349400343039172)) : uint64;
    (secret (@repr U64 18013005311323887904)) : uint64;
    (secret (@repr U64 12377427846571989832)) : uint64;
    (secret (@repr U64 5967237584920922243)) : uint64;
    (secret (@repr U64 7720081932193848650)) : uint64
  ].

Definition g1_yden_k_9_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1619701357752249884)) : uint64;
    (secret (@repr U64 16898074901591262352)) : uint64;
    (secret (@repr U64 3609344159736760251)) : uint64;
    (secret (@repr U64 5983130161189999867)) : uint64;
    (secret (@repr U64 14355327869992416094)) : uint64;
    (secret (@repr U64 3778226018344582997)) : uint64
  ].

Definition g1_yden_k_10_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 347606589330687421)) : uint64;
    (secret (@repr U64 5255719044972187933)) : uint64;
    (secret (@repr U64 11271894388753671721)) : uint64;
    (secret (@repr U64 1033887512062764488)) : uint64;
    (secret (@repr U64 8189165486932690436)) : uint64;
    (secret (@repr U64 70004379462101672)) : uint64
  ].

Definition g1_yden_k_11_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 778202887894139711)) : uint64;
    (secret (@repr U64 17691595219776375879)) : uint64;
    (secret (@repr U64 9193253711563866834)) : uint64;
    (secret (@repr U64 10092455202333888821)) : uint64;
    (secret (@repr U64 1655469341950262250)) : uint64;
    (secret (@repr U64 10845992994110574738)) : uint64
  ].

Definition g1_yden_k_12_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 781015344221683683)) : uint64;
    (secret (@repr U64 14078588081290548374)) : uint64;
    (secret (@repr U64 6067271023149908518)) : uint64;
    (secret (@repr U64 9033357708497886086)) : uint64;
    (secret (@repr U64 10592474449179118273)) : uint64;
    (secret (@repr U64 2204988348113831372)) : uint64
  ].

Definition g1_yden_k_13_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 172830037692534587)) : uint64;
    (secret (@repr U64 7101012286790006514)) : uint64;
    (secret (@repr U64 13787308004332873665)) : uint64;
    (secret (@repr U64 14660498759553796110)) : uint64;
    (secret (@repr U64 4757234684169342080)) : uint64;
    (secret (@repr U64 15130647872920159991)) : uint64
  ].

Definition g1_yden_k_14_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1013206390650290238)) : uint64;
    (secret (@repr U64 7720336747103001025)) : uint64;
    (secret (@repr U64 8197694151986493523)) : uint64;
    (secret (@repr U64 3625112747029342752)) : uint64;
    (secret (@repr U64 6675167463148394368)) : uint64;
    (secret (@repr U64 4905905684016745359)) : uint64
  ].

Definition x1_2432_loc : ChoiceEqualityLocation :=
  (fp_t ; 2434%nat).
Definition y_2433_loc : ChoiceEqualityLocation :=
  (fp_t ; 2435%nat).
Notation "'g1_simple_swu_iso_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_simple_swu_iso_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'g1_simple_swu_iso_out'" :=((fp_t '× fp_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'g1_simple_swu_iso_out'" :=((fp_t '× fp_t
  ) : ChoiceEquality) (at level 2).
Definition G1_SIMPLE_SWU_ISO : nat :=
  2445.
Program Definition g1_simple_swu_iso (u_2439 : fp_t)
  : both (CEfset ([x1_2432_loc ; y_2433_loc])) [interface] ((fp_t '× fp_t)) :=
  ((letb z_2436 : fp_t :=
        nat_mod_from_literal (_) (lift_to_both0 (@repr U128 11)) in
      letb a_2437 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (
            lift_to_both0 g1_iso_a_v)) in
      letb b_2438 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (
            lift_to_both0 g1_iso_b_v)) in
      letb tv1_2440 : fp_t :=
        nat_mod_inv ((((lift_to_both0 z_2436) *% (lift_to_both0 z_2436)) *% (
              nat_mod_exp (lift_to_both0 u_2439) (lift_to_both0 (
                  @repr U32 4)))) +% (((lift_to_both0 z_2436) *% (
                lift_to_both0 u_2439)) *% (lift_to_both0 u_2439))) in
      letbm x1_2432 : fp_t loc( x1_2432_loc ) :=
        (((nat_mod_zero ) -% (lift_to_both0 b_2438)) *% (nat_mod_inv (
              lift_to_both0 a_2437))) *% ((nat_mod_one ) +% (
            lift_to_both0 tv1_2440)) in
      letb '(x1_2432) :=
        if (lift_to_both0 tv1_2440) =.? (nat_mod_zero ) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([x1_2432_loc])) (L2 := CEfset (
            [x1_2432_loc ; y_2433_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x1_2432 loc( x1_2432_loc ) :=
            (lift_to_both0 b_2438) *% (nat_mod_inv ((lift_to_both0 z_2436) *% (
                  lift_to_both0 a_2437))) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 x1_2432)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 x1_2432)
         in
      letb gx1_2441 : fp_t :=
        ((nat_mod_exp (lift_to_both0 x1_2432) (lift_to_both0 (
                @repr U32 3))) +% ((lift_to_both0 a_2437) *% (
              lift_to_both0 x1_2432))) +% (lift_to_both0 b_2438) in
      letb x2_2442 : fp_t :=
        (((lift_to_both0 z_2436) *% (lift_to_both0 u_2439)) *% (
            lift_to_both0 u_2439)) *% (lift_to_both0 x1_2432) in
      letb gx2_2443 : fp_t :=
        ((nat_mod_exp (lift_to_both0 x2_2442) (lift_to_both0 (
                @repr U32 3))) +% ((lift_to_both0 a_2437) *% (
              lift_to_both0 x2_2442))) +% (lift_to_both0 b_2438) in
      letb '(x_2444, y_2433) : (fp_t '× fp_t) :=
        if is_pure (I := [interface]) (fp_is_square (lift_to_both0 gx1_2441))
        then prod_b(lift_to_both0 x1_2432, fp_sqrt (lift_to_both0 gx1_2441))
        else prod_b(lift_to_both0 x2_2442, fp_sqrt (lift_to_both0 gx2_2443)) in
      letb '(y_2433) :=
        if (fp_sgn0 (lift_to_both0 u_2439)) !=.? (fp_sgn0 (
            lift_to_both0 y_2433)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([x1_2432_loc ; y_2433_loc])) (
          L2 := CEfset ([x1_2432_loc ; y_2433_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm y_2433 loc( y_2433_loc ) :=
            (nat_mod_zero ) -% (lift_to_both0 y_2433) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 y_2433)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 y_2433)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_2444,
          lift_to_both0 y_2433
        ))
      ) : both (CEfset ([x1_2432_loc ; y_2433_loc])) [interface] ((fp_t '× fp_t
      ))).
Fail Next Obligation.

Definition ynum_2454_loc : ChoiceEqualityLocation :=
  (fp_t ; 2459%nat).
Definition yden_k_2449_loc : ChoiceEqualityLocation :=
  (seq fp_t ; 2460%nat).
Definition inf_2458_loc : ChoiceEqualityLocation :=
  (bool_ChoiceEquality ; 2461%nat).
Definition xnum_k_2446_loc : ChoiceEqualityLocation :=
  (seq fp_t ; 2462%nat).
Definition yden_2456_loc : ChoiceEqualityLocation :=
  (fp_t ; 2463%nat).
Definition xden_2452_loc : ChoiceEqualityLocation :=
  (fp_t ; 2464%nat).
Definition ynum_k_2448_loc : ChoiceEqualityLocation :=
  (seq fp_t ; 2465%nat).
Definition xden_k_2447_loc : ChoiceEqualityLocation :=
  (seq fp_t ; 2466%nat).
Definition xnum_2450_loc : ChoiceEqualityLocation :=
  (fp_t ; 2467%nat).
Definition xx_2453_loc : ChoiceEqualityLocation :=
  (fp_t ; 2468%nat).
Definition xx_2457_loc : ChoiceEqualityLocation :=
  (fp_t ; 2469%nat).
Definition xx_2451_loc : ChoiceEqualityLocation :=
  (fp_t ; 2470%nat).
Definition xx_2455_loc : ChoiceEqualityLocation :=
  (fp_t ; 2471%nat).
Notation "'g1_isogeny_map_inp'" :=(
  fp_t '× fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_isogeny_map_inp'" :=(fp_t '× fp_t : ChoiceEquality) (at level 2).
Notation "'g1_isogeny_map_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_isogeny_map_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1_ISOGENY_MAP : nat :=
  2480.
Program Definition g1_isogeny_map (x_2473 : fp_t) (y_2478 : fp_t)
  : both (CEfset (
      [xnum_k_2446_loc ; xden_k_2447_loc ; ynum_k_2448_loc ; yden_k_2449_loc ; xnum_2450_loc ; xx_2451_loc ; xden_2452_loc ; xx_2453_loc ; ynum_2454_loc ; xx_2455_loc ; yden_2456_loc ; xx_2457_loc ; inf_2458_loc])) [interface] (
    g1_t) :=
  ((letbm xnum_k_2446 : seq fp_t loc( xnum_k_2446_loc ) :=
        seq_new_ (default : fp_t) (lift_to_both0 (usize 12)) in
      letb xnum_k_2446 : seq fp_t :=
        seq_upd xnum_k_2446 (lift_to_both0 (usize 0)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_0_v)))) in
      letb xnum_k_2446 : seq fp_t :=
        seq_upd xnum_k_2446 (lift_to_both0 (usize 1)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_1_v)))) in
      letb xnum_k_2446 : seq fp_t :=
        seq_upd xnum_k_2446 (lift_to_both0 (usize 2)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_2_v)))) in
      letb xnum_k_2446 : seq fp_t :=
        seq_upd xnum_k_2446 (lift_to_both0 (usize 3)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_3_v)))) in
      letb xnum_k_2446 : seq fp_t :=
        seq_upd xnum_k_2446 (lift_to_both0 (usize 4)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_4_v)))) in
      letb xnum_k_2446 : seq fp_t :=
        seq_upd xnum_k_2446 (lift_to_both0 (usize 5)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_5_v)))) in
      letb xnum_k_2446 : seq fp_t :=
        seq_upd xnum_k_2446 (lift_to_both0 (usize 6)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_6_v)))) in
      letb xnum_k_2446 : seq fp_t :=
        seq_upd xnum_k_2446 (lift_to_both0 (usize 7)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_7_v)))) in
      letb xnum_k_2446 : seq fp_t :=
        seq_upd xnum_k_2446 (lift_to_both0 (usize 8)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_8_v)))) in
      letb xnum_k_2446 : seq fp_t :=
        seq_upd xnum_k_2446 (lift_to_both0 (usize 9)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_9_v)))) in
      letb xnum_k_2446 : seq fp_t :=
        seq_upd xnum_k_2446 (lift_to_both0 (usize 10)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_10_v)))) in
      letb xnum_k_2446 : seq fp_t :=
        seq_upd xnum_k_2446 (lift_to_both0 (usize 11)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_11_v)))) in
      letbm xden_k_2447 : seq fp_t loc( xden_k_2447_loc ) :=
        seq_new_ (default : fp_t) (lift_to_both0 (usize 10)) in
      letb xden_k_2447 : seq fp_t :=
        seq_upd xden_k_2447 (lift_to_both0 (usize 0)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_0_v)))) in
      letb xden_k_2447 : seq fp_t :=
        seq_upd xden_k_2447 (lift_to_both0 (usize 1)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_1_v)))) in
      letb xden_k_2447 : seq fp_t :=
        seq_upd xden_k_2447 (lift_to_both0 (usize 2)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_2_v)))) in
      letb xden_k_2447 : seq fp_t :=
        seq_upd xden_k_2447 (lift_to_both0 (usize 3)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_3_v)))) in
      letb xden_k_2447 : seq fp_t :=
        seq_upd xden_k_2447 (lift_to_both0 (usize 4)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_4_v)))) in
      letb xden_k_2447 : seq fp_t :=
        seq_upd xden_k_2447 (lift_to_both0 (usize 5)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_5_v)))) in
      letb xden_k_2447 : seq fp_t :=
        seq_upd xden_k_2447 (lift_to_both0 (usize 6)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_6_v)))) in
      letb xden_k_2447 : seq fp_t :=
        seq_upd xden_k_2447 (lift_to_both0 (usize 7)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_7_v)))) in
      letb xden_k_2447 : seq fp_t :=
        seq_upd xden_k_2447 (lift_to_both0 (usize 8)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_8_v)))) in
      letb xden_k_2447 : seq fp_t :=
        seq_upd xden_k_2447 (lift_to_both0 (usize 9)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_9_v)))) in
      letbm ynum_k_2448 : seq fp_t loc( ynum_k_2448_loc ) :=
        seq_new_ (default : fp_t) (lift_to_both0 (usize 16)) in
      letb ynum_k_2448 : seq fp_t :=
        seq_upd ynum_k_2448 (lift_to_both0 (usize 0)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_0_v)))) in
      letb ynum_k_2448 : seq fp_t :=
        seq_upd ynum_k_2448 (lift_to_both0 (usize 1)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_1_v)))) in
      letb ynum_k_2448 : seq fp_t :=
        seq_upd ynum_k_2448 (lift_to_both0 (usize 2)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_2_v)))) in
      letb ynum_k_2448 : seq fp_t :=
        seq_upd ynum_k_2448 (lift_to_both0 (usize 3)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_3_v)))) in
      letb ynum_k_2448 : seq fp_t :=
        seq_upd ynum_k_2448 (lift_to_both0 (usize 4)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_4_v)))) in
      letb ynum_k_2448 : seq fp_t :=
        seq_upd ynum_k_2448 (lift_to_both0 (usize 5)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_5_v)))) in
      letb ynum_k_2448 : seq fp_t :=
        seq_upd ynum_k_2448 (lift_to_both0 (usize 6)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_6_v)))) in
      letb ynum_k_2448 : seq fp_t :=
        seq_upd ynum_k_2448 (lift_to_both0 (usize 7)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_7_v)))) in
      letb ynum_k_2448 : seq fp_t :=
        seq_upd ynum_k_2448 (lift_to_both0 (usize 8)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_8_v)))) in
      letb ynum_k_2448 : seq fp_t :=
        seq_upd ynum_k_2448 (lift_to_both0 (usize 9)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_9_v)))) in
      letb ynum_k_2448 : seq fp_t :=
        seq_upd ynum_k_2448 (lift_to_both0 (usize 10)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_10_v)))) in
      letb ynum_k_2448 : seq fp_t :=
        seq_upd ynum_k_2448 (lift_to_both0 (usize 11)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_11_v)))) in
      letb ynum_k_2448 : seq fp_t :=
        seq_upd ynum_k_2448 (lift_to_both0 (usize 12)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_12_v)))) in
      letb ynum_k_2448 : seq fp_t :=
        seq_upd ynum_k_2448 (lift_to_both0 (usize 13)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_13_v)))) in
      letb ynum_k_2448 : seq fp_t :=
        seq_upd ynum_k_2448 (lift_to_both0 (usize 14)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_14_v)))) in
      letb ynum_k_2448 : seq fp_t :=
        seq_upd ynum_k_2448 (lift_to_both0 (usize 15)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_15_v)))) in
      letbm yden_k_2449 : seq fp_t loc( yden_k_2449_loc ) :=
        seq_new_ (default : fp_t) (lift_to_both0 (usize 15)) in
      letb yden_k_2449 : seq fp_t :=
        seq_upd yden_k_2449 (lift_to_both0 (usize 0)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_0_v)))) in
      letb yden_k_2449 : seq fp_t :=
        seq_upd yden_k_2449 (lift_to_both0 (usize 1)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_1_v)))) in
      letb yden_k_2449 : seq fp_t :=
        seq_upd yden_k_2449 (lift_to_both0 (usize 2)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_2_v)))) in
      letb yden_k_2449 : seq fp_t :=
        seq_upd yden_k_2449 (lift_to_both0 (usize 3)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_3_v)))) in
      letb yden_k_2449 : seq fp_t :=
        seq_upd yden_k_2449 (lift_to_both0 (usize 4)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_4_v)))) in
      letb yden_k_2449 : seq fp_t :=
        seq_upd yden_k_2449 (lift_to_both0 (usize 5)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_5_v)))) in
      letb yden_k_2449 : seq fp_t :=
        seq_upd yden_k_2449 (lift_to_both0 (usize 6)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_6_v)))) in
      letb yden_k_2449 : seq fp_t :=
        seq_upd yden_k_2449 (lift_to_both0 (usize 7)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_7_v)))) in
      letb yden_k_2449 : seq fp_t :=
        seq_upd yden_k_2449 (lift_to_both0 (usize 8)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_8_v)))) in
      letb yden_k_2449 : seq fp_t :=
        seq_upd yden_k_2449 (lift_to_both0 (usize 9)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_9_v)))) in
      letb yden_k_2449 : seq fp_t :=
        seq_upd yden_k_2449 (lift_to_both0 (usize 10)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_10_v)))) in
      letb yden_k_2449 : seq fp_t :=
        seq_upd yden_k_2449 (lift_to_both0 (usize 11)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_11_v)))) in
      letb yden_k_2449 : seq fp_t :=
        seq_upd yden_k_2449 (lift_to_both0 (usize 12)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_12_v)))) in
      letb yden_k_2449 : seq fp_t :=
        seq_upd yden_k_2449 (lift_to_both0 (usize 13)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_13_v)))) in
      letb yden_k_2449 : seq fp_t :=
        seq_upd yden_k_2449 (lift_to_both0 (usize 14)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_14_v)))) in
      letbm xnum_2450 : fp_t loc( xnum_2450_loc ) := nat_mod_zero  in
      letbm xx_2451 : fp_t loc( xx_2451_loc ) := nat_mod_one  in
      letb '(xnum_2450, xx_2451) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 xnum_k_2446)) prod_ce(xnum_2450, xx_2451) (L := (
              CEfset (
                [xnum_k_2446_loc ; xden_k_2447_loc ; ynum_k_2448_loc ; yden_k_2449_loc ; xnum_2450_loc ; xx_2451_loc ; xden_2452_loc ; xx_2453_loc ; ynum_2454_loc ; xx_2455_loc ; yden_2456_loc ; xx_2457_loc ; inf_2458_loc]))) (
            I := [interface]) (fun i_2472 '(xnum_2450, xx_2451) =>
            letbm xnum_2450 loc( xnum_2450_loc ) :=
              (lift_to_both0 xnum_2450) +% ((lift_to_both0 xx_2451) *% (
                  seq_index (xnum_k_2446) (lift_to_both0 i_2472))) in
            letbm xx_2451 loc( xx_2451_loc ) :=
              (lift_to_both0 xx_2451) *% (lift_to_both0 x_2473) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 xnum_2450,
                lift_to_both0 xx_2451
              ))
            ) in
      letbm xden_2452 : fp_t loc( xden_2452_loc ) := nat_mod_zero  in
      letbm xx_2453 : fp_t loc( xx_2453_loc ) := nat_mod_one  in
      letb '(xden_2452, xx_2453) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 xden_k_2447)) prod_ce(xden_2452, xx_2453) (L := (
              CEfset (
                [xnum_k_2446_loc ; xden_k_2447_loc ; ynum_k_2448_loc ; yden_k_2449_loc ; xnum_2450_loc ; xx_2451_loc ; xden_2452_loc ; xx_2453_loc ; ynum_2454_loc ; xx_2455_loc ; yden_2456_loc ; xx_2457_loc ; inf_2458_loc]))) (
            I := [interface]) (fun i_2474 '(xden_2452, xx_2453) =>
            letbm xden_2452 loc( xden_2452_loc ) :=
              (lift_to_both0 xden_2452) +% ((lift_to_both0 xx_2453) *% (
                  seq_index (xden_k_2447) (lift_to_both0 i_2474))) in
            letbm xx_2453 loc( xx_2453_loc ) :=
              (lift_to_both0 xx_2453) *% (lift_to_both0 x_2473) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 xden_2452,
                lift_to_both0 xx_2453
              ))
            ) in
      letbm xden_2452 loc( xden_2452_loc ) :=
        (lift_to_both0 xden_2452) +% (lift_to_both0 xx_2453) in
      letbm ynum_2454 : fp_t loc( ynum_2454_loc ) := nat_mod_zero  in
      letbm xx_2455 : fp_t loc( xx_2455_loc ) := nat_mod_one  in
      letb '(ynum_2454, xx_2455) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 ynum_k_2448)) prod_ce(ynum_2454, xx_2455) (L := (
              CEfset (
                [xnum_k_2446_loc ; xden_k_2447_loc ; ynum_k_2448_loc ; yden_k_2449_loc ; xnum_2450_loc ; xx_2451_loc ; xden_2452_loc ; xx_2453_loc ; ynum_2454_loc ; xx_2455_loc ; yden_2456_loc ; xx_2457_loc ; inf_2458_loc]))) (
            I := [interface]) (fun i_2475 '(ynum_2454, xx_2455) =>
            letbm ynum_2454 loc( ynum_2454_loc ) :=
              (lift_to_both0 ynum_2454) +% ((lift_to_both0 xx_2455) *% (
                  seq_index (ynum_k_2448) (lift_to_both0 i_2475))) in
            letbm xx_2455 loc( xx_2455_loc ) :=
              (lift_to_both0 xx_2455) *% (lift_to_both0 x_2473) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 ynum_2454,
                lift_to_both0 xx_2455
              ))
            ) in
      letbm yden_2456 : fp_t loc( yden_2456_loc ) := nat_mod_zero  in
      letbm xx_2457 : fp_t loc( xx_2457_loc ) := nat_mod_one  in
      letb '(yden_2456, xx_2457) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 yden_k_2449)) prod_ce(yden_2456, xx_2457) (L := (
              CEfset (
                [xnum_k_2446_loc ; xden_k_2447_loc ; ynum_k_2448_loc ; yden_k_2449_loc ; xnum_2450_loc ; xx_2451_loc ; xden_2452_loc ; xx_2453_loc ; ynum_2454_loc ; xx_2455_loc ; yden_2456_loc ; xx_2457_loc ; inf_2458_loc]))) (
            I := [interface]) (fun i_2476 '(yden_2456, xx_2457) =>
            letbm yden_2456 loc( yden_2456_loc ) :=
              (lift_to_both0 yden_2456) +% ((lift_to_both0 xx_2457) *% (
                  seq_index (yden_k_2449) (lift_to_both0 i_2476))) in
            letbm xx_2457 loc( xx_2457_loc ) :=
              (lift_to_both0 xx_2457) *% (lift_to_both0 x_2473) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 yden_2456,
                lift_to_both0 xx_2457
              ))
            ) in
      letbm yden_2456 loc( yden_2456_loc ) :=
        (lift_to_both0 yden_2456) +% (lift_to_both0 xx_2457) in
      letb xr_2477 : fp_t :=
        (lift_to_both0 xnum_2450) *% (nat_mod_inv (lift_to_both0 xden_2452)) in
      letb yr_2479 : fp_t :=
        ((lift_to_both0 y_2478) *% (lift_to_both0 ynum_2454)) *% (nat_mod_inv (
            lift_to_both0 yden_2456)) in
      letbm inf_2458 : bool_ChoiceEquality loc( inf_2458_loc ) :=
        lift_to_both0 ((false : bool_ChoiceEquality)) in
      letb '(inf_2458) :=
        if ((lift_to_both0 xden_2452) =.? (nat_mod_zero )) || ((
            lift_to_both0 yden_2456) =.? (nat_mod_zero )) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [xnum_k_2446_loc ; xden_k_2447_loc ; ynum_k_2448_loc ; yden_k_2449_loc ; xnum_2450_loc ; xx_2451_loc ; xden_2452_loc ; xx_2453_loc ; ynum_2454_loc ; xx_2455_loc ; yden_2456_loc ; xx_2457_loc ; inf_2458_loc])) (
          L2 := CEfset (
            [xnum_k_2446_loc ; xden_k_2447_loc ; ynum_k_2448_loc ; yden_k_2449_loc ; xnum_2450_loc ; xx_2451_loc ; xden_2452_loc ; xx_2453_loc ; ynum_2454_loc ; xx_2455_loc ; yden_2456_loc ; xx_2457_loc ; inf_2458_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm inf_2458 loc( inf_2458_loc ) :=
            lift_to_both0 ((true : bool_ChoiceEquality)) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 inf_2458)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 inf_2458)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 xr_2477,
          lift_to_both0 yr_2479,
          lift_to_both0 inf_2458
        ))
      ) : both (CEfset (
        [xnum_k_2446_loc ; xden_k_2447_loc ; ynum_k_2448_loc ; yden_k_2449_loc ; xnum_2450_loc ; xx_2451_loc ; xden_2452_loc ; xx_2453_loc ; ynum_2454_loc ; xx_2455_loc ; yden_2456_loc ; xx_2457_loc ; inf_2458_loc])) [interface] (
      g1_t)).
Fail Next Obligation.


Notation "'g1_map_to_curve_sswu_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_map_to_curve_sswu_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'g1_map_to_curve_sswu_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_map_to_curve_sswu_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1_MAP_TO_CURVE_SSWU : nat :=
  2485.
Program Definition g1_map_to_curve_sswu (u_2481 : fp_t)
  : both (CEfset (
      [x1_2432_loc ; y_2433_loc ; xnum_k_2446_loc ; xden_k_2447_loc ; ynum_k_2448_loc ; yden_k_2449_loc ; xnum_2450_loc ; xx_2451_loc ; xden_2452_loc ; xx_2453_loc ; ynum_2454_loc ; xx_2455_loc ; yden_2456_loc ; xx_2457_loc ; inf_2458_loc])) [interface] (
    g1_t) :=
  ((letb '(xp_2482, yp_2483) : (fp_t '× fp_t) :=
        g1_simple_swu_iso (lift_to_both0 u_2481) in
      letb p_2484 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_isogeny_map (lift_to_both0 xp_2482) (lift_to_both0 yp_2483) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2484)
      ) : both (CEfset (
        [x1_2432_loc ; y_2433_loc ; xnum_k_2446_loc ; xden_k_2447_loc ; ynum_k_2448_loc ; yden_k_2449_loc ; xnum_2450_loc ; xx_2451_loc ; xden_2452_loc ; xx_2453_loc ; ynum_2454_loc ; xx_2455_loc ; yden_2456_loc ; xx_2457_loc ; inf_2458_loc])) [interface] (
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
  2493.
Program Definition g1_hash_to_curve_sswu (msg_2486 : byte_seq) (
    dst_2487 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2251_loc ; b_i_2252_loc ; uniform_bytes_2253_loc ; output_2268_loc ; x1_2432_loc ; y_2433_loc ; xnum_k_2446_loc ; xden_k_2447_loc ; ynum_k_2448_loc ; yden_k_2449_loc ; xnum_2450_loc ; xx_2451_loc ; xden_2452_loc ; xx_2453_loc ; ynum_2454_loc ; xx_2455_loc ; yden_2456_loc ; xx_2457_loc ; inf_2458_loc])) [interface] (
    g1_t) :=
  ((letb u_2488 : seq fp_t :=
        fp_hash_to_field (lift_to_both0 msg_2486) (lift_to_both0 dst_2487) (
          lift_to_both0 (usize 2)) in
      letb q0_2489 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_map_to_curve_sswu (seq_index (u_2488) (lift_to_both0 (usize 0))) in
      letb q1_2490 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_map_to_curve_sswu (seq_index (u_2488) (lift_to_both0 (usize 1))) in
      letb r_2491 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1add (lift_to_both0 q0_2489) (lift_to_both0 q1_2490) in
      letb p_2492 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_clear_cofactor (lift_to_both0 r_2491) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2492)
      ) : both (CEfset (
        [l_i_b_str_2251_loc ; b_i_2252_loc ; uniform_bytes_2253_loc ; output_2268_loc ; x1_2432_loc ; y_2433_loc ; xnum_k_2446_loc ; xden_k_2447_loc ; ynum_k_2448_loc ; yden_k_2449_loc ; xnum_2450_loc ; xx_2451_loc ; xden_2452_loc ; xx_2453_loc ; ynum_2454_loc ; xx_2455_loc ; yden_2456_loc ; xx_2457_loc ; inf_2458_loc])) [interface] (
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
  2499.
Program Definition g1_encode_to_curve_sswu (msg_2494 : byte_seq) (
    dst_2495 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2251_loc ; b_i_2252_loc ; uniform_bytes_2253_loc ; output_2268_loc ; x1_2432_loc ; y_2433_loc ; xnum_k_2446_loc ; xden_k_2447_loc ; ynum_k_2448_loc ; yden_k_2449_loc ; xnum_2450_loc ; xx_2451_loc ; xden_2452_loc ; xx_2453_loc ; ynum_2454_loc ; xx_2455_loc ; yden_2456_loc ; xx_2457_loc ; inf_2458_loc])) [interface] (
    g1_t) :=
  ((letb u_2496 : seq fp_t :=
        fp_hash_to_field (lift_to_both0 msg_2494) (lift_to_both0 dst_2495) (
          lift_to_both0 (usize 1)) in
      letb q_2497 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_map_to_curve_sswu (seq_index (u_2496) (lift_to_both0 (usize 0))) in
      letb p_2498 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_clear_cofactor (lift_to_both0 q_2497) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2498)
      ) : both (CEfset (
        [l_i_b_str_2251_loc ; b_i_2252_loc ; uniform_bytes_2253_loc ; output_2268_loc ; x1_2432_loc ; y_2433_loc ; xnum_k_2446_loc ; xden_k_2447_loc ; ynum_k_2448_loc ; yden_k_2449_loc ; xnum_2450_loc ; xx_2451_loc ; xden_2452_loc ; xx_2453_loc ; ynum_2454_loc ; xx_2455_loc ; yden_2456_loc ; xx_2457_loc ; inf_2458_loc])) [interface] (
      g1_t)).
Fail Next Obligation.

Definition g2_xnum_k_0_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 416399692810564414)) : uint64;
    (secret (@repr U64 13500519111022079365)) : uint64;
    (secret (@repr U64 3658379999393219626)) : uint64;
    (secret (@repr U64 9850925049107374429)) : uint64;
    (secret (@repr U64 6640057249351452444)) : uint64;
    (secret (@repr U64 7077594464397203414)) : uint64
  ].

Definition g2_xnum_k_1_i_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1249199078431693244)) : uint64;
    (secret (@repr U64 3608069185647134863)) : uint64;
    (secret (@repr U64 10975139998179658879)) : uint64;
    (secret (@repr U64 11106031073612571672)) : uint64;
    (secret (@repr U64 1473427674344805717)) : uint64;
    (secret (@repr U64 2786039319482058522)) : uint64
  ].

Definition g2_xnum_k_2_r_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1249199078431693244)) : uint64;
    (secret (@repr U64 3608069185647134863)) : uint64;
    (secret (@repr U64 10975139998179658879)) : uint64;
    (secret (@repr U64 11106031073612571672)) : uint64;
    (secret (@repr U64 1473427674344805717)) : uint64;
    (secret (@repr U64 2786039319482058526)) : uint64
  ].

Definition g2_xnum_k_2_i_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 624599539215846622)) : uint64;
    (secret (@repr U64 1804034592823567431)) : uint64;
    (secret (@repr U64 14710942035944605247)) : uint64;
    (secret (@repr U64 14776387573661061644)) : uint64;
    (secret (@repr U64 736713837172402858)) : uint64;
    (secret (@repr U64 10616391696595805069)) : uint64
  ].

Definition g2_xnum_k_3_r_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1665598771242257658)) : uint64;
    (secret (@repr U64 17108588296669214228)) : uint64;
    (secret (@repr U64 14633519997572878506)) : uint64;
    (secret (@repr U64 2510212049010394485)) : uint64;
    (secret (@repr U64 8113484923696258161)) : uint64;
    (secret (@repr U64 9863633783879261905)) : uint64
  ].

Definition g2_xden_k_0_i_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1873798617647539866)) : uint64;
    (secret (@repr U64 5412103778470702295)) : uint64;
    (secret (@repr U64 7239337960414712511)) : uint64;
    (secret (@repr U64 7435674573564081700)) : uint64;
    (secret (@repr U64 2210141511517208575)) : uint64;
    (secret (@repr U64 13402431016077863523)) : uint64
  ].

Definition g2_xden_k_1_i_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1873798617647539866)) : uint64;
    (secret (@repr U64 5412103778470702295)) : uint64;
    (secret (@repr U64 7239337960414712511)) : uint64;
    (secret (@repr U64 7435674573564081700)) : uint64;
    (secret (@repr U64 2210141511517208575)) : uint64;
    (secret (@repr U64 13402431016077863583)) : uint64
  ].

Definition g2_ynum_k_0_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1526798873638736187)) : uint64;
    (secret (@repr U64 6459500568425337235)) : uint64;
    (secret (@repr U64 1116230615302104219)) : uint64;
    (secret (@repr U64 17673314439684154624)) : uint64;
    (secret (@repr U64 18197961889718808424)) : uint64;
    (secret (@repr U64 1355520937843676934)) : uint64
  ].

Definition g2_ynum_k_1_i_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 416399692810564414)) : uint64;
    (secret (@repr U64 13500519111022079365)) : uint64;
    (secret (@repr U64 3658379999393219626)) : uint64;
    (secret (@repr U64 9850925049107374429)) : uint64;
    (secret (@repr U64 6640057249351452444)) : uint64;
    (secret (@repr U64 7077594464397203390)) : uint64
  ].

Definition g2_ynum_k_2_r_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1249199078431693244)) : uint64;
    (secret (@repr U64 3608069185647134863)) : uint64;
    (secret (@repr U64 10975139998179658879)) : uint64;
    (secret (@repr U64 11106031073612571672)) : uint64;
    (secret (@repr U64 1473427674344805717)) : uint64;
    (secret (@repr U64 2786039319482058524)) : uint64
  ].

Definition g2_ynum_k_2_i_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 624599539215846622)) : uint64;
    (secret (@repr U64 1804034592823567431)) : uint64;
    (secret (@repr U64 14710942035944605247)) : uint64;
    (secret (@repr U64 14776387573661061644)) : uint64;
    (secret (@repr U64 736713837172402858)) : uint64;
    (secret (@repr U64 10616391696595805071)) : uint64
  ].

Definition g2_ynum_k_3_r_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1318599027233453979)) : uint64;
    (secret (@repr U64 18155985086623849168)) : uint64;
    (secret (@repr U64 8510412652460270214)) : uint64;
    (secret (@repr U64 12747851915130467410)) : uint64;
    (secret (@repr U64 5654561228188306393)) : uint64;
    (secret (@repr U64 16263467779354626832)) : uint64
  ].

Definition g2_yden_k_0_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1873798617647539866)) : uint64;
    (secret (@repr U64 5412103778470702295)) : uint64;
    (secret (@repr U64 7239337960414712511)) : uint64;
    (secret (@repr U64 7435674573564081700)) : uint64;
    (secret (@repr U64 2210141511517208575)) : uint64;
    (secret (@repr U64 13402431016077863163)) : uint64
  ].

Definition g2_yden_k_1_i_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1873798617647539866)) : uint64;
    (secret (@repr U64 5412103778470702295)) : uint64;
    (secret (@repr U64 7239337960414712511)) : uint64;
    (secret (@repr U64 7435674573564081700)) : uint64;
    (secret (@repr U64 2210141511517208575)) : uint64;
    (secret (@repr U64 13402431016077863379)) : uint64
  ].

Definition g2_yden_k_2_i_v : arr_fp_t :=
  array_from_list uint64 [
    (secret (@repr U64 1873798617647539866)) : uint64;
    (secret (@repr U64 5412103778470702295)) : uint64;
    (secret (@repr U64 7239337960414712511)) : uint64;
    (secret (@repr U64 7435674573564081700)) : uint64;
    (secret (@repr U64 2210141511517208575)) : uint64;
    (secret (@repr U64 13402431016077863577)) : uint64
  ].

Definition y_2501_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2502%nat).
Definition x1_2500_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2503%nat).
Notation "'g2_simple_swu_iso_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_simple_swu_iso_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'g2_simple_swu_iso_out'" :=((fp2_t '× fp2_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'g2_simple_swu_iso_out'" :=((fp2_t '× fp2_t
  ) : ChoiceEquality) (at level 2).
Definition G2_SIMPLE_SWU_ISO : nat :=
  2513.
Program Definition g2_simple_swu_iso (u_2507 : fp2_t)
  : both (CEfset ([c_2358_loc ; x1_2500_loc ; y_2501_loc])) [interface] ((
      fp2_t '×
      fp2_t
    )) :=
  ((letb z_2504 : (fp_t '× fp_t) :=
        fp2neg (prod_b(nat_mod_two , nat_mod_one )) in
      letb a_2505 : (fp_t '× fp_t) :=
        prod_b(
          nat_mod_zero ,
          nat_mod_from_literal (_) (lift_to_both0 (@repr U128 240))
        ) in
      letb b_2506 : (fp_t '× fp_t) :=
        prod_b(
          nat_mod_from_literal (_) (lift_to_both0 (@repr U128 1012)),
          nat_mod_from_literal (_) (lift_to_both0 (@repr U128 1012))
        ) in
      letb tv1_2508 : (fp_t '× fp_t) :=
        fp2inv (fp2add (fp2mul (fp2mul (lift_to_both0 z_2504) (
                lift_to_both0 z_2504)) (fp2mul (fp2mul (lift_to_both0 u_2507) (
                  lift_to_both0 u_2507)) (fp2mul (lift_to_both0 u_2507) (
                  lift_to_both0 u_2507)))) (fp2mul (lift_to_both0 z_2504) (
              fp2mul (lift_to_both0 u_2507) (lift_to_both0 u_2507)))) in
      letbm x1_2500 : (fp_t '× fp_t) loc( x1_2500_loc ) :=
        fp2mul (fp2mul (fp2neg (lift_to_both0 b_2506)) (fp2inv (
              lift_to_both0 a_2505))) (fp2add (fp2fromfp (nat_mod_one )) (
            lift_to_both0 tv1_2508)) in
      letb '(x1_2500) :=
        if (lift_to_both0 tv1_2508) =.? (fp2zero ) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([x1_2500_loc])) (L2 := CEfset (
            [c_2358_loc ; x1_2500_loc ; y_2501_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x1_2500 loc( x1_2500_loc ) :=
            fp2mul (lift_to_both0 b_2506) (fp2inv (fp2mul (
                  lift_to_both0 z_2504) (lift_to_both0 a_2505))) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 x1_2500)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 x1_2500)
         in
      letb gx1_2509 : (fp_t '× fp_t) :=
        fp2add (fp2add (fp2mul (fp2mul (lift_to_both0 x1_2500) (
                lift_to_both0 x1_2500)) (lift_to_both0 x1_2500)) (fp2mul (
              lift_to_both0 a_2505) (lift_to_both0 x1_2500))) (
          lift_to_both0 b_2506) in
      letb x2_2510 : (fp_t '× fp_t) :=
        fp2mul (fp2mul (lift_to_both0 z_2504) (fp2mul (lift_to_both0 u_2507) (
              lift_to_both0 u_2507))) (lift_to_both0 x1_2500) in
      letb gx2_2511 : (fp_t '× fp_t) :=
        fp2add (fp2add (fp2mul (fp2mul (lift_to_both0 x2_2510) (
                lift_to_both0 x2_2510)) (lift_to_both0 x2_2510)) (fp2mul (
              lift_to_both0 a_2505) (lift_to_both0 x2_2510))) (
          lift_to_both0 b_2506) in
      letb '(x_2512, y_2501) : ((fp_t '× fp_t) '× fp2_t) :=
        if is_pure (I := [interface]) (fp2_is_square (lift_to_both0 gx1_2509))
        then prod_b(lift_to_both0 x1_2500, fp2_sqrt (lift_to_both0 gx1_2509))
        else prod_b(lift_to_both0 x2_2510, fp2_sqrt (lift_to_both0 gx2_2511)) in
      letb '(y_2501) :=
        if (fp2_sgn0 (lift_to_both0 u_2507)) !=.? (fp2_sgn0 (
            lift_to_both0 y_2501)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [c_2358_loc ; x1_2500_loc ; y_2501_loc])) (L2 := CEfset (
            [c_2358_loc ; x1_2500_loc ; y_2501_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm y_2501 loc( y_2501_loc ) := fp2neg (lift_to_both0 y_2501) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 y_2501)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 y_2501)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_2512,
          lift_to_both0 y_2501
        ))
      ) : both (CEfset ([c_2358_loc ; x1_2500_loc ; y_2501_loc])) [interface] ((
        fp2_t '×
        fp2_t
      ))).
Fail Next Obligation.

Definition xnum_k_2514_loc : ChoiceEqualityLocation :=
  (seq (fp_t '× fp_t) ; 2527%nat).
Definition yden_k_2517_loc : ChoiceEqualityLocation :=
  (seq (fp_t '× fp_t) ; 2528%nat).
Definition xx_2519_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2529%nat).
Definition xden_2520_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2530%nat).
Definition xx_2523_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2531%nat).
Definition ynum_2522_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2532%nat).
Definition inf_2526_loc : ChoiceEqualityLocation :=
  (bool_ChoiceEquality ; 2533%nat).
Definition xx_2525_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2534%nat).
Definition ynum_k_2516_loc : ChoiceEqualityLocation :=
  (seq (fp_t '× fp_t) ; 2535%nat).
Definition xden_k_2515_loc : ChoiceEqualityLocation :=
  (seq (fp_t '× fp_t) ; 2536%nat).
Definition xx_2521_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2537%nat).
Definition yden_2524_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2538%nat).
Definition xnum_2518_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2539%nat).
Notation "'g2_isogeny_map_inp'" :=(
  fp2_t '× fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_isogeny_map_inp'" :=(
  fp2_t '× fp2_t : ChoiceEquality) (at level 2).
Notation "'g2_isogeny_map_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_isogeny_map_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_ISOGENY_MAP : nat :=
  2548.
Program Definition g2_isogeny_map (x_2541 : fp2_t) (y_2546 : fp2_t)
  : both (CEfset (
      [xnum_k_2514_loc ; xden_k_2515_loc ; ynum_k_2516_loc ; yden_k_2517_loc ; xnum_2518_loc ; xx_2519_loc ; xden_2520_loc ; xx_2521_loc ; ynum_2522_loc ; xx_2523_loc ; yden_2524_loc ; xx_2525_loc ; inf_2526_loc])) [interface] (
    g2_t) :=
  ((letbm xnum_k_2514 : seq (fp_t '× fp_t) loc( xnum_k_2514_loc ) :=
        seq_new_ (default : fp2_t) (lift_to_both0 (usize 4)) in
      letb xnum_k_2514 : seq (fp_t '× fp_t) :=
        seq_upd xnum_k_2514 (lift_to_both0 (usize 0)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xnum_k_0_v)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xnum_k_0_v))
            ))) in
      letb xnum_k_2514 : seq (fp_t '× fp_t) :=
        seq_upd xnum_k_2514 (lift_to_both0 (usize 1)) (is_pure (prod_b(
              nat_mod_zero ,
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xnum_k_1_i_v))
            ))) in
      letb xnum_k_2514 : seq (fp_t '× fp_t) :=
        seq_upd xnum_k_2514 (lift_to_both0 (usize 2)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xnum_k_2_r_v)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xnum_k_2_i_v))
            ))) in
      letb xnum_k_2514 : seq (fp_t '× fp_t) :=
        seq_upd xnum_k_2514 (lift_to_both0 (usize 3)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xnum_k_3_r_v)),
              nat_mod_zero 
            ))) in
      letbm xden_k_2515 : seq (fp_t '× fp_t) loc( xden_k_2515_loc ) :=
        seq_new_ (default : fp2_t) (lift_to_both0 (usize 2)) in
      letb xden_k_2515 : seq (fp_t '× fp_t) :=
        seq_upd xden_k_2515 (lift_to_both0 (usize 0)) (is_pure (prod_b(
              nat_mod_zero ,
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xden_k_0_i_v))
            ))) in
      letb xden_k_2515 : seq (fp_t '× fp_t) :=
        seq_upd xden_k_2515 (lift_to_both0 (usize 1)) (is_pure (prod_b(
              nat_mod_from_literal (_) (lift_to_both0 (@repr U128 12)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xden_k_1_i_v))
            ))) in
      letbm ynum_k_2516 : seq (fp_t '× fp_t) loc( ynum_k_2516_loc ) :=
        seq_new_ (default : fp2_t) (lift_to_both0 (usize 4)) in
      letb ynum_k_2516 : seq (fp_t '× fp_t) :=
        seq_upd ynum_k_2516 (lift_to_both0 (usize 0)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_ynum_k_0_v)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_ynum_k_0_v))
            ))) in
      letb ynum_k_2516 : seq (fp_t '× fp_t) :=
        seq_upd ynum_k_2516 (lift_to_both0 (usize 1)) (is_pure (prod_b(
              nat_mod_zero ,
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_ynum_k_1_i_v))
            ))) in
      letb ynum_k_2516 : seq (fp_t '× fp_t) :=
        seq_upd ynum_k_2516 (lift_to_both0 (usize 2)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_ynum_k_2_r_v)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_ynum_k_2_i_v))
            ))) in
      letb ynum_k_2516 : seq (fp_t '× fp_t) :=
        seq_upd ynum_k_2516 (lift_to_both0 (usize 3)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_ynum_k_3_r_v)),
              nat_mod_zero 
            ))) in
      letbm yden_k_2517 : seq (fp_t '× fp_t) loc( yden_k_2517_loc ) :=
        seq_new_ (default : fp2_t) (lift_to_both0 (usize 3)) in
      letb yden_k_2517 : seq (fp_t '× fp_t) :=
        seq_upd yden_k_2517 (lift_to_both0 (usize 0)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_yden_k_0_v)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_yden_k_0_v))
            ))) in
      letb yden_k_2517 : seq (fp_t '× fp_t) :=
        seq_upd yden_k_2517 (lift_to_both0 (usize 1)) (is_pure (prod_b(
              nat_mod_zero ,
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_yden_k_1_i_v))
            ))) in
      letb yden_k_2517 : seq (fp_t '× fp_t) :=
        seq_upd yden_k_2517 (lift_to_both0 (usize 2)) (is_pure (prod_b(
              nat_mod_from_literal (_) (lift_to_both0 (@repr U128 18)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_yden_k_2_i_v))
            ))) in
      letbm xnum_2518 : (fp_t '× fp_t) loc( xnum_2518_loc ) := fp2zero  in
      letbm xx_2519 : (fp_t '× fp_t) loc( xx_2519_loc ) :=
        fp2fromfp (nat_mod_one ) in
      letb '(xnum_2518, xx_2519) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 xnum_k_2514)) prod_ce(xnum_2518, xx_2519) (L := (
              CEfset (
                [xnum_k_2514_loc ; xden_k_2515_loc ; ynum_k_2516_loc ; yden_k_2517_loc ; xnum_2518_loc ; xx_2519_loc ; xden_2520_loc ; xx_2521_loc ; ynum_2522_loc ; xx_2523_loc ; yden_2524_loc ; xx_2525_loc ; inf_2526_loc]))) (
            I := [interface]) (fun i_2540 '(xnum_2518, xx_2519) =>
            letbm xnum_2518 loc( xnum_2518_loc ) :=
              fp2add (lift_to_both0 xnum_2518) (fp2mul (lift_to_both0 xx_2519) (
                  seq_index (xnum_k_2514) (lift_to_both0 i_2540))) in
            letbm xx_2519 loc( xx_2519_loc ) :=
              fp2mul (lift_to_both0 xx_2519) (lift_to_both0 x_2541) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 xnum_2518,
                lift_to_both0 xx_2519
              ))
            ) in
      letbm xden_2520 : (fp_t '× fp_t) loc( xden_2520_loc ) := fp2zero  in
      letbm xx_2521 : (fp_t '× fp_t) loc( xx_2521_loc ) :=
        fp2fromfp (nat_mod_one ) in
      letb '(xden_2520, xx_2521) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 xden_k_2515)) prod_ce(xden_2520, xx_2521) (L := (
              CEfset (
                [xnum_k_2514_loc ; xden_k_2515_loc ; ynum_k_2516_loc ; yden_k_2517_loc ; xnum_2518_loc ; xx_2519_loc ; xden_2520_loc ; xx_2521_loc ; ynum_2522_loc ; xx_2523_loc ; yden_2524_loc ; xx_2525_loc ; inf_2526_loc]))) (
            I := [interface]) (fun i_2542 '(xden_2520, xx_2521) =>
            letbm xden_2520 loc( xden_2520_loc ) :=
              fp2add (lift_to_both0 xden_2520) (fp2mul (lift_to_both0 xx_2521) (
                  seq_index (xden_k_2515) (lift_to_both0 i_2542))) in
            letbm xx_2521 loc( xx_2521_loc ) :=
              fp2mul (lift_to_both0 xx_2521) (lift_to_both0 x_2541) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 xden_2520,
                lift_to_both0 xx_2521
              ))
            ) in
      letbm xden_2520 loc( xden_2520_loc ) :=
        fp2add (lift_to_both0 xden_2520) (lift_to_both0 xx_2521) in
      letbm ynum_2522 : (fp_t '× fp_t) loc( ynum_2522_loc ) := fp2zero  in
      letbm xx_2523 : (fp_t '× fp_t) loc( xx_2523_loc ) :=
        fp2fromfp (nat_mod_one ) in
      letb '(ynum_2522, xx_2523) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 ynum_k_2516)) prod_ce(ynum_2522, xx_2523) (L := (
              CEfset (
                [xnum_k_2514_loc ; xden_k_2515_loc ; ynum_k_2516_loc ; yden_k_2517_loc ; xnum_2518_loc ; xx_2519_loc ; xden_2520_loc ; xx_2521_loc ; ynum_2522_loc ; xx_2523_loc ; yden_2524_loc ; xx_2525_loc ; inf_2526_loc]))) (
            I := [interface]) (fun i_2543 '(ynum_2522, xx_2523) =>
            letbm ynum_2522 loc( ynum_2522_loc ) :=
              fp2add (lift_to_both0 ynum_2522) (fp2mul (lift_to_both0 xx_2523) (
                  seq_index (ynum_k_2516) (lift_to_both0 i_2543))) in
            letbm xx_2523 loc( xx_2523_loc ) :=
              fp2mul (lift_to_both0 xx_2523) (lift_to_both0 x_2541) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 ynum_2522,
                lift_to_both0 xx_2523
              ))
            ) in
      letbm yden_2524 : (fp_t '× fp_t) loc( yden_2524_loc ) := fp2zero  in
      letbm xx_2525 : (fp_t '× fp_t) loc( xx_2525_loc ) :=
        fp2fromfp (nat_mod_one ) in
      letb '(yden_2524, xx_2525) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 yden_k_2517)) prod_ce(yden_2524, xx_2525) (L := (
              CEfset (
                [xnum_k_2514_loc ; xden_k_2515_loc ; ynum_k_2516_loc ; yden_k_2517_loc ; xnum_2518_loc ; xx_2519_loc ; xden_2520_loc ; xx_2521_loc ; ynum_2522_loc ; xx_2523_loc ; yden_2524_loc ; xx_2525_loc ; inf_2526_loc]))) (
            I := [interface]) (fun i_2544 '(yden_2524, xx_2525) =>
            letbm yden_2524 loc( yden_2524_loc ) :=
              fp2add (lift_to_both0 yden_2524) (fp2mul (lift_to_both0 xx_2525) (
                  seq_index (yden_k_2517) (lift_to_both0 i_2544))) in
            letbm xx_2525 loc( xx_2525_loc ) :=
              fp2mul (lift_to_both0 xx_2525) (lift_to_both0 x_2541) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 yden_2524,
                lift_to_both0 xx_2525
              ))
            ) in
      letbm yden_2524 loc( yden_2524_loc ) :=
        fp2add (lift_to_both0 yden_2524) (lift_to_both0 xx_2525) in
      letb xr_2545 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 xnum_2518) (fp2inv (lift_to_both0 xden_2520)) in
      letb yr_2547 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 y_2546) (fp2mul (lift_to_both0 ynum_2522) (
            fp2inv (lift_to_both0 yden_2524))) in
      letbm inf_2526 : bool_ChoiceEquality loc( inf_2526_loc ) :=
        lift_to_both0 ((false : bool_ChoiceEquality)) in
      letb '(inf_2526) :=
        if ((lift_to_both0 xden_2520) =.? (fp2zero )) || ((
            lift_to_both0 yden_2524) =.? (fp2zero )) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [xnum_k_2514_loc ; xden_k_2515_loc ; ynum_k_2516_loc ; yden_k_2517_loc ; xnum_2518_loc ; xx_2519_loc ; xden_2520_loc ; xx_2521_loc ; ynum_2522_loc ; xx_2523_loc ; yden_2524_loc ; xx_2525_loc ; inf_2526_loc])) (
          L2 := CEfset (
            [xnum_k_2514_loc ; xden_k_2515_loc ; ynum_k_2516_loc ; yden_k_2517_loc ; xnum_2518_loc ; xx_2519_loc ; xden_2520_loc ; xx_2521_loc ; ynum_2522_loc ; xx_2523_loc ; yden_2524_loc ; xx_2525_loc ; inf_2526_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm inf_2526 loc( inf_2526_loc ) :=
            lift_to_both0 ((true : bool_ChoiceEquality)) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 inf_2526)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 inf_2526)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 xr_2545,
          lift_to_both0 yr_2547,
          lift_to_both0 inf_2526
        ))
      ) : both (CEfset (
        [xnum_k_2514_loc ; xden_k_2515_loc ; ynum_k_2516_loc ; yden_k_2517_loc ; xnum_2518_loc ; xx_2519_loc ; xden_2520_loc ; xx_2521_loc ; ynum_2522_loc ; xx_2523_loc ; yden_2524_loc ; xx_2525_loc ; inf_2526_loc])) [interface] (
      g2_t)).
Fail Next Obligation.


Notation "'g2_map_to_curve_sswu_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_map_to_curve_sswu_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'g2_map_to_curve_sswu_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_map_to_curve_sswu_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_MAP_TO_CURVE_SSWU : nat :=
  2553.
Program Definition g2_map_to_curve_sswu (u_2549 : fp2_t)
  : both (CEfset (
      [c_2358_loc ; x1_2500_loc ; y_2501_loc ; xnum_k_2514_loc ; xden_k_2515_loc ; ynum_k_2516_loc ; yden_k_2517_loc ; xnum_2518_loc ; xx_2519_loc ; xden_2520_loc ; xx_2521_loc ; ynum_2522_loc ; xx_2523_loc ; yden_2524_loc ; xx_2525_loc ; inf_2526_loc])) [interface] (
    g2_t) :=
  ((letb '(xp_2550, yp_2551) : (fp2_t '× fp2_t) :=
        g2_simple_swu_iso (lift_to_both0 u_2549) in
      letb p_2552 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_isogeny_map (lift_to_both0 xp_2550) (lift_to_both0 yp_2551) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2552)
      ) : both (CEfset (
        [c_2358_loc ; x1_2500_loc ; y_2501_loc ; xnum_k_2514_loc ; xden_k_2515_loc ; ynum_k_2516_loc ; yden_k_2517_loc ; xnum_2518_loc ; xx_2519_loc ; xden_2520_loc ; xx_2521_loc ; ynum_2522_loc ; xx_2523_loc ; yden_2524_loc ; xx_2525_loc ; inf_2526_loc])) [interface] (
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
  2561.
Program Definition g2_hash_to_curve_sswu (msg_2554 : byte_seq) (
    dst_2555 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2251_loc ; b_i_2252_loc ; uniform_bytes_2253_loc ; output_2326_loc ; c_2358_loc ; x1_2500_loc ; y_2501_loc ; xnum_k_2514_loc ; xden_k_2515_loc ; ynum_k_2516_loc ; yden_k_2517_loc ; xnum_2518_loc ; xx_2519_loc ; xden_2520_loc ; xx_2521_loc ; ynum_2522_loc ; xx_2523_loc ; yden_2524_loc ; xx_2525_loc ; inf_2526_loc])) [interface] (
    g2_t) :=
  ((letb u_2556 : seq fp2_t :=
        fp2_hash_to_field (lift_to_both0 msg_2554) (lift_to_both0 dst_2555) (
          lift_to_both0 (usize 2)) in
      letb q0_2557 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2_map_to_curve_sswu (seq_index (u_2556) (lift_to_both0 (usize 0))) in
      letb q1_2558 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2_map_to_curve_sswu (seq_index (u_2556) (lift_to_both0 (usize 1))) in
      letb r_2559 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 q0_2557) (lift_to_both0 q1_2558) in
      letb p_2560 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_clear_cofactor (lift_to_both0 r_2559) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2560)
      ) : both (CEfset (
        [l_i_b_str_2251_loc ; b_i_2252_loc ; uniform_bytes_2253_loc ; output_2326_loc ; c_2358_loc ; x1_2500_loc ; y_2501_loc ; xnum_k_2514_loc ; xden_k_2515_loc ; ynum_k_2516_loc ; yden_k_2517_loc ; xnum_2518_loc ; xx_2519_loc ; xden_2520_loc ; xx_2521_loc ; ynum_2522_loc ; xx_2523_loc ; yden_2524_loc ; xx_2525_loc ; inf_2526_loc])) [interface] (
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
  2567.
Program Definition g2_encode_to_curve_sswu (msg_2562 : byte_seq) (
    dst_2563 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2251_loc ; b_i_2252_loc ; uniform_bytes_2253_loc ; output_2326_loc ; c_2358_loc ; x1_2500_loc ; y_2501_loc ; xnum_k_2514_loc ; xden_k_2515_loc ; ynum_k_2516_loc ; yden_k_2517_loc ; xnum_2518_loc ; xx_2519_loc ; xden_2520_loc ; xx_2521_loc ; ynum_2522_loc ; xx_2523_loc ; yden_2524_loc ; xx_2525_loc ; inf_2526_loc])) [interface] (
    g2_t) :=
  ((letb u_2564 : seq fp2_t :=
        fp2_hash_to_field (lift_to_both0 msg_2562) (lift_to_both0 dst_2563) (
          lift_to_both0 (usize 1)) in
      letb q_2565 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_map_to_curve_sswu (seq_index (u_2564) (lift_to_both0 (usize 0))) in
      letb p_2566 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_clear_cofactor (lift_to_both0 q_2565) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2566)
      ) : both (CEfset (
        [l_i_b_str_2251_loc ; b_i_2252_loc ; uniform_bytes_2253_loc ; output_2326_loc ; c_2358_loc ; x1_2500_loc ; y_2501_loc ; xnum_k_2514_loc ; xden_k_2515_loc ; ynum_k_2516_loc ; yden_k_2517_loc ; xnum_2518_loc ; xx_2519_loc ; xden_2520_loc ; xx_2521_loc ; ynum_2522_loc ; xx_2523_loc ; yden_2524_loc ; xx_2525_loc ; inf_2526_loc])) [interface] (
      g2_t)).
Fail Next Obligation.

