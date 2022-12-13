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

Definition b_i_2202_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2204%nat).
Definition uniform_bytes_2203_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2205%nat).
Definition l_i_b_str_2201_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2206%nat).
Notation "'expand_message_xmd_inp'" :=(
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'expand_message_xmd_inp'" :=(
  byte_seq '× byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'expand_message_xmd_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'expand_message_xmd_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition EXPAND_MESSAGE_XMD : nat :=
  2217.
Program Definition expand_message_xmd (msg_2212 : byte_seq) (
    dst_2209 : byte_seq) (len_in_bytes_2207 : uint_size)
  : both (CEfset (
      [l_i_b_str_2201_loc ; b_i_2202_loc ; uniform_bytes_2203_loc])) [interface] (
    byte_seq) :=
  ((letb ell_2208 : uint_size :=
        (((lift_to_both0 len_in_bytes_2207) .+ (
              lift_to_both0 b_in_bytes_v)) .- (lift_to_both0 (usize 1))) ./ (
          lift_to_both0 b_in_bytes_v) in
      letb dst_prime_2210 : seq uint8 :=
        seq_push (lift_to_both0 dst_2209) (uint8_from_usize (seq_len (
              lift_to_both0 dst_2209))) in
      letb z_pad_2211 : seq uint8 :=
        seq_new_ (default : uint8) (lift_to_both0 s_in_bytes_v) in
      letbm l_i_b_str_2201 : seq uint8 loc( l_i_b_str_2201_loc ) :=
        seq_new_ (default : uint8) (lift_to_both0 (usize 2)) in
      letb l_i_b_str_2201 : seq uint8 :=
        seq_upd l_i_b_str_2201 (lift_to_both0 (usize 0)) (is_pure (
            uint8_from_usize ((lift_to_both0 len_in_bytes_2207) ./ (
                lift_to_both0 (usize 256))))) in
      letb l_i_b_str_2201 : seq uint8 :=
        seq_upd l_i_b_str_2201 (lift_to_both0 (usize 1)) (is_pure (
            uint8_from_usize (lift_to_both0 len_in_bytes_2207))) in
      letb msg_prime_2213 : seq uint8 :=
        seq_concat (seq_concat (seq_concat (seq_concat (
                lift_to_both0 z_pad_2211) (lift_to_both0 msg_2212)) (
              lift_to_both0 l_i_b_str_2201)) (seq_new_ (default : uint8) (
              lift_to_both0 (usize 1)))) (lift_to_both0 dst_prime_2210) in
      letb b_0_2214 : seq uint8 :=
        seq_from_seq (array_to_seq (hash (lift_to_both0 msg_prime_2213))) in
      letbm b_i_2202 : seq uint8 loc( b_i_2202_loc ) :=
        seq_from_seq (array_to_seq (hash (seq_concat (seq_push (
                lift_to_both0 b_0_2214) (secret (lift_to_both0 (@repr U8 1)))) (
              lift_to_both0 dst_prime_2210)))) in
      letbm uniform_bytes_2203 : seq uint8 loc( uniform_bytes_2203_loc ) :=
        seq_from_seq (lift_to_both0 b_i_2202) in
      letb '(b_i_2202, uniform_bytes_2203) :=
        foldi_both' (lift_to_both0 (usize 2)) ((lift_to_both0 ell_2208) .+ (
              lift_to_both0 (usize 1))) prod_ce(b_i_2202, uniform_bytes_2203) (
            L := (CEfset (
                [l_i_b_str_2201_loc ; b_i_2202_loc ; uniform_bytes_2203_loc]))) (
            I := [interface]) (fun i_2215 '(b_i_2202, uniform_bytes_2203) =>
            letb t_2216 : seq uint8 := seq_from_seq (lift_to_both0 b_0_2214) in
            letbm b_i_2202 loc( b_i_2202_loc ) :=
              seq_from_seq (array_to_seq (hash (seq_concat (seq_push ((
                        lift_to_both0 t_2216) seq_xor (
                        lift_to_both0 b_i_2202)) (uint8_from_usize (
                        lift_to_both0 i_2215))) (
                    lift_to_both0 dst_prime_2210)))) in
            letbm uniform_bytes_2203 loc( uniform_bytes_2203_loc ) :=
              seq_concat (lift_to_both0 uniform_bytes_2203) (
                lift_to_both0 b_i_2202) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 b_i_2202,
                lift_to_both0 uniform_bytes_2203
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (seq_truncate (
          lift_to_both0 uniform_bytes_2203) (lift_to_both0 len_in_bytes_2207))
      ) : both (CEfset (
        [l_i_b_str_2201_loc ; b_i_2202_loc ; uniform_bytes_2203_loc])) [interface] (
      byte_seq)).
Fail Next Obligation.

Definition output_2218_loc : ChoiceEqualityLocation :=
  (seq fp_t ; 2219%nat).
Notation "'fp_hash_to_field_inp'" :=(
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'fp_hash_to_field_inp'" :=(
  byte_seq '× byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'fp_hash_to_field_out'" :=(
  seq fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_hash_to_field_out'" :=(seq fp_t : ChoiceEquality) (at level 2).
Definition FP_HASH_TO_FIELD : nat :=
  2229.
Program Definition fp_hash_to_field (msg_2222 : byte_seq) (
    dst_2223 : byte_seq) (count_2220 : uint_size)
  : both (CEfset (
      [l_i_b_str_2201_loc ; b_i_2202_loc ; uniform_bytes_2203_loc ; output_2218_loc])) [interface] (
    seq fp_t) :=
  ((letb len_in_bytes_2221 : uint_size :=
        (lift_to_both0 count_2220) .* (lift_to_both0 l_v) in
      letb uniform_bytes_2224 : seq uint8 :=
        expand_message_xmd (lift_to_both0 msg_2222) (lift_to_both0 dst_2223) (
          lift_to_both0 len_in_bytes_2221) in
      letbm output_2218 : seq fp_t loc( output_2218_loc ) :=
        seq_new_ (default : fp_t) (lift_to_both0 count_2220) in
      letb output_2218 :=
        foldi_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 count_2220) output_2218 (L := (CEfset (
                [l_i_b_str_2201_loc ; b_i_2202_loc ; uniform_bytes_2203_loc ; output_2218_loc]))) (
            I := [interface]) (fun i_2225 output_2218 =>
            letb elm_offset_2226 : uint_size :=
              (lift_to_both0 l_v) .* (lift_to_both0 i_2225) in
            letb tv_2227 : seq uint8 :=
              seq_slice (lift_to_both0 uniform_bytes_2224) (
                lift_to_both0 elm_offset_2226) (lift_to_both0 l_v) in
            letb u_i_2228 : fp_t :=
              nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
                    nat_mod_from_byte_seq_be (lift_to_both0 tv_2227))) (
                  lift_to_both0 (usize 16)) (lift_to_both0 (usize 48))) in
            letb output_2218 : seq fp_t :=
              seq_upd output_2218 (lift_to_both0 i_2225) (is_pure (
                  lift_to_both0 u_i_2228)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 output_2218)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 output_2218)
      ) : both (CEfset (
        [l_i_b_str_2201_loc ; b_i_2202_loc ; uniform_bytes_2203_loc ; output_2218_loc])) [interface] (
      seq fp_t)).
Fail Next Obligation.


Notation "'fp_sgn0_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_sgn0_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'fp_sgn0_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'fp_sgn0_out'" :=(bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition FP_SGN0 : nat :=
  2231.
Program Definition fp_sgn0 (x_2230 : fp_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 x_2230) rem (nat_mod_two )) =.? (nat_mod_one ))
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
  2235.
Program Definition fp_is_square (x_2233 : fp_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb c1_2232 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_1_2_v)) in
      letb tv_2234 : fp_t :=
        nat_mod_pow_self (lift_to_both0 x_2233) (lift_to_both0 c1_2232) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 tv_2234) =.? (nat_mod_zero )) || ((
            lift_to_both0 tv_2234) =.? (nat_mod_one )))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'fp_sqrt_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_sqrt_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'fp_sqrt_out'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_sqrt_out'" :=(fp_t : ChoiceEquality) (at level 2).
Definition FP_SQRT : nat :=
  2238.
Program Definition fp_sqrt (x_2237 : fp_t)
  : both (fset.fset0) [interface] (fp_t) :=
  ((letb c1_2236 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_1_4_v)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (nat_mod_pow_self (
          lift_to_both0 x_2237) (lift_to_both0 c1_2236))
      ) : both (fset.fset0) [interface] (fp_t)).
Fail Next Obligation.


Notation "'g1_curve_func_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_curve_func_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'g1_curve_func_out'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_curve_func_out'" :=(fp_t : ChoiceEquality) (at level 2).
Definition G1_CURVE_FUNC : nat :=
  2240.
Program Definition g1_curve_func (x_2239 : fp_t)
  : both (fset.fset0) [interface] (fp_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((((
              lift_to_both0 x_2239) *% (lift_to_both0 x_2239)) *% (
            lift_to_both0 x_2239)) +% (nat_mod_from_literal (_) (lift_to_both0 (
              @repr U128 4))))
      ) : both (fset.fset0) [interface] (fp_t)).
Fail Next Obligation.

Definition tv4_2241_loc : ChoiceEqualityLocation :=
  (fp_t ; 2243%nat).
Definition y_2242_loc : ChoiceEqualityLocation :=
  (fp_t ; 2244%nat).
Notation "'g1_map_to_curve_svdw_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_map_to_curve_svdw_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'g1_map_to_curve_svdw_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_map_to_curve_svdw_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1_MAP_TO_CURVE_SVDW : nat :=
  2258.
Program Definition g1_map_to_curve_svdw (u_2247 : fp_t)
  : both (CEfset ([tv4_2241_loc ; y_2242_loc])) [interface] (g1_t) :=
  ((letb z_2245 : fp_t :=
        (nat_mod_zero ) -% (nat_mod_from_literal (_) (lift_to_both0 (
              @repr U128 3))) in
      letb gz_2246 : fp_t := g1_curve_func (lift_to_both0 z_2245) in
      letb tv1_2248 : fp_t :=
        ((lift_to_both0 u_2247) *% (lift_to_both0 u_2247)) *% (
          lift_to_both0 gz_2246) in
      letb tv2_2249 : fp_t := (nat_mod_one ) +% (lift_to_both0 tv1_2248) in
      letb tv1_2250 : fp_t := (nat_mod_one ) -% (lift_to_both0 tv1_2248) in
      letb tv3_2251 : fp_t :=
        nat_mod_inv ((lift_to_both0 tv1_2250) *% (lift_to_both0 tv2_2249)) in
      letbm tv4_2241 : fp_t loc( tv4_2241_loc ) :=
        fp_sqrt (((nat_mod_zero ) -% (lift_to_both0 gz_2246)) *% (((
                nat_mod_from_literal (_) (lift_to_both0 (@repr U128 3))) *% (
                lift_to_both0 z_2245)) *% (lift_to_both0 z_2245))) in
      letb '(tv4_2241) :=
        if fp_sgn0 (lift_to_both0 tv4_2241) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([tv4_2241_loc])) (L2 := CEfset (
            [tv4_2241_loc ; y_2242_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm tv4_2241 loc( tv4_2241_loc ) :=
            (nat_mod_zero ) -% (lift_to_both0 tv4_2241) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 tv4_2241)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 tv4_2241)
         in
      letb tv5_2252 : fp_t :=
        (((lift_to_both0 u_2247) *% (lift_to_both0 tv1_2250)) *% (
            lift_to_both0 tv3_2251)) *% (lift_to_both0 tv4_2241) in
      letb tv6_2253 : fp_t :=
        (((nat_mod_zero ) -% (nat_mod_from_literal (_) (lift_to_both0 (
                  @repr U128 4)))) *% (lift_to_both0 gz_2246)) *% (nat_mod_inv (
            ((nat_mod_from_literal (_) (lift_to_both0 (@repr U128 3))) *% (
                lift_to_both0 z_2245)) *% (lift_to_both0 z_2245))) in
      letb x1_2254 : fp_t :=
        (((nat_mod_zero ) -% (lift_to_both0 z_2245)) *% (nat_mod_inv (
              nat_mod_two ))) -% (lift_to_both0 tv5_2252) in
      letb x2_2255 : fp_t :=
        (((nat_mod_zero ) -% (lift_to_both0 z_2245)) *% (nat_mod_inv (
              nat_mod_two ))) +% (lift_to_both0 tv5_2252) in
      letb x3_2256 : fp_t :=
        (lift_to_both0 z_2245) +% (((lift_to_both0 tv6_2253) *% (((
                  lift_to_both0 tv2_2249) *% (lift_to_both0 tv2_2249)) *% (
                lift_to_both0 tv3_2251))) *% (((lift_to_both0 tv2_2249) *% (
                lift_to_both0 tv2_2249)) *% (lift_to_both0 tv3_2251))) in
      letb x_2257 : fp_t :=
        if is_pure (I := [interface]) (fp_is_square (g1_curve_func (
              lift_to_both0 x1_2254)))
        then lift_to_both0 x1_2254
        else if is_pure (I := [interface]) (fp_is_square (g1_curve_func (
              lift_to_both0 x2_2255)))
        then lift_to_both0 x2_2255
        else lift_to_both0 x3_2256 in
      letbm y_2242 : fp_t loc( y_2242_loc ) :=
        fp_sqrt (g1_curve_func (lift_to_both0 x_2257)) in
      letb '(y_2242) :=
        if (fp_sgn0 (lift_to_both0 u_2247)) !=.? (fp_sgn0 (
            lift_to_both0 y_2242)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([tv4_2241_loc ; y_2242_loc])) (
          L2 := CEfset ([tv4_2241_loc ; y_2242_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm y_2242 loc( y_2242_loc ) :=
            (nat_mod_zero ) -% (lift_to_both0 y_2242) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 y_2242)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 y_2242)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_2257,
          lift_to_both0 y_2242,
          lift_to_both0 ((false : bool_ChoiceEquality))
        ))
      ) : both (CEfset ([tv4_2241_loc ; y_2242_loc])) [interface] (g1_t)).
Fail Next Obligation.


Notation "'g1_clear_cofactor_inp'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_clear_cofactor_inp'" :=(g1_t : ChoiceEquality) (at level 2).
Notation "'g1_clear_cofactor_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_clear_cofactor_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1_CLEAR_COFACTOR : nat :=
  2261.
Program Definition g1_clear_cofactor (x_2260 : g1_t)
  : both (fset.fset0) [interface] (g1_t) :=
  ((letb h_eff_2259 : scalar_t :=
        nat_mod_from_literal (_) (lift_to_both0 (
            @repr U128 15132376222941642753)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (g1mul (
          lift_to_both0 h_eff_2259) (lift_to_both0 x_2260))
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
  2269.
Program Definition g1_hash_to_curve_svdw (msg_2262 : byte_seq) (
    dst_2263 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2201_loc ; b_i_2202_loc ; uniform_bytes_2203_loc ; output_2218_loc ; tv4_2241_loc ; y_2242_loc])) [interface] (
    g1_t) :=
  ((letb u_2264 : seq fp_t :=
        fp_hash_to_field (lift_to_both0 msg_2262) (lift_to_both0 dst_2263) (
          lift_to_both0 (usize 2)) in
      letb q0_2265 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_map_to_curve_svdw (seq_index (u_2264) (lift_to_both0 (usize 0))) in
      letb q1_2266 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_map_to_curve_svdw (seq_index (u_2264) (lift_to_both0 (usize 1))) in
      letb r_2267 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1add (lift_to_both0 q0_2265) (lift_to_both0 q1_2266) in
      letb p_2268 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_clear_cofactor (lift_to_both0 r_2267) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2268)
      ) : both (CEfset (
        [l_i_b_str_2201_loc ; b_i_2202_loc ; uniform_bytes_2203_loc ; output_2218_loc ; tv4_2241_loc ; y_2242_loc])) [interface] (
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
  2275.
Program Definition g1_encode_to_curve_svdw (msg_2270 : byte_seq) (
    dst_2271 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2201_loc ; b_i_2202_loc ; uniform_bytes_2203_loc ; output_2218_loc ; tv4_2241_loc ; y_2242_loc])) [interface] (
    g1_t) :=
  ((letb u_2272 : seq fp_t :=
        fp_hash_to_field (lift_to_both0 msg_2270) (lift_to_both0 dst_2271) (
          lift_to_both0 (usize 1)) in
      letb q_2273 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_map_to_curve_svdw (seq_index (u_2272) (lift_to_both0 (usize 0))) in
      letb p_2274 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_clear_cofactor (lift_to_both0 q_2273) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2274)
      ) : both (CEfset (
        [l_i_b_str_2201_loc ; b_i_2202_loc ; uniform_bytes_2203_loc ; output_2218_loc ; tv4_2241_loc ; y_2242_loc])) [interface] (
      g1_t)).
Fail Next Obligation.

Definition output_2276_loc : ChoiceEqualityLocation :=
  (seq (fp_t '× fp_t) ; 2277%nat).
Notation "'fp2_hash_to_field_inp'" :=(
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'fp2_hash_to_field_inp'" :=(
  byte_seq '× byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'fp2_hash_to_field_out'" :=(
  seq fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2_hash_to_field_out'" :=(seq fp2_t : ChoiceEquality) (at level 2).
Definition FP2_HASH_TO_FIELD : nat :=
  2290.
Program Definition fp2_hash_to_field (msg_2280 : byte_seq) (
    dst_2281 : byte_seq) (count_2278 : uint_size)
  : both (CEfset (
      [l_i_b_str_2201_loc ; b_i_2202_loc ; uniform_bytes_2203_loc ; output_2276_loc])) [interface] (
    seq fp2_t) :=
  ((letb len_in_bytes_2279 : uint_size :=
        ((lift_to_both0 count_2278) .* (lift_to_both0 (usize 2))) .* (
          lift_to_both0 l_v) in
      letb uniform_bytes_2282 : seq uint8 :=
        expand_message_xmd (lift_to_both0 msg_2280) (lift_to_both0 dst_2281) (
          lift_to_both0 len_in_bytes_2279) in
      letbm output_2276 : seq (fp_t '× fp_t) loc( output_2276_loc ) :=
        seq_new_ (default : fp2_t) (lift_to_both0 count_2278) in
      letb output_2276 :=
        foldi_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 count_2278) output_2276 (L := (CEfset (
                [l_i_b_str_2201_loc ; b_i_2202_loc ; uniform_bytes_2203_loc ; output_2276_loc]))) (
            I := [interface]) (fun i_2283 output_2276 =>
            letb elm_offset_2284 : uint_size :=
              ((lift_to_both0 l_v) .* (lift_to_both0 i_2283)) .* (
                lift_to_both0 (usize 2)) in
            letb tv_2285 : seq uint8 :=
              seq_slice (lift_to_both0 uniform_bytes_2282) (
                lift_to_both0 elm_offset_2284) (lift_to_both0 l_v) in
            letb e_1_2286 : fp_t :=
              nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
                    nat_mod_from_byte_seq_be (lift_to_both0 tv_2285))) (
                  lift_to_both0 (usize 16)) (lift_to_both0 (usize 48))) in
            letb elm_offset_2287 : uint_size :=
              (lift_to_both0 l_v) .* ((lift_to_both0 (usize 1)) .+ ((
                    lift_to_both0 i_2283) .* (lift_to_both0 (usize 2)))) in
            letb tv_2288 : seq uint8 :=
              seq_slice (lift_to_both0 uniform_bytes_2282) (
                lift_to_both0 elm_offset_2287) (lift_to_both0 l_v) in
            letb e_2_2289 : fp_t :=
              nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
                    nat_mod_from_byte_seq_be (lift_to_both0 tv_2288))) (
                  lift_to_both0 (usize 16)) (lift_to_both0 (usize 48))) in
            letb output_2276 : seq (fp_t '× fp_t) :=
              seq_upd output_2276 (lift_to_both0 i_2283) (is_pure (prod_b(
                    lift_to_both0 e_1_2286,
                    lift_to_both0 e_2_2289
                  ))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 output_2276)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 output_2276)
      ) : both (CEfset (
        [l_i_b_str_2201_loc ; b_i_2202_loc ; uniform_bytes_2203_loc ; output_2276_loc])) [interface] (
      seq fp2_t)).
Fail Next Obligation.


Notation "'fp2_sgn0_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2_sgn0_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'fp2_sgn0_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'fp2_sgn0_out'" :=(bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition FP2_SGN0 : nat :=
  2297.
Program Definition fp2_sgn0 (x_2291 : fp2_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb '(x0_2292, x1_2293) : (fp_t '× fp_t) := lift_to_both0 x_2291 in
      letb sign_0_2294 : bool_ChoiceEquality :=
        fp_sgn0 (lift_to_both0 x0_2292) in
      letb zero_0_2295 : bool_ChoiceEquality :=
        (lift_to_both0 x0_2292) =.? (nat_mod_zero ) in
      letb sign_1_2296 : bool_ChoiceEquality :=
        fp_sgn0 (lift_to_both0 x1_2293) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 sign_0_2294) || ((lift_to_both0 zero_0_2295) && (
            lift_to_both0 sign_1_2296)))
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
  2307.
Program Definition fp2_is_square (x_2299 : fp2_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb c1_2298 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_1_2_v)) in
      letb '(x1_2300, x2_2301) : (fp_t '× fp_t) := lift_to_both0 x_2299 in
      letb tv1_2302 : fp_t :=
        (lift_to_both0 x1_2300) *% (lift_to_both0 x1_2300) in
      letb tv2_2303 : fp_t :=
        (lift_to_both0 x2_2301) *% (lift_to_both0 x2_2301) in
      letb tv1_2304 : fp_t :=
        (lift_to_both0 tv1_2302) +% (lift_to_both0 tv2_2303) in
      letb tv1_2305 : fp_t :=
        nat_mod_pow_self (lift_to_both0 tv1_2304) (lift_to_both0 c1_2298) in
      letb neg1_2306 : fp_t := (nat_mod_zero ) -% (nat_mod_one ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 tv1_2305) !=.? (lift_to_both0 neg1_2306))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.

Definition c_2308_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2309%nat).
Notation "'fp2exp_inp'" :=(
  fp2_t '× fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2exp_inp'" :=(fp2_t '× fp_t : ChoiceEquality) (at level 2).
Notation "'fp2exp_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2exp_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition FP2EXP : nat :=
  2313.
Program Definition fp2exp (n_2312 : fp2_t) (k_2311 : fp_t)
  : both (CEfset ([c_2308_loc])) [interface] (fp2_t) :=
  ((letbm c_2308 : (fp_t '× fp_t) loc( c_2308_loc ) :=
        fp2fromfp (nat_mod_one ) in
      letb c_2308 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 381)) c_2308 (L := (CEfset ([c_2308_loc]))) (
            I := [interface]) (fun i_2310 c_2308 =>
            letbm c_2308 loc( c_2308_loc ) :=
              fp2mul (lift_to_both0 c_2308) (lift_to_both0 c_2308) in
            letb '(c_2308) :=
              if nat_mod_bit (lift_to_both0 k_2311) ((lift_to_both0 (
                    usize 380)) .- (lift_to_both0 i_2310)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([c_2308_loc])) (L2 := CEfset (
                  [c_2308_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm c_2308 loc( c_2308_loc ) :=
                  fp2mul (lift_to_both0 c_2308) (lift_to_both0 n_2312) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 c_2308)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 c_2308)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 c_2308)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 c_2308)
      ) : both (CEfset ([c_2308_loc])) [interface] (fp2_t)).
Fail Next Obligation.


Notation "'fp2_sqrt_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2_sqrt_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'fp2_sqrt_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2_sqrt_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition FP2_SQRT : nat :=
  2322.
Program Definition fp2_sqrt (a_2316 : fp2_t)
  : both (CEfset ([c_2308_loc])) [interface] (fp2_t) :=
  ((letb c1_2314 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_3_4_v)) in
      letb c2_2315 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (lift_to_both0 p_1_2_v)) in
      letb a1_2317 : (fp_t '× fp_t) :=
        fp2exp (lift_to_both0 a_2316) (lift_to_both0 c1_2314) in
      letb alpha_2318 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 a1_2317) (fp2mul (lift_to_both0 a1_2317) (
            lift_to_both0 a_2316)) in
      letb x0_2319 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 a1_2317) (lift_to_both0 a_2316) in
      letb neg1_2320 : (fp_t '× fp_t) :=
        prod_b((nat_mod_zero ) -% (nat_mod_one ), nat_mod_zero ) in
      letb b_2321 : (fp_t '× fp_t) :=
        fp2exp (fp2add (fp2fromfp (nat_mod_one )) (lift_to_both0 alpha_2318)) (
          lift_to_both0 c2_2315) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 alpha_2318) =.? (
            lift_to_both0 neg1_2320))
        then fp2mul (prod_b(nat_mod_zero , nat_mod_one )) (
          lift_to_both0 x0_2319)
        else fp2mul (lift_to_both0 b_2321) (lift_to_both0 x0_2319))
      ) : both (CEfset ([c_2308_loc])) [interface] (fp2_t)).
Fail Next Obligation.


Notation "'g2_curve_func_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_curve_func_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'g2_curve_func_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_curve_func_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition G2_CURVE_FUNC : nat :=
  2324.
Program Definition g2_curve_func (x_2323 : fp2_t)
  : both (fset.fset0) [interface] (fp2_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp2add (fp2mul (
            lift_to_both0 x_2323) (fp2mul (lift_to_both0 x_2323) (
              lift_to_both0 x_2323))) (prod_b(
            nat_mod_from_literal (_) (lift_to_both0 (@repr U128 4)),
            nat_mod_from_literal (_) (lift_to_both0 (@repr U128 4))
          )))
      ) : both (fset.fset0) [interface] (fp2_t)).
Fail Next Obligation.

Definition tv4_2325_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2327%nat).
Definition y_2326_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2328%nat).
Notation "'g2_map_to_curve_svdw_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_map_to_curve_svdw_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'g2_map_to_curve_svdw_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_map_to_curve_svdw_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_MAP_TO_CURVE_SVDW : nat :=
  2343.
Program Definition g2_map_to_curve_svdw (u_2331 : fp2_t)
  : both (CEfset ([c_2308_loc ; tv4_2325_loc ; y_2326_loc])) [interface] (
    g2_t) :=
  ((letb z_2329 : (fp_t '× fp_t) := fp2neg (fp2fromfp (nat_mod_one )) in
      letb gz_2330 : (fp_t '× fp_t) := g2_curve_func (lift_to_both0 z_2329) in
      letb tv1_2332 : (fp_t '× fp_t) :=
        fp2mul (fp2mul (lift_to_both0 u_2331) (lift_to_both0 u_2331)) (
          lift_to_both0 gz_2330) in
      letb tv2_2333 : (fp_t '× fp_t) :=
        fp2add (fp2fromfp (nat_mod_one )) (lift_to_both0 tv1_2332) in
      letb tv1_2334 : (fp_t '× fp_t) :=
        fp2sub (fp2fromfp (nat_mod_one )) (lift_to_both0 tv1_2332) in
      letb tv3_2335 : (fp_t '× fp_t) :=
        fp2inv (fp2mul (lift_to_both0 tv1_2334) (lift_to_both0 tv2_2333)) in
      letbm tv4_2325 : (fp_t '× fp_t) loc( tv4_2325_loc ) :=
        fp2_sqrt (fp2mul (fp2neg (lift_to_both0 gz_2330)) (fp2mul (fp2fromfp (
                nat_mod_from_literal (_) (lift_to_both0 (@repr U128 3)))) (
              fp2mul (lift_to_both0 z_2329) (lift_to_both0 z_2329)))) in
      letb '(tv4_2325) :=
        if fp2_sgn0 (lift_to_both0 tv4_2325) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([c_2308_loc ; tv4_2325_loc])) (
          L2 := CEfset ([c_2308_loc ; tv4_2325_loc ; y_2326_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm tv4_2325 loc( tv4_2325_loc ) :=
            fp2neg (lift_to_both0 tv4_2325) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 tv4_2325)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 tv4_2325)
         in
      letb tv5_2336 : (fp_t '× fp_t) :=
        fp2mul (fp2mul (fp2mul (lift_to_both0 u_2331) (
              lift_to_both0 tv1_2334)) (lift_to_both0 tv3_2335)) (
          lift_to_both0 tv4_2325) in
      letb tv6_2337 : (fp_t '× fp_t) :=
        fp2mul (fp2mul (fp2neg (fp2fromfp (nat_mod_from_literal (_) (
                  lift_to_both0 (@repr U128 4))))) (lift_to_both0 gz_2330)) (
          fp2inv (fp2mul (fp2fromfp (nat_mod_from_literal (_) (lift_to_both0 (
                    @repr U128 3)))) (fp2mul (lift_to_both0 z_2329) (
                lift_to_both0 z_2329)))) in
      letb x1_2338 : (fp_t '× fp_t) :=
        fp2sub (fp2mul (fp2neg (lift_to_both0 z_2329)) (fp2inv (fp2fromfp (
                nat_mod_two )))) (lift_to_both0 tv5_2336) in
      letb x2_2339 : (fp_t '× fp_t) :=
        fp2add (fp2mul (fp2neg (lift_to_both0 z_2329)) (fp2inv (fp2fromfp (
                nat_mod_two )))) (lift_to_both0 tv5_2336) in
      letb tv7_2340 : (fp_t '× fp_t) :=
        fp2mul (fp2mul (lift_to_both0 tv2_2333) (lift_to_both0 tv2_2333)) (
          lift_to_both0 tv3_2335) in
      letb x3_2341 : (fp_t '× fp_t) :=
        fp2add (lift_to_both0 z_2329) (fp2mul (lift_to_both0 tv6_2337) (fp2mul (
              lift_to_both0 tv7_2340) (lift_to_both0 tv7_2340))) in
      letb x_2342 : (fp_t '× fp_t) :=
        if is_pure (I := [interface]) (fp2_is_square (g2_curve_func (
              lift_to_both0 x1_2338)))
        then lift_to_both0 x1_2338
        else if is_pure (I := [interface]) (fp2_is_square (g2_curve_func (
              lift_to_both0 x2_2339)))
        then lift_to_both0 x2_2339
        else lift_to_both0 x3_2341 in
      letbm y_2326 : (fp_t '× fp_t) loc( y_2326_loc ) :=
        fp2_sqrt (g2_curve_func (lift_to_both0 x_2342)) in
      letb '(y_2326) :=
        if (fp2_sgn0 (lift_to_both0 u_2331)) !=.? (fp2_sgn0 (
            lift_to_both0 y_2326)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [c_2308_loc ; tv4_2325_loc ; y_2326_loc])) (L2 := CEfset (
            [c_2308_loc ; tv4_2325_loc ; y_2326_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm y_2326 loc( y_2326_loc ) := fp2neg (lift_to_both0 y_2326) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 y_2326)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 y_2326)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_2342,
          lift_to_both0 y_2326,
          lift_to_both0 ((false : bool_ChoiceEquality))
        ))
      ) : both (CEfset ([c_2308_loc ; tv4_2325_loc ; y_2326_loc])) [interface] (
      g2_t)).
Fail Next Obligation.


Notation "'psi_inp'" :=(g2_t : choice_type) (in custom pack_type at level 2).
Notation "'psi_inp'" :=(g2_t : ChoiceEquality) (at level 2).
Notation "'psi_out'" :=(g2_t : choice_type) (in custom pack_type at level 2).
Notation "'psi_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition PSI : nat :=
  2352.
Program Definition psi (p_2346 : g2_t)
  : both (CEfset ([c_2308_loc])) [interface] (g2_t) :=
  ((letb c1_2344 : (fp_t '× fp_t) :=
        fp2inv (fp2exp (prod_b(nat_mod_one , nat_mod_one )) (((
                nat_mod_zero ) -% (nat_mod_one )) *% (nat_mod_inv (
                nat_mod_from_literal (_) (lift_to_both0 (@repr U128 3)))))) in
      letb c2_2345 : (fp_t '× fp_t) :=
        fp2inv (fp2exp (prod_b(nat_mod_one , nat_mod_one )) (((
                nat_mod_zero ) -% (nat_mod_one )) *% (nat_mod_inv (
                nat_mod_two )))) in
      letb '(x_2347, y_2348, inf_2349) : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        lift_to_both0 p_2346 in
      letb qx_2350 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 c1_2344) (fp2conjugate (lift_to_both0 x_2347)) in
      letb qy_2351 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 c2_2345) (fp2conjugate (lift_to_both0 y_2348)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 qx_2350,
          lift_to_both0 qy_2351,
          lift_to_both0 inf_2349
        ))
      ) : both (CEfset ([c_2308_loc])) [interface] (g2_t)).
Fail Next Obligation.


Notation "'g2_clear_cofactor_inp'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_clear_cofactor_inp'" :=(g2_t : ChoiceEquality) (at level 2).
Notation "'g2_clear_cofactor_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_clear_cofactor_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_CLEAR_COFACTOR : nat :=
  2367.
Program Definition g2_clear_cofactor (p_2354 : g2_t)
  : both (CEfset ([c_2308_loc])) [interface] (g2_t) :=
  ((letb c1_2353 : scalar_t :=
        nat_mod_from_literal (_) (lift_to_both0 (
            @repr U128 15132376222941642752)) in
      letb t1_2355 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2mul (lift_to_both0 c1_2353) (lift_to_both0 p_2354) in
      letb t1_2356 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2neg (lift_to_both0 t1_2355) in
      letb t2_2357 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        psi (lift_to_both0 p_2354) in
      letb t3_2358 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2double (lift_to_both0 p_2354) in
      letb t3_2359 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        psi (psi (lift_to_both0 t3_2358)) in
      letb t3_2360 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 t3_2359) (g2neg (lift_to_both0 t2_2357)) in
      letb t2_2361 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 t1_2356) (lift_to_both0 t2_2357) in
      letb t2_2362 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2mul (lift_to_both0 c1_2353) (lift_to_both0 t2_2361) in
      letb t2_2363 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2neg (lift_to_both0 t2_2362) in
      letb t3_2364 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 t3_2360) (lift_to_both0 t2_2363) in
      letb t3_2365 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 t3_2364) (g2neg (lift_to_both0 t1_2356)) in
      letb q_2366 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 t3_2365) (g2neg (lift_to_both0 p_2354)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 q_2366)
      ) : both (CEfset ([c_2308_loc])) [interface] (g2_t)).
Fail Next Obligation.


Notation "'g2_hash_to_curve_svdw_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g2_hash_to_curve_svdw_inp'" :=(
  byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'g2_hash_to_curve_svdw_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_hash_to_curve_svdw_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_HASH_TO_CURVE_SVDW : nat :=
  2375.
Program Definition g2_hash_to_curve_svdw (msg_2368 : byte_seq) (
    dst_2369 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2201_loc ; b_i_2202_loc ; uniform_bytes_2203_loc ; output_2276_loc ; c_2308_loc ; tv4_2325_loc ; y_2326_loc])) [interface] (
    g2_t) :=
  ((letb u_2370 : seq fp2_t :=
        fp2_hash_to_field (lift_to_both0 msg_2368) (lift_to_both0 dst_2369) (
          lift_to_both0 (usize 2)) in
      letb q0_2371 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2_map_to_curve_svdw (seq_index (u_2370) (lift_to_both0 (usize 0))) in
      letb q1_2372 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2_map_to_curve_svdw (seq_index (u_2370) (lift_to_both0 (usize 1))) in
      letb r_2373 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 q0_2371) (lift_to_both0 q1_2372) in
      letb p_2374 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_clear_cofactor (lift_to_both0 r_2373) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2374)
      ) : both (CEfset (
        [l_i_b_str_2201_loc ; b_i_2202_loc ; uniform_bytes_2203_loc ; output_2276_loc ; c_2308_loc ; tv4_2325_loc ; y_2326_loc])) [interface] (
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
  2381.
Program Definition g2_encode_to_curve_svdw (msg_2376 : byte_seq) (
    dst_2377 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2201_loc ; b_i_2202_loc ; uniform_bytes_2203_loc ; output_2276_loc ; c_2308_loc ; tv4_2325_loc ; y_2326_loc])) [interface] (
    g2_t) :=
  ((letb u_2378 : seq fp2_t :=
        fp2_hash_to_field (lift_to_both0 msg_2376) (lift_to_both0 dst_2377) (
          lift_to_both0 (usize 1)) in
      letb q_2379 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_map_to_curve_svdw (seq_index (u_2378) (lift_to_both0 (usize 0))) in
      letb p_2380 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_clear_cofactor (lift_to_both0 q_2379) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2380)
      ) : both (CEfset (
        [l_i_b_str_2201_loc ; b_i_2202_loc ; uniform_bytes_2203_loc ; output_2276_loc ; c_2308_loc ; tv4_2325_loc ; y_2326_loc])) [interface] (
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

Definition y_2383_loc : ChoiceEqualityLocation :=
  (fp_t ; 2384%nat).
Definition x1_2382_loc : ChoiceEqualityLocation :=
  (fp_t ; 2385%nat).
Notation "'g1_simple_swu_iso_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_simple_swu_iso_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'g1_simple_swu_iso_out'" :=((fp_t '× fp_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'g1_simple_swu_iso_out'" :=((fp_t '× fp_t
  ) : ChoiceEquality) (at level 2).
Definition G1_SIMPLE_SWU_ISO : nat :=
  2395.
Program Definition g1_simple_swu_iso (u_2389 : fp_t)
  : both (CEfset ([x1_2382_loc ; y_2383_loc])) [interface] ((fp_t '× fp_t)) :=
  ((letb z_2386 : fp_t :=
        nat_mod_from_literal (_) (lift_to_both0 (@repr U128 11)) in
      letb a_2387 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (
            lift_to_both0 g1_iso_a_v)) in
      letb b_2388 : fp_t :=
        nat_mod_from_byte_seq_be (array_to_be_bytes (
            lift_to_both0 g1_iso_b_v)) in
      letb tv1_2390 : fp_t :=
        nat_mod_inv ((((lift_to_both0 z_2386) *% (lift_to_both0 z_2386)) *% (
              nat_mod_exp (lift_to_both0 u_2389) (lift_to_both0 (
                  @repr U32 4)))) +% (((lift_to_both0 z_2386) *% (
                lift_to_both0 u_2389)) *% (lift_to_both0 u_2389))) in
      letbm x1_2382 : fp_t loc( x1_2382_loc ) :=
        (((nat_mod_zero ) -% (lift_to_both0 b_2388)) *% (nat_mod_inv (
              lift_to_both0 a_2387))) *% ((nat_mod_one ) +% (
            lift_to_both0 tv1_2390)) in
      letb '(x1_2382) :=
        if (lift_to_both0 tv1_2390) =.? (nat_mod_zero ) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([x1_2382_loc])) (L2 := CEfset (
            [x1_2382_loc ; y_2383_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x1_2382 loc( x1_2382_loc ) :=
            (lift_to_both0 b_2388) *% (nat_mod_inv ((lift_to_both0 z_2386) *% (
                  lift_to_both0 a_2387))) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 x1_2382)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 x1_2382)
         in
      letb gx1_2391 : fp_t :=
        ((nat_mod_exp (lift_to_both0 x1_2382) (lift_to_both0 (
                @repr U32 3))) +% ((lift_to_both0 a_2387) *% (
              lift_to_both0 x1_2382))) +% (lift_to_both0 b_2388) in
      letb x2_2392 : fp_t :=
        (((lift_to_both0 z_2386) *% (lift_to_both0 u_2389)) *% (
            lift_to_both0 u_2389)) *% (lift_to_both0 x1_2382) in
      letb gx2_2393 : fp_t :=
        ((nat_mod_exp (lift_to_both0 x2_2392) (lift_to_both0 (
                @repr U32 3))) +% ((lift_to_both0 a_2387) *% (
              lift_to_both0 x2_2392))) +% (lift_to_both0 b_2388) in
      letb '(x_2394, y_2383) : (fp_t '× fp_t) :=
        if is_pure (I := [interface]) (fp_is_square (lift_to_both0 gx1_2391))
        then prod_b(lift_to_both0 x1_2382, fp_sqrt (lift_to_both0 gx1_2391))
        else prod_b(lift_to_both0 x2_2392, fp_sqrt (lift_to_both0 gx2_2393)) in
      letb '(y_2383) :=
        if (fp_sgn0 (lift_to_both0 u_2389)) !=.? (fp_sgn0 (
            lift_to_both0 y_2383)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([x1_2382_loc ; y_2383_loc])) (
          L2 := CEfset ([x1_2382_loc ; y_2383_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm y_2383 loc( y_2383_loc ) :=
            (nat_mod_zero ) -% (lift_to_both0 y_2383) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 y_2383)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 y_2383)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_2394,
          lift_to_both0 y_2383
        ))
      ) : both (CEfset ([x1_2382_loc ; y_2383_loc])) [interface] ((fp_t '× fp_t
      ))).
Fail Next Obligation.

Definition xx_2405_loc : ChoiceEqualityLocation :=
  (fp_t ; 2409%nat).
Definition inf_2408_loc : ChoiceEqualityLocation :=
  (bool_ChoiceEquality ; 2410%nat).
Definition ynum_k_2398_loc : ChoiceEqualityLocation :=
  (seq fp_t ; 2411%nat).
Definition xden_k_2397_loc : ChoiceEqualityLocation :=
  (seq fp_t ; 2412%nat).
Definition xx_2407_loc : ChoiceEqualityLocation :=
  (fp_t ; 2413%nat).
Definition xx_2403_loc : ChoiceEqualityLocation :=
  (fp_t ; 2414%nat).
Definition yden_k_2399_loc : ChoiceEqualityLocation :=
  (seq fp_t ; 2415%nat).
Definition xnum_2400_loc : ChoiceEqualityLocation :=
  (fp_t ; 2416%nat).
Definition ynum_2404_loc : ChoiceEqualityLocation :=
  (fp_t ; 2417%nat).
Definition xx_2401_loc : ChoiceEqualityLocation :=
  (fp_t ; 2418%nat).
Definition xnum_k_2396_loc : ChoiceEqualityLocation :=
  (seq fp_t ; 2419%nat).
Definition yden_2406_loc : ChoiceEqualityLocation :=
  (fp_t ; 2420%nat).
Definition xden_2402_loc : ChoiceEqualityLocation :=
  (fp_t ; 2421%nat).
Notation "'g1_isogeny_map_inp'" :=(
  fp_t '× fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_isogeny_map_inp'" :=(fp_t '× fp_t : ChoiceEquality) (at level 2).
Notation "'g1_isogeny_map_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_isogeny_map_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1_ISOGENY_MAP : nat :=
  2430.
Program Definition g1_isogeny_map (x_2423 : fp_t) (y_2428 : fp_t)
  : both (CEfset (
      [xnum_k_2396_loc ; xden_k_2397_loc ; ynum_k_2398_loc ; yden_k_2399_loc ; xnum_2400_loc ; xx_2401_loc ; xden_2402_loc ; xx_2403_loc ; ynum_2404_loc ; xx_2405_loc ; yden_2406_loc ; xx_2407_loc ; inf_2408_loc])) [interface] (
    g1_t) :=
  ((letbm xnum_k_2396 : seq fp_t loc( xnum_k_2396_loc ) :=
        seq_new_ (default : fp_t) (lift_to_both0 (usize 12)) in
      letb xnum_k_2396 : seq fp_t :=
        seq_upd xnum_k_2396 (lift_to_both0 (usize 0)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_0_v)))) in
      letb xnum_k_2396 : seq fp_t :=
        seq_upd xnum_k_2396 (lift_to_both0 (usize 1)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_1_v)))) in
      letb xnum_k_2396 : seq fp_t :=
        seq_upd xnum_k_2396 (lift_to_both0 (usize 2)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_2_v)))) in
      letb xnum_k_2396 : seq fp_t :=
        seq_upd xnum_k_2396 (lift_to_both0 (usize 3)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_3_v)))) in
      letb xnum_k_2396 : seq fp_t :=
        seq_upd xnum_k_2396 (lift_to_both0 (usize 4)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_4_v)))) in
      letb xnum_k_2396 : seq fp_t :=
        seq_upd xnum_k_2396 (lift_to_both0 (usize 5)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_5_v)))) in
      letb xnum_k_2396 : seq fp_t :=
        seq_upd xnum_k_2396 (lift_to_both0 (usize 6)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_6_v)))) in
      letb xnum_k_2396 : seq fp_t :=
        seq_upd xnum_k_2396 (lift_to_both0 (usize 7)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_7_v)))) in
      letb xnum_k_2396 : seq fp_t :=
        seq_upd xnum_k_2396 (lift_to_both0 (usize 8)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_8_v)))) in
      letb xnum_k_2396 : seq fp_t :=
        seq_upd xnum_k_2396 (lift_to_both0 (usize 9)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_9_v)))) in
      letb xnum_k_2396 : seq fp_t :=
        seq_upd xnum_k_2396 (lift_to_both0 (usize 10)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_10_v)))) in
      letb xnum_k_2396 : seq fp_t :=
        seq_upd xnum_k_2396 (lift_to_both0 (usize 11)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xnum_k_11_v)))) in
      letbm xden_k_2397 : seq fp_t loc( xden_k_2397_loc ) :=
        seq_new_ (default : fp_t) (lift_to_both0 (usize 10)) in
      letb xden_k_2397 : seq fp_t :=
        seq_upd xden_k_2397 (lift_to_both0 (usize 0)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_0_v)))) in
      letb xden_k_2397 : seq fp_t :=
        seq_upd xden_k_2397 (lift_to_both0 (usize 1)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_1_v)))) in
      letb xden_k_2397 : seq fp_t :=
        seq_upd xden_k_2397 (lift_to_both0 (usize 2)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_2_v)))) in
      letb xden_k_2397 : seq fp_t :=
        seq_upd xden_k_2397 (lift_to_both0 (usize 3)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_3_v)))) in
      letb xden_k_2397 : seq fp_t :=
        seq_upd xden_k_2397 (lift_to_both0 (usize 4)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_4_v)))) in
      letb xden_k_2397 : seq fp_t :=
        seq_upd xden_k_2397 (lift_to_both0 (usize 5)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_5_v)))) in
      letb xden_k_2397 : seq fp_t :=
        seq_upd xden_k_2397 (lift_to_both0 (usize 6)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_6_v)))) in
      letb xden_k_2397 : seq fp_t :=
        seq_upd xden_k_2397 (lift_to_both0 (usize 7)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_7_v)))) in
      letb xden_k_2397 : seq fp_t :=
        seq_upd xden_k_2397 (lift_to_both0 (usize 8)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_8_v)))) in
      letb xden_k_2397 : seq fp_t :=
        seq_upd xden_k_2397 (lift_to_both0 (usize 9)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_xden_k_9_v)))) in
      letbm ynum_k_2398 : seq fp_t loc( ynum_k_2398_loc ) :=
        seq_new_ (default : fp_t) (lift_to_both0 (usize 16)) in
      letb ynum_k_2398 : seq fp_t :=
        seq_upd ynum_k_2398 (lift_to_both0 (usize 0)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_0_v)))) in
      letb ynum_k_2398 : seq fp_t :=
        seq_upd ynum_k_2398 (lift_to_both0 (usize 1)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_1_v)))) in
      letb ynum_k_2398 : seq fp_t :=
        seq_upd ynum_k_2398 (lift_to_both0 (usize 2)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_2_v)))) in
      letb ynum_k_2398 : seq fp_t :=
        seq_upd ynum_k_2398 (lift_to_both0 (usize 3)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_3_v)))) in
      letb ynum_k_2398 : seq fp_t :=
        seq_upd ynum_k_2398 (lift_to_both0 (usize 4)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_4_v)))) in
      letb ynum_k_2398 : seq fp_t :=
        seq_upd ynum_k_2398 (lift_to_both0 (usize 5)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_5_v)))) in
      letb ynum_k_2398 : seq fp_t :=
        seq_upd ynum_k_2398 (lift_to_both0 (usize 6)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_6_v)))) in
      letb ynum_k_2398 : seq fp_t :=
        seq_upd ynum_k_2398 (lift_to_both0 (usize 7)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_7_v)))) in
      letb ynum_k_2398 : seq fp_t :=
        seq_upd ynum_k_2398 (lift_to_both0 (usize 8)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_8_v)))) in
      letb ynum_k_2398 : seq fp_t :=
        seq_upd ynum_k_2398 (lift_to_both0 (usize 9)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_9_v)))) in
      letb ynum_k_2398 : seq fp_t :=
        seq_upd ynum_k_2398 (lift_to_both0 (usize 10)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_10_v)))) in
      letb ynum_k_2398 : seq fp_t :=
        seq_upd ynum_k_2398 (lift_to_both0 (usize 11)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_11_v)))) in
      letb ynum_k_2398 : seq fp_t :=
        seq_upd ynum_k_2398 (lift_to_both0 (usize 12)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_12_v)))) in
      letb ynum_k_2398 : seq fp_t :=
        seq_upd ynum_k_2398 (lift_to_both0 (usize 13)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_13_v)))) in
      letb ynum_k_2398 : seq fp_t :=
        seq_upd ynum_k_2398 (lift_to_both0 (usize 14)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_14_v)))) in
      letb ynum_k_2398 : seq fp_t :=
        seq_upd ynum_k_2398 (lift_to_both0 (usize 15)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_ynum_k_15_v)))) in
      letbm yden_k_2399 : seq fp_t loc( yden_k_2399_loc ) :=
        seq_new_ (default : fp_t) (lift_to_both0 (usize 15)) in
      letb yden_k_2399 : seq fp_t :=
        seq_upd yden_k_2399 (lift_to_both0 (usize 0)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_0_v)))) in
      letb yden_k_2399 : seq fp_t :=
        seq_upd yden_k_2399 (lift_to_both0 (usize 1)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_1_v)))) in
      letb yden_k_2399 : seq fp_t :=
        seq_upd yden_k_2399 (lift_to_both0 (usize 2)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_2_v)))) in
      letb yden_k_2399 : seq fp_t :=
        seq_upd yden_k_2399 (lift_to_both0 (usize 3)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_3_v)))) in
      letb yden_k_2399 : seq fp_t :=
        seq_upd yden_k_2399 (lift_to_both0 (usize 4)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_4_v)))) in
      letb yden_k_2399 : seq fp_t :=
        seq_upd yden_k_2399 (lift_to_both0 (usize 5)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_5_v)))) in
      letb yden_k_2399 : seq fp_t :=
        seq_upd yden_k_2399 (lift_to_both0 (usize 6)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_6_v)))) in
      letb yden_k_2399 : seq fp_t :=
        seq_upd yden_k_2399 (lift_to_both0 (usize 7)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_7_v)))) in
      letb yden_k_2399 : seq fp_t :=
        seq_upd yden_k_2399 (lift_to_both0 (usize 8)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_8_v)))) in
      letb yden_k_2399 : seq fp_t :=
        seq_upd yden_k_2399 (lift_to_both0 (usize 9)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_9_v)))) in
      letb yden_k_2399 : seq fp_t :=
        seq_upd yden_k_2399 (lift_to_both0 (usize 10)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_10_v)))) in
      letb yden_k_2399 : seq fp_t :=
        seq_upd yden_k_2399 (lift_to_both0 (usize 11)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_11_v)))) in
      letb yden_k_2399 : seq fp_t :=
        seq_upd yden_k_2399 (lift_to_both0 (usize 12)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_12_v)))) in
      letb yden_k_2399 : seq fp_t :=
        seq_upd yden_k_2399 (lift_to_both0 (usize 13)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_13_v)))) in
      letb yden_k_2399 : seq fp_t :=
        seq_upd yden_k_2399 (lift_to_both0 (usize 14)) (is_pure (
            nat_mod_from_byte_seq_be (array_to_be_bytes (
                lift_to_both0 g1_yden_k_14_v)))) in
      letbm xnum_2400 : fp_t loc( xnum_2400_loc ) := nat_mod_zero  in
      letbm xx_2401 : fp_t loc( xx_2401_loc ) := nat_mod_one  in
      letb '(xnum_2400, xx_2401) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 xnum_k_2396)) prod_ce(xnum_2400, xx_2401) (L := (
              CEfset (
                [xnum_k_2396_loc ; xden_k_2397_loc ; ynum_k_2398_loc ; yden_k_2399_loc ; xnum_2400_loc ; xx_2401_loc ; xden_2402_loc ; xx_2403_loc ; ynum_2404_loc ; xx_2405_loc ; yden_2406_loc ; xx_2407_loc ; inf_2408_loc]))) (
            I := [interface]) (fun i_2422 '(xnum_2400, xx_2401) =>
            letbm xnum_2400 loc( xnum_2400_loc ) :=
              (lift_to_both0 xnum_2400) +% ((lift_to_both0 xx_2401) *% (
                  seq_index (xnum_k_2396) (lift_to_both0 i_2422))) in
            letbm xx_2401 loc( xx_2401_loc ) :=
              (lift_to_both0 xx_2401) *% (lift_to_both0 x_2423) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 xnum_2400,
                lift_to_both0 xx_2401
              ))
            ) in
      letbm xden_2402 : fp_t loc( xden_2402_loc ) := nat_mod_zero  in
      letbm xx_2403 : fp_t loc( xx_2403_loc ) := nat_mod_one  in
      letb '(xden_2402, xx_2403) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 xden_k_2397)) prod_ce(xden_2402, xx_2403) (L := (
              CEfset (
                [xnum_k_2396_loc ; xden_k_2397_loc ; ynum_k_2398_loc ; yden_k_2399_loc ; xnum_2400_loc ; xx_2401_loc ; xden_2402_loc ; xx_2403_loc ; ynum_2404_loc ; xx_2405_loc ; yden_2406_loc ; xx_2407_loc ; inf_2408_loc]))) (
            I := [interface]) (fun i_2424 '(xden_2402, xx_2403) =>
            letbm xden_2402 loc( xden_2402_loc ) :=
              (lift_to_both0 xden_2402) +% ((lift_to_both0 xx_2403) *% (
                  seq_index (xden_k_2397) (lift_to_both0 i_2424))) in
            letbm xx_2403 loc( xx_2403_loc ) :=
              (lift_to_both0 xx_2403) *% (lift_to_both0 x_2423) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 xden_2402,
                lift_to_both0 xx_2403
              ))
            ) in
      letbm xden_2402 loc( xden_2402_loc ) :=
        (lift_to_both0 xden_2402) +% (lift_to_both0 xx_2403) in
      letbm ynum_2404 : fp_t loc( ynum_2404_loc ) := nat_mod_zero  in
      letbm xx_2405 : fp_t loc( xx_2405_loc ) := nat_mod_one  in
      letb '(ynum_2404, xx_2405) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 ynum_k_2398)) prod_ce(ynum_2404, xx_2405) (L := (
              CEfset (
                [xnum_k_2396_loc ; xden_k_2397_loc ; ynum_k_2398_loc ; yden_k_2399_loc ; xnum_2400_loc ; xx_2401_loc ; xden_2402_loc ; xx_2403_loc ; ynum_2404_loc ; xx_2405_loc ; yden_2406_loc ; xx_2407_loc ; inf_2408_loc]))) (
            I := [interface]) (fun i_2425 '(ynum_2404, xx_2405) =>
            letbm ynum_2404 loc( ynum_2404_loc ) :=
              (lift_to_both0 ynum_2404) +% ((lift_to_both0 xx_2405) *% (
                  seq_index (ynum_k_2398) (lift_to_both0 i_2425))) in
            letbm xx_2405 loc( xx_2405_loc ) :=
              (lift_to_both0 xx_2405) *% (lift_to_both0 x_2423) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 ynum_2404,
                lift_to_both0 xx_2405
              ))
            ) in
      letbm yden_2406 : fp_t loc( yden_2406_loc ) := nat_mod_zero  in
      letbm xx_2407 : fp_t loc( xx_2407_loc ) := nat_mod_one  in
      letb '(yden_2406, xx_2407) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 yden_k_2399)) prod_ce(yden_2406, xx_2407) (L := (
              CEfset (
                [xnum_k_2396_loc ; xden_k_2397_loc ; ynum_k_2398_loc ; yden_k_2399_loc ; xnum_2400_loc ; xx_2401_loc ; xden_2402_loc ; xx_2403_loc ; ynum_2404_loc ; xx_2405_loc ; yden_2406_loc ; xx_2407_loc ; inf_2408_loc]))) (
            I := [interface]) (fun i_2426 '(yden_2406, xx_2407) =>
            letbm yden_2406 loc( yden_2406_loc ) :=
              (lift_to_both0 yden_2406) +% ((lift_to_both0 xx_2407) *% (
                  seq_index (yden_k_2399) (lift_to_both0 i_2426))) in
            letbm xx_2407 loc( xx_2407_loc ) :=
              (lift_to_both0 xx_2407) *% (lift_to_both0 x_2423) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 yden_2406,
                lift_to_both0 xx_2407
              ))
            ) in
      letbm yden_2406 loc( yden_2406_loc ) :=
        (lift_to_both0 yden_2406) +% (lift_to_both0 xx_2407) in
      letb xr_2427 : fp_t :=
        (lift_to_both0 xnum_2400) *% (nat_mod_inv (lift_to_both0 xden_2402)) in
      letb yr_2429 : fp_t :=
        ((lift_to_both0 y_2428) *% (lift_to_both0 ynum_2404)) *% (nat_mod_inv (
            lift_to_both0 yden_2406)) in
      letbm inf_2408 : bool_ChoiceEquality loc( inf_2408_loc ) :=
        lift_to_both0 ((false : bool_ChoiceEquality)) in
      letb '(inf_2408) :=
        if ((lift_to_both0 xden_2402) =.? (nat_mod_zero )) || ((
            lift_to_both0 yden_2406) =.? (nat_mod_zero )) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [xnum_k_2396_loc ; xden_k_2397_loc ; ynum_k_2398_loc ; yden_k_2399_loc ; xnum_2400_loc ; xx_2401_loc ; xden_2402_loc ; xx_2403_loc ; ynum_2404_loc ; xx_2405_loc ; yden_2406_loc ; xx_2407_loc ; inf_2408_loc])) (
          L2 := CEfset (
            [xnum_k_2396_loc ; xden_k_2397_loc ; ynum_k_2398_loc ; yden_k_2399_loc ; xnum_2400_loc ; xx_2401_loc ; xden_2402_loc ; xx_2403_loc ; ynum_2404_loc ; xx_2405_loc ; yden_2406_loc ; xx_2407_loc ; inf_2408_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm inf_2408 loc( inf_2408_loc ) :=
            lift_to_both0 ((true : bool_ChoiceEquality)) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 inf_2408)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 inf_2408)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 xr_2427,
          lift_to_both0 yr_2429,
          lift_to_both0 inf_2408
        ))
      ) : both (CEfset (
        [xnum_k_2396_loc ; xden_k_2397_loc ; ynum_k_2398_loc ; yden_k_2399_loc ; xnum_2400_loc ; xx_2401_loc ; xden_2402_loc ; xx_2403_loc ; ynum_2404_loc ; xx_2405_loc ; yden_2406_loc ; xx_2407_loc ; inf_2408_loc])) [interface] (
      g1_t)).
Fail Next Obligation.


Notation "'g1_map_to_curve_sswu_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_map_to_curve_sswu_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'g1_map_to_curve_sswu_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_map_to_curve_sswu_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1_MAP_TO_CURVE_SSWU : nat :=
  2435.
Program Definition g1_map_to_curve_sswu (u_2431 : fp_t)
  : both (CEfset (
      [x1_2382_loc ; y_2383_loc ; xnum_k_2396_loc ; xden_k_2397_loc ; ynum_k_2398_loc ; yden_k_2399_loc ; xnum_2400_loc ; xx_2401_loc ; xden_2402_loc ; xx_2403_loc ; ynum_2404_loc ; xx_2405_loc ; yden_2406_loc ; xx_2407_loc ; inf_2408_loc])) [interface] (
    g1_t) :=
  ((letb '(xp_2432, yp_2433) : (fp_t '× fp_t) :=
        g1_simple_swu_iso (lift_to_both0 u_2431) in
      letb p_2434 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_isogeny_map (lift_to_both0 xp_2432) (lift_to_both0 yp_2433) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2434)
      ) : both (CEfset (
        [x1_2382_loc ; y_2383_loc ; xnum_k_2396_loc ; xden_k_2397_loc ; ynum_k_2398_loc ; yden_k_2399_loc ; xnum_2400_loc ; xx_2401_loc ; xden_2402_loc ; xx_2403_loc ; ynum_2404_loc ; xx_2405_loc ; yden_2406_loc ; xx_2407_loc ; inf_2408_loc])) [interface] (
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
  2443.
Program Definition g1_hash_to_curve_sswu (msg_2436 : byte_seq) (
    dst_2437 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2201_loc ; b_i_2202_loc ; uniform_bytes_2203_loc ; output_2218_loc ; x1_2382_loc ; y_2383_loc ; xnum_k_2396_loc ; xden_k_2397_loc ; ynum_k_2398_loc ; yden_k_2399_loc ; xnum_2400_loc ; xx_2401_loc ; xden_2402_loc ; xx_2403_loc ; ynum_2404_loc ; xx_2405_loc ; yden_2406_loc ; xx_2407_loc ; inf_2408_loc])) [interface] (
    g1_t) :=
  ((letb u_2438 : seq fp_t :=
        fp_hash_to_field (lift_to_both0 msg_2436) (lift_to_both0 dst_2437) (
          lift_to_both0 (usize 2)) in
      letb q0_2439 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_map_to_curve_sswu (seq_index (u_2438) (lift_to_both0 (usize 0))) in
      letb q1_2440 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_map_to_curve_sswu (seq_index (u_2438) (lift_to_both0 (usize 1))) in
      letb r_2441 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1add (lift_to_both0 q0_2439) (lift_to_both0 q1_2440) in
      letb p_2442 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_clear_cofactor (lift_to_both0 r_2441) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2442)
      ) : both (CEfset (
        [l_i_b_str_2201_loc ; b_i_2202_loc ; uniform_bytes_2203_loc ; output_2218_loc ; x1_2382_loc ; y_2383_loc ; xnum_k_2396_loc ; xden_k_2397_loc ; ynum_k_2398_loc ; yden_k_2399_loc ; xnum_2400_loc ; xx_2401_loc ; xden_2402_loc ; xx_2403_loc ; ynum_2404_loc ; xx_2405_loc ; yden_2406_loc ; xx_2407_loc ; inf_2408_loc])) [interface] (
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
  2449.
Program Definition g1_encode_to_curve_sswu (msg_2444 : byte_seq) (
    dst_2445 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2201_loc ; b_i_2202_loc ; uniform_bytes_2203_loc ; output_2218_loc ; x1_2382_loc ; y_2383_loc ; xnum_k_2396_loc ; xden_k_2397_loc ; ynum_k_2398_loc ; yden_k_2399_loc ; xnum_2400_loc ; xx_2401_loc ; xden_2402_loc ; xx_2403_loc ; ynum_2404_loc ; xx_2405_loc ; yden_2406_loc ; xx_2407_loc ; inf_2408_loc])) [interface] (
    g1_t) :=
  ((letb u_2446 : seq fp_t :=
        fp_hash_to_field (lift_to_both0 msg_2444) (lift_to_both0 dst_2445) (
          lift_to_both0 (usize 1)) in
      letb q_2447 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_map_to_curve_sswu (seq_index (u_2446) (lift_to_both0 (usize 0))) in
      letb p_2448 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
        g1_clear_cofactor (lift_to_both0 q_2447) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2448)
      ) : both (CEfset (
        [l_i_b_str_2201_loc ; b_i_2202_loc ; uniform_bytes_2203_loc ; output_2218_loc ; x1_2382_loc ; y_2383_loc ; xnum_k_2396_loc ; xden_k_2397_loc ; ynum_k_2398_loc ; yden_k_2399_loc ; xnum_2400_loc ; xx_2401_loc ; xden_2402_loc ; xx_2403_loc ; ynum_2404_loc ; xx_2405_loc ; yden_2406_loc ; xx_2407_loc ; inf_2408_loc])) [interface] (
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

Definition x1_2450_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2452%nat).
Definition y_2451_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2453%nat).
Notation "'g2_simple_swu_iso_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_simple_swu_iso_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'g2_simple_swu_iso_out'" :=((fp2_t '× fp2_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'g2_simple_swu_iso_out'" :=((fp2_t '× fp2_t
  ) : ChoiceEquality) (at level 2).
Definition G2_SIMPLE_SWU_ISO : nat :=
  2463.
Program Definition g2_simple_swu_iso (u_2457 : fp2_t)
  : both (CEfset ([c_2308_loc ; x1_2450_loc ; y_2451_loc])) [interface] ((
      fp2_t '×
      fp2_t
    )) :=
  ((letb z_2454 : (fp_t '× fp_t) :=
        fp2neg (prod_b(nat_mod_two , nat_mod_one )) in
      letb a_2455 : (fp_t '× fp_t) :=
        prod_b(
          nat_mod_zero ,
          nat_mod_from_literal (_) (lift_to_both0 (@repr U128 240))
        ) in
      letb b_2456 : (fp_t '× fp_t) :=
        prod_b(
          nat_mod_from_literal (_) (lift_to_both0 (@repr U128 1012)),
          nat_mod_from_literal (_) (lift_to_both0 (@repr U128 1012))
        ) in
      letb tv1_2458 : (fp_t '× fp_t) :=
        fp2inv (fp2add (fp2mul (fp2mul (lift_to_both0 z_2454) (
                lift_to_both0 z_2454)) (fp2mul (fp2mul (lift_to_both0 u_2457) (
                  lift_to_both0 u_2457)) (fp2mul (lift_to_both0 u_2457) (
                  lift_to_both0 u_2457)))) (fp2mul (lift_to_both0 z_2454) (
              fp2mul (lift_to_both0 u_2457) (lift_to_both0 u_2457)))) in
      letbm x1_2450 : (fp_t '× fp_t) loc( x1_2450_loc ) :=
        fp2mul (fp2mul (fp2neg (lift_to_both0 b_2456)) (fp2inv (
              lift_to_both0 a_2455))) (fp2add (fp2fromfp (nat_mod_one )) (
            lift_to_both0 tv1_2458)) in
      letb '(x1_2450) :=
        if (lift_to_both0 tv1_2458) =.? (fp2zero ) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([x1_2450_loc])) (L2 := CEfset (
            [c_2308_loc ; x1_2450_loc ; y_2451_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x1_2450 loc( x1_2450_loc ) :=
            fp2mul (lift_to_both0 b_2456) (fp2inv (fp2mul (
                  lift_to_both0 z_2454) (lift_to_both0 a_2455))) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 x1_2450)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 x1_2450)
         in
      letb gx1_2459 : (fp_t '× fp_t) :=
        fp2add (fp2add (fp2mul (fp2mul (lift_to_both0 x1_2450) (
                lift_to_both0 x1_2450)) (lift_to_both0 x1_2450)) (fp2mul (
              lift_to_both0 a_2455) (lift_to_both0 x1_2450))) (
          lift_to_both0 b_2456) in
      letb x2_2460 : (fp_t '× fp_t) :=
        fp2mul (fp2mul (lift_to_both0 z_2454) (fp2mul (lift_to_both0 u_2457) (
              lift_to_both0 u_2457))) (lift_to_both0 x1_2450) in
      letb gx2_2461 : (fp_t '× fp_t) :=
        fp2add (fp2add (fp2mul (fp2mul (lift_to_both0 x2_2460) (
                lift_to_both0 x2_2460)) (lift_to_both0 x2_2460)) (fp2mul (
              lift_to_both0 a_2455) (lift_to_both0 x2_2460))) (
          lift_to_both0 b_2456) in
      letb '(x_2462, y_2451) : ((fp_t '× fp_t) '× fp2_t) :=
        if is_pure (I := [interface]) (fp2_is_square (lift_to_both0 gx1_2459))
        then prod_b(lift_to_both0 x1_2450, fp2_sqrt (lift_to_both0 gx1_2459))
        else prod_b(lift_to_both0 x2_2460, fp2_sqrt (lift_to_both0 gx2_2461)) in
      letb '(y_2451) :=
        if (fp2_sgn0 (lift_to_both0 u_2457)) !=.? (fp2_sgn0 (
            lift_to_both0 y_2451)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [c_2308_loc ; x1_2450_loc ; y_2451_loc])) (L2 := CEfset (
            [c_2308_loc ; x1_2450_loc ; y_2451_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm y_2451 loc( y_2451_loc ) := fp2neg (lift_to_both0 y_2451) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 y_2451)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 y_2451)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_2462,
          lift_to_both0 y_2451
        ))
      ) : both (CEfset ([c_2308_loc ; x1_2450_loc ; y_2451_loc])) [interface] ((
        fp2_t '×
        fp2_t
      ))).
Fail Next Obligation.

Definition xnum_2468_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2477%nat).
Definition xnum_k_2464_loc : ChoiceEqualityLocation :=
  (seq (fp_t '× fp_t) ; 2478%nat).
Definition xden_k_2465_loc : ChoiceEqualityLocation :=
  (seq (fp_t '× fp_t) ; 2479%nat).
Definition yden_2474_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2480%nat).
Definition ynum_2472_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2481%nat).
Definition xx_2473_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2482%nat).
Definition xden_2470_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2483%nat).
Definition yden_k_2467_loc : ChoiceEqualityLocation :=
  (seq (fp_t '× fp_t) ; 2484%nat).
Definition inf_2476_loc : ChoiceEqualityLocation :=
  (bool_ChoiceEquality ; 2485%nat).
Definition xx_2471_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2486%nat).
Definition xx_2469_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2487%nat).
Definition xx_2475_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2488%nat).
Definition ynum_k_2466_loc : ChoiceEqualityLocation :=
  (seq (fp_t '× fp_t) ; 2489%nat).
Notation "'g2_isogeny_map_inp'" :=(
  fp2_t '× fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_isogeny_map_inp'" :=(
  fp2_t '× fp2_t : ChoiceEquality) (at level 2).
Notation "'g2_isogeny_map_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_isogeny_map_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_ISOGENY_MAP : nat :=
  2498.
Program Definition g2_isogeny_map (x_2491 : fp2_t) (y_2496 : fp2_t)
  : both (CEfset (
      [xnum_k_2464_loc ; xden_k_2465_loc ; ynum_k_2466_loc ; yden_k_2467_loc ; xnum_2468_loc ; xx_2469_loc ; xden_2470_loc ; xx_2471_loc ; ynum_2472_loc ; xx_2473_loc ; yden_2474_loc ; xx_2475_loc ; inf_2476_loc])) [interface] (
    g2_t) :=
  ((letbm xnum_k_2464 : seq (fp_t '× fp_t) loc( xnum_k_2464_loc ) :=
        seq_new_ (default : fp2_t) (lift_to_both0 (usize 4)) in
      letb xnum_k_2464 : seq (fp_t '× fp_t) :=
        seq_upd xnum_k_2464 (lift_to_both0 (usize 0)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xnum_k_0_v)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xnum_k_0_v))
            ))) in
      letb xnum_k_2464 : seq (fp_t '× fp_t) :=
        seq_upd xnum_k_2464 (lift_to_both0 (usize 1)) (is_pure (prod_b(
              nat_mod_zero ,
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xnum_k_1_i_v))
            ))) in
      letb xnum_k_2464 : seq (fp_t '× fp_t) :=
        seq_upd xnum_k_2464 (lift_to_both0 (usize 2)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xnum_k_2_r_v)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xnum_k_2_i_v))
            ))) in
      letb xnum_k_2464 : seq (fp_t '× fp_t) :=
        seq_upd xnum_k_2464 (lift_to_both0 (usize 3)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xnum_k_3_r_v)),
              nat_mod_zero 
            ))) in
      letbm xden_k_2465 : seq (fp_t '× fp_t) loc( xden_k_2465_loc ) :=
        seq_new_ (default : fp2_t) (lift_to_both0 (usize 2)) in
      letb xden_k_2465 : seq (fp_t '× fp_t) :=
        seq_upd xden_k_2465 (lift_to_both0 (usize 0)) (is_pure (prod_b(
              nat_mod_zero ,
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xden_k_0_i_v))
            ))) in
      letb xden_k_2465 : seq (fp_t '× fp_t) :=
        seq_upd xden_k_2465 (lift_to_both0 (usize 1)) (is_pure (prod_b(
              nat_mod_from_literal (_) (lift_to_both0 (@repr U128 12)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_xden_k_1_i_v))
            ))) in
      letbm ynum_k_2466 : seq (fp_t '× fp_t) loc( ynum_k_2466_loc ) :=
        seq_new_ (default : fp2_t) (lift_to_both0 (usize 4)) in
      letb ynum_k_2466 : seq (fp_t '× fp_t) :=
        seq_upd ynum_k_2466 (lift_to_both0 (usize 0)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_ynum_k_0_v)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_ynum_k_0_v))
            ))) in
      letb ynum_k_2466 : seq (fp_t '× fp_t) :=
        seq_upd ynum_k_2466 (lift_to_both0 (usize 1)) (is_pure (prod_b(
              nat_mod_zero ,
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_ynum_k_1_i_v))
            ))) in
      letb ynum_k_2466 : seq (fp_t '× fp_t) :=
        seq_upd ynum_k_2466 (lift_to_both0 (usize 2)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_ynum_k_2_r_v)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_ynum_k_2_i_v))
            ))) in
      letb ynum_k_2466 : seq (fp_t '× fp_t) :=
        seq_upd ynum_k_2466 (lift_to_both0 (usize 3)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_ynum_k_3_r_v)),
              nat_mod_zero 
            ))) in
      letbm yden_k_2467 : seq (fp_t '× fp_t) loc( yden_k_2467_loc ) :=
        seq_new_ (default : fp2_t) (lift_to_both0 (usize 3)) in
      letb yden_k_2467 : seq (fp_t '× fp_t) :=
        seq_upd yden_k_2467 (lift_to_both0 (usize 0)) (is_pure (prod_b(
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_yden_k_0_v)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_yden_k_0_v))
            ))) in
      letb yden_k_2467 : seq (fp_t '× fp_t) :=
        seq_upd yden_k_2467 (lift_to_both0 (usize 1)) (is_pure (prod_b(
              nat_mod_zero ,
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_yden_k_1_i_v))
            ))) in
      letb yden_k_2467 : seq (fp_t '× fp_t) :=
        seq_upd yden_k_2467 (lift_to_both0 (usize 2)) (is_pure (prod_b(
              nat_mod_from_literal (_) (lift_to_both0 (@repr U128 18)),
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g2_yden_k_2_i_v))
            ))) in
      letbm xnum_2468 : (fp_t '× fp_t) loc( xnum_2468_loc ) := fp2zero  in
      letbm xx_2469 : (fp_t '× fp_t) loc( xx_2469_loc ) :=
        fp2fromfp (nat_mod_one ) in
      letb '(xnum_2468, xx_2469) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 xnum_k_2464)) prod_ce(xnum_2468, xx_2469) (L := (
              CEfset (
                [xnum_k_2464_loc ; xden_k_2465_loc ; ynum_k_2466_loc ; yden_k_2467_loc ; xnum_2468_loc ; xx_2469_loc ; xden_2470_loc ; xx_2471_loc ; ynum_2472_loc ; xx_2473_loc ; yden_2474_loc ; xx_2475_loc ; inf_2476_loc]))) (
            I := [interface]) (fun i_2490 '(xnum_2468, xx_2469) =>
            letbm xnum_2468 loc( xnum_2468_loc ) :=
              fp2add (lift_to_both0 xnum_2468) (fp2mul (lift_to_both0 xx_2469) (
                  seq_index (xnum_k_2464) (lift_to_both0 i_2490))) in
            letbm xx_2469 loc( xx_2469_loc ) :=
              fp2mul (lift_to_both0 xx_2469) (lift_to_both0 x_2491) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 xnum_2468,
                lift_to_both0 xx_2469
              ))
            ) in
      letbm xden_2470 : (fp_t '× fp_t) loc( xden_2470_loc ) := fp2zero  in
      letbm xx_2471 : (fp_t '× fp_t) loc( xx_2471_loc ) :=
        fp2fromfp (nat_mod_one ) in
      letb '(xden_2470, xx_2471) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 xden_k_2465)) prod_ce(xden_2470, xx_2471) (L := (
              CEfset (
                [xnum_k_2464_loc ; xden_k_2465_loc ; ynum_k_2466_loc ; yden_k_2467_loc ; xnum_2468_loc ; xx_2469_loc ; xden_2470_loc ; xx_2471_loc ; ynum_2472_loc ; xx_2473_loc ; yden_2474_loc ; xx_2475_loc ; inf_2476_loc]))) (
            I := [interface]) (fun i_2492 '(xden_2470, xx_2471) =>
            letbm xden_2470 loc( xden_2470_loc ) :=
              fp2add (lift_to_both0 xden_2470) (fp2mul (lift_to_both0 xx_2471) (
                  seq_index (xden_k_2465) (lift_to_both0 i_2492))) in
            letbm xx_2471 loc( xx_2471_loc ) :=
              fp2mul (lift_to_both0 xx_2471) (lift_to_both0 x_2491) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 xden_2470,
                lift_to_both0 xx_2471
              ))
            ) in
      letbm xden_2470 loc( xden_2470_loc ) :=
        fp2add (lift_to_both0 xden_2470) (lift_to_both0 xx_2471) in
      letbm ynum_2472 : (fp_t '× fp_t) loc( ynum_2472_loc ) := fp2zero  in
      letbm xx_2473 : (fp_t '× fp_t) loc( xx_2473_loc ) :=
        fp2fromfp (nat_mod_one ) in
      letb '(ynum_2472, xx_2473) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 ynum_k_2466)) prod_ce(ynum_2472, xx_2473) (L := (
              CEfset (
                [xnum_k_2464_loc ; xden_k_2465_loc ; ynum_k_2466_loc ; yden_k_2467_loc ; xnum_2468_loc ; xx_2469_loc ; xden_2470_loc ; xx_2471_loc ; ynum_2472_loc ; xx_2473_loc ; yden_2474_loc ; xx_2475_loc ; inf_2476_loc]))) (
            I := [interface]) (fun i_2493 '(ynum_2472, xx_2473) =>
            letbm ynum_2472 loc( ynum_2472_loc ) :=
              fp2add (lift_to_both0 ynum_2472) (fp2mul (lift_to_both0 xx_2473) (
                  seq_index (ynum_k_2466) (lift_to_both0 i_2493))) in
            letbm xx_2473 loc( xx_2473_loc ) :=
              fp2mul (lift_to_both0 xx_2473) (lift_to_both0 x_2491) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 ynum_2472,
                lift_to_both0 xx_2473
              ))
            ) in
      letbm yden_2474 : (fp_t '× fp_t) loc( yden_2474_loc ) := fp2zero  in
      letbm xx_2475 : (fp_t '× fp_t) loc( xx_2475_loc ) :=
        fp2fromfp (nat_mod_one ) in
      letb '(yden_2474, xx_2475) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 yden_k_2467)) prod_ce(yden_2474, xx_2475) (L := (
              CEfset (
                [xnum_k_2464_loc ; xden_k_2465_loc ; ynum_k_2466_loc ; yden_k_2467_loc ; xnum_2468_loc ; xx_2469_loc ; xden_2470_loc ; xx_2471_loc ; ynum_2472_loc ; xx_2473_loc ; yden_2474_loc ; xx_2475_loc ; inf_2476_loc]))) (
            I := [interface]) (fun i_2494 '(yden_2474, xx_2475) =>
            letbm yden_2474 loc( yden_2474_loc ) :=
              fp2add (lift_to_both0 yden_2474) (fp2mul (lift_to_both0 xx_2475) (
                  seq_index (yden_k_2467) (lift_to_both0 i_2494))) in
            letbm xx_2475 loc( xx_2475_loc ) :=
              fp2mul (lift_to_both0 xx_2475) (lift_to_both0 x_2491) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 yden_2474,
                lift_to_both0 xx_2475
              ))
            ) in
      letbm yden_2474 loc( yden_2474_loc ) :=
        fp2add (lift_to_both0 yden_2474) (lift_to_both0 xx_2475) in
      letb xr_2495 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 xnum_2468) (fp2inv (lift_to_both0 xden_2470)) in
      letb yr_2497 : (fp_t '× fp_t) :=
        fp2mul (lift_to_both0 y_2496) (fp2mul (lift_to_both0 ynum_2472) (
            fp2inv (lift_to_both0 yden_2474))) in
      letbm inf_2476 : bool_ChoiceEquality loc( inf_2476_loc ) :=
        lift_to_both0 ((false : bool_ChoiceEquality)) in
      letb '(inf_2476) :=
        if ((lift_to_both0 xden_2470) =.? (fp2zero )) || ((
            lift_to_both0 yden_2474) =.? (fp2zero )) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [xnum_k_2464_loc ; xden_k_2465_loc ; ynum_k_2466_loc ; yden_k_2467_loc ; xnum_2468_loc ; xx_2469_loc ; xden_2470_loc ; xx_2471_loc ; ynum_2472_loc ; xx_2473_loc ; yden_2474_loc ; xx_2475_loc ; inf_2476_loc])) (
          L2 := CEfset (
            [xnum_k_2464_loc ; xden_k_2465_loc ; ynum_k_2466_loc ; yden_k_2467_loc ; xnum_2468_loc ; xx_2469_loc ; xden_2470_loc ; xx_2471_loc ; ynum_2472_loc ; xx_2473_loc ; yden_2474_loc ; xx_2475_loc ; inf_2476_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm inf_2476 loc( inf_2476_loc ) :=
            lift_to_both0 ((true : bool_ChoiceEquality)) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 inf_2476)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 inf_2476)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 xr_2495,
          lift_to_both0 yr_2497,
          lift_to_both0 inf_2476
        ))
      ) : both (CEfset (
        [xnum_k_2464_loc ; xden_k_2465_loc ; ynum_k_2466_loc ; yden_k_2467_loc ; xnum_2468_loc ; xx_2469_loc ; xden_2470_loc ; xx_2471_loc ; ynum_2472_loc ; xx_2473_loc ; yden_2474_loc ; xx_2475_loc ; inf_2476_loc])) [interface] (
      g2_t)).
Fail Next Obligation.


Notation "'g2_map_to_curve_sswu_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_map_to_curve_sswu_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'g2_map_to_curve_sswu_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_map_to_curve_sswu_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_MAP_TO_CURVE_SSWU : nat :=
  2503.
Program Definition g2_map_to_curve_sswu (u_2499 : fp2_t)
  : both (CEfset (
      [c_2308_loc ; x1_2450_loc ; y_2451_loc ; xnum_k_2464_loc ; xden_k_2465_loc ; ynum_k_2466_loc ; yden_k_2467_loc ; xnum_2468_loc ; xx_2469_loc ; xden_2470_loc ; xx_2471_loc ; ynum_2472_loc ; xx_2473_loc ; yden_2474_loc ; xx_2475_loc ; inf_2476_loc])) [interface] (
    g2_t) :=
  ((letb '(xp_2500, yp_2501) : (fp2_t '× fp2_t) :=
        g2_simple_swu_iso (lift_to_both0 u_2499) in
      letb p_2502 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_isogeny_map (lift_to_both0 xp_2500) (lift_to_both0 yp_2501) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2502)
      ) : both (CEfset (
        [c_2308_loc ; x1_2450_loc ; y_2451_loc ; xnum_k_2464_loc ; xden_k_2465_loc ; ynum_k_2466_loc ; yden_k_2467_loc ; xnum_2468_loc ; xx_2469_loc ; xden_2470_loc ; xx_2471_loc ; ynum_2472_loc ; xx_2473_loc ; yden_2474_loc ; xx_2475_loc ; inf_2476_loc])) [interface] (
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
  2511.
Program Definition g2_hash_to_curve_sswu (msg_2504 : byte_seq) (
    dst_2505 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2201_loc ; b_i_2202_loc ; uniform_bytes_2203_loc ; output_2276_loc ; c_2308_loc ; x1_2450_loc ; y_2451_loc ; xnum_k_2464_loc ; xden_k_2465_loc ; ynum_k_2466_loc ; yden_k_2467_loc ; xnum_2468_loc ; xx_2469_loc ; xden_2470_loc ; xx_2471_loc ; ynum_2472_loc ; xx_2473_loc ; yden_2474_loc ; xx_2475_loc ; inf_2476_loc])) [interface] (
    g2_t) :=
  ((letb u_2506 : seq fp2_t :=
        fp2_hash_to_field (lift_to_both0 msg_2504) (lift_to_both0 dst_2505) (
          lift_to_both0 (usize 2)) in
      letb q0_2507 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2_map_to_curve_sswu (seq_index (u_2506) (lift_to_both0 (usize 0))) in
      letb q1_2508 : (
          (fp_t '× fp_t) '×
          (fp_t '× fp_t) '×
          bool_ChoiceEquality
        ) :=
        g2_map_to_curve_sswu (seq_index (u_2506) (lift_to_both0 (usize 1))) in
      letb r_2509 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2add (lift_to_both0 q0_2507) (lift_to_both0 q1_2508) in
      letb p_2510 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_clear_cofactor (lift_to_both0 r_2509) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2510)
      ) : both (CEfset (
        [l_i_b_str_2201_loc ; b_i_2202_loc ; uniform_bytes_2203_loc ; output_2276_loc ; c_2308_loc ; x1_2450_loc ; y_2451_loc ; xnum_k_2464_loc ; xden_k_2465_loc ; ynum_k_2466_loc ; yden_k_2467_loc ; xnum_2468_loc ; xx_2469_loc ; xden_2470_loc ; xx_2471_loc ; ynum_2472_loc ; xx_2473_loc ; yden_2474_loc ; xx_2475_loc ; inf_2476_loc])) [interface] (
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
  2517.
Program Definition g2_encode_to_curve_sswu (msg_2512 : byte_seq) (
    dst_2513 : byte_seq)
  : both (CEfset (
      [l_i_b_str_2201_loc ; b_i_2202_loc ; uniform_bytes_2203_loc ; output_2276_loc ; c_2308_loc ; x1_2450_loc ; y_2451_loc ; xnum_k_2464_loc ; xden_k_2465_loc ; ynum_k_2466_loc ; yden_k_2467_loc ; xnum_2468_loc ; xx_2469_loc ; xden_2470_loc ; xx_2471_loc ; ynum_2472_loc ; xx_2473_loc ; yden_2474_loc ; xx_2475_loc ; inf_2476_loc])) [interface] (
    g2_t) :=
  ((letb u_2514 : seq fp2_t :=
        fp2_hash_to_field (lift_to_both0 msg_2512) (lift_to_both0 dst_2513) (
          lift_to_both0 (usize 1)) in
      letb q_2515 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_map_to_curve_sswu (seq_index (u_2514) (lift_to_both0 (usize 0))) in
      letb p_2516 : ((fp_t '× fp_t) '× (fp_t '× fp_t) '× bool_ChoiceEquality
        ) :=
        g2_clear_cofactor (lift_to_both0 q_2515) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2516)
      ) : both (CEfset (
        [l_i_b_str_2201_loc ; b_i_2202_loc ; uniform_bytes_2203_loc ; output_2276_loc ; c_2308_loc ; x1_2450_loc ; y_2451_loc ; xnum_k_2464_loc ; xden_k_2465_loc ; ynum_k_2466_loc ; yden_k_2467_loc ; xnum_2468_loc ; xx_2469_loc ; xden_2470_loc ; xx_2471_loc ; ynum_2472_loc ; xx_2473_loc ; yden_2474_loc ; xx_2475_loc ; inf_2476_loc])) [interface] (
      g2_t)).
Fail Next Obligation.

