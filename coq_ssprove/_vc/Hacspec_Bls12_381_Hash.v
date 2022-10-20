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

Definition uniform_bytes_2083_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2084%nat).
Definition l_i_b_str_2081_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2085%nat).
Definition b_i_2082_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2086%nat).
Notation "'expand_message_xmd_inp'" :=(
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'expand_message_xmd_inp'" :=(
  byte_seq '× byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'expand_message_xmd_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'expand_message_xmd_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition EXPAND_MESSAGE_XMD : nat :=
  2097.
Program Definition expand_message_xmd
  : both_package (CEfset (
      [l_i_b_str_2081_loc ; b_i_2082_loc ; uniform_bytes_2083_loc])) [interface
  #val #[ HASH ] : hash_inp → hash_out ] [(EXPAND_MESSAGE_XMD,(
      expand_message_xmd_inp,expand_message_xmd_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      msg_2092 , dst_2089 , len_in_bytes_2087) := temp_inp : byte_seq '× byte_seq '× uint_size in
    
    let hash := fun x_0 => package_both hash (x_0) in
    ((letb ell_2088 : uint_size :=
          (((lift_to_both0 len_in_bytes_2087) .+ (
                lift_to_both0 b_in_bytes_v)) .- (lift_to_both0 (usize 1))) ./ (
            lift_to_both0 b_in_bytes_v) in
        letb dst_prime_2090 : seq uint8 :=
          seq_push (lift_to_both0 dst_2089) (uint8_from_usize (seq_len (
                lift_to_both0 dst_2089))) in
        letb z_pad_2091 : seq uint8 :=
          seq_new_ (default : uint8) (lift_to_both0 s_in_bytes_v) in
        letbm l_i_b_str_2081 : seq uint8 loc( l_i_b_str_2081_loc ) :=
          seq_new_ (default : uint8) (lift_to_both0 (usize 2)) in
        letb l_i_b_str_2081 : seq uint8 :=
          seq_upd l_i_b_str_2081 (lift_to_both0 (usize 0)) (is_pure (
              uint8_from_usize ((lift_to_both0 len_in_bytes_2087) ./ (
                  lift_to_both0 (usize 256))))) in
        letb l_i_b_str_2081 : seq uint8 :=
          seq_upd l_i_b_str_2081 (lift_to_both0 (usize 1)) (is_pure (
              uint8_from_usize (lift_to_both0 len_in_bytes_2087))) in
        letb msg_prime_2093 : seq uint8 :=
          seq_concat (seq_concat (seq_concat (seq_concat (
                  lift_to_both0 z_pad_2091) (lift_to_both0 msg_2092)) (
                lift_to_both0 l_i_b_str_2081)) (seq_new_ (default : uint8) (
                lift_to_both0 (usize 1)))) (lift_to_both0 dst_prime_2090) in
        letb b_0_2094 : seq uint8 :=
          seq_from_seq (array_to_seq (hash (lift_to_both0 msg_prime_2093))) in
        letbm b_i_2082 : seq uint8 loc( b_i_2082_loc ) :=
          seq_from_seq (array_to_seq (hash (seq_concat (seq_push (
                  lift_to_both0 b_0_2094) (secret (lift_to_both0 (
                      @repr U8 1)))) (lift_to_both0 dst_prime_2090)))) in
        letbm uniform_bytes_2083 : seq uint8 loc( uniform_bytes_2083_loc ) :=
          seq_from_seq (lift_to_both0 b_i_2082) in
        letb '(b_i_2082, uniform_bytes_2083) :=
          foldi_both' (lift_to_both0 (usize 2)) ((lift_to_both0 ell_2088) .+ (
                lift_to_both0 (usize 1))) prod_ce(b_i_2082, uniform_bytes_2083
            ) (L := (CEfset (
                [l_i_b_str_2081_loc ; b_i_2082_loc ; uniform_bytes_2083_loc]))) (I := (
              [interface #val #[ HASH ] : hash_inp → hash_out
              ])) (fun i_2095 '(b_i_2082, uniform_bytes_2083) =>
            letb t_2096 : seq uint8 := seq_from_seq (lift_to_both0 b_0_2094) in
            letbm b_i_2082 loc( b_i_2082_loc ) :=
              seq_from_seq (array_to_seq (hash (seq_concat (seq_push ((
                        lift_to_both0 t_2096) seq_xor (
                        lift_to_both0 b_i_2082)) (uint8_from_usize (
                        lift_to_both0 i_2095))) (
                    lift_to_both0 dst_prime_2090)))) in
            letbm uniform_bytes_2083 loc( uniform_bytes_2083_loc ) :=
              seq_concat (lift_to_both0 uniform_bytes_2083) (
                lift_to_both0 b_i_2082) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 b_i_2082,
                lift_to_both0 uniform_bytes_2083
              ))
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (seq_truncate (
            lift_to_both0 uniform_bytes_2083) (lift_to_both0 len_in_bytes_2087))
        ) : both (CEfset (
          [l_i_b_str_2081_loc ; b_i_2082_loc ; uniform_bytes_2083_loc])) [interface
      #val #[ HASH ] : hash_inp → hash_out ] (byte_seq)))in
  both_package' _ _ (EXPAND_MESSAGE_XMD,(
      expand_message_xmd_inp,expand_message_xmd_out)) temp_package_both.
Fail Next Obligation.

Definition output_2098_loc : ChoiceEqualityLocation :=
  (seq fp_t ; 2099%nat).
Notation "'fp_hash_to_field_inp'" :=(
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'fp_hash_to_field_inp'" :=(
  byte_seq '× byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'fp_hash_to_field_out'" :=(
  seq fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_hash_to_field_out'" :=(seq fp_t : ChoiceEquality) (at level 2).
Definition FP_HASH_TO_FIELD : nat :=
  2109.
Program Definition fp_hash_to_field
  : both_package (CEfset ([output_2098_loc])) [interface
  #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
  ] [(FP_HASH_TO_FIELD,(fp_hash_to_field_inp,fp_hash_to_field_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      msg_2102 , dst_2103 , count_2100) := temp_inp : byte_seq '× byte_seq '× uint_size in
    
    let expand_message_xmd := fun x_0 x_1 x_2 => package_both expand_message_xmd (
      x_0,x_1,x_2) in
    ((letb len_in_bytes_2101 : uint_size :=
          (lift_to_both0 count_2100) .* (lift_to_both0 l_v) in
        letb uniform_bytes_2104 : seq uint8 :=
          expand_message_xmd (lift_to_both0 msg_2102) (lift_to_both0 dst_2103) (
            lift_to_both0 len_in_bytes_2101) in
        letbm output_2098 : seq fp_t loc( output_2098_loc ) :=
          seq_new_ (default : fp_t) (lift_to_both0 count_2100) in
        letb output_2098 :=
          foldi_both' (lift_to_both0 (usize 0)) (
              lift_to_both0 count_2100) output_2098 (L := (CEfset (
                [output_2098_loc]))) (I := ([interface
              #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
              ])) (fun i_2105 output_2098 =>
            letb elm_offset_2106 : uint_size :=
              (lift_to_both0 l_v) .* (lift_to_both0 i_2105) in
            letb tv_2107 : seq uint8 :=
              seq_slice (lift_to_both0 uniform_bytes_2104) (
                lift_to_both0 elm_offset_2106) (lift_to_both0 l_v) in
            letb u_i_2108 : fp_t :=
              nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
                    nat_mod_from_byte_seq_be (lift_to_both0 tv_2107))) (
                  lift_to_both0 (usize 16)) (lift_to_both0 (usize 48))) in
            letb output_2098 : seq fp_t :=
              seq_upd output_2098 (lift_to_both0 i_2105) (is_pure (
                  lift_to_both0 u_i_2108)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 output_2098)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 output_2098)
        ) : both (CEfset ([output_2098_loc])) [interface
      #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
      ] (seq fp_t)))in
  both_package' _ _ (FP_HASH_TO_FIELD,(
      fp_hash_to_field_inp,fp_hash_to_field_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp_sgn0_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_sgn0_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'fp_sgn0_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'fp_sgn0_out'" :=(bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition FP_SGN0 : nat :=
  2111.
Program Definition fp_sgn0
  : both_package (fset.fset0) [interface] [(FP_SGN0,(
      fp_sgn0_inp,fp_sgn0_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_2110) := temp_inp : fp_t in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
              lift_to_both0 x_2110) rem (nat_mod_two )) =.? (nat_mod_one ))
        ) : both (fset.fset0) [interface] (bool_ChoiceEquality)))in
  both_package' _ _ (FP_SGN0,(fp_sgn0_inp,fp_sgn0_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp_is_square_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_is_square_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'fp_is_square_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'fp_is_square_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition FP_IS_SQUARE : nat :=
  2115.
Program Definition fp_is_square
  : both_package (fset.fset0) [interface] [(FP_IS_SQUARE,(
      fp_is_square_inp,fp_is_square_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_2113) := temp_inp : fp_t in
    
    ((letb c1_2112 : fp_t :=
          nat_mod_from_byte_seq_be (array_to_be_bytes (
              lift_to_both0 p_1_2_v)) in
        letb tv_2114 : fp_t :=
          nat_mod_pow_self (lift_to_both0 x_2113) (lift_to_both0 c1_2112) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
              lift_to_both0 tv_2114) =.? (nat_mod_zero )) || ((
              lift_to_both0 tv_2114) =.? (nat_mod_one )))
        ) : both (fset.fset0) [interface] (bool_ChoiceEquality)))in
  both_package' _ _ (FP_IS_SQUARE,(
      fp_is_square_inp,fp_is_square_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp_sqrt_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_sqrt_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'fp_sqrt_out'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp_sqrt_out'" :=(fp_t : ChoiceEquality) (at level 2).
Definition FP_SQRT : nat :=
  2118.
Program Definition fp_sqrt
  : both_package (fset.fset0) [interface] [(FP_SQRT,(
      fp_sqrt_inp,fp_sqrt_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_2117) := temp_inp : fp_t in
    
    ((letb c1_2116 : fp_t :=
          nat_mod_from_byte_seq_be (array_to_be_bytes (
              lift_to_both0 p_1_4_v)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (nat_mod_pow_self (
            lift_to_both0 x_2117) (lift_to_both0 c1_2116))
        ) : both (fset.fset0) [interface] (fp_t)))in
  both_package' _ _ (FP_SQRT,(fp_sqrt_inp,fp_sqrt_out)) temp_package_both.
Fail Next Obligation.


Notation "'g1_curve_func_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_curve_func_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'g1_curve_func_out'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_curve_func_out'" :=(fp_t : ChoiceEquality) (at level 2).
Definition G1_CURVE_FUNC : nat :=
  2120.
Program Definition g1_curve_func
  : both_package (fset.fset0) [interface] [(G1_CURVE_FUNC,(
      g1_curve_func_inp,g1_curve_func_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_2119) := temp_inp : fp_t in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((((
                lift_to_both0 x_2119) *% (lift_to_both0 x_2119)) *% (
              lift_to_both0 x_2119)) +% (nat_mod_from_literal (_) (
              lift_to_both0 (@repr U128 4))))
        ) : both (fset.fset0) [interface] (fp_t)))in
  both_package' _ _ (G1_CURVE_FUNC,(
      g1_curve_func_inp,g1_curve_func_out)) temp_package_both.
Fail Next Obligation.

Definition y_2122_loc : ChoiceEqualityLocation :=
  (fp_t ; 2123%nat).
Definition tv4_2121_loc : ChoiceEqualityLocation :=
  (fp_t ; 2124%nat).
Notation "'g1_map_to_curve_svdw_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_map_to_curve_svdw_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'g1_map_to_curve_svdw_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_map_to_curve_svdw_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1_MAP_TO_CURVE_SVDW : nat :=
  2138.
Program Definition g1_map_to_curve_svdw
  : both_package (CEfset ([tv4_2121_loc ; y_2122_loc])) [interface
  #val #[ FP_IS_SQUARE ] : fp_is_square_inp → fp_is_square_out ;
  #val #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out ;
  #val #[ FP_SQRT ] : fp_sqrt_inp → fp_sqrt_out ;
  #val #[ G1_CURVE_FUNC ] : g1_curve_func_inp → g1_curve_func_out ] [(
    G1_MAP_TO_CURVE_SVDW,(
      g1_map_to_curve_svdw_inp,g1_map_to_curve_svdw_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(u_2127) := temp_inp : fp_t in
    
    let fp_is_square := fun x_0 => package_both fp_is_square (x_0) in
    let fp_sgn0 := fun x_0 => package_both fp_sgn0 (x_0) in
    let fp_sqrt := fun x_0 => package_both fp_sqrt (x_0) in
    let g1_curve_func := fun x_0 => package_both g1_curve_func (x_0) in
    ((letb z_2125 : fp_t :=
          (nat_mod_zero ) -% (nat_mod_from_literal (_) (lift_to_both0 (
                @repr U128 3))) in
        letb gz_2126 : fp_t := g1_curve_func (lift_to_both0 z_2125) in
        letb tv1_2128 : fp_t :=
          ((lift_to_both0 u_2127) *% (lift_to_both0 u_2127)) *% (
            lift_to_both0 gz_2126) in
        letb tv2_2129 : fp_t := (nat_mod_one ) +% (lift_to_both0 tv1_2128) in
        letb tv1_2130 : fp_t := (nat_mod_one ) -% (lift_to_both0 tv1_2128) in
        letb tv3_2131 : fp_t :=
          nat_mod_inv ((lift_to_both0 tv1_2130) *% (lift_to_both0 tv2_2129)) in
        letbm tv4_2121 : fp_t loc( tv4_2121_loc ) :=
          fp_sqrt (((nat_mod_zero ) -% (lift_to_both0 gz_2126)) *% (((
                  nat_mod_from_literal (_) (lift_to_both0 (@repr U128 3))) *% (
                  lift_to_both0 z_2125)) *% (lift_to_both0 z_2125))) in
        letb 'tv4_2121 :=
          if fp_sgn0 (lift_to_both0 tv4_2121) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset ([tv4_2121_loc])) (L2 := CEfset (
            [tv4_2121_loc ; y_2122_loc])) (I1 := [interface]) (I2 := [interface
          #val #[ FP_IS_SQUARE ] : fp_is_square_inp → fp_is_square_out ;
          #val #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out ;
          #val #[ FP_SQRT ] : fp_sqrt_inp → fp_sqrt_out ;
          #val #[ G1_CURVE_FUNC ] : g1_curve_func_inp → g1_curve_func_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm tv4_2121 loc( tv4_2121_loc ) :=
              (nat_mod_zero ) -% (lift_to_both0 tv4_2121) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 tv4_2121)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 tv4_2121)
           in
        letb tv5_2132 : fp_t :=
          (((lift_to_both0 u_2127) *% (lift_to_both0 tv1_2130)) *% (
              lift_to_both0 tv3_2131)) *% (lift_to_both0 tv4_2121) in
        letb tv6_2133 : fp_t :=
          (((nat_mod_zero ) -% (nat_mod_from_literal (_) (lift_to_both0 (
                    @repr U128 4)))) *% (lift_to_both0 gz_2126)) *% (
            nat_mod_inv (((nat_mod_from_literal (_) (lift_to_both0 (
                      @repr U128 3))) *% (lift_to_both0 z_2125)) *% (
                lift_to_both0 z_2125))) in
        letb x1_2134 : fp_t :=
          (((nat_mod_zero ) -% (lift_to_both0 z_2125)) *% (nat_mod_inv (
                nat_mod_two ))) -% (lift_to_both0 tv5_2132) in
        letb x2_2135 : fp_t :=
          (((nat_mod_zero ) -% (lift_to_both0 z_2125)) *% (nat_mod_inv (
                nat_mod_two ))) +% (lift_to_both0 tv5_2132) in
        letb x3_2136 : fp_t :=
          (lift_to_both0 z_2125) +% (((lift_to_both0 tv6_2133) *% (((
                    lift_to_both0 tv2_2129) *% (lift_to_both0 tv2_2129)) *% (
                  lift_to_both0 tv3_2131))) *% (((lift_to_both0 tv2_2129) *% (
                  lift_to_both0 tv2_2129)) *% (lift_to_both0 tv3_2131))) in
        letb x_2137 : fp_t :=
          if is_pure (I := [interface]) (fp_is_square (g1_curve_func (
                lift_to_both0 x1_2134)))
          then lift_to_both0 x1_2134
          else if is_pure (I := [interface]) (fp_is_square (g1_curve_func (
                lift_to_both0 x2_2135)))
          then lift_to_both0 x2_2135
          else lift_to_both0 x3_2136 in
        letbm y_2122 : fp_t loc( y_2122_loc ) :=
          fp_sqrt (g1_curve_func (lift_to_both0 x_2137)) in
        letb 'y_2122 :=
          if (fp_sgn0 (lift_to_both0 u_2127)) !=.? (fp_sgn0 (
              lift_to_both0 y_2122)) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset (
            [tv4_2121_loc ; y_2122_loc])) (L2 := CEfset (
            [tv4_2121_loc ; y_2122_loc])) (I1 := [interface]) (I2 := [interface
          #val #[ FP_IS_SQUARE ] : fp_is_square_inp → fp_is_square_out ;
          #val #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out ;
          #val #[ FP_SQRT ] : fp_sqrt_inp → fp_sqrt_out ;
          #val #[ G1_CURVE_FUNC ] : g1_curve_func_inp → g1_curve_func_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm y_2122 loc( y_2122_loc ) :=
              (nat_mod_zero ) -% (lift_to_both0 y_2122) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 y_2122)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 y_2122)
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 x_2137,
            lift_to_both0 y_2122,
            lift_to_both0 ((false : bool_ChoiceEquality))
          ))
        ) : both (CEfset ([tv4_2121_loc ; y_2122_loc])) [interface
      #val #[ FP_IS_SQUARE ] : fp_is_square_inp → fp_is_square_out ;
      #val #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out ;
      #val #[ FP_SQRT ] : fp_sqrt_inp → fp_sqrt_out ;
      #val #[ G1_CURVE_FUNC ] : g1_curve_func_inp → g1_curve_func_out ] (
        g1_t)))in
  both_package' _ _ (G1_MAP_TO_CURVE_SVDW,(
      g1_map_to_curve_svdw_inp,g1_map_to_curve_svdw_out)) temp_package_both.
Fail Next Obligation.


Notation "'g1_clear_cofactor_inp'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_clear_cofactor_inp'" :=(g1_t : ChoiceEquality) (at level 2).
Notation "'g1_clear_cofactor_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_clear_cofactor_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1_CLEAR_COFACTOR : nat :=
  2141.
Program Definition g1_clear_cofactor
  : both_package (fset.fset0) [interface
  #val #[ G1MUL ] : g1mul_inp → g1mul_out ] [(G1_CLEAR_COFACTOR,(
      g1_clear_cofactor_inp,g1_clear_cofactor_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_2140) := temp_inp : g1_t in
    
    let g1mul := fun x_0 x_1 => package_both g1mul (x_0,x_1) in
    ((letb h_eff_2139 : scalar_t :=
          nat_mod_from_literal (_) (lift_to_both0 (
              @repr U128 15132376222941642753)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (g1mul (
            lift_to_both0 h_eff_2139) (lift_to_both0 x_2140))
        ) : both (fset.fset0) [interface
      #val #[ G1MUL ] : g1mul_inp → g1mul_out ] (g1_t)))in
  both_package' _ _ (G1_CLEAR_COFACTOR,(
      g1_clear_cofactor_inp,g1_clear_cofactor_out)) temp_package_both.
Fail Next Obligation.


Notation "'g1_hash_to_curve_svdw_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g1_hash_to_curve_svdw_inp'" :=(
  byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'g1_hash_to_curve_svdw_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_hash_to_curve_svdw_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1_HASH_TO_CURVE_SVDW : nat :=
  2149.
Program Definition g1_hash_to_curve_svdw
  : both_package (CEfset ([])) [interface
  #val #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out ;
  #val #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out ;
  #val #[ G1_MAP_TO_CURVE_SVDW ] : g1_map_to_curve_svdw_inp → g1_map_to_curve_svdw_out ;
  #val #[ G1ADD ] : g1add_inp → g1add_out ] [(G1_HASH_TO_CURVE_SVDW,(
      g1_hash_to_curve_svdw_inp,g1_hash_to_curve_svdw_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(msg_2142 , dst_2143) := temp_inp : byte_seq '× byte_seq in
    
    let fp_hash_to_field := fun x_0 x_1 x_2 => package_both fp_hash_to_field (
      x_0,x_1,x_2) in
    let g1_clear_cofactor := fun x_0 => package_both g1_clear_cofactor (x_0) in
    let g1_map_to_curve_svdw := fun x_0 => package_both g1_map_to_curve_svdw (
      x_0) in
    let g1add := fun x_0 x_1 => package_both g1add (x_0,x_1) in
    ((letb u_2144 : seq fp_t :=
          fp_hash_to_field (lift_to_both0 msg_2142) (lift_to_both0 dst_2143) (
            lift_to_both0 (usize 2)) in
        letb q0_2145 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
          g1_map_to_curve_svdw (seq_index (u_2144) (lift_to_both0 (usize 0))) in
        letb q1_2146 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
          g1_map_to_curve_svdw (seq_index (u_2144) (lift_to_both0 (usize 1))) in
        letb r_2147 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
          g1add (lift_to_both0 q0_2145) (lift_to_both0 q1_2146) in
        letb p_2148 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
          g1_clear_cofactor (lift_to_both0 r_2147) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2148)
        ) : both (CEfset ([])) [interface
      #val #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out ;
      #val #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out ;
      #val #[ G1_MAP_TO_CURVE_SVDW ] : g1_map_to_curve_svdw_inp → g1_map_to_curve_svdw_out ;
      #val #[ G1ADD ] : g1add_inp → g1add_out ] (g1_t)))in
  both_package' _ _ (G1_HASH_TO_CURVE_SVDW,(
      g1_hash_to_curve_svdw_inp,g1_hash_to_curve_svdw_out)) temp_package_both.
Fail Next Obligation.


Notation "'g1_encode_to_curve_svdw_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g1_encode_to_curve_svdw_inp'" :=(
  byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'g1_encode_to_curve_svdw_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_encode_to_curve_svdw_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1_ENCODE_TO_CURVE_SVDW : nat :=
  2155.
Program Definition g1_encode_to_curve_svdw
  : both_package (CEfset ([])) [interface
  #val #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out ;
  #val #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out ;
  #val #[ G1_MAP_TO_CURVE_SVDW ] : g1_map_to_curve_svdw_inp → g1_map_to_curve_svdw_out
  ] [(G1_ENCODE_TO_CURVE_SVDW,(
      g1_encode_to_curve_svdw_inp,g1_encode_to_curve_svdw_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(msg_2150 , dst_2151) := temp_inp : byte_seq '× byte_seq in
    
    let fp_hash_to_field := fun x_0 x_1 x_2 => package_both fp_hash_to_field (
      x_0,x_1,x_2) in
    let g1_clear_cofactor := fun x_0 => package_both g1_clear_cofactor (x_0) in
    let g1_map_to_curve_svdw := fun x_0 => package_both g1_map_to_curve_svdw (
      x_0) in
    ((letb u_2152 : seq fp_t :=
          fp_hash_to_field (lift_to_both0 msg_2150) (lift_to_both0 dst_2151) (
            lift_to_both0 (usize 1)) in
        letb q_2153 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
          g1_map_to_curve_svdw (seq_index (u_2152) (lift_to_both0 (usize 0))) in
        letb p_2154 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
          g1_clear_cofactor (lift_to_both0 q_2153) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2154)
        ) : both (CEfset ([])) [interface
      #val #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out ;
      #val #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out ;
      #val #[ G1_MAP_TO_CURVE_SVDW ] : g1_map_to_curve_svdw_inp → g1_map_to_curve_svdw_out
      ] (g1_t)))in
  both_package' _ _ (G1_ENCODE_TO_CURVE_SVDW,(
      g1_encode_to_curve_svdw_inp,g1_encode_to_curve_svdw_out)) temp_package_both.
Fail Next Obligation.

Definition output_2156_loc : ChoiceEqualityLocation :=
  (seq (fp_t '× fp_t) ; 2157%nat).
Notation "'fp2_hash_to_field_inp'" :=(
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'fp2_hash_to_field_inp'" :=(
  byte_seq '× byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'fp2_hash_to_field_out'" :=(
  seq fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2_hash_to_field_out'" :=(seq fp2_t : ChoiceEquality) (at level 2).
Definition FP2_HASH_TO_FIELD : nat :=
  2170.
Program Definition fp2_hash_to_field
  : both_package (CEfset ([output_2156_loc])) [interface
  #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
  ] [(FP2_HASH_TO_FIELD,(fp2_hash_to_field_inp,fp2_hash_to_field_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      msg_2160 , dst_2161 , count_2158) := temp_inp : byte_seq '× byte_seq '× uint_size in
    
    let expand_message_xmd := fun x_0 x_1 x_2 => package_both expand_message_xmd (
      x_0,x_1,x_2) in
    ((letb len_in_bytes_2159 : uint_size :=
          ((lift_to_both0 count_2158) .* (lift_to_both0 (usize 2))) .* (
            lift_to_both0 l_v) in
        letb uniform_bytes_2162 : seq uint8 :=
          expand_message_xmd (lift_to_both0 msg_2160) (lift_to_both0 dst_2161) (
            lift_to_both0 len_in_bytes_2159) in
        letbm output_2156 : seq (fp_t '× fp_t) loc( output_2156_loc ) :=
          seq_new_ (default : fp2_t) (lift_to_both0 count_2158) in
        letb output_2156 :=
          foldi_both' (lift_to_both0 (usize 0)) (
              lift_to_both0 count_2158) output_2156 (L := (CEfset (
                [output_2156_loc]))) (I := ([interface
              #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
              ])) (fun i_2163 output_2156 =>
            letb elm_offset_2164 : uint_size :=
              ((lift_to_both0 l_v) .* (lift_to_both0 i_2163)) .* (
                lift_to_both0 (usize 2)) in
            letb tv_2165 : seq uint8 :=
              seq_slice (lift_to_both0 uniform_bytes_2162) (
                lift_to_both0 elm_offset_2164) (lift_to_both0 l_v) in
            letb e_1_2166 : fp_t :=
              nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
                    nat_mod_from_byte_seq_be (lift_to_both0 tv_2165))) (
                  lift_to_both0 (usize 16)) (lift_to_both0 (usize 48))) in
            letb elm_offset_2167 : uint_size :=
              (lift_to_both0 l_v) .* ((lift_to_both0 (usize 1)) .+ ((
                    lift_to_both0 i_2163) .* (lift_to_both0 (usize 2)))) in
            letb tv_2168 : seq uint8 :=
              seq_slice (lift_to_both0 uniform_bytes_2162) (
                lift_to_both0 elm_offset_2167) (lift_to_both0 l_v) in
            letb e_2_2169 : fp_t :=
              nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
                    nat_mod_from_byte_seq_be (lift_to_both0 tv_2168))) (
                  lift_to_both0 (usize 16)) (lift_to_both0 (usize 48))) in
            letb output_2156 : seq (fp_t '× fp_t) :=
              seq_upd output_2156 (lift_to_both0 i_2163) (is_pure (prod_b(
                    lift_to_both0 e_1_2166,
                    lift_to_both0 e_2_2169
                  ))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 output_2156)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 output_2156)
        ) : both (CEfset ([output_2156_loc])) [interface
      #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
      ] (seq fp2_t)))in
  both_package' _ _ (FP2_HASH_TO_FIELD,(
      fp2_hash_to_field_inp,fp2_hash_to_field_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp2_sgn0_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2_sgn0_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'fp2_sgn0_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'fp2_sgn0_out'" :=(bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition FP2_SGN0 : nat :=
  2177.
Program Definition fp2_sgn0
  : both_package (fset.fset0) [interface
  #val #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out ] [(FP2_SGN0,(
      fp2_sgn0_inp,fp2_sgn0_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_2171) := temp_inp : fp2_t in
    
    let fp_sgn0 := fun x_0 => package_both fp_sgn0 (x_0) in
    ((letb '(x0_2172, x1_2173) : (fp_t '× fp_t) := lift_to_both0 x_2171 in
        letb sign_0_2174 : bool_ChoiceEquality :=
          fp_sgn0 (lift_to_both0 x0_2172) in
        letb zero_0_2175 : bool_ChoiceEquality :=
          (lift_to_both0 x0_2172) =.? (nat_mod_zero ) in
        letb sign_1_2176 : bool_ChoiceEquality :=
          fp_sgn0 (lift_to_both0 x1_2173) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
            lift_to_both0 sign_0_2174) || ((lift_to_both0 zero_0_2175) && (
              lift_to_both0 sign_1_2176)))
        ) : both (fset.fset0) [interface
      #val #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out ] (
        bool_ChoiceEquality)))in
  both_package' _ _ (FP2_SGN0,(fp2_sgn0_inp,fp2_sgn0_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp2_is_square_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2_is_square_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'fp2_is_square_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'fp2_is_square_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition FP2_IS_SQUARE : nat :=
  2187.
Program Definition fp2_is_square
  : both_package (fset.fset0) [interface] [(FP2_IS_SQUARE,(
      fp2_is_square_inp,fp2_is_square_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_2179) := temp_inp : fp2_t in
    
    ((letb c1_2178 : fp_t :=
          nat_mod_from_byte_seq_be (array_to_be_bytes (
              lift_to_both0 p_1_2_v)) in
        letb '(x1_2180, x2_2181) : (fp_t '× fp_t) := lift_to_both0 x_2179 in
        letb tv1_2182 : fp_t :=
          (lift_to_both0 x1_2180) *% (lift_to_both0 x1_2180) in
        letb tv2_2183 : fp_t :=
          (lift_to_both0 x2_2181) *% (lift_to_both0 x2_2181) in
        letb tv1_2184 : fp_t :=
          (lift_to_both0 tv1_2182) +% (lift_to_both0 tv2_2183) in
        letb tv1_2185 : fp_t :=
          nat_mod_pow_self (lift_to_both0 tv1_2184) (lift_to_both0 c1_2178) in
        letb neg1_2186 : fp_t := (nat_mod_zero ) -% (nat_mod_one ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
            lift_to_both0 tv1_2185) !=.? (lift_to_both0 neg1_2186))
        ) : both (fset.fset0) [interface] (bool_ChoiceEquality)))in
  both_package' _ _ (FP2_IS_SQUARE,(
      fp2_is_square_inp,fp2_is_square_out)) temp_package_both.
Fail Next Obligation.

Definition c_2188_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2189%nat).
Notation "'fp2exp_inp'" :=(
  fp2_t '× fp_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2exp_inp'" :=(fp2_t '× fp_t : ChoiceEquality) (at level 2).
Notation "'fp2exp_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2exp_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition FP2EXP : nat :=
  2193.
Program Definition fp2exp
  : both_package (CEfset ([c_2188_loc])) [interface
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] [(FP2EXP,(
      fp2exp_inp,fp2exp_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(n_2192 , k_2191) := temp_inp : fp2_t '× fp_t in
    
    let fp2fromfp := fun x_0 => package_both fp2fromfp (x_0) in
    let fp2mul := fun x_0 x_1 => package_both fp2mul (x_0,x_1) in
    ((letbm c_2188 : (fp_t '× fp_t) loc( c_2188_loc ) :=
          fp2fromfp (nat_mod_one ) in
        letb c_2188 :=
          foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
                usize 381)) c_2188 (L := (CEfset ([c_2188_loc]))) (I := (
              [interface #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out
              ])) (fun i_2190 c_2188 =>
            letbm c_2188 loc( c_2188_loc ) :=
              fp2mul (lift_to_both0 c_2188) (lift_to_both0 c_2188) in
            letb 'c_2188 :=
              if nat_mod_bit (lift_to_both0 k_2191) ((lift_to_both0 (
                    usize 380)) .- (lift_to_both0 i_2190)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([c_2188_loc])) (L2 := CEfset (
                [c_2188_loc])) (I1 := [interface
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ]) (I2 := [interface
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm c_2188 loc( c_2188_loc ) :=
                  fp2mul (lift_to_both0 c_2188) (lift_to_both0 n_2192) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 c_2188)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 c_2188)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 c_2188)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 c_2188)
        ) : both (CEfset ([c_2188_loc])) [interface
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] (fp2_t)))in
  both_package' _ _ (FP2EXP,(fp2exp_inp,fp2exp_out)) temp_package_both.
Fail Next Obligation.


Notation "'fp2_sqrt_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2_sqrt_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'fp2_sqrt_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'fp2_sqrt_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition FP2_SQRT : nat :=
  2202.
Program Definition fp2_sqrt
  : both_package (CEfset ([])) [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
  #val #[ FP2EXP ] : fp2exp_inp → fp2exp_out ;
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] [(FP2_SQRT,(
      fp2_sqrt_inp,fp2_sqrt_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(a_2196) := temp_inp : fp2_t in
    
    let fp2add := fun x_0 x_1 => package_both fp2add (x_0,x_1) in
    let fp2exp := fun x_0 x_1 => package_both fp2exp (x_0,x_1) in
    let fp2fromfp := fun x_0 => package_both fp2fromfp (x_0) in
    let fp2mul := fun x_0 x_1 => package_both fp2mul (x_0,x_1) in
    ((letb c1_2194 : fp_t :=
          nat_mod_from_byte_seq_be (array_to_be_bytes (
              lift_to_both0 p_3_4_v)) in
        letb c2_2195 : fp_t :=
          nat_mod_from_byte_seq_be (array_to_be_bytes (
              lift_to_both0 p_1_2_v)) in
        letb a1_2197 : (fp_t '× fp_t) :=
          fp2exp (lift_to_both0 a_2196) (lift_to_both0 c1_2194) in
        letb alpha_2198 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 a1_2197) (fp2mul (lift_to_both0 a1_2197) (
              lift_to_both0 a_2196)) in
        letb x0_2199 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 a1_2197) (lift_to_both0 a_2196) in
        letb neg1_2200 : (fp_t '× fp_t) :=
          prod_b((nat_mod_zero ) -% (nat_mod_one ), nat_mod_zero ) in
        letb b_2201 : (fp_t '× fp_t) :=
          fp2exp (fp2add (fp2fromfp (nat_mod_one )) (
              lift_to_both0 alpha_2198)) (lift_to_both0 c2_2195) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) ((lift_to_both0 alpha_2198) =.? (
              lift_to_both0 neg1_2200))
          then fp2mul (prod_b(nat_mod_zero , nat_mod_one )) (
            lift_to_both0 x0_2199)
          else fp2mul (lift_to_both0 b_2201) (lift_to_both0 x0_2199))
        ) : both (CEfset ([])) [interface
      #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
      #val #[ FP2EXP ] : fp2exp_inp → fp2exp_out ;
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] (fp2_t)))in
  both_package' _ _ (FP2_SQRT,(fp2_sqrt_inp,fp2_sqrt_out)) temp_package_both.
Fail Next Obligation.


Notation "'g2_curve_func_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_curve_func_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'g2_curve_func_out'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_curve_func_out'" :=(fp2_t : ChoiceEquality) (at level 2).
Definition G2_CURVE_FUNC : nat :=
  2204.
Program Definition g2_curve_func
  : both_package (fset.fset0) [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] [(G2_CURVE_FUNC,(
      g2_curve_func_inp,g2_curve_func_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_2203) := temp_inp : fp2_t in
    
    let fp2add := fun x_0 x_1 => package_both fp2add (x_0,x_1) in
    let fp2mul := fun x_0 x_1 => package_both fp2mul (x_0,x_1) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (fp2add (fp2mul (
              lift_to_both0 x_2203) (fp2mul (lift_to_both0 x_2203) (
                lift_to_both0 x_2203))) (prod_b(
              nat_mod_from_literal (_) (lift_to_both0 (@repr U128 4)),
              nat_mod_from_literal (_) (lift_to_both0 (@repr U128 4))
            )))
        ) : both (fset.fset0) [interface
      #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] (fp2_t)))in
  both_package' _ _ (G2_CURVE_FUNC,(
      g2_curve_func_inp,g2_curve_func_out)) temp_package_both.
Fail Next Obligation.

Definition y_2206_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2207%nat).
Definition tv4_2205_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2208%nat).
Notation "'g2_map_to_curve_svdw_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_map_to_curve_svdw_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'g2_map_to_curve_svdw_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_map_to_curve_svdw_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_MAP_TO_CURVE_SVDW : nat :=
  2223.
Program Definition g2_map_to_curve_svdw
  : both_package (CEfset ([tv4_2205_loc ; y_2206_loc])) [interface
  #val #[ FP2_IS_SQUARE ] : fp2_is_square_inp → fp2_is_square_out ;
  #val #[ FP2_SGN0 ] : fp2_sgn0_inp → fp2_sgn0_out ;
  #val #[ FP2_SQRT ] : fp2_sqrt_inp → fp2_sqrt_out ;
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
  #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ;
  #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ;
  #val #[ G2_CURVE_FUNC ] : g2_curve_func_inp → g2_curve_func_out ] [(
    G2_MAP_TO_CURVE_SVDW,(
      g2_map_to_curve_svdw_inp,g2_map_to_curve_svdw_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(u_2211) := temp_inp : fp2_t in
    
    let fp2_is_square := fun x_0 => package_both fp2_is_square (x_0) in
    let fp2_sgn0 := fun x_0 => package_both fp2_sgn0 (x_0) in
    let fp2_sqrt := fun x_0 => package_both fp2_sqrt (x_0) in
    let fp2add := fun x_0 x_1 => package_both fp2add (x_0,x_1) in
    let fp2fromfp := fun x_0 => package_both fp2fromfp (x_0) in
    let fp2inv := fun x_0 => package_both fp2inv (x_0) in
    let fp2mul := fun x_0 x_1 => package_both fp2mul (x_0,x_1) in
    let fp2neg := fun x_0 => package_both fp2neg (x_0) in
    let fp2sub := fun x_0 x_1 => package_both fp2sub (x_0,x_1) in
    let g2_curve_func := fun x_0 => package_both g2_curve_func (x_0) in
    ((letb z_2209 : (fp_t '× fp_t) := fp2neg (fp2fromfp (nat_mod_one )) in
        letb gz_2210 : (fp_t '× fp_t) :=
          g2_curve_func (lift_to_both0 z_2209) in
        letb tv1_2212 : (fp_t '× fp_t) :=
          fp2mul (fp2mul (lift_to_both0 u_2211) (lift_to_both0 u_2211)) (
            lift_to_both0 gz_2210) in
        letb tv2_2213 : (fp_t '× fp_t) :=
          fp2add (fp2fromfp (nat_mod_one )) (lift_to_both0 tv1_2212) in
        letb tv1_2214 : (fp_t '× fp_t) :=
          fp2sub (fp2fromfp (nat_mod_one )) (lift_to_both0 tv1_2212) in
        letb tv3_2215 : (fp_t '× fp_t) :=
          fp2inv (fp2mul (lift_to_both0 tv1_2214) (lift_to_both0 tv2_2213)) in
        letbm tv4_2205 : (fp_t '× fp_t) loc( tv4_2205_loc ) :=
          fp2_sqrt (fp2mul (fp2neg (lift_to_both0 gz_2210)) (fp2mul (fp2fromfp (
                  nat_mod_from_literal (_) (lift_to_both0 (@repr U128 3)))) (
                fp2mul (lift_to_both0 z_2209) (lift_to_both0 z_2209)))) in
        letb 'tv4_2205 :=
          if fp2_sgn0 (lift_to_both0 tv4_2205) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset ([tv4_2205_loc])) (L2 := CEfset (
            [tv4_2205_loc ; y_2206_loc])) (I1 := [interface
          #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ]) (I2 := [interface
          #val #[ FP2_IS_SQUARE ] : fp2_is_square_inp → fp2_is_square_out ;
          #val #[ FP2_SGN0 ] : fp2_sgn0_inp → fp2_sgn0_out ;
          #val #[ FP2_SQRT ] : fp2_sqrt_inp → fp2_sqrt_out ;
          #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
          #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
          #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
          #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
          #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ;
          #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ;
          #val #[ G2_CURVE_FUNC ] : g2_curve_func_inp → g2_curve_func_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm tv4_2205 loc( tv4_2205_loc ) :=
              fp2neg (lift_to_both0 tv4_2205) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 tv4_2205)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 tv4_2205)
           in
        letb tv5_2216 : (fp_t '× fp_t) :=
          fp2mul (fp2mul (fp2mul (lift_to_both0 u_2211) (
                lift_to_both0 tv1_2214)) (lift_to_both0 tv3_2215)) (
            lift_to_both0 tv4_2205) in
        letb tv6_2217 : (fp_t '× fp_t) :=
          fp2mul (fp2mul (fp2neg (fp2fromfp (nat_mod_from_literal (_) (
                    lift_to_both0 (@repr U128 4))))) (lift_to_both0 gz_2210)) (
            fp2inv (fp2mul (fp2fromfp (nat_mod_from_literal (_) (lift_to_both0 (
                      @repr U128 3)))) (fp2mul (lift_to_both0 z_2209) (
                  lift_to_both0 z_2209)))) in
        letb x1_2218 : (fp_t '× fp_t) :=
          fp2sub (fp2mul (fp2neg (lift_to_both0 z_2209)) (fp2inv (fp2fromfp (
                  nat_mod_two )))) (lift_to_both0 tv5_2216) in
        letb x2_2219 : (fp_t '× fp_t) :=
          fp2add (fp2mul (fp2neg (lift_to_both0 z_2209)) (fp2inv (fp2fromfp (
                  nat_mod_two )))) (lift_to_both0 tv5_2216) in
        letb tv7_2220 : (fp_t '× fp_t) :=
          fp2mul (fp2mul (lift_to_both0 tv2_2213) (lift_to_both0 tv2_2213)) (
            lift_to_both0 tv3_2215) in
        letb x3_2221 : (fp_t '× fp_t) :=
          fp2add (lift_to_both0 z_2209) (fp2mul (lift_to_both0 tv6_2217) (
              fp2mul (lift_to_both0 tv7_2220) (lift_to_both0 tv7_2220))) in
        letb x_2222 : (fp_t '× fp_t) :=
          if is_pure (I := [interface]) (fp2_is_square (g2_curve_func (
                lift_to_both0 x1_2218)))
          then lift_to_both0 x1_2218
          else if is_pure (I := [interface]) (fp2_is_square (g2_curve_func (
                lift_to_both0 x2_2219)))
          then lift_to_both0 x2_2219
          else lift_to_both0 x3_2221 in
        letbm y_2206 : (fp_t '× fp_t) loc( y_2206_loc ) :=
          fp2_sqrt (g2_curve_func (lift_to_both0 x_2222)) in
        letb 'y_2206 :=
          if (fp2_sgn0 (lift_to_both0 u_2211)) !=.? (fp2_sgn0 (
              lift_to_both0 y_2206)) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset (
            [tv4_2205_loc ; y_2206_loc])) (L2 := CEfset (
            [tv4_2205_loc ; y_2206_loc])) (I1 := [interface
          #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ]) (I2 := [interface
          #val #[ FP2_IS_SQUARE ] : fp2_is_square_inp → fp2_is_square_out ;
          #val #[ FP2_SGN0 ] : fp2_sgn0_inp → fp2_sgn0_out ;
          #val #[ FP2_SQRT ] : fp2_sqrt_inp → fp2_sqrt_out ;
          #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
          #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
          #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
          #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
          #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ;
          #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ;
          #val #[ G2_CURVE_FUNC ] : g2_curve_func_inp → g2_curve_func_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm y_2206 loc( y_2206_loc ) := fp2neg (lift_to_both0 y_2206) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 y_2206)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 y_2206)
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 x_2222,
            lift_to_both0 y_2206,
            lift_to_both0 ((false : bool_ChoiceEquality))
          ))
        ) : both (CEfset ([tv4_2205_loc ; y_2206_loc])) [interface
      #val #[ FP2_IS_SQUARE ] : fp2_is_square_inp → fp2_is_square_out ;
      #val #[ FP2_SGN0 ] : fp2_sgn0_inp → fp2_sgn0_out ;
      #val #[ FP2_SQRT ] : fp2_sqrt_inp → fp2_sqrt_out ;
      #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
      #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ;
      #val #[ FP2SUB ] : fp2sub_inp → fp2sub_out ;
      #val #[ G2_CURVE_FUNC ] : g2_curve_func_inp → g2_curve_func_out ] (
        g2_t)))in
  both_package' _ _ (G2_MAP_TO_CURVE_SVDW,(
      g2_map_to_curve_svdw_inp,g2_map_to_curve_svdw_out)) temp_package_both.
Fail Next Obligation.


Notation "'psi_inp'" :=(g2_t : choice_type) (in custom pack_type at level 2).
Notation "'psi_inp'" :=(g2_t : ChoiceEquality) (at level 2).
Notation "'psi_out'" :=(g2_t : choice_type) (in custom pack_type at level 2).
Notation "'psi_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition PSI : nat :=
  2232.
Program Definition psi
  : both_package (CEfset ([])) [interface
  #val #[ FP2CONJUGATE ] : fp2conjugate_inp → fp2conjugate_out ;
  #val #[ FP2EXP ] : fp2exp_inp → fp2exp_out ;
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] [(PSI,(psi_inp,psi_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_2226) := temp_inp : g2_t in
    
    let fp2conjugate := fun x_0 => package_both fp2conjugate (x_0) in
    let fp2exp := fun x_0 x_1 => package_both fp2exp (x_0,x_1) in
    let fp2inv := fun x_0 => package_both fp2inv (x_0) in
    let fp2mul := fun x_0 x_1 => package_both fp2mul (x_0,x_1) in
    ((letb c1_2224 : (fp_t '× fp_t) :=
          fp2inv (fp2exp (prod_b(nat_mod_one , nat_mod_one )) (((
                  nat_mod_zero ) -% (nat_mod_one )) *% (nat_mod_inv (
                  nat_mod_from_literal (_) (lift_to_both0 (@repr U128 3)))))) in
        letb c2_2225 : (fp_t '× fp_t) :=
          fp2inv (fp2exp (prod_b(nat_mod_one , nat_mod_one )) (((
                  nat_mod_zero ) -% (nat_mod_one )) *% (nat_mod_inv (
                  nat_mod_two )))) in
        letb '(x_2227, y_2228, inf_2229) : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          lift_to_both0 p_2226 in
        letb qx_2230 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 c1_2224) (fp2conjugate (
              lift_to_both0 x_2227)) in
        letb qy_2231 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 c2_2225) (fp2conjugate (
              lift_to_both0 y_2228)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 qx_2230,
            lift_to_both0 qy_2231,
            lift_to_both0 inf_2229
          ))
        ) : both (CEfset ([])) [interface
      #val #[ FP2CONJUGATE ] : fp2conjugate_inp → fp2conjugate_out ;
      #val #[ FP2EXP ] : fp2exp_inp → fp2exp_out ;
      #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ] (g2_t)))in
  both_package' _ _ (PSI,(psi_inp,psi_out)) temp_package_both.
Fail Next Obligation.


Notation "'g2_clear_cofactor_inp'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_clear_cofactor_inp'" :=(g2_t : ChoiceEquality) (at level 2).
Notation "'g2_clear_cofactor_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_clear_cofactor_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_CLEAR_COFACTOR : nat :=
  2247.
Program Definition g2_clear_cofactor
  : both_package (CEfset ([])) [interface
  #val #[ G2ADD ] : g2add_inp → g2add_out ;
  #val #[ G2DOUBLE ] : g2double_inp → g2double_out ;
  #val #[ G2MUL ] : g2mul_inp → g2mul_out ;
  #val #[ G2NEG ] : g2neg_inp → g2neg_out ;
  #val #[ PSI ] : psi_inp → psi_out ] [(G2_CLEAR_COFACTOR,(
      g2_clear_cofactor_inp,g2_clear_cofactor_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_2234) := temp_inp : g2_t in
    
    let g2add := fun x_0 x_1 => package_both g2add (x_0,x_1) in
    let g2double := fun x_0 => package_both g2double (x_0) in
    let g2mul := fun x_0 x_1 => package_both g2mul (x_0,x_1) in
    let g2neg := fun x_0 => package_both g2neg (x_0) in
    let psi := fun x_0 => package_both psi (x_0) in
    ((letb c1_2233 : scalar_t :=
          nat_mod_from_literal (_) (lift_to_both0 (
              @repr U128 15132376222941642752)) in
        letb t1_2235 : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          g2mul (lift_to_both0 c1_2233) (lift_to_both0 p_2234) in
        letb t1_2236 : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          g2neg (lift_to_both0 t1_2235) in
        letb t2_2237 : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          psi (lift_to_both0 p_2234) in
        letb t3_2238 : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          g2double (lift_to_both0 p_2234) in
        letb t3_2239 : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          psi (psi (lift_to_both0 t3_2238)) in
        letb t3_2240 : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          g2add (lift_to_both0 t3_2239) (g2neg (lift_to_both0 t2_2237)) in
        letb t2_2241 : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          g2add (lift_to_both0 t1_2236) (lift_to_both0 t2_2237) in
        letb t2_2242 : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          g2mul (lift_to_both0 c1_2233) (lift_to_both0 t2_2241) in
        letb t2_2243 : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          g2neg (lift_to_both0 t2_2242) in
        letb t3_2244 : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          g2add (lift_to_both0 t3_2240) (lift_to_both0 t2_2243) in
        letb t3_2245 : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          g2add (lift_to_both0 t3_2244) (g2neg (lift_to_both0 t1_2236)) in
        letb q_2246 : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          g2add (lift_to_both0 t3_2245) (g2neg (lift_to_both0 p_2234)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 q_2246)
        ) : both (CEfset ([])) [interface
      #val #[ G2ADD ] : g2add_inp → g2add_out ;
      #val #[ G2DOUBLE ] : g2double_inp → g2double_out ;
      #val #[ G2MUL ] : g2mul_inp → g2mul_out ;
      #val #[ G2NEG ] : g2neg_inp → g2neg_out ;
      #val #[ PSI ] : psi_inp → psi_out ] (g2_t)))in
  both_package' _ _ (G2_CLEAR_COFACTOR,(
      g2_clear_cofactor_inp,g2_clear_cofactor_out)) temp_package_both.
Fail Next Obligation.


Notation "'g2_hash_to_curve_svdw_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g2_hash_to_curve_svdw_inp'" :=(
  byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'g2_hash_to_curve_svdw_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_hash_to_curve_svdw_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_HASH_TO_CURVE_SVDW : nat :=
  2255.
Program Definition g2_hash_to_curve_svdw
  : both_package (CEfset ([])) [interface
  #val #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out ;
  #val #[ G2_CLEAR_COFACTOR ] : g2_clear_cofactor_inp → g2_clear_cofactor_out ;
  #val #[ G2_MAP_TO_CURVE_SVDW ] : g2_map_to_curve_svdw_inp → g2_map_to_curve_svdw_out ;
  #val #[ G2ADD ] : g2add_inp → g2add_out ] [(G2_HASH_TO_CURVE_SVDW,(
      g2_hash_to_curve_svdw_inp,g2_hash_to_curve_svdw_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(msg_2248 , dst_2249) := temp_inp : byte_seq '× byte_seq in
    
    let fp2_hash_to_field := fun x_0 x_1 x_2 => package_both fp2_hash_to_field (
      x_0,x_1,x_2) in
    let g2_clear_cofactor := fun x_0 => package_both g2_clear_cofactor (x_0) in
    let g2_map_to_curve_svdw := fun x_0 => package_both g2_map_to_curve_svdw (
      x_0) in
    let g2add := fun x_0 x_1 => package_both g2add (x_0,x_1) in
    ((letb u_2250 : seq fp2_t :=
          fp2_hash_to_field (lift_to_both0 msg_2248) (lift_to_both0 dst_2249) (
            lift_to_both0 (usize 2)) in
        letb q0_2251 : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          g2_map_to_curve_svdw (seq_index (u_2250) (lift_to_both0 (usize 0))) in
        letb q1_2252 : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          g2_map_to_curve_svdw (seq_index (u_2250) (lift_to_both0 (usize 1))) in
        letb r_2253 : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          g2add (lift_to_both0 q0_2251) (lift_to_both0 q1_2252) in
        letb p_2254 : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          g2_clear_cofactor (lift_to_both0 r_2253) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2254)
        ) : both (CEfset ([])) [interface
      #val #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out ;
      #val #[ G2_CLEAR_COFACTOR ] : g2_clear_cofactor_inp → g2_clear_cofactor_out ;
      #val #[ G2_MAP_TO_CURVE_SVDW ] : g2_map_to_curve_svdw_inp → g2_map_to_curve_svdw_out ;
      #val #[ G2ADD ] : g2add_inp → g2add_out ] (g2_t)))in
  both_package' _ _ (G2_HASH_TO_CURVE_SVDW,(
      g2_hash_to_curve_svdw_inp,g2_hash_to_curve_svdw_out)) temp_package_both.
Fail Next Obligation.


Notation "'g2_encode_to_curve_svdw_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g2_encode_to_curve_svdw_inp'" :=(
  byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'g2_encode_to_curve_svdw_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_encode_to_curve_svdw_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_ENCODE_TO_CURVE_SVDW : nat :=
  2261.
Program Definition g2_encode_to_curve_svdw
  : both_package (CEfset ([])) [interface
  #val #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out ;
  #val #[ G2_CLEAR_COFACTOR ] : g2_clear_cofactor_inp → g2_clear_cofactor_out ;
  #val #[ G2_MAP_TO_CURVE_SVDW ] : g2_map_to_curve_svdw_inp → g2_map_to_curve_svdw_out
  ] [(G2_ENCODE_TO_CURVE_SVDW,(
      g2_encode_to_curve_svdw_inp,g2_encode_to_curve_svdw_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(msg_2256 , dst_2257) := temp_inp : byte_seq '× byte_seq in
    
    let fp2_hash_to_field := fun x_0 x_1 x_2 => package_both fp2_hash_to_field (
      x_0,x_1,x_2) in
    let g2_clear_cofactor := fun x_0 => package_both g2_clear_cofactor (x_0) in
    let g2_map_to_curve_svdw := fun x_0 => package_both g2_map_to_curve_svdw (
      x_0) in
    ((letb u_2258 : seq fp2_t :=
          fp2_hash_to_field (lift_to_both0 msg_2256) (lift_to_both0 dst_2257) (
            lift_to_both0 (usize 1)) in
        letb q_2259 : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          g2_map_to_curve_svdw (seq_index (u_2258) (lift_to_both0 (usize 0))) in
        letb p_2260 : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          g2_clear_cofactor (lift_to_both0 q_2259) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2260)
        ) : both (CEfset ([])) [interface
      #val #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out ;
      #val #[ G2_CLEAR_COFACTOR ] : g2_clear_cofactor_inp → g2_clear_cofactor_out ;
      #val #[ G2_MAP_TO_CURVE_SVDW ] : g2_map_to_curve_svdw_inp → g2_map_to_curve_svdw_out
      ] (g2_t)))in
  both_package' _ _ (G2_ENCODE_TO_CURVE_SVDW,(
      g2_encode_to_curve_svdw_inp,g2_encode_to_curve_svdw_out)) temp_package_both.
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

Definition y_2263_loc : ChoiceEqualityLocation :=
  (fp_t ; 2264%nat).
Definition x1_2262_loc : ChoiceEqualityLocation :=
  (fp_t ; 2265%nat).
Notation "'g1_simple_swu_iso_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_simple_swu_iso_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'g1_simple_swu_iso_out'" :=((fp_t '× fp_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'g1_simple_swu_iso_out'" :=((fp_t '× fp_t
  ) : ChoiceEquality) (at level 2).
Definition G1_SIMPLE_SWU_ISO : nat :=
  2275.
Program Definition g1_simple_swu_iso
  : both_package (CEfset ([x1_2262_loc ; y_2263_loc])) [interface
  #val #[ FP_IS_SQUARE ] : fp_is_square_inp → fp_is_square_out ;
  #val #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out ;
  #val #[ FP_SQRT ] : fp_sqrt_inp → fp_sqrt_out ] [(G1_SIMPLE_SWU_ISO,(
      g1_simple_swu_iso_inp,g1_simple_swu_iso_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(u_2269) := temp_inp : fp_t in
    
    let fp_is_square := fun x_0 => package_both fp_is_square (x_0) in
    let fp_sgn0 := fun x_0 => package_both fp_sgn0 (x_0) in
    let fp_sqrt := fun x_0 => package_both fp_sqrt (x_0) in
    ((letb z_2266 : fp_t :=
          nat_mod_from_literal (_) (lift_to_both0 (@repr U128 11)) in
        letb a_2267 : fp_t :=
          nat_mod_from_byte_seq_be (array_to_be_bytes (
              lift_to_both0 g1_iso_a_v)) in
        letb b_2268 : fp_t :=
          nat_mod_from_byte_seq_be (array_to_be_bytes (
              lift_to_both0 g1_iso_b_v)) in
        letb tv1_2270 : fp_t :=
          nat_mod_inv ((((lift_to_both0 z_2266) *% (lift_to_both0 z_2266)) *% (
                nat_mod_exp (lift_to_both0 u_2269) (lift_to_both0 (
                    @repr U32 4)))) +% (((lift_to_both0 z_2266) *% (
                  lift_to_both0 u_2269)) *% (lift_to_both0 u_2269))) in
        letbm x1_2262 : fp_t loc( x1_2262_loc ) :=
          (((nat_mod_zero ) -% (lift_to_both0 b_2268)) *% (nat_mod_inv (
                lift_to_both0 a_2267))) *% ((nat_mod_one ) +% (
              lift_to_both0 tv1_2270)) in
        letb 'x1_2262 :=
          if (lift_to_both0 tv1_2270) =.? (nat_mod_zero ) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset ([x1_2262_loc])) (L2 := CEfset (
            [x1_2262_loc ; y_2263_loc])) (I1 := [interface]) (I2 := [interface
          #val #[ FP_IS_SQUARE ] : fp_is_square_inp → fp_is_square_out ;
          #val #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out ;
          #val #[ FP_SQRT ] : fp_sqrt_inp → fp_sqrt_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm x1_2262 loc( x1_2262_loc ) :=
              (lift_to_both0 b_2268) *% (nat_mod_inv ((
                    lift_to_both0 z_2266) *% (lift_to_both0 a_2267))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 x1_2262)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 x1_2262)
           in
        letb gx1_2271 : fp_t :=
          ((nat_mod_exp (lift_to_both0 x1_2262) (lift_to_both0 (
                  @repr U32 3))) +% ((lift_to_both0 a_2267) *% (
                lift_to_both0 x1_2262))) +% (lift_to_both0 b_2268) in
        letb x2_2272 : fp_t :=
          (((lift_to_both0 z_2266) *% (lift_to_both0 u_2269)) *% (
              lift_to_both0 u_2269)) *% (lift_to_both0 x1_2262) in
        letb gx2_2273 : fp_t :=
          ((nat_mod_exp (lift_to_both0 x2_2272) (lift_to_both0 (
                  @repr U32 3))) +% ((lift_to_both0 a_2267) *% (
                lift_to_both0 x2_2272))) +% (lift_to_both0 b_2268) in
        letb '(x_2274, y_2263) : (fp_t '× fp_t) :=
          if is_pure (I := [interface]) (fp_is_square (lift_to_both0 gx1_2271))
          then prod_b(lift_to_both0 x1_2262, fp_sqrt (lift_to_both0 gx1_2271))
          else prod_b(lift_to_both0 x2_2272, fp_sqrt (lift_to_both0 gx2_2273)
          ) in
        letb 'y_2263 :=
          if (fp_sgn0 (lift_to_both0 u_2269)) !=.? (fp_sgn0 (
              lift_to_both0 y_2263)) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset (
            [x1_2262_loc ; y_2263_loc])) (L2 := CEfset (
            [x1_2262_loc ; y_2263_loc])) (I1 := [interface]) (I2 := [interface
          #val #[ FP_IS_SQUARE ] : fp_is_square_inp → fp_is_square_out ;
          #val #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out ;
          #val #[ FP_SQRT ] : fp_sqrt_inp → fp_sqrt_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm y_2263 loc( y_2263_loc ) :=
              (nat_mod_zero ) -% (lift_to_both0 y_2263) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 y_2263)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 y_2263)
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 x_2274,
            lift_to_both0 y_2263
          ))
        ) : both (CEfset ([x1_2262_loc ; y_2263_loc])) [interface
      #val #[ FP_IS_SQUARE ] : fp_is_square_inp → fp_is_square_out ;
      #val #[ FP_SGN0 ] : fp_sgn0_inp → fp_sgn0_out ;
      #val #[ FP_SQRT ] : fp_sqrt_inp → fp_sqrt_out ] ((fp_t '× fp_t))))in
  both_package' _ _ (G1_SIMPLE_SWU_ISO,(
      g1_simple_swu_iso_inp,g1_simple_swu_iso_out)) temp_package_both.
Fail Next Obligation.

Definition ynum_2284_loc : ChoiceEqualityLocation :=
  (fp_t ; 2289%nat).
Definition xden_k_2277_loc : ChoiceEqualityLocation :=
  (seq fp_t ; 2290%nat).
Definition xnum_k_2276_loc : ChoiceEqualityLocation :=
  (seq fp_t ; 2291%nat).
Definition ynum_k_2278_loc : ChoiceEqualityLocation :=
  (seq fp_t ; 2292%nat).
Definition inf_2288_loc : ChoiceEqualityLocation :=
  (bool_ChoiceEquality ; 2293%nat).
Definition xx_2283_loc : ChoiceEqualityLocation :=
  (fp_t ; 2294%nat).
Definition xx_2285_loc : ChoiceEqualityLocation :=
  (fp_t ; 2295%nat).
Definition yden_2286_loc : ChoiceEqualityLocation :=
  (fp_t ; 2296%nat).
Definition yden_k_2279_loc : ChoiceEqualityLocation :=
  (seq fp_t ; 2297%nat).
Definition xnum_2280_loc : ChoiceEqualityLocation :=
  (fp_t ; 2298%nat).
Definition xden_2282_loc : ChoiceEqualityLocation :=
  (fp_t ; 2299%nat).
Definition xx_2281_loc : ChoiceEqualityLocation :=
  (fp_t ; 2300%nat).
Definition xx_2287_loc : ChoiceEqualityLocation :=
  (fp_t ; 2301%nat).
Notation "'g1_isogeny_map_inp'" :=(
  fp_t '× fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_isogeny_map_inp'" :=(fp_t '× fp_t : ChoiceEquality) (at level 2).
Notation "'g1_isogeny_map_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_isogeny_map_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1_ISOGENY_MAP : nat :=
  2310.
Program Definition g1_isogeny_map
  : both_package (CEfset (
      [xnum_k_2276_loc ; xden_k_2277_loc ; ynum_k_2278_loc ; yden_k_2279_loc ; xnum_2280_loc ; xx_2281_loc ; xden_2282_loc ; xx_2283_loc ; ynum_2284_loc ; xx_2285_loc ; yden_2286_loc ; xx_2287_loc ; inf_2288_loc])) [interface] [(
    G1_ISOGENY_MAP,(g1_isogeny_map_inp,g1_isogeny_map_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_2303 , y_2308) := temp_inp : fp_t '× fp_t in
    
    ((letbm xnum_k_2276 : seq fp_t loc( xnum_k_2276_loc ) :=
          seq_new_ (default : fp_t) (lift_to_both0 (usize 12)) in
        letb xnum_k_2276 : seq fp_t :=
          seq_upd xnum_k_2276 (lift_to_both0 (usize 0)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_xnum_k_0_v)))) in
        letb xnum_k_2276 : seq fp_t :=
          seq_upd xnum_k_2276 (lift_to_both0 (usize 1)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_xnum_k_1_v)))) in
        letb xnum_k_2276 : seq fp_t :=
          seq_upd xnum_k_2276 (lift_to_both0 (usize 2)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_xnum_k_2_v)))) in
        letb xnum_k_2276 : seq fp_t :=
          seq_upd xnum_k_2276 (lift_to_both0 (usize 3)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_xnum_k_3_v)))) in
        letb xnum_k_2276 : seq fp_t :=
          seq_upd xnum_k_2276 (lift_to_both0 (usize 4)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_xnum_k_4_v)))) in
        letb xnum_k_2276 : seq fp_t :=
          seq_upd xnum_k_2276 (lift_to_both0 (usize 5)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_xnum_k_5_v)))) in
        letb xnum_k_2276 : seq fp_t :=
          seq_upd xnum_k_2276 (lift_to_both0 (usize 6)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_xnum_k_6_v)))) in
        letb xnum_k_2276 : seq fp_t :=
          seq_upd xnum_k_2276 (lift_to_both0 (usize 7)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_xnum_k_7_v)))) in
        letb xnum_k_2276 : seq fp_t :=
          seq_upd xnum_k_2276 (lift_to_both0 (usize 8)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_xnum_k_8_v)))) in
        letb xnum_k_2276 : seq fp_t :=
          seq_upd xnum_k_2276 (lift_to_both0 (usize 9)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_xnum_k_9_v)))) in
        letb xnum_k_2276 : seq fp_t :=
          seq_upd xnum_k_2276 (lift_to_both0 (usize 10)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_xnum_k_10_v)))) in
        letb xnum_k_2276 : seq fp_t :=
          seq_upd xnum_k_2276 (lift_to_both0 (usize 11)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_xnum_k_11_v)))) in
        letbm xden_k_2277 : seq fp_t loc( xden_k_2277_loc ) :=
          seq_new_ (default : fp_t) (lift_to_both0 (usize 10)) in
        letb xden_k_2277 : seq fp_t :=
          seq_upd xden_k_2277 (lift_to_both0 (usize 0)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_xden_k_0_v)))) in
        letb xden_k_2277 : seq fp_t :=
          seq_upd xden_k_2277 (lift_to_both0 (usize 1)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_xden_k_1_v)))) in
        letb xden_k_2277 : seq fp_t :=
          seq_upd xden_k_2277 (lift_to_both0 (usize 2)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_xden_k_2_v)))) in
        letb xden_k_2277 : seq fp_t :=
          seq_upd xden_k_2277 (lift_to_both0 (usize 3)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_xden_k_3_v)))) in
        letb xden_k_2277 : seq fp_t :=
          seq_upd xden_k_2277 (lift_to_both0 (usize 4)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_xden_k_4_v)))) in
        letb xden_k_2277 : seq fp_t :=
          seq_upd xden_k_2277 (lift_to_both0 (usize 5)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_xden_k_5_v)))) in
        letb xden_k_2277 : seq fp_t :=
          seq_upd xden_k_2277 (lift_to_both0 (usize 6)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_xden_k_6_v)))) in
        letb xden_k_2277 : seq fp_t :=
          seq_upd xden_k_2277 (lift_to_both0 (usize 7)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_xden_k_7_v)))) in
        letb xden_k_2277 : seq fp_t :=
          seq_upd xden_k_2277 (lift_to_both0 (usize 8)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_xden_k_8_v)))) in
        letb xden_k_2277 : seq fp_t :=
          seq_upd xden_k_2277 (lift_to_both0 (usize 9)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_xden_k_9_v)))) in
        letbm ynum_k_2278 : seq fp_t loc( ynum_k_2278_loc ) :=
          seq_new_ (default : fp_t) (lift_to_both0 (usize 16)) in
        letb ynum_k_2278 : seq fp_t :=
          seq_upd ynum_k_2278 (lift_to_both0 (usize 0)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_ynum_k_0_v)))) in
        letb ynum_k_2278 : seq fp_t :=
          seq_upd ynum_k_2278 (lift_to_both0 (usize 1)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_ynum_k_1_v)))) in
        letb ynum_k_2278 : seq fp_t :=
          seq_upd ynum_k_2278 (lift_to_both0 (usize 2)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_ynum_k_2_v)))) in
        letb ynum_k_2278 : seq fp_t :=
          seq_upd ynum_k_2278 (lift_to_both0 (usize 3)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_ynum_k_3_v)))) in
        letb ynum_k_2278 : seq fp_t :=
          seq_upd ynum_k_2278 (lift_to_both0 (usize 4)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_ynum_k_4_v)))) in
        letb ynum_k_2278 : seq fp_t :=
          seq_upd ynum_k_2278 (lift_to_both0 (usize 5)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_ynum_k_5_v)))) in
        letb ynum_k_2278 : seq fp_t :=
          seq_upd ynum_k_2278 (lift_to_both0 (usize 6)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_ynum_k_6_v)))) in
        letb ynum_k_2278 : seq fp_t :=
          seq_upd ynum_k_2278 (lift_to_both0 (usize 7)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_ynum_k_7_v)))) in
        letb ynum_k_2278 : seq fp_t :=
          seq_upd ynum_k_2278 (lift_to_both0 (usize 8)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_ynum_k_8_v)))) in
        letb ynum_k_2278 : seq fp_t :=
          seq_upd ynum_k_2278 (lift_to_both0 (usize 9)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_ynum_k_9_v)))) in
        letb ynum_k_2278 : seq fp_t :=
          seq_upd ynum_k_2278 (lift_to_both0 (usize 10)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_ynum_k_10_v)))) in
        letb ynum_k_2278 : seq fp_t :=
          seq_upd ynum_k_2278 (lift_to_both0 (usize 11)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_ynum_k_11_v)))) in
        letb ynum_k_2278 : seq fp_t :=
          seq_upd ynum_k_2278 (lift_to_both0 (usize 12)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_ynum_k_12_v)))) in
        letb ynum_k_2278 : seq fp_t :=
          seq_upd ynum_k_2278 (lift_to_both0 (usize 13)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_ynum_k_13_v)))) in
        letb ynum_k_2278 : seq fp_t :=
          seq_upd ynum_k_2278 (lift_to_both0 (usize 14)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_ynum_k_14_v)))) in
        letb ynum_k_2278 : seq fp_t :=
          seq_upd ynum_k_2278 (lift_to_both0 (usize 15)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_ynum_k_15_v)))) in
        letbm yden_k_2279 : seq fp_t loc( yden_k_2279_loc ) :=
          seq_new_ (default : fp_t) (lift_to_both0 (usize 15)) in
        letb yden_k_2279 : seq fp_t :=
          seq_upd yden_k_2279 (lift_to_both0 (usize 0)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_yden_k_0_v)))) in
        letb yden_k_2279 : seq fp_t :=
          seq_upd yden_k_2279 (lift_to_both0 (usize 1)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_yden_k_1_v)))) in
        letb yden_k_2279 : seq fp_t :=
          seq_upd yden_k_2279 (lift_to_both0 (usize 2)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_yden_k_2_v)))) in
        letb yden_k_2279 : seq fp_t :=
          seq_upd yden_k_2279 (lift_to_both0 (usize 3)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_yden_k_3_v)))) in
        letb yden_k_2279 : seq fp_t :=
          seq_upd yden_k_2279 (lift_to_both0 (usize 4)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_yden_k_4_v)))) in
        letb yden_k_2279 : seq fp_t :=
          seq_upd yden_k_2279 (lift_to_both0 (usize 5)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_yden_k_5_v)))) in
        letb yden_k_2279 : seq fp_t :=
          seq_upd yden_k_2279 (lift_to_both0 (usize 6)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_yden_k_6_v)))) in
        letb yden_k_2279 : seq fp_t :=
          seq_upd yden_k_2279 (lift_to_both0 (usize 7)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_yden_k_7_v)))) in
        letb yden_k_2279 : seq fp_t :=
          seq_upd yden_k_2279 (lift_to_both0 (usize 8)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_yden_k_8_v)))) in
        letb yden_k_2279 : seq fp_t :=
          seq_upd yden_k_2279 (lift_to_both0 (usize 9)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_yden_k_9_v)))) in
        letb yden_k_2279 : seq fp_t :=
          seq_upd yden_k_2279 (lift_to_both0 (usize 10)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_yden_k_10_v)))) in
        letb yden_k_2279 : seq fp_t :=
          seq_upd yden_k_2279 (lift_to_both0 (usize 11)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_yden_k_11_v)))) in
        letb yden_k_2279 : seq fp_t :=
          seq_upd yden_k_2279 (lift_to_both0 (usize 12)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_yden_k_12_v)))) in
        letb yden_k_2279 : seq fp_t :=
          seq_upd yden_k_2279 (lift_to_both0 (usize 13)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_yden_k_13_v)))) in
        letb yden_k_2279 : seq fp_t :=
          seq_upd yden_k_2279 (lift_to_both0 (usize 14)) (is_pure (
              nat_mod_from_byte_seq_be (array_to_be_bytes (
                  lift_to_both0 g1_yden_k_14_v)))) in
        letbm xnum_2280 : fp_t loc( xnum_2280_loc ) := nat_mod_zero  in
        letbm xx_2281 : fp_t loc( xx_2281_loc ) := nat_mod_one  in
        letb '(xnum_2280, xx_2281) :=
          foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                lift_to_both0 xnum_k_2276)) prod_ce(xnum_2280, xx_2281) (L := (
              CEfset (
                [xnum_k_2276_loc ; xden_k_2277_loc ; ynum_k_2278_loc ; yden_k_2279_loc ; xnum_2280_loc ; xx_2281_loc ; xden_2282_loc ; xx_2283_loc ; ynum_2284_loc ; xx_2285_loc ; yden_2286_loc ; xx_2287_loc ; inf_2288_loc]))) (I := (
              [interface])) (fun i_2302 '(xnum_2280, xx_2281) =>
            letbm xnum_2280 loc( xnum_2280_loc ) :=
              (lift_to_both0 xnum_2280) +% ((lift_to_both0 xx_2281) *% (
                  seq_index (xnum_k_2276) (lift_to_both0 i_2302))) in
            letbm xx_2281 loc( xx_2281_loc ) :=
              (lift_to_both0 xx_2281) *% (lift_to_both0 x_2303) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 xnum_2280,
                lift_to_both0 xx_2281
              ))
            ) in
        letbm xden_2282 : fp_t loc( xden_2282_loc ) := nat_mod_zero  in
        letbm xx_2283 : fp_t loc( xx_2283_loc ) := nat_mod_one  in
        letb '(xden_2282, xx_2283) :=
          foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                lift_to_both0 xden_k_2277)) prod_ce(xden_2282, xx_2283) (L := (
              CEfset (
                [xnum_k_2276_loc ; xden_k_2277_loc ; ynum_k_2278_loc ; yden_k_2279_loc ; xnum_2280_loc ; xx_2281_loc ; xden_2282_loc ; xx_2283_loc ; ynum_2284_loc ; xx_2285_loc ; yden_2286_loc ; xx_2287_loc ; inf_2288_loc]))) (I := (
              [interface])) (fun i_2304 '(xden_2282, xx_2283) =>
            letbm xden_2282 loc( xden_2282_loc ) :=
              (lift_to_both0 xden_2282) +% ((lift_to_both0 xx_2283) *% (
                  seq_index (xden_k_2277) (lift_to_both0 i_2304))) in
            letbm xx_2283 loc( xx_2283_loc ) :=
              (lift_to_both0 xx_2283) *% (lift_to_both0 x_2303) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 xden_2282,
                lift_to_both0 xx_2283
              ))
            ) in
        letbm xden_2282 loc( xden_2282_loc ) :=
          (lift_to_both0 xden_2282) +% (lift_to_both0 xx_2283) in
        letbm ynum_2284 : fp_t loc( ynum_2284_loc ) := nat_mod_zero  in
        letbm xx_2285 : fp_t loc( xx_2285_loc ) := nat_mod_one  in
        letb '(ynum_2284, xx_2285) :=
          foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                lift_to_both0 ynum_k_2278)) prod_ce(ynum_2284, xx_2285) (L := (
              CEfset (
                [xnum_k_2276_loc ; xden_k_2277_loc ; ynum_k_2278_loc ; yden_k_2279_loc ; xnum_2280_loc ; xx_2281_loc ; xden_2282_loc ; xx_2283_loc ; ynum_2284_loc ; xx_2285_loc ; yden_2286_loc ; xx_2287_loc ; inf_2288_loc]))) (I := (
              [interface])) (fun i_2305 '(ynum_2284, xx_2285) =>
            letbm ynum_2284 loc( ynum_2284_loc ) :=
              (lift_to_both0 ynum_2284) +% ((lift_to_both0 xx_2285) *% (
                  seq_index (ynum_k_2278) (lift_to_both0 i_2305))) in
            letbm xx_2285 loc( xx_2285_loc ) :=
              (lift_to_both0 xx_2285) *% (lift_to_both0 x_2303) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 ynum_2284,
                lift_to_both0 xx_2285
              ))
            ) in
        letbm yden_2286 : fp_t loc( yden_2286_loc ) := nat_mod_zero  in
        letbm xx_2287 : fp_t loc( xx_2287_loc ) := nat_mod_one  in
        letb '(yden_2286, xx_2287) :=
          foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                lift_to_both0 yden_k_2279)) prod_ce(yden_2286, xx_2287) (L := (
              CEfset (
                [xnum_k_2276_loc ; xden_k_2277_loc ; ynum_k_2278_loc ; yden_k_2279_loc ; xnum_2280_loc ; xx_2281_loc ; xden_2282_loc ; xx_2283_loc ; ynum_2284_loc ; xx_2285_loc ; yden_2286_loc ; xx_2287_loc ; inf_2288_loc]))) (I := (
              [interface])) (fun i_2306 '(yden_2286, xx_2287) =>
            letbm yden_2286 loc( yden_2286_loc ) :=
              (lift_to_both0 yden_2286) +% ((lift_to_both0 xx_2287) *% (
                  seq_index (yden_k_2279) (lift_to_both0 i_2306))) in
            letbm xx_2287 loc( xx_2287_loc ) :=
              (lift_to_both0 xx_2287) *% (lift_to_both0 x_2303) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 yden_2286,
                lift_to_both0 xx_2287
              ))
            ) in
        letbm yden_2286 loc( yden_2286_loc ) :=
          (lift_to_both0 yden_2286) +% (lift_to_both0 xx_2287) in
        letb xr_2307 : fp_t :=
          (lift_to_both0 xnum_2280) *% (nat_mod_inv (
              lift_to_both0 xden_2282)) in
        letb yr_2309 : fp_t :=
          ((lift_to_both0 y_2308) *% (lift_to_both0 ynum_2284)) *% (
            nat_mod_inv (lift_to_both0 yden_2286)) in
        letbm inf_2288 : bool_ChoiceEquality loc( inf_2288_loc ) :=
          lift_to_both0 ((false : bool_ChoiceEquality)) in
        letb 'inf_2288 :=
          if ((lift_to_both0 xden_2282) =.? (nat_mod_zero )) || ((
              lift_to_both0 yden_2286) =.? (nat_mod_zero )) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset (
            [xnum_k_2276_loc ; xden_k_2277_loc ; ynum_k_2278_loc ; yden_k_2279_loc ; xnum_2280_loc ; xx_2281_loc ; xden_2282_loc ; xx_2283_loc ; ynum_2284_loc ; xx_2285_loc ; yden_2286_loc ; xx_2287_loc ; inf_2288_loc])) (L2 := CEfset (
            [xnum_k_2276_loc ; xden_k_2277_loc ; ynum_k_2278_loc ; yden_k_2279_loc ; xnum_2280_loc ; xx_2281_loc ; xden_2282_loc ; xx_2283_loc ; ynum_2284_loc ; xx_2285_loc ; yden_2286_loc ; xx_2287_loc ; inf_2288_loc])) (I1 := [interface]) (I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm inf_2288 loc( inf_2288_loc ) :=
              lift_to_both0 ((true : bool_ChoiceEquality)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 inf_2288)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 inf_2288)
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 xr_2307,
            lift_to_both0 yr_2309,
            lift_to_both0 inf_2288
          ))
        ) : both (CEfset (
          [xnum_k_2276_loc ; xden_k_2277_loc ; ynum_k_2278_loc ; yden_k_2279_loc ; xnum_2280_loc ; xx_2281_loc ; xden_2282_loc ; xx_2283_loc ; ynum_2284_loc ; xx_2285_loc ; yden_2286_loc ; xx_2287_loc ; inf_2288_loc])) [interface] (
        g1_t)))in
  both_package' _ _ (G1_ISOGENY_MAP,(
      g1_isogeny_map_inp,g1_isogeny_map_out)) temp_package_both.
Fail Next Obligation.


Notation "'g1_map_to_curve_sswu_inp'" :=(
  fp_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_map_to_curve_sswu_inp'" :=(fp_t : ChoiceEquality) (at level 2).
Notation "'g1_map_to_curve_sswu_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_map_to_curve_sswu_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1_MAP_TO_CURVE_SSWU : nat :=
  2315.
Program Definition g1_map_to_curve_sswu
  : both_package (CEfset ([])) [interface
  #val #[ G1_ISOGENY_MAP ] : g1_isogeny_map_inp → g1_isogeny_map_out ;
  #val #[ G1_SIMPLE_SWU_ISO ] : g1_simple_swu_iso_inp → g1_simple_swu_iso_out
  ] [(G1_MAP_TO_CURVE_SSWU,(
      g1_map_to_curve_sswu_inp,g1_map_to_curve_sswu_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(u_2311) := temp_inp : fp_t in
    
    let g1_isogeny_map := fun x_0 x_1 => package_both g1_isogeny_map (
      x_0,x_1) in
    let g1_simple_swu_iso := fun x_0 => package_both g1_simple_swu_iso (x_0) in
    ((letb '(xp_2312, yp_2313) : (fp_t '× fp_t) :=
          g1_simple_swu_iso (lift_to_both0 u_2311) in
        letb p_2314 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
          g1_isogeny_map (lift_to_both0 xp_2312) (lift_to_both0 yp_2313) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2314)
        ) : both (CEfset ([])) [interface
      #val #[ G1_ISOGENY_MAP ] : g1_isogeny_map_inp → g1_isogeny_map_out ;
      #val #[ G1_SIMPLE_SWU_ISO ] : g1_simple_swu_iso_inp → g1_simple_swu_iso_out
      ] (g1_t)))in
  both_package' _ _ (G1_MAP_TO_CURVE_SSWU,(
      g1_map_to_curve_sswu_inp,g1_map_to_curve_sswu_out)) temp_package_both.
Fail Next Obligation.


Notation "'g1_hash_to_curve_sswu_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g1_hash_to_curve_sswu_inp'" :=(
  byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'g1_hash_to_curve_sswu_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_hash_to_curve_sswu_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1_HASH_TO_CURVE_SSWU : nat :=
  2323.
Program Definition g1_hash_to_curve_sswu
  : both_package (CEfset ([])) [interface
  #val #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out ;
  #val #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out ;
  #val #[ G1_MAP_TO_CURVE_SSWU ] : g1_map_to_curve_sswu_inp → g1_map_to_curve_sswu_out ;
  #val #[ G1ADD ] : g1add_inp → g1add_out ] [(G1_HASH_TO_CURVE_SSWU,(
      g1_hash_to_curve_sswu_inp,g1_hash_to_curve_sswu_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(msg_2316 , dst_2317) := temp_inp : byte_seq '× byte_seq in
    
    let fp_hash_to_field := fun x_0 x_1 x_2 => package_both fp_hash_to_field (
      x_0,x_1,x_2) in
    let g1_clear_cofactor := fun x_0 => package_both g1_clear_cofactor (x_0) in
    let g1_map_to_curve_sswu := fun x_0 => package_both g1_map_to_curve_sswu (
      x_0) in
    let g1add := fun x_0 x_1 => package_both g1add (x_0,x_1) in
    ((letb u_2318 : seq fp_t :=
          fp_hash_to_field (lift_to_both0 msg_2316) (lift_to_both0 dst_2317) (
            lift_to_both0 (usize 2)) in
        letb q0_2319 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
          g1_map_to_curve_sswu (seq_index (u_2318) (lift_to_both0 (usize 0))) in
        letb q1_2320 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
          g1_map_to_curve_sswu (seq_index (u_2318) (lift_to_both0 (usize 1))) in
        letb r_2321 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
          g1add (lift_to_both0 q0_2319) (lift_to_both0 q1_2320) in
        letb p_2322 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
          g1_clear_cofactor (lift_to_both0 r_2321) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2322)
        ) : both (CEfset ([])) [interface
      #val #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out ;
      #val #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out ;
      #val #[ G1_MAP_TO_CURVE_SSWU ] : g1_map_to_curve_sswu_inp → g1_map_to_curve_sswu_out ;
      #val #[ G1ADD ] : g1add_inp → g1add_out ] (g1_t)))in
  both_package' _ _ (G1_HASH_TO_CURVE_SSWU,(
      g1_hash_to_curve_sswu_inp,g1_hash_to_curve_sswu_out)) temp_package_both.
Fail Next Obligation.


Notation "'g1_encode_to_curve_sswu_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g1_encode_to_curve_sswu_inp'" :=(
  byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'g1_encode_to_curve_sswu_out'" :=(
  g1_t : choice_type) (in custom pack_type at level 2).
Notation "'g1_encode_to_curve_sswu_out'" :=(g1_t : ChoiceEquality) (at level 2).
Definition G1_ENCODE_TO_CURVE_SSWU : nat :=
  2329.
Program Definition g1_encode_to_curve_sswu
  : both_package (CEfset ([])) [interface
  #val #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out ;
  #val #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out ;
  #val #[ G1_MAP_TO_CURVE_SSWU ] : g1_map_to_curve_sswu_inp → g1_map_to_curve_sswu_out
  ] [(G1_ENCODE_TO_CURVE_SSWU,(
      g1_encode_to_curve_sswu_inp,g1_encode_to_curve_sswu_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(msg_2324 , dst_2325) := temp_inp : byte_seq '× byte_seq in
    
    let fp_hash_to_field := fun x_0 x_1 x_2 => package_both fp_hash_to_field (
      x_0,x_1,x_2) in
    let g1_clear_cofactor := fun x_0 => package_both g1_clear_cofactor (x_0) in
    let g1_map_to_curve_sswu := fun x_0 => package_both g1_map_to_curve_sswu (
      x_0) in
    ((letb u_2326 : seq fp_t :=
          fp_hash_to_field (lift_to_both0 msg_2324) (lift_to_both0 dst_2325) (
            lift_to_both0 (usize 1)) in
        letb q_2327 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
          g1_map_to_curve_sswu (seq_index (u_2326) (lift_to_both0 (usize 0))) in
        letb p_2328 : (fp_t '× fp_t '× bool_ChoiceEquality) :=
          g1_clear_cofactor (lift_to_both0 q_2327) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2328)
        ) : both (CEfset ([])) [interface
      #val #[ FP_HASH_TO_FIELD ] : fp_hash_to_field_inp → fp_hash_to_field_out ;
      #val #[ G1_CLEAR_COFACTOR ] : g1_clear_cofactor_inp → g1_clear_cofactor_out ;
      #val #[ G1_MAP_TO_CURVE_SSWU ] : g1_map_to_curve_sswu_inp → g1_map_to_curve_sswu_out
      ] (g1_t)))in
  both_package' _ _ (G1_ENCODE_TO_CURVE_SSWU,(
      g1_encode_to_curve_sswu_inp,g1_encode_to_curve_sswu_out)) temp_package_both.
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

Definition y_2331_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2332%nat).
Definition x1_2330_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2333%nat).
Notation "'g2_simple_swu_iso_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_simple_swu_iso_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'g2_simple_swu_iso_out'" :=((fp2_t '× fp2_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'g2_simple_swu_iso_out'" :=((fp2_t '× fp2_t
  ) : ChoiceEquality) (at level 2).
Definition G2_SIMPLE_SWU_ISO : nat :=
  2343.
Program Definition g2_simple_swu_iso
  : both_package (CEfset ([x1_2330_loc ; y_2331_loc])) [interface
  #val #[ FP2_IS_SQUARE ] : fp2_is_square_inp → fp2_is_square_out ;
  #val #[ FP2_SGN0 ] : fp2_sgn0_inp → fp2_sgn0_out ;
  #val #[ FP2_SQRT ] : fp2_sqrt_inp → fp2_sqrt_out ;
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
  #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ;
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ] [(G2_SIMPLE_SWU_ISO,(
      g2_simple_swu_iso_inp,g2_simple_swu_iso_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(u_2337) := temp_inp : fp2_t in
    
    let fp2_is_square := fun x_0 => package_both fp2_is_square (x_0) in
    let fp2_sgn0 := fun x_0 => package_both fp2_sgn0 (x_0) in
    let fp2_sqrt := fun x_0 => package_both fp2_sqrt (x_0) in
    let fp2add := fun x_0 x_1 => package_both fp2add (x_0,x_1) in
    let fp2fromfp := fun x_0 => package_both fp2fromfp (x_0) in
    let fp2inv := fun x_0 => package_both fp2inv (x_0) in
    let fp2mul := fun x_0 x_1 => package_both fp2mul (x_0,x_1) in
    let fp2neg := fun x_0 => package_both fp2neg (x_0) in
    let fp2zero := package_both fp2zero tt in
    ((letb z_2334 : (fp_t '× fp_t) :=
          fp2neg (prod_b(nat_mod_two , nat_mod_one )) in
        letb a_2335 : (fp_t '× fp_t) :=
          prod_b(
            nat_mod_zero ,
            nat_mod_from_literal (_) (lift_to_both0 (@repr U128 240))
          ) in
        letb b_2336 : (fp_t '× fp_t) :=
          prod_b(
            nat_mod_from_literal (_) (lift_to_both0 (@repr U128 1012)),
            nat_mod_from_literal (_) (lift_to_both0 (@repr U128 1012))
          ) in
        letb tv1_2338 : (fp_t '× fp_t) :=
          fp2inv (fp2add (fp2mul (fp2mul (lift_to_both0 z_2334) (
                  lift_to_both0 z_2334)) (fp2mul (fp2mul (
                    lift_to_both0 u_2337) (lift_to_both0 u_2337)) (fp2mul (
                    lift_to_both0 u_2337) (lift_to_both0 u_2337)))) (fp2mul (
                lift_to_both0 z_2334) (fp2mul (lift_to_both0 u_2337) (
                  lift_to_both0 u_2337)))) in
        letbm x1_2330 : (fp_t '× fp_t) loc( x1_2330_loc ) :=
          fp2mul (fp2mul (fp2neg (lift_to_both0 b_2336)) (fp2inv (
                lift_to_both0 a_2335))) (fp2add (fp2fromfp (nat_mod_one )) (
              lift_to_both0 tv1_2338)) in
        letb 'x1_2330 :=
          if (lift_to_both0 tv1_2338) =.? (fp2zero ) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset ([x1_2330_loc])) (L2 := CEfset (
            [x1_2330_loc ; y_2331_loc])) (I1 := [interface
          #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
          #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ]) (I2 := [interface
          #val #[ FP2_IS_SQUARE ] : fp2_is_square_inp → fp2_is_square_out ;
          #val #[ FP2_SGN0 ] : fp2_sgn0_inp → fp2_sgn0_out ;
          #val #[ FP2_SQRT ] : fp2_sqrt_inp → fp2_sqrt_out ;
          #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
          #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
          #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
          #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
          #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ;
          #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm x1_2330 loc( x1_2330_loc ) :=
              fp2mul (lift_to_both0 b_2336) (fp2inv (fp2mul (
                    lift_to_both0 z_2334) (lift_to_both0 a_2335))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 x1_2330)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 x1_2330)
           in
        letb gx1_2339 : (fp_t '× fp_t) :=
          fp2add (fp2add (fp2mul (fp2mul (lift_to_both0 x1_2330) (
                  lift_to_both0 x1_2330)) (lift_to_both0 x1_2330)) (fp2mul (
                lift_to_both0 a_2335) (lift_to_both0 x1_2330))) (
            lift_to_both0 b_2336) in
        letb x2_2340 : (fp_t '× fp_t) :=
          fp2mul (fp2mul (lift_to_both0 z_2334) (fp2mul (lift_to_both0 u_2337) (
                lift_to_both0 u_2337))) (lift_to_both0 x1_2330) in
        letb gx2_2341 : (fp_t '× fp_t) :=
          fp2add (fp2add (fp2mul (fp2mul (lift_to_both0 x2_2340) (
                  lift_to_both0 x2_2340)) (lift_to_both0 x2_2340)) (fp2mul (
                lift_to_both0 a_2335) (lift_to_both0 x2_2340))) (
            lift_to_both0 b_2336) in
        letb '(x_2342, y_2331) : ((fp_t '× fp_t) '× fp2_t) :=
          if is_pure (I := [interface]) (fp2_is_square (lift_to_both0 gx1_2339))
          then prod_b(lift_to_both0 x1_2330, fp2_sqrt (lift_to_both0 gx1_2339))
          else prod_b(lift_to_both0 x2_2340, fp2_sqrt (lift_to_both0 gx2_2341)
          ) in
        letb 'y_2331 :=
          if (fp2_sgn0 (lift_to_both0 u_2337)) !=.? (fp2_sgn0 (
              lift_to_both0 y_2331)) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset (
            [x1_2330_loc ; y_2331_loc])) (L2 := CEfset (
            [x1_2330_loc ; y_2331_loc])) (I1 := [interface
          #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ]) (I2 := [interface
          #val #[ FP2_IS_SQUARE ] : fp2_is_square_inp → fp2_is_square_out ;
          #val #[ FP2_SGN0 ] : fp2_sgn0_inp → fp2_sgn0_out ;
          #val #[ FP2_SQRT ] : fp2_sqrt_inp → fp2_sqrt_out ;
          #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
          #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
          #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
          #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
          #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ;
          #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm y_2331 loc( y_2331_loc ) := fp2neg (lift_to_both0 y_2331) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 y_2331)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 y_2331)
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 x_2342,
            lift_to_both0 y_2331
          ))
        ) : both (CEfset ([x1_2330_loc ; y_2331_loc])) [interface
      #val #[ FP2_IS_SQUARE ] : fp2_is_square_inp → fp2_is_square_out ;
      #val #[ FP2_SGN0 ] : fp2_sgn0_inp → fp2_sgn0_out ;
      #val #[ FP2_SQRT ] : fp2_sqrt_inp → fp2_sqrt_out ;
      #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
      #val #[ FP2NEG ] : fp2neg_inp → fp2neg_out ;
      #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ] ((fp2_t '× fp2_t))))in
  both_package' _ _ (G2_SIMPLE_SWU_ISO,(
      g2_simple_swu_iso_inp,g2_simple_swu_iso_out)) temp_package_both.
Fail Next Obligation.

Definition xnum_k_2344_loc : ChoiceEqualityLocation :=
  (seq (fp_t '× fp_t) ; 2357%nat).
Definition xden_k_2345_loc : ChoiceEqualityLocation :=
  (seq (fp_t '× fp_t) ; 2358%nat).
Definition xx_2351_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2359%nat).
Definition yden_k_2347_loc : ChoiceEqualityLocation :=
  (seq (fp_t '× fp_t) ; 2360%nat).
Definition xx_2349_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2361%nat).
Definition inf_2356_loc : ChoiceEqualityLocation :=
  (bool_ChoiceEquality ; 2362%nat).
Definition xden_2350_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2363%nat).
Definition xnum_2348_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2364%nat).
Definition xx_2355_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2365%nat).
Definition yden_2354_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2366%nat).
Definition xx_2353_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2367%nat).
Definition ynum_k_2346_loc : ChoiceEqualityLocation :=
  (seq (fp_t '× fp_t) ; 2368%nat).
Definition ynum_2352_loc : ChoiceEqualityLocation :=
  ((fp_t '× fp_t) ; 2369%nat).
Notation "'g2_isogeny_map_inp'" :=(
  fp2_t '× fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_isogeny_map_inp'" :=(
  fp2_t '× fp2_t : ChoiceEquality) (at level 2).
Notation "'g2_isogeny_map_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_isogeny_map_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_ISOGENY_MAP : nat :=
  2378.
Program Definition g2_isogeny_map
  : both_package (CEfset (
      [xnum_k_2344_loc ; xden_k_2345_loc ; ynum_k_2346_loc ; yden_k_2347_loc ; xnum_2348_loc ; xx_2349_loc ; xden_2350_loc ; xx_2351_loc ; ynum_2352_loc ; xx_2353_loc ; yden_2354_loc ; xx_2355_loc ; inf_2356_loc])) [interface
  #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
  #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
  #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
  #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
  #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ] [(G2_ISOGENY_MAP,(
      g2_isogeny_map_inp,g2_isogeny_map_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_2371 , y_2376) := temp_inp : fp2_t '× fp2_t in
    
    let fp2add := fun x_0 x_1 => package_both fp2add (x_0,x_1) in
    let fp2fromfp := fun x_0 => package_both fp2fromfp (x_0) in
    let fp2inv := fun x_0 => package_both fp2inv (x_0) in
    let fp2mul := fun x_0 x_1 => package_both fp2mul (x_0,x_1) in
    let fp2zero := package_both fp2zero tt in
    ((letbm xnum_k_2344 : seq (fp_t '× fp_t) loc( xnum_k_2344_loc ) :=
          seq_new_ (default : fp2_t) (lift_to_both0 (usize 4)) in
        letb xnum_k_2344 : seq (fp_t '× fp_t) :=
          seq_upd xnum_k_2344 (lift_to_both0 (usize 0)) (is_pure (prod_b(
                nat_mod_from_byte_seq_be (array_to_be_bytes (
                    lift_to_both0 g2_xnum_k_0_v)),
                nat_mod_from_byte_seq_be (array_to_be_bytes (
                    lift_to_both0 g2_xnum_k_0_v))
              ))) in
        letb xnum_k_2344 : seq (fp_t '× fp_t) :=
          seq_upd xnum_k_2344 (lift_to_both0 (usize 1)) (is_pure (prod_b(
                nat_mod_zero ,
                nat_mod_from_byte_seq_be (array_to_be_bytes (
                    lift_to_both0 g2_xnum_k_1_i_v))
              ))) in
        letb xnum_k_2344 : seq (fp_t '× fp_t) :=
          seq_upd xnum_k_2344 (lift_to_both0 (usize 2)) (is_pure (prod_b(
                nat_mod_from_byte_seq_be (array_to_be_bytes (
                    lift_to_both0 g2_xnum_k_2_r_v)),
                nat_mod_from_byte_seq_be (array_to_be_bytes (
                    lift_to_both0 g2_xnum_k_2_i_v))
              ))) in
        letb xnum_k_2344 : seq (fp_t '× fp_t) :=
          seq_upd xnum_k_2344 (lift_to_both0 (usize 3)) (is_pure (prod_b(
                nat_mod_from_byte_seq_be (array_to_be_bytes (
                    lift_to_both0 g2_xnum_k_3_r_v)),
                nat_mod_zero 
              ))) in
        letbm xden_k_2345 : seq (fp_t '× fp_t) loc( xden_k_2345_loc ) :=
          seq_new_ (default : fp2_t) (lift_to_both0 (usize 2)) in
        letb xden_k_2345 : seq (fp_t '× fp_t) :=
          seq_upd xden_k_2345 (lift_to_both0 (usize 0)) (is_pure (prod_b(
                nat_mod_zero ,
                nat_mod_from_byte_seq_be (array_to_be_bytes (
                    lift_to_both0 g2_xden_k_0_i_v))
              ))) in
        letb xden_k_2345 : seq (fp_t '× fp_t) :=
          seq_upd xden_k_2345 (lift_to_both0 (usize 1)) (is_pure (prod_b(
                nat_mod_from_literal (_) (lift_to_both0 (@repr U128 12)),
                nat_mod_from_byte_seq_be (array_to_be_bytes (
                    lift_to_both0 g2_xden_k_1_i_v))
              ))) in
        letbm ynum_k_2346 : seq (fp_t '× fp_t) loc( ynum_k_2346_loc ) :=
          seq_new_ (default : fp2_t) (lift_to_both0 (usize 4)) in
        letb ynum_k_2346 : seq (fp_t '× fp_t) :=
          seq_upd ynum_k_2346 (lift_to_both0 (usize 0)) (is_pure (prod_b(
                nat_mod_from_byte_seq_be (array_to_be_bytes (
                    lift_to_both0 g2_ynum_k_0_v)),
                nat_mod_from_byte_seq_be (array_to_be_bytes (
                    lift_to_both0 g2_ynum_k_0_v))
              ))) in
        letb ynum_k_2346 : seq (fp_t '× fp_t) :=
          seq_upd ynum_k_2346 (lift_to_both0 (usize 1)) (is_pure (prod_b(
                nat_mod_zero ,
                nat_mod_from_byte_seq_be (array_to_be_bytes (
                    lift_to_both0 g2_ynum_k_1_i_v))
              ))) in
        letb ynum_k_2346 : seq (fp_t '× fp_t) :=
          seq_upd ynum_k_2346 (lift_to_both0 (usize 2)) (is_pure (prod_b(
                nat_mod_from_byte_seq_be (array_to_be_bytes (
                    lift_to_both0 g2_ynum_k_2_r_v)),
                nat_mod_from_byte_seq_be (array_to_be_bytes (
                    lift_to_both0 g2_ynum_k_2_i_v))
              ))) in
        letb ynum_k_2346 : seq (fp_t '× fp_t) :=
          seq_upd ynum_k_2346 (lift_to_both0 (usize 3)) (is_pure (prod_b(
                nat_mod_from_byte_seq_be (array_to_be_bytes (
                    lift_to_both0 g2_ynum_k_3_r_v)),
                nat_mod_zero 
              ))) in
        letbm yden_k_2347 : seq (fp_t '× fp_t) loc( yden_k_2347_loc ) :=
          seq_new_ (default : fp2_t) (lift_to_both0 (usize 3)) in
        letb yden_k_2347 : seq (fp_t '× fp_t) :=
          seq_upd yden_k_2347 (lift_to_both0 (usize 0)) (is_pure (prod_b(
                nat_mod_from_byte_seq_be (array_to_be_bytes (
                    lift_to_both0 g2_yden_k_0_v)),
                nat_mod_from_byte_seq_be (array_to_be_bytes (
                    lift_to_both0 g2_yden_k_0_v))
              ))) in
        letb yden_k_2347 : seq (fp_t '× fp_t) :=
          seq_upd yden_k_2347 (lift_to_both0 (usize 1)) (is_pure (prod_b(
                nat_mod_zero ,
                nat_mod_from_byte_seq_be (array_to_be_bytes (
                    lift_to_both0 g2_yden_k_1_i_v))
              ))) in
        letb yden_k_2347 : seq (fp_t '× fp_t) :=
          seq_upd yden_k_2347 (lift_to_both0 (usize 2)) (is_pure (prod_b(
                nat_mod_from_literal (_) (lift_to_both0 (@repr U128 18)),
                nat_mod_from_byte_seq_be (array_to_be_bytes (
                    lift_to_both0 g2_yden_k_2_i_v))
              ))) in
        letbm xnum_2348 : (fp_t '× fp_t) loc( xnum_2348_loc ) := fp2zero  in
        letbm xx_2349 : (fp_t '× fp_t) loc( xx_2349_loc ) :=
          fp2fromfp (nat_mod_one ) in
        letb '(xnum_2348, xx_2349) :=
          foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                lift_to_both0 xnum_k_2344)) prod_ce(xnum_2348, xx_2349) (L := (
              CEfset (
                [xnum_k_2344_loc ; xden_k_2345_loc ; ynum_k_2346_loc ; yden_k_2347_loc ; xnum_2348_loc ; xx_2349_loc ; xden_2350_loc ; xx_2351_loc ; ynum_2352_loc ; xx_2353_loc ; yden_2354_loc ; xx_2355_loc ; inf_2356_loc]))) (I := (
              [interface #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
              #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
              #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
              #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ])) (fun i_2370 '(
              xnum_2348,
              xx_2349
            ) =>
            letbm xnum_2348 loc( xnum_2348_loc ) :=
              fp2add (lift_to_both0 xnum_2348) (fp2mul (lift_to_both0 xx_2349) (
                  seq_index (xnum_k_2344) (lift_to_both0 i_2370))) in
            letbm xx_2349 loc( xx_2349_loc ) :=
              fp2mul (lift_to_both0 xx_2349) (lift_to_both0 x_2371) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 xnum_2348,
                lift_to_both0 xx_2349
              ))
            ) in
        letbm xden_2350 : (fp_t '× fp_t) loc( xden_2350_loc ) := fp2zero  in
        letbm xx_2351 : (fp_t '× fp_t) loc( xx_2351_loc ) :=
          fp2fromfp (nat_mod_one ) in
        letb '(xden_2350, xx_2351) :=
          foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                lift_to_both0 xden_k_2345)) prod_ce(xden_2350, xx_2351) (L := (
              CEfset (
                [xnum_k_2344_loc ; xden_k_2345_loc ; ynum_k_2346_loc ; yden_k_2347_loc ; xnum_2348_loc ; xx_2349_loc ; xden_2350_loc ; xx_2351_loc ; ynum_2352_loc ; xx_2353_loc ; yden_2354_loc ; xx_2355_loc ; inf_2356_loc]))) (I := (
              [interface #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
              #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
              #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
              #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ])) (fun i_2372 '(
              xden_2350,
              xx_2351
            ) =>
            letbm xden_2350 loc( xden_2350_loc ) :=
              fp2add (lift_to_both0 xden_2350) (fp2mul (lift_to_both0 xx_2351) (
                  seq_index (xden_k_2345) (lift_to_both0 i_2372))) in
            letbm xx_2351 loc( xx_2351_loc ) :=
              fp2mul (lift_to_both0 xx_2351) (lift_to_both0 x_2371) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 xden_2350,
                lift_to_both0 xx_2351
              ))
            ) in
        letbm xden_2350 loc( xden_2350_loc ) :=
          fp2add (lift_to_both0 xden_2350) (lift_to_both0 xx_2351) in
        letbm ynum_2352 : (fp_t '× fp_t) loc( ynum_2352_loc ) := fp2zero  in
        letbm xx_2353 : (fp_t '× fp_t) loc( xx_2353_loc ) :=
          fp2fromfp (nat_mod_one ) in
        letb '(ynum_2352, xx_2353) :=
          foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                lift_to_both0 ynum_k_2346)) prod_ce(ynum_2352, xx_2353) (L := (
              CEfset (
                [xnum_k_2344_loc ; xden_k_2345_loc ; ynum_k_2346_loc ; yden_k_2347_loc ; xnum_2348_loc ; xx_2349_loc ; xden_2350_loc ; xx_2351_loc ; ynum_2352_loc ; xx_2353_loc ; yden_2354_loc ; xx_2355_loc ; inf_2356_loc]))) (I := (
              [interface #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
              #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
              #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
              #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ])) (fun i_2373 '(
              ynum_2352,
              xx_2353
            ) =>
            letbm ynum_2352 loc( ynum_2352_loc ) :=
              fp2add (lift_to_both0 ynum_2352) (fp2mul (lift_to_both0 xx_2353) (
                  seq_index (ynum_k_2346) (lift_to_both0 i_2373))) in
            letbm xx_2353 loc( xx_2353_loc ) :=
              fp2mul (lift_to_both0 xx_2353) (lift_to_both0 x_2371) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 ynum_2352,
                lift_to_both0 xx_2353
              ))
            ) in
        letbm yden_2354 : (fp_t '× fp_t) loc( yden_2354_loc ) := fp2zero  in
        letbm xx_2355 : (fp_t '× fp_t) loc( xx_2355_loc ) :=
          fp2fromfp (nat_mod_one ) in
        letb '(yden_2354, xx_2355) :=
          foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                lift_to_both0 yden_k_2347)) prod_ce(yden_2354, xx_2355) (L := (
              CEfset (
                [xnum_k_2344_loc ; xden_k_2345_loc ; ynum_k_2346_loc ; yden_k_2347_loc ; xnum_2348_loc ; xx_2349_loc ; xden_2350_loc ; xx_2351_loc ; ynum_2352_loc ; xx_2353_loc ; yden_2354_loc ; xx_2355_loc ; inf_2356_loc]))) (I := (
              [interface #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
              #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
              #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
              #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
              #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ])) (fun i_2374 '(
              yden_2354,
              xx_2355
            ) =>
            letbm yden_2354 loc( yden_2354_loc ) :=
              fp2add (lift_to_both0 yden_2354) (fp2mul (lift_to_both0 xx_2355) (
                  seq_index (yden_k_2347) (lift_to_both0 i_2374))) in
            letbm xx_2355 loc( xx_2355_loc ) :=
              fp2mul (lift_to_both0 xx_2355) (lift_to_both0 x_2371) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 yden_2354,
                lift_to_both0 xx_2355
              ))
            ) in
        letbm yden_2354 loc( yden_2354_loc ) :=
          fp2add (lift_to_both0 yden_2354) (lift_to_both0 xx_2355) in
        letb xr_2375 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 xnum_2348) (fp2inv (lift_to_both0 xden_2350)) in
        letb yr_2377 : (fp_t '× fp_t) :=
          fp2mul (lift_to_both0 y_2376) (fp2mul (lift_to_both0 ynum_2352) (
              fp2inv (lift_to_both0 yden_2354))) in
        letbm inf_2356 : bool_ChoiceEquality loc( inf_2356_loc ) :=
          lift_to_both0 ((false : bool_ChoiceEquality)) in
        letb 'inf_2356 :=
          if ((lift_to_both0 xden_2350) =.? (fp2zero )) || ((
              lift_to_both0 yden_2354) =.? (fp2zero )) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset (
            [xnum_k_2344_loc ; xden_k_2345_loc ; ynum_k_2346_loc ; yden_k_2347_loc ; xnum_2348_loc ; xx_2349_loc ; xden_2350_loc ; xx_2351_loc ; ynum_2352_loc ; xx_2353_loc ; yden_2354_loc ; xx_2355_loc ; inf_2356_loc])) (L2 := CEfset (
            [xnum_k_2344_loc ; xden_k_2345_loc ; ynum_k_2346_loc ; yden_k_2347_loc ; xnum_2348_loc ; xx_2349_loc ; xden_2350_loc ; xx_2351_loc ; ynum_2352_loc ; xx_2353_loc ; yden_2354_loc ; xx_2355_loc ; inf_2356_loc])) (I1 := [interface]) (I2 := [interface
          #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
          #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
          #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
          #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
          #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm inf_2356 loc( inf_2356_loc ) :=
              lift_to_both0 ((true : bool_ChoiceEquality)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 inf_2356)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 inf_2356)
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 xr_2375,
            lift_to_both0 yr_2377,
            lift_to_both0 inf_2356
          ))
        ) : both (CEfset (
          [xnum_k_2344_loc ; xden_k_2345_loc ; ynum_k_2346_loc ; yden_k_2347_loc ; xnum_2348_loc ; xx_2349_loc ; xden_2350_loc ; xx_2351_loc ; ynum_2352_loc ; xx_2353_loc ; yden_2354_loc ; xx_2355_loc ; inf_2356_loc])) [interface
      #val #[ FP2ADD ] : fp2add_inp → fp2add_out ;
      #val #[ FP2FROMFP ] : fp2fromfp_inp → fp2fromfp_out ;
      #val #[ FP2INV ] : fp2inv_inp → fp2inv_out ;
      #val #[ FP2MUL ] : fp2mul_inp → fp2mul_out ;
      #val #[ FP2ZERO ] : fp2zero_inp → fp2zero_out ] (g2_t)))in
  both_package' _ _ (G2_ISOGENY_MAP,(
      g2_isogeny_map_inp,g2_isogeny_map_out)) temp_package_both.
Fail Next Obligation.


Notation "'g2_map_to_curve_sswu_inp'" :=(
  fp2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_map_to_curve_sswu_inp'" :=(fp2_t : ChoiceEquality) (at level 2).
Notation "'g2_map_to_curve_sswu_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_map_to_curve_sswu_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_MAP_TO_CURVE_SSWU : nat :=
  2383.
Program Definition g2_map_to_curve_sswu
  : both_package (CEfset ([])) [interface
  #val #[ G2_ISOGENY_MAP ] : g2_isogeny_map_inp → g2_isogeny_map_out ;
  #val #[ G2_SIMPLE_SWU_ISO ] : g2_simple_swu_iso_inp → g2_simple_swu_iso_out
  ] [(G2_MAP_TO_CURVE_SSWU,(
      g2_map_to_curve_sswu_inp,g2_map_to_curve_sswu_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(u_2379) := temp_inp : fp2_t in
    
    let g2_isogeny_map := fun x_0 x_1 => package_both g2_isogeny_map (
      x_0,x_1) in
    let g2_simple_swu_iso := fun x_0 => package_both g2_simple_swu_iso (x_0) in
    ((letb '(xp_2380, yp_2381) : (fp2_t '× fp2_t) :=
          g2_simple_swu_iso (lift_to_both0 u_2379) in
        letb p_2382 : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          g2_isogeny_map (lift_to_both0 xp_2380) (lift_to_both0 yp_2381) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2382)
        ) : both (CEfset ([])) [interface
      #val #[ G2_ISOGENY_MAP ] : g2_isogeny_map_inp → g2_isogeny_map_out ;
      #val #[ G2_SIMPLE_SWU_ISO ] : g2_simple_swu_iso_inp → g2_simple_swu_iso_out
      ] (g2_t)))in
  both_package' _ _ (G2_MAP_TO_CURVE_SSWU,(
      g2_map_to_curve_sswu_inp,g2_map_to_curve_sswu_out)) temp_package_both.
Fail Next Obligation.


Notation "'g2_hash_to_curve_sswu_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g2_hash_to_curve_sswu_inp'" :=(
  byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'g2_hash_to_curve_sswu_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_hash_to_curve_sswu_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_HASH_TO_CURVE_SSWU : nat :=
  2391.
Program Definition g2_hash_to_curve_sswu
  : both_package (CEfset ([])) [interface
  #val #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out ;
  #val #[ G2_CLEAR_COFACTOR ] : g2_clear_cofactor_inp → g2_clear_cofactor_out ;
  #val #[ G2_MAP_TO_CURVE_SSWU ] : g2_map_to_curve_sswu_inp → g2_map_to_curve_sswu_out ;
  #val #[ G2ADD ] : g2add_inp → g2add_out ] [(G2_HASH_TO_CURVE_SSWU,(
      g2_hash_to_curve_sswu_inp,g2_hash_to_curve_sswu_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(msg_2384 , dst_2385) := temp_inp : byte_seq '× byte_seq in
    
    let fp2_hash_to_field := fun x_0 x_1 x_2 => package_both fp2_hash_to_field (
      x_0,x_1,x_2) in
    let g2_clear_cofactor := fun x_0 => package_both g2_clear_cofactor (x_0) in
    let g2_map_to_curve_sswu := fun x_0 => package_both g2_map_to_curve_sswu (
      x_0) in
    let g2add := fun x_0 x_1 => package_both g2add (x_0,x_1) in
    ((letb u_2386 : seq fp2_t :=
          fp2_hash_to_field (lift_to_both0 msg_2384) (lift_to_both0 dst_2385) (
            lift_to_both0 (usize 2)) in
        letb q0_2387 : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          g2_map_to_curve_sswu (seq_index (u_2386) (lift_to_both0 (usize 0))) in
        letb q1_2388 : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          g2_map_to_curve_sswu (seq_index (u_2386) (lift_to_both0 (usize 1))) in
        letb r_2389 : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          g2add (lift_to_both0 q0_2387) (lift_to_both0 q1_2388) in
        letb p_2390 : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          g2_clear_cofactor (lift_to_both0 r_2389) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2390)
        ) : both (CEfset ([])) [interface
      #val #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out ;
      #val #[ G2_CLEAR_COFACTOR ] : g2_clear_cofactor_inp → g2_clear_cofactor_out ;
      #val #[ G2_MAP_TO_CURVE_SSWU ] : g2_map_to_curve_sswu_inp → g2_map_to_curve_sswu_out ;
      #val #[ G2ADD ] : g2add_inp → g2add_out ] (g2_t)))in
  both_package' _ _ (G2_HASH_TO_CURVE_SSWU,(
      g2_hash_to_curve_sswu_inp,g2_hash_to_curve_sswu_out)) temp_package_both.
Fail Next Obligation.


Notation "'g2_encode_to_curve_sswu_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'g2_encode_to_curve_sswu_inp'" :=(
  byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'g2_encode_to_curve_sswu_out'" :=(
  g2_t : choice_type) (in custom pack_type at level 2).
Notation "'g2_encode_to_curve_sswu_out'" :=(g2_t : ChoiceEquality) (at level 2).
Definition G2_ENCODE_TO_CURVE_SSWU : nat :=
  2397.
Program Definition g2_encode_to_curve_sswu
  : both_package (CEfset ([])) [interface
  #val #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out ;
  #val #[ G2_CLEAR_COFACTOR ] : g2_clear_cofactor_inp → g2_clear_cofactor_out ;
  #val #[ G2_MAP_TO_CURVE_SSWU ] : g2_map_to_curve_sswu_inp → g2_map_to_curve_sswu_out
  ] [(G2_ENCODE_TO_CURVE_SSWU,(
      g2_encode_to_curve_sswu_inp,g2_encode_to_curve_sswu_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(msg_2392 , dst_2393) := temp_inp : byte_seq '× byte_seq in
    
    let fp2_hash_to_field := fun x_0 x_1 x_2 => package_both fp2_hash_to_field (
      x_0,x_1,x_2) in
    let g2_clear_cofactor := fun x_0 => package_both g2_clear_cofactor (x_0) in
    let g2_map_to_curve_sswu := fun x_0 => package_both g2_map_to_curve_sswu (
      x_0) in
    ((letb u_2394 : seq fp2_t :=
          fp2_hash_to_field (lift_to_both0 msg_2392) (lift_to_both0 dst_2393) (
            lift_to_both0 (usize 1)) in
        letb q_2395 : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          g2_map_to_curve_sswu (seq_index (u_2394) (lift_to_both0 (usize 0))) in
        letb p_2396 : (
            (fp_t '× fp_t) '×
            (fp_t '× fp_t) '×
            bool_ChoiceEquality
          ) :=
          g2_clear_cofactor (lift_to_both0 q_2395) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p_2396)
        ) : both (CEfset ([])) [interface
      #val #[ FP2_HASH_TO_FIELD ] : fp2_hash_to_field_inp → fp2_hash_to_field_out ;
      #val #[ G2_CLEAR_COFACTOR ] : g2_clear_cofactor_inp → g2_clear_cofactor_out ;
      #val #[ G2_MAP_TO_CURVE_SSWU ] : g2_map_to_curve_sswu_inp → g2_map_to_curve_sswu_out
      ] (g2_t)))in
  both_package' _ _ (G2_ENCODE_TO_CURVE_SSWU,(
      g2_encode_to_curve_sswu_inp,g2_encode_to_curve_sswu_out)) temp_package_both.
Fail Next Obligation.

