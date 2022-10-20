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


Require Import Hacspec_Edwards25519.

Require Import Hacspec_Sha512.

Definition b_in_bytes_v : uint_size :=
  usize 64.

Definition s_in_bytes_v : uint_size :=
  usize 128.

Definition l_v : uint_size :=
  usize 48.

Definition j_v : int128 :=
  @repr U128 486662.

Definition z_v : int128 :=
  @repr U128 2.

Definition arr_ed25519_field_element_t := nseq (uint64) (usize 4).

Definition ed_field_hash_canvas_t := nseq (int8) (usize 64).
Definition ed_field_hash_t :=
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Definition error_t : ChoiceEquality :=
  unit_ChoiceEquality.
Definition ExpandMessageAbort : error_t :=
   tt.

Notation "'byte_seq_result_t'" := ((result error_t byte_seq)) : hacspec_scope.

Notation "'seq_ed_result_t'" := ((
  result error_t seq ed25519_field_element_t)) : hacspec_scope.

Notation "'ed_point_result_t'" := ((result error_t ed_point_t)) : hacspec_scope.

Definition p_1_2_v : arr_ed25519_field_element_t :=
  array_from_list uint64 [
    (secret (@repr U64 4611686018427387903)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551606)) : uint64
  ].

Definition p_3_8_v : arr_ed25519_field_element_t :=
  array_from_list uint64 [
    (secret (@repr U64 1152921504606846975)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551614)) : uint64
  ].

Definition p_5_8_v : arr_ed25519_field_element_t :=
  array_from_list uint64 [
    (secret (@repr U64 1152921504606846975)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551615)) : uint64;
    (secret (@repr U64 18446744073709551613)) : uint64
  ].

Definition l_i_b_str_2778_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2781%nat).
Definition uniform_bytes_2780_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2782%nat).
Definition result_2777_loc : ChoiceEqualityLocation :=
  ((result (error_t) (byte_seq)) ; 2783%nat).
Definition b_i_2779_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 2784%nat).
Notation "'expand_message_xmd_inp'" :=(
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'expand_message_xmd_inp'" :=(
  byte_seq '× byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'expand_message_xmd_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'expand_message_xmd_out'" :=(
  byte_seq_result_t : ChoiceEquality) (at level 2).
Definition EXPAND_MESSAGE_XMD : nat :=
  2795.
Program Definition expand_message_xmd
  : both_package (CEfset (
      [result_2777_loc ; l_i_b_str_2778_loc ; b_i_2779_loc ; uniform_bytes_2780_loc])) [interface
  #val #[ HASH ] : hash_inp → hash_out ] [(EXPAND_MESSAGE_XMD,(
      expand_message_xmd_inp,expand_message_xmd_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      msg_2790 , dst_2787 , len_in_bytes_2785) := temp_inp : byte_seq '× byte_seq '× uint_size in
    
    let hash := fun x_0 => package_both hash (x_0) in
    ((letb ell_2786 : uint_size :=
          (((lift_to_both0 len_in_bytes_2785) .+ (
                lift_to_both0 b_in_bytes_v)) .- (lift_to_both0 (usize 1))) ./ (
            lift_to_both0 b_in_bytes_v) in
        letbm result_2777 : (result (error_t) (
              byte_seq)) loc( result_2777_loc ) :=
          @Err byte_seq error_t (ExpandMessageAbort) in
        letb 'result_2777 :=
          if negb ((((lift_to_both0 ell_2786) >.? (lift_to_both0 (
                    usize 255))) || ((lift_to_both0 len_in_bytes_2785) >.? (
                  lift_to_both0 (usize 65535)))) || ((seq_len (
                  lift_to_both0 dst_2787)) >.? (lift_to_both0 (
                  usize 255)))) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset (
            [result_2777_loc ; l_i_b_str_2778_loc ; b_i_2779_loc ; uniform_bytes_2780_loc])) (L2 := CEfset (
            [result_2777_loc ; l_i_b_str_2778_loc ; b_i_2779_loc ; uniform_bytes_2780_loc])) (I1 := [interface
          #val #[ HASH ] : hash_inp → hash_out ]) (I2 := [interface
          #val #[ HASH ] : hash_inp → hash_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letb dst_prime_2788 : seq uint8 :=
              seq_push (lift_to_both0 dst_2787) (uint8_from_usize (seq_len (
                    lift_to_both0 dst_2787))) in
            letb z_pad_2789 : seq uint8 :=
              seq_new_ (default : uint8) (lift_to_both0 s_in_bytes_v) in
            letbm l_i_b_str_2778 : seq uint8 loc( l_i_b_str_2778_loc ) :=
              seq_new_ (default : uint8) (lift_to_both0 (usize 2)) in
            letb l_i_b_str_2778 : seq uint8 :=
              seq_upd l_i_b_str_2778 (lift_to_both0 (usize 0)) (is_pure (
                  uint8_from_usize ((lift_to_both0 len_in_bytes_2785) ./ (
                      lift_to_both0 (usize 256))))) in
            letb l_i_b_str_2778 : seq uint8 :=
              seq_upd l_i_b_str_2778 (lift_to_both0 (usize 1)) (is_pure (
                  uint8_from_usize (lift_to_both0 len_in_bytes_2785))) in
            letb msg_prime_2791 : seq uint8 :=
              seq_concat (seq_concat (seq_concat (seq_concat (
                      lift_to_both0 z_pad_2789) (lift_to_both0 msg_2790)) (
                    lift_to_both0 l_i_b_str_2778)) (seq_new_ (default : uint8) (
                    lift_to_both0 (usize 1)))) (lift_to_both0 dst_prime_2788) in
            letb b_0_2792 : seq uint8 :=
              seq_from_seq (array_to_seq (hash (
                  lift_to_both0 msg_prime_2791))) in
            letbm b_i_2779 : seq uint8 loc( b_i_2779_loc ) :=
              seq_from_seq (array_to_seq (hash (seq_concat (seq_push (
                      lift_to_both0 b_0_2792) (secret (lift_to_both0 (
                          @repr U8 1)))) (lift_to_both0 dst_prime_2788)))) in
            letbm uniform_bytes_2780 : seq uint8 loc( uniform_bytes_2780_loc ) :=
              seq_from_seq (lift_to_both0 b_i_2779) in
            letb '(b_i_2779, uniform_bytes_2780) :=
              foldi_both' (lift_to_both0 (usize 2)) ((
                    lift_to_both0 ell_2786) .+ (lift_to_both0 (
                      usize 1))) prod_ce(b_i_2779, uniform_bytes_2780) (L := (
                  CEfset (
                    [result_2777_loc ; l_i_b_str_2778_loc ; b_i_2779_loc ; uniform_bytes_2780_loc]))) (I := (
                  [interface #val #[ HASH ] : hash_inp → hash_out
                  ])) (fun i_2793 '(b_i_2779, uniform_bytes_2780) =>
                letb t_2794 : seq uint8 :=
                  seq_from_seq (lift_to_both0 b_0_2792) in
                letbm b_i_2779 loc( b_i_2779_loc ) :=
                  seq_from_seq (array_to_seq (hash (seq_concat (seq_push ((
                            lift_to_both0 t_2794) seq_xor (
                            lift_to_both0 b_i_2779)) (uint8_from_usize (
                            lift_to_both0 i_2793))) (
                        lift_to_both0 dst_prime_2788)))) in
                letbm uniform_bytes_2780 loc( uniform_bytes_2780_loc ) :=
                  seq_concat (lift_to_both0 uniform_bytes_2780) (
                    lift_to_both0 b_i_2779) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 b_i_2779,
                    lift_to_both0 uniform_bytes_2780
                  ))
                ) in
            letbm result_2777 loc( result_2777_loc ) :=
              @Ok byte_seq error_t (seq_truncate (
                  lift_to_both0 uniform_bytes_2780) (
                  lift_to_both0 len_in_bytes_2785)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 result_2777)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 result_2777)
           in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 result_2777)
        ) : both (CEfset (
          [result_2777_loc ; l_i_b_str_2778_loc ; b_i_2779_loc ; uniform_bytes_2780_loc])) [interface
      #val #[ HASH ] : hash_inp → hash_out ] (byte_seq_result_t)))in
  both_package' _ _ (EXPAND_MESSAGE_XMD,(
      expand_message_xmd_inp,expand_message_xmd_out)) temp_package_both.
Fail Next Obligation.

Definition output_2796_loc : ChoiceEqualityLocation :=
  (seq ed25519_field_element_t ; 2797%nat).
Notation "'ed_hash_to_field_inp'" :=(
  byte_seq '× byte_seq '× uint_size : choice_type) (in custom pack_type at level 2).
Notation "'ed_hash_to_field_inp'" :=(
  byte_seq '× byte_seq '× uint_size : ChoiceEquality) (at level 2).
Notation "'ed_hash_to_field_out'" :=(
  seq_ed_result_t : choice_type) (in custom pack_type at level 2).
Notation "'ed_hash_to_field_out'" :=(
  seq_ed_result_t : ChoiceEquality) (at level 2).
Definition ED_HASH_TO_FIELD : nat :=
  2807.
Program Definition ed_hash_to_field
  : both_package (CEfset ([output_2796_loc])) [interface
  #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
  ] [(ED_HASH_TO_FIELD,(ed_hash_to_field_inp,ed_hash_to_field_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      msg_2800 , dst_2801 , count_2798) := temp_inp : byte_seq '× byte_seq '× uint_size in
    
    let expand_message_xmd := fun x_0 x_1 x_2 => package_both expand_message_xmd (
      x_0,x_1,x_2) in
    ((letb len_in_bytes_2799 : uint_size :=
          (lift_to_both0 count_2798) .* (lift_to_both0 l_v) in
        letbnd(_) uniform_bytes_2802 : byte_seq :=
          expand_message_xmd (lift_to_both0 msg_2800) (lift_to_both0 dst_2801) (
            lift_to_both0 len_in_bytes_2799) in
        letbm output_2796 : seq ed25519_field_element_t loc( output_2796_loc ) :=
          seq_new_ (default : ed25519_field_element_t) (
            lift_to_both0 count_2798) in
        letb output_2796 :=
          foldi_both' (lift_to_both0 (usize 0)) (
              lift_to_both0 count_2798) output_2796 (L := (CEfset (
                [output_2796_loc]))) (I := ([interface
              #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
              ])) (fun i_2803 output_2796 =>
            letb elm_offset_2804 : uint_size :=
              (lift_to_both0 l_v) .* (lift_to_both0 i_2803) in
            letb tv_2805 : seq uint8 :=
              seq_slice (lift_to_both0 uniform_bytes_2802) (
                lift_to_both0 elm_offset_2804) (lift_to_both0 l_v) in
            letb u_i_2806 : ed25519_field_element_t :=
              nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
                    nat_mod_from_byte_seq_be (lift_to_both0 tv_2805))) (
                  lift_to_both0 (usize 32)) (lift_to_both0 (usize 32))) in
            letb output_2796 : seq ed25519_field_element_t :=
              seq_upd output_2796 (lift_to_both0 i_2803) (is_pure (
                  lift_to_both0 u_i_2806)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 output_2796)
            ) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok seq ed25519_field_element_t error_t (lift_to_both0 output_2796))
        ) : both (CEfset ([output_2796_loc])) [interface
      #val #[ EXPAND_MESSAGE_XMD ] : expand_message_xmd_inp → expand_message_xmd_out
      ] (seq_ed_result_t)))in
  both_package' _ _ (ED_HASH_TO_FIELD,(
      ed_hash_to_field_inp,ed_hash_to_field_out)) temp_package_both.
Fail Next Obligation.


Notation "'ed_is_square_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'ed_is_square_inp'" :=(
  ed25519_field_element_t : ChoiceEquality) (at level 2).
Notation "'ed_is_square_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'ed_is_square_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition ED_IS_SQUARE : nat :=
  2811.
Program Definition ed_is_square
  : both_package (fset.fset0) [interface] [(ED_IS_SQUARE,(
      ed_is_square_inp,ed_is_square_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_2809) := temp_inp : ed25519_field_element_t in
    
    ((letb c1_2808 : ed25519_field_element_t :=
          nat_mod_from_byte_seq_be (array_to_be_bytes (
              lift_to_both0 p_1_2_v)) in
        letb tv_2810 : ed25519_field_element_t :=
          nat_mod_pow_self (lift_to_both0 x_2809) (lift_to_both0 c1_2808) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
              lift_to_both0 tv_2810) =.? (nat_mod_zero )) || ((
              lift_to_both0 tv_2810) =.? (nat_mod_one )))
        ) : both (fset.fset0) [interface] (bool_ChoiceEquality)))in
  both_package' _ _ (ED_IS_SQUARE,(
      ed_is_square_inp,ed_is_square_out)) temp_package_both.
Fail Next Obligation.


Notation "'sgn0_m_eq_1_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'sgn0_m_eq_1_inp'" :=(
  ed25519_field_element_t : ChoiceEquality) (at level 2).
Notation "'sgn0_m_eq_1_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'sgn0_m_eq_1_out'" :=(
  bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition SGN0_M_EQ_1 : nat :=
  2813.
Program Definition sgn0_m_eq_1
  : both_package (fset.fset0) [interface] [(SGN0_M_EQ_1,(
      sgn0_m_eq_1_inp,sgn0_m_eq_1_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_2812) := temp_inp : ed25519_field_element_t in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
              lift_to_both0 x_2812) rem (nat_mod_two )) =.? (nat_mod_one ))
        ) : both (fset.fset0) [interface] (bool_ChoiceEquality)))in
  both_package' _ _ (SGN0_M_EQ_1,(
      sgn0_m_eq_1_inp,sgn0_m_eq_1_out)) temp_package_both.
Fail Next Obligation.


Notation "'ed_clear_cofactor_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'ed_clear_cofactor_inp'" :=(ed_point_t : ChoiceEquality) (at level 2).
Notation "'ed_clear_cofactor_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'ed_clear_cofactor_out'" :=(ed_point_t : ChoiceEquality) (at level 2).
Definition ED_CLEAR_COFACTOR : nat :=
  2815.
Program Definition ed_clear_cofactor
  : both_package (fset.fset0) [interface
  #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out
  ] [(ED_CLEAR_COFACTOR,(ed_clear_cofactor_inp,ed_clear_cofactor_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(x_2814) := temp_inp : ed_point_t in
    
    let point_mul_by_cofactor := fun x_0 => package_both point_mul_by_cofactor (
      x_0) in
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (point_mul_by_cofactor (
            lift_to_both0 x_2814))
        ) : both (fset.fset0) [interface
      #val #[ POINT_MUL_BY_COFACTOR ] : point_mul_by_cofactor_inp → point_mul_by_cofactor_out
      ] (ed_point_t)))in
  both_package' _ _ (ED_CLEAR_COFACTOR,(
      ed_clear_cofactor_inp,ed_clear_cofactor_out)) temp_package_both.
Fail Next Obligation.


Notation "'cmov_inp'" :=(
  ed25519_field_element_t '× ed25519_field_element_t '× bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'cmov_inp'" :=(
  ed25519_field_element_t '× ed25519_field_element_t '× bool_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'cmov_out'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'cmov_out'" :=(ed25519_field_element_t : ChoiceEquality) (at level 2).
Definition CMOV : nat :=
  2819.
Program Definition cmov
  : both_package (fset.fset0) [interface] [(CMOV,(cmov_inp,cmov_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      a_2818 , b_2817 , c_2816) := temp_inp : ed25519_field_element_t '× ed25519_field_element_t '× bool_ChoiceEquality in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) (lift_to_both0 c_2816)
          then lift_to_both0 b_2817
          else lift_to_both0 a_2818)
        ) : both (fset.fset0) [interface] (ed25519_field_element_t)))in
  both_package' _ _ (CMOV,(cmov_inp,cmov_out)) temp_package_both.
Fail Next Obligation.


Notation "'xor_inp'" :=(
  bool_ChoiceEquality '× bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'xor_inp'" :=(
  bool_ChoiceEquality '× bool_ChoiceEquality : ChoiceEquality) (at level 2).
Notation "'xor_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'xor_out'" :=(bool_ChoiceEquality : ChoiceEquality) (at level 2).
Definition XOR : nat :=
  2822.
Program Definition xor
  : both_package (fset.fset0) [interface] [(XOR,(xor_inp,xor_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(
      a_2820 , b_2821) := temp_inp : bool_ChoiceEquality '× bool_ChoiceEquality in
    
    ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          if is_pure (I := [interface]) (lift_to_both0 a_2820)
          then if is_pure (I := [interface]) (lift_to_both0 b_2821)
          then lift_to_both0 ((false : bool_ChoiceEquality))
          else lift_to_both0 ((true : bool_ChoiceEquality))
          else if is_pure (I := [interface]) (lift_to_both0 b_2821)
          then lift_to_both0 ((true : bool_ChoiceEquality))
          else lift_to_both0 ((false : bool_ChoiceEquality)))
        ) : both (fset.fset0) [interface] (bool_ChoiceEquality)))in
  both_package' _ _ (XOR,(xor_inp,xor_out)) temp_package_both.
Fail Next Obligation.


Notation "'curve25519_to_edwards25519_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'curve25519_to_edwards25519_inp'" :=(
  ed_point_t : ChoiceEquality) (at level 2).
Notation "'curve25519_to_edwards25519_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'curve25519_to_edwards25519_out'" :=(
  ed_point_t : ChoiceEquality) (at level 2).
Definition CURVE25519_TO_EDWARDS25519 : nat :=
  2841.
Program Definition curve25519_to_edwards25519
  : both_package (fset.fset0) [interface
  #val #[ CMOV ] : cmov_inp → cmov_out ;
  #val #[ POINT_NORMALIZE ] : point_normalize_inp → point_normalize_out ;
  #val #[ SQRT ] : sqrt_inp → sqrt_out ] [(CURVE25519_TO_EDWARDS25519,(
      curve25519_to_edwards25519_inp,curve25519_to_edwards25519_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(p_2823) := temp_inp : ed_point_t in
    
    let cmov := fun x_0 x_1 x_2 => package_both cmov (x_0,x_1,x_2) in
    let point_normalize := fun x_0 => package_both point_normalize (x_0) in
    let sqrt := fun x_0 => package_both sqrt (x_0) in
    ((letb '(s_2824, t_2825, _, _) : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          point_normalize (lift_to_both0 p_2823) in
        letb one_2826 : ed25519_field_element_t := nat_mod_one  in
        letb zero_2827 : ed25519_field_element_t := nat_mod_zero  in
        letb tv1_2828 : ed25519_field_element_t :=
          (lift_to_both0 s_2824) +% (lift_to_both0 one_2826) in
        letb tv2_2829 : ed25519_field_element_t :=
          (lift_to_both0 tv1_2828) *% (lift_to_both0 t_2825) in
        letb tv2_2830 : ed25519_field_element_t :=
          nat_mod_inv (lift_to_both0 tv2_2829) in
        letb v_2831 : ed25519_field_element_t :=
          (lift_to_both0 tv2_2830) *% (lift_to_both0 tv1_2828) in
        letb v_2832 : ed25519_field_element_t :=
          (lift_to_both0 v_2831) *% (lift_to_both0 s_2824) in
        letb w_2833 : ed25519_field_element_t :=
          (lift_to_both0 tv2_2830) *% (lift_to_both0 t_2825) in
        letb tv1_2834 : ed25519_field_element_t :=
          (lift_to_both0 s_2824) -% (lift_to_both0 one_2826) in
        letb w_2835 : ed25519_field_element_t :=
          (lift_to_both0 w_2833) *% (lift_to_both0 tv1_2834) in
        letb e_2836 : bool_ChoiceEquality :=
          (lift_to_both0 tv2_2830) =.? (lift_to_both0 zero_2827) in
        letb w_2837 : ed25519_field_element_t :=
          cmov (lift_to_both0 w_2835) (lift_to_both0 one_2826) (
            lift_to_both0 e_2836) in
        letb c_2838 : ed25519_field_element_t :=
          (nat_mod_zero ) -% (nat_mod_from_literal (_) (lift_to_both0 (
                @repr U128 486664))) in
        letb sq_2839 : (option (ed25519_field_element_t)) :=
          sqrt (lift_to_both0 c_2838) in
        letb v_2840 : ed25519_field_element_t :=
          (lift_to_both0 v_2832) *% (option_unwrap (lift_to_both0 sq_2839)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 v_2840,
            lift_to_both0 w_2837,
            lift_to_both0 one_2826,
            (lift_to_both0 v_2840) *% (lift_to_both0 w_2837)
          ))
        ) : both (fset.fset0) [interface
      #val #[ CMOV ] : cmov_inp → cmov_out ;
      #val #[ POINT_NORMALIZE ] : point_normalize_inp → point_normalize_out ;
      #val #[ SQRT ] : sqrt_inp → sqrt_out ] (ed_point_t)))in
  both_package' _ _ (CURVE25519_TO_EDWARDS25519,(
      curve25519_to_edwards25519_inp,curve25519_to_edwards25519_out)) temp_package_both.
Fail Next Obligation.

Definition y_2844_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 2845%nat).
Definition x_2843_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 2846%nat).
Definition x1_2842_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 2847%nat).
Notation "'map_to_curve_elligator2_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_inp'" :=(
  ed25519_field_element_t : ChoiceEquality) (at level 2).
Notation "'map_to_curve_elligator2_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_out'" :=(
  ed_point_t : ChoiceEquality) (at level 2).
Definition MAP_TO_CURVE_ELLIGATOR2 : nat :=
  2858.
Program Definition map_to_curve_elligator2
  : both_package (CEfset ([x1_2842_loc ; x_2843_loc ; y_2844_loc])) [interface
  #val #[ ED_IS_SQUARE ] : ed_is_square_inp → ed_is_square_out ;
  #val #[ SGN0_M_EQ_1 ] : sgn0_m_eq_1_inp → sgn0_m_eq_1_out ;
  #val #[ SQRT ] : sqrt_inp → sqrt_out ] [(MAP_TO_CURVE_ELLIGATOR2,(
      map_to_curve_elligator2_inp,map_to_curve_elligator2_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(u_2852) := temp_inp : ed25519_field_element_t in
    
    let ed_is_square := fun x_0 => package_both ed_is_square (x_0) in
    let sgn0_m_eq_1 := fun x_0 => package_both sgn0_m_eq_1 (x_0) in
    let sqrt := fun x_0 => package_both sqrt (x_0) in
    ((letb j_2848 : ed25519_field_element_t :=
          nat_mod_from_literal (_) (lift_to_both0 j_v) in
        letb z_2849 : ed25519_field_element_t :=
          nat_mod_from_literal (_) (lift_to_both0 z_v) in
        letb one_2850 : ed25519_field_element_t := nat_mod_one  in
        letb zero_2851 : ed25519_field_element_t := nat_mod_zero  in
        letbm x1_2842 : ed25519_field_element_t loc( x1_2842_loc ) :=
          ((lift_to_both0 zero_2851) -% (lift_to_both0 j_2848)) *% (
            nat_mod_inv ((lift_to_both0 one_2850) +% (((
                    lift_to_both0 z_2849) *% (lift_to_both0 u_2852)) *% (
                  lift_to_both0 u_2852)))) in
        letb 'x1_2842 :=
          if (lift_to_both0 x1_2842) =.? (
            lift_to_both0 zero_2851) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset ([x1_2842_loc])) (L2 := CEfset (
            [x1_2842_loc ; x_2843_loc ; y_2844_loc])) (I1 := [interface]) (I2 := [interface
          #val #[ ED_IS_SQUARE ] : ed_is_square_inp → ed_is_square_out ;
          #val #[ SGN0_M_EQ_1 ] : sgn0_m_eq_1_inp → sgn0_m_eq_1_out ;
          #val #[ SQRT ] : sqrt_inp → sqrt_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm x1_2842 loc( x1_2842_loc ) :=
              (lift_to_both0 zero_2851) -% (lift_to_both0 j_2848) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 x1_2842)
            )
          else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 x1_2842)
           in
        letb gx1_2853 : ed25519_field_element_t :=
          ((((lift_to_both0 x1_2842) *% (lift_to_both0 x1_2842)) *% (
                lift_to_both0 x1_2842)) +% (((lift_to_both0 j_2848) *% (
                  lift_to_both0 x1_2842)) *% (lift_to_both0 x1_2842))) +% (
            lift_to_both0 x1_2842) in
        letb x2_2854 : ed25519_field_element_t :=
          ((lift_to_both0 zero_2851) -% (lift_to_both0 x1_2842)) -% (
            lift_to_both0 j_2848) in
        letb gx2_2855 : ed25519_field_element_t :=
          ((((lift_to_both0 x2_2854) *% (lift_to_both0 x2_2854)) *% (
                lift_to_both0 x2_2854)) +% ((lift_to_both0 j_2848) *% ((
                  lift_to_both0 x2_2854) *% (lift_to_both0 x2_2854)))) +% (
            lift_to_both0 x2_2854) in
        letbm x_2843 : ed25519_field_element_t loc( x_2843_loc ) :=
          lift_to_both0 zero_2851 in
        letbm y_2844 : ed25519_field_element_t loc( y_2844_loc ) :=
          lift_to_both0 zero_2851 in
        letb '(x_2843, y_2844) :=
          if ed_is_square (lift_to_both0 gx1_2853) :bool_ChoiceEquality
          then lift_scope (L1 := CEfset (
            [x1_2842_loc ; x_2843_loc ; y_2844_loc])) (L2 := CEfset (
            [x1_2842_loc ; x_2843_loc ; y_2844_loc])) (I1 := [interface
          #val #[ SGN0_M_EQ_1 ] : sgn0_m_eq_1_inp → sgn0_m_eq_1_out ;
          #val #[ SQRT ] : sqrt_inp → sqrt_out ]) (I2 := [interface
          #val #[ ED_IS_SQUARE ] : ed_is_square_inp → ed_is_square_out ;
          #val #[ SGN0_M_EQ_1 ] : sgn0_m_eq_1_inp → sgn0_m_eq_1_out ;
          #val #[ SQRT ] : sqrt_inp → sqrt_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm x_2843 loc( x_2843_loc ) := lift_to_both0 x1_2842 in
            letbm y_2844 loc( y_2844_loc ) :=
              option_unwrap (sqrt (lift_to_both0 gx1_2853)) in
            letb 'y_2844 :=
              if negb (sgn0_m_eq_1 (lift_to_both0 y_2844)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                [x1_2842_loc ; x_2843_loc ; y_2844_loc])) (L2 := CEfset (
                [x1_2842_loc ; x_2843_loc ; y_2844_loc])) (I1 := [interface]) (I2 := [interface
              #val #[ SGN0_M_EQ_1 ] : sgn0_m_eq_1_inp → sgn0_m_eq_1_out ;
              #val #[ SQRT ] : sqrt_inp → sqrt_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm y_2844 loc( y_2844_loc ) :=
                  (lift_to_both0 zero_2851) -% (lift_to_both0 y_2844) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 y_2844)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 y_2844)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 x_2843,
                lift_to_both0 y_2844
              ))
            )
          else  lift_scope (L1 := CEfset (
            [x1_2842_loc ; x_2843_loc ; y_2844_loc])) (L2 := CEfset (
            [x1_2842_loc ; x_2843_loc ; y_2844_loc])) (I1 := [interface
          #val #[ SGN0_M_EQ_1 ] : sgn0_m_eq_1_inp → sgn0_m_eq_1_out ;
          #val #[ SQRT ] : sqrt_inp → sqrt_out ]) (I2 := [interface
          #val #[ ED_IS_SQUARE ] : ed_is_square_inp → ed_is_square_out ;
          #val #[ SGN0_M_EQ_1 ] : sgn0_m_eq_1_inp → sgn0_m_eq_1_out ;
          #val #[ SQRT ] : sqrt_inp → sqrt_out
          ]) (H_loc_incl := _) (H_opsig_incl := _) (
            letbm x_2843 loc( x_2843_loc ) := lift_to_both0 x2_2854 in
            letbm y_2844 loc( y_2844_loc ) :=
              option_unwrap (sqrt (lift_to_both0 gx2_2855)) in
            letb 'y_2844 :=
              if sgn0_m_eq_1 (lift_to_both0 y_2844) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                [x1_2842_loc ; x_2843_loc ; y_2844_loc])) (L2 := CEfset (
                [x1_2842_loc ; x_2843_loc ; y_2844_loc])) (I1 := [interface]) (I2 := [interface
              #val #[ SGN0_M_EQ_1 ] : sgn0_m_eq_1_inp → sgn0_m_eq_1_out ;
              #val #[ SQRT ] : sqrt_inp → sqrt_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm y_2844 loc( y_2844_loc ) :=
                  (lift_to_both0 zero_2851) -% (lift_to_both0 y_2844) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 y_2844)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 y_2844)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 x_2843,
                lift_to_both0 y_2844
              ))
            ) in
        letb s_2856 : ed25519_field_element_t := lift_to_both0 x_2843 in
        letb t_2857 : ed25519_field_element_t := lift_to_both0 y_2844 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 s_2856,
            lift_to_both0 t_2857,
            lift_to_both0 one_2850,
            (lift_to_both0 s_2856) *% (lift_to_both0 t_2857)
          ))
        ) : both (CEfset ([x1_2842_loc ; x_2843_loc ; y_2844_loc])) [interface
      #val #[ ED_IS_SQUARE ] : ed_is_square_inp → ed_is_square_out ;
      #val #[ SGN0_M_EQ_1 ] : sgn0_m_eq_1_inp → sgn0_m_eq_1_out ;
      #val #[ SQRT ] : sqrt_inp → sqrt_out ] (ed_point_t)))in
  both_package' _ _ (MAP_TO_CURVE_ELLIGATOR2,(
      map_to_curve_elligator2_inp,map_to_curve_elligator2_out)) temp_package_both.
Fail Next Obligation.


Notation "'map_to_curve_elligator2_straight_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_straight_inp'" :=(
  ed25519_field_element_t : ChoiceEquality) (at level 2).
Notation "'map_to_curve_elligator2_straight_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_straight_out'" :=(
  ed_point_t : ChoiceEquality) (at level 2).
Definition MAP_TO_CURVE_ELLIGATOR2_STRAIGHT : nat :=
  2885.
Program Definition map_to_curve_elligator2_straight
  : both_package (fset.fset0) [interface
  #val #[ CMOV ] : cmov_inp → cmov_out ;
  #val #[ ED_IS_SQUARE ] : ed_is_square_inp → ed_is_square_out ;
  #val #[ SGN0_M_EQ_1 ] : sgn0_m_eq_1_inp → sgn0_m_eq_1_out ;
  #val #[ SQRT ] : sqrt_inp → sqrt_out ; #val #[ XOR ] : xor_inp → xor_out
  ] [(MAP_TO_CURVE_ELLIGATOR2_STRAIGHT,(
      map_to_curve_elligator2_straight_inp,map_to_curve_elligator2_straight_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(u_2863) := temp_inp : ed25519_field_element_t in
    
    let cmov := fun x_0 x_1 x_2 => package_both cmov (x_0,x_1,x_2) in
    let ed_is_square := fun x_0 => package_both ed_is_square (x_0) in
    let sgn0_m_eq_1 := fun x_0 => package_both sgn0_m_eq_1 (x_0) in
    let sqrt := fun x_0 => package_both sqrt (x_0) in
    let xor := fun x_0 x_1 => package_both xor (x_0,x_1) in
    ((letb j_2859 : ed25519_field_element_t :=
          nat_mod_from_literal (_) (lift_to_both0 j_v) in
        letb z_2860 : ed25519_field_element_t :=
          nat_mod_from_literal (_) (lift_to_both0 z_v) in
        letb one_2861 : ed25519_field_element_t := nat_mod_one  in
        letb zero_2862 : ed25519_field_element_t := nat_mod_zero  in
        letb tv1_2864 : ed25519_field_element_t :=
          (lift_to_both0 u_2863) *% (lift_to_both0 u_2863) in
        letb tv1_2865 : ed25519_field_element_t :=
          (lift_to_both0 z_2860) *% (lift_to_both0 tv1_2864) in
        letb e1_2866 : bool_ChoiceEquality :=
          (lift_to_both0 tv1_2865) =.? ((lift_to_both0 zero_2862) -% (
              lift_to_both0 one_2861)) in
        letb tv1_2867 : ed25519_field_element_t :=
          cmov (lift_to_both0 tv1_2865) (lift_to_both0 zero_2862) (
            lift_to_both0 e1_2866) in
        letb x1_2868 : ed25519_field_element_t :=
          (lift_to_both0 tv1_2867) +% (lift_to_both0 one_2861) in
        letb x1_2869 : ed25519_field_element_t :=
          nat_mod_inv (lift_to_both0 x1_2868) in
        letb x1_2870 : ed25519_field_element_t :=
          ((lift_to_both0 zero_2862) -% (lift_to_both0 j_2859)) *% (
            lift_to_both0 x1_2869) in
        letb gx1_2871 : ed25519_field_element_t :=
          (lift_to_both0 x1_2870) +% (lift_to_both0 j_2859) in
        letb gx1_2872 : ed25519_field_element_t :=
          (lift_to_both0 gx1_2871) *% (lift_to_both0 x1_2870) in
        letb gx1_2873 : ed25519_field_element_t :=
          (lift_to_both0 gx1_2872) +% (lift_to_both0 one_2861) in
        letb gx1_2874 : ed25519_field_element_t :=
          (lift_to_both0 gx1_2873) *% (lift_to_both0 x1_2870) in
        letb x2_2875 : ed25519_field_element_t :=
          ((lift_to_both0 zero_2862) -% (lift_to_both0 x1_2870)) -% (
            lift_to_both0 j_2859) in
        letb gx2_2876 : ed25519_field_element_t :=
          (lift_to_both0 tv1_2867) *% (lift_to_both0 gx1_2874) in
        letb e2_2877 : bool_ChoiceEquality :=
          ed_is_square (lift_to_both0 gx1_2874) in
        letb x_2878 : ed25519_field_element_t :=
          cmov (lift_to_both0 x2_2875) (lift_to_both0 x1_2870) (
            lift_to_both0 e2_2877) in
        letb y2_2879 : ed25519_field_element_t :=
          cmov (lift_to_both0 gx2_2876) (lift_to_both0 gx1_2874) (
            lift_to_both0 e2_2877) in
        letb y_2880 : ed25519_field_element_t :=
          option_unwrap (sqrt (lift_to_both0 y2_2879)) in
        letb e3_2881 : bool_ChoiceEquality :=
          sgn0_m_eq_1 (lift_to_both0 y_2880) in
        letb y_2882 : ed25519_field_element_t :=
          cmov (lift_to_both0 y_2880) ((lift_to_both0 zero_2862) -% (
              lift_to_both0 y_2880)) (xor (lift_to_both0 e2_2877) (
              lift_to_both0 e3_2881)) in
        letb s_2883 : ed25519_field_element_t := lift_to_both0 x_2878 in
        letb t_2884 : ed25519_field_element_t := lift_to_both0 y_2882 in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 s_2883,
            lift_to_both0 t_2884,
            lift_to_both0 one_2861,
            (lift_to_both0 s_2883) *% (lift_to_both0 t_2884)
          ))
        ) : both (fset.fset0) [interface
      #val #[ CMOV ] : cmov_inp → cmov_out ;
      #val #[ ED_IS_SQUARE ] : ed_is_square_inp → ed_is_square_out ;
      #val #[ SGN0_M_EQ_1 ] : sgn0_m_eq_1_inp → sgn0_m_eq_1_out ;
      #val #[ SQRT ] : sqrt_inp → sqrt_out ;
      #val #[ XOR ] : xor_inp → xor_out ] (ed_point_t)))in
  both_package' _ _ (MAP_TO_CURVE_ELLIGATOR2_STRAIGHT,(
      map_to_curve_elligator2_straight_inp,map_to_curve_elligator2_straight_out)) temp_package_both.
Fail Next Obligation.


Notation "'map_to_curve_elligator2_curve25519_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_curve25519_inp'" :=(
  ed25519_field_element_t : ChoiceEquality) (at level 2).
Notation "'map_to_curve_elligator2_curve25519_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_curve25519_out'" :=(
  ed_point_t : ChoiceEquality) (at level 2).
Definition MAP_TO_CURVE_ELLIGATOR2_CURVE25519 : nat :=
  2933.
Program Definition map_to_curve_elligator2_curve25519
  : both_package (fset.fset0) [interface
  #val #[ CMOV ] : cmov_inp → cmov_out ;
  #val #[ SGN0_M_EQ_1 ] : sgn0_m_eq_1_inp → sgn0_m_eq_1_out ;
  #val #[ SQRT ] : sqrt_inp → sqrt_out ; #val #[ XOR ] : xor_inp → xor_out
  ] [(MAP_TO_CURVE_ELLIGATOR2_CURVE25519,(
      map_to_curve_elligator2_curve25519_inp,map_to_curve_elligator2_curve25519_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(u_2894) := temp_inp : ed25519_field_element_t in
    
    let cmov := fun x_0 x_1 x_2 => package_both cmov (x_0,x_1,x_2) in
    let sgn0_m_eq_1 := fun x_0 => package_both sgn0_m_eq_1 (x_0) in
    let sqrt := fun x_0 => package_both sqrt (x_0) in
    let xor := fun x_0 x_1 => package_both xor (x_0,x_1) in
    ((letb j_2886 : ed25519_field_element_t :=
          nat_mod_from_literal (_) (lift_to_both0 j_v) in
        letb zero_2887 : ed25519_field_element_t := nat_mod_zero  in
        letb one_2888 : ed25519_field_element_t := nat_mod_one  in
        letb two_2889 : ed25519_field_element_t := nat_mod_two  in
        letb c1_2890 : ed25519_field_element_t :=
          nat_mod_from_byte_seq_be (array_to_be_bytes (
              lift_to_both0 p_3_8_v)) in
        letb c2_2891 : ed25519_field_element_t :=
          nat_mod_pow_self (lift_to_both0 two_2889) (lift_to_both0 c1_2890) in
        letb c3_2892 : ed25519_field_element_t :=
          option_unwrap (sqrt ((lift_to_both0 zero_2887) -% (
                lift_to_both0 one_2888))) in
        letb c4_2893 : ed25519_field_element_t :=
          nat_mod_from_byte_seq_be (array_to_be_bytes (
              lift_to_both0 p_5_8_v)) in
        letb tv1_2895 : ed25519_field_element_t :=
          (lift_to_both0 u_2894) *% (lift_to_both0 u_2894) in
        letb tv1_2896 : ed25519_field_element_t :=
          (lift_to_both0 two_2889) *% (lift_to_both0 tv1_2895) in
        letb xd_2897 : ed25519_field_element_t :=
          (lift_to_both0 tv1_2896) +% (lift_to_both0 one_2888) in
        letb x1n_2898 : ed25519_field_element_t :=
          (lift_to_both0 zero_2887) -% (lift_to_both0 j_2886) in
        letb tv2_2899 : ed25519_field_element_t :=
          (lift_to_both0 xd_2897) *% (lift_to_both0 xd_2897) in
        letb gxd_2900 : ed25519_field_element_t :=
          (lift_to_both0 tv2_2899) *% (lift_to_both0 xd_2897) in
        letb gx1_2901 : ed25519_field_element_t :=
          (lift_to_both0 j_2886) *% (lift_to_both0 tv1_2896) in
        letb gx1_2902 : ed25519_field_element_t :=
          (lift_to_both0 gx1_2901) *% (lift_to_both0 x1n_2898) in
        letb gx1_2903 : ed25519_field_element_t :=
          (lift_to_both0 gx1_2902) +% (lift_to_both0 tv2_2899) in
        letb gx1_2904 : ed25519_field_element_t :=
          (lift_to_both0 gx1_2903) *% (lift_to_both0 x1n_2898) in
        letb tv3_2905 : ed25519_field_element_t :=
          (lift_to_both0 gxd_2900) *% (lift_to_both0 gxd_2900) in
        letb tv2_2906 : ed25519_field_element_t :=
          (lift_to_both0 tv3_2905) *% (lift_to_both0 tv3_2905) in
        letb tv3_2907 : ed25519_field_element_t :=
          (lift_to_both0 tv3_2905) *% (lift_to_both0 gxd_2900) in
        letb tv3_2908 : ed25519_field_element_t :=
          (lift_to_both0 tv3_2907) *% (lift_to_both0 gx1_2904) in
        letb tv2_2909 : ed25519_field_element_t :=
          (lift_to_both0 tv2_2906) *% (lift_to_both0 tv3_2908) in
        letb y11_2910 : ed25519_field_element_t :=
          nat_mod_pow_self (lift_to_both0 tv2_2909) (lift_to_both0 c4_2893) in
        letb y11_2911 : ed25519_field_element_t :=
          (lift_to_both0 y11_2910) *% (lift_to_both0 tv3_2908) in
        letb y12_2912 : ed25519_field_element_t :=
          (lift_to_both0 y11_2911) *% (lift_to_both0 c3_2892) in
        letb tv2_2913 : ed25519_field_element_t :=
          (lift_to_both0 y11_2911) *% (lift_to_both0 y11_2911) in
        letb tv2_2914 : ed25519_field_element_t :=
          (lift_to_both0 tv2_2913) *% (lift_to_both0 gxd_2900) in
        letb e1_2915 : bool_ChoiceEquality :=
          (lift_to_both0 tv2_2914) =.? (lift_to_both0 gx1_2904) in
        letb y1_2916 : ed25519_field_element_t :=
          cmov (lift_to_both0 y12_2912) (lift_to_both0 y11_2911) (
            lift_to_both0 e1_2915) in
        letb x2n_2917 : ed25519_field_element_t :=
          (lift_to_both0 x1n_2898) *% (lift_to_both0 tv1_2896) in
        letb y21_2918 : ed25519_field_element_t :=
          (lift_to_both0 y11_2911) *% (lift_to_both0 u_2894) in
        letb y21_2919 : ed25519_field_element_t :=
          (lift_to_both0 y21_2918) *% (lift_to_both0 c2_2891) in
        letb y22_2920 : ed25519_field_element_t :=
          (lift_to_both0 y21_2919) *% (lift_to_both0 c3_2892) in
        letb gx2_2921 : ed25519_field_element_t :=
          (lift_to_both0 gx1_2904) *% (lift_to_both0 tv1_2896) in
        letb tv2_2922 : ed25519_field_element_t :=
          (lift_to_both0 y21_2919) *% (lift_to_both0 y21_2919) in
        letb tv2_2923 : ed25519_field_element_t :=
          (lift_to_both0 tv2_2922) *% (lift_to_both0 gxd_2900) in
        letb e2_2924 : bool_ChoiceEquality :=
          (lift_to_both0 tv2_2923) =.? (lift_to_both0 gx2_2921) in
        letb y2_2925 : ed25519_field_element_t :=
          cmov (lift_to_both0 y22_2920) (lift_to_both0 y21_2919) (
            lift_to_both0 e2_2924) in
        letb tv2_2926 : ed25519_field_element_t :=
          (lift_to_both0 y1_2916) *% (lift_to_both0 y1_2916) in
        letb tv2_2927 : ed25519_field_element_t :=
          (lift_to_both0 tv2_2926) *% (lift_to_both0 gxd_2900) in
        letb e3_2928 : bool_ChoiceEquality :=
          (lift_to_both0 tv2_2927) =.? (lift_to_both0 gx1_2904) in
        letb xn_2929 : ed25519_field_element_t :=
          cmov (lift_to_both0 x2n_2917) (lift_to_both0 x1n_2898) (
            lift_to_both0 e3_2928) in
        letb y_2930 : ed25519_field_element_t :=
          cmov (lift_to_both0 y2_2925) (lift_to_both0 y1_2916) (
            lift_to_both0 e3_2928) in
        letb e4_2931 : bool_ChoiceEquality :=
          sgn0_m_eq_1 (lift_to_both0 y_2930) in
        letb y_2932 : ed25519_field_element_t :=
          cmov (lift_to_both0 y_2930) ((lift_to_both0 zero_2887) -% (
              lift_to_both0 y_2930)) (xor (lift_to_both0 e3_2928) (
              lift_to_both0 e4_2931)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 xn_2929,
            lift_to_both0 xd_2897,
            lift_to_both0 y_2932,
            lift_to_both0 one_2888
          ))
        ) : both (fset.fset0) [interface
      #val #[ CMOV ] : cmov_inp → cmov_out ;
      #val #[ SGN0_M_EQ_1 ] : sgn0_m_eq_1_inp → sgn0_m_eq_1_out ;
      #val #[ SQRT ] : sqrt_inp → sqrt_out ;
      #val #[ XOR ] : xor_inp → xor_out ] (ed_point_t)))in
  both_package' _ _ (MAP_TO_CURVE_ELLIGATOR2_CURVE25519,(
      map_to_curve_elligator2_curve25519_inp,map_to_curve_elligator2_curve25519_out)) temp_package_both.
Fail Next Obligation.


Notation "'map_to_curve_elligator2_edwards25519_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_edwards25519_inp'" :=(
  ed25519_field_element_t : ChoiceEquality) (at level 2).
Notation "'map_to_curve_elligator2_edwards25519_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_edwards25519_out'" :=(
  ed_point_t : ChoiceEquality) (at level 2).
Definition MAP_TO_CURVE_ELLIGATOR2_EDWARDS25519 : nat :=
  2957.
Program Definition map_to_curve_elligator2_edwards25519
  : both_package (fset.fset0) [interface
  #val #[ CMOV ] : cmov_inp → cmov_out ;
  #val #[ MAP_TO_CURVE_ELLIGATOR2_CURVE25519 ] : map_to_curve_elligator2_curve25519_inp → map_to_curve_elligator2_curve25519_out ;
  #val #[ SQRT ] : sqrt_inp → sqrt_out ] [(
    MAP_TO_CURVE_ELLIGATOR2_EDWARDS25519,(
      map_to_curve_elligator2_edwards25519_inp,map_to_curve_elligator2_edwards25519_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(u_2939) := temp_inp : ed25519_field_element_t in
    
    let cmov := fun x_0 x_1 x_2 => package_both cmov (x_0,x_1,x_2) in
    let map_to_curve_elligator2_curve25519 := fun x_0 => package_both map_to_curve_elligator2_curve25519 (
      x_0) in
    let sqrt := fun x_0 => package_both sqrt (x_0) in
    ((letb j_2934 : ed25519_field_element_t :=
          nat_mod_from_literal (_) (lift_to_both0 j_v) in
        letb zero_2935 : ed25519_field_element_t := nat_mod_zero  in
        letb one_2936 : ed25519_field_element_t := nat_mod_one  in
        letb two_2937 : ed25519_field_element_t := nat_mod_two  in
        letb c1_2938 : ed25519_field_element_t :=
          option_unwrap (sqrt ((lift_to_both0 zero_2935) -% ((
                  lift_to_both0 j_2934) +% (lift_to_both0 two_2937)))) in
        letb '(xmn_2940, xmd_2941, ymn_2942, ymd_2943) : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          map_to_curve_elligator2_curve25519 (lift_to_both0 u_2939) in
        letb xn_2944 : ed25519_field_element_t :=
          (lift_to_both0 xmn_2940) *% (lift_to_both0 ymd_2943) in
        letb xn_2945 : ed25519_field_element_t :=
          (lift_to_both0 xn_2944) *% (lift_to_both0 c1_2938) in
        letb xd_2946 : ed25519_field_element_t :=
          (lift_to_both0 xmd_2941) *% (lift_to_both0 ymn_2942) in
        letb yn_2947 : ed25519_field_element_t :=
          (lift_to_both0 xmn_2940) -% (lift_to_both0 xmd_2941) in
        letb yd_2948 : ed25519_field_element_t :=
          (lift_to_both0 xmn_2940) +% (lift_to_both0 xmd_2941) in
        letb tv1_2949 : ed25519_field_element_t :=
          (lift_to_both0 xd_2946) *% (lift_to_both0 yd_2948) in
        letb e_2950 : bool_ChoiceEquality :=
          (lift_to_both0 tv1_2949) =.? (lift_to_both0 zero_2935) in
        letb xn_2951 : ed25519_field_element_t :=
          cmov (lift_to_both0 xn_2945) (lift_to_both0 zero_2935) (
            lift_to_both0 e_2950) in
        letb xd_2952 : ed25519_field_element_t :=
          cmov (lift_to_both0 xd_2946) (lift_to_both0 one_2936) (
            lift_to_both0 e_2950) in
        letb yn_2953 : ed25519_field_element_t :=
          cmov (lift_to_both0 yn_2947) (lift_to_both0 one_2936) (
            lift_to_both0 e_2950) in
        letb yd_2954 : ed25519_field_element_t :=
          cmov (lift_to_both0 yd_2948) (lift_to_both0 one_2936) (
            lift_to_both0 e_2950) in
        letb x_2955 : ed25519_field_element_t :=
          (lift_to_both0 xn_2951) *% (nat_mod_inv (lift_to_both0 xd_2952)) in
        letb y_2956 : ed25519_field_element_t :=
          (lift_to_both0 yn_2953) *% (nat_mod_inv (lift_to_both0 yd_2954)) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 x_2955,
            lift_to_both0 y_2956,
            lift_to_both0 one_2936,
            (lift_to_both0 x_2955) *% (lift_to_both0 y_2956)
          ))
        ) : both (fset.fset0) [interface
      #val #[ CMOV ] : cmov_inp → cmov_out ;
      #val #[ MAP_TO_CURVE_ELLIGATOR2_CURVE25519 ] : map_to_curve_elligator2_curve25519_inp → map_to_curve_elligator2_curve25519_out ;
      #val #[ SQRT ] : sqrt_inp → sqrt_out ] (ed_point_t)))in
  both_package' _ _ (MAP_TO_CURVE_ELLIGATOR2_EDWARDS25519,(
      map_to_curve_elligator2_edwards25519_inp,map_to_curve_elligator2_edwards25519_out)) temp_package_both.
Fail Next Obligation.


Notation "'map_to_curve_elligator2_edwards_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_edwards_inp'" :=(
  ed25519_field_element_t : ChoiceEquality) (at level 2).
Notation "'map_to_curve_elligator2_edwards_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'map_to_curve_elligator2_edwards_out'" :=(
  ed_point_t : ChoiceEquality) (at level 2).
Definition MAP_TO_CURVE_ELLIGATOR2_EDWARDS : nat :=
  2960.
Program Definition map_to_curve_elligator2_edwards
  : both_package (CEfset ([])) [interface
  #val #[ CURVE25519_TO_EDWARDS25519 ] : curve25519_to_edwards25519_inp → curve25519_to_edwards25519_out ;
  #val #[ MAP_TO_CURVE_ELLIGATOR2 ] : map_to_curve_elligator2_inp → map_to_curve_elligator2_out
  ] [(MAP_TO_CURVE_ELLIGATOR2_EDWARDS,(
      map_to_curve_elligator2_edwards_inp,map_to_curve_elligator2_edwards_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(u_2958) := temp_inp : ed25519_field_element_t in
    
    let curve25519_to_edwards25519 := fun x_0 => package_both curve25519_to_edwards25519 (
      x_0) in
    let map_to_curve_elligator2 := fun x_0 => package_both map_to_curve_elligator2 (
      x_0) in
    ((letb st_2959 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          map_to_curve_elligator2 (lift_to_both0 u_2958) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          curve25519_to_edwards25519 (lift_to_both0 st_2959))
        ) : both (CEfset ([])) [interface
      #val #[ CURVE25519_TO_EDWARDS25519 ] : curve25519_to_edwards25519_inp → curve25519_to_edwards25519_out ;
      #val #[ MAP_TO_CURVE_ELLIGATOR2 ] : map_to_curve_elligator2_inp → map_to_curve_elligator2_out
      ] (ed_point_t)))in
  both_package' _ _ (MAP_TO_CURVE_ELLIGATOR2_EDWARDS,(
      map_to_curve_elligator2_edwards_inp,map_to_curve_elligator2_edwards_out)) temp_package_both.
Fail Next Obligation.


Notation "'ed_encode_to_curve_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'ed_encode_to_curve_inp'" :=(
  byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'ed_encode_to_curve_out'" :=(
  ed_point_result_t : choice_type) (in custom pack_type at level 2).
Notation "'ed_encode_to_curve_out'" :=(
  ed_point_result_t : ChoiceEquality) (at level 2).
Definition ED_ENCODE_TO_CURVE : nat :=
  2965.
Program Definition ed_encode_to_curve
  : both_package (CEfset ([])) [interface
  #val #[ ED_CLEAR_COFACTOR ] : ed_clear_cofactor_inp → ed_clear_cofactor_out ;
  #val #[ ED_HASH_TO_FIELD ] : ed_hash_to_field_inp → ed_hash_to_field_out ;
  #val #[ MAP_TO_CURVE_ELLIGATOR2_EDWARDS ] : map_to_curve_elligator2_edwards_inp → map_to_curve_elligator2_edwards_out
  ] [(ED_ENCODE_TO_CURVE,(ed_encode_to_curve_inp,ed_encode_to_curve_out))] :=
  let temp_package_both := (fun temp_inp => 
    let '(msg_2961 , dst_2962) := temp_inp : byte_seq '× byte_seq in
    
    let ed_clear_cofactor := fun x_0 => package_both ed_clear_cofactor (x_0) in
    let ed_hash_to_field := fun x_0 x_1 x_2 => package_both ed_hash_to_field (
      x_0,x_1,x_2) in
    let map_to_curve_elligator2_edwards := fun x_0 => package_both map_to_curve_elligator2_edwards (
      x_0) in
    ((letbnd(_) u_2963 : seq ed25519_field_element_t :=
          ed_hash_to_field (lift_to_both0 msg_2961) (lift_to_both0 dst_2962) (
            lift_to_both0 (usize 1)) in
        letb q_2964 : (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) :=
          map_to_curve_elligator2_edwards (seq_index (u_2963) (lift_to_both0 (
                usize 0))) in
        lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Ok ed_point_t error_t (ed_clear_cofactor (lift_to_both0 q_2964)))
        ) : both (CEfset ([])) [interface
      #val #[ ED_CLEAR_COFACTOR ] : ed_clear_cofactor_inp → ed_clear_cofactor_out ;
      #val #[ ED_HASH_TO_FIELD ] : ed_hash_to_field_inp → ed_hash_to_field_out ;
      #val #[ MAP_TO_CURVE_ELLIGATOR2_EDWARDS ] : map_to_curve_elligator2_edwards_inp → map_to_curve_elligator2_edwards_out
      ] (ed_point_result_t)))in
  both_package' _ _ (ED_ENCODE_TO_CURVE,(
      ed_encode_to_curve_inp,ed_encode_to_curve_out)) temp_package_both.
Fail Next Obligation.

