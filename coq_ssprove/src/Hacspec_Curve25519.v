(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From CoqWord Require Import ssrZ word.
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

Obligation Tactic := try timeout 40 solve_ssprove_obligations.
Require Import Hacspec_Lib.

Definition field_canvas_t  :=
  (nseq (int8) (32)).
Definition x25519_field_element_t  :=
  (nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed).

Definition scalar_canvas_t  :=
  (nseq (int8) (32)).
Definition scalar_t  :=
  (nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000).

Notation "'point_t'" := ((x25519_field_element_t '× x25519_field_element_t
)) : hacspec_scope.

Definition x25519_serialized_point_t  :=
  ( nseq (uint8) (usize 32)).

Definition x25519_serialized_scalar_t  :=
  ( nseq (uint8) (usize 32)).

Definition k_2_loc : ChoiceEqualityLocation :=
  ((x25519_serialized_scalar_t ; 20%nat)).
Notation "'mask_scalar_inp'" := (
  x25519_serialized_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'mask_scalar_out'" := (
  x25519_serialized_scalar_t : choice_type) (in custom pack_type at level 2).
Definition MASK_SCALAR : nat :=
  (21).
Program Definition mask_scalar
   : package (CEfset ([k_2_loc])) [interface  ] [interface
  #val #[ MASK_SCALAR ] : mask_scalar_inp → mask_scalar_out ] :=
  (
    [package #def #[ MASK_SCALAR ] (temp_inp : mask_scalar_inp) : mask_scalar_out { 
    let '(s_0) := temp_inp : x25519_serialized_scalar_t in
    ({ code  '(k_2 : x25519_serialized_scalar_t) ←
          (ret (s_0)) ;;
        #put k_2_loc := k_2 ;;
       '(k_2 : x25519_serialized_scalar_t) ←
        ( temp_3 ←
            (array_index (k_2) (usize 0)) ;;
           '(temp_5 : int8) ←
            (secret (@repr U8 248)) ;;
           temp_7 ←
            ((temp_3) .& (temp_5)) ;;
          ret (array_upd k_2 (usize 0) (temp_7))) ;;
      
       '(k_2 : x25519_serialized_scalar_t) ←
        ( temp_9 ←
            (array_index (k_2) (usize 31)) ;;
           '(temp_11 : int8) ←
            (secret (@repr U8 127)) ;;
           temp_13 ←
            ((temp_9) .& (temp_11)) ;;
          ret (array_upd k_2 (usize 31) (temp_13))) ;;
      
       '(k_2 : x25519_serialized_scalar_t) ←
        ( temp_15 ←
            (array_index (k_2) (usize 31)) ;;
           '(temp_17 : int8) ←
            (secret (@repr U8 64)) ;;
           temp_19 ←
            ((temp_15) .| (temp_17)) ;;
          ret (array_upd k_2 (usize 31) (temp_19))) ;;
      
      @ret (x25519_serialized_scalar_t) (k_2) } : code (CEfset (
          [k_2_loc])) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_mask_scalar : package _ _ _ :=
  (mask_scalar).
Fail Next Obligation.


Notation "'decode_scalar_inp'" := (
  x25519_serialized_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'decode_scalar_out'" := (
  scalar_t : choice_type) (in custom pack_type at level 2).
Definition DECODE_SCALAR : nat :=
  (30).
Program Definition decode_scalar
   : package (CEfset ([])) [interface
  #val #[ MASK_SCALAR ] : mask_scalar_inp → mask_scalar_out ] [interface
  #val #[ DECODE_SCALAR ] : decode_scalar_inp → decode_scalar_out ] :=
  (
    [package #def #[ DECODE_SCALAR ] (temp_inp : decode_scalar_inp) : decode_scalar_out { 
    let '(s_22) := temp_inp : x25519_serialized_scalar_t in
    #import {sig #[ MASK_SCALAR ] : mask_scalar_inp → mask_scalar_out } as mask_scalar ;;
    let mask_scalar := fun x_0 => mask_scalar (x_0) in
    ({ code  '(k_25 : x25519_serialized_scalar_t) ←
        ( '(temp_24 : x25519_serialized_scalar_t) ←
            (mask_scalar (s_22)) ;;
          ret (temp_24)) ;;
       '(temp_27 : seq uint8) ←
        (array_to_seq (k_25)) ;;
       '(temp_29 : scalar_t) ←
        (nat_mod_from_byte_seq_le (temp_27)) ;;
      @ret (scalar_t) (temp_29) } : code (CEfset ([])) [interface
      #val #[ MASK_SCALAR ] : mask_scalar_inp → mask_scalar_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_decode_scalar : package _ _ _ :=
  (seq_link decode_scalar link_rest(package_mask_scalar)).
Fail Next Obligation.

Definition u_33_loc : ChoiceEqualityLocation :=
  ((x25519_serialized_point_t ; 45%nat)).
Notation "'decode_point_inp'" := (
  x25519_serialized_point_t : choice_type) (in custom pack_type at level 2).
Notation "'decode_point_out'" := (
  point_t : choice_type) (in custom pack_type at level 2).
Definition DECODE_POINT : nat :=
  (46).
Program Definition decode_point
   : package (CEfset ([u_33_loc])) [interface  ] [interface
  #val #[ DECODE_POINT ] : decode_point_inp → decode_point_out ] :=
  (
    [package #def #[ DECODE_POINT ] (temp_inp : decode_point_inp) : decode_point_out { 
    let '(u_31) := temp_inp : x25519_serialized_point_t in
    ({ code  '(u_33 : x25519_serialized_point_t) ←
          (ret (u_31)) ;;
        #put u_33_loc := u_33 ;;
       '(u_33 : x25519_serialized_point_t) ←
        ( temp_34 ←
            (array_index (u_33) (usize 31)) ;;
           '(temp_36 : int8) ←
            (secret (@repr U8 127)) ;;
           temp_38 ←
            ((temp_34) .& (temp_36)) ;;
          ret (array_upd u_33 (usize 31) (temp_38))) ;;
      
       '(temp_40 : seq uint8) ←
        (array_to_seq (u_33)) ;;
       '(temp_42 : x25519_field_element_t) ←
        (nat_mod_from_byte_seq_le (temp_40)) ;;
       '(temp_44 : x25519_field_element_t) ←
        (nat_mod_from_literal (
            0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
            @repr U128 1)) ;;
      @ret ((x25519_field_element_t '× x25519_field_element_t)) (prod_ce(
          temp_42,
          temp_44
        )) } : code (CEfset ([u_33_loc])) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_decode_point : package _ _ _ :=
  (decode_point).
Fail Next Obligation.


Notation "'encode_point_inp'" := (
  point_t : choice_type) (in custom pack_type at level 2).
Notation "'encode_point_out'" := (
  x25519_serialized_point_t : choice_type) (in custom pack_type at level 2).
Definition ENCODE_POINT : nat :=
  (63).
Program Definition encode_point
   : package (fset.fset0) [interface  ] [interface
  #val #[ ENCODE_POINT ] : encode_point_inp → encode_point_out ] :=
  (
    [package #def #[ ENCODE_POINT ] (temp_inp : encode_point_inp) : encode_point_out { 
    let '(p_47) := temp_inp : point_t in
    ({ code  temp_62 ←
        (ret (p_47)) ;;
      let '(x_48, y_49) :=
        (temp_62) : (x25519_field_element_t '× x25519_field_element_t) in
       '(b_56 : x25519_field_element_t) ←
        ( temp_51 ←
            (nat_mod_inv (y_49)) ;;
           '(temp_53 : x25519_field_element_t) ←
            ((x_48) *% (temp_51)) ;;
          ret (temp_53)) ;;
       '(temp_55 : x25519_serialized_point_t) ←
        (array_new_ (default : uint8) (32)) ;;
       temp_58 ←
        (nat_mod_to_byte_seq_le (b_56)) ;;
       '(temp_60 : x25519_serialized_point_t) ←
        (array_update_start (temp_55) (temp_58)) ;;
      @ret (x25519_serialized_point_t) (temp_60) } : code (
        fset.fset0) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_encode_point : package _ _ _ :=
  (encode_point).
Fail Next Obligation.


Notation "'point_add_and_double_inp'" := (point_t '× (point_t '× point_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'point_add_and_double_out'" := ((point_t '× point_t
  ) : choice_type) (in custom pack_type at level 2).
Definition POINT_ADD_AND_DOUBLE : nat :=
  (134).
Program Definition point_add_and_double
   : package (fset.fset0) [interface  ] [interface
  #val #[ POINT_ADD_AND_DOUBLE ] : point_add_and_double_inp → point_add_and_double_out
  ] := (
    [package #def #[ POINT_ADD_AND_DOUBLE ] (temp_inp : point_add_and_double_inp) : point_add_and_double_out { 
    let '(q_65 , np_64) := temp_inp : point_t '× (point_t '× point_t) in
    ({ code  temp_133 ←
        (ret (np_64)) ;;
      let '(nq_66, nqp1_67) :=
        (temp_133) : (point_t '× point_t) in
       temp_130 ←
        (ret (q_65)) ;;
      let '(x_1_102, z_1_131) :=
        (temp_130) : (x25519_field_element_t '× x25519_field_element_t) in
       temp_128 ←
        (ret (nq_66)) ;;
      let '(x_2_68, z_2_69) :=
        (temp_128) : (x25519_field_element_t '× x25519_field_element_t) in
       temp_126 ←
        (ret (nqp1_67)) ;;
      let '(x_3_84, z_3_85) :=
        (temp_126) : (x25519_field_element_t '× x25519_field_element_t) in
       '(a_72 : x25519_field_element_t) ←
        ( '(temp_71 : x25519_field_element_t) ←
            ((x_2_68) +% (z_2_69)) ;;
          ret (temp_71)) ;;
       '(aa_80 : x25519_field_element_t) ←
        ( '(temp_74 : x25519_field_element_t) ←
            (nat_mod_pow (a_72) (@repr U128 2)) ;;
          ret (temp_74)) ;;
       '(b_77 : x25519_field_element_t) ←
        ( '(temp_76 : x25519_field_element_t) ←
            ((x_2_68) -% (z_2_69)) ;;
          ret (temp_76)) ;;
       '(bb_81 : x25519_field_element_t) ←
        ( '(temp_79 : x25519_field_element_t) ←
            ((b_77) *% (b_77)) ;;
          ret (temp_79)) ;;
       '(e_113 : x25519_field_element_t) ←
        ( '(temp_83 : x25519_field_element_t) ←
            ((aa_80) -% (bb_81)) ;;
          ret (temp_83)) ;;
       '(c_93 : x25519_field_element_t) ←
        ( '(temp_87 : x25519_field_element_t) ←
            ((x_3_84) +% (z_3_85)) ;;
          ret (temp_87)) ;;
       '(d_90 : x25519_field_element_t) ←
        ( '(temp_89 : x25519_field_element_t) ←
            ((x_3_84) -% (z_3_85)) ;;
          ret (temp_89)) ;;
       '(da_96 : x25519_field_element_t) ←
        ( '(temp_92 : x25519_field_element_t) ←
            ((d_90) *% (a_72)) ;;
          ret (temp_92)) ;;
       '(cb_97 : x25519_field_element_t) ←
        ( '(temp_95 : x25519_field_element_t) ←
            ((c_93) *% (b_77)) ;;
          ret (temp_95)) ;;
       '(x_3_123 : x25519_field_element_t) ←
        ( '(temp_99 : x25519_field_element_t) ←
            ((da_96) +% (cb_97)) ;;
           '(temp_101 : x25519_field_element_t) ←
            (nat_mod_pow (temp_99) (@repr U128 2)) ;;
          ret (temp_101)) ;;
       '(z_3_124 : x25519_field_element_t) ←
        ( '(temp_104 : x25519_field_element_t) ←
            ((da_96) -% (cb_97)) ;;
           '(temp_106 : x25519_field_element_t) ←
            (nat_mod_pow (temp_104) (@repr U128 2)) ;;
           '(temp_108 : x25519_field_element_t) ←
            ((x_1_102) *% (temp_106)) ;;
          ret (temp_108)) ;;
       '(x_2_121 : x25519_field_element_t) ←
        ( '(temp_110 : x25519_field_element_t) ←
            ((aa_80) *% (bb_81)) ;;
          ret (temp_110)) ;;
       '(e121665_114 : x25519_field_element_t) ←
        ( '(temp_112 : x25519_field_element_t) ←
            (nat_mod_from_literal (
                0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
                @repr U128 121665)) ;;
          ret (temp_112)) ;;
       '(z_2_122 : x25519_field_element_t) ←
        ( '(temp_116 : x25519_field_element_t) ←
            ((e121665_114) *% (e_113)) ;;
           '(temp_118 : x25519_field_element_t) ←
            ((aa_80) +% (temp_116)) ;;
           '(temp_120 : x25519_field_element_t) ←
            ((e_113) *% (temp_118)) ;;
          ret (temp_120)) ;;
      @ret ((
          (x25519_field_element_t '× x25519_field_element_t) '×
          (x25519_field_element_t '× x25519_field_element_t)
        )) (prod_ce(prod_ce(x_2_121, z_2_122), prod_ce(x_3_123, z_3_124)
        )) } : code (fset.fset0) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_point_add_and_double : package _ _ _ :=
  (point_add_and_double).
Fail Next Obligation.


Notation "'swap_inp'" := ((point_t '× point_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'swap_out'" := ((point_t '× point_t
  ) : choice_type) (in custom pack_type at level 2).
Definition SWAP : nat :=
  (140).
Program Definition swap
   : package (fset.fset0) [interface  ] [interface
  #val #[ SWAP ] : swap_inp → swap_out ] :=
  ([package #def #[ SWAP ] (temp_inp : swap_inp) : swap_out { 
    let '(x_135) := temp_inp : (point_t '× point_t) in
    ({ code  temp_139 ←
        (ret (x_135)) ;;
      let '(x0_137, x1_136) :=
        (temp_139) : (point_t '× point_t) in
      @ret ((
          (x25519_field_element_t '× x25519_field_element_t) '×
          (x25519_field_element_t '× x25519_field_element_t)
        )) (prod_ce(x1_136, x0_137)) } : code (fset.fset0) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_swap : package _ _ _ :=
  (swap).
Fail Next Obligation.

Definition acc_153_loc : ChoiceEqualityLocation :=
  (((point_t '× point_t) ; 165%nat)).
Notation "'montgomery_ladder_inp'" := (
  scalar_t '× point_t : choice_type) (in custom pack_type at level 2).
Notation "'montgomery_ladder_out'" := (
  point_t : choice_type) (in custom pack_type at level 2).
Definition MONTGOMERY_LADDER : nat :=
  (166).
Program Definition montgomery_ladder
   : package (CEfset ([acc_153_loc])) [interface
  #val #[ POINT_ADD_AND_DOUBLE ] : point_add_and_double_inp → point_add_and_double_out ;
  #val #[ SWAP ] : swap_inp → swap_out ] [interface
  #val #[ MONTGOMERY_LADDER ] : montgomery_ladder_inp → montgomery_ladder_out
  ] :=
  (
    [package #def #[ MONTGOMERY_LADDER ] (temp_inp : montgomery_ladder_inp) : montgomery_ladder_out { 
    let '(k_147 , init_146) := temp_inp : scalar_t '× point_t in
    #import {sig #[ POINT_ADD_AND_DOUBLE ] : point_add_and_double_inp → point_add_and_double_out } as point_add_and_double ;;
    let point_add_and_double := fun x_0 x_1 => point_add_and_double (x_0,x_1) in
    #import {sig #[ SWAP ] : swap_inp → swap_out } as swap ;;
    let swap := fun x_0 => swap (x_0) in
    ({ code  '(inf_145 : (x25519_field_element_t '× x25519_field_element_t
          )) ←
        ( '(temp_142 : x25519_field_element_t) ←
            (nat_mod_from_literal (
                0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
                @repr U128 1)) ;;
           '(temp_144 : x25519_field_element_t) ←
            (nat_mod_from_literal (
                0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
                @repr U128 0)) ;;
          ret (prod_ce(temp_142, temp_144))) ;;
       '(acc_153 : (point_t '× point_t)) ←
          (ret (prod_ce(inf_145, init_146))) ;;
        #put acc_153_loc := acc_153 ;;
       '(acc_153 : (
            ((x25519_field_element_t '× x25519_field_element_t) '× point_t)
          )) ←
        (foldi' (usize 0) (usize 256) acc_153 (L2 := CEfset ([acc_153_loc])) (
              I2 := [interface
              #val #[ POINT_ADD_AND_DOUBLE ] : point_add_and_double_inp → point_add_and_double_out ;
              #val #[ SWAP ] : swap_inp → swap_out
              ]) (H_loc_incl := _) (H_opsig_incl := _) (fun i_148 acc_153 =>
            ({ code  '(temp_150 : uint_size) ←
                ((usize 255) .- (i_148)) ;;
               temp_152 ←
                (nat_mod_bit (k_147) (temp_150)) ;;
               '(acc_153 : (
                    (
                      (x25519_field_element_t '× x25519_field_element_t) '×
                      point_t
                    )
                  )) ←
                (if temp_152:bool_ChoiceEquality
                  then (({ code  '(acc_153 : (
                              (x25519_field_element_t '× x25519_field_element_t
                              ) '×
                              point_t
                            )) ←
                          (( '(temp_155 : (point_t '× point_t)) ←
                                (swap (acc_153)) ;;
                              ret (temp_155))) ;;
                        #put acc_153_loc := acc_153 ;;
                      
                       '(acc_153 : (
                              (x25519_field_element_t '× x25519_field_element_t
                              ) '×
                              point_t
                            )) ←
                          (( '(temp_157 : (point_t '× point_t)) ←
                                (point_add_and_double (init_146) (acc_153)) ;;
                              ret (temp_157))) ;;
                        #put acc_153_loc := acc_153 ;;
                      
                       '(acc_153 : (
                              (x25519_field_element_t '× x25519_field_element_t
                              ) '×
                              point_t
                            )) ←
                          (( '(temp_159 : (point_t '× point_t)) ←
                                (swap (acc_153)) ;;
                              ret (temp_159))) ;;
                        #put acc_153_loc := acc_153 ;;
                      
                      @ret ((
                          (
                            (x25519_field_element_t '× x25519_field_element_t
                            ) '×
                            point_t
                          )
                        )) (acc_153) } : code (CEfset (
                          [acc_153_loc])) [interface
                      #val #[ POINT_ADD_AND_DOUBLE ] : point_add_and_double_inp → point_add_and_double_out ;
                      #val #[ SWAP ] : swap_inp → swap_out ] _))
                  else  (({ code  '(acc_153 : (
                              (x25519_field_element_t '× x25519_field_element_t
                              ) '×
                              point_t
                            )) ←
                          (( '(temp_161 : (point_t '× point_t)) ←
                                (point_add_and_double (init_146) (acc_153)) ;;
                              ret (temp_161))) ;;
                        #put acc_153_loc := acc_153 ;;
                      
                      @ret ((
                          (
                            (x25519_field_element_t '× x25519_field_element_t
                            ) '×
                            point_t
                          )
                        )) (acc_153) } : code (CEfset (
                          [acc_153_loc])) [interface
                      #val #[ POINT_ADD_AND_DOUBLE ] : point_add_and_double_inp → point_add_and_double_out
                      ] _))) ;;
              
              @ret ((
                  (
                    (x25519_field_element_t '× x25519_field_element_t) '×
                    point_t
                  )
                )) (acc_153) } : code (CEfset ([acc_153_loc])) [interface
              #val #[ POINT_ADD_AND_DOUBLE ] : point_add_and_double_inp → point_add_and_double_out ;
              #val #[ SWAP ] : swap_inp → swap_out ] _))) ;;
      
       temp_164 ←
        (ret (acc_153)) ;;
      let '(out_162, _) :=
        (temp_164) : (
        (x25519_field_element_t '× x25519_field_element_t) '×
        point_t
      ) in
      @ret ((x25519_field_element_t '× x25519_field_element_t)) (
        out_162) } : code (CEfset ([acc_153_loc])) [interface
      #val #[ POINT_ADD_AND_DOUBLE ] : point_add_and_double_inp → point_add_and_double_out ;
      #val #[ SWAP ] : swap_inp → swap_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_montgomery_ladder : package _ _ _ :=
  (seq_link montgomery_ladder link_rest(
      package_point_add_and_double,package_swap)).
Fail Next Obligation.


Notation "'x25519_scalarmult_inp'" := (
  x25519_serialized_scalar_t '× x25519_serialized_point_t : choice_type) (in custom pack_type at level 2).
Notation "'x25519_scalarmult_out'" := (
  x25519_serialized_point_t : choice_type) (in custom pack_type at level 2).
Definition X25519_SCALARMULT : nat :=
  (180).
Program Definition x25519_scalarmult
   : package (CEfset ([])) [interface
  #val #[ DECODE_POINT ] : decode_point_inp → decode_point_out ;
  #val #[ DECODE_SCALAR ] : decode_scalar_inp → decode_scalar_out ;
  #val #[ ENCODE_POINT ] : encode_point_inp → encode_point_out ;
  #val #[ MONTGOMERY_LADDER ] : montgomery_ladder_inp → montgomery_ladder_out
  ] [interface
  #val #[ X25519_SCALARMULT ] : x25519_scalarmult_inp → x25519_scalarmult_out
  ] :=
  (
    [package #def #[ X25519_SCALARMULT ] (temp_inp : x25519_scalarmult_inp) : x25519_scalarmult_out { 
    let '(
      s_167 , p_170) := temp_inp : x25519_serialized_scalar_t '× x25519_serialized_point_t in
    #import {sig #[ DECODE_POINT ] : decode_point_inp → decode_point_out } as decode_point ;;
    let decode_point := fun x_0 => decode_point (x_0) in
    #import {sig #[ DECODE_SCALAR ] : decode_scalar_inp → decode_scalar_out } as decode_scalar ;;
    let decode_scalar := fun x_0 => decode_scalar (x_0) in
    #import {sig #[ ENCODE_POINT ] : encode_point_inp → encode_point_out } as encode_point ;;
    let encode_point := fun x_0 => encode_point (x_0) in
    #import {sig #[ MONTGOMERY_LADDER ] : montgomery_ladder_inp → montgomery_ladder_out } as montgomery_ladder ;;
    let montgomery_ladder := fun x_0 x_1 => montgomery_ladder (x_0,x_1) in
    ({ code  '(s_173 : scalar_t) ←
        ( '(temp_169 : scalar_t) ←
            (decode_scalar (s_167)) ;;
          ret (temp_169)) ;;
       '(p_174 : (x25519_field_element_t '× x25519_field_element_t)) ←
        ( '(temp_172 : point_t) ←
            (decode_point (p_170)) ;;
          ret (temp_172)) ;;
       '(r_177 : (x25519_field_element_t '× x25519_field_element_t)) ←
        ( '(temp_176 : point_t) ←
            (montgomery_ladder (s_173) (p_174)) ;;
          ret (temp_176)) ;;
       '(temp_179 : x25519_serialized_point_t) ←
        (encode_point (r_177)) ;;
      @ret (x25519_serialized_point_t) (temp_179) } : code (CEfset (
          [])) [interface
      #val #[ DECODE_POINT ] : decode_point_inp → decode_point_out ;
      #val #[ DECODE_SCALAR ] : decode_scalar_inp → decode_scalar_out ;
      #val #[ ENCODE_POINT ] : encode_point_inp → encode_point_out ;
      #val #[ MONTGOMERY_LADDER ] : montgomery_ladder_inp → montgomery_ladder_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_x25519_scalarmult : package _ _ _ :=
  (seq_link x25519_scalarmult link_rest(
      package_decode_point,package_decode_scalar,package_encode_point,package_montgomery_ladder)).
Fail Next Obligation.

Definition base_186_loc : ChoiceEqualityLocation :=
  ((x25519_serialized_point_t ; 189%nat)).
Notation "'x25519_secret_to_public_inp'" := (
  x25519_serialized_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'x25519_secret_to_public_out'" := (
  x25519_serialized_point_t : choice_type) (in custom pack_type at level 2).
Definition X25519_SECRET_TO_PUBLIC : nat :=
  (190).
Program Definition x25519_secret_to_public
   : package (CEfset ([base_186_loc])) [interface
  #val #[ X25519_SCALARMULT ] : x25519_scalarmult_inp → x25519_scalarmult_out
  ] [interface
  #val #[ X25519_SECRET_TO_PUBLIC ] : x25519_secret_to_public_inp → x25519_secret_to_public_out
  ] :=
  (
    [package #def #[ X25519_SECRET_TO_PUBLIC ] (temp_inp : x25519_secret_to_public_inp) : x25519_secret_to_public_out { 
    let '(s_185) := temp_inp : x25519_serialized_scalar_t in
    #import {sig #[ X25519_SCALARMULT ] : x25519_scalarmult_inp → x25519_scalarmult_out } as x25519_scalarmult ;;
    let x25519_scalarmult := fun x_0 x_1 => x25519_scalarmult (x_0,x_1) in
    ({ code  '(base_186 : x25519_serialized_point_t) ←
          ( '(temp_182 : x25519_serialized_point_t) ←
              (array_new_ (default : uint8) (32)) ;;
            ret (temp_182)) ;;
        #put base_186_loc := base_186 ;;
       '(base_186 : x25519_serialized_point_t) ←
        ( '(temp_184 : int8) ←
            (secret (@repr U8 9)) ;;
          ret (array_upd base_186 (usize 0) (temp_184))) ;;
      
       '(temp_188 : x25519_serialized_point_t) ←
        (x25519_scalarmult (s_185) (base_186)) ;;
      @ret (x25519_serialized_point_t) (temp_188) } : code (CEfset (
          [base_186_loc])) [interface
      #val #[ X25519_SCALARMULT ] : x25519_scalarmult_inp → x25519_scalarmult_out
      ] _)
    }]).
Fail Next Obligation.
Program Definition package_x25519_secret_to_public : package _ _ _ :=
  (seq_link x25519_secret_to_public link_rest(package_x25519_scalarmult)).
Fail Next Obligation.

