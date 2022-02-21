(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Inductive error_t :=
| InvalidAddition : error_t.

Definition bits_v : uint_size :=
  usize 256.

Definition field_canvas_t := nseq (int8) (32).
Definition p256_field_element_t :=
  nat_mod 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff.

Definition scalar_canvas_t := nseq (int8) (32).
Definition p256_scalar_t :=
  nat_mod 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551.

Notation "'affine_t'" := ((p256_field_element_t × p256_field_element_t
)) : hacspec_scope.

Notation "'affine_result_t'" := ((result affine_t error_t)) : hacspec_scope.

Notation "'p256_jacobian_t'" := ((
  p256_field_element_t ×
  p256_field_element_t ×
  p256_field_element_t
)) : hacspec_scope.

Notation "'jacobian_result_t'" := ((
  result p256_jacobian_t error_t)) : hacspec_scope.

Definition element_t := nseq (uint8) (usize 32).

Definition jacobian_to_affine (p_0 : p256_jacobian_t) : affine_t :=
  let '(x_1, y_2, z_3) :=
    p_0 in 
  let z2_4 : p256_field_element_t :=
    nat_mod_exp (z_3) (@repr WORDSIZE32 2) in 
  let z2i_5 : p256_field_element_t :=
    nat_mod_inv (z2_4) in 
  let z3_6 : p256_field_element_t :=
    (z_3) *% (z2_4) in 
  let z3i_7 : p256_field_element_t :=
    nat_mod_inv (z3_6) in 
  let x_8 : p256_field_element_t :=
    (x_1) *% (z2i_5) in 
  let y_9 : p256_field_element_t :=
    (y_2) *% (z3i_7) in 
  (x_8, y_9).

Definition affine_to_jacobian (p_10 : affine_t) : p256_jacobian_t :=
  let '(x_11, y_12) :=
    p_10 in 
  (
    x_11,
    y_12,
    nat_mod_from_literal (
      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
      @repr WORDSIZE128 1) : p256_field_element_t
  ).

Definition point_double (p_13 : p256_jacobian_t) : p256_jacobian_t :=
  let '(x1_14, y1_15, z1_16) :=
    p_13 in 
  let delta_17 : p256_field_element_t :=
    nat_mod_exp (z1_16) (@repr WORDSIZE32 2) in 
  let gamma_18 : p256_field_element_t :=
    nat_mod_exp (y1_15) (@repr WORDSIZE32 2) in 
  let beta_19 : p256_field_element_t :=
    (x1_14) *% (gamma_18) in 
  let alpha_1_20 : p256_field_element_t :=
    (x1_14) -% (delta_17) in 
  let alpha_2_21 : p256_field_element_t :=
    (x1_14) +% (delta_17) in 
  let alpha_22 : p256_field_element_t :=
    (nat_mod_from_literal (
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
        @repr WORDSIZE128 3) : p256_field_element_t) *% ((alpha_1_20) *% (
        alpha_2_21)) in 
  let x3_23 : p256_field_element_t :=
    (nat_mod_exp (alpha_22) (@repr WORDSIZE32 2)) -% ((nat_mod_from_literal (
          0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
          @repr WORDSIZE128 8) : p256_field_element_t) *% (beta_19)) in 
  let z3_24 : p256_field_element_t :=
    nat_mod_exp ((y1_15) +% (z1_16)) (@repr WORDSIZE32 2) in 
  let z3_25 : p256_field_element_t :=
    (z3_24) -% ((gamma_18) +% (delta_17)) in 
  let y3_1_26 : p256_field_element_t :=
    ((nat_mod_from_literal (
          0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
          @repr WORDSIZE128 4) : p256_field_element_t) *% (beta_19)) -% (
      x3_23) in 
  let y3_2_27 : p256_field_element_t :=
    (nat_mod_from_literal (
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
        @repr WORDSIZE128 8) : p256_field_element_t) *% ((gamma_18) *% (
        gamma_18)) in 
  let y3_28 : p256_field_element_t :=
    ((alpha_22) *% (y3_1_26)) -% (y3_2_27) in 
  (x3_23, y3_28, z3_25).

Definition is_point_at_infinity (p_29 : p256_jacobian_t) : bool :=
  let '(x_30, y_31, z_32) :=
    p_29 in 
  nat_mod_equal (z_32) (nat_mod_from_literal (
      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
      @repr WORDSIZE128 0) : p256_field_element_t).

Definition s1_equal_s2
  (s1_33 : p256_field_element_t)
  (s2_34 : p256_field_element_t)
  : jacobian_result_t :=
  (if (nat_mod_equal (s1_33) (s2_34)):bool then (@Err p256_jacobian_t error_t (
        InvalidAddition)) else (@Ok p256_jacobian_t error_t ((
          nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            @repr WORDSIZE128 0) : p256_field_element_t,
          nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            @repr WORDSIZE128 1) : p256_field_element_t,
          nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            @repr WORDSIZE128 0) : p256_field_element_t
        )))).

Definition point_add_jacob
  (p_35 : p256_jacobian_t)
  (q_36 : p256_jacobian_t)
  : jacobian_result_t :=
  let result_37 : (result p256_jacobian_t error_t) :=
    @Ok p256_jacobian_t error_t (q_36) in 
  let '(result_37) :=
    if negb (is_point_at_infinity (p_35)):bool then (let '(result_37) :=
        if is_point_at_infinity (q_36):bool then (let result_37 :=
            @Ok p256_jacobian_t error_t (p_35) in 
          (result_37)) else (let '(x1_38, y1_39, z1_40) :=
            p_35 in 
          let '(x2_41, y2_42, z2_43) :=
            q_36 in 
          let z1z1_44 : p256_field_element_t :=
            nat_mod_exp (z1_40) (@repr WORDSIZE32 2) in 
          let z2z2_45 : p256_field_element_t :=
            nat_mod_exp (z2_43) (@repr WORDSIZE32 2) in 
          let u1_46 : p256_field_element_t :=
            (x1_38) *% (z2z2_45) in 
          let u2_47 : p256_field_element_t :=
            (x2_41) *% (z1z1_44) in 
          let s1_48 : p256_field_element_t :=
            ((y1_39) *% (z2_43)) *% (z2z2_45) in 
          let s2_49 : p256_field_element_t :=
            ((y2_42) *% (z1_40)) *% (z1z1_44) in 
          let '(result_37) :=
            if nat_mod_equal (u1_46) (u2_47):bool then (let result_37 :=
                s1_equal_s2 (s1_48) (s2_49) in 
              (result_37)) else (let h_50 : p256_field_element_t :=
                (u2_47) -% (u1_46) in 
              let i_51 : p256_field_element_t :=
                nat_mod_exp ((nat_mod_from_literal (
                      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                      @repr WORDSIZE128 2) : p256_field_element_t) *% (h_50)) (
                  @repr WORDSIZE32 2) in 
              let j_52 : p256_field_element_t :=
                (h_50) *% (i_51) in 
              let r_53 : p256_field_element_t :=
                (nat_mod_from_literal (
                    0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                    @repr WORDSIZE128 2) : p256_field_element_t) *% ((
                    s2_49) -% (s1_48)) in 
              let v_54 : p256_field_element_t :=
                (u1_46) *% (i_51) in 
              let x3_1_55 : p256_field_element_t :=
                (nat_mod_from_literal (
                    0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                    @repr WORDSIZE128 2) : p256_field_element_t) *% (v_54) in 
              let x3_2_56 : p256_field_element_t :=
                (nat_mod_exp (r_53) (@repr WORDSIZE32 2)) -% (j_52) in 
              let x3_57 : p256_field_element_t :=
                (x3_2_56) -% (x3_1_55) in 
              let y3_1_58 : p256_field_element_t :=
                ((nat_mod_from_literal (
                      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                      @repr WORDSIZE128 2) : p256_field_element_t) *% (
                    s1_48)) *% (j_52) in 
              let y3_2_59 : p256_field_element_t :=
                (r_53) *% ((v_54) -% (x3_57)) in 
              let y3_60 : p256_field_element_t :=
                (y3_2_59) -% (y3_1_58) in 
              let z3_61 : p256_field_element_t :=
                nat_mod_exp ((z1_40) +% (z2_43)) (@repr WORDSIZE32 2) in 
              let z3_62 : p256_field_element_t :=
                ((z3_61) -% ((z1z1_44) +% (z2z2_45))) *% (h_50) in 
              let result_37 :=
                @Ok p256_jacobian_t error_t ((x3_57, y3_60, z3_62)) in 
              (result_37)) in 
          (result_37)) in 
      (result_37)) else ((result_37)) in 
  result_37.

Definition ltr_mul
  (k_63 : p256_scalar_t)
  (p_64 : p256_jacobian_t)
  : jacobian_result_t :=
  let q_65 : (
      p256_field_element_t ×
      p256_field_element_t ×
      p256_field_element_t
    ) :=
    (
      nat_mod_from_literal (
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
        @repr WORDSIZE128 0) : p256_field_element_t,
      nat_mod_from_literal (
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
        @repr WORDSIZE128 1) : p256_field_element_t,
      nat_mod_from_literal (
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
        @repr WORDSIZE128 0) : p256_field_element_t
    ) in 
  bind (foldibnd (usize 0) to (bits_v) for q_65 >> (fun i_66 q_65 =>
    let q_65 :=
      point_double (q_65) in 
    ifbnd nat_mod_equal (nat_mod_get_bit (k_63) (((bits_v) - (usize 1)) - (
          i_66))) (nat_mod_one ) : bool
    thenbnd (bind (point_add_jacob (q_65) (p_64)) (fun q_65  => Ok ((q_65))))
    else ((q_65)) >> (fun '(q_65) =>
    Ok ((q_65))))) (fun q_65 => @Ok p256_jacobian_t error_t (q_65)).

Definition p256_point_mul
  (k_67 : p256_scalar_t)
  (p_68 : affine_t)
  : affine_result_t :=
  bind (ltr_mul (k_67) (affine_to_jacobian (p_68))) (fun jac_69 =>
    @Ok affine_t error_t (jacobian_to_affine (jac_69))).

Definition p256_point_mul_base (k_70 : p256_scalar_t) : affine_result_t :=
  let base_point_71 : (p256_field_element_t × p256_field_element_t) :=
    (
      nat_mod_from_byte_seq_be (array_from_list uint8 (let l :=
            [
              secret (@repr WORDSIZE8 107) : int8;
              secret (@repr WORDSIZE8 23) : int8;
              secret (@repr WORDSIZE8 209) : int8;
              secret (@repr WORDSIZE8 242) : int8;
              secret (@repr WORDSIZE8 225) : int8;
              secret (@repr WORDSIZE8 44) : int8;
              secret (@repr WORDSIZE8 66) : int8;
              secret (@repr WORDSIZE8 71) : int8;
              secret (@repr WORDSIZE8 248) : int8;
              secret (@repr WORDSIZE8 188) : int8;
              secret (@repr WORDSIZE8 230) : int8;
              secret (@repr WORDSIZE8 229) : int8;
              secret (@repr WORDSIZE8 99) : int8;
              secret (@repr WORDSIZE8 164) : int8;
              secret (@repr WORDSIZE8 64) : int8;
              secret (@repr WORDSIZE8 242) : int8;
              secret (@repr WORDSIZE8 119) : int8;
              secret (@repr WORDSIZE8 3) : int8;
              secret (@repr WORDSIZE8 125) : int8;
              secret (@repr WORDSIZE8 129) : int8;
              secret (@repr WORDSIZE8 45) : int8;
              secret (@repr WORDSIZE8 235) : int8;
              secret (@repr WORDSIZE8 51) : int8;
              secret (@repr WORDSIZE8 160) : int8;
              secret (@repr WORDSIZE8 244) : int8;
              secret (@repr WORDSIZE8 161) : int8;
              secret (@repr WORDSIZE8 57) : int8;
              secret (@repr WORDSIZE8 69) : int8;
              secret (@repr WORDSIZE8 216) : int8;
              secret (@repr WORDSIZE8 152) : int8;
              secret (@repr WORDSIZE8 194) : int8;
              secret (@repr WORDSIZE8 150) : int8
            ] in  l)) : p256_field_element_t,
      nat_mod_from_byte_seq_be (array_from_list uint8 (let l :=
            [
              secret (@repr WORDSIZE8 79) : int8;
              secret (@repr WORDSIZE8 227) : int8;
              secret (@repr WORDSIZE8 66) : int8;
              secret (@repr WORDSIZE8 226) : int8;
              secret (@repr WORDSIZE8 254) : int8;
              secret (@repr WORDSIZE8 26) : int8;
              secret (@repr WORDSIZE8 127) : int8;
              secret (@repr WORDSIZE8 155) : int8;
              secret (@repr WORDSIZE8 142) : int8;
              secret (@repr WORDSIZE8 231) : int8;
              secret (@repr WORDSIZE8 235) : int8;
              secret (@repr WORDSIZE8 74) : int8;
              secret (@repr WORDSIZE8 124) : int8;
              secret (@repr WORDSIZE8 15) : int8;
              secret (@repr WORDSIZE8 158) : int8;
              secret (@repr WORDSIZE8 22) : int8;
              secret (@repr WORDSIZE8 43) : int8;
              secret (@repr WORDSIZE8 206) : int8;
              secret (@repr WORDSIZE8 51) : int8;
              secret (@repr WORDSIZE8 87) : int8;
              secret (@repr WORDSIZE8 107) : int8;
              secret (@repr WORDSIZE8 49) : int8;
              secret (@repr WORDSIZE8 94) : int8;
              secret (@repr WORDSIZE8 206) : int8;
              secret (@repr WORDSIZE8 203) : int8;
              secret (@repr WORDSIZE8 182) : int8;
              secret (@repr WORDSIZE8 64) : int8;
              secret (@repr WORDSIZE8 104) : int8;
              secret (@repr WORDSIZE8 55) : int8;
              secret (@repr WORDSIZE8 191) : int8;
              secret (@repr WORDSIZE8 81) : int8;
              secret (@repr WORDSIZE8 245) : int8
            ] in  l)) : p256_field_element_t
    ) in 
  p256_point_mul (k_70) (base_point_71).

Definition point_add_distinct
  (p_72 : affine_t)
  (q_73 : affine_t)
  : affine_result_t :=
  bind (point_add_jacob (affine_to_jacobian (p_72)) (affine_to_jacobian (
        q_73))) (fun r_74 => @Ok affine_t error_t (jacobian_to_affine (r_74))).

Definition point_add (p_75 : affine_t) (q_76 : affine_t) : affine_result_t :=
  (if ((p_75) !=.? (q_76)):bool then (point_add_distinct (p_75) (q_76)) else (
      @Ok affine_t error_t (jacobian_to_affine (point_double (
            affine_to_jacobian (p_75)))))).

Definition p256_validate_private_key (k_77 : byte_seq) : bool :=
  let valid_78 : bool :=
    true in 
  let k_element_79 : p256_scalar_t :=
    nat_mod_from_byte_seq_be (k_77) : p256_scalar_t in 
  let k_element_bytes_80 : seq uint8 :=
    nat_mod_to_byte_seq_be (k_element_79) in 
  let all_zero_81 : bool :=
    true in 
  let '(valid_78, all_zero_81) :=
    foldi (usize 0) (seq_len (k_77)) (fun i_82 '(valid_78, all_zero_81) =>
      let '(all_zero_81) :=
        if negb (uint8_equal (seq_index (k_77) (i_82)) (secret (
              @repr WORDSIZE8 0) : int8)):bool then (let all_zero_81 :=
            false in 
          (all_zero_81)) else ((all_zero_81)) in 
      let '(valid_78) :=
        if negb (uint8_equal (seq_index (k_element_bytes_80) (i_82)) (
            seq_index (k_77) (i_82))):bool then (let valid_78 :=
            false in 
          (valid_78)) else ((valid_78)) in 
      (valid_78, all_zero_81))
    (valid_78, all_zero_81) in 
  (valid_78) && (negb (all_zero_81)).

Definition p256_validate_public_key (p_83 : affine_t) : bool :=
  let b_84 : p256_field_element_t :=
    nat_mod_from_byte_seq_be ([
        secret (@repr WORDSIZE8 90) : int8;
        secret (@repr WORDSIZE8 198) : int8;
        secret (@repr WORDSIZE8 53) : int8;
        secret (@repr WORDSIZE8 216) : int8;
        secret (@repr WORDSIZE8 170) : int8;
        secret (@repr WORDSIZE8 58) : int8;
        secret (@repr WORDSIZE8 147) : int8;
        secret (@repr WORDSIZE8 231) : int8;
        secret (@repr WORDSIZE8 179) : int8;
        secret (@repr WORDSIZE8 235) : int8;
        secret (@repr WORDSIZE8 189) : int8;
        secret (@repr WORDSIZE8 85) : int8;
        secret (@repr WORDSIZE8 118) : int8;
        secret (@repr WORDSIZE8 152) : int8;
        secret (@repr WORDSIZE8 134) : int8;
        secret (@repr WORDSIZE8 188) : int8;
        secret (@repr WORDSIZE8 101) : int8;
        secret (@repr WORDSIZE8 29) : int8;
        secret (@repr WORDSIZE8 6) : int8;
        secret (@repr WORDSIZE8 176) : int8;
        secret (@repr WORDSIZE8 204) : int8;
        secret (@repr WORDSIZE8 83) : int8;
        secret (@repr WORDSIZE8 176) : int8;
        secret (@repr WORDSIZE8 246) : int8;
        secret (@repr WORDSIZE8 59) : int8;
        secret (@repr WORDSIZE8 206) : int8;
        secret (@repr WORDSIZE8 60) : int8;
        secret (@repr WORDSIZE8 62) : int8;
        secret (@repr WORDSIZE8 39) : int8;
        secret (@repr WORDSIZE8 210) : int8;
        secret (@repr WORDSIZE8 96) : int8;
        secret (@repr WORDSIZE8 75) : int8
      ]) : p256_field_element_t in 
  let point_at_infinity_85 : bool :=
    is_point_at_infinity (affine_to_jacobian (p_83)) in 
  let '(x_86, y_87) :=
    p_83 in 
  let on_curve_88 : bool :=
    ((y_87) *% (y_87)) =.? (((((x_86) *% (x_86)) *% (x_86)) -% ((
            nat_mod_from_literal (
              0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
              @repr WORDSIZE128 3) : p256_field_element_t) *% (x_86))) +% (
        b_84)) in 
  (negb (point_at_infinity_85)) && (on_curve_88).

