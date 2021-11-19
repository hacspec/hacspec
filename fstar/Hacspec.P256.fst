module Hacspec.P256

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib
noeq
type error_t = | InvalidAddition_error_t : error_t

let bits_v:uint_size = usize 256

type field_canvas_t = lseq (pub_uint8) (32)

type p256_field_element_t =
  nat_mod 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff

type scalar_canvas_t = lseq (pub_uint8) (32)

type p256_scalar_t = nat_mod 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

type affine_t = (p256_field_element_t & p256_field_element_t)

type affine_result_t = (result affine_t error_t)

type p256_jacobian_t = (p256_field_element_t & p256_field_element_t & p256_field_element_t)

type jacobian_result_t = (result p256_jacobian_t error_t)

type element_t = lseq (uint8) (usize 32)

let jacobian_to_affine (p_0: p256_jacobian_t) : affine_t =
  let x_1, y_2, z_3 = p_0 in
  let z2_4 =
    nat_exp (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (z_3) (pub_u32 0x2)
  in
  let z2i_5 = nat_inv (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (z2_4) in
  let z3_6 = (z_3) *% (z2_4) in
  let z3i_7 = nat_inv (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (z3_6) in
  let x_8 = (x_1) *% (z2i_5) in
  let y_9 = (y_2) *% (z3i_7) in
  (x_8, y_9)

let affine_to_jacobian (p_10: affine_t) : p256_jacobian_t =
  let x_11, y_12 = p_10 in
  (x_11,
    y_12,
    nat_from_literal (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
      (pub_u128 0x1))

let point_double (p_13: p256_jacobian_t) : p256_jacobian_t =
  let x1_14, y1_15, z1_16 = p_13 in
  let delta_17 =
    nat_exp (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
      (z1_16)
      (pub_u32 0x2)
  in
  let gamma_18 =
    nat_exp (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
      (y1_15)
      (pub_u32 0x2)
  in
  let beta_19 = (x1_14) *% (gamma_18) in
  let alpha_1_20 = (x1_14) -% (delta_17) in
  let alpha_2_21 = (x1_14) +% (delta_17) in
  let alpha_22 =
    (nat_from_literal (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
        (pub_u128 0x3)) *%
    ((alpha_1_20) *% (alpha_2_21))
  in
  let x3_23 =
    (nat_exp (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
        (alpha_22)
        (pub_u32 0x2)) -%
    ((nat_from_literal (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
          (pub_u128 0x8)) *%
      (beta_19))
  in
  let z3_24 =
    nat_exp (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
      ((y1_15) +% (z1_16))
      (pub_u32 0x2)
  in
  let z3_25 = (z3_24) -% ((gamma_18) +% (delta_17)) in
  let y3_1_26 =
    ((nat_from_literal (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
          (pub_u128 0x4)) *%
      (beta_19)) -%
    (x3_23)
  in
  let y3_2_27 =
    (nat_from_literal (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
        (pub_u128 0x8)) *%
    ((gamma_18) *% (gamma_18))
  in
  let y3_28 = ((alpha_22) *% (y3_1_26)) -% (y3_2_27) in
  (x3_23, y3_28, z3_25)

let is_point_at_infinity (p_29: p256_jacobian_t) : bool =
  let x_30, y_31, z_32 = p_29 in
  nat_equal (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
    (z_32)
    (nat_from_literal (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
        (pub_u128 0x0))

let s1_equal_s2 (s1_33 s2_34: p256_field_element_t) : jacobian_result_t =
  if
    (nat_equal (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (s1_33) (s2_34))
  then (Err (InvalidAddition_error_t))
  else
    (Ok
      ((nat_from_literal (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
            (pub_u128 0x0),
          nat_from_literal (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
            (pub_u128 0x1),
          nat_from_literal (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
            (pub_u128 0x0))))

let point_add_jacob (p_35 q_36: p256_jacobian_t) : jacobian_result_t =
  let result_37 = Ok (q_36) in
  let result_37 =
    if not (is_point_at_infinity (p_35))
    then
      let result_37 =
        if is_point_at_infinity (q_36)
        then
          let result_37 = Ok (p_35) in
          (result_37)
        else
          let x1_38, y1_39, z1_40 = p_35 in
          let x2_41, y2_42, z2_43 = q_36 in
          let z1z1_44 =
            nat_exp (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
              (z1_40)
              (pub_u32 0x2)
          in
          let z2z2_45 =
            nat_exp (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
              (z2_43)
              (pub_u32 0x2)
          in
          let u1_46 = (x1_38) *% (z2z2_45) in
          let u2_47 = (x2_41) *% (z1z1_44) in
          let s1_48 = ((y1_39) *% (z2_43)) *% (z2z2_45) in
          let s2_49 = ((y2_42) *% (z1_40)) *% (z1z1_44) in
          let result_37 =
            if
              nat_equal (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
                (u1_46)
                (u2_47)
            then
              let result_37 = s1_equal_s2 (s1_48) (s2_49) in
              (result_37)
            else
              let h_50 = (u2_47) -% (u1_46) in
              let i_51 =
                nat_exp (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
                  ((nat_from_literal (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
                        )
                        (pub_u128 0x2)) *%
                    (h_50))
                  (pub_u32 0x2)
              in
              let j_52 = (h_50) *% (i_51) in
              let r_53 =
                (nat_from_literal (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
                    )
                    (pub_u128 0x2)) *%
                ((s2_49) -% (s1_48))
              in
              let v_54 = (u1_46) *% (i_51) in
              let x3_1_55 =
                (nat_from_literal (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
                    )
                    (pub_u128 0x2)) *%
                (v_54)
              in
              let x3_2_56 =
                (nat_exp (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
                    (r_53)
                    (pub_u32 0x2)) -%
                (j_52)
              in
              let x3_57 = (x3_2_56) -% (x3_1_55) in
              let y3_1_58 =
                ((nat_from_literal (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
                      )
                      (pub_u128 0x2)) *%
                  (s1_48)) *%
                (j_52)
              in
              let y3_2_59 = (r_53) *% ((v_54) -% (x3_57)) in
              let y3_60 = (y3_2_59) -% (y3_1_58) in
              let z3_61 =
                nat_exp (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
                  ((z1_40) +% (z2_43))
                  (pub_u32 0x2)
              in
              let z3_62 = ((z3_61) -% ((z1z1_44) +% (z2z2_45))) *% (h_50) in
              let result_37 = Ok ((x3_57, y3_60, z3_62)) in
              (result_37)
          in
          (result_37)
      in
      (result_37)
    else (result_37)
  in
  result_37

let ltr_mul (k_63: p256_scalar_t) (p_64: p256_jacobian_t) : jacobian_result_t =
  let q_65 =
    (nat_from_literal (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
        (pub_u128 0x0),
      nat_from_literal (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
        (pub_u128 0x1),
      nat_from_literal (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
        (pub_u128 0x0))
  in
  match
    (foldi_result (usize 0)
        (bits_v)
        (fun i_66 q_65 ->
            let q_65 = point_double (q_65) in
            match
              (if
                  nat_equal (0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551)
                    (nat_get_bit (0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
                        )
                        (k_63)
                        (((bits_v) - (usize 1)) - (i_66)))
                    (nat_one (0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551))
                then
                  match (point_add_jacob (q_65) (p_64)) with
                  | Err x -> Err x
                  | Ok q_65 -> Ok ((q_65))
                else Ok ((q_65)))
            with
            | Err x -> Err x
            | Ok q_65 -> Ok ((q_65)))
        (q_65))
  with
  | Err x -> Err x
  | Ok q_65 -> Ok (q_65)

let p256_point_mul (k_67: p256_scalar_t) (p_68: affine_t) : affine_result_t =
  match (ltr_mul (k_67) (affine_to_jacobian (p_68))) with
  | Err x -> Err x
  | Ok jac_69 -> Ok (jacobian_to_affine (jac_69))

let p256_point_mul_base (k_70: p256_scalar_t) : affine_result_t =
  let base_point_71 =
    (nat_from_byte_seq_be (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
        (32)
        (array_from_list (let l =
                [
                  secret (pub_u8 0x6b); secret (pub_u8 0x17); secret (pub_u8 0xd1);
                  secret (pub_u8 0xf2); secret (pub_u8 0xe1); secret (pub_u8 0x2c);
                  secret (pub_u8 0x42); secret (pub_u8 0x47); secret (pub_u8 0xf8);
                  secret (pub_u8 0xbc); secret (pub_u8 0xe6); secret (pub_u8 0xe5);
                  secret (pub_u8 0x63); secret (pub_u8 0xa4); secret (pub_u8 0x40);
                  secret (pub_u8 0xf2); secret (pub_u8 0x77); secret (pub_u8 0x3);
                  secret (pub_u8 0x7d); secret (pub_u8 0x81); secret (pub_u8 0x2d);
                  secret (pub_u8 0xeb); secret (pub_u8 0x33); secret (pub_u8 0xa0);
                  secret (pub_u8 0xf4); secret (pub_u8 0xa1); secret (pub_u8 0x39);
                  secret (pub_u8 0x45); secret (pub_u8 0xd8); secret (pub_u8 0x98);
                  secret (pub_u8 0xc2); secret (pub_u8 0x96)
                ]
              in
              assert_norm (List.Tot.length l == 32);
              l)),
      nat_from_byte_seq_be (0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
        (32)
        (array_from_list (let l =
                [
                  secret (pub_u8 0x4f); secret (pub_u8 0xe3); secret (pub_u8 0x42);
                  secret (pub_u8 0xe2); secret (pub_u8 0xfe); secret (pub_u8 0x1a);
                  secret (pub_u8 0x7f); secret (pub_u8 0x9b); secret (pub_u8 0x8e);
                  secret (pub_u8 0xe7); secret (pub_u8 0xeb); secret (pub_u8 0x4a);
                  secret (pub_u8 0x7c); secret (pub_u8 0xf); secret (pub_u8 0x9e);
                  secret (pub_u8 0x16); secret (pub_u8 0x2b); secret (pub_u8 0xce);
                  secret (pub_u8 0x33); secret (pub_u8 0x57); secret (pub_u8 0x6b);
                  secret (pub_u8 0x31); secret (pub_u8 0x5e); secret (pub_u8 0xce);
                  secret (pub_u8 0xcb); secret (pub_u8 0xb6); secret (pub_u8 0x40);
                  secret (pub_u8 0x68); secret (pub_u8 0x37); secret (pub_u8 0xbf);
                  secret (pub_u8 0x51); secret (pub_u8 0xf5)
                ]
              in
              assert_norm (List.Tot.length l == 32);
              l)))
  in
  p256_point_mul (k_70) (base_point_71)

let point_add_distinct (p_72 q_73: affine_t) : affine_result_t =
  match (point_add_jacob (affine_to_jacobian (p_72)) (affine_to_jacobian (q_73))) with
  | Err x -> Err x
  | Ok r_74 -> Ok (jacobian_to_affine (r_74))

let point_add (p_75 q_76: affine_t) : affine_result_t =
  if ((p_75) <> (q_76))
  then (point_add_distinct (p_75) (q_76))
  else (Ok (jacobian_to_affine (point_double (affine_to_jacobian (p_75)))))

