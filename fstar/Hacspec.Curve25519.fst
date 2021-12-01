module Hacspec.Curve25519

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

type field_canvas_t = lseq (pub_uint8) (32)

type x25519_field_element_t =
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed

type scalar_canvas_t = lseq (pub_uint8) (32)

type scalar_t = nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000

type point_t = (x25519_field_element_t & x25519_field_element_t)

type x25519_serialized_point_t = lseq (uint8) (usize 32)

type x25519_serialized_scalar_t = lseq (uint8) (usize 32)

let mask_scalar (s_0: x25519_serialized_scalar_t) : x25519_serialized_scalar_t =
  let k_1 = s_0 in
  let k_1 = array_upd k_1 (usize 0) ((array_index (k_1) (usize 0)) &. (secret (pub_u8 0xf8))) in
  let k_1 = array_upd k_1 (usize 31) ((array_index (k_1) (usize 31)) &. (secret (pub_u8 0x7f))) in
  let k_1 = array_upd k_1 (usize 31) ((array_index (k_1) (usize 31)) |. (secret (pub_u8 0x40))) in
  k_1

let decode_scalar (s_2: x25519_serialized_scalar_t) : scalar_t =
  let k_3 = mask_scalar (s_2) in
  nat_from_byte_seq_le (0x8000000000000000000000000000000000000000000000000000000000000000)
    (32)
    (k_3)

let decode_point (u_4: x25519_serialized_point_t) : point_t =
  let u_5 = u_4 in
  let u_5 = array_upd u_5 (usize 31) ((array_index (u_5) (usize 31)) &. (secret (pub_u8 0x7f))) in
  (nat_from_byte_seq_le (0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed)
      (32)
      (u_5),
    nat_from_literal (0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed)
      (pub_u128 0x1))

let encode_point (p_6: point_t) : x25519_serialized_point_t =
  let x_7, y_8 = p_6 in
  let b_9 =
    (x_7) *% (nat_inv (0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (y_8))
  in
  array_update_start (array_new_ (secret (pub_u8 0x0)) (32))
    (nat_to_byte_seq_le (0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed)
        (32)
        (b_9))

let point_add_and_double (q_10: point_t) (np_11: (point_t & point_t)) : (point_t & point_t) =
  let nq_12, nqp1_13 = np_11 in
  let x_1_14, z_1_15 = q_10 in
  let x_2_16, z_2_17 = nq_12 in
  let x_3_18, z_3_19 = nqp1_13 in
  let a_20 = (x_2_16) +% (z_2_17) in
  let aa_21 =
    nat_pow (0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed)
      (a_20)
      (pub_u128 0x2)
  in
  let b_22 = (x_2_16) -% (z_2_17) in
  let bb_23 = (b_22) *% (b_22) in
  let e_24 = (aa_21) -% (bb_23) in
  let c_25 = (x_3_18) +% (z_3_19) in
  let d_26 = (x_3_18) -% (z_3_19) in
  let da_27 = (d_26) *% (a_20) in
  let cb_28 = (c_25) *% (b_22) in
  let x_3_29 =
    nat_pow (0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed)
      ((da_27) +% (cb_28))
      (pub_u128 0x2)
  in
  let z_3_30 =
    (x_1_14) *%
    (nat_pow (0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed)
        ((da_27) -% (cb_28))
        (pub_u128 0x2))
  in
  let x_2_31 = (aa_21) *% (bb_23) in
  let e121665_32 =
    nat_from_literal (0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed)
      (pub_u128 0x1db41)
  in
  let z_2_33 = (e_24) *% ((aa_21) +% ((e121665_32) *% (e_24))) in
  ((x_2_31, z_2_33), (x_3_29, z_3_30))

let swap (x_34: (point_t & point_t)) : (point_t & point_t) =
  let x0_35, x1_36 = x_34 in
  (x1_36, x0_35)

let montgomery_ladder (k_37: scalar_t) (init_38: point_t) : point_t =
  let inf_39 =
    (nat_from_literal (0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed)
        (pub_u128 0x1),
      nat_from_literal (0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed)
        (pub_u128 0x0))
  in
  let acc_40:(point_t & point_t) = (inf_39, init_38) in
  let acc_40 =
    foldi (usize 0)
      (usize 256)
      (fun i_41 acc_40 ->
          let acc_40 =
            if
              nat_bit (0x8000000000000000000000000000000000000000000000000000000000000000)
                (k_37)
                ((usize 255) - (i_41))
            then
              let acc_40 = swap (acc_40) in
              let acc_40 = point_add_and_double (init_38) (acc_40) in
              let acc_40 = swap (acc_40) in
              (acc_40)
            else
              let acc_40 = point_add_and_double (init_38) (acc_40) in
              (acc_40)
          in
          (acc_40))
      (acc_40)
  in
  let out_42, _ = acc_40 in
  out_42

let x25519_scalarmult (s_43: x25519_serialized_scalar_t) (p_44: x25519_serialized_point_t)
    : x25519_serialized_point_t =
  let s_45 = decode_scalar (s_43) in
  let p_46 = decode_point (p_44) in
  let r_47 = montgomery_ladder (s_45) (p_46) in
  encode_point (r_47)

let x25519_secret_to_public (s_48: x25519_serialized_scalar_t) : x25519_serialized_point_t =
  let base_49 = array_new_ (secret (pub_u8 0x0)) (32) in
  let base_49 = array_upd base_49 (usize 0) (secret (pub_u8 0x9)) in
  x25519_scalarmult (s_48) (base_49)

