(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition field_canvas_t := nseq (int8) (32).
Definition x25519_field_element_t :=
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Definition scalar_canvas_t := nseq (int8) (32).
Definition scalar_t :=
  nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000.

Notation "'point_t'" := ((x25519_field_element_t × x25519_field_element_t
)) : hacspec_scope.

Definition x25519_serialized_point_t := nseq (uint8) (usize 32).

Definition x25519_serialized_scalar_t := nseq (uint8) (usize 32).

Definition mask_scalar
  (s_0 : x25519_serialized_scalar_t)
  : x25519_serialized_scalar_t :=
  let k_1 : x25519_serialized_scalar_t :=
    s_0 in 
  let k_1 :=
    array_upd k_1 (usize 0) ((array_index (k_1) (usize 0)) .& (secret (
          @repr WORDSIZE8 248) : int8)) in 
  let k_1 :=
    array_upd k_1 (usize 31) ((array_index (k_1) (usize 31)) .& (secret (
          @repr WORDSIZE8 127) : int8)) in 
  let k_1 :=
    array_upd k_1 (usize 31) ((array_index (k_1) (usize 31)) .| (secret (
          @repr WORDSIZE8 64) : int8)) in 
  k_1.

Definition decode_scalar (s_2 : x25519_serialized_scalar_t) : scalar_t :=
  let k_3 : x25519_serialized_scalar_t :=
    mask_scalar (s_2) in 
  nat_mod_from_byte_seq_le (k_3) : scalar_t.

Definition decode_point (u_4 : x25519_serialized_point_t) : point_t :=
  let u_5 : x25519_serialized_point_t :=
    u_4 in 
  let u_5 :=
    array_upd u_5 (usize 31) ((array_index (u_5) (usize 31)) .& (secret (
          @repr WORDSIZE8 127) : int8)) in 
  (
    nat_mod_from_byte_seq_le (u_5) : x25519_field_element_t,
    nat_mod_from_literal (
      0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
      @repr WORDSIZE128 1) : x25519_field_element_t
  ).

Definition encode_point (p_6 : point_t) : x25519_serialized_point_t :=
  let '(x_7, y_8) :=
    p_6 in 
  let b_9 : x25519_field_element_t :=
    (x_7) *% (nat_mod_inv (y_8)) in 
  array_update_start (array_new_ (default) (32)) (nat_mod_to_byte_seq_le (b_9)).

Definition point_add_and_double
  (q_10 : point_t)
  (np_11 : (point_t × point_t))
  : (point_t × point_t) :=
  let '(nq_12, nqp1_13) :=
    np_11 in 
  let '(x_1_14, z_1_15) :=
    q_10 in 
  let '(x_2_16, z_2_17) :=
    nq_12 in 
  let '(x_3_18, z_3_19) :=
    nqp1_13 in 
  let a_20 : x25519_field_element_t :=
    (x_2_16) +% (z_2_17) in 
  let aa_21 : x25519_field_element_t :=
    nat_mod_pow (a_20) (@repr WORDSIZE128 2) in 
  let b_22 : x25519_field_element_t :=
    (x_2_16) -% (z_2_17) in 
  let bb_23 : x25519_field_element_t :=
    (b_22) *% (b_22) in 
  let e_24 : x25519_field_element_t :=
    (aa_21) -% (bb_23) in 
  let c_25 : x25519_field_element_t :=
    (x_3_18) +% (z_3_19) in 
  let d_26 : x25519_field_element_t :=
    (x_3_18) -% (z_3_19) in 
  let da_27 : x25519_field_element_t :=
    (d_26) *% (a_20) in 
  let cb_28 : x25519_field_element_t :=
    (c_25) *% (b_22) in 
  let x_3_29 : x25519_field_element_t :=
    nat_mod_pow ((da_27) +% (cb_28)) (@repr WORDSIZE128 2) in 
  let z_3_30 : x25519_field_element_t :=
    (x_1_14) *% (nat_mod_pow ((da_27) -% (cb_28)) (@repr WORDSIZE128 2)) in 
  let x_2_31 : x25519_field_element_t :=
    (aa_21) *% (bb_23) in 
  let e121665_32 : x25519_field_element_t :=
    nat_mod_from_literal (
      0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
      @repr WORDSIZE128 121665) : x25519_field_element_t in 
  let z_2_33 : x25519_field_element_t :=
    (e_24) *% ((aa_21) +% ((e121665_32) *% (e_24))) in 
  ((x_2_31, z_2_33), (x_3_29, z_3_30)).

Definition swap (x_34 : (point_t × point_t)) : (point_t × point_t) :=
  let '(x0_35, x1_36) :=
    x_34 in 
  (x1_36, x0_35).

Definition montgomery_ladder (k_37 : scalar_t) (init_38 : point_t) : point_t :=
  let inf_39 : (x25519_field_element_t × x25519_field_element_t) :=
    (
      nat_mod_from_literal (
        0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
        @repr WORDSIZE128 1) : x25519_field_element_t,
      nat_mod_from_literal (
        0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
        @repr WORDSIZE128 0) : x25519_field_element_t
    ) in 
  let acc_40 : (point_t × point_t) :=
    (inf_39, init_38) in 
  let acc_40 :=
    foldi (usize 0) (usize 256) (fun i_41 acc_40 =>
      let '(acc_40) :=
        if nat_mod_bit (k_37) ((usize 255) - (i_41)):bool then (let acc_40 :=
            swap (acc_40) in 
          let acc_40 :=
            point_add_and_double (init_38) (acc_40) in 
          let acc_40 :=
            swap (acc_40) in 
          (acc_40)) else (let acc_40 :=
            point_add_and_double (init_38) (acc_40) in 
          (acc_40)) in 
      (acc_40))
    acc_40 in 
  let '(out_42, _) :=
    acc_40 in 
  out_42.

Definition x25519_scalarmult
  (s_43 : x25519_serialized_scalar_t)
  (p_44 : x25519_serialized_point_t)
  : x25519_serialized_point_t :=
  let s_45 : scalar_t :=
    decode_scalar (s_43) in 
  let p_46 : (x25519_field_element_t × x25519_field_element_t) :=
    decode_point (p_44) in 
  let r_47 : (x25519_field_element_t × x25519_field_element_t) :=
    montgomery_ladder (s_45) (p_46) in 
  encode_point (r_47).

Definition x25519_secret_to_public
  (s_48 : x25519_serialized_scalar_t)
  : x25519_serialized_point_t :=
  let base_49 : x25519_serialized_point_t :=
    array_new_ (default) (32) in 
  let base_49 :=
    array_upd base_49 (usize 0) (secret (@repr WORDSIZE8 9) : int8) in 
  x25519_scalarmult (s_48) (base_49).

