Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Lib.

Definition field_canvas := nseq (int8) (32).
Definition field_element :=
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Definition scalar_canvas := nseq (int8) (32).
Definition scalar :=
  nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000.

Notation "'point'" := ((field_element × field_element)) : hacspec_scope.

Definition serialized_point := nseq (uint8) (usize 32).

Definition serialized_scalar := nseq (uint8) (usize 32).

Definition mask_scalar (s_0 : serialized_scalar) : serialized_scalar :=
  let k_1 :=
    s_0 in 
  let k_1 :=
    array_upd k_1 (usize 0) (
      (array_index (k_1) (usize 0)) .& (secret (repr 248))) in 
  let k_1 :=
    array_upd k_1 (usize 31) (
      (array_index (k_1) (usize 31)) .& (secret (repr 127))) in 
  let k_1 :=
    array_upd k_1 (usize 31) (
      (array_index (k_1) (usize 31)) .| (secret (repr 64))) in 
  k_1.

Definition decode_scalar (s_2 : serialized_scalar) : scalar :=
  let k_3 :=
    mask_scalar (s_2) in 
  nat_mod_from_byte_seq_le (k_3).

Definition decode_point (u_4 : serialized_point) : point :=
  let u_5 :=
    u_4 in 
  let u_5 :=
    array_upd u_5 (usize 31) (
      (array_index (u_5) (usize 31)) .& (secret (repr 127))) in 
  (
    nat_mod_from_byte_seq_le (u_5),
    nat_mod_from_literal (
      0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
      repr 1)
  ).

Definition encode_point (p_6 : point) : serialized_point :=
  let '(x_7, y_8) :=
    p_6 in 
  let b_9 :=
    (x_7) *% (nat_mod_inv (y_8)) in 
  array_update_start (array_new_ (secret (repr 0)) (32)) (
    nat_mod_to_byte_seq_le (b_9)).

Definition point_add_and_double
  (q_10 : point)
  (np_11 : (point × point))
  : (point × point) :=
  let '(nq_12, nqp1_13) :=
    np_11 in 
  let '(x_1_14, z_1_15) :=
    q_10 in 
  let '(x_2_16, z_2_17) :=
    nq_12 in 
  let '(x_3_18, z_3_19) :=
    nqp1_13 in 
  let a_20 :=
    (x_2_16) +% (z_2_17) in 
  let aa_21 :=
    nat_mod_pow (a_20) (repr 2) in 
  let b_22 :=
    (x_2_16) -% (z_2_17) in 
  let bb_23 :=
    (b_22) *% (b_22) in 
  let e_24 :=
    (aa_21) -% (bb_23) in 
  let c_25 :=
    (x_3_18) +% (z_3_19) in 
  let d_26 :=
    (x_3_18) -% (z_3_19) in 
  let da_27 :=
    (d_26) *% (a_20) in 
  let cb_28 :=
    (c_25) *% (b_22) in 
  let x_3_29 :=
    nat_mod_pow ((da_27) +% (cb_28)) (repr 2) in 
  let z_3_30 :=
    (x_1_14) *% (nat_mod_pow ((da_27) -% (cb_28)) (repr 2)) in 
  let x_2_31 :=
    (aa_21) *% (bb_23) in 
  let e121665_32 :=
    nat_mod_from_literal (
      0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
      repr 121665) in 
  let z_2_33 :=
    (e_24) *% ((aa_21) +% ((e121665_32) *% (e_24))) in 
  ((x_2_31, z_2_33), (x_3_29, z_3_30)).

Definition swap (x_34 : (point × point)) : (point × point) :=
  let '(x0_35, x1_36) :=
    x_34 in 
  (x1_36, x0_35).

Definition montgomery_ladder (k_37 : scalar) (init_38 : point) : point :=
  let inf_39 :=
    (
      nat_mod_from_literal (
        0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
        repr 1),
      nat_mod_from_literal (
        0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
        repr 0)
    ) in 
  let acc_40 : (point × point) :=
    (inf_39, init_38) in 
  let acc_40 :=
    foldi (usize 0) (usize 256) (fun i_41 acc_40 =>
      let '(acc_40) :=
        if nat_mod_bit (k_37) ((usize 255) - (i_41)):bool then (
          let acc_40 :=
            swap (acc_40) in 
          let acc_40 :=
            point_add_and_double (init_38) (acc_40) in 
          let acc_40 :=
            swap (acc_40) in 
          (acc_40)
        ) else (
          let acc_40 :=
            point_add_and_double (init_38) (acc_40) in 
          (acc_40)
        ) in 
      (acc_40))
    acc_40 in 
  let '(out_42, _) :=
    acc_40 in 
  out_42.

Definition scalarmult
  (s_43 : serialized_scalar)
  (p_44 : serialized_point)
  : serialized_point :=
  let s_45 :=
    decode_scalar (s_43) in 
  let p_46 :=
    decode_point (p_44) in 
  let r_47 :=
    montgomery_ladder (s_45) (p_46) in 
  encode_point (r_47).

Definition secret_to_public (s_48 : serialized_scalar) : serialized_point :=
  let base_49 :=
    array_new_ (secret (repr 0)) (32) in 
  let base_49 :=
    array_upd base_49 (usize 0) (secret (repr 9)) in 
  scalarmult (s_48) (base_49).

