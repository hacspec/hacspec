(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Hacspec_Sha512.

Definition field_canvas_t := nseq (int8) (32).
Definition ed25519_field_element_t :=
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Definition scalar_canvas_t := nseq (int8) (32).
Definition scalar_t :=
  nat_mod 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed.

Definition big_scalar_canvas_t := nseq (int8) (64).
Definition big_scalar_t :=
  nat_mod 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed.

Definition big_integer_canvas_t := nseq (int8) (32).
Definition big_integer_t :=
  nat_mod 0x8000000000000000000000000000000080000000000000000000000000000000.

Notation "'ed_point_t'" := ((
  ed25519_field_element_t ×
  ed25519_field_element_t ×
  ed25519_field_element_t ×
  ed25519_field_element_t
)) : hacspec_scope.

Definition compressed_ed_point_t := nseq (uint8) (usize 32).

Definition serialized_scalar_t := nseq (uint8) (usize 32).

Definition signature_t := nseq (uint8) (usize 64).

Notation "'public_key_t'" := (compressed_ed_point_t) : hacspec_scope.

Notation "'secret_key_t'" := (serialized_scalar_t) : hacspec_scope.

Inductive error_t :=
| InvalidPublickey : error_t
| InvalidSignature : error_t
| InvalidS : error_t
| InvalidR : error_t
| SmallOrderPoint : error_t
| NotEnoughRandomness : error_t.

Notation "'verify_result_t'" := ((result unit error_t)) : hacspec_scope.

Definition base_v : compressed_ed_point_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 88) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8
      ] in  l).

Definition constant_p_v : serialized_scalar_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 237) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 127) : int8
      ] in  l).

Definition constant_l_v : serialized_scalar_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 237) : int8;
        secret (@repr WORDSIZE8 211) : int8;
        secret (@repr WORDSIZE8 245) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 26) : int8;
        secret (@repr WORDSIZE8 99) : int8;
        secret (@repr WORDSIZE8 18) : int8;
        secret (@repr WORDSIZE8 88) : int8;
        secret (@repr WORDSIZE8 214) : int8;
        secret (@repr WORDSIZE8 156) : int8;
        secret (@repr WORDSIZE8 247) : int8;
        secret (@repr WORDSIZE8 162) : int8;
        secret (@repr WORDSIZE8 222) : int8;
        secret (@repr WORDSIZE8 249) : int8;
        secret (@repr WORDSIZE8 222) : int8;
        secret (@repr WORDSIZE8 20) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 16) : int8
      ] in  l).

Definition constant_p3_8_v : serialized_scalar_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 254) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 15) : int8
      ] in  l).

Definition constant_p1_4_v : serialized_scalar_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 251) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 31) : int8
      ] in  l).

Definition constant_d_v : serialized_scalar_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 163) : int8;
        secret (@repr WORDSIZE8 120) : int8;
        secret (@repr WORDSIZE8 89) : int8;
        secret (@repr WORDSIZE8 19) : int8;
        secret (@repr WORDSIZE8 202) : int8;
        secret (@repr WORDSIZE8 77) : int8;
        secret (@repr WORDSIZE8 235) : int8;
        secret (@repr WORDSIZE8 117) : int8;
        secret (@repr WORDSIZE8 171) : int8;
        secret (@repr WORDSIZE8 216) : int8;
        secret (@repr WORDSIZE8 65) : int8;
        secret (@repr WORDSIZE8 65) : int8;
        secret (@repr WORDSIZE8 77) : int8;
        secret (@repr WORDSIZE8 10) : int8;
        secret (@repr WORDSIZE8 112) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 152) : int8;
        secret (@repr WORDSIZE8 232) : int8;
        secret (@repr WORDSIZE8 121) : int8;
        secret (@repr WORDSIZE8 119) : int8;
        secret (@repr WORDSIZE8 121) : int8;
        secret (@repr WORDSIZE8 64) : int8;
        secret (@repr WORDSIZE8 199) : int8;
        secret (@repr WORDSIZE8 140) : int8;
        secret (@repr WORDSIZE8 115) : int8;
        secret (@repr WORDSIZE8 254) : int8;
        secret (@repr WORDSIZE8 111) : int8;
        secret (@repr WORDSIZE8 43) : int8;
        secret (@repr WORDSIZE8 238) : int8;
        secret (@repr WORDSIZE8 108) : int8;
        secret (@repr WORDSIZE8 3) : int8;
        secret (@repr WORDSIZE8 82) : int8
      ] in  l).

Definition is_negative (x_1635 : ed25519_field_element_t) : uint8 :=
  (if (nat_mod_bit (x_1635) (usize 0)):bool then (secret (
        @repr WORDSIZE8 1) : int8) else (secret (@repr WORDSIZE8 0) : int8)).

Definition compress (p_1636 : ed_point_t) : compressed_ed_point_t :=
  let '(x_1637, y_1638, z_1639, _) :=
    p_1636 in 
  let z_inv_1640 : ed25519_field_element_t :=
    nat_mod_inv (z_1639) in 
  let x_1641 : ed25519_field_element_t :=
    (x_1637) *% (z_inv_1640) in 
  let y_1642 : ed25519_field_element_t :=
    (y_1638) *% (z_inv_1640) in 
  let s_1643 : byte_seq :=
    nat_mod_to_byte_seq_le (y_1642) in 
  let s_1643 :=
    seq_upd s_1643 (usize 31) ((seq_index (s_1643) (usize 31)) .^ ((
          is_negative (x_1641)) shift_left (usize 7))) in 
  array_from_slice (default) (32) (s_1643) (usize 0) (usize 32).

Definition sqrt
  (a_1644 : ed25519_field_element_t)
  : (option ed25519_field_element_t) :=
  let p3_8_1645 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_p3_8_v)) : ed25519_field_element_t in 
  let p1_4_1646 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_p1_4_v)) : ed25519_field_element_t in 
  let x_c_1647 : ed25519_field_element_t :=
    nat_mod_pow_self (a_1644) (p3_8_1645) in 
  let result_1648 : (option ed25519_field_element_t) :=
    @None ed25519_field_element_t in 
  let '(result_1648) :=
    if ((x_c_1647) *% (x_c_1647)) =.? (a_1644):bool then (let result_1648 :=
        some (x_c_1647) in 
      (result_1648)) else ((result_1648)) in 
  let '(result_1648) :=
    if ((x_c_1647) *% (x_c_1647)) =.? ((nat_mod_zero ) -% (a_1644)):bool then (
      let x_1649 : ed25519_field_element_t :=
        (nat_mod_pow_self (nat_mod_two ) (p1_4_1646)) *% (x_c_1647) in 
      let result_1648 :=
        some (x_1649) in 
      (result_1648)) else ((result_1648)) in 
  result_1648.

Definition check_canonical_point (x_1650 : compressed_ed_point_t) : bool :=
  let x_1650 :=
    array_upd x_1650 (usize 31) ((array_index (x_1650) (usize 31)) .& (secret (
          @repr WORDSIZE8 127) : int8)) in 
  let x_1651 : big_integer_t :=
    nat_mod_from_byte_seq_le (array_to_seq (x_1650)) : big_integer_t in 
  (x_1651) <.? (nat_mod_from_byte_seq_le (
      array_to_seq (constant_p_v)) : big_integer_t).

Definition decompress (q_1652 : compressed_ed_point_t) : (option ed_point_t) :=
  let d_1653 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_d_v)) : ed25519_field_element_t in 
  let x_s_1654 : uint8 :=
    ((array_index (q_1652) (usize 31)) .& (secret (
          @repr WORDSIZE8 128) : int8)) shift_right (usize 7) in 
  let y_s_1655 : compressed_ed_point_t :=
    q_1652 in 
  let y_s_1655 :=
    array_upd y_s_1655 (usize 31) ((array_index (y_s_1655) (usize 31)) .& (
        secret (@repr WORDSIZE8 127) : int8)) in 
  ifbnd negb (check_canonical_point (y_s_1655)) : bool
  thenbnd (bind (@None ed_point_t) (fun _ => Some (tt)))
  else (tt) >> (fun 'tt =>
  let y_1656 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (y_s_1655)) : ed25519_field_element_t in 
  let z_1657 : ed25519_field_element_t :=
    nat_mod_one  in 
  let yy_1658 : ed25519_field_element_t :=
    (y_1656) *% (y_1656) in 
  let u_1659 : ed25519_field_element_t :=
    (yy_1658) -% (z_1657) in 
  let v_1660 : ed25519_field_element_t :=
    ((d_1653) *% (yy_1658)) +% (z_1657) in 
  let xx_1661 : ed25519_field_element_t :=
    (u_1659) *% (nat_mod_inv (v_1660)) in 
  bind (sqrt (xx_1661)) (fun x_1662 => let x_r_1663 : uint8 :=
      is_negative (x_1662) in 
    ifbnd ((x_1662) =.? (nat_mod_zero )) && ((uint8_declassify (x_s_1654)) =.? (
        @repr WORDSIZE8 1)) : bool
    thenbnd (bind (@None ed_point_t) (fun _ => Some (tt)))
    else (tt) >> (fun 'tt =>
    let '(x_1662) :=
      if (uint8_declassify (x_r_1663)) !=.? (uint8_declassify (
          x_s_1654)):bool then (let x_1662 :=
          (nat_mod_zero ) -% (x_1662) in 
        (x_1662)) else ((x_1662)) in 
    some ((x_1662, y_1656, z_1657, (x_1662) *% (y_1656)))))).

Definition decompress_non_canonical
  (p_1664 : compressed_ed_point_t)
  : (option ed_point_t) :=
  let d_1665 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_d_v)) : ed25519_field_element_t in 
  let x_s_1666 : uint8 :=
    ((array_index (p_1664) (usize 31)) .& (secret (
          @repr WORDSIZE8 128) : int8)) shift_right (usize 7) in 
  let y_s_1667 : compressed_ed_point_t :=
    p_1664 in 
  let y_s_1667 :=
    array_upd y_s_1667 (usize 31) ((array_index (y_s_1667) (usize 31)) .& (
        secret (@repr WORDSIZE8 127) : int8)) in 
  let y_1668 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (y_s_1667)) : ed25519_field_element_t in 
  let z_1669 : ed25519_field_element_t :=
    nat_mod_one  in 
  let yy_1670 : ed25519_field_element_t :=
    (y_1668) *% (y_1668) in 
  let u_1671 : ed25519_field_element_t :=
    (yy_1670) -% (z_1669) in 
  let v_1672 : ed25519_field_element_t :=
    ((d_1665) *% (yy_1670)) +% (z_1669) in 
  let xx_1673 : ed25519_field_element_t :=
    (u_1671) *% (nat_mod_inv (v_1672)) in 
  bind (sqrt (xx_1673)) (fun x_1674 => let x_r_1675 : uint8 :=
      is_negative (x_1674) in 
    let '(x_1674) :=
      if (uint8_declassify (x_r_1675)) !=.? (uint8_declassify (
          x_s_1666)):bool then (let x_1674 :=
          (nat_mod_zero ) -% (x_1674) in 
        (x_1674)) else ((x_1674)) in 
    some ((x_1674, y_1668, z_1669, (x_1674) *% (y_1668)))).

Definition point_add (p_1676 : ed_point_t) (q_1677 : ed_point_t) : ed_point_t :=
  let d_c_1678 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_d_v)) : ed25519_field_element_t in 
  let two_1679 : ed25519_field_element_t :=
    nat_mod_two  in 
  let '(x1_1680, y1_1681, z1_1682, t1_1683) :=
    p_1676 in 
  let '(x2_1684, y2_1685, z2_1686, t2_1687) :=
    q_1677 in 
  let a_1688 : ed25519_field_element_t :=
    ((y1_1681) -% (x1_1680)) *% ((y2_1685) -% (x2_1684)) in 
  let b_1689 : ed25519_field_element_t :=
    ((y1_1681) +% (x1_1680)) *% ((y2_1685) +% (x2_1684)) in 
  let c_1690 : ed25519_field_element_t :=
    (((t1_1683) *% (two_1679)) *% (d_c_1678)) *% (t2_1687) in 
  let d_1691 : ed25519_field_element_t :=
    ((z1_1682) *% (two_1679)) *% (z2_1686) in 
  let e_1692 : ed25519_field_element_t :=
    (b_1689) -% (a_1688) in 
  let f_1693 : ed25519_field_element_t :=
    (d_1691) -% (c_1690) in 
  let g_1694 : ed25519_field_element_t :=
    (d_1691) +% (c_1690) in 
  let h_1695 : ed25519_field_element_t :=
    (b_1689) +% (a_1688) in 
  let x3_1696 : ed25519_field_element_t :=
    (e_1692) *% (f_1693) in 
  let y3_1697 : ed25519_field_element_t :=
    (g_1694) *% (h_1695) in 
  let t3_1698 : ed25519_field_element_t :=
    (e_1692) *% (h_1695) in 
  let z3_1699 : ed25519_field_element_t :=
    (f_1693) *% (g_1694) in 
  (x3_1696, y3_1697, z3_1699, t3_1698).

Definition point_identity  : ed_point_t :=
  (nat_mod_zero , nat_mod_one , nat_mod_one , nat_mod_zero ).

Definition point_mul (s_1700 : scalar_t) (p_1701 : ed_point_t) : ed_point_t :=
  let p_1702 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    p_1701 in 
  let q_1703 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let '(p_1702, q_1703) :=
    foldi (usize 0) (usize 256) (fun i_1704 '(p_1702, q_1703) =>
      let '(q_1703) :=
        if nat_mod_bit (s_1700) (i_1704):bool then (let q_1703 :=
            point_add (q_1703) (p_1702) in 
          (q_1703)) else ((q_1703)) in 
      let p_1702 :=
        point_add (p_1702) (p_1702) in 
      (p_1702, q_1703))
    (p_1702, q_1703) in 
  q_1703.

Definition point_mul_by_cofactor (p_1705 : ed_point_t) : ed_point_t :=
  let p2_1706 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_add (p_1705) (p_1705) in 
  let p4_1707 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_add (p2_1706) (p2_1706) in 
  let p8_1708 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_add (p4_1707) (p4_1707) in 
  p8_1708.

Definition point_neg (p_1709 : ed_point_t) : ed_point_t :=
  let '(x_1710, y_1711, z_1712, t_1713) :=
    p_1709 in 
  ((nat_mod_zero ) -% (x_1710), y_1711, z_1712, (nat_mod_zero ) -% (t_1713)).

Definition point_eq (p_1714 : ed_point_t) (q_1715 : ed_point_t) : bool :=
  let '(x1_1716, y1_1717, z1_1718, _) :=
    p_1714 in 
  let '(x2_1719, y2_1720, z2_1721, _) :=
    q_1715 in 
  (((x1_1716) *% (z2_1721)) =.? ((x2_1719) *% (z1_1718))) && (((y1_1717) *% (
        z2_1721)) =.? ((y2_1720) *% (z1_1718))).

Definition secret_expand
  (sk_1722 : secret_key_t)
  : (serialized_scalar_t × serialized_scalar_t) :=
  let h_1723 : sha512_digest_t :=
    sha512 (seq_from_slice (sk_1722) (usize 0) (usize 32)) in 
  let h_d_1724 : serialized_scalar_t :=
    array_from_slice (default) (32) (array_to_seq (h_1723)) (usize 32) (
      usize 32) in 
  let s_1725 : serialized_scalar_t :=
    array_from_slice (default) (32) (array_to_seq (h_1723)) (usize 0) (
      usize 32) in 
  let s_1725 :=
    array_upd s_1725 (usize 0) ((array_index (s_1725) (usize 0)) .& (secret (
          @repr WORDSIZE8 248) : int8)) in 
  let s_1725 :=
    array_upd s_1725 (usize 31) ((array_index (s_1725) (usize 31)) .& (secret (
          @repr WORDSIZE8 127) : int8)) in 
  let s_1725 :=
    array_upd s_1725 (usize 31) ((array_index (s_1725) (usize 31)) .| (secret (
          @repr WORDSIZE8 64) : int8)) in 
  (s_1725, h_d_1724).

Definition secret_to_public (sk_1726 : secret_key_t) : public_key_t :=
  let '(s_1727, _) :=
    secret_expand (sk_1726) in 
  let base_1728 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let ss_1729 : scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (s_1727)) : scalar_t in 
  let a_1730 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul (ss_1729) (base_1728) in 
  compress (a_1730).

Definition check_canonical_scalar (s_1731 : serialized_scalar_t) : bool :=
  (if ((uint8_declassify ((array_index (s_1731) (usize 31)) .& (secret (
              @repr WORDSIZE8 224) : int8))) !=.? (
        @repr WORDSIZE8 0)):bool then (false) else ((nat_mod_from_byte_seq_le (
          array_to_seq (s_1731)) : big_integer_t) <.? (
        nat_mod_from_byte_seq_le (
          array_to_seq (constant_l_v)) : big_integer_t))).

Definition scalar_from_hash (h_1732 : sha512_digest_t) : scalar_t :=
  let s_1733 : big_scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (h_1732)) : big_scalar_t in 
  nat_mod_from_byte_seq_le (seq_slice (nat_mod_to_byte_seq_le (s_1733)) (
      usize 0) (usize 32)) : scalar_t.

Definition sign (sk_1734 : secret_key_t) (msg_1735 : byte_seq) : signature_t :=
  let '(a_1736, prefix_1737) :=
    secret_expand (sk_1734) in 
  let a_1738 : scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (a_1736)) : scalar_t in 
  let b_1739 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let a_p_1740 : compressed_ed_point_t :=
    compress (point_mul (a_1738) (b_1739)) in 
  let r_1741 : scalar_t :=
    scalar_from_hash (sha512 (array_concat (prefix_1737) (msg_1735))) in 
  let r_p_1742 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul (r_1741) (b_1739) in 
  let r_s_1743 : compressed_ed_point_t :=
    compress (r_p_1742) in 
  let h_1744 : scalar_t :=
    scalar_from_hash (sha512 (seq_concat (array_concat (r_s_1743) (
            array_to_seq (a_p_1740))) (msg_1735))) in 
  let s_1745 : scalar_t :=
    (r_1741) +% ((h_1744) *% (a_1738)) in 
  let s_bytes_1746 : seq uint8 :=
    seq_slice (nat_mod_to_byte_seq_le (s_1745)) (usize 0) (usize 32) in 
  array_update (array_update (array_new_ (default) (64)) (usize 0) (
      array_to_seq (r_s_1743))) (usize 32) (s_bytes_1746).

Definition zcash_verify
  (pk_1747 : public_key_t)
  (signature_1748 : signature_t)
  (msg_1749 : byte_seq)
  : verify_result_t :=
  let b_1750 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress_non_canonical (base_v)) in 
  bind (option_ok_or (decompress_non_canonical (pk_1747)) (InvalidPublickey)) (
    fun a_1751 => let r_bytes_1752 : compressed_ed_point_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1748)) (
        usize 0) (usize 32) in 
    let s_bytes_1753 : serialized_scalar_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1748)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_1753)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress_non_canonical (r_bytes_1752)) (InvalidR)) (
      fun r_1754 => let s_1755 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1753)) : scalar_t in 
      let k_1756 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1752) (
                pk_1747)) (msg_1749))) in 
      let sb_1757 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (s_1755) (b_1750)) in 
      let rc_1758 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (r_1754) in 
      let ka_1759 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (k_1756) (a_1751)) in 
      (if (point_eq (sb_1757) (point_add (rc_1758) (ka_1759))):bool then (
          @Ok unit error_t (tt)) else (@Err unit error_t (
            InvalidSignature)))))).

Definition ietf_cofactored_verify
  (pk_1760 : public_key_t)
  (signature_1761 : signature_t)
  (msg_1762 : byte_seq)
  : verify_result_t :=
  let b_1763 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  bind (option_ok_or (decompress (pk_1760)) (InvalidPublickey)) (fun a_1764 =>
    let r_bytes_1765 : compressed_ed_point_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1761)) (
        usize 0) (usize 32) in 
    let s_bytes_1766 : serialized_scalar_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1761)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_1766)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress (r_bytes_1765)) (InvalidR)) (fun r_1767 =>
      let s_1768 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1766)) : scalar_t in 
      let k_1769 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1765) (
                pk_1760)) (msg_1762))) in 
      let sb_1770 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (s_1768) (b_1763)) in 
      let rc_1771 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (r_1767) in 
      let ka_1772 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (k_1769) (a_1764)) in 
      (if (point_eq (sb_1770) (point_add (rc_1771) (ka_1772))):bool then (
          @Ok unit error_t (tt)) else (@Err unit error_t (
            InvalidSignature)))))).

Definition ietf_cofactorless_verify
  (pk_1773 : public_key_t)
  (signature_1774 : signature_t)
  (msg_1775 : byte_seq)
  : verify_result_t :=
  let b_1776 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  bind (option_ok_or (decompress (pk_1773)) (InvalidPublickey)) (fun a_1777 =>
    let r_bytes_1778 : compressed_ed_point_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1774)) (
        usize 0) (usize 32) in 
    let s_bytes_1779 : serialized_scalar_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1774)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_1779)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress (r_bytes_1778)) (InvalidR)) (fun r_1780 =>
      let s_1781 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1779)) : scalar_t in 
      let k_1782 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1778) (
                pk_1773)) (msg_1775))) in 
      let sb_1783 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        point_mul (s_1781) (b_1776) in 
      let ka_1784 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        point_mul (k_1782) (a_1777) in 
      (if (point_eq (sb_1783) (point_add (r_1780) (ka_1784))):bool then (
          @Ok unit error_t (tt)) else (@Err unit error_t (
            InvalidSignature)))))).

Definition is_identity (p_1785 : ed_point_t) : bool :=
  point_eq (p_1785) (point_identity ).

Definition alg2_verify
  (pk_1786 : public_key_t)
  (signature_1787 : signature_t)
  (msg_1788 : byte_seq)
  : verify_result_t :=
  let b_1789 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  bind (option_ok_or (decompress (pk_1786)) (InvalidPublickey)) (fun a_1790 =>
    ifbnd is_identity (point_mul_by_cofactor (a_1790)) : bool
    thenbnd (bind (@Err unit error_t (SmallOrderPoint)) (fun _ => Ok (tt)))
    else (tt) >> (fun 'tt =>
    let r_bytes_1791 : compressed_ed_point_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1787)) (
        usize 0) (usize 32) in 
    let s_bytes_1792 : serialized_scalar_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1787)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_1792)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress (r_bytes_1791)) (InvalidR)) (fun r_1793 =>
      let s_1794 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1792)) : scalar_t in 
      let k_1795 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1791) (
                pk_1786)) (msg_1788))) in 
      let sb_1796 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (s_1794) (b_1789)) in 
      let rc_1797 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (r_1793) in 
      let ka_1798 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (k_1795) (a_1790)) in 
      (if (point_eq (sb_1796) (point_add (rc_1797) (ka_1798))):bool then (
          @Ok unit error_t (tt)) else (@Err unit error_t (
            InvalidSignature))))))).

Inductive batch_entry_t :=
| BatchEntry : (public_key_t × byte_seq × signature_t) -> batch_entry_t.

Definition zcash_batch_verify
  (entries_1799 : seq batch_entry_t)
  (entropy_1800 : byte_seq)
  : verify_result_t :=
  ifbnd (seq_len (entropy_1800)) <.? ((usize 16) * (seq_len (
        entries_1799))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_1801 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_1802 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_1803 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  bind (foldibnd (usize 0) to (seq_len (entries_1799)) for (
      s_sum_1801,
      r_sum_1802,
      a_sum_1803
    ) >> (fun i_1804 '(s_sum_1801, r_sum_1802, a_sum_1803) =>
    let 'BatchEntry ((pk_1805, msg_1806, signature_1807)) :=
      (seq_index (entries_1799) (i_1804)) in 
    bind (option_ok_or (decompress_non_canonical (pk_1805)) (
        InvalidPublickey)) (fun a_1808 =>
      let r_bytes_1809 : compressed_ed_point_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1807)) (
          usize 0) (usize 32) in 
      let s_bytes_1810 : serialized_scalar_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1807)) (
          usize 32) (usize 32) in 
      ifbnd negb (check_canonical_scalar (s_bytes_1810)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress_non_canonical (r_bytes_1809)) (InvalidR)) (
        fun r_1811 => let s_1812 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1810)) : scalar_t in 
        let c_1813 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1809) (
                  array_to_seq (pk_1805))) (msg_1806))) in 
        let z_1814 : seq uint8 :=
          seq_slice (entropy_1800) ((usize 16) * (i_1804)) (usize 16) in 
        let z_1815 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_1814) (seq_new_ (default) (
                usize 16))) : scalar_t in 
        let s_sum_1801 :=
          (s_sum_1801) +% ((s_1812) *% (z_1815)) in 
        let r_sum_1802 :=
          point_add (r_sum_1802) (point_mul (z_1815) (r_1811)) in 
        let a_sum_1803 :=
          point_add (a_sum_1803) (point_mul ((z_1815) *% (c_1813)) (a_1808)) in 
        Ok ((s_sum_1801, r_sum_1802, a_sum_1803))))))) (fun '(
      s_sum_1801,
      r_sum_1802,
      a_sum_1803
    ) => let b_1816 : (
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      option_unwrap (decompress (base_v)) in 
    let sb_1817 : (
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      point_mul (s_sum_1801) (b_1816) in 
    let check_1818 : (
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      point_mul_by_cofactor (point_add (point_neg (sb_1817)) (point_add (
            r_sum_1802) (a_sum_1803))) in 
    (if (is_identity (check_1818)):bool then (@Ok unit error_t (tt)) else (
        @Err unit error_t (InvalidSignature))))).

Definition ietf_cofactored_batch_verify
  (entries_1819 : seq batch_entry_t)
  (entropy_1820 : byte_seq)
  : verify_result_t :=
  ifbnd (seq_len (entropy_1820)) <.? ((usize 16) * (seq_len (
        entries_1819))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_1821 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_1822 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_1823 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  bind (foldibnd (usize 0) to (seq_len (entries_1819)) for (
      s_sum_1821,
      r_sum_1822,
      a_sum_1823
    ) >> (fun i_1824 '(s_sum_1821, r_sum_1822, a_sum_1823) =>
    let 'BatchEntry ((pk_1825, msg_1826, signature_1827)) :=
      (seq_index (entries_1819) (i_1824)) in 
    bind (option_ok_or (decompress (pk_1825)) (InvalidPublickey)) (fun a_1828 =>
      let r_bytes_1829 : compressed_ed_point_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1827)) (
          usize 0) (usize 32) in 
      let s_bytes_1830 : serialized_scalar_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1827)) (
          usize 32) (usize 32) in 
      ifbnd negb (check_canonical_scalar (s_bytes_1830)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress (r_bytes_1829)) (InvalidR)) (fun r_1831 =>
        let s_1832 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1830)) : scalar_t in 
        let c_1833 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1829) (
                  array_to_seq (pk_1825))) (msg_1826))) in 
        let z_1834 : seq uint8 :=
          seq_slice (entropy_1820) ((usize 16) * (i_1824)) (usize 16) in 
        let z_1835 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_1834) (seq_new_ (default) (
                usize 16))) : scalar_t in 
        let s_sum_1821 :=
          (s_sum_1821) +% ((s_1832) *% (z_1835)) in 
        let r_sum_1822 :=
          point_add (r_sum_1822) (point_mul (z_1835) (r_1831)) in 
        let a_sum_1823 :=
          point_add (a_sum_1823) (point_mul ((z_1835) *% (c_1833)) (a_1828)) in 
        Ok ((s_sum_1821, r_sum_1822, a_sum_1823))))))) (fun '(
      s_sum_1821,
      r_sum_1822,
      a_sum_1823
    ) => let b_1836 : (
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      option_unwrap (decompress (base_v)) in 
    let sb_1837 : (
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      point_mul (s_sum_1821) (b_1836) in 
    let check_1838 : (
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      point_mul_by_cofactor (point_add (point_neg (sb_1837)) (point_add (
            r_sum_1822) (a_sum_1823))) in 
    (if (is_identity (check_1838)):bool then (@Ok unit error_t (tt)) else (
        @Err unit error_t (InvalidSignature))))).

Definition ietf_cofactorless_batch_verify
  (entries_1839 : seq batch_entry_t)
  (entropy_1840 : byte_seq)
  : verify_result_t :=
  ifbnd (seq_len (entropy_1840)) <.? ((usize 16) * (seq_len (
        entries_1839))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_1841 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_1842 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_1843 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  bind (foldibnd (usize 0) to (seq_len (entries_1839)) for (
      s_sum_1841,
      r_sum_1842,
      a_sum_1843
    ) >> (fun i_1844 '(s_sum_1841, r_sum_1842, a_sum_1843) =>
    let 'BatchEntry ((pk_1845, msg_1846, signature_1847)) :=
      (seq_index (entries_1839) (i_1844)) in 
    bind (option_ok_or (decompress (pk_1845)) (InvalidPublickey)) (fun a_1848 =>
      let r_bytes_1849 : compressed_ed_point_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1847)) (
          usize 0) (usize 32) in 
      let s_bytes_1850 : serialized_scalar_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1847)) (
          usize 32) (usize 32) in 
      ifbnd negb (check_canonical_scalar (s_bytes_1850)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress (r_bytes_1849)) (InvalidR)) (fun r_1851 =>
        let s_1852 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1850)) : scalar_t in 
        let c_1853 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1849) (
                  array_to_seq (pk_1845))) (msg_1846))) in 
        let z_1854 : seq uint8 :=
          seq_slice (entropy_1840) ((usize 16) * (i_1844)) (usize 16) in 
        let z_1855 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_1854) (seq_new_ (default) (
                usize 16))) : scalar_t in 
        let s_sum_1841 :=
          (s_sum_1841) +% ((s_1852) *% (z_1855)) in 
        let r_sum_1842 :=
          point_add (r_sum_1842) (point_mul (z_1855) (r_1851)) in 
        let a_sum_1843 :=
          point_add (a_sum_1843) (point_mul ((z_1855) *% (c_1853)) (a_1848)) in 
        Ok ((s_sum_1841, r_sum_1842, a_sum_1843))))))) (fun '(
      s_sum_1841,
      r_sum_1842,
      a_sum_1843
    ) => let b_1856 : (
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      option_unwrap (decompress (base_v)) in 
    let sb_1857 : (
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      point_mul (s_sum_1841) (b_1856) in 
    let check_1858 : (
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      point_add (point_neg (sb_1857)) (point_add (r_sum_1842) (a_sum_1843)) in 
    (if (is_identity (check_1858)):bool then (@Ok unit error_t (tt)) else (
        @Err unit error_t (InvalidSignature))))).

Definition alg3_batch_verify
  (entries_1859 : seq batch_entry_t)
  (entropy_1860 : byte_seq)
  : verify_result_t :=
  ifbnd (seq_len (entropy_1860)) <.? ((usize 16) * (seq_len (
        entries_1859))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_1861 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_1862 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_1863 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  bind (foldibnd (usize 0) to (seq_len (entries_1859)) for (
      s_sum_1861,
      r_sum_1862,
      a_sum_1863
    ) >> (fun i_1864 '(s_sum_1861, r_sum_1862, a_sum_1863) =>
    let 'BatchEntry ((pk_1865, msg_1866, signature_1867)) :=
      (seq_index (entries_1859) (i_1864)) in 
    bind (option_ok_or (decompress (pk_1865)) (InvalidPublickey)) (fun a_1868 =>
      ifbnd is_identity (point_mul_by_cofactor (a_1868)) : bool
      thenbnd (bind (@Err unit error_t (SmallOrderPoint)) (fun _ => Ok (tt)))
      else (tt) >> (fun 'tt =>
      let r_bytes_1869 : compressed_ed_point_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1867)) (
          usize 0) (usize 32) in 
      let s_bytes_1870 : serialized_scalar_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1867)) (
          usize 32) (usize 32) in 
      ifbnd negb (check_canonical_scalar (s_bytes_1870)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress (r_bytes_1869)) (InvalidR)) (fun r_1871 =>
        let s_1872 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1870)) : scalar_t in 
        let c_1873 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1869) (
                  array_to_seq (pk_1865))) (msg_1866))) in 
        let z_1874 : seq uint8 :=
          seq_slice (entropy_1860) ((usize 16) * (i_1864)) (usize 16) in 
        let z_1875 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_1874) (seq_new_ (default) (
                usize 16))) : scalar_t in 
        let s_sum_1861 :=
          (s_sum_1861) +% ((s_1872) *% (z_1875)) in 
        let r_sum_1862 :=
          point_add (r_sum_1862) (point_mul (z_1875) (r_1871)) in 
        let a_sum_1863 :=
          point_add (a_sum_1863) (point_mul ((z_1875) *% (c_1873)) (a_1868)) in 
        Ok ((s_sum_1861, r_sum_1862, a_sum_1863)))))))) (fun '(
      s_sum_1861,
      r_sum_1862,
      a_sum_1863
    ) => let b_1876 : (
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      option_unwrap (decompress (base_v)) in 
    let sb_1877 : (
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      point_mul (s_sum_1861) (b_1876) in 
    let check_1878 : (
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      point_mul_by_cofactor (point_add (point_neg (sb_1877)) (point_add (
            r_sum_1862) (a_sum_1863))) in 
    (if (is_identity (check_1878)):bool then (@Ok unit error_t (tt)) else (
        @Err unit error_t (InvalidSignature))))).

