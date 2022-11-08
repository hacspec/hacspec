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

Definition is_negative (x_2043 : ed25519_field_element_t) : uint8 :=
  (if (nat_mod_bit (x_2043) (usize 0)):bool then (secret (
        @repr WORDSIZE8 1) : int8) else (secret (@repr WORDSIZE8 0) : int8)).

Definition compress (p_2044 : ed_point_t) : compressed_ed_point_t :=
  let '(x_2045, y_2046, z_2047, _) :=
    p_2044 in 
  let z_inv_2048 : ed25519_field_element_t :=
    nat_mod_inv (z_2047) in 
  let x_2049 : ed25519_field_element_t :=
    (x_2045) *% (z_inv_2048) in 
  let y_2050 : ed25519_field_element_t :=
    (y_2046) *% (z_inv_2048) in 
  let s_2051 : byte_seq :=
    nat_mod_to_byte_seq_le (y_2050) in 
  let s_2051 :=
    seq_upd s_2051 (usize 31) ((seq_index (s_2051) (usize 31)) .^ ((
          is_negative (x_2049)) shift_left (usize 7))) in 
  array_from_slice (default) (32) (s_2051) (usize 0) (usize 32).

Definition sqrt
  (a_2052 : ed25519_field_element_t)
  : (option ed25519_field_element_t) :=
  let p3_8_2053 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_p3_8_v)) : ed25519_field_element_t in 
  let p1_4_2054 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_p1_4_v)) : ed25519_field_element_t in 
  let x_c_2055 : ed25519_field_element_t :=
    nat_mod_pow_self (a_2052) (p3_8_2053) in 
  let result_2056 : (option ed25519_field_element_t) :=
    @None ed25519_field_element_t in 
  let '(result_2056) :=
    if ((x_c_2055) *% (x_c_2055)) =.? (a_2052):bool then (let result_2056 :=
        some (x_c_2055) in 
      (result_2056)) else ((result_2056)) in 
  let '(result_2056) :=
    if ((x_c_2055) *% (x_c_2055)) =.? ((nat_mod_zero ) -% (a_2052)):bool then (
      let x_2057 : ed25519_field_element_t :=
        (nat_mod_pow_self (nat_mod_two ) (p1_4_2054)) *% (x_c_2055) in 
      let result_2056 :=
        some (x_2057) in 
      (result_2056)) else ((result_2056)) in 
  result_2056.

Definition check_canonical_point (x_2058 : compressed_ed_point_t) : bool :=
  let x_2058 :=
    array_upd x_2058 (usize 31) ((array_index (x_2058) (usize 31)) .& (secret (
          @repr WORDSIZE8 127) : int8)) in 
  let x_2059 : big_integer_t :=
    nat_mod_from_byte_seq_le (array_to_seq (x_2058)) : big_integer_t in 
  (x_2059) <.? (nat_mod_from_byte_seq_le (
      array_to_seq (constant_p_v)) : big_integer_t).

Definition decompress (q_2060 : compressed_ed_point_t) : (option ed_point_t) :=
  let d_2061 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_d_v)) : ed25519_field_element_t in 
  let x_s_2062 : uint8 :=
    ((array_index (q_2060) (usize 31)) .& (secret (
          @repr WORDSIZE8 128) : int8)) shift_right (usize 7) in 
  let y_s_2063 : compressed_ed_point_t :=
    q_2060 in 
  let y_s_2063 :=
    array_upd y_s_2063 (usize 31) ((array_index (y_s_2063) (usize 31)) .& (
        secret (@repr WORDSIZE8 127) : int8)) in 
  let 'tt :=
    if negb (check_canonical_point (y_s_2063)):bool then (let _ : ed_point_t :=
        @None ed_point_t in 
      tt) else (tt) in 
  let y_2064 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (y_s_2063)) : ed25519_field_element_t in 
  let z_2065 : ed25519_field_element_t :=
    nat_mod_one  in 
  let yy_2066 : ed25519_field_element_t :=
    (y_2064) *% (y_2064) in 
  let u_2067 : ed25519_field_element_t :=
    (yy_2066) -% (z_2065) in 
  let v_2068 : ed25519_field_element_t :=
    ((d_2061) *% (yy_2066)) +% (z_2065) in 
  let xx_2069 : ed25519_field_element_t :=
    (u_2067) *% (nat_mod_inv (v_2068)) in 
  let x_2070 : ed25519_field_element_t :=
    sqrt (xx_2069) in 
  let x_r_2071 : uint8 :=
    is_negative (x_2070) in 
  let 'tt :=
    if ((x_2070) =.? (nat_mod_zero )) && ((uint8_declassify (x_s_2062)) =.? (
        @repr WORDSIZE8 1)):bool then (let _ : ed_point_t :=
        @None ed_point_t in 
      tt) else (tt) in 
  let '(x_2070) :=
    if (uint8_declassify (x_r_2071)) !=.? (uint8_declassify (
        x_s_2062)):bool then (let x_2070 :=
        (nat_mod_zero ) -% (x_2070) in 
      (x_2070)) else ((x_2070)) in 
  some ((x_2070, y_2064, z_2065, (x_2070) *% (y_2064))).

Definition decompress_non_canonical
  (p_2072 : compressed_ed_point_t)
  : (option ed_point_t) :=
  let d_2073 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_d_v)) : ed25519_field_element_t in 
  let x_s_2074 : uint8 :=
    ((array_index (p_2072) (usize 31)) .& (secret (
          @repr WORDSIZE8 128) : int8)) shift_right (usize 7) in 
  let y_s_2075 : compressed_ed_point_t :=
    p_2072 in 
  let y_s_2075 :=
    array_upd y_s_2075 (usize 31) ((array_index (y_s_2075) (usize 31)) .& (
        secret (@repr WORDSIZE8 127) : int8)) in 
  let y_2076 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (y_s_2075)) : ed25519_field_element_t in 
  let z_2077 : ed25519_field_element_t :=
    nat_mod_one  in 
  let yy_2078 : ed25519_field_element_t :=
    (y_2076) *% (y_2076) in 
  let u_2079 : ed25519_field_element_t :=
    (yy_2078) -% (z_2077) in 
  let v_2080 : ed25519_field_element_t :=
    ((d_2073) *% (yy_2078)) +% (z_2077) in 
  let xx_2081 : ed25519_field_element_t :=
    (u_2079) *% (nat_mod_inv (v_2080)) in 
  let x_2082 : ed25519_field_element_t :=
    sqrt (xx_2081) in 
  let x_r_2083 : uint8 :=
    is_negative (x_2082) in 
  let '(x_2082) :=
    if (uint8_declassify (x_r_2083)) !=.? (uint8_declassify (
        x_s_2074)):bool then (let x_2082 :=
        (nat_mod_zero ) -% (x_2082) in 
      (x_2082)) else ((x_2082)) in 
  some ((x_2082, y_2076, z_2077, (x_2082) *% (y_2076))).

Definition encode (p_2084 : ed_point_t) : byte_seq :=
  let '(x_2085, y_2086, z_2087, _) :=
    p_2084 in 
  let z_inv_2088 : ed25519_field_element_t :=
    nat_mod_inv (z_2087) in 
  let x_2089 : ed25519_field_element_t :=
    (x_2085) *% (z_inv_2088) in 
  let y_2090 : ed25519_field_element_t :=
    (y_2086) *% (z_inv_2088) in 
  let s_2091 : byte_seq :=
    nat_mod_to_byte_seq_le (y_2090) in 
  let s_2091 :=
    seq_upd s_2091 (usize 31) ((seq_index (s_2091) (usize 31)) .^ ((
          is_negative (x_2089)) shift_left (usize 7))) in 
  s_2091.

Definition decode (q_s_2092 : byte_seq) : (option ed_point_t) :=
  let q_2093 : compressed_ed_point_t :=
    array_from_slice (default) (32) (q_s_2092) (usize 0) (usize 32) in 
  decompress (q_2093).

Definition point_add (p_2094 : ed_point_t) (q_2095 : ed_point_t) : ed_point_t :=
  let d_c_2096 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_d_v)) : ed25519_field_element_t in 
  let two_2097 : ed25519_field_element_t :=
    nat_mod_two  in 
  let '(x1_2098, y1_2099, z1_2100, t1_2101) :=
    p_2094 in 
  let '(x2_2102, y2_2103, z2_2104, t2_2105) :=
    q_2095 in 
  let a_2106 : ed25519_field_element_t :=
    ((y1_2099) -% (x1_2098)) *% ((y2_2103) -% (x2_2102)) in 
  let b_2107 : ed25519_field_element_t :=
    ((y1_2099) +% (x1_2098)) *% ((y2_2103) +% (x2_2102)) in 
  let c_2108 : ed25519_field_element_t :=
    (((t1_2101) *% (two_2097)) *% (d_c_2096)) *% (t2_2105) in 
  let d_2109 : ed25519_field_element_t :=
    ((z1_2100) *% (two_2097)) *% (z2_2104) in 
  let e_2110 : ed25519_field_element_t :=
    (b_2107) -% (a_2106) in 
  let f_2111 : ed25519_field_element_t :=
    (d_2109) -% (c_2108) in 
  let g_2112 : ed25519_field_element_t :=
    (d_2109) +% (c_2108) in 
  let h_2113 : ed25519_field_element_t :=
    (b_2107) +% (a_2106) in 
  let x3_2114 : ed25519_field_element_t :=
    (e_2110) *% (f_2111) in 
  let y3_2115 : ed25519_field_element_t :=
    (g_2112) *% (h_2113) in 
  let t3_2116 : ed25519_field_element_t :=
    (e_2110) *% (h_2113) in 
  let z3_2117 : ed25519_field_element_t :=
    (f_2111) *% (g_2112) in 
  (x3_2114, y3_2115, z3_2117, t3_2116).

Definition point_identity  : ed_point_t :=
  (nat_mod_zero , nat_mod_one , nat_mod_one , nat_mod_zero ).

Definition point_mul (s_2118 : scalar_t) (p_2119 : ed_point_t) : ed_point_t :=
  let p_2120 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    p_2119 in 
  let q_2121 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let '(p_2120, q_2121) :=
    foldi (usize 0) (usize 256) (fun i_2122 '(p_2120, q_2121) =>
      let '(q_2121) :=
        if nat_mod_bit (s_2118) (i_2122):bool then (let q_2121 :=
            point_add (q_2121) (p_2120) in 
          (q_2121)) else ((q_2121)) in 
      let p_2120 :=
        point_add (p_2120) (p_2120) in 
      (p_2120, q_2121))
    (p_2120, q_2121) in 
  q_2121.

Definition point_mul_by_cofactor (p_2123 : ed_point_t) : ed_point_t :=
  let p2_2124 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_add (p_2123) (p_2123) in 
  let p4_2125 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_add (p2_2124) (p2_2124) in 
  let p8_2126 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_add (p4_2125) (p4_2125) in 
  p8_2126.

Definition point_neg (p_2127 : ed_point_t) : ed_point_t :=
  let '(x_2128, y_2129, z_2130, t_2131) :=
    p_2127 in 
  ((nat_mod_zero ) -% (x_2128), y_2129, z_2130, (nat_mod_zero ) -% (t_2131)).

Definition point_eq (p_2132 : ed_point_t) (q_2133 : ed_point_t) : bool :=
  let '(x1_2134, y1_2135, z1_2136, _) :=
    p_2132 in 
  let '(x2_2137, y2_2138, z2_2139, _) :=
    q_2133 in 
  (((x1_2134) *% (z2_2139)) =.? ((x2_2137) *% (z1_2136))) && (((y1_2135) *% (
        z2_2139)) =.? ((y2_2138) *% (z1_2136))).

Definition point_normalize (q_2140 : ed_point_t) : ed_point_t :=
  let '(qx_2141, qy_2142, qz_2143, _) :=
    q_2140 in 
  let px_2144 : ed25519_field_element_t :=
    (qx_2141) *% (nat_mod_inv (qz_2143)) in 
  let py_2145 : ed25519_field_element_t :=
    (qy_2142) *% (nat_mod_inv (qz_2143)) in 
  let pz_2146 : ed25519_field_element_t :=
    nat_mod_one  in 
  let pt_2147 : ed25519_field_element_t :=
    (px_2144) *% (py_2145) in 
  (px_2144, py_2145, pz_2146, pt_2147).

Definition secret_expand
  (sk_2148 : secret_key_t)
  : (serialized_scalar_t × serialized_scalar_t) :=
  let h_2149 : sha512_digest_t :=
    sha512 (seq_from_slice (sk_2148) (usize 0) (usize 32)) in 
  let h_d_2150 : serialized_scalar_t :=
    array_from_slice (default) (32) (array_to_seq (h_2149)) (usize 32) (
      usize 32) in 
  let s_2151 : serialized_scalar_t :=
    array_from_slice (default) (32) (array_to_seq (h_2149)) (usize 0) (
      usize 32) in 
  let s_2151 :=
    array_upd s_2151 (usize 0) ((array_index (s_2151) (usize 0)) .& (secret (
          @repr WORDSIZE8 248) : int8)) in 
  let s_2151 :=
    array_upd s_2151 (usize 31) ((array_index (s_2151) (usize 31)) .& (secret (
          @repr WORDSIZE8 127) : int8)) in 
  let s_2151 :=
    array_upd s_2151 (usize 31) ((array_index (s_2151) (usize 31)) .| (secret (
          @repr WORDSIZE8 64) : int8)) in 
  (s_2151, h_d_2150).

Definition secret_to_public (sk_2152 : secret_key_t) : public_key_t :=
  let '(s_2153, _) :=
    secret_expand (sk_2152) in 
  let base_2154 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let ss_2155 : scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (s_2153)) : scalar_t in 
  let a_2156 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul (ss_2155) (base_2154) in 
  compress (a_2156).

Definition check_canonical_scalar (s_2157 : serialized_scalar_t) : bool :=
  (if ((uint8_declassify ((array_index (s_2157) (usize 31)) .& (secret (
              @repr WORDSIZE8 224) : int8))) !=.? (
        @repr WORDSIZE8 0)):bool then (false) else ((nat_mod_from_byte_seq_le (
          array_to_seq (s_2157)) : big_integer_t) <.? (
        nat_mod_from_byte_seq_le (
          array_to_seq (constant_l_v)) : big_integer_t))).

