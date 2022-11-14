(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
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

Definition is_negative (x_2101 : ed25519_field_element_t) : uint8 :=
  (if (nat_mod_bit (x_2101) (usize 0)):bool then (secret (
        @repr WORDSIZE8 1) : int8) else (secret (@repr WORDSIZE8 0) : int8)).

Definition compress (p_2102 : ed_point_t) : compressed_ed_point_t :=
  let '(x_2103, y_2104, z_2105, _) :=
    p_2102 in 
  let z_inv_2106 : ed25519_field_element_t :=
    nat_mod_inv (z_2105) in 
  let x_2107 : ed25519_field_element_t :=
    (x_2103) *% (z_inv_2106) in 
  let y_2108 : ed25519_field_element_t :=
    (y_2104) *% (z_inv_2106) in 
  let s_2109 : byte_seq :=
    nat_mod_to_byte_seq_le (y_2108) in 
  let s_2109 :=
    seq_upd s_2109 (usize 31) ((seq_index (s_2109) (usize 31)) .^ ((
          is_negative (x_2107)) shift_left (usize 7))) in 
  array_from_slice (default : uint8) (32) (s_2109) (usize 0) (usize 32).

Definition sqrt
  (a_2110 : ed25519_field_element_t)
  : (option ed25519_field_element_t) :=
  let p3_8_2111 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_p3_8_v)) : ed25519_field_element_t in 
  let p1_4_2112 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_p1_4_v)) : ed25519_field_element_t in 
  let x_c_2113 : ed25519_field_element_t :=
    nat_mod_pow_self (a_2110) (p3_8_2111) in 
  let result_2114 : (option ed25519_field_element_t) :=
    @None ed25519_field_element_t in 
  let '(result_2114) :=
    if ((x_c_2113) *% (x_c_2113)) =.? (a_2110):bool then (let result_2114 :=
        some (x_c_2113) in 
      (result_2114)) else ((result_2114)) in 
  let '(result_2114) :=
    if ((x_c_2113) *% (x_c_2113)) =.? ((nat_mod_zero ) -% (a_2110)):bool then (
      let x_2115 : ed25519_field_element_t :=
        (nat_mod_pow_self (nat_mod_two ) (p1_4_2112)) *% (x_c_2113) in 
      let result_2114 :=
        some (x_2115) in 
      (result_2114)) else ((result_2114)) in 
  result_2114.

Definition check_canonical_point (x_2116 : compressed_ed_point_t) : bool :=
  let x_2116 :=
    array_upd x_2116 (usize 31) ((array_index (x_2116) (usize 31)) .& (secret (
          @repr WORDSIZE8 127) : int8)) in 
  let x_2117 : big_integer_t :=
    nat_mod_from_byte_seq_le (array_to_seq (x_2116)) : big_integer_t in 
  (x_2117) <.? (nat_mod_from_byte_seq_le (
      array_to_seq (constant_p_v)) : big_integer_t).

Definition decompress (q_2118 : compressed_ed_point_t) : (option ed_point_t) :=
  let d_2119 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_d_v)) : ed25519_field_element_t in 
  let x_s_2120 : uint8 :=
    ((array_index (q_2118) (usize 31)) .& (secret (
          @repr WORDSIZE8 128) : int8)) shift_right (usize 7) in 
  let y_s_2121 : compressed_ed_point_t :=
    q_2118 in 
  let y_s_2121 :=
    array_upd y_s_2121 (usize 31) ((array_index (y_s_2121) (usize 31)) .& (
        secret (@repr WORDSIZE8 127) : int8)) in 
  let 'tt :=
    if negb (check_canonical_point (y_s_2121)):bool then (let _ : ed_point_t :=
        @None ed_point_t in 
      tt) else (tt) in 
  let y_2122 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (y_s_2121)) : ed25519_field_element_t in 
  let z_2123 : ed25519_field_element_t :=
    nat_mod_one  in 
  let yy_2124 : ed25519_field_element_t :=
    (y_2122) *% (y_2122) in 
  let u_2125 : ed25519_field_element_t :=
    (yy_2124) -% (z_2123) in 
  let v_2126 : ed25519_field_element_t :=
    ((d_2119) *% (yy_2124)) +% (z_2123) in 
  let xx_2127 : ed25519_field_element_t :=
    (u_2125) *% (nat_mod_inv (v_2126)) in 
  let x_2128 : ed25519_field_element_t :=
    sqrt (xx_2127) in 
  let x_r_2129 : uint8 :=
    is_negative (x_2128) in 
  let 'tt :=
    if ((x_2128) =.? (nat_mod_zero )) && ((uint8_declassify (x_s_2120)) =.? (
        @repr WORDSIZE8 1)):bool then (let _ : ed_point_t :=
        @None ed_point_t in 
      tt) else (tt) in 
  let '(x_2128) :=
    if (uint8_declassify (x_r_2129)) !=.? (uint8_declassify (
        x_s_2120)):bool then (let x_2128 :=
        (nat_mod_zero ) -% (x_2128) in 
      (x_2128)) else ((x_2128)) in 
  some ((x_2128, y_2122, z_2123, (x_2128) *% (y_2122))).

Definition decompress_non_canonical
  (p_2130 : compressed_ed_point_t)
  : (option ed_point_t) :=
  let d_2131 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_d_v)) : ed25519_field_element_t in 
  let x_s_2132 : uint8 :=
    ((array_index (p_2130) (usize 31)) .& (secret (
          @repr WORDSIZE8 128) : int8)) shift_right (usize 7) in 
  let y_s_2133 : compressed_ed_point_t :=
    p_2130 in 
  let y_s_2133 :=
    array_upd y_s_2133 (usize 31) ((array_index (y_s_2133) (usize 31)) .& (
        secret (@repr WORDSIZE8 127) : int8)) in 
  let y_2134 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (y_s_2133)) : ed25519_field_element_t in 
  let z_2135 : ed25519_field_element_t :=
    nat_mod_one  in 
  let yy_2136 : ed25519_field_element_t :=
    (y_2134) *% (y_2134) in 
  let u_2137 : ed25519_field_element_t :=
    (yy_2136) -% (z_2135) in 
  let v_2138 : ed25519_field_element_t :=
    ((d_2131) *% (yy_2136)) +% (z_2135) in 
  let xx_2139 : ed25519_field_element_t :=
    (u_2137) *% (nat_mod_inv (v_2138)) in 
  let x_2140 : ed25519_field_element_t :=
    sqrt (xx_2139) in 
  let x_r_2141 : uint8 :=
    is_negative (x_2140) in 
  let '(x_2140) :=
    if (uint8_declassify (x_r_2141)) !=.? (uint8_declassify (
        x_s_2132)):bool then (let x_2140 :=
        (nat_mod_zero ) -% (x_2140) in 
      (x_2140)) else ((x_2140)) in 
  some ((x_2140, y_2134, z_2135, (x_2140) *% (y_2134))).

Definition encode (p_2142 : ed_point_t) : byte_seq :=
  let '(x_2143, y_2144, z_2145, _) :=
    p_2142 in 
  let z_inv_2146 : ed25519_field_element_t :=
    nat_mod_inv (z_2145) in 
  let x_2147 : ed25519_field_element_t :=
    (x_2143) *% (z_inv_2146) in 
  let y_2148 : ed25519_field_element_t :=
    (y_2144) *% (z_inv_2146) in 
  let s_2149 : byte_seq :=
    nat_mod_to_byte_seq_le (y_2148) in 
  let s_2149 :=
    seq_upd s_2149 (usize 31) ((seq_index (s_2149) (usize 31)) .^ ((
          is_negative (x_2147)) shift_left (usize 7))) in 
  s_2149.

Definition decode (q_s_2150 : byte_seq) : (option ed_point_t) :=
  let q_2151 : compressed_ed_point_t :=
    array_from_slice (default : uint8) (32) (q_s_2150) (usize 0) (usize 32) in 
  decompress (q_2151).

Definition point_add (p_2152 : ed_point_t) (q_2153 : ed_point_t) : ed_point_t :=
  let d_c_2154 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_d_v)) : ed25519_field_element_t in 
  let two_2155 : ed25519_field_element_t :=
    nat_mod_two  in 
  let '(x1_2156, y1_2157, z1_2158, t1_2159) :=
    p_2152 in 
  let '(x2_2160, y2_2161, z2_2162, t2_2163) :=
    q_2153 in 
  let a_2164 : ed25519_field_element_t :=
    ((y1_2157) -% (x1_2156)) *% ((y2_2161) -% (x2_2160)) in 
  let b_2165 : ed25519_field_element_t :=
    ((y1_2157) +% (x1_2156)) *% ((y2_2161) +% (x2_2160)) in 
  let c_2166 : ed25519_field_element_t :=
    (((t1_2159) *% (two_2155)) *% (d_c_2154)) *% (t2_2163) in 
  let d_2167 : ed25519_field_element_t :=
    ((z1_2158) *% (two_2155)) *% (z2_2162) in 
  let e_2168 : ed25519_field_element_t :=
    (b_2165) -% (a_2164) in 
  let f_2169 : ed25519_field_element_t :=
    (d_2167) -% (c_2166) in 
  let g_2170 : ed25519_field_element_t :=
    (d_2167) +% (c_2166) in 
  let h_2171 : ed25519_field_element_t :=
    (b_2165) +% (a_2164) in 
  let x3_2172 : ed25519_field_element_t :=
    (e_2168) *% (f_2169) in 
  let y3_2173 : ed25519_field_element_t :=
    (g_2170) *% (h_2171) in 
  let t3_2174 : ed25519_field_element_t :=
    (e_2168) *% (h_2171) in 
  let z3_2175 : ed25519_field_element_t :=
    (f_2169) *% (g_2170) in 
  (x3_2172, y3_2173, z3_2175, t3_2174).

Definition point_identity  : ed_point_t :=
  (nat_mod_zero , nat_mod_one , nat_mod_one , nat_mod_zero ).

Definition point_mul (s_2176 : scalar_t) (p_2177 : ed_point_t) : ed_point_t :=
  let p_2178 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    p_2177 in 
  let q_2179 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let '(p_2178, q_2179) :=
    foldi (usize 0) (usize 256) (fun i_2180 '(p_2178, q_2179) =>
      let '(q_2179) :=
        if nat_mod_bit (s_2176) (i_2180):bool then (let q_2179 :=
            point_add (q_2179) (p_2178) in 
          (q_2179)) else ((q_2179)) in 
      let p_2178 :=
        point_add (p_2178) (p_2178) in 
      (p_2178, q_2179))
    (p_2178, q_2179) in 
  q_2179.

Definition point_mul_by_cofactor (p_2181 : ed_point_t) : ed_point_t :=
  let p2_2182 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_add (p_2181) (p_2181) in 
  let p4_2183 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_add (p2_2182) (p2_2182) in 
  let p8_2184 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_add (p4_2183) (p4_2183) in 
  p8_2184.

Definition point_neg (p_2185 : ed_point_t) : ed_point_t :=
  let '(x_2186, y_2187, z_2188, t_2189) :=
    p_2185 in 
  ((nat_mod_zero ) -% (x_2186), y_2187, z_2188, (nat_mod_zero ) -% (t_2189)).

Definition point_eq (p_2190 : ed_point_t) (q_2191 : ed_point_t) : bool :=
  let '(x1_2192, y1_2193, z1_2194, _) :=
    p_2190 in 
  let '(x2_2195, y2_2196, z2_2197, _) :=
    q_2191 in 
  (((x1_2192) *% (z2_2197)) =.? ((x2_2195) *% (z1_2194))) && (((y1_2193) *% (
        z2_2197)) =.? ((y2_2196) *% (z1_2194))).

Definition point_normalize (q_2198 : ed_point_t) : ed_point_t :=
  let '(qx_2199, qy_2200, qz_2201, _) :=
    q_2198 in 
  let px_2202 : ed25519_field_element_t :=
    (qx_2199) *% (nat_mod_inv (qz_2201)) in 
  let py_2203 : ed25519_field_element_t :=
    (qy_2200) *% (nat_mod_inv (qz_2201)) in 
  let pz_2204 : ed25519_field_element_t :=
    nat_mod_one  in 
  let pt_2205 : ed25519_field_element_t :=
    (px_2202) *% (py_2203) in 
  (px_2202, py_2203, pz_2204, pt_2205).

Definition secret_expand
  (sk_2206 : secret_key_t)
  : (serialized_scalar_t × serialized_scalar_t) :=
  let h_2207 : sha512_digest_t :=
    sha512 (seq_from_slice (sk_2206) (usize 0) (usize 32)) in 
  let h_d_2208 : serialized_scalar_t :=
    array_from_slice (default : uint8) (32) (array_to_seq (h_2207)) (usize 32) (
      usize 32) in 
  let s_2209 : serialized_scalar_t :=
    array_from_slice (default : uint8) (32) (array_to_seq (h_2207)) (usize 0) (
      usize 32) in 
  let s_2209 :=
    array_upd s_2209 (usize 0) ((array_index (s_2209) (usize 0)) .& (secret (
          @repr WORDSIZE8 248) : int8)) in 
  let s_2209 :=
    array_upd s_2209 (usize 31) ((array_index (s_2209) (usize 31)) .& (secret (
          @repr WORDSIZE8 127) : int8)) in 
  let s_2209 :=
    array_upd s_2209 (usize 31) ((array_index (s_2209) (usize 31)) .| (secret (
          @repr WORDSIZE8 64) : int8)) in 
  (s_2209, h_d_2208).

Definition secret_to_public (sk_2210 : secret_key_t) : public_key_t :=
  let '(s_2211, _) :=
    secret_expand (sk_2210) in 
  let base_2212 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let ss_2213 : scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (s_2211)) : scalar_t in 
  let a_2214 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul (ss_2213) (base_2212) in 
  compress (a_2214).

Definition check_canonical_scalar (s_2215 : serialized_scalar_t) : bool :=
  (if ((uint8_declassify ((array_index (s_2215) (usize 31)) .& (secret (
              @repr WORDSIZE8 224) : int8))) !=.? (
        @repr WORDSIZE8 0)):bool then (false) else ((nat_mod_from_byte_seq_le (
          array_to_seq (s_2215)) : big_integer_t) <.? (
        nat_mod_from_byte_seq_le (
          array_to_seq (constant_l_v)) : big_integer_t))).

