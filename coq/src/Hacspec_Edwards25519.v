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
  ed25519_field_element_t '×
  ed25519_field_element_t '×
  ed25519_field_element_t '×
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

Definition is_negative (x_2228 : ed25519_field_element_t)  : uint8 :=
  (if (nat_mod_bit (x_2228) (usize 0)):bool then (secret (
        @repr WORDSIZE8 1) : int8) else (secret (@repr WORDSIZE8 0) : int8)).

Definition compress (p_2229 : ed_point_t)  : compressed_ed_point_t :=
  let '(x_2230, y_2231, z_2232, _) :=
    p_2229 in 
  let z_inv_2233 : ed25519_field_element_t :=
    nat_mod_inv (z_2232) in 
  let x_2234 : ed25519_field_element_t :=
    (x_2230) *% (z_inv_2233) in 
  let y_2235 : ed25519_field_element_t :=
    (y_2231) *% (z_inv_2233) in 
  let s_2236 : byte_seq :=
    nat_mod_to_byte_seq_le (y_2235) in 
  let s_2236 :=
    seq_upd s_2236 (usize 31) ((seq_index (s_2236) (usize 31)) .^ ((
          is_negative (x_2234)) shift_left (usize 7))) in 
  array_from_slice (default : uint8) (32) (s_2236) (usize 0) (usize 32).

Definition sqrt
  (a_2237 : ed25519_field_element_t)
  
  : (option ed25519_field_element_t) :=
  let p3_8_2238 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_p3_8_v)) : ed25519_field_element_t in 
  let p1_4_2239 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_p1_4_v)) : ed25519_field_element_t in 
  let x_c_2240 : ed25519_field_element_t :=
    nat_mod_pow_self (a_2237) (p3_8_2238) in 
  let result_2241 : (option ed25519_field_element_t) :=
    @None ed25519_field_element_t in 
  let '(result_2241) :=
    if ((x_c_2240) *% (x_c_2240)) =.? (a_2237):bool then (let result_2241 :=
        some (x_c_2240) in 
      (result_2241)) else ((result_2241)) in 
  let '(result_2241) :=
    if ((x_c_2240) *% (x_c_2240)) =.? ((nat_mod_zero ) -% (a_2237)):bool then (
      let x_2242 : ed25519_field_element_t :=
        (nat_mod_pow_self (nat_mod_two ) (p1_4_2239)) *% (x_c_2240) in 
      let result_2241 :=
        some (x_2242) in 
      (result_2241)) else ((result_2241)) in 
  result_2241.

Definition check_canonical_point (x_2243 : compressed_ed_point_t)  : bool :=
  let x_2243 :=
    array_upd x_2243 (usize 31) ((array_index (x_2243) (usize 31)) .& (secret (
          @repr WORDSIZE8 127) : int8)) in 
  let x_2244 : big_integer_t :=
    nat_mod_from_byte_seq_le (array_to_seq (x_2243)) : big_integer_t in 
  (x_2244) <.? (nat_mod_from_byte_seq_le (
      array_to_seq (constant_p_v)) : big_integer_t).

Definition decompress (q_2245 : compressed_ed_point_t)  : (option ed_point_t) :=
  let d_2246 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_d_v)) : ed25519_field_element_t in 
  let x_s_2247 : uint8 :=
    ((array_index (q_2245) (usize 31)) .& (secret (
          @repr WORDSIZE8 128) : int8)) shift_right (usize 7) in 
  let y_s_2248 : compressed_ed_point_t :=
    q_2245 in 
  let y_s_2248 :=
    array_upd y_s_2248 (usize 31) ((array_index (y_s_2248) (usize 31)) .& (
        secret (@repr WORDSIZE8 127) : int8)) in 
  ifbnd negb (check_canonical_point (y_s_2248)) : bool
  thenbnd (bind (@None ed_point_t) (fun _ => @Some unit (tt)))
  else (tt) >> (fun 'tt =>
  let y_2249 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (y_s_2248)) : ed25519_field_element_t in 
  let z_2250 : ed25519_field_element_t :=
    nat_mod_one  in 
  let yy_2251 : ed25519_field_element_t :=
    (y_2249) *% (y_2249) in 
  let u_2252 : ed25519_field_element_t :=
    (yy_2251) -% (z_2250) in 
  let v_2253 : ed25519_field_element_t :=
    ((d_2246) *% (yy_2251)) +% (z_2250) in 
  let xx_2254 : ed25519_field_element_t :=
    (u_2252) *% (nat_mod_inv (v_2253)) in 
  bind (sqrt (xx_2254)) (fun x_2255 => let x_r_2256 : uint8 :=
      is_negative (x_2255) in 
    ifbnd ((x_2255) =.? (nat_mod_zero )) && ((uint8_declassify (x_s_2247)) =.? (
        @repr WORDSIZE8 1)) : bool
    thenbnd (bind (@None ed_point_t) (fun _ => @Some unit (tt)))
    else (tt) >> (fun 'tt =>
    let '(x_2255) :=
      if (uint8_declassify (x_r_2256)) !=.? (uint8_declassify (
          x_s_2247)):bool then (let x_2255 :=
          (nat_mod_zero ) -% (x_2255) in 
        (x_2255)) else ((x_2255)) in 
    some ((x_2255, y_2249, z_2250, (x_2255) *% (y_2249)))))).

Definition decompress_non_canonical
  (p_2257 : compressed_ed_point_t)
  
  : (option ed_point_t) :=
  let d_2258 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_d_v)) : ed25519_field_element_t in 
  let x_s_2259 : uint8 :=
    ((array_index (p_2257) (usize 31)) .& (secret (
          @repr WORDSIZE8 128) : int8)) shift_right (usize 7) in 
  let y_s_2260 : compressed_ed_point_t :=
    p_2257 in 
  let y_s_2260 :=
    array_upd y_s_2260 (usize 31) ((array_index (y_s_2260) (usize 31)) .& (
        secret (@repr WORDSIZE8 127) : int8)) in 
  let y_2261 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (y_s_2260)) : ed25519_field_element_t in 
  let z_2262 : ed25519_field_element_t :=
    nat_mod_one  in 
  let yy_2263 : ed25519_field_element_t :=
    (y_2261) *% (y_2261) in 
  let u_2264 : ed25519_field_element_t :=
    (yy_2263) -% (z_2262) in 
  let v_2265 : ed25519_field_element_t :=
    ((d_2258) *% (yy_2263)) +% (z_2262) in 
  let xx_2266 : ed25519_field_element_t :=
    (u_2264) *% (nat_mod_inv (v_2265)) in 
  bind (sqrt (xx_2266)) (fun x_2267 => let x_r_2268 : uint8 :=
      is_negative (x_2267) in 
    let '(x_2267) :=
      if (uint8_declassify (x_r_2268)) !=.? (uint8_declassify (
          x_s_2259)):bool then (let x_2267 :=
          (nat_mod_zero ) -% (x_2267) in 
        (x_2267)) else ((x_2267)) in 
    some ((x_2267, y_2261, z_2262, (x_2267) *% (y_2261)))).

Definition encode (p_2269 : ed_point_t)  : byte_seq :=
  let '(x_2270, y_2271, z_2272, _) :=
    p_2269 in 
  let z_inv_2273 : ed25519_field_element_t :=
    nat_mod_inv (z_2272) in 
  let x_2274 : ed25519_field_element_t :=
    (x_2270) *% (z_inv_2273) in 
  let y_2275 : ed25519_field_element_t :=
    (y_2271) *% (z_inv_2273) in 
  let s_2276 : byte_seq :=
    nat_mod_to_byte_seq_le (y_2275) in 
  let s_2276 :=
    seq_upd s_2276 (usize 31) ((seq_index (s_2276) (usize 31)) .^ ((
          is_negative (x_2274)) shift_left (usize 7))) in 
  s_2276.

Definition decode (q_s_2277 : byte_seq)  : (option ed_point_t) :=
  let q_2278 : compressed_ed_point_t :=
    array_from_slice (default : uint8) (32) (q_s_2277) (usize 0) (usize 32) in 
  decompress (q_2278).

Definition point_add
  (p_2279 : ed_point_t)
  (q_2280 : ed_point_t)
  
  : ed_point_t :=
  let d_c_2281 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_d_v)) : ed25519_field_element_t in 
  let two_2282 : ed25519_field_element_t :=
    nat_mod_two  in 
  let '(x1_2283, y1_2284, z1_2285, t1_2286) :=
    p_2279 in 
  let '(x2_2287, y2_2288, z2_2289, t2_2290) :=
    q_2280 in 
  let a_2291 : ed25519_field_element_t :=
    ((y1_2284) -% (x1_2283)) *% ((y2_2288) -% (x2_2287)) in 
  let b_2292 : ed25519_field_element_t :=
    ((y1_2284) +% (x1_2283)) *% ((y2_2288) +% (x2_2287)) in 
  let c_2293 : ed25519_field_element_t :=
    (((t1_2286) *% (two_2282)) *% (d_c_2281)) *% (t2_2290) in 
  let d_2294 : ed25519_field_element_t :=
    ((z1_2285) *% (two_2282)) *% (z2_2289) in 
  let e_2295 : ed25519_field_element_t :=
    (b_2292) -% (a_2291) in 
  let f_2296 : ed25519_field_element_t :=
    (d_2294) -% (c_2293) in 
  let g_2297 : ed25519_field_element_t :=
    (d_2294) +% (c_2293) in 
  let h_2298 : ed25519_field_element_t :=
    (b_2292) +% (a_2291) in 
  let x3_2299 : ed25519_field_element_t :=
    (e_2295) *% (f_2296) in 
  let y3_2300 : ed25519_field_element_t :=
    (g_2297) *% (h_2298) in 
  let t3_2301 : ed25519_field_element_t :=
    (e_2295) *% (h_2298) in 
  let z3_2302 : ed25519_field_element_t :=
    (f_2296) *% (g_2297) in 
  (x3_2299, y3_2300, z3_2302, t3_2301).

Definition point_identity   : ed_point_t :=
  (nat_mod_zero , nat_mod_one , nat_mod_one , nat_mod_zero ).

Definition point_mul (s_2303 : scalar_t) (p_2304 : ed_point_t)  : ed_point_t :=
  let p_2305 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    p_2304 in 
  let q_2306 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let '(p_2305, q_2306) :=
    foldi (usize 0) (usize 256) (fun i_2307 '(p_2305, q_2306) =>
      let '(q_2306) :=
        if nat_mod_bit (s_2303) (i_2307):bool then (let q_2306 :=
            point_add (q_2306) (p_2305) in 
          (q_2306)) else ((q_2306)) in 
      let p_2305 :=
        point_add (p_2305) (p_2305) in 
      (p_2305, q_2306))
    (p_2305, q_2306) in 
  q_2306.

Definition point_mul_by_cofactor (p_2308 : ed_point_t)  : ed_point_t :=
  let p2_2309 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_add (p_2308) (p_2308) in 
  let p4_2310 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_add (p2_2309) (p2_2309) in 
  let p8_2311 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_add (p4_2310) (p4_2310) in 
  p8_2311.

Definition point_neg (p_2312 : ed_point_t)  : ed_point_t :=
  let '(x_2313, y_2314, z_2315, t_2316) :=
    p_2312 in 
  ((nat_mod_zero ) -% (x_2313), y_2314, z_2315, (nat_mod_zero ) -% (t_2316)).

Definition point_eq (p_2317 : ed_point_t) (q_2318 : ed_point_t)  : bool :=
  let '(x1_2319, y1_2320, z1_2321, _) :=
    p_2317 in 
  let '(x2_2322, y2_2323, z2_2324, _) :=
    q_2318 in 
  (((x1_2319) *% (z2_2324)) =.? ((x2_2322) *% (z1_2321))) && (((y1_2320) *% (
        z2_2324)) =.? ((y2_2323) *% (z1_2321))).

Definition point_normalize (q_2325 : ed_point_t)  : ed_point_t :=
  let '(qx_2326, qy_2327, qz_2328, _) :=
    q_2325 in 
  let px_2329 : ed25519_field_element_t :=
    (qx_2326) *% (nat_mod_inv (qz_2328)) in 
  let py_2330 : ed25519_field_element_t :=
    (qy_2327) *% (nat_mod_inv (qz_2328)) in 
  let pz_2331 : ed25519_field_element_t :=
    nat_mod_one  in 
  let pt_2332 : ed25519_field_element_t :=
    (px_2329) *% (py_2330) in 
  (px_2329, py_2330, pz_2331, pt_2332).

Definition secret_expand
  (sk_2333 : secret_key_t)
  
  : (serialized_scalar_t '× serialized_scalar_t) :=
  let h_2334 : sha512_digest_t :=
    sha512 (seq_from_slice (sk_2333) (usize 0) (usize 32)) in 
  let h_d_2335 : serialized_scalar_t :=
    array_from_slice (default : uint8) (32) (array_to_seq (h_2334)) (usize 32) (
      usize 32) in 
  let s_2336 : serialized_scalar_t :=
    array_from_slice (default : uint8) (32) (array_to_seq (h_2334)) (usize 0) (
      usize 32) in 
  let s_2336 :=
    array_upd s_2336 (usize 0) ((array_index (s_2336) (usize 0)) .& (secret (
          @repr WORDSIZE8 248) : int8)) in 
  let s_2336 :=
    array_upd s_2336 (usize 31) ((array_index (s_2336) (usize 31)) .& (secret (
          @repr WORDSIZE8 127) : int8)) in 
  let s_2336 :=
    array_upd s_2336 (usize 31) ((array_index (s_2336) (usize 31)) .| (secret (
          @repr WORDSIZE8 64) : int8)) in 
  (s_2336, h_d_2335).

Definition secret_to_public (sk_2337 : secret_key_t)  : public_key_t :=
  let '(s_2338, _) :=
    secret_expand (sk_2337) in 
  let base_2339 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let ss_2340 : scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (s_2338)) : scalar_t in 
  let a_2341 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_mul (ss_2340) (base_2339) in 
  compress (a_2341).

Definition check_canonical_scalar (s_2342 : serialized_scalar_t)  : bool :=
  (if ((uint8_declassify ((array_index (s_2342) (usize 31)) .& (secret (
              @repr WORDSIZE8 224) : int8))) !=.? (
        @repr WORDSIZE8 0)):bool then (false) else ((nat_mod_from_byte_seq_le (
          array_to_seq (s_2342)) : big_integer_t) <.? (
        nat_mod_from_byte_seq_le (
          array_to_seq (constant_l_v)) : big_integer_t))).

