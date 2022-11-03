(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Hacspec_Edwards25519.

Require Import Hacspec_Sha512.

Definition b_in_bytes_v : uint_size :=
  usize 64.

Definition s_in_bytes_v : uint_size :=
  usize 128.

Definition l_v : uint_size :=
  usize 48.

Definition j_v : int128 :=
  @repr WORDSIZE128 486662.

Definition z_v : int128 :=
  @repr WORDSIZE128 2.

Definition arr_ed25519_field_element_t := nseq (uint64) (usize 4).

Definition ed_field_hash_canvas_t := nseq (int8) (64).
Definition ed_field_hash_t :=
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Inductive error_t :=
| ExpandMessageAbort : error_t.

Definition eqb_error_t (x y : error_t) : bool :=
match x with
   | ExpandMessageAbort => match y with | ExpandMessageAbort=> true end
   end.

Definition eqb_leibniz_error_t (x y : error_t) : eqb_error_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_error_t : EqDec (error_t) :=
Build_EqDec (error_t) (eqb_error_t) (eqb_leibniz_error_t).


Notation "'byte_seq_result_t'" := ((result byte_seq error_t)) : hacspec_scope.

Notation "'seq_ed_result_t'" := ((
  result seq ed25519_field_element_t error_t)) : hacspec_scope.

Notation "'ed_point_result_t'" := ((result ed_point_t error_t)) : hacspec_scope.

Definition p_1_2_v : arr_ed25519_field_element_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 4611686018427387903) : int64;
        secret (@repr WORDSIZE64 18446744073709551615) : int64;
        secret (@repr WORDSIZE64 18446744073709551615) : int64;
        secret (@repr WORDSIZE64 18446744073709551606) : int64
      ] in  l).

Definition p_3_8_v : arr_ed25519_field_element_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1152921504606846975) : int64;
        secret (@repr WORDSIZE64 18446744073709551615) : int64;
        secret (@repr WORDSIZE64 18446744073709551615) : int64;
        secret (@repr WORDSIZE64 18446744073709551614) : int64
      ] in  l).

Definition p_5_8_v : arr_ed25519_field_element_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1152921504606846975) : int64;
        secret (@repr WORDSIZE64 18446744073709551615) : int64;
        secret (@repr WORDSIZE64 18446744073709551615) : int64;
        secret (@repr WORDSIZE64 18446744073709551613) : int64
      ] in  l).

Definition expand_message_xmd
  (msg_2208 : byte_seq)
  (dst_2209 : byte_seq)
  (len_in_bytes_2210 : uint_size)
  : byte_seq_result_t :=
  let ell_2211 : uint_size :=
    (((len_in_bytes_2210) + (b_in_bytes_v)) - (usize 1)) / (b_in_bytes_v) in 
  let result_2212 : (result byte_seq error_t) :=
    @Err byte_seq error_t (ExpandMessageAbort) in 
  let '(result_2212) :=
    if negb ((((ell_2211) >.? (usize 255)) || ((len_in_bytes_2210) >.? (
            usize 65535))) || ((seq_len (dst_2209)) >.? (
          usize 255))):bool then (let dst_prime_2213 : seq uint8 :=
        seq_push (dst_2209) (uint8_from_usize (seq_len (dst_2209))) in 
      let z_pad_2214 : seq uint8 :=
        seq_new_ (default) (s_in_bytes_v) in 
      let l_i_b_str_2215 : seq uint8 :=
        seq_new_ (default) (usize 2) in 
      let l_i_b_str_2215 :=
        seq_upd l_i_b_str_2215 (usize 0) (uint8_from_usize ((
              len_in_bytes_2210) / (usize 256))) in 
      let l_i_b_str_2215 :=
        seq_upd l_i_b_str_2215 (usize 1) (uint8_from_usize (
            len_in_bytes_2210)) in 
      let msg_prime_2216 : seq uint8 :=
        seq_concat (seq_concat (seq_concat (seq_concat (z_pad_2214) (
                msg_2208)) (l_i_b_str_2215)) (seq_new_ (default) (usize 1))) (
          dst_prime_2213) in 
      let b_0_2217 : seq uint8 :=
        seq_from_seq (array_to_seq (hash (msg_prime_2216))) in 
      let b_i_2218 : seq uint8 :=
        seq_from_seq (array_to_seq (hash (seq_concat (seq_push (b_0_2217) (
                secret (@repr WORDSIZE8 1) : int8)) (dst_prime_2213)))) in 
      let uniform_bytes_2219 : seq uint8 :=
        seq_from_seq (b_i_2218) in 
      let '(b_i_2218, uniform_bytes_2219) :=
        foldi (usize 2) ((ell_2211) + (usize 1)) (fun i_2220 '(
            b_i_2218,
            uniform_bytes_2219
          ) =>
          let t_2221 : seq uint8 :=
            seq_from_seq (b_0_2217) in 
          let b_i_2218 :=
            seq_from_seq (array_to_seq (hash (seq_concat (seq_push ((
                      t_2221) seq_xor (b_i_2218)) (uint8_from_usize (i_2220))) (
                  dst_prime_2213)))) in 
          let uniform_bytes_2219 :=
            seq_concat (uniform_bytes_2219) (b_i_2218) in 
          (b_i_2218, uniform_bytes_2219))
        (b_i_2218, uniform_bytes_2219) in 
      let result_2212 :=
        @Ok byte_seq error_t (seq_truncate (uniform_bytes_2219) (
            len_in_bytes_2210)) in 
      (result_2212)) else ((result_2212)) in 
  result_2212.

Definition ed_hash_to_field
  (msg_2222 : byte_seq)
  (dst_2223 : byte_seq)
  (count_2224 : uint_size)
  : seq_ed_result_t :=
  let len_in_bytes_2225 : uint_size :=
    (count_2224) * (l_v) in 
  let uniform_bytes_2226 : byte_seq :=
    expand_message_xmd (msg_2222) (dst_2223) (len_in_bytes_2225) in 
  let output_2227 : seq ed25519_field_element_t :=
    seq_new_ (default) (count_2224) in 
  let output_2227 :=
    foldi (usize 0) (count_2224) (fun i_2228 output_2227 =>
      let elm_offset_2229 : uint_size :=
        (l_v) * (i_2228) in 
      let tv_2230 : seq uint8 :=
        seq_slice (uniform_bytes_2226) (elm_offset_2229) (l_v) in 
      let u_i_2231 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
              nat_mod_from_byte_seq_be (tv_2230) : ed_field_hash_t)) (
            usize 32) (usize 32)) : ed25519_field_element_t in 
      let output_2227 :=
        seq_upd output_2227 (i_2228) (u_i_2231) in 
      (output_2227))
    output_2227 in 
  @Ok seq ed25519_field_element_t error_t (output_2227).

Definition ed_is_square (x_2232 : ed25519_field_element_t) : bool :=
  let c1_2233 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (
        p_1_2_v)) : ed25519_field_element_t in 
  let tv_2234 : ed25519_field_element_t :=
    nat_mod_pow_self (x_2232) (c1_2233) in 
  ((tv_2234) =.? (nat_mod_zero )) || ((tv_2234) =.? (nat_mod_one )).

Definition sgn0_m_eq_1 (x_2235 : ed25519_field_element_t) : bool :=
  ((x_2235) rem (nat_mod_two )) =.? (nat_mod_one ).

Definition ed_clear_cofactor (x_2236 : ed_point_t) : ed_point_t :=
  point_mul_by_cofactor (x_2236).

Definition cmov
  (a_2237 : ed25519_field_element_t)
  (b_2238 : ed25519_field_element_t)
  (c_2239 : bool)
  : ed25519_field_element_t :=
  (if (c_2239):bool then (b_2238) else (a_2237)).

Definition xor (a_2240 : bool) (b_2241 : bool) : bool :=
  (if (a_2240):bool then ((if (b_2241):bool then (false) else (true))) else ((
        if (b_2241):bool then (true) else (false)))).

Definition curve25519_to_edwards25519 (p_2242 : ed_point_t) : ed_point_t :=
  let '(s_2243, t_2244, _, _) :=
    point_normalize (p_2242) in 
  let one_2245 : ed25519_field_element_t :=
    nat_mod_one  in 
  let zero_2246 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let tv1_2247 : ed25519_field_element_t :=
    (s_2243) +% (one_2245) in 
  let tv2_2248 : ed25519_field_element_t :=
    (tv1_2247) *% (t_2244) in 
  let tv2_2249 : ed25519_field_element_t :=
    nat_mod_inv (tv2_2248) in 
  let v_2250 : ed25519_field_element_t :=
    (tv2_2249) *% (tv1_2247) in 
  let v_2251 : ed25519_field_element_t :=
    (v_2250) *% (s_2243) in 
  let w_2252 : ed25519_field_element_t :=
    (tv2_2249) *% (t_2244) in 
  let tv1_2253 : ed25519_field_element_t :=
    (s_2243) -% (one_2245) in 
  let w_2254 : ed25519_field_element_t :=
    (w_2252) *% (tv1_2253) in 
  let e_2255 : bool :=
    (tv2_2249) =.? (zero_2246) in 
  let w_2256 : ed25519_field_element_t :=
    cmov (w_2254) (one_2245) (e_2255) in 
  let c_2257 : ed25519_field_element_t :=
    (nat_mod_zero ) -% (nat_mod_from_literal (_) (
        @repr WORDSIZE128 486664) : ed25519_field_element_t) in 
  let sq_2258 : (option ed25519_field_element_t) :=
    sqrt (c_2257) in 
  let v_2259 : ed25519_field_element_t :=
    (v_2251) *% (option_unwrap (sq_2258)) in 
  (v_2259, w_2256, one_2245, (v_2259) *% (w_2256)).

Definition map_to_curve_elligator2
  (u_2260 : ed25519_field_element_t)
  : ed_point_t :=
  let j_2261 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (j_v) : ed25519_field_element_t in 
  let z_2262 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (z_v) : ed25519_field_element_t in 
  let one_2263 : ed25519_field_element_t :=
    nat_mod_one  in 
  let zero_2264 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let x1_2265 : ed25519_field_element_t :=
    ((zero_2264) -% (j_2261)) *% (nat_mod_inv ((one_2263) +% (((z_2262) *% (
              u_2260)) *% (u_2260)))) in 
  let '(x1_2265) :=
    if (x1_2265) =.? (zero_2264):bool then (let x1_2265 :=
        (zero_2264) -% (j_2261) in 
      (x1_2265)) else ((x1_2265)) in 
  let gx1_2266 : ed25519_field_element_t :=
    ((((x1_2265) *% (x1_2265)) *% (x1_2265)) +% (((j_2261) *% (x1_2265)) *% (
          x1_2265))) +% (x1_2265) in 
  let x2_2267 : ed25519_field_element_t :=
    ((zero_2264) -% (x1_2265)) -% (j_2261) in 
  let gx2_2268 : ed25519_field_element_t :=
    ((((x2_2267) *% (x2_2267)) *% (x2_2267)) +% ((j_2261) *% ((x2_2267) *% (
            x2_2267)))) +% (x2_2267) in 
  let x_2269 : ed25519_field_element_t :=
    zero_2264 in 
  let y_2270 : ed25519_field_element_t :=
    zero_2264 in 
  let '(x_2269, y_2270) :=
    if ed_is_square (gx1_2266):bool then (let x_2269 :=
        x1_2265 in 
      let y_2270 :=
        option_unwrap (sqrt (gx1_2266)) in 
      let '(y_2270) :=
        if negb (sgn0_m_eq_1 (y_2270)):bool then (let y_2270 :=
            (zero_2264) -% (y_2270) in 
          (y_2270)) else ((y_2270)) in 
      (x_2269, y_2270)) else (let x_2269 :=
        x2_2267 in 
      let y_2270 :=
        option_unwrap (sqrt (gx2_2268)) in 
      let '(y_2270) :=
        if sgn0_m_eq_1 (y_2270):bool then (let y_2270 :=
            (zero_2264) -% (y_2270) in 
          (y_2270)) else ((y_2270)) in 
      (x_2269, y_2270)) in 
  let s_2271 : ed25519_field_element_t :=
    x_2269 in 
  let t_2272 : ed25519_field_element_t :=
    y_2270 in 
  (s_2271, t_2272, one_2263, (s_2271) *% (t_2272)).

Definition map_to_curve_elligator2_straight
  (u_2273 : ed25519_field_element_t)
  : ed_point_t :=
  let j_2274 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (j_v) : ed25519_field_element_t in 
  let z_2275 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (z_v) : ed25519_field_element_t in 
  let one_2276 : ed25519_field_element_t :=
    nat_mod_one  in 
  let zero_2277 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let tv1_2278 : ed25519_field_element_t :=
    (u_2273) *% (u_2273) in 
  let tv1_2279 : ed25519_field_element_t :=
    (z_2275) *% (tv1_2278) in 
  let e1_2280 : bool :=
    (tv1_2279) =.? ((zero_2277) -% (one_2276)) in 
  let tv1_2281 : ed25519_field_element_t :=
    cmov (tv1_2279) (zero_2277) (e1_2280) in 
  let x1_2282 : ed25519_field_element_t :=
    (tv1_2281) +% (one_2276) in 
  let x1_2283 : ed25519_field_element_t :=
    nat_mod_inv (x1_2282) in 
  let x1_2284 : ed25519_field_element_t :=
    ((zero_2277) -% (j_2274)) *% (x1_2283) in 
  let gx1_2285 : ed25519_field_element_t :=
    (x1_2284) +% (j_2274) in 
  let gx1_2286 : ed25519_field_element_t :=
    (gx1_2285) *% (x1_2284) in 
  let gx1_2287 : ed25519_field_element_t :=
    (gx1_2286) +% (one_2276) in 
  let gx1_2288 : ed25519_field_element_t :=
    (gx1_2287) *% (x1_2284) in 
  let x2_2289 : ed25519_field_element_t :=
    ((zero_2277) -% (x1_2284)) -% (j_2274) in 
  let gx2_2290 : ed25519_field_element_t :=
    (tv1_2281) *% (gx1_2288) in 
  let e2_2291 : bool :=
    ed_is_square (gx1_2288) in 
  let x_2292 : ed25519_field_element_t :=
    cmov (x2_2289) (x1_2284) (e2_2291) in 
  let y2_2293 : ed25519_field_element_t :=
    cmov (gx2_2290) (gx1_2288) (e2_2291) in 
  let y_2294 : ed25519_field_element_t :=
    option_unwrap (sqrt (y2_2293)) in 
  let e3_2295 : bool :=
    sgn0_m_eq_1 (y_2294) in 
  let y_2296 : ed25519_field_element_t :=
    cmov (y_2294) ((zero_2277) -% (y_2294)) (xor (e2_2291) (e3_2295)) in 
  let s_2297 : ed25519_field_element_t :=
    x_2292 in 
  let t_2298 : ed25519_field_element_t :=
    y_2296 in 
  (s_2297, t_2298, one_2276, (s_2297) *% (t_2298)).

Definition map_to_curve_elligator2_curve25519
  (u_2299 : ed25519_field_element_t)
  : ed_point_t :=
  let j_2300 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (j_v) : ed25519_field_element_t in 
  let zero_2301 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let one_2302 : ed25519_field_element_t :=
    nat_mod_one  in 
  let two_2303 : ed25519_field_element_t :=
    nat_mod_two  in 
  let c1_2304 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (
        p_3_8_v)) : ed25519_field_element_t in 
  let c2_2305 : ed25519_field_element_t :=
    nat_mod_pow_self (two_2303) (c1_2304) in 
  let c3_2306 : ed25519_field_element_t :=
    option_unwrap (sqrt ((zero_2301) -% (one_2302))) in 
  let c4_2307 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (
        p_5_8_v)) : ed25519_field_element_t in 
  let tv1_2308 : ed25519_field_element_t :=
    (u_2299) *% (u_2299) in 
  let tv1_2309 : ed25519_field_element_t :=
    (two_2303) *% (tv1_2308) in 
  let xd_2310 : ed25519_field_element_t :=
    (tv1_2309) +% (one_2302) in 
  let x1n_2311 : ed25519_field_element_t :=
    (zero_2301) -% (j_2300) in 
  let tv2_2312 : ed25519_field_element_t :=
    (xd_2310) *% (xd_2310) in 
  let gxd_2313 : ed25519_field_element_t :=
    (tv2_2312) *% (xd_2310) in 
  let gx1_2314 : ed25519_field_element_t :=
    (j_2300) *% (tv1_2309) in 
  let gx1_2315 : ed25519_field_element_t :=
    (gx1_2314) *% (x1n_2311) in 
  let gx1_2316 : ed25519_field_element_t :=
    (gx1_2315) +% (tv2_2312) in 
  let gx1_2317 : ed25519_field_element_t :=
    (gx1_2316) *% (x1n_2311) in 
  let tv3_2318 : ed25519_field_element_t :=
    (gxd_2313) *% (gxd_2313) in 
  let tv2_2319 : ed25519_field_element_t :=
    (tv3_2318) *% (tv3_2318) in 
  let tv3_2320 : ed25519_field_element_t :=
    (tv3_2318) *% (gxd_2313) in 
  let tv3_2321 : ed25519_field_element_t :=
    (tv3_2320) *% (gx1_2317) in 
  let tv2_2322 : ed25519_field_element_t :=
    (tv2_2319) *% (tv3_2321) in 
  let y11_2323 : ed25519_field_element_t :=
    nat_mod_pow_self (tv2_2322) (c4_2307) in 
  let y11_2324 : ed25519_field_element_t :=
    (y11_2323) *% (tv3_2321) in 
  let y12_2325 : ed25519_field_element_t :=
    (y11_2324) *% (c3_2306) in 
  let tv2_2326 : ed25519_field_element_t :=
    (y11_2324) *% (y11_2324) in 
  let tv2_2327 : ed25519_field_element_t :=
    (tv2_2326) *% (gxd_2313) in 
  let e1_2328 : bool :=
    (tv2_2327) =.? (gx1_2317) in 
  let y1_2329 : ed25519_field_element_t :=
    cmov (y12_2325) (y11_2324) (e1_2328) in 
  let x2n_2330 : ed25519_field_element_t :=
    (x1n_2311) *% (tv1_2309) in 
  let y21_2331 : ed25519_field_element_t :=
    (y11_2324) *% (u_2299) in 
  let y21_2332 : ed25519_field_element_t :=
    (y21_2331) *% (c2_2305) in 
  let y22_2333 : ed25519_field_element_t :=
    (y21_2332) *% (c3_2306) in 
  let gx2_2334 : ed25519_field_element_t :=
    (gx1_2317) *% (tv1_2309) in 
  let tv2_2335 : ed25519_field_element_t :=
    (y21_2332) *% (y21_2332) in 
  let tv2_2336 : ed25519_field_element_t :=
    (tv2_2335) *% (gxd_2313) in 
  let e2_2337 : bool :=
    (tv2_2336) =.? (gx2_2334) in 
  let y2_2338 : ed25519_field_element_t :=
    cmov (y22_2333) (y21_2332) (e2_2337) in 
  let tv2_2339 : ed25519_field_element_t :=
    (y1_2329) *% (y1_2329) in 
  let tv2_2340 : ed25519_field_element_t :=
    (tv2_2339) *% (gxd_2313) in 
  let e3_2341 : bool :=
    (tv2_2340) =.? (gx1_2317) in 
  let xn_2342 : ed25519_field_element_t :=
    cmov (x2n_2330) (x1n_2311) (e3_2341) in 
  let y_2343 : ed25519_field_element_t :=
    cmov (y2_2338) (y1_2329) (e3_2341) in 
  let e4_2344 : bool :=
    sgn0_m_eq_1 (y_2343) in 
  let y_2345 : ed25519_field_element_t :=
    cmov (y_2343) ((zero_2301) -% (y_2343)) (xor (e3_2341) (e4_2344)) in 
  (xn_2342, xd_2310, y_2345, one_2302).

Definition map_to_curve_elligator2_edwards25519
  (u_2346 : ed25519_field_element_t)
  : ed_point_t :=
  let j_2347 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (j_v) : ed25519_field_element_t in 
  let zero_2348 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let one_2349 : ed25519_field_element_t :=
    nat_mod_one  in 
  let two_2350 : ed25519_field_element_t :=
    nat_mod_two  in 
  let c1_2351 : ed25519_field_element_t :=
    option_unwrap (sqrt ((zero_2348) -% ((j_2347) +% (two_2350)))) in 
  let '(xmn_2352, xmd_2353, ymn_2354, ymd_2355) :=
    map_to_curve_elligator2_curve25519 (u_2346) in 
  let xn_2356 : ed25519_field_element_t :=
    (xmn_2352) *% (ymd_2355) in 
  let xn_2357 : ed25519_field_element_t :=
    (xn_2356) *% (c1_2351) in 
  let xd_2358 : ed25519_field_element_t :=
    (xmd_2353) *% (ymn_2354) in 
  let yn_2359 : ed25519_field_element_t :=
    (xmn_2352) -% (xmd_2353) in 
  let yd_2360 : ed25519_field_element_t :=
    (xmn_2352) +% (xmd_2353) in 
  let tv1_2361 : ed25519_field_element_t :=
    (xd_2358) *% (yd_2360) in 
  let e_2362 : bool :=
    (tv1_2361) =.? (zero_2348) in 
  let xn_2363 : ed25519_field_element_t :=
    cmov (xn_2357) (zero_2348) (e_2362) in 
  let xd_2364 : ed25519_field_element_t :=
    cmov (xd_2358) (one_2349) (e_2362) in 
  let yn_2365 : ed25519_field_element_t :=
    cmov (yn_2359) (one_2349) (e_2362) in 
  let yd_2366 : ed25519_field_element_t :=
    cmov (yd_2360) (one_2349) (e_2362) in 
  let x_2367 : ed25519_field_element_t :=
    (xn_2363) *% (nat_mod_inv (xd_2364)) in 
  let y_2368 : ed25519_field_element_t :=
    (yn_2365) *% (nat_mod_inv (yd_2366)) in 
  (x_2367, y_2368, one_2349, (x_2367) *% (y_2368)).

Definition map_to_curve_elligator2_edwards
  (u_2369 : ed25519_field_element_t)
  : ed_point_t :=
  let st_2370 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    map_to_curve_elligator2 (u_2369) in 
  curve25519_to_edwards25519 (st_2370).

Definition ed_encode_to_curve
  (msg_2371 : byte_seq)
  (dst_2372 : byte_seq)
  : ed_point_result_t :=
  let u_2373 : seq ed25519_field_element_t :=
    ed_hash_to_field (msg_2371) (dst_2372) (usize 1) in 
  let q_2374 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    map_to_curve_elligator2_edwards (seq_index (u_2373) (usize 0)) in 
  @Ok ed_point_t error_t (ed_clear_cofactor (q_2374)).

