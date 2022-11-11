(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
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
  (msg_2266 : byte_seq)
  (dst_2267 : byte_seq)
  (len_in_bytes_2268 : uint_size)
  : byte_seq_result_t :=
  let ell_2269 : uint_size :=
    (((len_in_bytes_2268) + (b_in_bytes_v)) - (usize 1)) / (b_in_bytes_v) in 
  let result_2270 : (result byte_seq error_t) :=
    @Err byte_seq error_t (ExpandMessageAbort) in 
  let '(result_2270) :=
    if negb ((((ell_2269) >.? (usize 255)) || ((len_in_bytes_2268) >.? (
            usize 65535))) || ((seq_len (dst_2267)) >.? (
          usize 255))):bool then (let dst_prime_2271 : seq uint8 :=
        seq_push (dst_2267) (uint8_from_usize (seq_len (dst_2267))) in 
      let z_pad_2272 : seq uint8 :=
        seq_new_ (default : uint8) (s_in_bytes_v) in 
      let l_i_b_str_2273 : seq uint8 :=
        seq_new_ (default : uint8) (usize 2) in 
      let l_i_b_str_2273 :=
        seq_upd l_i_b_str_2273 (usize 0) (uint8_from_usize ((
              len_in_bytes_2268) / (usize 256))) in 
      let l_i_b_str_2273 :=
        seq_upd l_i_b_str_2273 (usize 1) (uint8_from_usize (
            len_in_bytes_2268)) in 
      let msg_prime_2274 : seq uint8 :=
        seq_concat (seq_concat (seq_concat (seq_concat (z_pad_2272) (
                msg_2266)) (l_i_b_str_2273)) (seq_new_ (default : uint8) (
              usize 1))) (dst_prime_2271) in 
      let b_0_2275 : seq uint8 :=
        seq_from_seq (array_to_seq (hash (msg_prime_2274))) in 
      let b_i_2276 : seq uint8 :=
        seq_from_seq (array_to_seq (hash (seq_concat (seq_push (b_0_2275) (
                secret (@repr WORDSIZE8 1) : int8)) (dst_prime_2271)))) in 
      let uniform_bytes_2277 : seq uint8 :=
        seq_from_seq (b_i_2276) in 
      let '(b_i_2276, uniform_bytes_2277) :=
        foldi (usize 2) ((ell_2269) + (usize 1)) (fun i_2278 '(
            b_i_2276,
            uniform_bytes_2277
          ) =>
          let t_2279 : seq uint8 :=
            seq_from_seq (b_0_2275) in 
          let b_i_2276 :=
            seq_from_seq (array_to_seq (hash (seq_concat (seq_push ((
                      t_2279) seq_xor (b_i_2276)) (uint8_from_usize (i_2278))) (
                  dst_prime_2271)))) in 
          let uniform_bytes_2277 :=
            seq_concat (uniform_bytes_2277) (b_i_2276) in 
          (b_i_2276, uniform_bytes_2277))
        (b_i_2276, uniform_bytes_2277) in 
      let result_2270 :=
        @Ok byte_seq error_t (seq_truncate (uniform_bytes_2277) (
            len_in_bytes_2268)) in 
      (result_2270)) else ((result_2270)) in 
  result_2270.

Definition ed_hash_to_field
  (msg_2280 : byte_seq)
  (dst_2281 : byte_seq)
  (count_2282 : uint_size)
  : seq_ed_result_t :=
  let len_in_bytes_2283 : uint_size :=
    (count_2282) * (l_v) in 
  let uniform_bytes_2284 : byte_seq :=
    expand_message_xmd (msg_2280) (dst_2281) (len_in_bytes_2283) in 
  let output_2285 : seq ed25519_field_element_t :=
    seq_new_ (default : ed25519_field_element_t) (count_2282) in 
  let output_2285 :=
    foldi (usize 0) (count_2282) (fun i_2286 output_2285 =>
      let elm_offset_2287 : uint_size :=
        (l_v) * (i_2286) in 
      let tv_2288 : seq uint8 :=
        seq_slice (uniform_bytes_2284) (elm_offset_2287) (l_v) in 
      let u_i_2289 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
              nat_mod_from_byte_seq_be (tv_2288) : ed_field_hash_t)) (
            usize 32) (usize 32)) : ed25519_field_element_t in 
      let output_2285 :=
        seq_upd output_2285 (i_2286) (u_i_2289) in 
      (output_2285))
    output_2285 in 
  @Ok seq ed25519_field_element_t error_t (output_2285).

Definition ed_is_square (x_2290 : ed25519_field_element_t) : bool :=
  let c1_2291 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (
        p_1_2_v)) : ed25519_field_element_t in 
  let tv_2292 : ed25519_field_element_t :=
    nat_mod_pow_self (x_2290) (c1_2291) in 
  ((tv_2292) =.? (nat_mod_zero )) || ((tv_2292) =.? (nat_mod_one )).

Definition sgn0_m_eq_1 (x_2293 : ed25519_field_element_t) : bool :=
  ((x_2293) rem (nat_mod_two )) =.? (nat_mod_one ).

Definition ed_clear_cofactor (x_2294 : ed_point_t) : ed_point_t :=
  point_mul_by_cofactor (x_2294).

Definition cmov
  (a_2295 : ed25519_field_element_t)
  (b_2296 : ed25519_field_element_t)
  (c_2297 : bool)
  : ed25519_field_element_t :=
  (if (c_2297):bool then (b_2296) else (a_2295)).

Definition xor (a_2298 : bool) (b_2299 : bool) : bool :=
  (if (a_2298):bool then ((if (b_2299):bool then (false) else (true))) else ((
        if (b_2299):bool then (true) else (false)))).

Definition curve25519_to_edwards25519 (p_2300 : ed_point_t) : ed_point_t :=
  let '(s_2301, t_2302, _, _) :=
    point_normalize (p_2300) in 
  let one_2303 : ed25519_field_element_t :=
    nat_mod_one  in 
  let zero_2304 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let tv1_2305 : ed25519_field_element_t :=
    (s_2301) +% (one_2303) in 
  let tv2_2306 : ed25519_field_element_t :=
    (tv1_2305) *% (t_2302) in 
  let tv2_2307 : ed25519_field_element_t :=
    nat_mod_inv (tv2_2306) in 
  let v_2308 : ed25519_field_element_t :=
    (tv2_2307) *% (tv1_2305) in 
  let v_2309 : ed25519_field_element_t :=
    (v_2308) *% (s_2301) in 
  let w_2310 : ed25519_field_element_t :=
    (tv2_2307) *% (t_2302) in 
  let tv1_2311 : ed25519_field_element_t :=
    (s_2301) -% (one_2303) in 
  let w_2312 : ed25519_field_element_t :=
    (w_2310) *% (tv1_2311) in 
  let e_2313 : bool :=
    (tv2_2307) =.? (zero_2304) in 
  let w_2314 : ed25519_field_element_t :=
    cmov (w_2312) (one_2303) (e_2313) in 
  let c_2315 : ed25519_field_element_t :=
    (nat_mod_zero ) -% (nat_mod_from_literal (_) (
        @repr WORDSIZE128 486664) : ed25519_field_element_t) in 
  let sq_2316 : (option ed25519_field_element_t) :=
    sqrt (c_2315) in 
  let v_2317 : ed25519_field_element_t :=
    (v_2309) *% (option_unwrap (sq_2316)) in 
  (v_2317, w_2314, one_2303, (v_2317) *% (w_2314)).

Definition map_to_curve_elligator2
  (u_2318 : ed25519_field_element_t)
  : ed_point_t :=
  let j_2319 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (j_v) : ed25519_field_element_t in 
  let z_2320 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (z_v) : ed25519_field_element_t in 
  let one_2321 : ed25519_field_element_t :=
    nat_mod_one  in 
  let zero_2322 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let x1_2323 : ed25519_field_element_t :=
    ((zero_2322) -% (j_2319)) *% (nat_mod_inv ((one_2321) +% (((z_2320) *% (
              u_2318)) *% (u_2318)))) in 
  let '(x1_2323) :=
    if (x1_2323) =.? (zero_2322):bool then (let x1_2323 :=
        (zero_2322) -% (j_2319) in 
      (x1_2323)) else ((x1_2323)) in 
  let gx1_2324 : ed25519_field_element_t :=
    ((((x1_2323) *% (x1_2323)) *% (x1_2323)) +% (((j_2319) *% (x1_2323)) *% (
          x1_2323))) +% (x1_2323) in 
  let x2_2325 : ed25519_field_element_t :=
    ((zero_2322) -% (x1_2323)) -% (j_2319) in 
  let gx2_2326 : ed25519_field_element_t :=
    ((((x2_2325) *% (x2_2325)) *% (x2_2325)) +% ((j_2319) *% ((x2_2325) *% (
            x2_2325)))) +% (x2_2325) in 
  let x_2327 : ed25519_field_element_t :=
    zero_2322 in 
  let y_2328 : ed25519_field_element_t :=
    zero_2322 in 
  let '(x_2327, y_2328) :=
    if ed_is_square (gx1_2324):bool then (let x_2327 :=
        x1_2323 in 
      let y_2328 :=
        option_unwrap (sqrt (gx1_2324)) in 
      let '(y_2328) :=
        if negb (sgn0_m_eq_1 (y_2328)):bool then (let y_2328 :=
            (zero_2322) -% (y_2328) in 
          (y_2328)) else ((y_2328)) in 
      (x_2327, y_2328)) else (let x_2327 :=
        x2_2325 in 
      let y_2328 :=
        option_unwrap (sqrt (gx2_2326)) in 
      let '(y_2328) :=
        if sgn0_m_eq_1 (y_2328):bool then (let y_2328 :=
            (zero_2322) -% (y_2328) in 
          (y_2328)) else ((y_2328)) in 
      (x_2327, y_2328)) in 
  let s_2329 : ed25519_field_element_t :=
    x_2327 in 
  let t_2330 : ed25519_field_element_t :=
    y_2328 in 
  (s_2329, t_2330, one_2321, (s_2329) *% (t_2330)).

Definition map_to_curve_elligator2_straight
  (u_2331 : ed25519_field_element_t)
  : ed_point_t :=
  let j_2332 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (j_v) : ed25519_field_element_t in 
  let z_2333 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (z_v) : ed25519_field_element_t in 
  let one_2334 : ed25519_field_element_t :=
    nat_mod_one  in 
  let zero_2335 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let tv1_2336 : ed25519_field_element_t :=
    (u_2331) *% (u_2331) in 
  let tv1_2337 : ed25519_field_element_t :=
    (z_2333) *% (tv1_2336) in 
  let e1_2338 : bool :=
    (tv1_2337) =.? ((zero_2335) -% (one_2334)) in 
  let tv1_2339 : ed25519_field_element_t :=
    cmov (tv1_2337) (zero_2335) (e1_2338) in 
  let x1_2340 : ed25519_field_element_t :=
    (tv1_2339) +% (one_2334) in 
  let x1_2341 : ed25519_field_element_t :=
    nat_mod_inv (x1_2340) in 
  let x1_2342 : ed25519_field_element_t :=
    ((zero_2335) -% (j_2332)) *% (x1_2341) in 
  let gx1_2343 : ed25519_field_element_t :=
    (x1_2342) +% (j_2332) in 
  let gx1_2344 : ed25519_field_element_t :=
    (gx1_2343) *% (x1_2342) in 
  let gx1_2345 : ed25519_field_element_t :=
    (gx1_2344) +% (one_2334) in 
  let gx1_2346 : ed25519_field_element_t :=
    (gx1_2345) *% (x1_2342) in 
  let x2_2347 : ed25519_field_element_t :=
    ((zero_2335) -% (x1_2342)) -% (j_2332) in 
  let gx2_2348 : ed25519_field_element_t :=
    (tv1_2339) *% (gx1_2346) in 
  let e2_2349 : bool :=
    ed_is_square (gx1_2346) in 
  let x_2350 : ed25519_field_element_t :=
    cmov (x2_2347) (x1_2342) (e2_2349) in 
  let y2_2351 : ed25519_field_element_t :=
    cmov (gx2_2348) (gx1_2346) (e2_2349) in 
  let y_2352 : ed25519_field_element_t :=
    option_unwrap (sqrt (y2_2351)) in 
  let e3_2353 : bool :=
    sgn0_m_eq_1 (y_2352) in 
  let y_2354 : ed25519_field_element_t :=
    cmov (y_2352) ((zero_2335) -% (y_2352)) (xor (e2_2349) (e3_2353)) in 
  let s_2355 : ed25519_field_element_t :=
    x_2350 in 
  let t_2356 : ed25519_field_element_t :=
    y_2354 in 
  (s_2355, t_2356, one_2334, (s_2355) *% (t_2356)).

Definition map_to_curve_elligator2_curve25519
  (u_2357 : ed25519_field_element_t)
  : ed_point_t :=
  let j_2358 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (j_v) : ed25519_field_element_t in 
  let zero_2359 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let one_2360 : ed25519_field_element_t :=
    nat_mod_one  in 
  let two_2361 : ed25519_field_element_t :=
    nat_mod_two  in 
  let c1_2362 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (
        p_3_8_v)) : ed25519_field_element_t in 
  let c2_2363 : ed25519_field_element_t :=
    nat_mod_pow_self (two_2361) (c1_2362) in 
  let c3_2364 : ed25519_field_element_t :=
    option_unwrap (sqrt ((zero_2359) -% (one_2360))) in 
  let c4_2365 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (
        p_5_8_v)) : ed25519_field_element_t in 
  let tv1_2366 : ed25519_field_element_t :=
    (u_2357) *% (u_2357) in 
  let tv1_2367 : ed25519_field_element_t :=
    (two_2361) *% (tv1_2366) in 
  let xd_2368 : ed25519_field_element_t :=
    (tv1_2367) +% (one_2360) in 
  let x1n_2369 : ed25519_field_element_t :=
    (zero_2359) -% (j_2358) in 
  let tv2_2370 : ed25519_field_element_t :=
    (xd_2368) *% (xd_2368) in 
  let gxd_2371 : ed25519_field_element_t :=
    (tv2_2370) *% (xd_2368) in 
  let gx1_2372 : ed25519_field_element_t :=
    (j_2358) *% (tv1_2367) in 
  let gx1_2373 : ed25519_field_element_t :=
    (gx1_2372) *% (x1n_2369) in 
  let gx1_2374 : ed25519_field_element_t :=
    (gx1_2373) +% (tv2_2370) in 
  let gx1_2375 : ed25519_field_element_t :=
    (gx1_2374) *% (x1n_2369) in 
  let tv3_2376 : ed25519_field_element_t :=
    (gxd_2371) *% (gxd_2371) in 
  let tv2_2377 : ed25519_field_element_t :=
    (tv3_2376) *% (tv3_2376) in 
  let tv3_2378 : ed25519_field_element_t :=
    (tv3_2376) *% (gxd_2371) in 
  let tv3_2379 : ed25519_field_element_t :=
    (tv3_2378) *% (gx1_2375) in 
  let tv2_2380 : ed25519_field_element_t :=
    (tv2_2377) *% (tv3_2379) in 
  let y11_2381 : ed25519_field_element_t :=
    nat_mod_pow_self (tv2_2380) (c4_2365) in 
  let y11_2382 : ed25519_field_element_t :=
    (y11_2381) *% (tv3_2379) in 
  let y12_2383 : ed25519_field_element_t :=
    (y11_2382) *% (c3_2364) in 
  let tv2_2384 : ed25519_field_element_t :=
    (y11_2382) *% (y11_2382) in 
  let tv2_2385 : ed25519_field_element_t :=
    (tv2_2384) *% (gxd_2371) in 
  let e1_2386 : bool :=
    (tv2_2385) =.? (gx1_2375) in 
  let y1_2387 : ed25519_field_element_t :=
    cmov (y12_2383) (y11_2382) (e1_2386) in 
  let x2n_2388 : ed25519_field_element_t :=
    (x1n_2369) *% (tv1_2367) in 
  let y21_2389 : ed25519_field_element_t :=
    (y11_2382) *% (u_2357) in 
  let y21_2390 : ed25519_field_element_t :=
    (y21_2389) *% (c2_2363) in 
  let y22_2391 : ed25519_field_element_t :=
    (y21_2390) *% (c3_2364) in 
  let gx2_2392 : ed25519_field_element_t :=
    (gx1_2375) *% (tv1_2367) in 
  let tv2_2393 : ed25519_field_element_t :=
    (y21_2390) *% (y21_2390) in 
  let tv2_2394 : ed25519_field_element_t :=
    (tv2_2393) *% (gxd_2371) in 
  let e2_2395 : bool :=
    (tv2_2394) =.? (gx2_2392) in 
  let y2_2396 : ed25519_field_element_t :=
    cmov (y22_2391) (y21_2390) (e2_2395) in 
  let tv2_2397 : ed25519_field_element_t :=
    (y1_2387) *% (y1_2387) in 
  let tv2_2398 : ed25519_field_element_t :=
    (tv2_2397) *% (gxd_2371) in 
  let e3_2399 : bool :=
    (tv2_2398) =.? (gx1_2375) in 
  let xn_2400 : ed25519_field_element_t :=
    cmov (x2n_2388) (x1n_2369) (e3_2399) in 
  let y_2401 : ed25519_field_element_t :=
    cmov (y2_2396) (y1_2387) (e3_2399) in 
  let e4_2402 : bool :=
    sgn0_m_eq_1 (y_2401) in 
  let y_2403 : ed25519_field_element_t :=
    cmov (y_2401) ((zero_2359) -% (y_2401)) (xor (e3_2399) (e4_2402)) in 
  (xn_2400, xd_2368, y_2403, one_2360).

Definition map_to_curve_elligator2_edwards25519
  (u_2404 : ed25519_field_element_t)
  : ed_point_t :=
  let j_2405 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (j_v) : ed25519_field_element_t in 
  let zero_2406 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let one_2407 : ed25519_field_element_t :=
    nat_mod_one  in 
  let two_2408 : ed25519_field_element_t :=
    nat_mod_two  in 
  let c1_2409 : ed25519_field_element_t :=
    option_unwrap (sqrt ((zero_2406) -% ((j_2405) +% (two_2408)))) in 
  let '(xmn_2410, xmd_2411, ymn_2412, ymd_2413) :=
    map_to_curve_elligator2_curve25519 (u_2404) in 
  let xn_2414 : ed25519_field_element_t :=
    (xmn_2410) *% (ymd_2413) in 
  let xn_2415 : ed25519_field_element_t :=
    (xn_2414) *% (c1_2409) in 
  let xd_2416 : ed25519_field_element_t :=
    (xmd_2411) *% (ymn_2412) in 
  let yn_2417 : ed25519_field_element_t :=
    (xmn_2410) -% (xmd_2411) in 
  let yd_2418 : ed25519_field_element_t :=
    (xmn_2410) +% (xmd_2411) in 
  let tv1_2419 : ed25519_field_element_t :=
    (xd_2416) *% (yd_2418) in 
  let e_2420 : bool :=
    (tv1_2419) =.? (zero_2406) in 
  let xn_2421 : ed25519_field_element_t :=
    cmov (xn_2415) (zero_2406) (e_2420) in 
  let xd_2422 : ed25519_field_element_t :=
    cmov (xd_2416) (one_2407) (e_2420) in 
  let yn_2423 : ed25519_field_element_t :=
    cmov (yn_2417) (one_2407) (e_2420) in 
  let yd_2424 : ed25519_field_element_t :=
    cmov (yd_2418) (one_2407) (e_2420) in 
  let x_2425 : ed25519_field_element_t :=
    (xn_2421) *% (nat_mod_inv (xd_2422)) in 
  let y_2426 : ed25519_field_element_t :=
    (yn_2423) *% (nat_mod_inv (yd_2424)) in 
  (x_2425, y_2426, one_2407, (x_2425) *% (y_2426)).

Definition map_to_curve_elligator2_edwards
  (u_2427 : ed25519_field_element_t)
  : ed_point_t :=
  let st_2428 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    map_to_curve_elligator2 (u_2427) in 
  curve25519_to_edwards25519 (st_2428).

Definition ed_encode_to_curve
  (msg_2429 : byte_seq)
  (dst_2430 : byte_seq)
  : ed_point_result_t :=
  let u_2431 : seq ed25519_field_element_t :=
    ed_hash_to_field (msg_2429) (dst_2430) (usize 1) in 
  let q_2432 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    map_to_curve_elligator2_edwards (seq_index (u_2431) (usize 0)) in 
  @Ok ed_point_t error_t (ed_clear_cofactor (q_2432)).

