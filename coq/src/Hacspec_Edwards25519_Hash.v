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
  (msg_2393 : byte_seq)
  (dst_2394 : byte_seq)
  (len_in_bytes_2395 : uint_size)
  
  : byte_seq_result_t :=
  let ell_2396 : uint_size :=
    (((len_in_bytes_2395) + (b_in_bytes_v)) - (usize 1)) / (b_in_bytes_v) in 
  let result_2397 : (result byte_seq error_t) :=
    @Err byte_seq error_t (ExpandMessageAbort) in 
  let '(result_2397) :=
    if negb ((((ell_2396) >.? (usize 255)) || ((len_in_bytes_2395) >.? (
            usize 65535))) || ((seq_len (dst_2394)) >.? (
          usize 255))):bool then (let dst_prime_2398 : seq uint8 :=
        seq_push (dst_2394) (uint8_from_usize (seq_len (dst_2394))) in 
      let z_pad_2399 : seq uint8 :=
        seq_new_ (default : uint8) (s_in_bytes_v) in 
      let l_i_b_str_2400 : seq uint8 :=
        seq_new_ (default : uint8) (usize 2) in 
      let l_i_b_str_2400 :=
        seq_upd l_i_b_str_2400 (usize 0) (uint8_from_usize ((
              len_in_bytes_2395) / (usize 256))) in 
      let l_i_b_str_2400 :=
        seq_upd l_i_b_str_2400 (usize 1) (uint8_from_usize (
            len_in_bytes_2395)) in 
      let msg_prime_2401 : seq uint8 :=
        seq_concat (seq_concat (seq_concat (seq_concat (z_pad_2399) (
                msg_2393)) (l_i_b_str_2400)) (seq_new_ (default : uint8) (
              usize 1))) (dst_prime_2398) in 
      let b_0_2402 : seq uint8 :=
        seq_from_seq (array_to_seq (hash (msg_prime_2401))) in 
      let b_i_2403 : seq uint8 :=
        seq_from_seq (array_to_seq (hash (seq_concat (seq_push (b_0_2402) (
                secret (@repr WORDSIZE8 1) : int8)) (dst_prime_2398)))) in 
      let uniform_bytes_2404 : seq uint8 :=
        seq_from_seq (b_i_2403) in 
      let '(b_i_2403, uniform_bytes_2404) :=
        foldi (usize 2) ((ell_2396) + (usize 1)) (fun i_2405 '(
            b_i_2403,
            uniform_bytes_2404
          ) =>
          let t_2406 : seq uint8 :=
            seq_from_seq (b_0_2402) in 
          let b_i_2403 :=
            seq_from_seq (array_to_seq (hash (seq_concat (seq_push ((
                      t_2406) seq_xor (b_i_2403)) (uint8_from_usize (i_2405))) (
                  dst_prime_2398)))) in 
          let uniform_bytes_2404 :=
            seq_concat (uniform_bytes_2404) (b_i_2403) in 
          (b_i_2403, uniform_bytes_2404))
        (b_i_2403, uniform_bytes_2404) in 
      let result_2397 :=
        @Ok byte_seq error_t (seq_truncate (uniform_bytes_2404) (
            len_in_bytes_2395)) in 
      (result_2397)) else ((result_2397)) in 
  result_2397.

Definition ed_hash_to_field
  (msg_2407 : byte_seq)
  (dst_2408 : byte_seq)
  (count_2409 : uint_size)
  
  : seq_ed_result_t :=
  let len_in_bytes_2410 : uint_size :=
    (count_2409) * (l_v) in 
  bind (expand_message_xmd (msg_2407) (dst_2408) (len_in_bytes_2410)) (
    fun uniform_bytes_2411 => let output_2412 : seq ed25519_field_element_t :=
      seq_new_ (default : ed25519_field_element_t) (count_2409) in 
    let output_2412 :=
      foldi (usize 0) (count_2409) (fun i_2413 output_2412 =>
        let elm_offset_2414 : uint_size :=
          (l_v) * (i_2413) in 
        let tv_2415 : seq uint8 :=
          seq_slice (uniform_bytes_2411) (elm_offset_2414) (l_v) in 
        let u_i_2416 : ed25519_field_element_t :=
          nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
                nat_mod_from_byte_seq_be (tv_2415) : ed_field_hash_t)) (
              usize 32) (usize 32)) : ed25519_field_element_t in 
        let output_2412 :=
          seq_upd output_2412 (i_2413) (u_i_2416) in 
        (output_2412))
      output_2412 in 
    @Ok seq ed25519_field_element_t error_t (output_2412)).

Definition ed_is_square (x_2417 : ed25519_field_element_t)  : bool :=
  let c1_2418 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (
        p_1_2_v)) : ed25519_field_element_t in 
  let tv_2419 : ed25519_field_element_t :=
    nat_mod_pow_self (x_2417) (c1_2418) in 
  ((tv_2419) =.? (nat_mod_zero )) || ((tv_2419) =.? (nat_mod_one )).

Definition sgn0_m_eq_1 (x_2420 : ed25519_field_element_t)  : bool :=
  ((x_2420) rem (nat_mod_two )) =.? (nat_mod_one ).

Definition ed_clear_cofactor (x_2421 : ed_point_t)  : ed_point_t :=
  point_mul_by_cofactor (x_2421).

Definition cmov
  (a_2422 : ed25519_field_element_t)
  (b_2423 : ed25519_field_element_t)
  (c_2424 : bool)
  
  : ed25519_field_element_t :=
  (if (c_2424):bool then (b_2423) else (a_2422)).

Definition xor (a_2425 : bool) (b_2426 : bool)  : bool :=
  (if (a_2425):bool then ((if (b_2426):bool then (false) else (true))) else ((
        if (b_2426):bool then (true) else (false)))).

Definition curve25519_to_edwards25519 (p_2427 : ed_point_t)  : ed_point_t :=
  let '(s_2428, t_2429, _, _) :=
    point_normalize (p_2427) in 
  let one_2430 : ed25519_field_element_t :=
    nat_mod_one  in 
  let zero_2431 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let tv1_2432 : ed25519_field_element_t :=
    (s_2428) +% (one_2430) in 
  let tv2_2433 : ed25519_field_element_t :=
    (tv1_2432) *% (t_2429) in 
  let tv2_2434 : ed25519_field_element_t :=
    nat_mod_inv (tv2_2433) in 
  let v_2435 : ed25519_field_element_t :=
    (tv2_2434) *% (tv1_2432) in 
  let v_2436 : ed25519_field_element_t :=
    (v_2435) *% (s_2428) in 
  let w_2437 : ed25519_field_element_t :=
    (tv2_2434) *% (t_2429) in 
  let tv1_2438 : ed25519_field_element_t :=
    (s_2428) -% (one_2430) in 
  let w_2439 : ed25519_field_element_t :=
    (w_2437) *% (tv1_2438) in 
  let e_2440 : bool :=
    (tv2_2434) =.? (zero_2431) in 
  let w_2441 : ed25519_field_element_t :=
    cmov (w_2439) (one_2430) (e_2440) in 
  let c_2442 : ed25519_field_element_t :=
    (nat_mod_zero ) -% (nat_mod_from_literal (_) (
        @repr WORDSIZE128 486664) : ed25519_field_element_t) in 
  let sq_2443 : (option ed25519_field_element_t) :=
    sqrt (c_2442) in 
  let v_2444 : ed25519_field_element_t :=
    (v_2436) *% (option_unwrap (sq_2443)) in 
  (v_2444, w_2441, one_2430, (v_2444) *% (w_2441)).

Definition map_to_curve_elligator2
  (u_2445 : ed25519_field_element_t)
  
  : ed_point_t :=
  let j_2446 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (j_v) : ed25519_field_element_t in 
  let z_2447 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (z_v) : ed25519_field_element_t in 
  let one_2448 : ed25519_field_element_t :=
    nat_mod_one  in 
  let zero_2449 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let x1_2450 : ed25519_field_element_t :=
    ((zero_2449) -% (j_2446)) *% (nat_mod_inv ((one_2448) +% (((z_2447) *% (
              u_2445)) *% (u_2445)))) in 
  let '(x1_2450) :=
    if (x1_2450) =.? (zero_2449):bool then (let x1_2450 :=
        (zero_2449) -% (j_2446) in 
      (x1_2450)) else ((x1_2450)) in 
  let gx1_2451 : ed25519_field_element_t :=
    ((((x1_2450) *% (x1_2450)) *% (x1_2450)) +% (((j_2446) *% (x1_2450)) *% (
          x1_2450))) +% (x1_2450) in 
  let x2_2452 : ed25519_field_element_t :=
    ((zero_2449) -% (x1_2450)) -% (j_2446) in 
  let gx2_2453 : ed25519_field_element_t :=
    ((((x2_2452) *% (x2_2452)) *% (x2_2452)) +% ((j_2446) *% ((x2_2452) *% (
            x2_2452)))) +% (x2_2452) in 
  let x_2454 : ed25519_field_element_t :=
    zero_2449 in 
  let y_2455 : ed25519_field_element_t :=
    zero_2449 in 
  let '(x_2454, y_2455) :=
    if ed_is_square (gx1_2451):bool then (let x_2454 :=
        x1_2450 in 
      let y_2455 :=
        option_unwrap (sqrt (gx1_2451)) in 
      let '(y_2455) :=
        if negb (sgn0_m_eq_1 (y_2455)):bool then (let y_2455 :=
            (zero_2449) -% (y_2455) in 
          (y_2455)) else ((y_2455)) in 
      (x_2454, y_2455)) else (let x_2454 :=
        x2_2452 in 
      let y_2455 :=
        option_unwrap (sqrt (gx2_2453)) in 
      let '(y_2455) :=
        if sgn0_m_eq_1 (y_2455):bool then (let y_2455 :=
            (zero_2449) -% (y_2455) in 
          (y_2455)) else ((y_2455)) in 
      (x_2454, y_2455)) in 
  let s_2456 : ed25519_field_element_t :=
    x_2454 in 
  let t_2457 : ed25519_field_element_t :=
    y_2455 in 
  (s_2456, t_2457, one_2448, (s_2456) *% (t_2457)).

Definition map_to_curve_elligator2_straight
  (u_2458 : ed25519_field_element_t)
  
  : ed_point_t :=
  let j_2459 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (j_v) : ed25519_field_element_t in 
  let z_2460 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (z_v) : ed25519_field_element_t in 
  let one_2461 : ed25519_field_element_t :=
    nat_mod_one  in 
  let zero_2462 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let tv1_2463 : ed25519_field_element_t :=
    (u_2458) *% (u_2458) in 
  let tv1_2464 : ed25519_field_element_t :=
    (z_2460) *% (tv1_2463) in 
  let e1_2465 : bool :=
    (tv1_2464) =.? ((zero_2462) -% (one_2461)) in 
  let tv1_2466 : ed25519_field_element_t :=
    cmov (tv1_2464) (zero_2462) (e1_2465) in 
  let x1_2467 : ed25519_field_element_t :=
    (tv1_2466) +% (one_2461) in 
  let x1_2468 : ed25519_field_element_t :=
    nat_mod_inv (x1_2467) in 
  let x1_2469 : ed25519_field_element_t :=
    ((zero_2462) -% (j_2459)) *% (x1_2468) in 
  let gx1_2470 : ed25519_field_element_t :=
    (x1_2469) +% (j_2459) in 
  let gx1_2471 : ed25519_field_element_t :=
    (gx1_2470) *% (x1_2469) in 
  let gx1_2472 : ed25519_field_element_t :=
    (gx1_2471) +% (one_2461) in 
  let gx1_2473 : ed25519_field_element_t :=
    (gx1_2472) *% (x1_2469) in 
  let x2_2474 : ed25519_field_element_t :=
    ((zero_2462) -% (x1_2469)) -% (j_2459) in 
  let gx2_2475 : ed25519_field_element_t :=
    (tv1_2466) *% (gx1_2473) in 
  let e2_2476 : bool :=
    ed_is_square (gx1_2473) in 
  let x_2477 : ed25519_field_element_t :=
    cmov (x2_2474) (x1_2469) (e2_2476) in 
  let y2_2478 : ed25519_field_element_t :=
    cmov (gx2_2475) (gx1_2473) (e2_2476) in 
  let y_2479 : ed25519_field_element_t :=
    option_unwrap (sqrt (y2_2478)) in 
  let e3_2480 : bool :=
    sgn0_m_eq_1 (y_2479) in 
  let y_2481 : ed25519_field_element_t :=
    cmov (y_2479) ((zero_2462) -% (y_2479)) (xor (e2_2476) (e3_2480)) in 
  let s_2482 : ed25519_field_element_t :=
    x_2477 in 
  let t_2483 : ed25519_field_element_t :=
    y_2481 in 
  (s_2482, t_2483, one_2461, (s_2482) *% (t_2483)).

Definition map_to_curve_elligator2_curve25519
  (u_2484 : ed25519_field_element_t)
  
  : ed_point_t :=
  let j_2485 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (j_v) : ed25519_field_element_t in 
  let zero_2486 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let one_2487 : ed25519_field_element_t :=
    nat_mod_one  in 
  let two_2488 : ed25519_field_element_t :=
    nat_mod_two  in 
  let c1_2489 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (
        p_3_8_v)) : ed25519_field_element_t in 
  let c2_2490 : ed25519_field_element_t :=
    nat_mod_pow_self (two_2488) (c1_2489) in 
  let c3_2491 : ed25519_field_element_t :=
    option_unwrap (sqrt ((zero_2486) -% (one_2487))) in 
  let c4_2492 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (
        p_5_8_v)) : ed25519_field_element_t in 
  let tv1_2493 : ed25519_field_element_t :=
    (u_2484) *% (u_2484) in 
  let tv1_2494 : ed25519_field_element_t :=
    (two_2488) *% (tv1_2493) in 
  let xd_2495 : ed25519_field_element_t :=
    (tv1_2494) +% (one_2487) in 
  let x1n_2496 : ed25519_field_element_t :=
    (zero_2486) -% (j_2485) in 
  let tv2_2497 : ed25519_field_element_t :=
    (xd_2495) *% (xd_2495) in 
  let gxd_2498 : ed25519_field_element_t :=
    (tv2_2497) *% (xd_2495) in 
  let gx1_2499 : ed25519_field_element_t :=
    (j_2485) *% (tv1_2494) in 
  let gx1_2500 : ed25519_field_element_t :=
    (gx1_2499) *% (x1n_2496) in 
  let gx1_2501 : ed25519_field_element_t :=
    (gx1_2500) +% (tv2_2497) in 
  let gx1_2502 : ed25519_field_element_t :=
    (gx1_2501) *% (x1n_2496) in 
  let tv3_2503 : ed25519_field_element_t :=
    (gxd_2498) *% (gxd_2498) in 
  let tv2_2504 : ed25519_field_element_t :=
    (tv3_2503) *% (tv3_2503) in 
  let tv3_2505 : ed25519_field_element_t :=
    (tv3_2503) *% (gxd_2498) in 
  let tv3_2506 : ed25519_field_element_t :=
    (tv3_2505) *% (gx1_2502) in 
  let tv2_2507 : ed25519_field_element_t :=
    (tv2_2504) *% (tv3_2506) in 
  let y11_2508 : ed25519_field_element_t :=
    nat_mod_pow_self (tv2_2507) (c4_2492) in 
  let y11_2509 : ed25519_field_element_t :=
    (y11_2508) *% (tv3_2506) in 
  let y12_2510 : ed25519_field_element_t :=
    (y11_2509) *% (c3_2491) in 
  let tv2_2511 : ed25519_field_element_t :=
    (y11_2509) *% (y11_2509) in 
  let tv2_2512 : ed25519_field_element_t :=
    (tv2_2511) *% (gxd_2498) in 
  let e1_2513 : bool :=
    (tv2_2512) =.? (gx1_2502) in 
  let y1_2514 : ed25519_field_element_t :=
    cmov (y12_2510) (y11_2509) (e1_2513) in 
  let x2n_2515 : ed25519_field_element_t :=
    (x1n_2496) *% (tv1_2494) in 
  let y21_2516 : ed25519_field_element_t :=
    (y11_2509) *% (u_2484) in 
  let y21_2517 : ed25519_field_element_t :=
    (y21_2516) *% (c2_2490) in 
  let y22_2518 : ed25519_field_element_t :=
    (y21_2517) *% (c3_2491) in 
  let gx2_2519 : ed25519_field_element_t :=
    (gx1_2502) *% (tv1_2494) in 
  let tv2_2520 : ed25519_field_element_t :=
    (y21_2517) *% (y21_2517) in 
  let tv2_2521 : ed25519_field_element_t :=
    (tv2_2520) *% (gxd_2498) in 
  let e2_2522 : bool :=
    (tv2_2521) =.? (gx2_2519) in 
  let y2_2523 : ed25519_field_element_t :=
    cmov (y22_2518) (y21_2517) (e2_2522) in 
  let tv2_2524 : ed25519_field_element_t :=
    (y1_2514) *% (y1_2514) in 
  let tv2_2525 : ed25519_field_element_t :=
    (tv2_2524) *% (gxd_2498) in 
  let e3_2526 : bool :=
    (tv2_2525) =.? (gx1_2502) in 
  let xn_2527 : ed25519_field_element_t :=
    cmov (x2n_2515) (x1n_2496) (e3_2526) in 
  let y_2528 : ed25519_field_element_t :=
    cmov (y2_2523) (y1_2514) (e3_2526) in 
  let e4_2529 : bool :=
    sgn0_m_eq_1 (y_2528) in 
  let y_2530 : ed25519_field_element_t :=
    cmov (y_2528) ((zero_2486) -% (y_2528)) (xor (e3_2526) (e4_2529)) in 
  (xn_2527, xd_2495, y_2530, one_2487).

Definition map_to_curve_elligator2_edwards25519
  (u_2531 : ed25519_field_element_t)
  
  : ed_point_t :=
  let j_2532 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (j_v) : ed25519_field_element_t in 
  let zero_2533 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let one_2534 : ed25519_field_element_t :=
    nat_mod_one  in 
  let two_2535 : ed25519_field_element_t :=
    nat_mod_two  in 
  let c1_2536 : ed25519_field_element_t :=
    option_unwrap (sqrt ((zero_2533) -% ((j_2532) +% (two_2535)))) in 
  let '(xmn_2537, xmd_2538, ymn_2539, ymd_2540) :=
    map_to_curve_elligator2_curve25519 (u_2531) in 
  let xn_2541 : ed25519_field_element_t :=
    (xmn_2537) *% (ymd_2540) in 
  let xn_2542 : ed25519_field_element_t :=
    (xn_2541) *% (c1_2536) in 
  let xd_2543 : ed25519_field_element_t :=
    (xmd_2538) *% (ymn_2539) in 
  let yn_2544 : ed25519_field_element_t :=
    (xmn_2537) -% (xmd_2538) in 
  let yd_2545 : ed25519_field_element_t :=
    (xmn_2537) +% (xmd_2538) in 
  let tv1_2546 : ed25519_field_element_t :=
    (xd_2543) *% (yd_2545) in 
  let e_2547 : bool :=
    (tv1_2546) =.? (zero_2533) in 
  let xn_2548 : ed25519_field_element_t :=
    cmov (xn_2542) (zero_2533) (e_2547) in 
  let xd_2549 : ed25519_field_element_t :=
    cmov (xd_2543) (one_2534) (e_2547) in 
  let yn_2550 : ed25519_field_element_t :=
    cmov (yn_2544) (one_2534) (e_2547) in 
  let yd_2551 : ed25519_field_element_t :=
    cmov (yd_2545) (one_2534) (e_2547) in 
  let x_2552 : ed25519_field_element_t :=
    (xn_2548) *% (nat_mod_inv (xd_2549)) in 
  let y_2553 : ed25519_field_element_t :=
    (yn_2550) *% (nat_mod_inv (yd_2551)) in 
  (x_2552, y_2553, one_2534, (x_2552) *% (y_2553)).

Definition map_to_curve_elligator2_edwards
  (u_2554 : ed25519_field_element_t)
  
  : ed_point_t :=
  let st_2555 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    map_to_curve_elligator2 (u_2554) in 
  curve25519_to_edwards25519 (st_2555).

Definition ed_encode_to_curve
  (msg_2556 : byte_seq)
  (dst_2557 : byte_seq)
  
  : ed_point_result_t :=
  bind (ed_hash_to_field (msg_2556) (dst_2557) (usize 1)) (fun u_2558 =>
    let q_2559 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      map_to_curve_elligator2_edwards (seq_index (u_2558) (usize 0)) in 
    @Ok ed_point_t error_t (ed_clear_cofactor (q_2559))).

