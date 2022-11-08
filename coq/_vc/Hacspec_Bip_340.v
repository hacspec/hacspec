(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Hacspec_Sha256.

Inductive error_t :=
| InvalidSecretKey : error_t
| InvalidNonceGenerated : error_t
| InvalidPublicKey : error_t
| InvalidXCoordinate : error_t
| InvalidSignature : error_t.

Definition eqb_error_t (x y : error_t) : bool :=
match x with
   | InvalidSecretKey => match y with | InvalidSecretKey=> true | _ => false end
   | InvalidNonceGenerated =>
       match y with
       | InvalidNonceGenerated=> true
       | _ => false
       end
   | InvalidPublicKey => match y with | InvalidPublicKey=> true | _ => false end
   | InvalidXCoordinate =>
       match y with
       | InvalidXCoordinate=> true
       | _ => false
       end
   | InvalidSignature => match y with | InvalidSignature=> true | _ => false end
   end.

Definition eqb_leibniz_error_t (x y : error_t) : eqb_error_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_error_t : EqDec (error_t) :=
Build_EqDec (error_t) (eqb_error_t) (eqb_leibniz_error_t).


Definition field_canvas_t := nseq (int8) (32).
Definition field_element_t :=
  nat_mod 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F.

Definition scalar_canvas_t := nseq (int8) (32).
Definition scalar_t :=
  nat_mod 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141.

Definition big_integer_t := nat_mod pow2 256.

Notation "'affine_point_t'" := ((field_element_t × field_element_t
)) : hacspec_scope.

Definition p_bytes32_t := nseq (int8) (usize 32).

Inductive point_t :=
| Affine : affine_point_t -> point_t
| AtInfinity : point_t.

Definition finite (p_2400 : point_t) : (option affine_point_t) :=
  match p_2400 with
  | Affine (p_2401) => some (p_2401)
  | AtInfinity => @None affine_point_t
  end.

Definition x (p_2402 : affine_point_t) : field_element_t :=
  let '(x_2403, _) :=
    p_2402 in 
  x_2403.

Definition y (p_2404 : affine_point_t) : field_element_t :=
  let '(_, y_2405) :=
    p_2404 in 
  y_2405.

Definition has_even_y (p_2406 : affine_point_t) : bool :=
  ((y (p_2406)) rem (nat_mod_two )) =.? (nat_mod_zero ).

Definition sqrt (y_2407 : field_element_t) : (option field_element_t) :=
  let p1_4_2408 : field_element_t :=
    nat_mod_from_public_byte_seq_be (array_from_list int8 (let l :=
          [
            @repr WORDSIZE8 63;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 191;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 12
          ] in  l)) in 
  let x_2409 : field_element_t :=
    nat_mod_pow_self (y_2407) (p1_4_2408) in 
  (if ((nat_mod_pow_self (x_2409) (nat_mod_two )) =.? (y_2407)):bool then (
      some (x_2409)) else (@None field_element_t)).

Definition lift_x
  (x_2410 : field_element_t)
  : (result affine_point_t error_t) :=
  let one_2411 : field_element_t :=
    nat_mod_one  in 
  let two_2412 : field_element_t :=
    nat_mod_two  in 
  let three_2413 : field_element_t :=
    nat_mod_from_literal (
      0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
      @repr WORDSIZE128 3) : field_element_t in 
  let seven_2414 : field_element_t :=
    nat_mod_from_literal (
      0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
      @repr WORDSIZE128 7) : field_element_t in 
  let y_sq_2415 : field_element_t :=
    (nat_mod_pow_self (x_2410) (three_2413)) +% (seven_2414) in 
  let y_2416 : field_element_t :=
    option_ok_or (sqrt (y_sq_2415)) (InvalidXCoordinate) in 
  let '(y_2416) :=
    if ((y_2416) rem (two_2412)) =.? (one_2411):bool then (let y_2416 :=
        (nat_mod_zero ) -% (y_2416) in 
      (y_2416)) else ((y_2416)) in 
  @Ok affine_point_t error_t ((x_2410, y_2416)).

Definition compute_lam
  (p1_2417 : affine_point_t)
  (p2_2418 : affine_point_t)
  : field_element_t :=
  let three_2419 : field_element_t :=
    nat_mod_from_literal (
      0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
      @repr WORDSIZE128 3) : field_element_t in 
  (if ((p1_2417) !=.? (p2_2418)):bool then (((y (p2_2418)) -% (y (
            p1_2417))) *% (nat_mod_pow_self ((x (p2_2418)) -% (x (p1_2417))) ((
            nat_mod_zero ) -% (nat_mod_two )))) else ((((three_2419) *% (x (
              p1_2417))) *% (x (p1_2417))) *% (nat_mod_pow_self ((
            nat_mod_two ) *% (y (p1_2417))) ((nat_mod_zero ) -% (
            nat_mod_two ))))).

Definition point_add (p1_2420 : point_t) (p2_2421 : point_t) : point_t :=
  let result_2422 : point_t :=
    AtInfinity in 
  let '(result_2422) :=
    if option_is_none (finite (p1_2420)):bool then (let result_2422 :=
        p2_2421 in 
      (result_2422)) else (let '(result_2422) :=
        if option_is_none (finite (p2_2421)):bool then (let result_2422 :=
            p1_2420 in 
          (result_2422)) else (let p1_2423 : (field_element_t × field_element_t
            ) :=
            option_unwrap (finite (p1_2420)) in 
          let p2_2424 : (field_element_t × field_element_t) :=
            option_unwrap (finite (p2_2421)) in 
          let '(result_2422) :=
            if negb (((x (p1_2423)) =.? (x (p2_2424))) && ((y (p1_2423)) !=.? (
                  y (p2_2424)))):bool then (let lam_2425 : field_element_t :=
                compute_lam (p1_2423) (p2_2424) in 
              let x3_2426 : field_element_t :=
                (((lam_2425) *% (lam_2425)) -% (x (p1_2423))) -% (x (
                    p2_2424)) in 
              let result_2422 :=
                Affine ((
                    x3_2426,
                    ((lam_2425) *% ((x (p1_2423)) -% (x3_2426))) -% (y (
                        p1_2423))
                  )) in 
              (result_2422)) else ((result_2422)) in 
          (result_2422)) in 
      (result_2422)) in 
  result_2422.

Definition point_mul (s_2427 : scalar_t) (p_2428 : point_t) : point_t :=
  let p_2429 : point_t :=
    p_2428 in 
  let q_2430 : point_t :=
    AtInfinity in 
  let '(p_2429, q_2430) :=
    foldi (usize 0) (usize 256) (fun i_2431 '(p_2429, q_2430) =>
      let '(q_2430) :=
        if nat_mod_bit (s_2427) (i_2431):bool then (let q_2430 :=
            point_add (q_2430) (p_2429) in 
          (q_2430)) else ((q_2430)) in 
      let p_2429 :=
        point_add (p_2429) (p_2429) in 
      (p_2429, q_2430))
    (p_2429, q_2430) in 
  q_2430.

Definition point_mul_base (s_2432 : scalar_t) : point_t :=
  let gx_2433 : p_bytes32_t :=
    array_from_list int8 (let l :=
        [
          @repr WORDSIZE8 121;
          @repr WORDSIZE8 190;
          @repr WORDSIZE8 102;
          @repr WORDSIZE8 126;
          @repr WORDSIZE8 249;
          @repr WORDSIZE8 220;
          @repr WORDSIZE8 187;
          @repr WORDSIZE8 172;
          @repr WORDSIZE8 85;
          @repr WORDSIZE8 160;
          @repr WORDSIZE8 98;
          @repr WORDSIZE8 149;
          @repr WORDSIZE8 206;
          @repr WORDSIZE8 135;
          @repr WORDSIZE8 11;
          @repr WORDSIZE8 7;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 155;
          @repr WORDSIZE8 252;
          @repr WORDSIZE8 219;
          @repr WORDSIZE8 45;
          @repr WORDSIZE8 206;
          @repr WORDSIZE8 40;
          @repr WORDSIZE8 217;
          @repr WORDSIZE8 89;
          @repr WORDSIZE8 242;
          @repr WORDSIZE8 129;
          @repr WORDSIZE8 91;
          @repr WORDSIZE8 22;
          @repr WORDSIZE8 248;
          @repr WORDSIZE8 23;
          @repr WORDSIZE8 152
        ] in  l) in 
  let gy_2434 : p_bytes32_t :=
    array_from_list int8 (let l :=
        [
          @repr WORDSIZE8 72;
          @repr WORDSIZE8 58;
          @repr WORDSIZE8 218;
          @repr WORDSIZE8 119;
          @repr WORDSIZE8 38;
          @repr WORDSIZE8 163;
          @repr WORDSIZE8 196;
          @repr WORDSIZE8 101;
          @repr WORDSIZE8 93;
          @repr WORDSIZE8 164;
          @repr WORDSIZE8 251;
          @repr WORDSIZE8 252;
          @repr WORDSIZE8 14;
          @repr WORDSIZE8 17;
          @repr WORDSIZE8 8;
          @repr WORDSIZE8 168;
          @repr WORDSIZE8 253;
          @repr WORDSIZE8 23;
          @repr WORDSIZE8 180;
          @repr WORDSIZE8 72;
          @repr WORDSIZE8 166;
          @repr WORDSIZE8 133;
          @repr WORDSIZE8 84;
          @repr WORDSIZE8 25;
          @repr WORDSIZE8 156;
          @repr WORDSIZE8 71;
          @repr WORDSIZE8 208;
          @repr WORDSIZE8 143;
          @repr WORDSIZE8 251;
          @repr WORDSIZE8 16;
          @repr WORDSIZE8 212;
          @repr WORDSIZE8 184
        ] in  l) in 
  let g_2435 : point_t :=
    Affine ((
        nat_mod_from_public_byte_seq_be (gx_2433),
        nat_mod_from_public_byte_seq_be (gy_2434)
      )) in 
  point_mul (s_2432) (g_2435).

Definition bytes32_t := nseq (uint8) (usize 32).

Notation "'secret_key_t'" := (bytes32_t) : hacspec_scope.

Notation "'public_key_t'" := (bytes32_t) : hacspec_scope.

Notation "'message_t'" := (bytes32_t) : hacspec_scope.

Notation "'aux_rand_t'" := (bytes32_t) : hacspec_scope.

Definition signature_t := nseq (uint8) (usize 64).

Definition tagged_hash
  (tag_2436 : public_byte_seq)
  (msg_2437 : byte_seq)
  : bytes32_t :=
  let tag_hash_2438 : seq uint8 :=
    array_to_be_bytes (sha256 (seq_from_public_seq (tag_2436))) in 
  let hash_2439 : sha256_digest_t :=
    sha256 (seq_concat (seq_concat (tag_hash_2438) (tag_hash_2438)) (
        msg_2437)) in 
  array_from_seq (32) (array_to_seq (hash_2439)).

Definition tagged_hash_aux_prefix_t := nseq (int8) (usize 11).

Definition bip0340_aux_v : tagged_hash_aux_prefix_t :=
  array_from_list int8 (let l :=
      [
        @repr WORDSIZE8 66;
        @repr WORDSIZE8 73;
        @repr WORDSIZE8 80;
        @repr WORDSIZE8 48;
        @repr WORDSIZE8 51;
        @repr WORDSIZE8 52;
        @repr WORDSIZE8 48;
        @repr WORDSIZE8 47;
        @repr WORDSIZE8 97;
        @repr WORDSIZE8 117;
        @repr WORDSIZE8 120
      ] in  l).

Definition hash_aux (aux_rand_2440 : aux_rand_t) : bytes32_t :=
  tagged_hash (seq_from_seq (array_to_seq (bip0340_aux_v))) (seq_from_seq (
      aux_rand_2440)).

Definition tagged_hash_nonce_prefix_t := nseq (int8) (usize 13).

Definition bip0340_nonce_v : tagged_hash_nonce_prefix_t :=
  array_from_list int8 (let l :=
      [
        @repr WORDSIZE8 66;
        @repr WORDSIZE8 73;
        @repr WORDSIZE8 80;
        @repr WORDSIZE8 48;
        @repr WORDSIZE8 51;
        @repr WORDSIZE8 52;
        @repr WORDSIZE8 48;
        @repr WORDSIZE8 47;
        @repr WORDSIZE8 110;
        @repr WORDSIZE8 111;
        @repr WORDSIZE8 110;
        @repr WORDSIZE8 99;
        @repr WORDSIZE8 101
      ] in  l).

Definition hash_nonce
  (rand_2441 : bytes32_t)
  (pubkey_2442 : bytes32_t)
  (msg_2443 : message_t)
  : bytes32_t :=
  let c_2444 : byte_seq :=
    seq_concat (seq_concat (seq_from_seq (array_to_seq (rand_2441))) (
        array_to_seq (pubkey_2442))) (msg_2443) in 
  tagged_hash (seq_from_seq (array_to_seq (bip0340_nonce_v))) (c_2444).

Definition tagged_hash_challenge_prefix_t := nseq (int8) (usize 17).

Definition bip0340_challenge_v : tagged_hash_challenge_prefix_t :=
  array_from_list int8 (let l :=
      [
        @repr WORDSIZE8 66;
        @repr WORDSIZE8 73;
        @repr WORDSIZE8 80;
        @repr WORDSIZE8 48;
        @repr WORDSIZE8 51;
        @repr WORDSIZE8 52;
        @repr WORDSIZE8 48;
        @repr WORDSIZE8 47;
        @repr WORDSIZE8 99;
        @repr WORDSIZE8 104;
        @repr WORDSIZE8 97;
        @repr WORDSIZE8 108;
        @repr WORDSIZE8 108;
        @repr WORDSIZE8 101;
        @repr WORDSIZE8 110;
        @repr WORDSIZE8 103;
        @repr WORDSIZE8 101
      ] in  l).

Definition hash_challenge
  (rx_2445 : bytes32_t)
  (pubkey_2446 : bytes32_t)
  (msg_2447 : bytes32_t)
  : bytes32_t :=
  let c_2448 : byte_seq :=
    seq_concat (seq_concat (seq_from_seq (array_to_seq (rx_2445))) (
        array_to_seq (pubkey_2446))) (array_to_seq (msg_2447)) in 
  tagged_hash (seq_from_seq (array_to_seq (bip0340_challenge_v))) (c_2448).

Definition bytes_from_point (p_2449 : affine_point_t) : bytes32_t :=
  let '(x_2450, _) :=
    p_2449 in 
  array_from_seq (32) (nat_mod_to_byte_seq_be (x_2450)).

Definition bytes_from_scalar (x_2451 : scalar_t) : bytes32_t :=
  array_from_seq (32) (nat_mod_to_byte_seq_be (x_2451)).

Definition scalar_from_bytes (b_2452 : bytes32_t) : scalar_t :=
  nat_mod_from_byte_seq_be (array_to_seq (b_2452)) : scalar_t.

Definition scalar_from_bytes_strict (b_2453 : bytes32_t) : (option scalar_t) :=
  let s_2454 : big_integer_t :=
    nat_mod_from_byte_seq_be (array_to_seq (b_2453)) : big_integer_t in 
  let max_scalar_2455 : big_integer_t :=
    nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (
        nat_mod_max_val )) : big_integer_t in 
  (if ((s_2454) >.? (max_scalar_2455)):bool then (@None scalar_t) else (
      @Some scalar_t (nat_mod_from_byte_seq_be (
          array_to_seq (b_2453)) : scalar_t))).

Definition seckey_scalar_from_bytes (b_2456 : bytes32_t) : (option scalar_t) :=
  let s_2457 : scalar_t :=
    scalar_from_bytes_strict (b_2456) in 
  (if ((s_2457) =.? (nat_mod_zero )):bool then (@None scalar_t) else (
      @Some scalar_t (s_2457))).

Definition fieldelem_from_bytes
  (b_2458 : public_key_t)
  : (option field_element_t) :=
  let s_2459 : big_integer_t :=
    nat_mod_from_byte_seq_be (b_2458) : big_integer_t in 
  let max_fe_2460 : big_integer_t :=
    nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (
        nat_mod_max_val )) : big_integer_t in 
  (if ((s_2459) >.? (max_fe_2460)):bool then (@None field_element_t) else (
      @Some field_element_t (nat_mod_from_byte_seq_be (
          b_2458) : field_element_t))).

Definition xor_bytes (b0_2461 : bytes32_t) (b1_2462 : bytes32_t) : bytes32_t :=
  let b_2463 : seq uint8 :=
    seq_new_ (default) (array_len (b0_2461)) in 
  let b_2463 :=
    foldi (usize 0) (array_len (b0_2461)) (fun i_2464 b_2463 =>
      let b_2463 :=
        seq_upd b_2463 (i_2464) ((array_index (b0_2461) (i_2464)) .^ (
            array_index (b1_2462) (i_2464))) in 
      (b_2463))
    b_2463 in 
  array_from_seq (32) (b_2463).

Notation "'pubkey_gen_result_t'" := ((
  result public_key_t error_t)) : hacspec_scope.

Definition pubkey_gen (seckey_2465 : secret_key_t) : pubkey_gen_result_t :=
  let d0_2466 : scalar_t :=
    option_ok_or (seckey_scalar_from_bytes (seckey_2465)) (InvalidSecretKey) in 
  let p_2467 : (field_element_t × field_element_t) :=
    option_unwrap (finite (point_mul_base (d0_2466))) in 
  @Ok public_key_t error_t (bytes_from_point (p_2467)).

Notation "'sign_result_t'" := ((result signature_t error_t)) : hacspec_scope.

Definition sign
  (msg_2468 : message_t)
  (seckey_2469 : secret_key_t)
  (aux_rand_2470 : aux_rand_t)
  : sign_result_t :=
  let d0_2471 : scalar_t :=
    option_ok_or (seckey_scalar_from_bytes (seckey_2469)) (InvalidSecretKey) in 
  let p_2472 : (field_element_t × field_element_t) :=
    option_unwrap (finite (point_mul_base (d0_2471))) in 
  let d_2473 : scalar_t :=
    (if (has_even_y (p_2472)):bool then (d0_2471) else ((nat_mod_zero ) -% (
          d0_2471))) in 
  let t_2474 : bytes32_t :=
    xor_bytes (bytes_from_scalar (d_2473)) (hash_aux (aux_rand_2470)) in 
  let k0_2475 : scalar_t :=
    scalar_from_bytes (hash_nonce (t_2474) (bytes_from_point (p_2472)) (
        msg_2468)) in 
  let 'tt :=
    if (k0_2475) =.? (nat_mod_zero ):bool then (let _ : signature_t :=
        @Err signature_t error_t (InvalidNonceGenerated) in 
      tt) else (tt) in 
  let r_2476 : (field_element_t × field_element_t) :=
    option_unwrap (finite (point_mul_base (k0_2475))) in 
  let k_2477 : scalar_t :=
    (if (has_even_y (r_2476)):bool then (k0_2475) else ((nat_mod_zero ) -% (
          k0_2475))) in 
  let e_2478 : scalar_t :=
    scalar_from_bytes (hash_challenge (bytes_from_point (r_2476)) (
        bytes_from_point (p_2472)) (msg_2468)) in 
  let sig_2479 : signature_t :=
    array_update (array_update (array_new_ (default) (64)) (usize 0) (
        array_to_seq (bytes_from_point (r_2476)))) (usize 32) (
      array_to_seq (bytes_from_scalar ((k_2477) +% ((e_2478) *% (d_2473))))) in 
  let _ : unit :=
    verify (msg_2468) (bytes_from_point (p_2472)) (sig_2479) in 
  @Ok signature_t error_t (sig_2479).

Notation "'verification_result_t'" := ((result unit error_t)) : hacspec_scope.

Definition verify
  (msg_2480 : message_t)
  (pubkey_2481 : public_key_t)
  (sig_2482 : signature_t)
  : verification_result_t :=
  let p_x_2483 : field_element_t :=
    option_ok_or (fieldelem_from_bytes (pubkey_2481)) (InvalidPublicKey) in 
  let p_2484 : affine_point_t :=
    lift_x (p_x_2483) in 
  let r_2485 : field_element_t :=
    option_ok_or (fieldelem_from_bytes (array_from_slice (default) (32) (
          array_to_seq (sig_2482)) (usize 0) (usize 32))) (InvalidSignature) in 
  let s_2486 : scalar_t :=
    option_ok_or (scalar_from_bytes_strict (array_from_slice (default) (32) (
          array_to_seq (sig_2482)) (usize 32) (usize 32))) (
      InvalidSignature) in 
  let e_2487 : scalar_t :=
    scalar_from_bytes (hash_challenge (array_from_slice (default) (32) (
          array_to_seq (sig_2482)) (usize 0) (usize 32)) (bytes_from_point (
          p_2484)) (msg_2480)) in 
  let r_p_2488 : (field_element_t × field_element_t) :=
    option_ok_or (finite (point_add (point_mul_base (s_2486)) (point_mul ((
              nat_mod_zero ) -% (e_2487)) (Affine (p_2484))))) (
      InvalidSignature) in 
  (if ((negb (has_even_y (r_p_2488))) || ((x (r_p_2488)) !=.? (
          r_2485))):bool then (@Err unit error_t (InvalidSignature)) else (
      @Ok unit error_t (tt))).

