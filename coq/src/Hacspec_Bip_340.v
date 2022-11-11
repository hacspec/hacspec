(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
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

Definition finite (p_2458 : point_t) : (option affine_point_t) :=
  match p_2458 with
  | Affine (p_2459) => some (p_2459)
  | AtInfinity => @None affine_point_t
  end.

Definition x (p_2460 : affine_point_t) : field_element_t :=
  let '(x_2461, _) :=
    p_2460 in 
  x_2461.

Definition y (p_2462 : affine_point_t) : field_element_t :=
  let '(_, y_2463) :=
    p_2462 in 
  y_2463.

Definition has_even_y (p_2464 : affine_point_t) : bool :=
  ((y (p_2464)) rem (nat_mod_two )) =.? (nat_mod_zero ).

Definition sqrt (y_2465 : field_element_t) : (option field_element_t) :=
  let p1_4_2466 : field_element_t :=
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
  let x_2467 : field_element_t :=
    nat_mod_pow_self (y_2465) (p1_4_2466) in 
  (if ((nat_mod_pow_self (x_2467) (nat_mod_two )) =.? (y_2465)):bool then (
      some (x_2467)) else (@None field_element_t)).

Definition lift_x
  (x_2468 : field_element_t)
  : (result affine_point_t error_t) :=
  let one_2469 : field_element_t :=
    nat_mod_one  in 
  let two_2470 : field_element_t :=
    nat_mod_two  in 
  let three_2471 : field_element_t :=
    nat_mod_from_literal (
      0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
      @repr WORDSIZE128 3) : field_element_t in 
  let seven_2472 : field_element_t :=
    nat_mod_from_literal (
      0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
      @repr WORDSIZE128 7) : field_element_t in 
  let y_sq_2473 : field_element_t :=
    (nat_mod_pow_self (x_2468) (three_2471)) +% (seven_2472) in 
  let y_2474 : field_element_t :=
    option_ok_or (sqrt (y_sq_2473)) (InvalidXCoordinate) in 
  let '(y_2474) :=
    if ((y_2474) rem (two_2470)) =.? (one_2469):bool then (let y_2474 :=
        (nat_mod_zero ) -% (y_2474) in 
      (y_2474)) else ((y_2474)) in 
  @Ok affine_point_t error_t ((x_2468, y_2474)).

Definition compute_lam
  (p1_2475 : affine_point_t)
  (p2_2476 : affine_point_t)
  : field_element_t :=
  let three_2477 : field_element_t :=
    nat_mod_from_literal (
      0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
      @repr WORDSIZE128 3) : field_element_t in 
  (if ((p1_2475) !=.? (p2_2476)):bool then (((y (p2_2476)) -% (y (
            p1_2475))) *% (nat_mod_pow_self ((x (p2_2476)) -% (x (p1_2475))) ((
            nat_mod_zero ) -% (nat_mod_two )))) else ((((three_2477) *% (x (
              p1_2475))) *% (x (p1_2475))) *% (nat_mod_pow_self ((
            nat_mod_two ) *% (y (p1_2475))) ((nat_mod_zero ) -% (
            nat_mod_two ))))).

Definition point_add (p1_2478 : point_t) (p2_2479 : point_t) : point_t :=
  let result_2480 : point_t :=
    AtInfinity in 
  let '(result_2480) :=
    if option_is_none (finite (p1_2478)):bool then (let result_2480 :=
        p2_2479 in 
      (result_2480)) else (let '(result_2480) :=
        if option_is_none (finite (p2_2479)):bool then (let result_2480 :=
            p1_2478 in 
          (result_2480)) else (let p1_2481 : (field_element_t × field_element_t
            ) :=
            option_unwrap (finite (p1_2478)) in 
          let p2_2482 : (field_element_t × field_element_t) :=
            option_unwrap (finite (p2_2479)) in 
          let '(result_2480) :=
            if negb (((x (p1_2481)) =.? (x (p2_2482))) && ((y (p1_2481)) !=.? (
                  y (p2_2482)))):bool then (let lam_2483 : field_element_t :=
                compute_lam (p1_2481) (p2_2482) in 
              let x3_2484 : field_element_t :=
                (((lam_2483) *% (lam_2483)) -% (x (p1_2481))) -% (x (
                    p2_2482)) in 
              let result_2480 :=
                Affine ((
                    x3_2484,
                    ((lam_2483) *% ((x (p1_2481)) -% (x3_2484))) -% (y (
                        p1_2481))
                  )) in 
              (result_2480)) else ((result_2480)) in 
          (result_2480)) in 
      (result_2480)) in 
  result_2480.

Definition point_mul (s_2485 : scalar_t) (p_2486 : point_t) : point_t :=
  let p_2487 : point_t :=
    p_2486 in 
  let q_2488 : point_t :=
    AtInfinity in 
  let '(p_2487, q_2488) :=
    foldi (usize 0) (usize 256) (fun i_2489 '(p_2487, q_2488) =>
      let '(q_2488) :=
        if nat_mod_bit (s_2485) (i_2489):bool then (let q_2488 :=
            point_add (q_2488) (p_2487) in 
          (q_2488)) else ((q_2488)) in 
      let p_2487 :=
        point_add (p_2487) (p_2487) in 
      (p_2487, q_2488))
    (p_2487, q_2488) in 
  q_2488.

Definition point_mul_base (s_2490 : scalar_t) : point_t :=
  let gx_2491 : p_bytes32_t :=
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
  let gy_2492 : p_bytes32_t :=
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
  let g_2493 : point_t :=
    Affine ((
        nat_mod_from_public_byte_seq_be (gx_2491),
        nat_mod_from_public_byte_seq_be (gy_2492)
      )) in 
  point_mul (s_2490) (g_2493).

Definition bytes32_t := nseq (uint8) (usize 32).

Notation "'secret_key_t'" := (bytes32_t) : hacspec_scope.

Notation "'public_key_t'" := (bytes32_t) : hacspec_scope.

Notation "'message_t'" := (bytes32_t) : hacspec_scope.

Notation "'aux_rand_t'" := (bytes32_t) : hacspec_scope.

Definition signature_t := nseq (uint8) (usize 64).

Definition tagged_hash
  (tag_2494 : public_byte_seq)
  (msg_2495 : byte_seq)
  : bytes32_t :=
  let tag_hash_2496 : seq uint8 :=
    array_to_be_bytes (sha256 (seq_from_public_seq (tag_2494))) in 
  let hash_2497 : sha256_digest_t :=
    sha256 (seq_concat (seq_concat (tag_hash_2496) (tag_hash_2496)) (
        msg_2495)) in 
  array_from_seq (32) (array_to_seq (hash_2497)).

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

Definition hash_aux (aux_rand_2498 : aux_rand_t) : bytes32_t :=
  tagged_hash (seq_from_seq (array_to_seq (bip0340_aux_v))) (seq_from_seq (
      aux_rand_2498)).

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
  (rand_2499 : bytes32_t)
  (pubkey_2500 : bytes32_t)
  (msg_2501 : message_t)
  : bytes32_t :=
  let c_2502 : byte_seq :=
    seq_concat (seq_concat (seq_from_seq (array_to_seq (rand_2499))) (
        array_to_seq (pubkey_2500))) (msg_2501) in 
  tagged_hash (seq_from_seq (array_to_seq (bip0340_nonce_v))) (c_2502).

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
  (rx_2503 : bytes32_t)
  (pubkey_2504 : bytes32_t)
  (msg_2505 : bytes32_t)
  : bytes32_t :=
  let c_2506 : byte_seq :=
    seq_concat (seq_concat (seq_from_seq (array_to_seq (rx_2503))) (
        array_to_seq (pubkey_2504))) (array_to_seq (msg_2505)) in 
  tagged_hash (seq_from_seq (array_to_seq (bip0340_challenge_v))) (c_2506).

Definition bytes_from_point (p_2507 : affine_point_t) : bytes32_t :=
  let '(x_2508, _) :=
    p_2507 in 
  array_from_seq (32) (nat_mod_to_byte_seq_be (x_2508)).

Definition bytes_from_scalar (x_2509 : scalar_t) : bytes32_t :=
  array_from_seq (32) (nat_mod_to_byte_seq_be (x_2509)).

Definition scalar_from_bytes (b_2510 : bytes32_t) : scalar_t :=
  nat_mod_from_byte_seq_be (array_to_seq (b_2510)) : scalar_t.

Definition scalar_from_bytes_strict (b_2511 : bytes32_t) : (option scalar_t) :=
  let s_2512 : big_integer_t :=
    nat_mod_from_byte_seq_be (array_to_seq (b_2511)) : big_integer_t in 
  let max_scalar_2513 : big_integer_t :=
    nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (
        nat_mod_max_val )) : big_integer_t in 
  (if ((s_2512) >.? (max_scalar_2513)):bool then (@None scalar_t) else (
      @Some scalar_t (nat_mod_from_byte_seq_be (
          array_to_seq (b_2511)) : scalar_t))).

Definition seckey_scalar_from_bytes (b_2514 : bytes32_t) : (option scalar_t) :=
  let s_2515 : scalar_t :=
    scalar_from_bytes_strict (b_2514) in 
  (if ((s_2515) =.? (nat_mod_zero )):bool then (@None scalar_t) else (
      @Some scalar_t (s_2515))).

Definition fieldelem_from_bytes
  (b_2516 : public_key_t)
  : (option field_element_t) :=
  let s_2517 : big_integer_t :=
    nat_mod_from_byte_seq_be (b_2516) : big_integer_t in 
  let max_fe_2518 : big_integer_t :=
    nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (
        nat_mod_max_val )) : big_integer_t in 
  (if ((s_2517) >.? (max_fe_2518)):bool then (@None field_element_t) else (
      @Some field_element_t (nat_mod_from_byte_seq_be (
          b_2516) : field_element_t))).

Definition xor_bytes (b0_2519 : bytes32_t) (b1_2520 : bytes32_t) : bytes32_t :=
  let b_2521 : seq uint8 :=
    seq_new_ (default : uint8) (array_len (b0_2519)) in 
  let b_2521 :=
    foldi (usize 0) (array_len (b0_2519)) (fun i_2522 b_2521 =>
      let b_2521 :=
        seq_upd b_2521 (i_2522) ((array_index (b0_2519) (i_2522)) .^ (
            array_index (b1_2520) (i_2522))) in 
      (b_2521))
    b_2521 in 
  array_from_seq (32) (b_2521).

Notation "'pubkey_gen_result_t'" := ((
  result public_key_t error_t)) : hacspec_scope.

Definition pubkey_gen (seckey_2523 : secret_key_t) : pubkey_gen_result_t :=
  let d0_2524 : scalar_t :=
    option_ok_or (seckey_scalar_from_bytes (seckey_2523)) (InvalidSecretKey) in 
  let p_2525 : (field_element_t × field_element_t) :=
    option_unwrap (finite (point_mul_base (d0_2524))) in 
  @Ok public_key_t error_t (bytes_from_point (p_2525)).

Notation "'sign_result_t'" := ((result signature_t error_t)) : hacspec_scope.

Definition sign
  (msg_2526 : message_t)
  (seckey_2527 : secret_key_t)
  (aux_rand_2528 : aux_rand_t)
  : sign_result_t :=
  let d0_2529 : scalar_t :=
    option_ok_or (seckey_scalar_from_bytes (seckey_2527)) (InvalidSecretKey) in 
  let p_2530 : (field_element_t × field_element_t) :=
    option_unwrap (finite (point_mul_base (d0_2529))) in 
  let d_2531 : scalar_t :=
    (if (has_even_y (p_2530)):bool then (d0_2529) else ((nat_mod_zero ) -% (
          d0_2529))) in 
  let t_2532 : bytes32_t :=
    xor_bytes (bytes_from_scalar (d_2531)) (hash_aux (aux_rand_2528)) in 
  let k0_2533 : scalar_t :=
    scalar_from_bytes (hash_nonce (t_2532) (bytes_from_point (p_2530)) (
        msg_2526)) in 
  let 'tt :=
    if (k0_2533) =.? (nat_mod_zero ):bool then (let _ : signature_t :=
        @Err signature_t error_t (InvalidNonceGenerated) in 
      tt) else (tt) in 
  let r_2534 : (field_element_t × field_element_t) :=
    option_unwrap (finite (point_mul_base (k0_2533))) in 
  let k_2535 : scalar_t :=
    (if (has_even_y (r_2534)):bool then (k0_2533) else ((nat_mod_zero ) -% (
          k0_2533))) in 
  let e_2536 : scalar_t :=
    scalar_from_bytes (hash_challenge (bytes_from_point (r_2534)) (
        bytes_from_point (p_2530)) (msg_2526)) in 
  let sig_2537 : signature_t :=
    array_update (array_update (array_new_ (default : uint8) (64)) (usize 0) (
        array_to_seq (bytes_from_point (r_2534)))) (usize 32) (
      array_to_seq (bytes_from_scalar ((k_2535) +% ((e_2536) *% (d_2531))))) in 
  let _ : unit :=
    verify (msg_2526) (bytes_from_point (p_2530)) (sig_2537) in 
  @Ok signature_t error_t (sig_2537).

Notation "'verification_result_t'" := ((result unit error_t)) : hacspec_scope.

Definition verify
  (msg_2538 : message_t)
  (pubkey_2539 : public_key_t)
  (sig_2540 : signature_t)
  : verification_result_t :=
  let p_x_2541 : field_element_t :=
    option_ok_or (fieldelem_from_bytes (pubkey_2539)) (InvalidPublicKey) in 
  let p_2542 : affine_point_t :=
    lift_x (p_x_2541) in 
  let r_2543 : field_element_t :=
    option_ok_or (fieldelem_from_bytes (array_from_slice (default : uint8) (
          32) (array_to_seq (sig_2540)) (usize 0) (usize 32))) (
      InvalidSignature) in 
  let s_2544 : scalar_t :=
    option_ok_or (scalar_from_bytes_strict (array_from_slice (default : uint8) (
          32) (array_to_seq (sig_2540)) (usize 32) (usize 32))) (
      InvalidSignature) in 
  let e_2545 : scalar_t :=
    scalar_from_bytes (hash_challenge (array_from_slice (default : uint8) (32) (
          array_to_seq (sig_2540)) (usize 0) (usize 32)) (bytes_from_point (
          p_2542)) (msg_2538)) in 
  let r_p_2546 : (field_element_t × field_element_t) :=
    option_ok_or (finite (point_add (point_mul_base (s_2544)) (point_mul ((
              nat_mod_zero ) -% (e_2545)) (Affine (p_2542))))) (
      InvalidSignature) in 
  (if ((negb (has_even_y (r_p_2546))) || ((x (r_p_2546)) !=.? (
          r_2543))):bool then (@Err unit error_t (InvalidSignature)) else (
      @Ok unit error_t (tt))).

