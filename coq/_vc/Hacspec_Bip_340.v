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

Notation "'affine_point_t'" := ((field_element_t '× field_element_t
)) : hacspec_scope.

Definition p_bytes32_t := nseq (int8) (usize 32).

Inductive point_t :=
| Affine : affine_point_t -> point_t
| AtInfinity : point_t.

Definition finite (p_2482 : point_t) : (option affine_point_t) :=
  match p_2482 with
  | Affine (p_2483) => some (p_2483)
  | AtInfinity => @None affine_point_t
  end.

Definition x (p_2484 : affine_point_t) : field_element_t :=
  let '(x_2485, _) :=
    p_2484 in 
  x_2485.

Definition y (p_2486 : affine_point_t) : field_element_t :=
  let '(_, y_2487) :=
    p_2486 in 
  y_2487.

Definition has_even_y (p_2488 : affine_point_t) : bool :=
  ((y (p_2488)) rem (nat_mod_two )) =.? (nat_mod_zero ).

Definition sqrt (y_2489 : field_element_t) : (option field_element_t) :=
  let p1_4_2490 : field_element_t :=
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
  let x_2491 : field_element_t :=
    nat_mod_pow_self (y_2489) (p1_4_2490) in 
  (if ((nat_mod_pow_self (x_2491) (nat_mod_two )) =.? (y_2489)):bool then (
      some (x_2491)) else (@None field_element_t)).

Definition lift_x
  (x_2492 : field_element_t)
  : (result affine_point_t error_t) :=
  let one_2493 : field_element_t :=
    nat_mod_one  in 
  let two_2494 : field_element_t :=
    nat_mod_two  in 
  let three_2495 : field_element_t :=
    nat_mod_from_literal (
      0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
      @repr WORDSIZE128 3) : field_element_t in 
  let seven_2496 : field_element_t :=
    nat_mod_from_literal (
      0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
      @repr WORDSIZE128 7) : field_element_t in 
  let y_sq_2497 : field_element_t :=
    (nat_mod_pow_self (x_2492) (three_2495)) +% (seven_2496) in 
  bind (option_ok_or (sqrt (y_sq_2497)) (InvalidXCoordinate)) (fun y_2498 =>
    let '(y_2498) :=
      if ((y_2498) rem (two_2494)) =.? (one_2493):bool then (let y_2498 :=
          (nat_mod_zero ) -% (y_2498) in 
        (y_2498)) else ((y_2498)) in 
    @Ok affine_point_t error_t ((x_2492, y_2498))).

Definition compute_lam
  (p1_2499 : affine_point_t)
  (p2_2500 : affine_point_t)
  : field_element_t :=
  let three_2501 : field_element_t :=
    nat_mod_from_literal (
      0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
      @repr WORDSIZE128 3) : field_element_t in 
  (if ((p1_2499) !=.? (p2_2500)):bool then (((y (p2_2500)) -% (y (
            p1_2499))) *% (nat_mod_pow_self ((x (p2_2500)) -% (x (p1_2499))) ((
            nat_mod_zero ) -% (nat_mod_two )))) else ((((three_2501) *% (x (
              p1_2499))) *% (x (p1_2499))) *% (nat_mod_pow_self ((
            nat_mod_two ) *% (y (p1_2499))) ((nat_mod_zero ) -% (
            nat_mod_two ))))).

Definition point_add (p1_2502 : point_t) (p2_2503 : point_t) : point_t :=
  let result_2504 : point_t :=
    AtInfinity in 
  let '(result_2504) :=
    if option_is_none (finite (p1_2502)):bool then (let result_2504 :=
        p2_2503 in 
      (result_2504)) else (let '(result_2504) :=
        if option_is_none (finite (p2_2503)):bool then (let result_2504 :=
            p1_2502 in 
          (result_2504)) else (let p1_2505 : (
              field_element_t '×
              field_element_t
            ) :=
            option_unwrap (finite (p1_2502)) in 
          let p2_2506 : (field_element_t '× field_element_t) :=
            option_unwrap (finite (p2_2503)) in 
          let '(result_2504) :=
            if negb (((x (p1_2505)) =.? (x (p2_2506))) && ((y (p1_2505)) !=.? (
                  y (p2_2506)))):bool then (let lam_2507 : field_element_t :=
                compute_lam (p1_2505) (p2_2506) in 
              let x3_2508 : field_element_t :=
                (((lam_2507) *% (lam_2507)) -% (x (p1_2505))) -% (x (
                    p2_2506)) in 
              let result_2504 :=
                Affine ((
                    x3_2508,
                    ((lam_2507) *% ((x (p1_2505)) -% (x3_2508))) -% (y (
                        p1_2505))
                  )) in 
              (result_2504)) else ((result_2504)) in 
          (result_2504)) in 
      (result_2504)) in 
  result_2504.

Definition point_mul (s_2509 : scalar_t) (p_2510 : point_t) : point_t :=
  let p_2511 : point_t :=
    p_2510 in 
  let q_2512 : point_t :=
    AtInfinity in 
  let '(p_2511, q_2512) :=
    foldi (usize 0) (usize 256) (fun i_2513 '(p_2511, q_2512) =>
      let '(q_2512) :=
        if nat_mod_bit (s_2509) (i_2513):bool then (let q_2512 :=
            point_add (q_2512) (p_2511) in 
          (q_2512)) else ((q_2512)) in 
      let p_2511 :=
        point_add (p_2511) (p_2511) in 
      (p_2511, q_2512))
    (p_2511, q_2512) in 
  q_2512.

Definition point_mul_base (s_2514 : scalar_t) : point_t :=
  let gx_2515 : p_bytes32_t :=
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
  let gy_2516 : p_bytes32_t :=
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
  let g_2517 : point_t :=
    Affine ((
        nat_mod_from_public_byte_seq_be (gx_2515),
        nat_mod_from_public_byte_seq_be (gy_2516)
      )) in 
  point_mul (s_2514) (g_2517).

Definition bytes32_t := nseq (uint8) (usize 32).

Notation "'secret_key_t'" := (bytes32_t) : hacspec_scope.

Notation "'public_key_t'" := (bytes32_t) : hacspec_scope.

Notation "'message_t'" := (bytes32_t) : hacspec_scope.

Notation "'aux_rand_t'" := (bytes32_t) : hacspec_scope.

Definition signature_t := nseq (uint8) (usize 64).

Definition tagged_hash
  (tag_2518 : public_byte_seq)
  (msg_2519 : byte_seq)
  : bytes32_t :=
  let tag_hash_2520 : seq uint8 :=
    array_to_be_bytes (sha256 (seq_from_public_seq (tag_2518))) in 
  let hash_2521 : sha256_digest_t :=
    sha256 (seq_concat (seq_concat (tag_hash_2520) (tag_hash_2520)) (
        msg_2519)) in 
  array_from_seq (32) (array_to_seq (hash_2521)).

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

Definition hash_aux (aux_rand_2522 : aux_rand_t) : bytes32_t :=
  tagged_hash (seq_from_seq (array_to_seq (bip0340_aux_v))) (seq_from_seq (
      aux_rand_2522)).

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
  (rand_2523 : bytes32_t)
  (pubkey_2524 : bytes32_t)
  (msg_2525 : message_t)
  : bytes32_t :=
  let c_2526 : byte_seq :=
    seq_concat (seq_concat (seq_from_seq (array_to_seq (rand_2523))) (
        array_to_seq (pubkey_2524))) (msg_2525) in 
  tagged_hash (seq_from_seq (array_to_seq (bip0340_nonce_v))) (c_2526).

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
  (rx_2527 : bytes32_t)
  (pubkey_2528 : bytes32_t)
  (msg_2529 : bytes32_t)
  : bytes32_t :=
  let c_2530 : byte_seq :=
    seq_concat (seq_concat (seq_from_seq (array_to_seq (rx_2527))) (
        array_to_seq (pubkey_2528))) (array_to_seq (msg_2529)) in 
  tagged_hash (seq_from_seq (array_to_seq (bip0340_challenge_v))) (c_2530).

Definition bytes_from_point (p_2531 : affine_point_t) : bytes32_t :=
  let '(x_2532, _) :=
    p_2531 in 
  array_from_seq (32) (nat_mod_to_byte_seq_be (x_2532)).

Definition bytes_from_scalar (x_2533 : scalar_t) : bytes32_t :=
  array_from_seq (32) (nat_mod_to_byte_seq_be (x_2533)).

Definition scalar_from_bytes (b_2534 : bytes32_t) : scalar_t :=
  nat_mod_from_byte_seq_be (array_to_seq (b_2534)) : scalar_t.

Definition scalar_from_bytes_strict (b_2535 : bytes32_t) : (option scalar_t) :=
  let s_2536 : big_integer_t :=
    nat_mod_from_byte_seq_be (array_to_seq (b_2535)) : big_integer_t in 
  let max_scalar_2537 : big_integer_t :=
    nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (
        nat_mod_max_val )) : big_integer_t in 
  (if ((s_2536) >.? (max_scalar_2537)):bool then (@None scalar_t) else (
      @Some scalar_t (nat_mod_from_byte_seq_be (
          array_to_seq (b_2535)) : scalar_t))).

Definition seckey_scalar_from_bytes (b_2538 : bytes32_t) : (option scalar_t) :=
  bind (scalar_from_bytes_strict (b_2538)) (fun s_2539 => (if ((s_2539) =.? (
          nat_mod_zero )):bool then (@None scalar_t) else (@Some scalar_t (
          s_2539)))).

Definition fieldelem_from_bytes
  (b_2540 : public_key_t)
  : (option field_element_t) :=
  let s_2541 : big_integer_t :=
    nat_mod_from_byte_seq_be (b_2540) : big_integer_t in 
  let max_fe_2542 : big_integer_t :=
    nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (
        nat_mod_max_val )) : big_integer_t in 
  (if ((s_2541) >.? (max_fe_2542)):bool then (@None field_element_t) else (
      @Some field_element_t (nat_mod_from_byte_seq_be (
          b_2540) : field_element_t))).

Definition xor_bytes (b0_2543 : bytes32_t) (b1_2544 : bytes32_t) : bytes32_t :=
  let b_2545 : seq uint8 :=
    seq_new_ (default : uint8) (array_len (b0_2543)) in 
  let b_2545 :=
    foldi (usize 0) (array_len (b0_2543)) (fun i_2546 b_2545 =>
      let b_2545 :=
        seq_upd b_2545 (i_2546) ((array_index (b0_2543) (i_2546)) .^ (
            array_index (b1_2544) (i_2546))) in 
      (b_2545))
    b_2545 in 
  array_from_seq (32) (b_2545).

Notation "'pubkey_gen_result_t'" := ((
  result public_key_t error_t)) : hacspec_scope.

Definition pubkey_gen (seckey_2547 : secret_key_t) : pubkey_gen_result_t :=
  bind (option_ok_or (seckey_scalar_from_bytes (seckey_2547)) (
      InvalidSecretKey)) (fun d0_2548 => let p_2549 : (
        field_element_t '×
        field_element_t
      ) :=
      option_unwrap (finite (point_mul_base (d0_2548))) in 
    @Ok public_key_t error_t (bytes_from_point (p_2549))).

Notation "'sign_result_t'" := ((result signature_t error_t)) : hacspec_scope.

Definition sign
  (msg_2550 : message_t)
  (seckey_2551 : secret_key_t)
  (aux_rand_2552 : aux_rand_t)
  : sign_result_t :=
  bind (option_ok_or (seckey_scalar_from_bytes (seckey_2551)) (
      InvalidSecretKey)) (fun d0_2553 => let p_2554 : (
        field_element_t '×
        field_element_t
      ) :=
      option_unwrap (finite (point_mul_base (d0_2553))) in 
    let d_2555 : scalar_t :=
      (if (has_even_y (p_2554)):bool then (d0_2553) else ((nat_mod_zero ) -% (
            d0_2553))) in 
    let t_2556 : bytes32_t :=
      xor_bytes (bytes_from_scalar (d_2555)) (hash_aux (aux_rand_2552)) in 
    let k0_2557 : scalar_t :=
      scalar_from_bytes (hash_nonce (t_2556) (bytes_from_point (p_2554)) (
          msg_2550)) in 
    ifbnd (k0_2557) =.? (nat_mod_zero ) : bool
    thenbnd (bind (@Err signature_t error_t (InvalidNonceGenerated)) (fun _ =>
        @Ok unit error_t (tt)))
    else (tt) >> (fun 'tt =>
    let r_2558 : (field_element_t '× field_element_t) :=
      option_unwrap (finite (point_mul_base (k0_2557))) in 
    let k_2559 : scalar_t :=
      (if (has_even_y (r_2558)):bool then (k0_2557) else ((nat_mod_zero ) -% (
            k0_2557))) in 
    let e_2560 : scalar_t :=
      scalar_from_bytes (hash_challenge (bytes_from_point (r_2558)) (
          bytes_from_point (p_2554)) (msg_2550)) in 
    let sig_2561 : signature_t :=
      array_update (array_update (array_new_ (default : uint8) (64)) (usize 0) (
          array_to_seq (bytes_from_point (r_2558)))) (usize 32) (
        array_to_seq (bytes_from_scalar ((k_2559) +% ((e_2560) *% (
              d_2555))))) in 
    bind (verify (msg_2550) (bytes_from_point (p_2554)) (sig_2561)) (fun _ =>
      @Ok signature_t error_t (sig_2561)))).

Notation "'verification_result_t'" := ((result unit error_t)) : hacspec_scope.

Definition verify
  (msg_2562 : message_t)
  (pubkey_2563 : public_key_t)
  (sig_2564 : signature_t)
  : verification_result_t :=
  bind (option_ok_or (fieldelem_from_bytes (pubkey_2563)) (InvalidPublicKey)) (
    fun p_x_2565 => bind (lift_x (p_x_2565)) (fun p_2566 => bind (option_ok_or (
          fieldelem_from_bytes (array_from_slice (default : uint8) (32) (
              array_to_seq (sig_2564)) (usize 0) (usize 32))) (
          InvalidSignature)) (fun r_2567 => bind (option_ok_or (
            scalar_from_bytes_strict (array_from_slice (default : uint8) (32) (
                array_to_seq (sig_2564)) (usize 32) (usize 32))) (
            InvalidSignature)) (fun s_2568 => let e_2569 : scalar_t :=
            scalar_from_bytes (hash_challenge (array_from_slice (
                  default : uint8) (32) (array_to_seq (sig_2564)) (usize 0) (
                  usize 32)) (bytes_from_point (p_2566)) (msg_2562)) in 
          bind (option_ok_or (finite (point_add (point_mul_base (s_2568)) (
                  point_mul ((nat_mod_zero ) -% (e_2569)) (Affine (p_2566))))) (
              InvalidSignature)) (fun r_p_2570 => (if ((negb (has_even_y (
                      r_p_2570))) || ((x (r_p_2570)) !=.? (r_2567))):bool then (
                @Err unit error_t (InvalidSignature)) else (@Ok unit error_t (
                  tt)))))))).

