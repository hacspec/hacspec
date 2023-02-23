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

Definition finite (p_2658 : point_t)  : (option affine_point_t) :=
  match p_2658 with
  | Affine (p_2659) => some (p_2659)
  | AtInfinity => @None affine_point_t
  end.

Definition x (p_2660 : affine_point_t)  : field_element_t :=
  let '(x_2661, _) :=
    p_2660 in 
  x_2661.

Definition y (p_2662 : affine_point_t)  : field_element_t :=
  let '(_, y_2663) :=
    p_2662 in 
  y_2663.

Definition has_even_y (p_2664 : affine_point_t)  : bool :=
  ((y (p_2664)) rem (nat_mod_two )) =.? (nat_mod_zero ).

Definition sqrt (y_2665 : field_element_t)  : (option field_element_t) :=
  let p1_4_2666 : field_element_t :=
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
  let x_2667 : field_element_t :=
    nat_mod_pow_self (y_2665) (p1_4_2666) in 
  (if ((nat_mod_pow_self (x_2667) (nat_mod_two )) =.? (y_2665)):bool then (
      some (x_2667)) else (@None field_element_t)).

Definition lift_x
  (x_2668 : field_element_t)
  
  : (result affine_point_t error_t) :=
  let one_2669 : field_element_t :=
    nat_mod_one  in 
  let two_2670 : field_element_t :=
    nat_mod_two  in 
  let three_2671 : field_element_t :=
    nat_mod_from_literal (
      0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
      @repr WORDSIZE128 3) : field_element_t in 
  let seven_2672 : field_element_t :=
    nat_mod_from_literal (
      0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
      @repr WORDSIZE128 7) : field_element_t in 
  let y_sq_2673 : field_element_t :=
    (nat_mod_pow_self (x_2668) (three_2671)) +% (seven_2672) in 
  bind (option_ok_or (sqrt (y_sq_2673)) (InvalidXCoordinate)) (fun y_2674 =>
    let '(y_2674) :=
      if ((y_2674) rem (two_2670)) =.? (one_2669):bool then (let y_2674 :=
          (nat_mod_zero ) -% (y_2674) in 
        (y_2674)) else ((y_2674)) in 
    @Ok affine_point_t error_t ((x_2668, y_2674))).

Definition compute_lam
  (p1_2675 : affine_point_t)
  (p2_2676 : affine_point_t)
  
  : field_element_t :=
  let three_2677 : field_element_t :=
    nat_mod_from_literal (
      0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
      @repr WORDSIZE128 3) : field_element_t in 
  (if ((p1_2675) !=.? (p2_2676)):bool then (((y (p2_2676)) -% (y (
            p1_2675))) *% (nat_mod_pow_self ((x (p2_2676)) -% (x (p1_2675))) ((
            nat_mod_zero ) -% (nat_mod_two )))) else ((((three_2677) *% (x (
              p1_2675))) *% (x (p1_2675))) *% (nat_mod_pow_self ((
            nat_mod_two ) *% (y (p1_2675))) ((nat_mod_zero ) -% (
            nat_mod_two ))))).

Definition point_add (p1_2678 : point_t) (p2_2679 : point_t)  : point_t :=
  let result_2680 : point_t :=
    AtInfinity in 
  let '(result_2680) :=
    if option_is_none (finite (p1_2678)):bool then (let result_2680 :=
        p2_2679 in 
      (result_2680)) else (let '(result_2680) :=
        if option_is_none (finite (p2_2679)):bool then (let result_2680 :=
            p1_2678 in 
          (result_2680)) else (let p1_2681 : (
              field_element_t '×
              field_element_t
            ) :=
            option_unwrap (finite (p1_2678)) in 
          let p2_2682 : (field_element_t '× field_element_t) :=
            option_unwrap (finite (p2_2679)) in 
          let '(result_2680) :=
            if negb (((x (p1_2681)) =.? (x (p2_2682))) && ((y (p1_2681)) !=.? (
                  y (p2_2682)))):bool then (let lam_2683 : field_element_t :=
                compute_lam (p1_2681) (p2_2682) in 
              let x3_2684 : field_element_t :=
                (((lam_2683) *% (lam_2683)) -% (x (p1_2681))) -% (x (
                    p2_2682)) in 
              let result_2680 :=
                Affine ((
                    x3_2684,
                    ((lam_2683) *% ((x (p1_2681)) -% (x3_2684))) -% (y (
                        p1_2681))
                  )) in 
              (result_2680)) else ((result_2680)) in 
          (result_2680)) in 
      (result_2680)) in 
  result_2680.

Definition point_mul (s_2685 : scalar_t) (p_2686 : point_t)  : point_t :=
  let p_2687 : point_t :=
    p_2686 in 
  let q_2688 : point_t :=
    AtInfinity in 
  let '(p_2687, q_2688) :=
    foldi (usize 0) (usize 256) (fun i_2689 '(p_2687, q_2688) =>
      let '(q_2688) :=
        if nat_mod_bit (s_2685) (i_2689):bool then (let q_2688 :=
            point_add (q_2688) (p_2687) in 
          (q_2688)) else ((q_2688)) in 
      let p_2687 :=
        point_add (p_2687) (p_2687) in 
      (p_2687, q_2688))
    (p_2687, q_2688) in 
  q_2688.

Definition point_mul_base (s_2690 : scalar_t)  : point_t :=
  let gx_2691 : p_bytes32_t :=
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
  let gy_2692 : p_bytes32_t :=
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
  let g_2693 : point_t :=
    Affine ((
        nat_mod_from_public_byte_seq_be (gx_2691),
        nat_mod_from_public_byte_seq_be (gy_2692)
      )) in 
  point_mul (s_2690) (g_2693).

Definition bytes32_t := nseq (uint8) (usize 32).

Notation "'secret_key_t'" := (bytes32_t) : hacspec_scope.

Notation "'public_key_t'" := (bytes32_t) : hacspec_scope.

Notation "'message_t'" := (bytes32_t) : hacspec_scope.

Notation "'aux_rand_t'" := (bytes32_t) : hacspec_scope.

Definition signature_t := nseq (uint8) (usize 64).

Definition tagged_hash
  (tag_2694 : public_byte_seq)
  (msg_2695 : byte_seq)
  
  : bytes32_t :=
  let tag_hash_2696 : seq uint8 :=
    array_to_be_bytes (sha256 (seq_from_public_seq (tag_2694))) in 
  let hash_2697 : sha256_digest_t :=
    sha256 (seq_concat (seq_concat (tag_hash_2696) (tag_hash_2696)) (
        msg_2695)) in 
  array_from_seq (32) (array_to_seq (hash_2697)).

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

Definition hash_aux (aux_rand_2698 : aux_rand_t)  : bytes32_t :=
  tagged_hash (seq_from_seq (array_to_seq (bip0340_aux_v))) (seq_from_seq (
      aux_rand_2698)).

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
  (rand_2699 : bytes32_t)
  (pubkey_2700 : bytes32_t)
  (msg_2701 : message_t)
  
  : bytes32_t :=
  let c_2702 : byte_seq :=
    seq_concat (seq_concat (seq_from_seq (array_to_seq (rand_2699))) (
        array_to_seq (pubkey_2700))) (msg_2701) in 
  tagged_hash (seq_from_seq (array_to_seq (bip0340_nonce_v))) (c_2702).

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
  (rx_2703 : bytes32_t)
  (pubkey_2704 : bytes32_t)
  (msg_2705 : bytes32_t)
  
  : bytes32_t :=
  let c_2706 : byte_seq :=
    seq_concat (seq_concat (seq_from_seq (array_to_seq (rx_2703))) (
        array_to_seq (pubkey_2704))) (array_to_seq (msg_2705)) in 
  tagged_hash (seq_from_seq (array_to_seq (bip0340_challenge_v))) (c_2706).

Definition bytes_from_point (p_2707 : affine_point_t)  : bytes32_t :=
  let '(x_2708, _) :=
    p_2707 in 
  array_from_seq (32) (nat_mod_to_byte_seq_be (x_2708)).

Definition bytes_from_scalar (x_2709 : scalar_t)  : bytes32_t :=
  array_from_seq (32) (nat_mod_to_byte_seq_be (x_2709)).

Definition scalar_from_bytes (b_2710 : bytes32_t)  : scalar_t :=
  nat_mod_from_byte_seq_be (array_to_seq (b_2710)) : scalar_t.

Definition scalar_from_bytes_strict (b_2711 : bytes32_t)  : (option scalar_t) :=
  let s_2712 : big_integer_t :=
    nat_mod_from_byte_seq_be (array_to_seq (b_2711)) : big_integer_t in 
  let max_scalar_2713 : big_integer_t :=
    nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (
        nat_mod_max_val )) : big_integer_t in 
  (if ((s_2712) >.? (max_scalar_2713)):bool then (@None scalar_t) else (
      @Some scalar_t (nat_mod_from_byte_seq_be (
          array_to_seq (b_2711)) : scalar_t))).

Definition seckey_scalar_from_bytes (b_2714 : bytes32_t)  : (option scalar_t) :=
  bind (scalar_from_bytes_strict (b_2714)) (fun s_2715 => (if ((s_2715) =.? (
          nat_mod_zero )):bool then (@None scalar_t) else (@Some scalar_t (
          s_2715)))).

Definition fieldelem_from_bytes
  (b_2716 : public_key_t)
  
  : (option field_element_t) :=
  let s_2717 : big_integer_t :=
    nat_mod_from_byte_seq_be (b_2716) : big_integer_t in 
  let max_fe_2718 : big_integer_t :=
    nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (
        nat_mod_max_val )) : big_integer_t in 
  (if ((s_2717) >.? (max_fe_2718)):bool then (@None field_element_t) else (
      @Some field_element_t (nat_mod_from_byte_seq_be (
          b_2716) : field_element_t))).

Definition xor_bytes (b0_2719 : bytes32_t) (b1_2720 : bytes32_t)  : bytes32_t :=
  let b_2721 : seq uint8 :=
    seq_new_ (default : uint8) (array_len (b0_2719)) in 
  let b_2721 :=
    foldi (usize 0) (array_len (b0_2719)) (fun i_2722 b_2721 =>
      let b_2721 :=
        seq_upd b_2721 (i_2722) ((array_index (b0_2719) (i_2722)) .^ (
            array_index (b1_2720) (i_2722))) in 
      (b_2721))
    b_2721 in 
  array_from_seq (32) (b_2721).

Notation "'pubkey_gen_result_t'" := ((
  result public_key_t error_t)) : hacspec_scope.

Definition pubkey_gen (seckey_2723 : secret_key_t)  : pubkey_gen_result_t :=
  bind (option_ok_or (seckey_scalar_from_bytes (seckey_2723)) (
      InvalidSecretKey)) (fun d0_2724 => let p_2725 : (
        field_element_t '×
        field_element_t
      ) :=
      option_unwrap (finite (point_mul_base (d0_2724))) in 
    @Ok public_key_t error_t (bytes_from_point (p_2725))).

Notation "'sign_result_t'" := ((result signature_t error_t)) : hacspec_scope.

Definition sign
  (msg_2726 : message_t)
  (seckey_2727 : secret_key_t)
  (aux_rand_2728 : aux_rand_t)
  
  : sign_result_t :=
  bind (option_ok_or (seckey_scalar_from_bytes (seckey_2727)) (
      InvalidSecretKey)) (fun d0_2729 => let p_2730 : (
        field_element_t '×
        field_element_t
      ) :=
      option_unwrap (finite (point_mul_base (d0_2729))) in 
    let d_2731 : scalar_t :=
      (if (has_even_y (p_2730)):bool then (d0_2729) else ((nat_mod_zero ) -% (
            d0_2729))) in 
    let t_2732 : bytes32_t :=
      xor_bytes (bytes_from_scalar (d_2731)) (hash_aux (aux_rand_2728)) in 
    let k0_2733 : scalar_t :=
      scalar_from_bytes (hash_nonce (t_2732) (bytes_from_point (p_2730)) (
          msg_2726)) in 
    ifbnd (k0_2733) =.? (nat_mod_zero ) : bool
    thenbnd (bind (@Err signature_t error_t (InvalidNonceGenerated)) (fun _ =>
        @Ok unit error_t (tt)))
    else (tt) >> (fun 'tt =>
    let r_2734 : (field_element_t '× field_element_t) :=
      option_unwrap (finite (point_mul_base (k0_2733))) in 
    let k_2735 : scalar_t :=
      (if (has_even_y (r_2734)):bool then (k0_2733) else ((nat_mod_zero ) -% (
            k0_2733))) in 
    let e_2736 : scalar_t :=
      scalar_from_bytes (hash_challenge (bytes_from_point (r_2734)) (
          bytes_from_point (p_2730)) (msg_2726)) in 
    let sig_2737 : signature_t :=
      array_update (array_update (array_new_ (default : uint8) (64)) (usize 0) (
          array_to_seq (bytes_from_point (r_2734)))) (usize 32) (
        array_to_seq (bytes_from_scalar ((k_2735) +% ((e_2736) *% (
              d_2731))))) in 
    bind (verify (msg_2726) (bytes_from_point (p_2730)) (sig_2737)) (fun _ =>
      @Ok signature_t error_t (sig_2737)))).

Notation "'verification_result_t'" := ((result unit error_t)) : hacspec_scope.

Definition verify
  (msg_2738 : message_t)
  (pubkey_2739 : public_key_t)
  (sig_2740 : signature_t)
  
  : verification_result_t :=
  bind (option_ok_or (fieldelem_from_bytes (pubkey_2739)) (InvalidPublicKey)) (
    fun p_x_2741 => bind (lift_x (p_x_2741)) (fun p_2742 => bind (option_ok_or (
          fieldelem_from_bytes (array_from_slice (default : uint8) (32) (
              array_to_seq (sig_2740)) (usize 0) (usize 32))) (
          InvalidSignature)) (fun r_2743 => bind (option_ok_or (
            scalar_from_bytes_strict (array_from_slice (default : uint8) (32) (
                array_to_seq (sig_2740)) (usize 32) (usize 32))) (
            InvalidSignature)) (fun s_2744 => let e_2745 : scalar_t :=
            scalar_from_bytes (hash_challenge (array_from_slice (
                  default : uint8) (32) (array_to_seq (sig_2740)) (usize 0) (
                  usize 32)) (bytes_from_point (p_2742)) (msg_2738)) in 
          bind (option_ok_or (finite (point_add (point_mul_base (s_2744)) (
                  point_mul ((nat_mod_zero ) -% (e_2745)) (Affine (p_2742))))) (
              InvalidSignature)) (fun r_p_2746 => (if ((negb (has_even_y (
                      r_p_2746))) || ((x (r_p_2746)) !=.? (r_2743))):bool then (
                @Err unit error_t (InvalidSignature)) else (@Ok unit error_t (
                  tt)))))))).

