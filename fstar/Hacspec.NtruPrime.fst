module Hacspec.NtruPrime

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

let build_irreducible (p_0: uint_size) : seq pub_int128 =
  let irr_1 = seq_new_ (pub_i128 0x0) ((p_0) + (usize 1)) in
  let irr_1 = seq_upd irr_1 (usize 0) ((pub_i128 0x0) -. (pub_i128 0x1)) in
  let irr_1 = seq_upd irr_1 (usize 1) ((pub_i128 0x0) -. (pub_i128 0x1)) in
  let irr_1 = seq_upd irr_1 (p_0) (pub_i128 0x1) in
  irr_1

let round_to_3 (poly_2: seq pub_int128) (q_3: pub_int128) : seq pub_int128 =
  let result_4 = seq_clone (poly_2) in
  let q_12_5 = ((q_3) -. (pub_i128 0x1)) /. (pub_i128 0x2) in
  let result_4 =
    foldi (usize 0)
      (seq_len (poly_2))
      (fun i_6 result_4 ->
          let result_4 =
            if (seq_index (poly_2) (i_6)) >. (q_12_5)
            then
              let result_4 = seq_upd result_4 (i_6) ((seq_index (poly_2) (i_6)) -. (q_3)) in
              (result_4)
            else (result_4)
          in
          (result_4))
      (result_4)
  in
  let result_4 =
    foldi (usize 0)
      (seq_len (result_4))
      (fun i_7 result_4 ->
          let result_4 =
            if ((seq_index (result_4) (i_7)) %. (pub_i128 0x3)) <> (pub_i128 0x0)
            then
              let result_4 =
                seq_upd result_4 (i_7) ((seq_index (result_4) (i_7)) -. (pub_i128 0x1))
              in
              let result_4 =
                if ((seq_index (result_4) (i_7)) %. (pub_i128 0x3)) <> (pub_i128 0x0)
                then
                  let result_4 =
                    seq_upd result_4 (i_7) ((seq_index (result_4) (i_7)) +. (pub_i128 0x2))
                  in
                  (result_4)
                else (result_4)
              in
              (result_4)
            else (result_4)
          in
          (result_4))
      (result_4)
  in
  result_4

let encrypt (r_8 h_9: seq pub_int128) (q_10: pub_int128) (irreducible_11: seq pub_int128)
    : seq pub_int128 =
  let pre_12 = mul_poly_irr (r_8) (h_9) (irreducible_11) (q_10) in
  round_to_3 (pre_12) (q_10)

let ntru_prime_653_encrypt (r_13 h_14: seq pub_int128) : seq pub_int128 =
  let p_15 = usize 653 in
  let q_16 = pub_i128 0x120d in
  let w_17 = usize 288 in
  let irreducible_18 = build_irreducible (p_15) in
  encrypt (r_13) (h_14) (q_16) (irreducible_18)

let ntru_prime_653_decrypt (c_19 key_f_20 key_v_21: seq pub_int128) : (seq pub_int128 & bool) =
  let p_22 = usize 653 in
  let q_23 = pub_i128 0x120d in
  let w_24 = usize 288 in
  let irreducible_25 = build_irreducible (p_22) in
  let f_c_26 = mul_poly_irr (key_f_20) (c_19) (irreducible_25) (q_23) in
  let f_3_c_and_decryption_ok_27 =
    poly_to_ring (irreducible_25)
      (add_poly (f_c_26) (add_poly (f_c_26) (f_c_26) (q_23)) (q_23))
      (q_23)
  in
  let f_3_c_28, ok_decrypt_29 = f_3_c_and_decryption_ok_27 in
  let f_3_c_30 = f_3_c_28 in
  let q_12_31 = ((q_23) -. (pub_i128 0x1)) /. (pub_i128 0x2) in
  let f_3_c_30 =
    foldi (usize 0)
      (seq_len (f_3_c_30))
      (fun i_32 f_3_c_30 ->
          let f_3_c_30 =
            if (seq_index (f_3_c_30) (i_32)) >. (q_12_31)
            then
              let f_3_c_30 = seq_upd f_3_c_30 (i_32) ((seq_index (f_3_c_30) (i_32)) -. (q_23)) in
              (f_3_c_30)
            else (f_3_c_30)
          in
          (f_3_c_30))
      (f_3_c_30)
  in
  let e_33 = seq_new_ (pub_i128 0x0) (seq_len (f_3_c_30)) in
  let e_33 =
    foldi (usize 0)
      (seq_len (e_33))
      (fun i_34 e_33 ->
          let e_33 = seq_upd e_33 (i_34) ((seq_index (f_3_c_30) (i_34)) %. (pub_i128 0x3)) in
          (e_33))
      (e_33)
  in
  let e_33 = make_positive (e_33) (pub_i128 0x3) in
  let r_35 = mul_poly_irr (e_33) (key_v_21) (irreducible_25) (pub_i128 0x3) in
  let r_35 =
    foldi (usize 0)
      (seq_len (r_35))
      (fun i_36 r_35 ->
          let r_35 =
            if (seq_index (r_35) (i_36)) = (pub_i128 0x2)
            then
              let r_35 = seq_upd r_35 (i_36) ((pub_i128 0x0) -. (pub_i128 0x1)) in
              (r_35)
            else (r_35)
          in
          (r_35))
      (r_35)
  in
  (r_35, ok_decrypt_29)

