(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition build_irreducible (p_1232 : uint_size) : seq int128 :=
  let irr_1233 : seq int128 :=
    seq_new_ (default : int128) ((p_1232) + (usize 1)) in 
  let irr_1233 :=
    seq_upd irr_1233 (usize 0) (- (@repr WORDSIZE128 1)) in 
  let irr_1233 :=
    seq_upd irr_1233 (usize 1) (- (@repr WORDSIZE128 1)) in 
  let irr_1233 :=
    seq_upd irr_1233 (p_1232) (@repr WORDSIZE128 1) in 
  irr_1233.

Definition round_to_3 (poly_1234 : seq int128) (q_1235 : int128) : seq int128 :=
  let result_1236 : seq int128 :=
    (poly_1234) in 
  let q_12_1237 : int128 :=
    ((q_1235) .- (@repr WORDSIZE128 1)) ./ (@repr WORDSIZE128 2) in 
  let result_1236 :=
    foldi (usize 0) (seq_len (poly_1234)) (fun i_1238 result_1236 =>
      let '(result_1236) :=
        if (seq_index (poly_1234) (i_1238)) >.? (q_12_1237):bool then (
          let result_1236 :=
            seq_upd result_1236 (i_1238) ((seq_index (poly_1234) (i_1238)) .- (
                q_1235)) in 
          (result_1236)) else ((result_1236)) in 
      (result_1236))
    result_1236 in 
  let result_1236 :=
    foldi (usize 0) (seq_len (result_1236)) (fun i_1239 result_1236 =>
      let '(result_1236) :=
        if ((seq_index (result_1236) (i_1239)) .% (@repr WORDSIZE128 3)) !=.? (
          @repr WORDSIZE128 0):bool then (let result_1236 :=
            seq_upd result_1236 (i_1239) ((seq_index (result_1236) (
                  i_1239)) .- (@repr WORDSIZE128 1)) in 
          let '(result_1236) :=
            if ((seq_index (result_1236) (i_1239)) .% (
                @repr WORDSIZE128 3)) !=.? (@repr WORDSIZE128 0):bool then (
              let result_1236 :=
                seq_upd result_1236 (i_1239) ((seq_index (result_1236) (
                      i_1239)) .+ (@repr WORDSIZE128 2)) in 
              (result_1236)) else ((result_1236)) in 
          (result_1236)) else ((result_1236)) in 
      (result_1236))
    result_1236 in 
  result_1236.

Definition encrypt
  (r_1240 : seq int128)
  (h_1241 : seq int128)
  (q_1242 : int128)
  (irreducible_1243 : seq int128)
  : seq int128 :=
  let pre_1244 : seq int128 :=
    mul_poly_irr (r_1240) (h_1241) (irreducible_1243) (q_1242) in 
  round_to_3 (pre_1244) (q_1242).

Definition ntru_prime_653_encrypt
  (r_1245 : seq int128)
  (h_1246 : seq int128)
  : seq int128 :=
  let p_1247 : uint_size :=
    usize 653 in 
  let q_1248 : int128 :=
    @repr WORDSIZE128 4621 in 
  let w_1249 : uint_size :=
    usize 288 in 
  let irreducible_1250 : seq int128 :=
    build_irreducible (p_1247) in 
  encrypt (r_1245) (h_1246) (q_1248) (irreducible_1250).

Definition ntru_prime_653_decrypt
  (c_1251 : seq int128)
  (key_f_1252 : seq int128)
  (key_v_1253 : seq int128)
  : (seq int128 × bool) :=
  let p_1254 : uint_size :=
    usize 653 in 
  let q_1255 : int128 :=
    @repr WORDSIZE128 4621 in 
  let w_1256 : uint_size :=
    usize 288 in 
  let irreducible_1257 : seq int128 :=
    build_irreducible (p_1254) in 
  let f_c_1258 : seq int128 :=
    mul_poly_irr (key_f_1252) (c_1251) (irreducible_1257) (q_1255) in 
  let f_3_c_and_decryption_ok_1259 : (seq int128 × bool) :=
    poly_to_ring (irreducible_1257) (add_poly (f_c_1258) (add_poly (f_c_1258) (
          f_c_1258) (q_1255)) (q_1255)) (q_1255) in 
  let '(f_3_c_1260, ok_decrypt_1261) :=
    f_3_c_and_decryption_ok_1259 in 
  let f_3_c_1262 : seq int128 :=
    f_3_c_1260 in 
  let q_12_1263 : int128 :=
    ((q_1255) .- (@repr WORDSIZE128 1)) ./ (@repr WORDSIZE128 2) in 
  let f_3_c_1262 :=
    foldi (usize 0) (seq_len (f_3_c_1262)) (fun i_1264 f_3_c_1262 =>
      let '(f_3_c_1262) :=
        if (seq_index (f_3_c_1262) (i_1264)) >.? (q_12_1263):bool then (
          let f_3_c_1262 :=
            seq_upd f_3_c_1262 (i_1264) ((seq_index (f_3_c_1262) (i_1264)) .- (
                q_1255)) in 
          (f_3_c_1262)) else ((f_3_c_1262)) in 
      (f_3_c_1262))
    f_3_c_1262 in 
  let e_1265 : seq int128 :=
    seq_new_ (default : int128) (seq_len (f_3_c_1262)) in 
  let e_1265 :=
    foldi (usize 0) (seq_len (e_1265)) (fun i_1266 e_1265 =>
      let e_1265 :=
        seq_upd e_1265 (i_1266) ((seq_index (f_3_c_1262) (i_1266)) .% (
            @repr WORDSIZE128 3)) in 
      (e_1265))
    e_1265 in 
  let e_1265 :=
    make_positive (e_1265) (@repr WORDSIZE128 3) in 
  let r_1267 : seq int128 :=
    mul_poly_irr (e_1265) (key_v_1253) (irreducible_1257) (
      @repr WORDSIZE128 3) in 
  let r_1267 :=
    foldi (usize 0) (seq_len (r_1267)) (fun i_1268 r_1267 =>
      let '(r_1267) :=
        if (seq_index (r_1267) (i_1268)) =.? (@repr WORDSIZE128 2):bool then (
          let r_1267 :=
            seq_upd r_1267 (i_1268) (- (@repr WORDSIZE128 1)) in 
          (r_1267)) else ((r_1267)) in 
      (r_1267))
    r_1267 in 
  (r_1267, ok_decrypt_1261).

