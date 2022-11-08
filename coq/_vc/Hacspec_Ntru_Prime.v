(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition build_irreducible (p_1174 : uint_size) : seq int128 :=
  let irr_1175 : seq int128 :=
    seq_new_ (default) ((p_1174) + (usize 1)) in 
  let irr_1175 :=
    seq_upd irr_1175 (usize 0) (- (@repr WORDSIZE128 1)) in 
  let irr_1175 :=
    seq_upd irr_1175 (usize 1) (- (@repr WORDSIZE128 1)) in 
  let irr_1175 :=
    seq_upd irr_1175 (p_1174) (@repr WORDSIZE128 1) in 
  irr_1175.

Definition round_to_3 (poly_1176 : seq int128) (q_1177 : int128) : seq int128 :=
  let result_1178 : seq int128 :=
    (poly_1176) in 
  let q_12_1179 : int128 :=
    ((q_1177) .- (@repr WORDSIZE128 1)) ./ (@repr WORDSIZE128 2) in 
  let result_1178 :=
    foldi (usize 0) (seq_len (poly_1176)) (fun i_1180 result_1178 =>
      let '(result_1178) :=
        if (seq_index (poly_1176) (i_1180)) >.? (q_12_1179):bool then (
          let result_1178 :=
            seq_upd result_1178 (i_1180) ((seq_index (poly_1176) (i_1180)) .- (
                q_1177)) in 
          (result_1178)) else ((result_1178)) in 
      (result_1178))
    result_1178 in 
  let result_1178 :=
    foldi (usize 0) (seq_len (result_1178)) (fun i_1181 result_1178 =>
      let '(result_1178) :=
        if ((seq_index (result_1178) (i_1181)) .% (@repr WORDSIZE128 3)) !=.? (
          @repr WORDSIZE128 0):bool then (let result_1178 :=
            seq_upd result_1178 (i_1181) ((seq_index (result_1178) (
                  i_1181)) .- (@repr WORDSIZE128 1)) in 
          let '(result_1178) :=
            if ((seq_index (result_1178) (i_1181)) .% (
                @repr WORDSIZE128 3)) !=.? (@repr WORDSIZE128 0):bool then (
              let result_1178 :=
                seq_upd result_1178 (i_1181) ((seq_index (result_1178) (
                      i_1181)) .+ (@repr WORDSIZE128 2)) in 
              (result_1178)) else ((result_1178)) in 
          (result_1178)) else ((result_1178)) in 
      (result_1178))
    result_1178 in 
  result_1178.

Definition encrypt
  (r_1182 : seq int128)
  (h_1183 : seq int128)
  (q_1184 : int128)
  (irreducible_1185 : seq int128)
  : seq int128 :=
  let pre_1186 : seq int128 :=
    mul_poly_irr (r_1182) (h_1183) (irreducible_1185) (q_1184) in 
  round_to_3 (pre_1186) (q_1184).

Definition ntru_prime_653_encrypt
  (r_1187 : seq int128)
  (h_1188 : seq int128)
  : seq int128 :=
  let p_1189 : uint_size :=
    usize 653 in 
  let q_1190 : int128 :=
    @repr WORDSIZE128 4621 in 
  let w_1191 : uint_size :=
    usize 288 in 
  let irreducible_1192 : seq int128 :=
    build_irreducible (p_1189) in 
  encrypt (r_1187) (h_1188) (q_1190) (irreducible_1192).

Definition ntru_prime_653_decrypt
  (c_1193 : seq int128)
  (key_f_1194 : seq int128)
  (key_v_1195 : seq int128)
  : (seq int128 × bool) :=
  let p_1196 : uint_size :=
    usize 653 in 
  let q_1197 : int128 :=
    @repr WORDSIZE128 4621 in 
  let w_1198 : uint_size :=
    usize 288 in 
  let irreducible_1199 : seq int128 :=
    build_irreducible (p_1196) in 
  let f_c_1200 : seq int128 :=
    mul_poly_irr (key_f_1194) (c_1193) (irreducible_1199) (q_1197) in 
  let f_3_c_and_decryption_ok_1201 : (seq int128 × bool) :=
    poly_to_ring (irreducible_1199) (add_poly (f_c_1200) (add_poly (f_c_1200) (
          f_c_1200) (q_1197)) (q_1197)) (q_1197) in 
  let '(f_3_c_1202, ok_decrypt_1203) :=
    f_3_c_and_decryption_ok_1201 in 
  let f_3_c_1204 : seq int128 :=
    f_3_c_1202 in 
  let q_12_1205 : int128 :=
    ((q_1197) .- (@repr WORDSIZE128 1)) ./ (@repr WORDSIZE128 2) in 
  let f_3_c_1204 :=
    foldi (usize 0) (seq_len (f_3_c_1204)) (fun i_1206 f_3_c_1204 =>
      let '(f_3_c_1204) :=
        if (seq_index (f_3_c_1204) (i_1206)) >.? (q_12_1205):bool then (
          let f_3_c_1204 :=
            seq_upd f_3_c_1204 (i_1206) ((seq_index (f_3_c_1204) (i_1206)) .- (
                q_1197)) in 
          (f_3_c_1204)) else ((f_3_c_1204)) in 
      (f_3_c_1204))
    f_3_c_1204 in 
  let e_1207 : seq int128 :=
    seq_new_ (default) (seq_len (f_3_c_1204)) in 
  let e_1207 :=
    foldi (usize 0) (seq_len (e_1207)) (fun i_1208 e_1207 =>
      let e_1207 :=
        seq_upd e_1207 (i_1208) ((seq_index (f_3_c_1204) (i_1208)) .% (
            @repr WORDSIZE128 3)) in 
      (e_1207))
    e_1207 in 
  let e_1207 :=
    make_positive (e_1207) (@repr WORDSIZE128 3) in 
  let r_1209 : seq int128 :=
    mul_poly_irr (e_1207) (key_v_1195) (irreducible_1199) (
      @repr WORDSIZE128 3) in 
  let r_1209 :=
    foldi (usize 0) (seq_len (r_1209)) (fun i_1210 r_1209 =>
      let '(r_1209) :=
        if (seq_index (r_1209) (i_1210)) =.? (@repr WORDSIZE128 2):bool then (
          let r_1209 :=
            seq_upd r_1209 (i_1210) (- (@repr WORDSIZE128 1)) in 
          (r_1209)) else ((r_1209)) in 
      (r_1209))
    r_1209 in 
  (r_1209, ok_decrypt_1203).

