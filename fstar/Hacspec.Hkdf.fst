module Hacspec.Hkdf

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Hmac

open Hacspec.Lib

open Hacspec.Sha256

let hash_len_v:uint_size = (usize 256) / (usize 8)
noeq
type hkdf_error_t = | InvalidOutputLength_hkdf_error_t : hkdf_error_t

type hkdf_byte_seq_result_t = (result byte_seq hkdf_error_t)

let extract (salt_0 ikm_1: byte_seq) : prk_t =
  let salt_or_zero_2 = seq_new_ (secret (pub_u8 0x0)) (hash_len_v) in
  let salt_or_zero_2 =
    if (seq_len (salt_0)) > (usize 0)
    then
      let salt_or_zero_2 = seq_from_seq (salt_0) in
      (salt_or_zero_2)
    else (salt_or_zero_2)
  in
  array_from_seq (0) (hmac (salt_or_zero_2) (ikm_1))

let build_hmac_txt (t_3 info_4: byte_seq) (iteration_5: uint8) : byte_seq =
  let out_6 = seq_new_ (secret (pub_u8 0x0)) (((seq_len (t_3)) + (seq_len (info_4))) + (usize 1)) in
  let out_6 = seq_update (out_6) (usize 0) (t_3) in
  let out_6 = seq_update (out_6) (seq_len (t_3)) (info_4) in
  let out_6 = seq_upd out_6 ((seq_len (t_3)) + (seq_len (info_4))) (iteration_5) in
  out_6

let div_ceil (a_7 b_8: uint_size) : uint_size =
  let q_9 = (a_7) / (b_8) in
  let q_9 =
    if ((a_7) % (b_8)) <> (usize 0)
    then
      let q_9 = (q_9) + (usize 1) in
      (q_9)
    else (q_9)
  in
  q_9

let check_output_limit (l_10: uint_size) : (result uint_size hkdf_error_t) =
  let n_11 = div_ceil (l_10) (hash_len_v) in
  if ((n_11) <= (usize 255)) then (Ok (n_11)) else (Err (InvalidOutputLength_hkdf_error_t))

let expand (prk_12 info_13: byte_seq) (l_14: uint_size) : hkdf_byte_seq_result_t =
  match (check_output_limit (l_14)) with
  | Err x -> Err x
  | Ok n_15 ->
    let t_i_16 = array_new_ (secret (pub_u8 0x0)) (0) in
    let t_17 = seq_new_ (secret (pub_u8 0x0)) ((n_15) * (hash_size_v)) in
    let t_i_16, t_17 =
      foldi (usize 0)
        (n_15)
        (fun i_18 (t_i_16, t_17) ->
            let hmac_txt_in_19 =
              if ((i_18) = (usize 0))
              then
                (build_hmac_txt (seq_new_ (secret (pub_u8 0x0)) (usize 0))
                    (info_13)
                    (secret ((pub_u8 (i_18)) +. (pub_u8 0x1))))
              else
                (build_hmac_txt (seq_from_seq (t_i_16))
                    (info_13)
                    (secret ((pub_u8 (i_18)) +. (pub_u8 0x1))))
            in
            let t_i_16 = hmac (prk_12) (hmac_txt_in_19) in
            let t_17 = seq_update (t_17) ((i_18) * (array_len (t_i_16))) (t_i_16) in
            (t_i_16, t_17))
        (t_i_16, t_17)
    in
    Ok (seq_slice (t_17) (usize 0) (l_14))

