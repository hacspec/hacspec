module Hacspec.Hmac

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

open Hacspec.Sha256

let block_len_v:uint_size = k_size_v

type prk_t = lseq (uint8) (hash_size_v)

type block_t = lseq (uint8) (block_len_v)

let i_pad_v:block_t =
  array_from_list (let l =
        [
          secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36);
          secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36);
          secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36);
          secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36);
          secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36);
          secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36);
          secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36);
          secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36);
          secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36);
          secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36);
          secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36);
          secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36);
          secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36);
          secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36);
          secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36);
          secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36); secret (pub_u8 0x36)
        ]
      in
      assert_norm (List.Tot.length l == 64);
      l)

let o_pad_v:block_t =
  array_from_list (let l =
        [
          secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c);
          secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c);
          secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c);
          secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c);
          secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c);
          secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c);
          secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c);
          secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c);
          secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c);
          secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c);
          secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c);
          secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c);
          secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c);
          secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c);
          secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c);
          secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c); secret (pub_u8 0x5c)
        ]
      in
      assert_norm (List.Tot.length l == 64);
      l)

let k_block (k_0: byte_seq) : block_t =
  if ((seq_len (k_0)) > (block_len_v))
  then (array_update_start (array_new_ (secret (pub_u8 0x0)) (block_len_v)) (hash (k_0)))
  else (array_update_start (array_new_ (secret (pub_u8 0x0)) (block_len_v)) (k_0))

let hmac (k_1 txt_2: byte_seq) : prk_t =
  let k_block_3 = k_block (k_1) in
  let h_in_4 = seq_from_seq (array_xor ( ^. ) (k_block_3) (i_pad_v)) in
  let h_in_4 = seq_concat (h_in_4) (txt_2) in
  let h_inner_5 = hash (h_in_4) in
  let h_in_6 = seq_from_seq (array_xor ( ^. ) (k_block_3) (o_pad_v)) in
  let h_in_6 = seq_concat (h_in_6) (h_inner_5) in
  array_from_seq (hash_size_v) (hash (h_in_6))

