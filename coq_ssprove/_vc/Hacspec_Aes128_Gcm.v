(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp.word Require Import ssrZ word.
From Jasmin Require Import word.

From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope bool_scope.

Require Import ChoiceEquality.
Require Import LocationUtility.
Require Import Hacspec_Lib_Comparable.
Require Import Hacspec_Lib_Pre.
Require Import Hacspec_Lib.

Open Scope hacspec_scope.

Obligation Tactic := try timeout 8 solve_ssprove_obligations.


Require Import Hacspec_Aes.

Require Import Hacspec_Gf128.

Notation "'aes_gcm_byte_seq_result_t'" := ((
  result int8 byte_seq)) : hacspec_scope.

Definition invalid_tag_v : int8 :=
  @repr U8 1.

Definition padded_msg_164_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 165%nat).
Notation "'pad_aad_msg_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'pad_aad_msg_inp'" :=(
  byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'pad_aad_msg_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'pad_aad_msg_out'" :=(byte_seq : ChoiceEquality) (at level 2).
Definition PAD_AAD_MSG : nat :=
  172.
Program Definition pad_aad_msg (aad_166 : byte_seq) (msg_168 : byte_seq)
  : both (CEfset ([padded_msg_164_loc])) [interface] (byte_seq) :=
  ((letb laad_167 : uint_size := seq_len (lift_to_both0 aad_166) in
      letb lmsg_169 : uint_size := seq_len (lift_to_both0 msg_168) in
      letb pad_aad_170 : uint_size :=
        if is_pure (I := [interface]) (((lift_to_both0 laad_167) .% (
              lift_to_both0 (usize 16))) =.? (lift_to_both0 (usize 0)))
        then lift_to_both0 laad_167
        else (lift_to_both0 laad_167) .+ ((lift_to_both0 (usize 16)) .- ((
              lift_to_both0 laad_167) .% (lift_to_both0 (usize 16)))) in
      letb pad_msg_171 : uint_size :=
        if is_pure (I := [interface]) (((lift_to_both0 lmsg_169) .% (
              lift_to_both0 (usize 16))) =.? (lift_to_both0 (usize 0)))
        then lift_to_both0 lmsg_169
        else (lift_to_both0 lmsg_169) .+ ((lift_to_both0 (usize 16)) .- ((
              lift_to_both0 lmsg_169) .% (lift_to_both0 (usize 16)))) in
      letbm padded_msg_164 : seq uint8 loc( padded_msg_164_loc ) :=
        seq_new_ (default : uint8) (((lift_to_both0 pad_aad_170) .+ (
              lift_to_both0 pad_msg_171)) .+ (lift_to_both0 (usize 16))) in
      letbm padded_msg_164 loc( padded_msg_164_loc ) :=
        seq_update (lift_to_both0 padded_msg_164) (lift_to_both0 (usize 0)) (
          lift_to_both0 aad_166) in
      letbm padded_msg_164 loc( padded_msg_164_loc ) :=
        seq_update (lift_to_both0 padded_msg_164) (lift_to_both0 pad_aad_170) (
          lift_to_both0 msg_168) in
      letbm padded_msg_164 loc( padded_msg_164_loc ) :=
        seq_update (lift_to_both0 padded_msg_164) ((
            lift_to_both0 pad_aad_170) .+ (lift_to_both0 pad_msg_171)) (
          @array_to_seq (uint64_to_be_bytes ((secret (pub_u64 (is_pure (
                    lift_to_both0 laad_167)))) .* (secret (lift_to_both0 (
                  @repr U64 8)))))) in
      letbm padded_msg_164 loc( padded_msg_164_loc ) :=
        seq_update (lift_to_both0 padded_msg_164) (((
              lift_to_both0 pad_aad_170) .+ (lift_to_both0 pad_msg_171)) .+ (
            lift_to_both0 (usize 8))) (@array_to_seq (uint64_to_be_bytes ((
              secret (pub_u64 (is_pure (lift_to_both0 lmsg_169)))) .* (secret (
                lift_to_both0 (@repr U64 8)))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 padded_msg_164)
      ) : both (CEfset ([padded_msg_164_loc])) [interface] (byte_seq)).
Fail Next Obligation.


Notation "'encrypt_aes_inp'" :=(
  byte_seq '× aes_nonce_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'encrypt_aes_inp'" :=(
  byte_seq '× aes_nonce_t '× byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'encrypt_aes_out'" :=((byte_seq '× gf128_tag_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'encrypt_aes_out'" :=((byte_seq '× gf128_tag_t
  ) : ChoiceEquality) (at level 2).
Definition ENCRYPT_AES : nat :=
  184.
Program Definition encrypt_aes (key_174 : byte_seq) (iv_176 : aes_nonce_t) (
    aad_180 : byte_seq) (msg_178 : byte_seq)
  : both (CEfset ([padded_msg_164_loc])) [interface] ((byte_seq '× gf128_tag_t
    )) :=
  ((letb iv0_173 : aes_nonce_t := array_new_ (default : uint8) (_) in
      letb mac_key_175 : block_t :=
        result_unwrap (aes_ctr_key_block (lift_to_both0 key_174) (
            lift_to_both0 iv0_173) (secret (lift_to_both0 (@repr U32 0))) (
            lift_to_both0 key_length_v) (lift_to_both0 rounds_v) (
            lift_to_both0 key_schedule_length_v) (lift_to_both0 key_length_v) (
            lift_to_both0 iterations_v)) in
      letb tag_mix_177 : block_t :=
        result_unwrap (aes_ctr_key_block (lift_to_both0 key_174) ((
              lift_to_both0 iv_176)) (secret (lift_to_both0 (@repr U32 1))) (
            lift_to_both0 key_length_v) (lift_to_both0 rounds_v) (
            lift_to_both0 key_schedule_length_v) (lift_to_both0 key_length_v) (
            lift_to_both0 iterations_v)) in
      letb cipher_text_179 : seq uint8 :=
        aes128_encrypt (array_from_seq (_) (lift_to_both0 key_174)) (
          lift_to_both0 iv_176) (secret (lift_to_both0 (@repr U32 2))) (
          lift_to_both0 msg_178) in
      letb padded_msg_181 : seq uint8 :=
        pad_aad_msg (lift_to_both0 aad_180) (lift_to_both0 cipher_text_179) in
      letb tag_182 : gf128_tag_t :=
        gmac (lift_to_both0 padded_msg_181) (array_from_seq (_) (
            @array_to_seq (lift_to_both0 mac_key_175))) in
      letb tag_183 : block_t :=
        xor_block (array_from_seq (_) (@array_to_seq (lift_to_both0 tag_182))) (
          lift_to_both0 tag_mix_177) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 cipher_text_179,
          array_from_seq (_) (@array_to_seq (lift_to_both0 tag_183))
        ))
      ) : both (CEfset ([padded_msg_164_loc])) [interface] ((
        byte_seq '×
        gf128_tag_t
      ))).
Fail Next Obligation.


Notation "'encrypt_aes128_inp'" :=(
  key128_t '× aes_nonce_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'encrypt_aes128_inp'" :=(
  key128_t '× aes_nonce_t '× byte_seq '× byte_seq : ChoiceEquality) (at level 2).
Notation "'encrypt_aes128_out'" :=((byte_seq '× gf128_tag_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'encrypt_aes128_out'" :=((byte_seq '× gf128_tag_t
  ) : ChoiceEquality) (at level 2).
Definition ENCRYPT_AES128 : nat :=
  189.
Program Definition encrypt_aes128 (key_185 : key128_t) (iv_186 : aes_nonce_t) (
    aad_187 : byte_seq) (msg_188 : byte_seq)
  : both (CEfset ([padded_msg_164_loc])) [interface] ((byte_seq '× gf128_tag_t
    )) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (encrypt_aes (
          seq_from_seq (@array_to_seq (lift_to_both0 key_185))) (
          lift_to_both0 iv_186) (lift_to_both0 aad_187) (lift_to_both0 msg_188))
      ) : both (CEfset ([padded_msg_164_loc])) [interface] ((
        byte_seq '×
        gf128_tag_t
      ))).
Fail Next Obligation.


Notation "'decrypt_aes_inp'" :=(
  byte_seq '× aes_nonce_t '× byte_seq '× byte_seq '× gf128_tag_t : choice_type) (in custom pack_type at level 2).
Notation "'decrypt_aes_inp'" :=(
  byte_seq '× aes_nonce_t '× byte_seq '× byte_seq '× gf128_tag_t : ChoiceEquality) (at level 2).
Notation "'decrypt_aes_out'" :=(
  aes_gcm_byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'decrypt_aes_out'" :=(
  aes_gcm_byte_seq_result_t : ChoiceEquality) (at level 2).
Definition DECRYPT_AES : nat :=
  202.
Program Definition decrypt_aes (key_191 : byte_seq) (iv_193 : aes_nonce_t) (
    aad_195 : byte_seq) (cipher_text_196 : byte_seq) (tag_201 : gf128_tag_t)
  : both (CEfset ([padded_msg_164_loc])) [interface] (
    aes_gcm_byte_seq_result_t) :=
  ((letb iv0_190 : aes_nonce_t := array_new_ (default : uint8) (_) in
      letbnd(_) mac_key_192 : block_t :=
        aes_ctr_key_block (lift_to_both0 key_191) (lift_to_both0 iv0_190) (
          secret (lift_to_both0 (@repr U32 0))) (lift_to_both0 key_length_v) (
          lift_to_both0 rounds_v) (lift_to_both0 key_schedule_length_v) (
          lift_to_both0 key_length_v) (lift_to_both0 iterations_v) in
      letbnd(_) tag_mix_194 : block_t :=
        aes_ctr_key_block (lift_to_both0 key_191) ((lift_to_both0 iv_193)) (
          secret (lift_to_both0 (@repr U32 1))) (lift_to_both0 key_length_v) (
          lift_to_both0 rounds_v) (lift_to_both0 key_schedule_length_v) (
          lift_to_both0 key_length_v) (lift_to_both0 iterations_v) in
      letb padded_msg_197 : seq uint8 :=
        pad_aad_msg (lift_to_both0 aad_195) (lift_to_both0 cipher_text_196) in
      letb my_tag_198 : gf128_tag_t :=
        gmac (lift_to_both0 padded_msg_197) (array_from_seq (_) (
            @array_to_seq (lift_to_both0 mac_key_192))) in
      letb my_tag_199 : block_t :=
        xor_block (array_from_seq (_) (
            @array_to_seq (lift_to_both0 my_tag_198))) (
          lift_to_both0 tag_mix_194) in
      letb ptxt_200 : seq uint8 :=
        aes128_decrypt (array_from_seq (_) (lift_to_both0 key_191)) (
          lift_to_both0 iv_193) (secret (lift_to_both0 (@repr U32 2))) (
          lift_to_both0 cipher_text_196) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (array_declassify_eq (
            lift_to_both0 my_tag_199) (array_from_seq (_) (
              @array_to_seq (lift_to_both0 tag_201))))
        then @Ok byte_seq int8 (lift_to_both0 ptxt_200)
        else @Err byte_seq int8 (lift_to_both0 invalid_tag_v))
      ) : both (CEfset ([padded_msg_164_loc])) [interface] (
      aes_gcm_byte_seq_result_t)).
Fail Next Obligation.


Notation "'decrypt_aes128_inp'" :=(
  key128_t '× aes_nonce_t '× byte_seq '× byte_seq '× gf128_tag_t : choice_type) (in custom pack_type at level 2).
Notation "'decrypt_aes128_inp'" :=(
  key128_t '× aes_nonce_t '× byte_seq '× byte_seq '× gf128_tag_t : ChoiceEquality) (at level 2).
Notation "'decrypt_aes128_out'" :=(
  aes_gcm_byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Notation "'decrypt_aes128_out'" :=(
  aes_gcm_byte_seq_result_t : ChoiceEquality) (at level 2).
Definition DECRYPT_AES128 : nat :=
  208.
Program Definition decrypt_aes128 (key_203 : key128_t) (iv_204 : aes_nonce_t) (
    aad_205 : byte_seq) (cipher_text_206 : byte_seq) (tag_207 : gf128_tag_t)
  : both (CEfset ([padded_msg_164_loc])) [interface] (
    aes_gcm_byte_seq_result_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (decrypt_aes (
          seq_from_seq (@array_to_seq (lift_to_both0 key_203))) (
          lift_to_both0 iv_204) (lift_to_both0 aad_205) (
          lift_to_both0 cipher_text_206) (lift_to_both0 tag_207))
      ) : both (CEfset ([padded_msg_164_loc])) [interface] (
      aes_gcm_byte_seq_result_t)).
Fail Next Obligation.

