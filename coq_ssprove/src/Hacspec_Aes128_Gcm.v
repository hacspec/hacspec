(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From CoqWord Require Import ssrZ word.
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
Require Import Hacspec_Lib.

Require Import Hacspec_Aes.

Require Import Hacspec_Gf128.

Notation "'aes_gcm_byte_seq_result_t'" := ((
  result int8 byte_seq)) : hacspec_scope.

Definition invalid_tag_v : (int8) :=
  ((@repr U8 1)).

Definition padded_msg_36_loc : ChoiceEqualityLocation :=
  ((seq uint8 ; 71%nat)).
Notation "'pad_aad_msg_inp'" :=(
  byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'pad_aad_msg_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition PAD_AAD_MSG : nat :=
  (72).
Program Definition pad_aad_msg
   : package (CEfset ([padded_msg_36_loc])) [interface  ] [interface
  #val #[ PAD_AAD_MSG ] : pad_aad_msg_inp → pad_aad_msg_out ] :=
  (
    [package #def #[ PAD_AAD_MSG ] (temp_inp : pad_aad_msg_inp) : pad_aad_msg_out { 
    let '(aad_0 , msg_3) := temp_inp : byte_seq '× byte_seq in
    ({ code  '(laad_6 : uint_size) ←
        ( '(temp_2 : uint_size) ←
            (seq_len (aad_0)) ;;
          ret (temp_2)) ;;
       '(lmsg_17 : uint_size) ←
        ( '(temp_5 : uint_size) ←
            (seq_len (msg_3)) ;;
          ret (temp_5)) ;;
       '(pad_aad_28 : uint_size) ←
        ( '(temp_8 : uint_size) ←
            ((laad_6) %% (usize 16)) ;;
           '(temp_10 : bool_ChoiceEquality) ←
            ((temp_8) =.? (usize 0)) ;;
           '(temp_12 : uint_size) ←
            ((laad_6) %% (usize 16)) ;;
           '(temp_14 : uint_size) ←
            ((usize 16) .- (temp_12)) ;;
           '(temp_16 : uint_size) ←
            ((laad_6) .+ (temp_14)) ;;
          ret ((if (temp_10):bool_ChoiceEquality then (laad_6) else (
                temp_16)))) ;;
       '(pad_msg_29 : uint_size) ←
        ( '(temp_19 : uint_size) ←
            ((lmsg_17) %% (usize 16)) ;;
           '(temp_21 : bool_ChoiceEquality) ←
            ((temp_19) =.? (usize 0)) ;;
           '(temp_23 : uint_size) ←
            ((lmsg_17) %% (usize 16)) ;;
           '(temp_25 : uint_size) ←
            ((usize 16) .- (temp_23)) ;;
           '(temp_27 : uint_size) ←
            ((lmsg_17) .+ (temp_25)) ;;
          ret ((if (temp_21):bool_ChoiceEquality then (lmsg_17) else (
                temp_27)))) ;;
       '(padded_msg_36 : seq uint8) ←
          ( '(temp_31 : uint_size) ←
              ((pad_aad_28) .+ (pad_msg_29)) ;;
             '(temp_33 : uint_size) ←
              ((temp_31) .+ (usize 16)) ;;
             temp_35 ←
              (seq_new_ (default : uint8) (temp_33)) ;;
            ret (temp_35)) ;;
        #put padded_msg_36_loc := padded_msg_36 ;;
       '(padded_msg_36 : seq uint8) ←
          (( '(temp_38 : seq uint8) ←
                (seq_update (padded_msg_36) (usize 0) (aad_0)) ;;
              ret (temp_38))) ;;
        #put padded_msg_36_loc := padded_msg_36 ;;
      
       '(padded_msg_36 : seq uint8) ←
          (( '(temp_40 : seq uint8) ←
                (seq_update (padded_msg_36) (pad_aad_28) (msg_3)) ;;
              ret (temp_40))) ;;
        #put padded_msg_36_loc := padded_msg_36 ;;
      
       '(padded_msg_36 : seq uint8) ←
          (( '(temp_42 : uint_size) ←
                ((pad_aad_28) .+ (pad_msg_29)) ;;
               '(temp_44 : int64) ←
                (secret (pub_u64 (laad_6))) ;;
               '(temp_46 : int64) ←
                (secret (@repr U64 8)) ;;
               '(temp_48 : uint64) ←
                ((temp_44) .* (temp_46)) ;;
               '(temp_50 : uint64_word_t) ←
                (uint64_to_be_bytes (temp_48)) ;;
               '(temp_52 : seq uint8) ←
                (array_to_seq (temp_50)) ;;
               '(temp_54 : seq uint8) ←
                (seq_update (padded_msg_36) (temp_42) (temp_52)) ;;
              ret (temp_54))) ;;
        #put padded_msg_36_loc := padded_msg_36 ;;
      
       '(padded_msg_36 : seq uint8) ←
          (( '(temp_56 : uint_size) ←
                ((pad_aad_28) .+ (pad_msg_29)) ;;
               '(temp_58 : uint_size) ←
                ((temp_56) .+ (usize 8)) ;;
               '(temp_60 : int64) ←
                (secret (pub_u64 (lmsg_17))) ;;
               '(temp_62 : int64) ←
                (secret (@repr U64 8)) ;;
               '(temp_64 : uint64) ←
                ((temp_60) .* (temp_62)) ;;
               '(temp_66 : uint64_word_t) ←
                (uint64_to_be_bytes (temp_64)) ;;
               '(temp_68 : seq uint8) ←
                (array_to_seq (temp_66)) ;;
               '(temp_70 : seq uint8) ←
                (seq_update (padded_msg_36) (temp_58) (temp_68)) ;;
              ret (temp_70))) ;;
        #put padded_msg_36_loc := padded_msg_36 ;;
      
      @ret (seq uint8) (padded_msg_36) } : code (CEfset (
          [padded_msg_36_loc])) [interface  ] _)
    }]).
Fail Next Obligation.
Program Definition package_pad_aad_msg : package _ _ _ :=
  (pad_aad_msg).
Fail Next Obligation.


Notation "'encrypt_aes_inp'" :=(
  byte_seq '× aes_nonce_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'encrypt_aes_out'" :=((byte_seq '× gf128_tag_t
  ) : choice_type) (in custom pack_type at level 2).
Definition ENCRYPT_AES : nat :=
  (122).
Program Definition encrypt_aes
   : package (CEfset ([])) [interface
  #val #[ AES128_ENCRYPT ] : aes128_encrypt_inp → aes128_encrypt_out ;
  #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
  #val #[ GMAC ] : gmac_inp → gmac_out ;
  #val #[ PAD_AAD_MSG ] : pad_aad_msg_inp → pad_aad_msg_out ;
  #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out ] [interface
  #val #[ ENCRYPT_AES ] : encrypt_aes_inp → encrypt_aes_out ] :=
  (
    [package #def #[ ENCRYPT_AES ] (temp_inp : encrypt_aes_inp) : encrypt_aes_out { 
    let '(
      key_75 , iv_83 , aad_97 , msg_94) := temp_inp : byte_seq '× aes_nonce_t '× byte_seq '× byte_seq in
    #import {sig #[ AES128_ENCRYPT ] : aes128_encrypt_inp → aes128_encrypt_out } as  aes128_encrypt ;;
    let aes128_encrypt := fun x_0 x_1 x_2 x_3 => aes128_encrypt (
      x_0,x_1,x_2,x_3) in
    #import {sig #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out } as  aes_ctr_key_block ;;
    let aes_ctr_key_block := fun x_0 x_1 x_2 x_3 x_4 x_5 x_6 x_7 => aes_ctr_key_block (
      x_0,x_1,x_2,x_3,x_4,x_5,x_6,x_7) in
    #import {sig #[ GMAC ] : gmac_inp → gmac_out } as  gmac ;;
    let gmac := fun x_0 x_1 => gmac (x_0,x_1) in
    #import {sig #[ PAD_AAD_MSG ] : pad_aad_msg_inp → pad_aad_msg_out } as  pad_aad_msg ;;
    let pad_aad_msg := fun x_0 x_1 => pad_aad_msg (x_0,x_1) in
    #import {sig #[ XOR_BLOCK ] : xor_block_inp → xor_block_out } as  xor_block ;;
    let xor_block := fun x_0 x_1 => xor_block (x_0,x_1) in
    ({ code  '(iv0_76 : aes_nonce_t) ←
        ( '(temp_74 : aes_nonce_t) ←
            (array_new_ (default : uint8) (ivsize_v)) ;;
          ret (temp_74)) ;;
       '(mac_key_102 : block_t) ←
        ( '(temp_78 : int32) ←
            (secret (@repr U32 0)) ;;
           '(temp_80 : block_result_t) ←
            (aes_ctr_key_block (key_75) (iv0_76) (temp_78) (key_length_v) (
                rounds_v) (key_schedule_length_v) (key_length_v) (
                iterations_v)) ;;
           temp_82 ←
            (result_unwrap (temp_80)) ;;
          ret (temp_82)) ;;
       '(tag_mix_114 : block_t) ←
        ( '(temp_85 : int32) ←
            (secret (@repr U32 1)) ;;
           '(temp_87 : block_result_t) ←
            (aes_ctr_key_block (key_75) ((iv_83)) (temp_85) (key_length_v) (
                rounds_v) (key_schedule_length_v) (key_length_v) (
                iterations_v)) ;;
           temp_89 ←
            (result_unwrap (temp_87)) ;;
          ret (temp_89)) ;;
       '(cipher_text_98 : seq uint8) ←
        ( '(temp_91 : key128_t) ←
            (array_from_seq (blocksize_v) (key_75)) ;;
           '(temp_93 : int32) ←
            (secret (@repr U32 2)) ;;
           temp_96 ←
            (aes128_encrypt (temp_91) (iv_83) (temp_93) (msg_94)) ;;
          ret (temp_96)) ;;
       '(padded_msg_101 : seq uint8) ←
        ( '(temp_100 : byte_seq) ←
            (pad_aad_msg (aad_97) (cipher_text_98)) ;;
          ret (temp_100)) ;;
       '(tag_109 : gf128_tag_t) ←
        ( '(temp_104 : seq uint8) ←
            (array_to_seq (mac_key_102)) ;;
           '(temp_106 : gf128_key_t) ←
            (array_from_seq (blocksize_v) (temp_104)) ;;
           temp_108 ←
            (gmac (padded_msg_101) (temp_106)) ;;
          ret (temp_108)) ;;
       '(tag_117 : block_t) ←
        ( '(temp_111 : seq uint8) ←
            (array_to_seq (tag_109)) ;;
           '(temp_113 : block_t) ←
            (array_from_seq (blocksize_v) (temp_111)) ;;
           temp_116 ←
            (xor_block (temp_113) (tag_mix_114)) ;;
          ret (temp_116)) ;;
       '(temp_119 : seq uint8) ←
        (array_to_seq (tag_117)) ;;
       '(temp_121 : gf128_tag_t) ←
        (array_from_seq (blocksize_v) (temp_119)) ;;
      @ret ((seq uint8 '× gf128_tag_t)) (prod_ce(cipher_text_98, temp_121
        )) } : code (CEfset ([])) [interface
      #val #[ AES128_ENCRYPT ] : aes128_encrypt_inp → aes128_encrypt_out ;
      #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
      #val #[ GMAC ] : gmac_inp → gmac_out ;
      #val #[ PAD_AAD_MSG ] : pad_aad_msg_inp → pad_aad_msg_out ;
      #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_encrypt_aes : package _ _ _ :=
  (seq_link encrypt_aes link_rest(
      package_aes128_encrypt,package_aes_ctr_key_block,package_gmac,package_pad_aad_msg,package_xor_block)).
Fail Next Obligation.


Notation "'encrypt_aes128_inp'" :=(
  key128_t '× aes_nonce_t '× byte_seq '× byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'encrypt_aes128_out'" :=((byte_seq '× gf128_tag_t
  ) : choice_type) (in custom pack_type at level 2).
Definition ENCRYPT_AES128 : nat :=
  (133).
Program Definition encrypt_aes128
   : package (CEfset ([])) [interface
  #val #[ ENCRYPT_AES ] : encrypt_aes_inp → encrypt_aes_out ] [interface
  #val #[ ENCRYPT_AES128 ] : encrypt_aes128_inp → encrypt_aes128_out ] :=
  (
    [package #def #[ ENCRYPT_AES128 ] (temp_inp : encrypt_aes128_inp) : encrypt_aes128_out { 
    let '(
      key_123 , iv_128 , aad_129 , msg_130) := temp_inp : key128_t '× aes_nonce_t '× byte_seq '× byte_seq in
    #import {sig #[ ENCRYPT_AES ] : encrypt_aes_inp → encrypt_aes_out } as  encrypt_aes ;;
    let encrypt_aes := fun x_0 x_1 x_2 x_3 => encrypt_aes (x_0,x_1,x_2,x_3) in
    ({ code  '(temp_125 : seq uint8) ←
        (array_to_seq (key_123)) ;;
       '(temp_127 : byte_seq) ←
        (seq_from_seq (temp_125)) ;;
       '(temp_132 : (byte_seq '× gf128_tag_t)) ←
        (encrypt_aes (temp_127) (iv_128) (aad_129) (msg_130)) ;;
      @ret ((byte_seq '× gf128_tag_t)) (temp_132) } : code (CEfset (
          [])) [interface
      #val #[ ENCRYPT_AES ] : encrypt_aes_inp → encrypt_aes_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_encrypt_aes128 : package _ _ _ :=
  (seq_link encrypt_aes128 link_rest(package_encrypt_aes)).
Fail Next Obligation.


Notation "'decrypt_aes_inp'" :=(
  byte_seq '× aes_nonce_t '× byte_seq '× byte_seq '× gf128_tag_t : choice_type) (in custom pack_type at level 2).
Notation "'decrypt_aes_out'" :=(
  aes_gcm_byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Definition DECRYPT_AES : nat :=
  (182).
Program Definition decrypt_aes
   : package (CEfset ([])) [interface
  #val #[ AES128_DECRYPT ] : aes128_decrypt_inp → aes128_decrypt_out ;
  #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
  #val #[ GMAC ] : gmac_inp → gmac_out ;
  #val #[ PAD_AAD_MSG ] : pad_aad_msg_inp → pad_aad_msg_out ;
  #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out ] [interface
  #val #[ DECRYPT_AES ] : decrypt_aes_inp → decrypt_aes_out ] :=
  (
    [package #def #[ DECRYPT_AES ] (temp_inp : decrypt_aes_inp) : decrypt_aes_out { 
    let '(
      key_136 , iv_142 , aad_147 , cipher_text_148 , tag_174) := temp_inp : byte_seq '× aes_nonce_t '× byte_seq '× byte_seq '× gf128_tag_t in
    #import {sig #[ AES128_DECRYPT ] : aes128_decrypt_inp → aes128_decrypt_out } as  aes128_decrypt ;;
    let aes128_decrypt := fun x_0 x_1 x_2 x_3 => aes128_decrypt (
      x_0,x_1,x_2,x_3) in
    #import {sig #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out } as  aes_ctr_key_block ;;
    let aes_ctr_key_block := fun x_0 x_1 x_2 x_3 x_4 x_5 x_6 x_7 => aes_ctr_key_block (
      x_0,x_1,x_2,x_3,x_4,x_5,x_6,x_7) in
    #import {sig #[ GMAC ] : gmac_inp → gmac_out } as  gmac ;;
    let gmac := fun x_0 x_1 => gmac (x_0,x_1) in
    #import {sig #[ PAD_AAD_MSG ] : pad_aad_msg_inp → pad_aad_msg_out } as  pad_aad_msg ;;
    let pad_aad_msg := fun x_0 x_1 => pad_aad_msg (x_0,x_1) in
    #import {sig #[ XOR_BLOCK ] : xor_block_inp → xor_block_out } as  xor_block ;;
    let xor_block := fun x_0 x_1 => xor_block (x_0,x_1) in
    ({ code  '(iv0_137 : aes_nonce_t) ←
        ( '(temp_135 : aes_nonce_t) ←
            (array_new_ (default : uint8) (ivsize_v)) ;;
          ret (temp_135)) ;;
      bnd(ChoiceEqualityMonad.result_bind_code int8 , block_t , _ , CEfset (
          [])) mac_key_152 ⇠
      (({ code  '(temp_139 : int32) ←
            (secret (@repr U32 0)) ;;
           temp_141 ←
            (aes_ctr_key_block (key_136) (iv0_137) (temp_139) (key_length_v) (
                rounds_v) (key_schedule_length_v) (key_length_v) (
                iterations_v)) ;;
          @ret _ (temp_141) } : code (fset.fset0) [interface
          #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out
          ] _)) in
      ({ code bnd(
          ChoiceEqualityMonad.result_bind_code int8 , block_t , _ , CEfset (
            [])) tag_mix_164 ⇠
        (({ code  '(temp_144 : int32) ←
              (secret (@repr U32 1)) ;;
             temp_146 ←
              (aes_ctr_key_block (key_136) ((iv_142)) (temp_144) (
                  key_length_v) (rounds_v) (key_schedule_length_v) (
                  key_length_v) (iterations_v)) ;;
            @ret _ (temp_146) } : code (fset.fset0) [interface
            #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out
            ] _)) in
        ({ code  '(padded_msg_151 : seq uint8) ←
            ( '(temp_150 : byte_seq) ←
                (pad_aad_msg (aad_147) (cipher_text_148)) ;;
              ret (temp_150)) ;;
           '(my_tag_159 : gf128_tag_t) ←
            ( '(temp_154 : seq uint8) ←
                (array_to_seq (mac_key_152)) ;;
               '(temp_156 : gf128_key_t) ←
                (array_from_seq (blocksize_v) (temp_154)) ;;
               temp_158 ←
                (gmac (padded_msg_151) (temp_156)) ;;
              ret (temp_158)) ;;
           '(my_tag_173 : block_t) ←
            ( '(temp_161 : seq uint8) ←
                (array_to_seq (my_tag_159)) ;;
               '(temp_163 : block_t) ←
                (array_from_seq (blocksize_v) (temp_161)) ;;
               temp_166 ←
                (xor_block (temp_163) (tag_mix_164)) ;;
              ret (temp_166)) ;;
           '(ptxt_181 : seq uint8) ←
            ( '(temp_168 : key128_t) ←
                (array_from_seq (blocksize_v) (key_136)) ;;
               '(temp_170 : int32) ←
                (secret (@repr U32 2)) ;;
               temp_172 ←
                (aes128_decrypt (temp_168) (iv_142) (temp_170) (
                    cipher_text_148)) ;;
              ret (temp_172)) ;;
           '(temp_176 : seq uint8) ←
            (array_to_seq (tag_174)) ;;
           '(temp_178 : block_t) ←
            (array_from_seq (blocksize_v) (temp_176)) ;;
           temp_180 ←
            (array_declassify_eq (my_tag_173) (temp_178)) ;;
          @ret ((result int8 byte_seq)) ((if (
                temp_180):bool_ChoiceEquality then (@Ok byte_seq int8 (
                  ptxt_181)) else (@Err byte_seq int8 (
                  invalid_tag_v)))) } : code (CEfset ([])) [interface
          #val #[ AES128_DECRYPT ] : aes128_decrypt_inp → aes128_decrypt_out ;
          #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
          #val #[ GMAC ] : gmac_inp → gmac_out ;
          #val #[ PAD_AAD_MSG ] : pad_aad_msg_inp → pad_aad_msg_out ;
          #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out ] _) } : code (
          CEfset ([])) [interface
        #val #[ AES128_DECRYPT ] : aes128_decrypt_inp → aes128_decrypt_out ;
        #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
        #val #[ GMAC ] : gmac_inp → gmac_out ;
        #val #[ PAD_AAD_MSG ] : pad_aad_msg_inp → pad_aad_msg_out ;
        #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out ] _) } : code (
        CEfset ([])) [interface
      #val #[ AES128_DECRYPT ] : aes128_decrypt_inp → aes128_decrypt_out ;
      #val #[ AES_CTR_KEY_BLOCK ] : aes_ctr_key_block_inp → aes_ctr_key_block_out ;
      #val #[ GMAC ] : gmac_inp → gmac_out ;
      #val #[ PAD_AAD_MSG ] : pad_aad_msg_inp → pad_aad_msg_out ;
      #val #[ XOR_BLOCK ] : xor_block_inp → xor_block_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_decrypt_aes : package _ _ _ :=
  (seq_link decrypt_aes link_rest(
      package_aes128_decrypt,package_aes_ctr_key_block,package_gmac,package_pad_aad_msg,package_xor_block)).
Fail Next Obligation.


Notation "'decrypt_aes128_inp'" :=(
  key128_t '× aes_nonce_t '× byte_seq '× byte_seq '× gf128_tag_t : choice_type) (in custom pack_type at level 2).
Notation "'decrypt_aes128_out'" :=(
  aes_gcm_byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Definition DECRYPT_AES128 : nat :=
  (194).
Program Definition decrypt_aes128
   : package (CEfset ([])) [interface
  #val #[ DECRYPT_AES ] : decrypt_aes_inp → decrypt_aes_out ] [interface
  #val #[ DECRYPT_AES128 ] : decrypt_aes128_inp → decrypt_aes128_out ] :=
  (
    [package #def #[ DECRYPT_AES128 ] (temp_inp : decrypt_aes128_inp) : decrypt_aes128_out { 
    let '(
      key_183 , iv_188 , aad_189 , cipher_text_190 , tag_191) := temp_inp : key128_t '× aes_nonce_t '× byte_seq '× byte_seq '× gf128_tag_t in
    #import {sig #[ DECRYPT_AES ] : decrypt_aes_inp → decrypt_aes_out } as  decrypt_aes ;;
    let decrypt_aes := fun x_0 x_1 x_2 x_3 x_4 => decrypt_aes (
      x_0,x_1,x_2,x_3,x_4) in
    ({ code  '(temp_185 : seq uint8) ←
        (array_to_seq (key_183)) ;;
       '(temp_187 : byte_seq) ←
        (seq_from_seq (temp_185)) ;;
       '(temp_193 : aes_gcm_byte_seq_result_t) ←
        (decrypt_aes (temp_187) (iv_188) (aad_189) (cipher_text_190) (
            tag_191)) ;;
      @ret (aes_gcm_byte_seq_result_t) (temp_193) } : code (CEfset (
          [])) [interface
      #val #[ DECRYPT_AES ] : decrypt_aes_inp → decrypt_aes_out ] _)
    }]).
Fail Next Obligation.
Program Definition package_decrypt_aes128 : package _ _ _ :=
  (seq_link decrypt_aes128 link_rest(package_decrypt_aes)).
Fail Next Obligation.

