module Hacspec.Tls.Cryptolib

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

open Hacspec.Aes

open Hacspec.Aes128.Gcm

open Hacspec.Chacha20

open Hacspec.Chacha20poly1305

open Hacspec.Curve25519

open Hacspec.Ecdsa.P256.Sha256

open Hacspec.Gf128

open Hacspec.Hkdf

open Hacspec.Hmac

open Hacspec.P256

open Hacspec.Poly1305

open Hacspec.Sha256

noeq type crypto_error =
| CryptoError_crypto_error : crypto_error
| HkdfError_crypto_error : crypto_error
| InsufficientEntropy_crypto_error : crypto_error
| InvalidCert_crypto_error : crypto_error
| MacFailed_crypto_error : crypto_error
| UnsupportedAlgorithm_crypto_error : crypto_error
| VerifyFailed_crypto_error : crypto_error

let empty () : byte_seq =
  seq_new_ (secret (pub_u8 0x0)) (usize 0)

let zeros (u_0 : uint_size) : byte_seq =
  seq_new_ (secret (pub_u8 0x0)) (u_0)

type entropy = byte_seq

type random = lseq (uint8) (usize 32)

type dh_sk = byte_seq

type dh_pk = byte_seq

type signature_key = byte_seq

type verification_key = byte_seq

type mac_key = byte_seq

type aead_key = byte_seq

type key = byte_seq

type psk = key

type digest = byte_seq

type hmac = byte_seq

type signature = byte_seq

type aead_iv = byte_seq

type aead_key_iv = (aead_key & aead_iv)

noeq type named_group =
| X25519_named_group : named_group
| Secp256r1_named_group : named_group

noeq type hash_algorithm =
| SHA256_hash_algorithm : hash_algorithm
| SHA384_hash_algorithm : hash_algorithm

noeq type aead_algorithm =
| Chacha20Poly1305_aead_algorithm : aead_algorithm
| Aes128Gcm_aead_algorithm : aead_algorithm
| Aes256Gcm_aead_algorithm : aead_algorithm

noeq type signature_scheme =
| ED25519_signature_scheme : signature_scheme
| EcdsaSecp256r1Sha256_signature_scheme : signature_scheme
| RsaPssRsaSha256_signature_scheme : signature_scheme

let hash_len (ha_1 : hash_algorithm) : uint_size =
  match ha_1 with
  | SHA256_hash_algorithm -> usize 32
  | SHA384_hash_algorithm -> usize 48

let hmac_key_len (ha_2 : hash_algorithm) : uint_size =
  match ha_2 with
  | SHA256_hash_algorithm -> usize 32
  | SHA384_hash_algorithm -> usize 48

let ae_key_len (ae_3 : aead_algorithm) : uint_size =
  match ae_3 with
  | Chacha20Poly1305_aead_algorithm -> usize 32
  | Aes128Gcm_aead_algorithm -> usize 16
  | Aes256Gcm_aead_algorithm -> usize 16

let ae_iv_len (ae_4 : aead_algorithm) : uint_size =
  match ae_4 with
  | Chacha20Poly1305_aead_algorithm -> usize 12
  | Aes128Gcm_aead_algorithm -> usize 12
  | Aes256Gcm_aead_algorithm -> usize 12

let dh_priv_len (gn_5 : named_group) : uint_size =
  match gn_5 with
  | X25519_named_group -> usize 32
  | Secp256r1_named_group -> usize 32

let dh_pub_len (gn_6 : named_group) : uint_size =
  match gn_6 with
  | X25519_named_group -> usize 32
  | Secp256r1_named_group -> usize 64

let zero_key (ha_7 : hash_algorithm) : key =
  seq_new_ (secret (pub_u8 0x0)) (usize (hash_len (ha_7)))

let secret_to_public
  (group_name_8 : named_group)
  (x_9 : dh_sk)
  : (result dh_pk crypto_error) =
  match group_name_8 with
  | Secp256r1_named_group -> match p256_point_mul_base (
    nat_from_byte_seq_be (0xunknown) (x_9)) with
  | Ok (x_10, y_11) -> Ok (
    (
      seq_concat (nat_to_byte_seq_be (0xunknown) (x_10)) (
        nat_to_byte_seq_be (0xunknown) (y_11))
    ))
  | Err _ -> Err ((CryptoError_crypto_error))
  | X25519_named_group -> Ok (
    (seq_from_seq (x25519_secret_to_public (array_from_seq (32) (x_9)))))

let p256_ecdh (x_12 : dh_sk) (y_13 : dh_pk) : (result key crypto_error) =
  let pk_14 =
    (
      nat_from_byte_seq_be (0xunknown) (
        seq_slice_range (y_13) ((usize 0, usize 32))),
      nat_from_byte_seq_be (0xunknown) (
        seq_slice_range (y_13) ((usize 32, usize 64)))
    )
  in
  match p256_point_mul (nat_from_byte_seq_be (0xunknown) (x_12)) (pk_14) with
  | Ok (x_15, y_16) -> Ok (
    (
      seq_concat (nat_to_byte_seq_be (0xunknown) (x_15)) (
        nat_to_byte_seq_be (0xunknown) (y_16))
    ))
  | Err _ -> Err ((CryptoError_crypto_error))

let ecdh
  (group_name_17 : named_group)
  (x_18 : dh_sk)
  (y_19 : dh_pk)
  : (result key crypto_error) =
  match group_name_17 with
  | Secp256r1_named_group -> p256_ecdh (x_18) (y_19)
  | X25519_named_group -> Ok (
    (
      seq_from_seq (
        x25519_scalarmult (array_from_seq (32) (x_18)) (
          array_from_seq (32) (y_19)))
    ))

type kem_scheme = named_group

type kem_sk = byte_seq

type kem_pk = byte_seq

let kem_priv_len (ks_20 : kem_scheme) : uint_size =
  dh_priv_len (ks_20)

let kem_pub_len (ks_21 : kem_scheme) : uint_size =
  dh_pub_len (ks_21)

let kem_priv_to_pub
  (ks_22 : kem_scheme)
  (sk_23 : kem_sk)
  : (result kem_pk crypto_error) =
  secret_to_public (ks_22) (sk_23)

let kem_keygen_inner
  (ks_24 : kem_scheme)
  (ent_25 : entropy)
  : (result (kem_sk & kem_pk) crypto_error) =
  let sk_26 =
    seq_from_seq (seq_slice_range (ent_25) ((usize 0, dh_priv_len (ks_24))))
  in
  match (kem_priv_to_pub (ks_24) (sk_26)) with
  | Err x -> Err x
  | Ok  pk_27 ->
    Ok (((sk_26, pk_27)))

let kem_keygen
  (ks_28 : kem_scheme)
  (ent_29 : entropy)
  : (result (kem_sk & kem_pk) crypto_error) =
  if ((seq_len (ent_29)) <. (dh_priv_len (ks_28))) then (
    Err ((InsufficientEntropy_crypto_error))) else (
    kem_keygen_inner (ks_28) (ent_29))

let kem_encap
  (ks_30 : kem_scheme)
  (pk_31 : kem_pk)
  (ent_32 : entropy)
  : (result (key & byte_seq) crypto_error) =
  match (kem_keygen (ks_30) (ent_32)) with
  | Err x -> Err x
  | Ok  (x_33, gx_34) ->
    match (ecdh (ks_30) (x_33) (pk_31)) with
    | Err x -> Err x
    | Ok  gxy_35 ->
      Ok (((gxy_35, gx_34)))

let kem_decap
  (ks_36 : kem_scheme)
  (ct_37 : byte_seq)
  (sk_38 : kem_sk)
  : (result key crypto_error) =
  match (ecdh (ks_36) (sk_38) (ct_37)) with
  | Err x -> Err x
  | Ok  gxy_39 ->
    Ok ((gxy_39))

let hash
  (ha_40 : hash_algorithm)
  (payload_41 : byte_seq)
  : (result digest crypto_error) =
  match ha_40 with
  | SHA256_hash_algorithm -> Ok ((seq_from_seq (sha256 (payload_41))))
  | SHA384_hash_algorithm -> Err ((UnsupportedAlgorithm_crypto_error))

let hmac_tag
  (ha_42 : hash_algorithm)
  (mk_43 : mac_key)
  (payload_44 : byte_seq)
  : (result hmac crypto_error) =
  match ha_42 with
  | SHA256_hash_algorithm -> Ok ((seq_from_seq (hmac (mk_43) (payload_44))))
  | SHA384_hash_algorithm -> Err ((UnsupportedAlgorithm_crypto_error))

let check_tag_len (a_45 : hmac) (b_46 : hmac) : (result () crypto_error) =
  if ((seq_len (a_45)) = (seq_len (b_46))) then (Ok ((()))) else (
    Err ((MacFailed_crypto_error)))

let check_bytes (a_47 : uint8) (b_48 : uint8) : (result () crypto_error) =
  if (not (uint8_equal (a_47) (b_48))) then (
    Err ((MacFailed_crypto_error))) else (Ok ((())))

let hmac_verify
  (ha_49 : hash_algorithm)
  (mk_50 : mac_key)
  (payload_51 : byte_seq)
  (m_52 : hmac)
  : (result () crypto_error) =
  match (hmac_tag (ha_49) (mk_50) (payload_51)) with
  | Err x -> Err x
  | Ok  my_hmac_53 ->
    match (check_tag_len (m_52) (my_hmac_53)) with
    | Err x -> Err x
    | Ok  _ ->
      match (
        foldi_result (usize 0) (seq_len (m_52)) (fun i_54 () ->
          match (
            check_bytes (seq_index (my_hmac_53) (i_54)) (
              seq_index (m_52) (i_54))) with
          | Err x -> Err x
          | Ok  _ ->
            Ok (()))
        ()) with
      | Err x -> Err x
      | Ok  () ->
        Ok ((()))

type ec_oid_tag = lseq (uint8) (usize 9)

let get_length_length (b_55 : byte_seq) : uint_size =
  if (
    (
      (uint8_declassify (seq_index (b_55) (usize 0))) `shift_right` (
        usize 7)) = (pub_u8 0x1)) then (
    declassify_usize_from_uint8 (
      (seq_index (b_55) (usize 0)) &. (secret (pub_u8 0x7f)))) else (usize 0)

let get_length (b_56 : byte_seq) (len_57 : uint_size) : uint_size =
  (
    v (
      cast U32 PUB (
        declassify_u32_from_uint32 (
          uint32_from_be_bytes (
            array_from_slice (secret (pub_u8 0x0)) (4) (b_56) (usize 0) (
              len_57)))))) `usize_shift_right` (
    ((usize 4) - (len_57)) * (usize 8))

let get_short_length (b_58 : byte_seq) : uint_size =
  declassify_usize_from_uint8 (
    (seq_index (b_58) (usize 0)) &. (secret (pub_u8 0x7f)))

let verification_key_from_cert
  (cert_59 : byte_seq)
  : (result verification_key crypto_error) =
  let skip_60 =
    (
      (usize 2) + (
        get_length_length (
          seq_slice_range (cert_59) ((usize 1, seq_len (cert_59)))))) + (
      usize 1)
  in
  let seq1_len_len_61 =
    get_length_length (seq_slice_range (cert_59) ((skip_60, seq_len (cert_59))))
  in
  let skip_62 =
    (skip_60) + (usize 1)
  in
  let seq1_len_63 =
    get_length (
      seq_slice (cert_59) (skip_62) ((seq_len (cert_59)) - (skip_62))) (
      seq1_len_len_61)
  in
  let seq1_64 =
    seq_slice_range (cert_59) (
      (
        (skip_62) + (seq1_len_len_61),
        ((skip_62) + (seq1_len_len_61)) + (seq1_len_63)
      ))
  in
  let pk_65 =
    seq_new_ (secret (pub_u8 0x0)) (usize 0)
  in
  let (seq1_64, pk_65) =
    foldi (usize 0) (seq_len (seq1_64)) (fun i_66 (seq1_64, pk_65) ->
      let (seq1_64, pk_65) =
        if (seq_len (seq1_64)) >. (usize 0) then begin
          let element_type_67 =
            uint8_declassify (seq_index (seq1_64) (usize 0))
          in
          let seq1_64 =
            seq_slice (seq1_64) (usize 1) ((seq_len (seq1_64)) - (usize 1))
          in
          let len_len_68 =
            get_length_length (seq1_64)
          in
          let len_69 =
            get_short_length (seq1_64)
          in
          let seq1_64 =
            seq_slice (seq1_64) (usize 1) ((seq_len (seq1_64)) - (usize 1))
          in
          let (len_69) =
            if (len_len_68) <> (usize 0) then begin
              let len_69 =
                (get_length (seq1_64) (len_len_68)) + (len_len_68)
              in
              (len_69)
            end else begin (len_69)
            end
          in
          let (pk_65) =
            if ((element_type_67) = (pub_u8 0x30)) && (
              (seq_len (pk_65)) = (usize 0)) then begin
              let seq2_70 =
                seq_slice (seq1_64) (len_len_68) (len_69)
              in
              let element_type_71 =
                uint8_declassify (seq_index (seq2_70) (usize 0))
              in
              let seq2_72 =
                seq_slice (seq2_70) (usize 1) ((seq_len (seq2_70)) - (usize 1))
              in
              let (pk_65) =
                if (element_type_71) = (pub_u8 0x30) then begin
                  let len_len_73 =
                    get_length_length (seq2_72)
                  in
                  let (pk_65) =
                    if (len_len_73) = (usize 0) then begin
                      let oid_len_74 =
                        get_short_length (seq2_72)
                      in
                      let (pk_65) =
                        if (oid_len_74) >=. (usize 9) then begin
                          let expected_75 =
                            seq_from_seq (
                              array_from_list (
                                let l =
                                  [
                                    secret (pub_u8 0x6);
                                    secret (pub_u8 0x7);
                                    secret (pub_u8 0x2a);
                                    secret (pub_u8 0x86);
                                    secret (pub_u8 0x48);
                                    secret (pub_u8 0xce);
                                    secret (pub_u8 0x3d);
                                    secret (pub_u8 0x2);
                                    secret (pub_u8 0x1)
                                  ]
                                in assert_norm (List.Tot.length l == 9); l))
                          in
                          let oid_76 =
                            seq_slice (seq2_72) (usize 1) (usize 9)
                          in
                          let ec_pk_oid_77 =
                            true
                          in
                          let (ec_pk_oid_77) =
                            foldi (usize 0) (usize 9) (fun i_78 (ec_pk_oid_77
                              ) ->
                              let oid_byte_equal_79 =
                                (
                                  uint8_declassify (
                                    seq_index (oid_76) (i_78))) = (
                                  uint8_declassify (
                                    seq_index (expected_75) (i_78)))
                              in
                              let ec_pk_oid_77 =
                                (ec_pk_oid_77) && (oid_byte_equal_79)
                              in
                              (ec_pk_oid_77))
                            (ec_pk_oid_77)
                          in
                          let (pk_65) =
                            if ec_pk_oid_77 then begin
                              let bit_string_80 =
                                seq_slice (seq2_72) ((oid_len_74) + (usize 1)) (
                                  ((seq_len (seq2_72)) - (oid_len_74)) - (
                                    usize 1))
                              in
                              let (pk_65) =
                                if (
                                  uint8_declassify (
                                    seq_index (bit_string_80) (usize 0))) = (
                                  pub_u8 0x3) then begin
                                  let pk_len_81 =
                                    declassify_usize_from_uint8 (
                                      seq_index (bit_string_80) (usize 1))
                                  in
                                  let zeroes_82 =
                                    declassify_usize_from_uint8 (
                                      seq_index (bit_string_80) (usize 2))
                                  in
                                  let uncompressed_83 =
                                    declassify_usize_from_uint8 (
                                      seq_index (bit_string_80) (usize 3))
                                  in
                                  let pk_65 =
                                    seq_slice (bit_string_80) (usize 4) (
                                      (pk_len_81) - (usize 2))
                                  in
                                  (pk_65)
                                end else begin (pk_65)
                                end
                              in
                              (pk_65)
                            end else begin (pk_65)
                            end
                          in
                          (pk_65)
                        end else begin (pk_65)
                        end
                      in
                      (pk_65)
                    end else begin (pk_65)
                    end
                  in
                  (pk_65)
                end else begin (pk_65)
                end
              in
              (pk_65)
            end else begin (pk_65)
            end
          in
          let seq1_64 =
            seq_slice (seq1_64) (len_69) ((seq_len (seq1_64)) - (len_69))
          in
          (seq1_64, pk_65)
        end else begin (seq1_64, pk_65)
        end
      in
      (seq1_64, pk_65))
    (seq1_64, pk_65)
  in
  if ((seq_len (pk_65)) = (usize 0)) then (
    Err ((InvalidCert_crypto_error))) else (Ok ((pk_65)))

let concat_signature
  (r_84 : p256_scalar)
  (s_85 : p256_scalar)
  : (result signature crypto_error) =
  let signature_86 =
    seq_concat (
      seq_concat (seq_new_ (secret (pub_u8 0x0)) (usize 0)) (
        nat_to_byte_seq_be (0xunknown) (r_84))) (
      nat_to_byte_seq_be (0xunknown) (s_85))
  in
  Ok ((signature_86))

let p256_sign
  (ps_87 : signature_key)
  (payload_88 : byte_seq)
  (ent_89 : entropy)
  : (result signature crypto_error) =
  let random_90 =
    array_from_seq (32) (seq_slice_range (ent_89) ((usize 0, usize 32)))
  in
  let nonce_91 =
    nat_from_byte_seq_be (0xunknown) (random_90)
  in
  match ecdsa_p256_sha256_sign (payload_88) (
    nat_from_byte_seq_be (0xunknown) (ps_87)) (nonce_91) with
  | Ok (r_92, s_93) -> concat_signature (r_92) (s_93)
  | Err _ -> Err ((CryptoError_crypto_error))

let sign
  (sa_94 : signature_scheme)
  (ps_95 : signature_key)
  (payload_96 : byte_seq)
  (ent_97 : entropy)
  : (result signature crypto_error) =
  match sa_94 with
  | EcdsaSecp256r1Sha256_signature_scheme -> p256_sign (ps_95) (payload_96) (
    ent_97)
  | ED25519_signature_scheme -> Err ((UnsupportedAlgorithm_crypto_error))
  | RsaPssRsaSha256_signature_scheme -> Err (
    (UnsupportedAlgorithm_crypto_error))

let p256_verify
  (pk_98 : verification_key)
  (payload_99 : byte_seq)
  (sig_100 : byte_seq)
  : (result () crypto_error) =
  let (pk_x_101, pk_y_102) =
    (
      nat_from_byte_seq_be (0xunknown) (seq_slice (pk_98) (usize 0) (usize 32)),
      nat_from_byte_seq_be (0xunknown) (seq_slice (pk_98) (usize 32) (usize 32))
    )
  in
  let (r_103, s_104) =
    (
      nat_from_byte_seq_be (0xunknown) (
        seq_slice (sig_100) (usize 0) (usize 32)),
      nat_from_byte_seq_be (0xunknown) (
        seq_slice (sig_100) (usize 32) (usize 32))
    )
  in
  match ecdsa_p256_sha256_verify (payload_99) ((pk_x_101, pk_y_102)) (
    (r_103, s_104)) with
  | Ok () -> Ok ((()))
  | Err _ -> Err ((VerifyFailed_crypto_error))

let verify
  (sa_105 : signature_scheme)
  (pk_106 : verification_key)
  (payload_107 : byte_seq)
  (sig_108 : byte_seq)
  : (result () crypto_error) =
  match sa_105 with
  | EcdsaSecp256r1Sha256_signature_scheme -> p256_verify (pk_106) (
    payload_107) (sig_108)
  | ED25519_signature_scheme -> Err ((UnsupportedAlgorithm_crypto_error))
  | RsaPssRsaSha256_signature_scheme -> Err (
    (UnsupportedAlgorithm_crypto_error))

let hkdf_extract
  (ha_109 : hash_algorithm)
  (k_110 : key)
  (salt_111 : key)
  : (result key crypto_error) =
  match ha_109 with
  | SHA256_hash_algorithm -> Ok ((seq_from_seq (extract (salt_111) (k_110))))
  | SHA384_hash_algorithm -> Err ((UnsupportedAlgorithm_crypto_error))

let hkdf_expand
  (ha_112 : hash_algorithm)
  (k_113 : key)
  (info_114 : byte_seq)
  (len_115 : uint_size)
  : (result key crypto_error) =
  match ha_112 with
  | SHA256_hash_algorithm -> match expand (k_113) (info_114) (len_115) with
  | Ok b_116 -> Ok ((seq_from_seq (b_116)))
  | Err _ -> Err ((HkdfError_crypto_error))
  | SHA384_hash_algorithm -> Err ((UnsupportedAlgorithm_crypto_error))

let aes128_encrypt
  (k_117 : aead_key)
  (iv_118 : aead_iv)
  (payload_119 : byte_seq)
  (ad_120 : byte_seq)
  : (result byte_seq crypto_error) =
  let (ctxt_121, tag_122) =
    encrypt_aes128 (key128_from_seq (k_117)) (aes_nonce_from_seq (iv_118)) (
      ad_120) (payload_119)
  in
  Ok ((seq_concat (ctxt_121) (seq_from_seq (tag_122))))

let chacha_encrypt
  (k_123 : aead_key)
  (iv_124 : aead_iv)
  (payload_125 : byte_seq)
  (ad_126 : byte_seq)
  : (result byte_seq crypto_error) =
  let (ctxt_127, tag_128) =
    chacha20_poly1305_encrypt (array_from_seq (32) (k_123)) (
      array_from_seq (12) (iv_124)) (ad_126) (payload_125)
  in
  Ok ((seq_concat (ctxt_127) (tag_128)))

let aead_encrypt
  (a_129 : aead_algorithm)
  (k_130 : aead_key)
  (iv_131 : aead_iv)
  (payload_132 : byte_seq)
  (ad_133 : byte_seq)
  : (result byte_seq crypto_error) =
  match a_129 with
  | Aes128Gcm_aead_algorithm -> aes128_encrypt (k_130) (iv_131) (payload_132) (
    ad_133)
  | Aes256Gcm_aead_algorithm -> Err ((UnsupportedAlgorithm_crypto_error))
  | Chacha20Poly1305_aead_algorithm -> chacha_encrypt (k_130) (iv_131) (
    payload_132) (ad_133)

let aes128_decrypt
  (k_134 : aead_key)
  (iv_135 : aead_iv)
  (ciphertext_136 : byte_seq)
  (ad_137 : byte_seq)
  : (result byte_seq crypto_error) =
  match decrypt_aes128 (key128_from_seq (k_134)) (aes_nonce_from_seq (iv_135)) (
    ad_137) (
    seq_slice_range (ciphertext_136) (
      (usize 0, (seq_len (ciphertext_136)) - (usize 16)))) (
    gf128_tag_from_seq (
      seq_slice_range (ciphertext_136) (
        ((seq_len (ciphertext_136)) - (usize 16), seq_len (ciphertext_136)
        )))) with
  | Ok m_138 -> Ok ((m_138))
  | Err _ -> Err ((MacFailed_crypto_error))

let chacha_decrypt
  (k_139 : aead_key)
  (iv_140 : aead_iv)
  (ciphertext_141 : byte_seq)
  (ad_142 : byte_seq)
  : (result byte_seq crypto_error) =
  match chacha20_poly1305_decrypt (array_from_seq (32) (k_139)) (
    array_from_seq (12) (iv_140)) (ad_142) (
    seq_slice_range (ciphertext_141) (
      (usize 0, (seq_len (ciphertext_141)) - (usize 16)))) (
    array_from_seq (16) (
      seq_slice_range (ciphertext_141) (
        ((seq_len (ciphertext_141)) - (usize 16), seq_len (ciphertext_141)
        )))) with
  | Ok ptxt_143 -> Ok ((ptxt_143))
  | Err _ -> Err ((MacFailed_crypto_error))

let aead_decrypt
  (a_144 : aead_algorithm)
  (k_145 : aead_key)
  (iv_146 : aead_iv)
  (ciphertext_147 : byte_seq)
  (ad_148 : byte_seq)
  : (result byte_seq crypto_error) =
  match a_144 with
  | Aes128Gcm_aead_algorithm -> aes128_decrypt (k_145) (iv_146) (
    ciphertext_147) (ad_148)
  | Aes256Gcm_aead_algorithm -> Err ((UnsupportedAlgorithm_crypto_error))
  | Chacha20Poly1305_aead_algorithm -> chacha_decrypt (k_145) (iv_146) (
    ciphertext_147) (ad_148)

