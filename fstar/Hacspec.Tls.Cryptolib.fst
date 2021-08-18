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

let p256_check_point_len (p_12 : dh_pk) : (result () crypto_error) =
  if ((seq_len (p_12)) <> (usize 64)) then (
    Err ((CryptoError_crypto_error))) else (Ok ((())))

let p256_ecdh (x_13 : dh_sk) (y_14 : dh_pk) : (result key crypto_error) =
  match (p256_check_point_len (y_14)) with
  | Err x -> Err x
  | Ok  _ ->
    let pk_15 =
      (
        nat_from_byte_seq_be (0xunknown) (
          seq_slice_range (y_14) ((usize 0, usize 32))),
        nat_from_byte_seq_be (0xunknown) (
          seq_slice_range (y_14) ((usize 32, usize 64)))
      )
    in
    match p256_point_mul (nat_from_byte_seq_be (0xunknown) (x_13)) (pk_15) with
    | Ok (x_16, y_17) -> Ok (
      (
        seq_concat (nat_to_byte_seq_be (0xunknown) (x_16)) (
          nat_to_byte_seq_be (0xunknown) (y_17))
      ))
    | Err _ -> Err ((CryptoError_crypto_error))

let ecdh
  (group_name_18 : named_group)
  (x_19 : dh_sk)
  (y_20 : dh_pk)
  : (result key crypto_error) =
  match group_name_18 with
  | Secp256r1_named_group -> p256_ecdh (x_19) (y_20)
  | X25519_named_group -> Ok (
    (
      seq_from_seq (
        x25519_scalarmult (array_from_seq (32) (x_19)) (
          array_from_seq (32) (y_20)))
    ))

type kem_scheme = named_group

type kem_sk = byte_seq

type kem_pk = byte_seq

let kem_priv_len (ks_21 : kem_scheme) : uint_size =
  dh_priv_len (ks_21)

let kem_pub_len (ks_22 : kem_scheme) : uint_size =
  dh_pub_len (ks_22)

let kem_priv_to_pub
  (ks_23 : kem_scheme)
  (sk_24 : kem_sk)
  : (result kem_pk crypto_error) =
  secret_to_public (ks_23) (sk_24)

let kem_keygen_inner
  (ks_25 : kem_scheme)
  (ent_26 : entropy)
  : (result (kem_sk & kem_pk) crypto_error) =
  let sk_27 =
    seq_from_seq (seq_slice_range (ent_26) ((usize 0, dh_priv_len (ks_25))))
  in
  match (kem_priv_to_pub (ks_25) (sk_27)) with
  | Err x -> Err x
  | Ok  pk_28 ->
    Ok (((sk_27, pk_28)))

let kem_keygen
  (ks_29 : kem_scheme)
  (ent_30 : entropy)
  : (result (kem_sk & kem_pk) crypto_error) =
  if ((seq_len (ent_30)) <. (dh_priv_len (ks_29))) then (
    Err ((InsufficientEntropy_crypto_error))) else (
    kem_keygen_inner (ks_29) (ent_30))

let kem_encap
  (ks_31 : kem_scheme)
  (pk_32 : kem_pk)
  (ent_33 : entropy)
  : (result (key & byte_seq) crypto_error) =
  match (kem_keygen (ks_31) (ent_33)) with
  | Err x -> Err x
  | Ok  (x_34, gx_35) ->
    match (ecdh (ks_31) (x_34) (pk_32)) with
    | Err x -> Err x
    | Ok  gxy_36 ->
      Ok (((gxy_36, gx_35)))

let kem_decap
  (ks_37 : kem_scheme)
  (ct_38 : byte_seq)
  (sk_39 : kem_sk)
  : (result key crypto_error) =
  match (ecdh (ks_37) (sk_39) (ct_38)) with
  | Err x -> Err x
  | Ok  gxy_40 ->
    Ok ((gxy_40))

let hash
  (ha_41 : hash_algorithm)
  (payload_42 : byte_seq)
  : (result digest crypto_error) =
  match ha_41 with
  | SHA256_hash_algorithm -> Ok ((seq_from_seq (sha256 (payload_42))))
  | SHA384_hash_algorithm -> Err ((UnsupportedAlgorithm_crypto_error))

let hmac_tag
  (ha_43 : hash_algorithm)
  (mk_44 : mac_key)
  (payload_45 : byte_seq)
  : (result hmac crypto_error) =
  match ha_43 with
  | SHA256_hash_algorithm -> Ok ((seq_from_seq (hmac (mk_44) (payload_45))))
  | SHA384_hash_algorithm -> Err ((UnsupportedAlgorithm_crypto_error))

let check_tag_len (a_46 : hmac) (b_47 : hmac) : (result () crypto_error) =
  if ((seq_len (a_46)) = (seq_len (b_47))) then (Ok ((()))) else (
    Err ((MacFailed_crypto_error)))

let check_bytes (a_48 : uint8) (b_49 : uint8) : (result () crypto_error) =
  if (not (uint8_equal (a_48) (b_49))) then (
    Err ((MacFailed_crypto_error))) else (Ok ((())))

let hmac_verify
  (ha_50 : hash_algorithm)
  (mk_51 : mac_key)
  (payload_52 : byte_seq)
  (m_53 : hmac)
  : (result () crypto_error) =
  match (hmac_tag (ha_50) (mk_51) (payload_52)) with
  | Err x -> Err x
  | Ok  my_hmac_54 ->
    match (check_tag_len (m_53) (my_hmac_54)) with
    | Err x -> Err x
    | Ok  _ ->
      match (
        foldi_result (usize 0) (seq_len (m_53)) (fun i_55 () ->
          match (
            check_bytes (seq_index (my_hmac_54) (i_55)) (
              seq_index (m_53) (i_55))) with
          | Err x -> Err x
          | Ok  _ ->
            Ok (()))
        ()) with
      | Err x -> Err x
      | Ok  () ->
        Ok ((()))

type ec_oid_tag = lseq (uint8) (usize 9)

let get_length_length (b_56 : byte_seq) : uint_size =
  if (
    (
      (uint8_declassify (seq_index (b_56) (usize 0))) `shift_right` (
        usize 7)) = (pub_u8 0x1)) then (
    declassify_usize_from_uint8 (
      (seq_index (b_56) (usize 0)) &. (secret (pub_u8 0x7f)))) else (usize 0)

let get_length (b_57 : byte_seq) (len_58 : uint_size) : uint_size =
  (
    v (
      cast U32 PUB (
        declassify_u32_from_uint32 (
          uint32_from_be_bytes (
            array_from_slice (secret (pub_u8 0x0)) (4) (b_57) (usize 0) (
              len_58)))))) `usize_shift_right` (
    ((usize 4) - (len_58)) * (usize 8))

let get_short_length (b_59 : byte_seq) : uint_size =
  declassify_usize_from_uint8 (
    (seq_index (b_59) (usize 0)) &. (secret (pub_u8 0x7f)))

let verification_key_from_cert
  (cert_60 : byte_seq)
  : (result verification_key crypto_error) =
  let skip_61 =
    (
      (usize 2) + (
        get_length_length (
          seq_slice_range (cert_60) ((usize 1, seq_len (cert_60)))))) + (
      usize 1)
  in
  let seq1_len_len_62 =
    get_length_length (seq_slice_range (cert_60) ((skip_61, seq_len (cert_60))))
  in
  let skip_63 =
    (skip_61) + (usize 1)
  in
  let seq1_len_64 =
    get_length (
      seq_slice (cert_60) (skip_63) ((seq_len (cert_60)) - (skip_63))) (
      seq1_len_len_62)
  in
  let seq1_65 =
    seq_slice_range (cert_60) (
      (
        (skip_63) + (seq1_len_len_62),
        ((skip_63) + (seq1_len_len_62)) + (seq1_len_64)
      ))
  in
  let pk_66 =
    seq_new_ (secret (pub_u8 0x0)) (usize 0)
  in
  let (seq1_65, pk_66) =
    foldi (usize 0) (seq_len (seq1_65)) (fun i_67 (seq1_65, pk_66) ->
      let (seq1_65, pk_66) =
        if (seq_len (seq1_65)) >. (usize 0) then begin
          let element_type_68 =
            uint8_declassify (seq_index (seq1_65) (usize 0))
          in
          let seq1_65 =
            seq_slice (seq1_65) (usize 1) ((seq_len (seq1_65)) - (usize 1))
          in
          let len_len_69 =
            get_length_length (seq1_65)
          in
          let len_70 =
            get_short_length (seq1_65)
          in
          let seq1_65 =
            seq_slice (seq1_65) (usize 1) ((seq_len (seq1_65)) - (usize 1))
          in
          let (len_70) =
            if (len_len_69) <> (usize 0) then begin
              let len_70 =
                (get_length (seq1_65) (len_len_69)) + (len_len_69)
              in
              (len_70)
            end else begin (len_70)
            end
          in
          let (pk_66) =
            if ((element_type_68) = (pub_u8 0x30)) && (
              (seq_len (pk_66)) = (usize 0)) then begin
              let seq2_71 =
                seq_slice (seq1_65) (len_len_69) (len_70)
              in
              let element_type_72 =
                uint8_declassify (seq_index (seq2_71) (usize 0))
              in
              let seq2_73 =
                seq_slice (seq2_71) (usize 1) ((seq_len (seq2_71)) - (usize 1))
              in
              let (pk_66) =
                if (element_type_72) = (pub_u8 0x30) then begin
                  let len_len_74 =
                    get_length_length (seq2_73)
                  in
                  let (pk_66) =
                    if (len_len_74) = (usize 0) then begin
                      let oid_len_75 =
                        get_short_length (seq2_73)
                      in
                      let (pk_66) =
                        if (oid_len_75) >=. (usize 9) then begin
                          let expected_76 =
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
                          let oid_77 =
                            seq_slice (seq2_73) (usize 1) (usize 9)
                          in
                          let ec_pk_oid_78 =
                            true
                          in
                          let (ec_pk_oid_78) =
                            foldi (usize 0) (usize 9) (fun i_79 (ec_pk_oid_78
                              ) ->
                              let oid_byte_equal_80 =
                                (
                                  uint8_declassify (
                                    seq_index (oid_77) (i_79))) = (
                                  uint8_declassify (
                                    seq_index (expected_76) (i_79)))
                              in
                              let ec_pk_oid_78 =
                                (ec_pk_oid_78) && (oid_byte_equal_80)
                              in
                              (ec_pk_oid_78))
                            (ec_pk_oid_78)
                          in
                          let (pk_66) =
                            if ec_pk_oid_78 then begin
                              let bit_string_81 =
                                seq_slice (seq2_73) ((oid_len_75) + (usize 1)) (
                                  ((seq_len (seq2_73)) - (oid_len_75)) - (
                                    usize 1))
                              in
                              let (pk_66) =
                                if (
                                  uint8_declassify (
                                    seq_index (bit_string_81) (usize 0))) = (
                                  pub_u8 0x3) then begin
                                  let pk_len_82 =
                                    declassify_usize_from_uint8 (
                                      seq_index (bit_string_81) (usize 1))
                                  in
                                  let zeroes_83 =
                                    declassify_usize_from_uint8 (
                                      seq_index (bit_string_81) (usize 2))
                                  in
                                  let uncompressed_84 =
                                    declassify_usize_from_uint8 (
                                      seq_index (bit_string_81) (usize 3))
                                  in
                                  let pk_66 =
                                    seq_slice (bit_string_81) (usize 4) (
                                      (pk_len_82) - (usize 2))
                                  in
                                  (pk_66)
                                end else begin (pk_66)
                                end
                              in
                              (pk_66)
                            end else begin (pk_66)
                            end
                          in
                          (pk_66)
                        end else begin (pk_66)
                        end
                      in
                      (pk_66)
                    end else begin (pk_66)
                    end
                  in
                  (pk_66)
                end else begin (pk_66)
                end
              in
              (pk_66)
            end else begin (pk_66)
            end
          in
          let seq1_65 =
            seq_slice (seq1_65) (len_70) ((seq_len (seq1_65)) - (len_70))
          in
          (seq1_65, pk_66)
        end else begin (seq1_65, pk_66)
        end
      in
      (seq1_65, pk_66))
    (seq1_65, pk_66)
  in
  if ((seq_len (pk_66)) = (usize 0)) then (
    Err ((InvalidCert_crypto_error))) else (Ok ((pk_66)))

let concat_signature
  (r_85 : p256_scalar)
  (s_86 : p256_scalar)
  : (result signature crypto_error) =
  let signature_87 =
    seq_concat (
      seq_concat (seq_new_ (secret (pub_u8 0x0)) (usize 0)) (
        nat_to_byte_seq_be (0xunknown) (r_85))) (
      nat_to_byte_seq_be (0xunknown) (s_86))
  in
  Ok ((signature_87))

let p256_sign
  (ps_88 : signature_key)
  (payload_89 : byte_seq)
  (ent_90 : entropy)
  : (result signature crypto_error) =
  let random_91 =
    array_from_seq (32) (seq_slice_range (ent_90) ((usize 0, usize 32)))
  in
  let nonce_92 =
    nat_from_byte_seq_be (0xunknown) (random_91)
  in
  match ecdsa_p256_sha256_sign (payload_89) (
    nat_from_byte_seq_be (0xunknown) (ps_88)) (nonce_92) with
  | Ok (r_93, s_94) -> concat_signature (r_93) (s_94)
  | Err _ -> Err ((CryptoError_crypto_error))

let sign
  (sa_95 : signature_scheme)
  (ps_96 : signature_key)
  (payload_97 : byte_seq)
  (ent_98 : entropy)
  : (result signature crypto_error) =
  match sa_95 with
  | EcdsaSecp256r1Sha256_signature_scheme -> p256_sign (ps_96) (payload_97) (
    ent_98)
  | ED25519_signature_scheme -> Err ((UnsupportedAlgorithm_crypto_error))
  | RsaPssRsaSha256_signature_scheme -> Err (
    (UnsupportedAlgorithm_crypto_error))

let p256_verify
  (pk_99 : verification_key)
  (payload_100 : byte_seq)
  (sig_101 : byte_seq)
  : (result () crypto_error) =
  let (pk_x_102, pk_y_103) =
    (
      nat_from_byte_seq_be (0xunknown) (seq_slice (pk_99) (usize 0) (usize 32)),
      nat_from_byte_seq_be (0xunknown) (seq_slice (pk_99) (usize 32) (usize 32))
    )
  in
  let (r_104, s_105) =
    (
      nat_from_byte_seq_be (0xunknown) (
        seq_slice (sig_101) (usize 0) (usize 32)),
      nat_from_byte_seq_be (0xunknown) (
        seq_slice (sig_101) (usize 32) (usize 32))
    )
  in
  match ecdsa_p256_sha256_verify (payload_100) ((pk_x_102, pk_y_103)) (
    (r_104, s_105)) with
  | Ok () -> Ok ((()))
  | Err _ -> Err ((VerifyFailed_crypto_error))

let verify
  (sa_106 : signature_scheme)
  (pk_107 : verification_key)
  (payload_108 : byte_seq)
  (sig_109 : byte_seq)
  : (result () crypto_error) =
  match sa_106 with
  | EcdsaSecp256r1Sha256_signature_scheme -> p256_verify (pk_107) (
    payload_108) (sig_109)
  | ED25519_signature_scheme -> Err ((UnsupportedAlgorithm_crypto_error))
  | RsaPssRsaSha256_signature_scheme -> Err (
    (UnsupportedAlgorithm_crypto_error))

let hkdf_extract
  (ha_110 : hash_algorithm)
  (k_111 : key)
  (salt_112 : key)
  : (result key crypto_error) =
  match ha_110 with
  | SHA256_hash_algorithm -> Ok ((seq_from_seq (extract (salt_112) (k_111))))
  | SHA384_hash_algorithm -> Err ((UnsupportedAlgorithm_crypto_error))

let hkdf_expand
  (ha_113 : hash_algorithm)
  (k_114 : key)
  (info_115 : byte_seq)
  (len_116 : uint_size)
  : (result key crypto_error) =
  match ha_113 with
  | SHA256_hash_algorithm -> match expand (k_114) (info_115) (len_116) with
  | Ok b_117 -> Ok ((seq_from_seq (b_117)))
  | Err _ -> Err ((HkdfError_crypto_error))
  | SHA384_hash_algorithm -> Err ((UnsupportedAlgorithm_crypto_error))

let aes128_encrypt
  (k_118 : aead_key)
  (iv_119 : aead_iv)
  (payload_120 : byte_seq)
  (ad_121 : byte_seq)
  : (result byte_seq crypto_error) =
  let (ctxt_122, tag_123) =
    encrypt_aes128 (key128_from_seq (k_118)) (aes_nonce_from_seq (iv_119)) (
      ad_121) (payload_120)
  in
  Ok ((seq_concat (ctxt_122) (seq_from_seq (tag_123))))

let chacha_encrypt
  (k_124 : aead_key)
  (iv_125 : aead_iv)
  (payload_126 : byte_seq)
  (ad_127 : byte_seq)
  : (result byte_seq crypto_error) =
  let (ctxt_128, tag_129) =
    chacha20_poly1305_encrypt (array_from_seq (32) (k_124)) (
      array_from_seq (12) (iv_125)) (ad_127) (payload_126)
  in
  Ok ((seq_concat (ctxt_128) (tag_129)))

let aead_encrypt
  (a_130 : aead_algorithm)
  (k_131 : aead_key)
  (iv_132 : aead_iv)
  (payload_133 : byte_seq)
  (ad_134 : byte_seq)
  : (result byte_seq crypto_error) =
  match a_130 with
  | Aes128Gcm_aead_algorithm -> aes128_encrypt (k_131) (iv_132) (payload_133) (
    ad_134)
  | Aes256Gcm_aead_algorithm -> Err ((UnsupportedAlgorithm_crypto_error))
  | Chacha20Poly1305_aead_algorithm -> chacha_encrypt (k_131) (iv_132) (
    payload_133) (ad_134)

let aes128_decrypt
  (k_135 : aead_key)
  (iv_136 : aead_iv)
  (ciphertext_137 : byte_seq)
  (ad_138 : byte_seq)
  : (result byte_seq crypto_error) =
  match decrypt_aes128 (key128_from_seq (k_135)) (aes_nonce_from_seq (iv_136)) (
    ad_138) (
    seq_slice_range (ciphertext_137) (
      (usize 0, (seq_len (ciphertext_137)) - (usize 16)))) (
    gf128_tag_from_seq (
      seq_slice_range (ciphertext_137) (
        ((seq_len (ciphertext_137)) - (usize 16), seq_len (ciphertext_137)
        )))) with
  | Ok m_139 -> Ok ((m_139))
  | Err _ -> Err ((MacFailed_crypto_error))

let chacha_decrypt
  (k_140 : aead_key)
  (iv_141 : aead_iv)
  (ciphertext_142 : byte_seq)
  (ad_143 : byte_seq)
  : (result byte_seq crypto_error) =
  match chacha20_poly1305_decrypt (array_from_seq (32) (k_140)) (
    array_from_seq (12) (iv_141)) (ad_143) (
    seq_slice_range (ciphertext_142) (
      (usize 0, (seq_len (ciphertext_142)) - (usize 16)))) (
    array_from_seq (16) (
      seq_slice_range (ciphertext_142) (
        ((seq_len (ciphertext_142)) - (usize 16), seq_len (ciphertext_142)
        )))) with
  | Ok ptxt_144 -> Ok ((ptxt_144))
  | Err _ -> Err ((MacFailed_crypto_error))

let aead_decrypt
  (a_145 : aead_algorithm)
  (k_146 : aead_key)
  (iv_147 : aead_iv)
  (ciphertext_148 : byte_seq)
  (ad_149 : byte_seq)
  : (result byte_seq crypto_error) =
  match a_145 with
  | Aes128Gcm_aead_algorithm -> aes128_decrypt (k_146) (iv_147) (
    ciphertext_148) (ad_149)
  | Aes256Gcm_aead_algorithm -> Err ((UnsupportedAlgorithm_crypto_error))
  | Chacha20Poly1305_aead_algorithm -> chacha_decrypt (k_146) (iv_147) (
    ciphertext_148) (ad_149)

