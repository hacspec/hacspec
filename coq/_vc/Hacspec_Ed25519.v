(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Hacspec_Sha512.

Require Import Hacspec_Edwards25519.

Definition scalar_from_hash (h_1954 : sha512_digest_t) : scalar_t :=
  let s_1955 : big_scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (h_1954)) : big_scalar_t in 
  nat_mod_from_byte_seq_le (seq_slice (nat_mod_to_byte_seq_le (s_1955)) (
      usize 0) (usize 32)) : scalar_t.

Definition sign (sk_1956 : secret_key_t) (msg_1957 : byte_seq) : signature_t :=
  let '(a_1958, prefix_1959) :=
    secret_expand (sk_1956) in 
  let a_1960 : scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (a_1958)) : scalar_t in 
  let b_1961 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let a_p_1962 : compressed_ed_point_t :=
    compress (point_mul (a_1960) (b_1961)) in 
  let r_1963 : scalar_t :=
    scalar_from_hash (sha512 (array_concat (prefix_1959) (msg_1957))) in 
  let r_p_1964 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul (r_1963) (b_1961) in 
  let r_s_1965 : compressed_ed_point_t :=
    compress (r_p_1964) in 
  let h_1966 : scalar_t :=
    scalar_from_hash (sha512 (seq_concat (array_concat (r_s_1965) (
            array_to_seq (a_p_1962))) (msg_1957))) in 
  let s_1967 : scalar_t :=
    (r_1963) +% ((h_1966) *% (a_1960)) in 
  let s_bytes_1968 : seq uint8 :=
    seq_slice (nat_mod_to_byte_seq_le (s_1967)) (usize 0) (usize 32) in 
  array_update (array_update (array_new_ (default : uint8) (64)) (usize 0) (
      array_to_seq (r_s_1965))) (usize 32) (s_bytes_1968).

Definition zcash_verify
  (pk_1969 : public_key_t)
  (signature_1970 : signature_t)
  (msg_1971 : byte_seq)
  : verify_result_t :=
  let b_1972 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress_non_canonical (base_v)) in 
  let a_1973 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_ok_or (decompress_non_canonical (pk_1969)) (InvalidPublickey) in 
  let r_bytes_1974 : compressed_ed_point_t :=
    array_from_slice (default : uint8) (32) (array_to_seq (signature_1970)) (
      usize 0) (usize 32) in 
  let s_bytes_1975 : serialized_scalar_t :=
    array_from_slice (default : uint8) (32) (array_to_seq (signature_1970)) (
      usize 32) (usize 32) in 
  let 'tt :=
    if negb (check_canonical_scalar (s_bytes_1975)):bool then (let _ : unit :=
        @Err unit error_t (InvalidS) in 
      tt) else (tt) in 
  let r_1976 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_ok_or (decompress_non_canonical (r_bytes_1974)) (InvalidR) in 
  let s_1977 : scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1975)) : scalar_t in 
  let k_1978 : scalar_t :=
    scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1974) (
            pk_1969)) (msg_1971))) in 
  let sb_1979 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul_by_cofactor (point_mul (s_1977) (b_1972)) in 
  let rc_1980 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul_by_cofactor (r_1976) in 
  let ka_1981 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul_by_cofactor (point_mul (k_1978) (a_1973)) in 
  (if (point_eq (sb_1979) (point_add (rc_1980) (ka_1981))):bool then (
      @Ok unit error_t (tt)) else (@Err unit error_t (InvalidSignature))).

Definition ietf_cofactored_verify
  (pk_1982 : public_key_t)
  (signature_1983 : signature_t)
  (msg_1984 : byte_seq)
  : verify_result_t :=
  let b_1985 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let a_1986 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_ok_or (decompress (pk_1982)) (InvalidPublickey) in 
  let r_bytes_1987 : compressed_ed_point_t :=
    array_from_slice (default : uint8) (32) (array_to_seq (signature_1983)) (
      usize 0) (usize 32) in 
  let s_bytes_1988 : serialized_scalar_t :=
    array_from_slice (default : uint8) (32) (array_to_seq (signature_1983)) (
      usize 32) (usize 32) in 
  let 'tt :=
    if negb (check_canonical_scalar (s_bytes_1988)):bool then (let _ : unit :=
        @Err unit error_t (InvalidS) in 
      tt) else (tt) in 
  let r_1989 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_ok_or (decompress (r_bytes_1987)) (InvalidR) in 
  let s_1990 : scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1988)) : scalar_t in 
  let k_1991 : scalar_t :=
    scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1987) (
            pk_1982)) (msg_1984))) in 
  let sb_1992 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul_by_cofactor (point_mul (s_1990) (b_1985)) in 
  let rc_1993 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul_by_cofactor (r_1989) in 
  let ka_1994 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul_by_cofactor (point_mul (k_1991) (a_1986)) in 
  (if (point_eq (sb_1992) (point_add (rc_1993) (ka_1994))):bool then (
      @Ok unit error_t (tt)) else (@Err unit error_t (InvalidSignature))).

Definition ietf_cofactorless_verify
  (pk_1995 : public_key_t)
  (signature_1996 : signature_t)
  (msg_1997 : byte_seq)
  : verify_result_t :=
  let b_1998 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let a_1999 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_ok_or (decompress (pk_1995)) (InvalidPublickey) in 
  let r_bytes_2000 : compressed_ed_point_t :=
    array_from_slice (default : uint8) (32) (array_to_seq (signature_1996)) (
      usize 0) (usize 32) in 
  let s_bytes_2001 : serialized_scalar_t :=
    array_from_slice (default : uint8) (32) (array_to_seq (signature_1996)) (
      usize 32) (usize 32) in 
  let 'tt :=
    if negb (check_canonical_scalar (s_bytes_2001)):bool then (let _ : unit :=
        @Err unit error_t (InvalidS) in 
      tt) else (tt) in 
  let r_2002 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_ok_or (decompress (r_bytes_2000)) (InvalidR) in 
  let s_2003 : scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (s_bytes_2001)) : scalar_t in 
  let k_2004 : scalar_t :=
    scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_2000) (
            pk_1995)) (msg_1997))) in 
  let sb_2005 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul (s_2003) (b_1998) in 
  let ka_2006 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul (k_2004) (a_1999) in 
  (if (point_eq (sb_2005) (point_add (r_2002) (ka_2006))):bool then (
      @Ok unit error_t (tt)) else (@Err unit error_t (InvalidSignature))).

Definition is_identity (p_2007 : ed_point_t) : bool :=
  point_eq (p_2007) (point_identity ).

Definition alg2_verify
  (pk_2008 : public_key_t)
  (signature_2009 : signature_t)
  (msg_2010 : byte_seq)
  : verify_result_t :=
  let b_2011 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let a_2012 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_ok_or (decompress (pk_2008)) (InvalidPublickey) in 
  let 'tt :=
    if is_identity (point_mul_by_cofactor (a_2012)):bool then (let _ : unit :=
        @Err unit error_t (SmallOrderPoint) in 
      tt) else (tt) in 
  let r_bytes_2013 : compressed_ed_point_t :=
    array_from_slice (default : uint8) (32) (array_to_seq (signature_2009)) (
      usize 0) (usize 32) in 
  let s_bytes_2014 : serialized_scalar_t :=
    array_from_slice (default : uint8) (32) (array_to_seq (signature_2009)) (
      usize 32) (usize 32) in 
  let 'tt :=
    if negb (check_canonical_scalar (s_bytes_2014)):bool then (let _ : unit :=
        @Err unit error_t (InvalidS) in 
      tt) else (tt) in 
  let r_2015 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_ok_or (decompress (r_bytes_2013)) (InvalidR) in 
  let s_2016 : scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (s_bytes_2014)) : scalar_t in 
  let k_2017 : scalar_t :=
    scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_2013) (
            pk_2008)) (msg_2010))) in 
  let sb_2018 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul_by_cofactor (point_mul (s_2016) (b_2011)) in 
  let rc_2019 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul_by_cofactor (r_2015) in 
  let ka_2020 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul_by_cofactor (point_mul (k_2017) (a_2012)) in 
  (if (point_eq (sb_2018) (point_add (rc_2019) (ka_2020))):bool then (
      @Ok unit error_t (tt)) else (@Err unit error_t (InvalidSignature))).

Inductive batch_entry_t :=
| BatchEntry : (public_key_t × byte_seq × signature_t) -> batch_entry_t.

Definition zcash_batch_verify
  (entries_2021 : seq batch_entry_t)
  (entropy_2022 : byte_seq)
  : verify_result_t :=
  let 'tt :=
    if (seq_len (entropy_2022)) <.? ((usize 16) * (seq_len (
          entries_2021))):bool then (let _ : unit :=
        @Err unit error_t (NotEnoughRandomness) in 
      tt) else (tt) in 
  let s_sum_2023 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_2024 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_2025 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let '(s_sum_2023, r_sum_2024, a_sum_2025) :=
    foldi (usize 0) (seq_len (entries_2021)) (fun i_2026 '(
        s_sum_2023,
        r_sum_2024,
        a_sum_2025
      ) =>
      let 'BatchEntry ((pk_2027, msg_2028, signature_2029)) :=
        (seq_index (entries_2021) (i_2026)) in 
      let a_2030 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress_non_canonical (pk_2027)) (InvalidPublickey) in 
      let r_bytes_2031 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_2029)) (usize 0) (usize 32) in 
      let s_bytes_2032 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_2029)) (usize 32) (usize 32) in 
      let 'tt :=
        if negb (check_canonical_scalar (s_bytes_2032)):bool then (
          let _ : unit :=
            @Err unit error_t (InvalidS) in 
          tt) else (tt) in 
      let r_2033 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress_non_canonical (r_bytes_2031)) (InvalidR) in 
      let s_2034 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_2032)) : scalar_t in 
      let c_2035 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_2031) (
                array_to_seq (pk_2027))) (msg_2028))) in 
      let z_2036 : seq uint8 :=
        seq_slice (entropy_2022) ((usize 16) * (i_2026)) (usize 16) in 
      let z_2037 : scalar_t :=
        nat_mod_from_byte_seq_le (seq_concat (z_2036) (seq_new_ (
              default : uint8) (usize 16))) : scalar_t in 
      let s_sum_2023 :=
        (s_sum_2023) +% ((s_2034) *% (z_2037)) in 
      let r_sum_2024 :=
        point_add (r_sum_2024) (point_mul (z_2037) (r_2033)) in 
      let a_sum_2025 :=
        point_add (a_sum_2025) (point_mul ((z_2037) *% (c_2035)) (a_2030)) in 
      (s_sum_2023, r_sum_2024, a_sum_2025))
    (s_sum_2023, r_sum_2024, a_sum_2025) in 
  let b_2038 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let sb_2039 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul (s_sum_2023) (b_2038) in 
  let check_2040 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul_by_cofactor (point_add (point_neg (sb_2039)) (point_add (
          r_sum_2024) (a_sum_2025))) in 
  (if (is_identity (check_2040)):bool then (@Ok unit error_t (tt)) else (
      @Err unit error_t (InvalidSignature))).

Definition ietf_cofactored_batch_verify
  (entries_2041 : seq batch_entry_t)
  (entropy_2042 : byte_seq)
  : verify_result_t :=
  let 'tt :=
    if (seq_len (entropy_2042)) <.? ((usize 16) * (seq_len (
          entries_2041))):bool then (let _ : unit :=
        @Err unit error_t (NotEnoughRandomness) in 
      tt) else (tt) in 
  let s_sum_2043 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_2044 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_2045 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let '(s_sum_2043, r_sum_2044, a_sum_2045) :=
    foldi (usize 0) (seq_len (entries_2041)) (fun i_2046 '(
        s_sum_2043,
        r_sum_2044,
        a_sum_2045
      ) =>
      let 'BatchEntry ((pk_2047, msg_2048, signature_2049)) :=
        (seq_index (entries_2041) (i_2046)) in 
      let a_2050 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (pk_2047)) (InvalidPublickey) in 
      let r_bytes_2051 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_2049)) (usize 0) (usize 32) in 
      let s_bytes_2052 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_2049)) (usize 32) (usize 32) in 
      let 'tt :=
        if negb (check_canonical_scalar (s_bytes_2052)):bool then (
          let _ : unit :=
            @Err unit error_t (InvalidS) in 
          tt) else (tt) in 
      let r_2053 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (r_bytes_2051)) (InvalidR) in 
      let s_2054 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_2052)) : scalar_t in 
      let c_2055 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_2051) (
                array_to_seq (pk_2047))) (msg_2048))) in 
      let z_2056 : seq uint8 :=
        seq_slice (entropy_2042) ((usize 16) * (i_2046)) (usize 16) in 
      let z_2057 : scalar_t :=
        nat_mod_from_byte_seq_le (seq_concat (z_2056) (seq_new_ (
              default : uint8) (usize 16))) : scalar_t in 
      let s_sum_2043 :=
        (s_sum_2043) +% ((s_2054) *% (z_2057)) in 
      let r_sum_2044 :=
        point_add (r_sum_2044) (point_mul (z_2057) (r_2053)) in 
      let a_sum_2045 :=
        point_add (a_sum_2045) (point_mul ((z_2057) *% (c_2055)) (a_2050)) in 
      (s_sum_2043, r_sum_2044, a_sum_2045))
    (s_sum_2043, r_sum_2044, a_sum_2045) in 
  let b_2058 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let sb_2059 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul (s_sum_2043) (b_2058) in 
  let check_2060 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul_by_cofactor (point_add (point_neg (sb_2059)) (point_add (
          r_sum_2044) (a_sum_2045))) in 
  (if (is_identity (check_2060)):bool then (@Ok unit error_t (tt)) else (
      @Err unit error_t (InvalidSignature))).

Definition ietf_cofactorless_batch_verify
  (entries_2061 : seq batch_entry_t)
  (entropy_2062 : byte_seq)
  : verify_result_t :=
  let 'tt :=
    if (seq_len (entropy_2062)) <.? ((usize 16) * (seq_len (
          entries_2061))):bool then (let _ : unit :=
        @Err unit error_t (NotEnoughRandomness) in 
      tt) else (tt) in 
  let s_sum_2063 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_2064 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_2065 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let '(s_sum_2063, r_sum_2064, a_sum_2065) :=
    foldi (usize 0) (seq_len (entries_2061)) (fun i_2066 '(
        s_sum_2063,
        r_sum_2064,
        a_sum_2065
      ) =>
      let 'BatchEntry ((pk_2067, msg_2068, signature_2069)) :=
        (seq_index (entries_2061) (i_2066)) in 
      let a_2070 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (pk_2067)) (InvalidPublickey) in 
      let r_bytes_2071 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_2069)) (usize 0) (usize 32) in 
      let s_bytes_2072 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_2069)) (usize 32) (usize 32) in 
      let 'tt :=
        if negb (check_canonical_scalar (s_bytes_2072)):bool then (
          let _ : unit :=
            @Err unit error_t (InvalidS) in 
          tt) else (tt) in 
      let r_2073 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (r_bytes_2071)) (InvalidR) in 
      let s_2074 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_2072)) : scalar_t in 
      let c_2075 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_2071) (
                array_to_seq (pk_2067))) (msg_2068))) in 
      let z_2076 : seq uint8 :=
        seq_slice (entropy_2062) ((usize 16) * (i_2066)) (usize 16) in 
      let z_2077 : scalar_t :=
        nat_mod_from_byte_seq_le (seq_concat (z_2076) (seq_new_ (
              default : uint8) (usize 16))) : scalar_t in 
      let s_sum_2063 :=
        (s_sum_2063) +% ((s_2074) *% (z_2077)) in 
      let r_sum_2064 :=
        point_add (r_sum_2064) (point_mul (z_2077) (r_2073)) in 
      let a_sum_2065 :=
        point_add (a_sum_2065) (point_mul ((z_2077) *% (c_2075)) (a_2070)) in 
      (s_sum_2063, r_sum_2064, a_sum_2065))
    (s_sum_2063, r_sum_2064, a_sum_2065) in 
  let b_2078 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let sb_2079 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul (s_sum_2063) (b_2078) in 
  let check_2080 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_add (point_neg (sb_2079)) (point_add (r_sum_2064) (a_sum_2065)) in 
  (if (is_identity (check_2080)):bool then (@Ok unit error_t (tt)) else (
      @Err unit error_t (InvalidSignature))).

Definition alg3_batch_verify
  (entries_2081 : seq batch_entry_t)
  (entropy_2082 : byte_seq)
  : verify_result_t :=
  let 'tt :=
    if (seq_len (entropy_2082)) <.? ((usize 16) * (seq_len (
          entries_2081))):bool then (let _ : unit :=
        @Err unit error_t (NotEnoughRandomness) in 
      tt) else (tt) in 
  let s_sum_2083 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_2084 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_2085 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let '(s_sum_2083, r_sum_2084, a_sum_2085) :=
    foldi (usize 0) (seq_len (entries_2081)) (fun i_2086 '(
        s_sum_2083,
        r_sum_2084,
        a_sum_2085
      ) =>
      let 'BatchEntry ((pk_2087, msg_2088, signature_2089)) :=
        (seq_index (entries_2081) (i_2086)) in 
      let a_2090 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (pk_2087)) (InvalidPublickey) in 
      let 'tt :=
        if is_identity (point_mul_by_cofactor (a_2090)):bool then (
          let _ : unit :=
            @Err unit error_t (SmallOrderPoint) in 
          tt) else (tt) in 
      let r_bytes_2091 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_2089)) (usize 0) (usize 32) in 
      let s_bytes_2092 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_2089)) (usize 32) (usize 32) in 
      let 'tt :=
        if negb (check_canonical_scalar (s_bytes_2092)):bool then (
          let _ : unit :=
            @Err unit error_t (InvalidS) in 
          tt) else (tt) in 
      let r_2093 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (r_bytes_2091)) (InvalidR) in 
      let s_2094 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_2092)) : scalar_t in 
      let c_2095 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_2091) (
                array_to_seq (pk_2087))) (msg_2088))) in 
      let z_2096 : seq uint8 :=
        seq_slice (entropy_2082) ((usize 16) * (i_2086)) (usize 16) in 
      let z_2097 : scalar_t :=
        nat_mod_from_byte_seq_le (seq_concat (z_2096) (seq_new_ (
              default : uint8) (usize 16))) : scalar_t in 
      let s_sum_2083 :=
        (s_sum_2083) +% ((s_2094) *% (z_2097)) in 
      let r_sum_2084 :=
        point_add (r_sum_2084) (point_mul (z_2097) (r_2093)) in 
      let a_sum_2085 :=
        point_add (a_sum_2085) (point_mul ((z_2097) *% (c_2095)) (a_2090)) in 
      (s_sum_2083, r_sum_2084, a_sum_2085))
    (s_sum_2083, r_sum_2084, a_sum_2085) in 
  let b_2098 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let sb_2099 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul (s_sum_2083) (b_2098) in 
  let check_2100 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul_by_cofactor (point_add (point_neg (sb_2099)) (point_add (
          r_sum_2084) (a_sum_2085))) in 
  (if (is_identity (check_2100)):bool then (@Ok unit error_t (tt)) else (
      @Err unit error_t (InvalidSignature))).

