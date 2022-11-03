(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Hacspec_Sha512.

Require Import Hacspec_Edwards25519.

Definition scalar_from_hash (h_1896 : sha512_digest_t) : scalar_t :=
  let s_1897 : big_scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (h_1896)) : big_scalar_t in 
  nat_mod_from_byte_seq_le (seq_slice (nat_mod_to_byte_seq_le (s_1897)) (
      usize 0) (usize 32)) : scalar_t.

Definition sign (sk_1898 : secret_key_t) (msg_1899 : byte_seq) : signature_t :=
  let '(a_1900, prefix_1901) :=
    secret_expand (sk_1898) in 
  let a_1902 : scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (a_1900)) : scalar_t in 
  let b_1903 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let a_p_1904 : compressed_ed_point_t :=
    compress (point_mul (a_1902) (b_1903)) in 
  let r_1905 : scalar_t :=
    scalar_from_hash (sha512 (array_concat (prefix_1901) (msg_1899))) in 
  let r_p_1906 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul (r_1905) (b_1903) in 
  let r_s_1907 : compressed_ed_point_t :=
    compress (r_p_1906) in 
  let h_1908 : scalar_t :=
    scalar_from_hash (sha512 (seq_concat (array_concat (r_s_1907) (
            array_to_seq (a_p_1904))) (msg_1899))) in 
  let s_1909 : scalar_t :=
    (r_1905) +% ((h_1908) *% (a_1902)) in 
  let s_bytes_1910 : seq uint8 :=
    seq_slice (nat_mod_to_byte_seq_le (s_1909)) (usize 0) (usize 32) in 
  array_update (array_update (array_new_ (default) (64)) (usize 0) (
      array_to_seq (r_s_1907))) (usize 32) (s_bytes_1910).

Definition zcash_verify
  (pk_1911 : public_key_t)
  (signature_1912 : signature_t)
  (msg_1913 : byte_seq)
  : verify_result_t :=
  let b_1914 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress_non_canonical (base_v)) in 
  let a_1915 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_ok_or (decompress_non_canonical (pk_1911)) (InvalidPublickey) in 
  let r_bytes_1916 : compressed_ed_point_t :=
    array_from_slice (default) (32) (array_to_seq (signature_1912)) (usize 0) (
      usize 32) in 
  let s_bytes_1917 : serialized_scalar_t :=
    array_from_slice (default) (32) (array_to_seq (signature_1912)) (usize 32) (
      usize 32) in 
  let 'tt :=
    if negb (check_canonical_scalar (s_bytes_1917)):bool then (let _ : unit :=
        @Err unit error_t (InvalidS) in 
      tt) else (tt) in 
  let r_1918 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_ok_or (decompress_non_canonical (r_bytes_1916)) (InvalidR) in 
  let s_1919 : scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1917)) : scalar_t in 
  let k_1920 : scalar_t :=
    scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1916) (
            pk_1911)) (msg_1913))) in 
  let sb_1921 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul_by_cofactor (point_mul (s_1919) (b_1914)) in 
  let rc_1922 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul_by_cofactor (r_1918) in 
  let ka_1923 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul_by_cofactor (point_mul (k_1920) (a_1915)) in 
  (if (point_eq (sb_1921) (point_add (rc_1922) (ka_1923))):bool then (
      @Ok unit error_t (tt)) else (@Err unit error_t (InvalidSignature))).

Definition ietf_cofactored_verify
  (pk_1924 : public_key_t)
  (signature_1925 : signature_t)
  (msg_1926 : byte_seq)
  : verify_result_t :=
  let b_1927 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let a_1928 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_ok_or (decompress (pk_1924)) (InvalidPublickey) in 
  let r_bytes_1929 : compressed_ed_point_t :=
    array_from_slice (default) (32) (array_to_seq (signature_1925)) (usize 0) (
      usize 32) in 
  let s_bytes_1930 : serialized_scalar_t :=
    array_from_slice (default) (32) (array_to_seq (signature_1925)) (usize 32) (
      usize 32) in 
  let 'tt :=
    if negb (check_canonical_scalar (s_bytes_1930)):bool then (let _ : unit :=
        @Err unit error_t (InvalidS) in 
      tt) else (tt) in 
  let r_1931 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_ok_or (decompress (r_bytes_1929)) (InvalidR) in 
  let s_1932 : scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1930)) : scalar_t in 
  let k_1933 : scalar_t :=
    scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1929) (
            pk_1924)) (msg_1926))) in 
  let sb_1934 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul_by_cofactor (point_mul (s_1932) (b_1927)) in 
  let rc_1935 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul_by_cofactor (r_1931) in 
  let ka_1936 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul_by_cofactor (point_mul (k_1933) (a_1928)) in 
  (if (point_eq (sb_1934) (point_add (rc_1935) (ka_1936))):bool then (
      @Ok unit error_t (tt)) else (@Err unit error_t (InvalidSignature))).

Definition ietf_cofactorless_verify
  (pk_1937 : public_key_t)
  (signature_1938 : signature_t)
  (msg_1939 : byte_seq)
  : verify_result_t :=
  let b_1940 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let a_1941 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_ok_or (decompress (pk_1937)) (InvalidPublickey) in 
  let r_bytes_1942 : compressed_ed_point_t :=
    array_from_slice (default) (32) (array_to_seq (signature_1938)) (usize 0) (
      usize 32) in 
  let s_bytes_1943 : serialized_scalar_t :=
    array_from_slice (default) (32) (array_to_seq (signature_1938)) (usize 32) (
      usize 32) in 
  let 'tt :=
    if negb (check_canonical_scalar (s_bytes_1943)):bool then (let _ : unit :=
        @Err unit error_t (InvalidS) in 
      tt) else (tt) in 
  let r_1944 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_ok_or (decompress (r_bytes_1942)) (InvalidR) in 
  let s_1945 : scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1943)) : scalar_t in 
  let k_1946 : scalar_t :=
    scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1942) (
            pk_1937)) (msg_1939))) in 
  let sb_1947 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul (s_1945) (b_1940) in 
  let ka_1948 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul (k_1946) (a_1941) in 
  (if (point_eq (sb_1947) (point_add (r_1944) (ka_1948))):bool then (
      @Ok unit error_t (tt)) else (@Err unit error_t (InvalidSignature))).

Definition is_identity (p_1949 : ed_point_t) : bool :=
  point_eq (p_1949) (point_identity ).

Definition alg2_verify
  (pk_1950 : public_key_t)
  (signature_1951 : signature_t)
  (msg_1952 : byte_seq)
  : verify_result_t :=
  let b_1953 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let a_1954 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_ok_or (decompress (pk_1950)) (InvalidPublickey) in 
  let 'tt :=
    if is_identity (point_mul_by_cofactor (a_1954)):bool then (let _ : unit :=
        @Err unit error_t (SmallOrderPoint) in 
      tt) else (tt) in 
  let r_bytes_1955 : compressed_ed_point_t :=
    array_from_slice (default) (32) (array_to_seq (signature_1951)) (usize 0) (
      usize 32) in 
  let s_bytes_1956 : serialized_scalar_t :=
    array_from_slice (default) (32) (array_to_seq (signature_1951)) (usize 32) (
      usize 32) in 
  let 'tt :=
    if negb (check_canonical_scalar (s_bytes_1956)):bool then (let _ : unit :=
        @Err unit error_t (InvalidS) in 
      tt) else (tt) in 
  let r_1957 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_ok_or (decompress (r_bytes_1955)) (InvalidR) in 
  let s_1958 : scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1956)) : scalar_t in 
  let k_1959 : scalar_t :=
    scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1955) (
            pk_1950)) (msg_1952))) in 
  let sb_1960 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul_by_cofactor (point_mul (s_1958) (b_1953)) in 
  let rc_1961 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul_by_cofactor (r_1957) in 
  let ka_1962 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul_by_cofactor (point_mul (k_1959) (a_1954)) in 
  (if (point_eq (sb_1960) (point_add (rc_1961) (ka_1962))):bool then (
      @Ok unit error_t (tt)) else (@Err unit error_t (InvalidSignature))).

Inductive batch_entry_t :=
| BatchEntry : (public_key_t × byte_seq × signature_t) -> batch_entry_t.

Definition zcash_batch_verify
  (entries_1963 : seq batch_entry_t)
  (entropy_1964 : byte_seq)
  : verify_result_t :=
  let 'tt :=
    if (seq_len (entropy_1964)) <.? ((usize 16) * (seq_len (
          entries_1963))):bool then (let _ : unit :=
        @Err unit error_t (NotEnoughRandomness) in 
      tt) else (tt) in 
  let s_sum_1965 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_1966 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_1967 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let '(s_sum_1965, r_sum_1966, a_sum_1967) :=
    foldi (usize 0) (seq_len (entries_1963)) (fun i_1968 '(
        s_sum_1965,
        r_sum_1966,
        a_sum_1967
      ) =>
      let 'BatchEntry ((pk_1969, msg_1970, signature_1971)) :=
        (seq_index (entries_1963) (i_1968)) in 
      let a_1972 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress_non_canonical (pk_1969)) (InvalidPublickey) in 
      let r_bytes_1973 : compressed_ed_point_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1971)) (
          usize 0) (usize 32) in 
      let s_bytes_1974 : serialized_scalar_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1971)) (
          usize 32) (usize 32) in 
      let 'tt :=
        if negb (check_canonical_scalar (s_bytes_1974)):bool then (
          let _ : unit :=
            @Err unit error_t (InvalidS) in 
          tt) else (tt) in 
      let r_1975 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress_non_canonical (r_bytes_1973)) (InvalidR) in 
      let s_1976 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1974)) : scalar_t in 
      let c_1977 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1973) (
                array_to_seq (pk_1969))) (msg_1970))) in 
      let z_1978 : seq uint8 :=
        seq_slice (entropy_1964) ((usize 16) * (i_1968)) (usize 16) in 
      let z_1979 : scalar_t :=
        nat_mod_from_byte_seq_le (seq_concat (z_1978) (seq_new_ (default) (
              usize 16))) : scalar_t in 
      let s_sum_1965 :=
        (s_sum_1965) +% ((s_1976) *% (z_1979)) in 
      let r_sum_1966 :=
        point_add (r_sum_1966) (point_mul (z_1979) (r_1975)) in 
      let a_sum_1967 :=
        point_add (a_sum_1967) (point_mul ((z_1979) *% (c_1977)) (a_1972)) in 
      (s_sum_1965, r_sum_1966, a_sum_1967))
    (s_sum_1965, r_sum_1966, a_sum_1967) in 
  let b_1980 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let sb_1981 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul (s_sum_1965) (b_1980) in 
  let check_1982 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul_by_cofactor (point_add (point_neg (sb_1981)) (point_add (
          r_sum_1966) (a_sum_1967))) in 
  (if (is_identity (check_1982)):bool then (@Ok unit error_t (tt)) else (
      @Err unit error_t (InvalidSignature))).

Definition ietf_cofactored_batch_verify
  (entries_1983 : seq batch_entry_t)
  (entropy_1984 : byte_seq)
  : verify_result_t :=
  let 'tt :=
    if (seq_len (entropy_1984)) <.? ((usize 16) * (seq_len (
          entries_1983))):bool then (let _ : unit :=
        @Err unit error_t (NotEnoughRandomness) in 
      tt) else (tt) in 
  let s_sum_1985 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_1986 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_1987 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let '(s_sum_1985, r_sum_1986, a_sum_1987) :=
    foldi (usize 0) (seq_len (entries_1983)) (fun i_1988 '(
        s_sum_1985,
        r_sum_1986,
        a_sum_1987
      ) =>
      let 'BatchEntry ((pk_1989, msg_1990, signature_1991)) :=
        (seq_index (entries_1983) (i_1988)) in 
      let a_1992 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (pk_1989)) (InvalidPublickey) in 
      let r_bytes_1993 : compressed_ed_point_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1991)) (
          usize 0) (usize 32) in 
      let s_bytes_1994 : serialized_scalar_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1991)) (
          usize 32) (usize 32) in 
      let 'tt :=
        if negb (check_canonical_scalar (s_bytes_1994)):bool then (
          let _ : unit :=
            @Err unit error_t (InvalidS) in 
          tt) else (tt) in 
      let r_1995 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (r_bytes_1993)) (InvalidR) in 
      let s_1996 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1994)) : scalar_t in 
      let c_1997 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1993) (
                array_to_seq (pk_1989))) (msg_1990))) in 
      let z_1998 : seq uint8 :=
        seq_slice (entropy_1984) ((usize 16) * (i_1988)) (usize 16) in 
      let z_1999 : scalar_t :=
        nat_mod_from_byte_seq_le (seq_concat (z_1998) (seq_new_ (default) (
              usize 16))) : scalar_t in 
      let s_sum_1985 :=
        (s_sum_1985) +% ((s_1996) *% (z_1999)) in 
      let r_sum_1986 :=
        point_add (r_sum_1986) (point_mul (z_1999) (r_1995)) in 
      let a_sum_1987 :=
        point_add (a_sum_1987) (point_mul ((z_1999) *% (c_1997)) (a_1992)) in 
      (s_sum_1985, r_sum_1986, a_sum_1987))
    (s_sum_1985, r_sum_1986, a_sum_1987) in 
  let b_2000 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let sb_2001 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul (s_sum_1985) (b_2000) in 
  let check_2002 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul_by_cofactor (point_add (point_neg (sb_2001)) (point_add (
          r_sum_1986) (a_sum_1987))) in 
  (if (is_identity (check_2002)):bool then (@Ok unit error_t (tt)) else (
      @Err unit error_t (InvalidSignature))).

Definition ietf_cofactorless_batch_verify
  (entries_2003 : seq batch_entry_t)
  (entropy_2004 : byte_seq)
  : verify_result_t :=
  let 'tt :=
    if (seq_len (entropy_2004)) <.? ((usize 16) * (seq_len (
          entries_2003))):bool then (let _ : unit :=
        @Err unit error_t (NotEnoughRandomness) in 
      tt) else (tt) in 
  let s_sum_2005 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_2006 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_2007 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let '(s_sum_2005, r_sum_2006, a_sum_2007) :=
    foldi (usize 0) (seq_len (entries_2003)) (fun i_2008 '(
        s_sum_2005,
        r_sum_2006,
        a_sum_2007
      ) =>
      let 'BatchEntry ((pk_2009, msg_2010, signature_2011)) :=
        (seq_index (entries_2003) (i_2008)) in 
      let a_2012 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (pk_2009)) (InvalidPublickey) in 
      let r_bytes_2013 : compressed_ed_point_t :=
        array_from_slice (default) (32) (array_to_seq (signature_2011)) (
          usize 0) (usize 32) in 
      let s_bytes_2014 : serialized_scalar_t :=
        array_from_slice (default) (32) (array_to_seq (signature_2011)) (
          usize 32) (usize 32) in 
      let 'tt :=
        if negb (check_canonical_scalar (s_bytes_2014)):bool then (
          let _ : unit :=
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
      let c_2017 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_2013) (
                array_to_seq (pk_2009))) (msg_2010))) in 
      let z_2018 : seq uint8 :=
        seq_slice (entropy_2004) ((usize 16) * (i_2008)) (usize 16) in 
      let z_2019 : scalar_t :=
        nat_mod_from_byte_seq_le (seq_concat (z_2018) (seq_new_ (default) (
              usize 16))) : scalar_t in 
      let s_sum_2005 :=
        (s_sum_2005) +% ((s_2016) *% (z_2019)) in 
      let r_sum_2006 :=
        point_add (r_sum_2006) (point_mul (z_2019) (r_2015)) in 
      let a_sum_2007 :=
        point_add (a_sum_2007) (point_mul ((z_2019) *% (c_2017)) (a_2012)) in 
      (s_sum_2005, r_sum_2006, a_sum_2007))
    (s_sum_2005, r_sum_2006, a_sum_2007) in 
  let b_2020 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let sb_2021 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul (s_sum_2005) (b_2020) in 
  let check_2022 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_add (point_neg (sb_2021)) (point_add (r_sum_2006) (a_sum_2007)) in 
  (if (is_identity (check_2022)):bool then (@Ok unit error_t (tt)) else (
      @Err unit error_t (InvalidSignature))).

Definition alg3_batch_verify
  (entries_2023 : seq batch_entry_t)
  (entropy_2024 : byte_seq)
  : verify_result_t :=
  let 'tt :=
    if (seq_len (entropy_2024)) <.? ((usize 16) * (seq_len (
          entries_2023))):bool then (let _ : unit :=
        @Err unit error_t (NotEnoughRandomness) in 
      tt) else (tt) in 
  let s_sum_2025 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_2026 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_2027 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let '(s_sum_2025, r_sum_2026, a_sum_2027) :=
    foldi (usize 0) (seq_len (entries_2023)) (fun i_2028 '(
        s_sum_2025,
        r_sum_2026,
        a_sum_2027
      ) =>
      let 'BatchEntry ((pk_2029, msg_2030, signature_2031)) :=
        (seq_index (entries_2023) (i_2028)) in 
      let a_2032 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (pk_2029)) (InvalidPublickey) in 
      let 'tt :=
        if is_identity (point_mul_by_cofactor (a_2032)):bool then (
          let _ : unit :=
            @Err unit error_t (SmallOrderPoint) in 
          tt) else (tt) in 
      let r_bytes_2033 : compressed_ed_point_t :=
        array_from_slice (default) (32) (array_to_seq (signature_2031)) (
          usize 0) (usize 32) in 
      let s_bytes_2034 : serialized_scalar_t :=
        array_from_slice (default) (32) (array_to_seq (signature_2031)) (
          usize 32) (usize 32) in 
      let 'tt :=
        if negb (check_canonical_scalar (s_bytes_2034)):bool then (
          let _ : unit :=
            @Err unit error_t (InvalidS) in 
          tt) else (tt) in 
      let r_2035 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        option_ok_or (decompress (r_bytes_2033)) (InvalidR) in 
      let s_2036 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_2034)) : scalar_t in 
      let c_2037 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_2033) (
                array_to_seq (pk_2029))) (msg_2030))) in 
      let z_2038 : seq uint8 :=
        seq_slice (entropy_2024) ((usize 16) * (i_2028)) (usize 16) in 
      let z_2039 : scalar_t :=
        nat_mod_from_byte_seq_le (seq_concat (z_2038) (seq_new_ (default) (
              usize 16))) : scalar_t in 
      let s_sum_2025 :=
        (s_sum_2025) +% ((s_2036) *% (z_2039)) in 
      let r_sum_2026 :=
        point_add (r_sum_2026) (point_mul (z_2039) (r_2035)) in 
      let a_sum_2027 :=
        point_add (a_sum_2027) (point_mul ((z_2039) *% (c_2037)) (a_2032)) in 
      (s_sum_2025, r_sum_2026, a_sum_2027))
    (s_sum_2025, r_sum_2026, a_sum_2027) in 
  let b_2040 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let sb_2041 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul (s_sum_2025) (b_2040) in 
  let check_2042 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul_by_cofactor (point_add (point_neg (sb_2041)) (point_add (
          r_sum_2026) (a_sum_2027))) in 
  (if (is_identity (check_2042)):bool then (@Ok unit error_t (tt)) else (
      @Err unit error_t (InvalidSignature))).

