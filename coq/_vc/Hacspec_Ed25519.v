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

Definition scalar_from_hash (h_2081 : sha512_digest_t)  : scalar_t :=
  let s_2082 : big_scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (h_2081)) : big_scalar_t in 
  nat_mod_from_byte_seq_le (seq_slice (nat_mod_to_byte_seq_le (s_2082)) (
      usize 0) (usize 32)) : scalar_t.

Definition sign (sk_2083 : secret_key_t) (msg_2084 : byte_seq)  : signature_t :=
  let '(a_2085, prefix_2086) :=
    secret_expand (sk_2083) in 
  let a_2087 : scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (a_2085)) : scalar_t in 
  let b_2088 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let a_p_2089 : compressed_ed_point_t :=
    compress (point_mul (a_2087) (b_2088)) in 
  let r_2090 : scalar_t :=
    scalar_from_hash (sha512 (array_concat (prefix_2086) (msg_2084))) in 
  let r_p_2091 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_mul (r_2090) (b_2088) in 
  let r_s_2092 : compressed_ed_point_t :=
    compress (r_p_2091) in 
  let h_2093 : scalar_t :=
    scalar_from_hash (sha512 (seq_concat (array_concat (r_s_2092) (
            array_to_seq (a_p_2089))) (msg_2084))) in 
  let s_2094 : scalar_t :=
    (r_2090) +% ((h_2093) *% (a_2087)) in 
  let s_bytes_2095 : seq uint8 :=
    seq_slice (nat_mod_to_byte_seq_le (s_2094)) (usize 0) (usize 32) in 
  array_update (array_update (array_new_ (default : uint8) (64)) (usize 0) (
      array_to_seq (r_s_2092))) (usize 32) (s_bytes_2095).

Definition zcash_verify
  (pk_2096 : public_key_t)
  (signature_2097 : signature_t)
  (msg_2098 : byte_seq)
  
  : verify_result_t :=
  let b_2099 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress_non_canonical (base_v)) in 
  bind (option_ok_or (decompress_non_canonical (pk_2096)) (InvalidPublickey)) (
    fun a_2100 => let r_bytes_2101 : compressed_ed_point_t :=
      array_from_slice (default : uint8) (32) (array_to_seq (signature_2097)) (
        usize 0) (usize 32) in 
    let s_bytes_2102 : serialized_scalar_t :=
      array_from_slice (default : uint8) (32) (array_to_seq (signature_2097)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_2102)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => @Ok unit error_t (
          tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress_non_canonical (r_bytes_2101)) (InvalidR)) (
      fun r_2103 => let s_2104 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_2102)) : scalar_t in 
      let k_2105 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_2101) (
                pk_2096)) (msg_2098))) in 
      let sb_2106 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (s_2104) (b_2099)) in 
      let rc_2107 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (r_2103) in 
      let ka_2108 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (k_2105) (a_2100)) in 
      (if (point_eq (sb_2106) (point_add (rc_2107) (ka_2108))):bool then (
          @Ok unit error_t (tt)) else (@Err unit error_t (
            InvalidSignature)))))).

Definition ietf_cofactored_verify
  (pk_2109 : public_key_t)
  (signature_2110 : signature_t)
  (msg_2111 : byte_seq)
  
  : verify_result_t :=
  let b_2112 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  bind (option_ok_or (decompress (pk_2109)) (InvalidPublickey)) (fun a_2113 =>
    let r_bytes_2114 : compressed_ed_point_t :=
      array_from_slice (default : uint8) (32) (array_to_seq (signature_2110)) (
        usize 0) (usize 32) in 
    let s_bytes_2115 : serialized_scalar_t :=
      array_from_slice (default : uint8) (32) (array_to_seq (signature_2110)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_2115)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => @Ok unit error_t (
          tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress (r_bytes_2114)) (InvalidR)) (fun r_2116 =>
      let s_2117 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_2115)) : scalar_t in 
      let k_2118 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_2114) (
                pk_2109)) (msg_2111))) in 
      let sb_2119 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (s_2117) (b_2112)) in 
      let rc_2120 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (r_2116) in 
      let ka_2121 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (k_2118) (a_2113)) in 
      (if (point_eq (sb_2119) (point_add (rc_2120) (ka_2121))):bool then (
          @Ok unit error_t (tt)) else (@Err unit error_t (
            InvalidSignature)))))).

Definition ietf_cofactorless_verify
  (pk_2122 : public_key_t)
  (signature_2123 : signature_t)
  (msg_2124 : byte_seq)
  
  : verify_result_t :=
  let b_2125 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  bind (option_ok_or (decompress (pk_2122)) (InvalidPublickey)) (fun a_2126 =>
    let r_bytes_2127 : compressed_ed_point_t :=
      array_from_slice (default : uint8) (32) (array_to_seq (signature_2123)) (
        usize 0) (usize 32) in 
    let s_bytes_2128 : serialized_scalar_t :=
      array_from_slice (default : uint8) (32) (array_to_seq (signature_2123)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_2128)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => @Ok unit error_t (
          tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress (r_bytes_2127)) (InvalidR)) (fun r_2129 =>
      let s_2130 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_2128)) : scalar_t in 
      let k_2131 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_2127) (
                pk_2122)) (msg_2124))) in 
      let sb_2132 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (s_2130) (b_2125) in 
      let ka_2133 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (k_2131) (a_2126) in 
      (if (point_eq (sb_2132) (point_add (r_2129) (ka_2133))):bool then (
          @Ok unit error_t (tt)) else (@Err unit error_t (
            InvalidSignature)))))).

Definition is_identity (p_2134 : ed_point_t)  : bool :=
  point_eq (p_2134) (point_identity ).

Definition alg2_verify
  (pk_2135 : public_key_t)
  (signature_2136 : signature_t)
  (msg_2137 : byte_seq)
  
  : verify_result_t :=
  let b_2138 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  bind (option_ok_or (decompress (pk_2135)) (InvalidPublickey)) (fun a_2139 =>
    ifbnd is_identity (point_mul_by_cofactor (a_2139)) : bool
    thenbnd (bind (@Err unit error_t (SmallOrderPoint)) (fun _ =>
        @Ok unit error_t (tt)))
    else (tt) >> (fun 'tt =>
    let r_bytes_2140 : compressed_ed_point_t :=
      array_from_slice (default : uint8) (32) (array_to_seq (signature_2136)) (
        usize 0) (usize 32) in 
    let s_bytes_2141 : serialized_scalar_t :=
      array_from_slice (default : uint8) (32) (array_to_seq (signature_2136)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_2141)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => @Ok unit error_t (
          tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress (r_bytes_2140)) (InvalidR)) (fun r_2142 =>
      let s_2143 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_2141)) : scalar_t in 
      let k_2144 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_2140) (
                pk_2135)) (msg_2137))) in 
      let sb_2145 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (s_2143) (b_2138)) in 
      let rc_2146 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (r_2142) in 
      let ka_2147 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (k_2144) (a_2139)) in 
      (if (point_eq (sb_2145) (point_add (rc_2146) (ka_2147))):bool then (
          @Ok unit error_t (tt)) else (@Err unit error_t (
            InvalidSignature))))))).

Inductive batch_entry_t :=
| BatchEntry : (public_key_t '× byte_seq '× signature_t) -> batch_entry_t.

Definition zcash_batch_verify
  (entries_2148 : seq batch_entry_t)
  (entropy_2149 : byte_seq)
  
  : verify_result_t :=
  ifbnd (seq_len (entropy_2149)) <.? ((usize 16) * (seq_len (
        entries_2148))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ =>
      @Ok unit error_t (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_2150 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_2151 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_2152 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  bind (foldibnd (usize 0) to (seq_len (entries_2148)) for (
      s_sum_2150,
      r_sum_2151,
      a_sum_2152
    ) >> (fun i_2153 '(s_sum_2150, r_sum_2151, a_sum_2152) =>
    let 'BatchEntry ((pk_2154, msg_2155, signature_2156)) :=
      (seq_index (entries_2148) (i_2153)) in 
    bind (option_ok_or (decompress_non_canonical (pk_2154)) (
        InvalidPublickey)) (fun a_2157 =>
      let r_bytes_2158 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_2156)) (usize 0) (usize 32) in 
      let s_bytes_2159 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_2156)) (usize 32) (usize 32) in 
      ifbnd negb (check_canonical_scalar (s_bytes_2159)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => @Ok unit error_t (
            tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress_non_canonical (r_bytes_2158)) (InvalidR)) (
        fun r_2160 => let s_2161 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_2159)) : scalar_t in 
        let c_2162 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_2158) (
                  array_to_seq (pk_2154))) (msg_2155))) in 
        let z_2163 : seq uint8 :=
          seq_slice (entropy_2149) ((usize 16) * (i_2153)) (usize 16) in 
        let z_2164 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_2163) (seq_new_ (
                default : uint8) (usize 16))) : scalar_t in 
        let s_sum_2150 :=
          (s_sum_2150) +% ((s_2161) *% (z_2164)) in 
        let r_sum_2151 :=
          point_add (r_sum_2151) (point_mul (z_2164) (r_2160)) in 
        let a_sum_2152 :=
          point_add (a_sum_2152) (point_mul ((z_2164) *% (c_2162)) (a_2157)) in 
        @Ok (
          scalar_t '×
          (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) '×
          (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          )
        ) error_t ((s_sum_2150, r_sum_2151, a_sum_2152))))))) (fun '(
      s_sum_2150,
      r_sum_2151,
      a_sum_2152
    ) => let b_2165 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      option_unwrap (decompress (base_v)) in 
    let sb_2166 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul (s_sum_2150) (b_2165) in 
    let check_2167 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul_by_cofactor (point_add (point_neg (sb_2166)) (point_add (
            r_sum_2151) (a_sum_2152))) in 
    (if (is_identity (check_2167)):bool then (@Ok unit error_t (tt)) else (
        @Err unit error_t (InvalidSignature))))).

Definition ietf_cofactored_batch_verify
  (entries_2168 : seq batch_entry_t)
  (entropy_2169 : byte_seq)
  
  : verify_result_t :=
  ifbnd (seq_len (entropy_2169)) <.? ((usize 16) * (seq_len (
        entries_2168))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ =>
      @Ok unit error_t (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_2170 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_2171 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_2172 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  bind (foldibnd (usize 0) to (seq_len (entries_2168)) for (
      s_sum_2170,
      r_sum_2171,
      a_sum_2172
    ) >> (fun i_2173 '(s_sum_2170, r_sum_2171, a_sum_2172) =>
    let 'BatchEntry ((pk_2174, msg_2175, signature_2176)) :=
      (seq_index (entries_2168) (i_2173)) in 
    bind (option_ok_or (decompress (pk_2174)) (InvalidPublickey)) (fun a_2177 =>
      let r_bytes_2178 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_2176)) (usize 0) (usize 32) in 
      let s_bytes_2179 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_2176)) (usize 32) (usize 32) in 
      ifbnd negb (check_canonical_scalar (s_bytes_2179)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => @Ok unit error_t (
            tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress (r_bytes_2178)) (InvalidR)) (fun r_2180 =>
        let s_2181 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_2179)) : scalar_t in 
        let c_2182 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_2178) (
                  array_to_seq (pk_2174))) (msg_2175))) in 
        let z_2183 : seq uint8 :=
          seq_slice (entropy_2169) ((usize 16) * (i_2173)) (usize 16) in 
        let z_2184 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_2183) (seq_new_ (
                default : uint8) (usize 16))) : scalar_t in 
        let s_sum_2170 :=
          (s_sum_2170) +% ((s_2181) *% (z_2184)) in 
        let r_sum_2171 :=
          point_add (r_sum_2171) (point_mul (z_2184) (r_2180)) in 
        let a_sum_2172 :=
          point_add (a_sum_2172) (point_mul ((z_2184) *% (c_2182)) (a_2177)) in 
        @Ok (
          scalar_t '×
          (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) '×
          (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          )
        ) error_t ((s_sum_2170, r_sum_2171, a_sum_2172))))))) (fun '(
      s_sum_2170,
      r_sum_2171,
      a_sum_2172
    ) => let b_2185 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      option_unwrap (decompress (base_v)) in 
    let sb_2186 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul (s_sum_2170) (b_2185) in 
    let check_2187 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul_by_cofactor (point_add (point_neg (sb_2186)) (point_add (
            r_sum_2171) (a_sum_2172))) in 
    (if (is_identity (check_2187)):bool then (@Ok unit error_t (tt)) else (
        @Err unit error_t (InvalidSignature))))).

Definition ietf_cofactorless_batch_verify
  (entries_2188 : seq batch_entry_t)
  (entropy_2189 : byte_seq)
  
  : verify_result_t :=
  ifbnd (seq_len (entropy_2189)) <.? ((usize 16) * (seq_len (
        entries_2188))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ =>
      @Ok unit error_t (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_2190 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_2191 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_2192 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  bind (foldibnd (usize 0) to (seq_len (entries_2188)) for (
      s_sum_2190,
      r_sum_2191,
      a_sum_2192
    ) >> (fun i_2193 '(s_sum_2190, r_sum_2191, a_sum_2192) =>
    let 'BatchEntry ((pk_2194, msg_2195, signature_2196)) :=
      (seq_index (entries_2188) (i_2193)) in 
    bind (option_ok_or (decompress (pk_2194)) (InvalidPublickey)) (fun a_2197 =>
      let r_bytes_2198 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_2196)) (usize 0) (usize 32) in 
      let s_bytes_2199 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_2196)) (usize 32) (usize 32) in 
      ifbnd negb (check_canonical_scalar (s_bytes_2199)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => @Ok unit error_t (
            tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress (r_bytes_2198)) (InvalidR)) (fun r_2200 =>
        let s_2201 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_2199)) : scalar_t in 
        let c_2202 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_2198) (
                  array_to_seq (pk_2194))) (msg_2195))) in 
        let z_2203 : seq uint8 :=
          seq_slice (entropy_2189) ((usize 16) * (i_2193)) (usize 16) in 
        let z_2204 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_2203) (seq_new_ (
                default : uint8) (usize 16))) : scalar_t in 
        let s_sum_2190 :=
          (s_sum_2190) +% ((s_2201) *% (z_2204)) in 
        let r_sum_2191 :=
          point_add (r_sum_2191) (point_mul (z_2204) (r_2200)) in 
        let a_sum_2192 :=
          point_add (a_sum_2192) (point_mul ((z_2204) *% (c_2202)) (a_2197)) in 
        @Ok (
          scalar_t '×
          (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) '×
          (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          )
        ) error_t ((s_sum_2190, r_sum_2191, a_sum_2192))))))) (fun '(
      s_sum_2190,
      r_sum_2191,
      a_sum_2192
    ) => let b_2205 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      option_unwrap (decompress (base_v)) in 
    let sb_2206 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul (s_sum_2190) (b_2205) in 
    let check_2207 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_add (point_neg (sb_2206)) (point_add (r_sum_2191) (a_sum_2192)) in 
    (if (is_identity (check_2207)):bool then (@Ok unit error_t (tt)) else (
        @Err unit error_t (InvalidSignature))))).

Definition alg3_batch_verify
  (entries_2208 : seq batch_entry_t)
  (entropy_2209 : byte_seq)
  
  : verify_result_t :=
  ifbnd (seq_len (entropy_2209)) <.? ((usize 16) * (seq_len (
        entries_2208))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ =>
      @Ok unit error_t (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_2210 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_2211 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_2212 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  bind (foldibnd (usize 0) to (seq_len (entries_2208)) for (
      s_sum_2210,
      r_sum_2211,
      a_sum_2212
    ) >> (fun i_2213 '(s_sum_2210, r_sum_2211, a_sum_2212) =>
    let 'BatchEntry ((pk_2214, msg_2215, signature_2216)) :=
      (seq_index (entries_2208) (i_2213)) in 
    bind (option_ok_or (decompress (pk_2214)) (InvalidPublickey)) (fun a_2217 =>
      ifbnd is_identity (point_mul_by_cofactor (a_2217)) : bool
      thenbnd (bind (@Err unit error_t (SmallOrderPoint)) (fun _ =>
          @Ok unit error_t (tt)))
      else (tt) >> (fun 'tt =>
      let r_bytes_2218 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_2216)) (usize 0) (usize 32) in 
      let s_bytes_2219 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_2216)) (usize 32) (usize 32) in 
      ifbnd negb (check_canonical_scalar (s_bytes_2219)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => @Ok unit error_t (
            tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress (r_bytes_2218)) (InvalidR)) (fun r_2220 =>
        let s_2221 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_2219)) : scalar_t in 
        let c_2222 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_2218) (
                  array_to_seq (pk_2214))) (msg_2215))) in 
        let z_2223 : seq uint8 :=
          seq_slice (entropy_2209) ((usize 16) * (i_2213)) (usize 16) in 
        let z_2224 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_2223) (seq_new_ (
                default : uint8) (usize 16))) : scalar_t in 
        let s_sum_2210 :=
          (s_sum_2210) +% ((s_2221) *% (z_2224)) in 
        let r_sum_2211 :=
          point_add (r_sum_2211) (point_mul (z_2224) (r_2220)) in 
        let a_sum_2212 :=
          point_add (a_sum_2212) (point_mul ((z_2224) *% (c_2222)) (a_2217)) in 
        @Ok (
          scalar_t '×
          (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) '×
          (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          )
        ) error_t ((s_sum_2210, r_sum_2211, a_sum_2212)))))))) (fun '(
      s_sum_2210,
      r_sum_2211,
      a_sum_2212
    ) => let b_2225 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      option_unwrap (decompress (base_v)) in 
    let sb_2226 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul (s_sum_2210) (b_2225) in 
    let check_2227 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul_by_cofactor (point_add (point_neg (sb_2226)) (point_add (
            r_sum_2211) (a_sum_2212))) in 
    (if (is_identity (check_2227)):bool then (@Ok unit error_t (tt)) else (
        @Err unit error_t (InvalidSignature))))).

