module Hacspec.Poly1305

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open Hacspec.Lib
open FStar.Mul

type key_poly = lseq (uint8) (usize 32)

let blocksize : uint_size =
  usize 16

type block = lseq (uint8) (blocksize)

type field_canvas_block = lseq (uint8) (usize 17)

let field_canvas_block_idx =
  nat_mod (usize 17)

type tag = lseq (pub_uint8) (blocksize)

type field_canvas = lseq (pub_uint8) (usize 131)

type field_element = nat_mod 0x03fffffffffffffffffffffffffffffffb

let le_bytes_to_num (b_1872 : byte_seq) : uint128 =
  let block_as_u128_1873 =
    array_from_slice (b_1872) (usize 0) (min (blocksize) (seq_len (b_1872)))
  in
  uint128_from_le_bytes (block_as_u128_1873)

let clamp (r_1874 : uint128) : field_element =
  let r_uint_1875 =
    (r_1874) &. (secret (pub_u128 0xffffffc0ffffffc0ffffffc0fffffff))
  in
  nat_from_secret_literal (0x03fffffffffffffffffffffffffffffffb) (r_uint_1875)

let encode
  (block_uint_1876 : uint128)
  (len_1877 : field_canvas_block_idx)
  : field_element =
  let w_elem_1878 =
    nat_from_secret_literal (0x03fffffffffffffffffffffffffffffffb) (
      block_uint_1876)
  in
  (**) assert_norm (pow2 128 < 0x03fffffffffffffffffffffffffffffffb);
  (**) Math.Lemmas.pow2_le_compat 128 (8 * len_1877);
  let l_elem_1879 =
    nat_pow2 (0x03fffffffffffffffffffffffffffffffb) ((usize 8) * (len_1877))
  in
  (w_elem_1878) +% (l_elem_1879)

let num_to_16_le_bytes (a_1880 : field_element) : tag =
  let n_v_1881 =
    nat_to_public_byte_seq_le (0x03fffffffffffffffffffffffffffffffb) (17) (
      a_1880)
  in
  array_from_seq (blocksize) (seq_slice (n_v_1881) (usize 0) (blocksize))

let poly (m_1882 : byte_seq) (key_1883 : key_poly) : tag =
  let r_1884 = le_bytes_to_num (array_slice (key_1883) (usize 0) (blocksize)) in
  let r_1885 = clamp (r_1884) in
  let s_1886 =
    le_bytes_to_num (array_slice (key_1883) (blocksize) (blocksize))
  in
  let s_1887 =
    nat_from_secret_literal (0x03fffffffffffffffffffffffffffffffb) (s_1886)
  in
  let a_1888 =
    nat_from_literal (0x03fffffffffffffffffffffffffffffffb) (pub_u128 0x0)
  in
  let (a_1888) =
    foldi (usize 0) (seq_num_chunks (m_1882) (blocksize)) (fun i_1889 (a_1888
      ) ->
      let (len_1890, block_1891) =
        seq_get_chunk (m_1882) (blocksize) (i_1889)
      in
      let block_uint_1892 = le_bytes_to_num (block_1891) in
      let n_1893 = encode (block_uint_1892) (len_1890) in
      let a_1888 = (a_1888) +% (n_1893) in
      let a_1888 = (r_1885) *% (a_1888) in
      (a_1888))
    (a_1888)
  in
  let a_1894 = (a_1888) +% (s_1887) in
  num_to_16_le_bytes (a_1894)
