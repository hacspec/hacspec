module Hacspec.Poly1305

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open Hacspec.Lib
open FStar.Mul

type key_poly = lseq (uint8) (usize 32)

let blocksize : uint_size =
  usize 16

type block = lseq (uint8) (blocksize)

type tag = lseq (pub_uint8) (blocksize)

type field_canvas = lseq (pub_uint8) (17)

type field_element = nat_mod 0x03fffffffffffffffffffffffffffffffb

let le_bytes_to_num (b_1865 : byte_seq) : uint128 =
  let block_as_u128_1866 =
    array_from_slice (secret (pub_u8 0x8)) (16) (b_1865) (usize 0) (
      min (blocksize) (seq_len (b_1865)))
  in
  uint128_from_le_bytes (block_as_u128_1866)

let clamp (r_1867 : uint128) : field_element =
  let r_uint_1868 =
    (r_1867) &. (secret (pub_u128 0xffffffc0ffffffc0ffffffc0fffffff))
  in
  nat_from_secret_literal (0x03fffffffffffffffffffffffffffffffb) (r_uint_1868)

let encode (block_uint_1869 : uint128) (len_1870 : uint_size{
  (**) len_1870 < 17
  }) : field_element =
  let w_elem_1871 =
    nat_from_secret_literal (0x03fffffffffffffffffffffffffffffffb) (
      block_uint_1869)
  in
  (**) assert_norm (pow2 128 < 0x03fffffffffffffffffffffffffffffffb);
  (**) Math.Lemmas.pow2_le_compat 128 (8 * len_1870);
  let l_elem_1872 =
    nat_pow2 (0x03fffffffffffffffffffffffffffffffb) ((usize 8) * (len_1870))
  in
  (w_elem_1871) +% (l_elem_1872)

let num_to_16_le_bytes (a_1873 : field_element) : tag =
  let n_v_1874 =
    nat_to_public_byte_seq_le (0x03fffffffffffffffffffffffffffffffb) (17) (
      a_1873)
  in
  array_from_seq (blocksize) (seq_slice (n_v_1874) (usize 0) (blocksize))

let poly (m_1875 : byte_seq) (key_1876 : key_poly) : tag =
  let r_1877 = le_bytes_to_num (array_slice (key_1876) (usize 0) (blocksize)) in
  let r_1878 = clamp (r_1877) in
  let s_1879 =
    le_bytes_to_num (array_slice (key_1876) (blocksize) (blocksize))
  in
  let s_1880 =
    nat_from_secret_literal (0x03fffffffffffffffffffffffffffffffb) (s_1879)
  in
  let a_1881 =
    nat_from_literal (0x03fffffffffffffffffffffffffffffffb) (pub_u128 0x0)
  in
  let (a_1881) =
    foldi (usize 0) (seq_num_chunks (m_1875) (blocksize)) (fun i_1882 (a_1881
      ) ->
      let (len_1883, block_1884) =
        seq_get_chunk (m_1875) (blocksize) (i_1882)
      in
      let block_uint_1885 = le_bytes_to_num (block_1884) in
      let n_1886 = encode (block_uint_1885) (len_1883) in
      let a_1881 = (a_1881) +% (n_1886) in
      let a_1881 = (r_1878) *% (a_1881) in
      (a_1881))
    (a_1881)
  in
  let a_1887 = (a_1881) +% (s_1880) in
  num_to_16_le_bytes (a_1887)
