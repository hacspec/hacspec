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

let le_bytes_to_num (b_1868 : byte_seq) : uint128 =
  let block_as_u128_1869 =
    array_from_slice (b_1868) (usize 0) (min (blocksize) (seq_len (b_1868)))
  in
  uint128_from_le_bytes (block_as_u128_1869)

let clamp (r_1870 : uint128) : field_element =
  let r_uint_1871 =
    (r_1870) &. (secret (pub_u128 0xffffffc0ffffffc0ffffffc0fffffff))
  in
  nat_from_secret_literal (0x03fffffffffffffffffffffffffffffffb) (r_uint_1871)

let encode (block_uint_1872 : uint128) (len_1873 : uint_size{
  (**) len_1873 < 17
  }) : field_element =
  let w_elem_1874 =
    nat_from_secret_literal (0x03fffffffffffffffffffffffffffffffb) (
      block_uint_1872)
  in
  (**) assert_norm (pow2 128 < 0x03fffffffffffffffffffffffffffffffb);
  (**) Math.Lemmas.pow2_le_compat 128 (8 * len_1873);
  let l_elem_1875 =
    nat_pow2 (0x03fffffffffffffffffffffffffffffffb) ((usize 8) * (len_1873))
  in
  (w_elem_1874) +% (l_elem_1875)

let num_to_16_le_bytes (a_1876 : field_element) : tag =
  let n_v_1877 =
    nat_to_public_byte_seq_le (0x03fffffffffffffffffffffffffffffffb) (17) (
      a_1876)
  in
  array_from_seq (blocksize) (seq_slice (n_v_1877) (usize 0) (blocksize))

let poly (m_1878 : byte_seq) (key_1879 : key_poly) : tag =
  let r_1880 = le_bytes_to_num (array_slice (key_1879) (usize 0) (blocksize)) in
  let r_1881 = clamp (r_1880) in
  let s_1882 =
    le_bytes_to_num (array_slice (key_1879) (blocksize) (blocksize))
  in
  let s_1883 =
    nat_from_secret_literal (0x03fffffffffffffffffffffffffffffffb) (s_1882)
  in
  let a_1884 =
    nat_from_literal (0x03fffffffffffffffffffffffffffffffb) (pub_u128 0x0)
  in
  let (a_1884) =
    foldi (usize 0) (seq_num_chunks (m_1878) (blocksize)) (fun i_1885 (a_1884
      ) ->
      let (len_1886, block_1887) =
        seq_get_chunk (m_1878) (blocksize) (i_1885)
      in
      let block_uint_1888 = le_bytes_to_num (block_1887) in
      let n_1889 = encode (block_uint_1888) (len_1886) in
      let a_1884 = (a_1884) +% (n_1889) in
      let a_1884 = (r_1881) *% (a_1884) in
      (a_1884))
    (a_1884)
  in
  let a_1890 = (a_1884) +% (s_1883) in
  num_to_16_le_bytes (a_1890)
