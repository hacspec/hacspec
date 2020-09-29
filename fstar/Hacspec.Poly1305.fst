module Hacspec.Poly1305

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open Hacspec.Lib
open FStar.Mul

type key_poly = lseq (uint8) (usize 32)

let blocksize : uint_size =
  usize 16

type block = lseq (uint8) (blocksize)

type tag = lseq (pub_uint8) (blocksize)

type field_canvas = lseq (pub_uint8) (usize 272)

type field_element = nat_mod 0x03fffffffffffffffffffffffffffffffb

let encode_r (r_1865 : block) : field_element =
  let r_128_1866 = seq_from_slice 16 (r_1865) (usize 0) (blocksize) in
  let r_uint_1867 = uint128_from_le_bytes (r_128_1866) in
  let r_uint_1868 =
    (r_uint_1867) &. (secret (pub_u128 0xffffffc0ffffffc0ffffffc0fffffff))
  in
  nat_from_secret_literal (r_uint_1868)

let encode (block_1869 : byte_seq) : field_element =
  let block_len_1870 = seq_len (block_1869) in
  let block_as_u128_1871 =
    seq_from_slice 16 (block_1869) (usize 0) (min (usize 16) (block_len_1870))
  in
  let w_elem_1872 =
    nat_from_secret_literal (uint128_from_le_bytes (block_as_u128_1871))
  in
  let l_elem_1873 = nat_pow2 ((usize 8) * (block_len_1870)) in
  (w_elem_1872) + (l_elem_1873)

let poly_inner (m_1874 : byte_seq) (r_1875 : field_element) : field_element =
  let acc_1876 = nat_from_literal (pub_u128 0x0) in
  let (acc_1876) =
    foldi (usize 0) (seq_num_chunks (m_1874) (blocksize)) (fun (
        i_1877,
        (acc_1876)
      ) ->
      let (_, block_1878) = seq_get_chunk (m_1874) (blocksize) (i_1877) in
      let acc_1876 = ((acc_1876) + (encode (block_1878))) * (r_1875) in
      (acc_1876))
    (acc_1876)
  in
  acc_1876

let poly (m_1879 : byte_seq) (key_1880 : key_poly) : tag =
  let s_elem_1881 =
    nat_from_secret_literal (
      uint128_from_le_bytes (
        seq_from_slice 16 (key_1880) (blocksize) (blocksize)))
  in
  let r_elem_1882 =
    encode_r (seq_from_slice_range blocksize (key_1880) ((usize 0, blocksize)))
  in
  let a_1883 = poly_inner (m_1879) (r_elem_1882) in
  let n_1884 = (a_1883) + (s_elem_1881) in
  let n_v_1885 = nat_to_public_byte_seq_le (n_1884) in
  let tag_1886 = seq_new_ blocksize (pub_u8 0x0) in
  let (tag_1886) =
    foldi (usize 0) (
        min (seq_len (tag_1886)) (seq_len #pub_uint8 (n_v_1885))) (fun (
        i_1887,
        (tag_1886)
      ) ->
      let tag_1886 =
        array_upd tag_1886 (i_1887) (array_index (n_v_1885) (i_1887))
      in
      (tag_1886))
    (tag_1886)
  in
  tag_1886

