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

let encode_r (r_1858 : block) : field_element =
  let r_128_1859 = seq_from_slice 16 (r_1858) (usize 0) (blocksize) in
  let r_uint_1860 = uint128_from_le_bytes (r_128_1859) in
  let r_uint_1861 =
    (r_uint_1860) &. (secret (pub_u128 0xffffffc0ffffffc0ffffffc0fffffff))
  in
  nat_from_secret_literal (r_uint_1861)

let encode (block_1862 : byte_seq) : field_element =
  let block_len_1863 = seq_len (block_1862) in
  let block_as_u128_1864 =
    seq_from_slice 16 (block_1862) (usize 0) (min (usize 16) (block_len_1863))
  in
  let w_elem_1865 =
    nat_from_secret_literal (uint128_from_le_bytes (block_as_u128_1864))
  in
  let l_elem_1866 = nat_pow2 ((usize 8) * (block_len_1863)) in
  (w_elem_1865) + (l_elem_1866)

let poly_inner (m_1867 : byte_seq) (r_1868 : field_element) : field_element =
  let acc_1869 = nat_from_literal (pub_u128 0x0) in
  let (acc_1869) =
    foldi (usize 0) (seq_num_chunks (m_1867) (blocksize)) (fun (
        i_1870,
        (acc_1869)
      ) ->
      let (_, block_1871) = seq_get_chunk (m_1867) (blocksize) (i_1870) in
      let acc_1869 = ((acc_1869) + (encode (block_1871))) * (r_1868) in
      (acc_1869))
    (acc_1869)
  in
  acc_1869

let poly (m_1872 : byte_seq) (key_1873 : key_poly) : tag =
  let s_elem_1874 =
    nat_from_secret_literal (
      uint128_from_le_bytes (
        seq_from_slice 16 (key_1873) (blocksize) (blocksize)))
  in
  let r_elem_1875 =
    encode_r (seq_from_slice_range blocksize (key_1873) ((usize 0, blocksize)))
  in
  let a_1876 = poly_inner (m_1872) (r_elem_1875) in
  let n_1877 = (a_1876) + (s_elem_1874) in
  let n_v_1878 = nat_to_public_byte_seq_le (n_1877) in
  let tag_1879 = seq_new_ blocksize (pub_u8 0x0) in
  let (tag_1879) =
    foldi (usize 0) (
        min (seq_len (tag_1879)) (seq_len #pub_uint8 (n_v_1878))) (fun (
        i_1880,
        (tag_1879)
      ) ->
      let tag_1879 =
        array_upd tag_1879 (i_1880) (array_index (n_v_1878) (i_1880))
      in
      (tag_1879))
    (tag_1879)
  in
  tag_1879

