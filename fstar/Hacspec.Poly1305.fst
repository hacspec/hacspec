module Hacspec.Poly1305

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open Hacspec.Lib
open FStar.Mul

module RSeq = Hacspec.Lib.Seq
module RNat = Hacspec.Lib.Nat

type key_poly = RSeq.lseq (uint8) (usize 32)

let blocksize : uint_size =
  usize 16

type block = RSeq.lseq (uint8) (blocksize)

type tag = RSeq.lseq (pub_uint8) (blocksize)

type field_canvas = RSeq.lseq (pub_uint8) (usize 272)

type field_element = nat_mod 0x03fffffffffffffffffffffffffffffffb

let encode_r (r_1864 : block) : field_element =
  let r_128_1865 = RSeq.from_slice (r_1864) (usize 0) (blocksize) in
  let r_uint_1866 = uint128_from_le_bytes (r_128_1865) in
  let r_uint_1867 =
    r_uint_1866 &. secret (pub_u128 0xffffffc0ffffffc0ffffffc0fffffff)
  in
  RNat.from_secret_literal (r_uint_1867)

let encode (block_1868 : byte_seq) : field_element =
  let block_len_1869 = len (block_1868) in
  let block_as_u128_1870 =
    RSeq.from_slice (block_1868) (usize 0) (min (usize 16) (block_len_1869))
  in
  let w_elem_1871 =
    RNat.from_secret_literal (uint128_from_le_bytes (block_as_u128_1870))
  in
  let l_elem_1872 = RNat.pow2 (usize 8 *. block_len_1869) in
  w_elem_1871 +. l_elem_1872

let poly_inner (m_1873 : byte_seq) (r_1874 : field_element) : field_element =
  let acc_1875 = RNat.from_literal (pub_u128 0x0) in
  let (acc_1875) =
    foldi (usize 0) (num_chunks (m_1873) (blocksize)) (fun (i_1876, (acc_1875)
      ) ->
      let (_, block_1877) = get_chunk (m_1873) (blocksize) (i_1876) in
      let acc_1875 = acc_1875 +. encode (block_1877) *. r_1874 in
      (acc_1875))
    (acc_1875)
  in
  acc_1875

let poly (m_1878 : byte_seq) (key_1879 : key_poly) : tag =
  let s_elem_1880 =
    RNat.from_secret_literal (
      uint128_from_le_bytes (
        RSeq.from_slice (key_1879) (blocksize) (blocksize)))
  in
  let r_elem_1881 =
    encode_r (RSeq.from_slice_range (key_1879) ((usize 0, blocksize)))
  in
  let a_1882 = poly_inner (m_1878) (r_elem_1881) in
  let n_1883 = a_1882 +. s_elem_1880 in
  let n_v_1884 = to_public_byte_seq_le (n_1883) in
  let tag_1885 = RSeq.new_ BLOCKSIZE () in
  let (tag_1885) =
    foldi (usize 0) (min (len (tag_1885)) (len (n_v_1884))) (fun (
        i_1886,
        (tag_1885)
      ) ->
      let tag_1885 =
        array_upd tag_1885 (i_1886) (array_index (n_v_1884) (i_1886))
      in
      (tag_1885))
    (tag_1885)
  in
  tag_1885

