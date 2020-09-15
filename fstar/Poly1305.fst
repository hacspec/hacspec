module Poly1305

open Rustspec
open FStar.Mul

module RSeq = Rustspec.Seq

type key_poly = RSeq.lseq s_u8 32ul

let blocksize : usize =
  16ul

type block = RSeq.lseq s_u8 blocksize

type tag = RSeq.lseq u8 blocksize

type field_canvas = Seq.lseq u8 272ul

// missing natural mod int type decl!

let encode_r (r_1864 : block) : field_element =
  let r_128_1865 = RSeq.from_slice (r_1864) (0ul) (blocksize) in
  let r_uint_1866 = s_u128_from_le_bytes (r_128_1865) in
  let r_uint_1867 =
    r_uint_1866 & s_u128 (
      UInt128.uint_to_t 21267647620597763993911028882763415551)
  in
  FieldElement.from_secret_literal (r_uint_1867)

let encode (block_1868 : byte_seq) : field_element =
  let block_len_1869 = len (block_1868) in
  let block_as_u128_1870 =
    RSeq.from_slice (block_1868) (0ul) (min (16ul) (block_len_1869))
  in
  let w_elem_1871 =
    FieldElement.from_secret_literal (s_u128_from_le_bytes (block_as_u128_1870))
  in
  let l_elem_1872 =
    FieldElement.from_canvas (RSeq.pow2 (8ul * block_len_1869))
  in
  w_elem_1871 + l_elem_1872

let poly_inner (m_1873 : byte_seq) (r_1874 : field_element) : field_element =
  let acc_1875 = FieldElement.from_literal (UInt128.uint_to_t 0) in
  let (acc_1875) =
    foldi (0ul) (num_chunks (m_1873) (blocksize)) (fun (i_1876, (acc_1875)) ->
      let (_, block_1877) = get_chunk (m_1873) (blocksize) (i_1876) in
      let acc_1875 = acc_1875 + encode (block_1877) * r_1874 in
      (acc_1875))
    (acc_1875)
  in
  acc_1875

let poly (m_1878 : byte_seq) (key_1879 : key_poly) : tag =
  let s_elem_1880 =
    FieldElement.from_secret_literal (
      s_u128_from_le_bytes (RSeq.from_slice (key_1879) (blocksize) (blocksize)))
  in
  let r_elem_1881 =
    encode_r (RSeq.from_slice_range (key_1879) ((0ul, blocksize)))
  in
  let a_1882 = poly_inner (m_1878) (r_elem_1881) in
  let n_1883 = a_1882 + s_elem_1880 in
  let n_v_1884 = to_public_byte_seq_le (n_1883) in
  let tag_1885 = RSeq.new_ BLOCKSIZE () in
  let (tag_1885) =
    foldi (0ul) (min (len (tag_1885)) (len (n_v_1884))) (fun (i_1886, (tag_1885)
      ) ->
      let tag_1885 =
        array_upd tag_1885 (i_1886) (array_index (n_v_1884) (i_1886))
      in
      (tag_1885))
    (tag_1885)
  in
  tag_1885

