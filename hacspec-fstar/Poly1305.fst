module Poly1305

open Rustspec
open FStar.Mul

module RSeq = Rustspec.Seq

let blocksize : usize =
  16ul

type block = RSeq.lseq s_u8 blocksize

type tag = RSeq.lseq u8 blocksize

type field_canvas = Seq.lseq u8 272ul

// missing natural mod int type decl!

let key_gen (key_1885 : key) (iv_1886 : iv) : key =
  let block_1887 = block (key_1885) (s_u32 (0ul)) (iv_1886) in
  RSeq.from_slice_range (block_1887) ((0ul, 32ul))

let encode_r (r_1888 : block) : field_element =
  let r_128_1889 = RSeq.from_slice (r_1888) (0ul) (blocksize) in
  let r_uint_1890 = s_u128_from_le_bytes (r_128_1889) in
  let r_uint_1891 =
    r_uint_1890 & s_u128 (
      UInt128.uint_to_t 21267647620597763993911028882763415551)
  in
  FieldElement.from_secret_literal (r_uint_1891)

let encode (block_1892 : byte_seq) : field_element =
  let block_len_1893 = len (block_1892) in
  let block_as_u128_1894 =
    RSeq.from_slice (block_1892) (0ul) (min (16ul) (block_len_1893))
  in
  let w_elem_1895 =
    FieldElement.from_secret_literal (s_u128_from_le_bytes (block_as_u128_1894))
  in
  let l_elem_1896 =
    FieldElement.from_canvas (RSeq.pow2 (8ul * block_len_1893))
  in
  w_elem_1895 + l_elem_1896

let poly_inner (m_1897 : byte_seq) (r_1898 : field_element) : field_element =
  let acc_1899 = FieldElement.from_literal (UInt128.uint_to_t 0) in
  let (acc_1899) =
    foldi (0ul) (num_chunks (m_1897) (blocksize)) (fun (i_1900, (acc_1899)) ->
      let (_, block_1901) = get_chunk (m_1897) (blocksize) (i_1900) in
      let acc_1899 = acc_1899 + encode (block_1901) * r_1898 in
      (acc_1899))
    (acc_1899)
  in
  acc_1899

let poly (m_1902 : byte_seq) (key_1903 : key) : tag =
  let s_elem_1904 =
    FieldElement.from_secret_literal (
      s_u128_from_le_bytes (RSeq.from_slice (key_1903) (blocksize) (blocksize)))
  in
  let r_elem_1905 =
    encode_r (RSeq.from_slice_range (key_1903) ((0ul, blocksize)))
  in
  let a_1906 = poly_inner (m_1902) (r_elem_1905) in
  let n_1907 = a_1906 + s_elem_1904 in
  let n_v_1908 = to_public_byte_seq_le (n_1907) in
  let tag_1909 = RSeq.new_ BLOCKSIZE () in
  let (tag_1909) =
    foldi (0ul) (min (len (tag_1909)) (len (n_v_1908))) (fun (i_1910, (tag_1909)
      ) ->
      let tag_1909 =
        array_upd tag_1909 (i_1910) (array_index (n_v_1908) (i_1910))
      in
      (tag_1909))
    (tag_1909)
  in
  tag_1909

let poly_mac (m_1911 : byte_seq) (key_1912 : key) (iv_1913 : iv) : tag =
  let mac_key_1914 = key_gen (key_1912) (iv_1913) in
  poly (m_1911) (mac_key_1914)

