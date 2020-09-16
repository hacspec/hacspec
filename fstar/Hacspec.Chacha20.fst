module Hacspec.Chacha20

open Hacspec.Lib
open FStar.Mul

module RSeq = Hacspec.Lib.Seq

type state = RSeq.lseq s_u32 (pub_u32 16ul)

type state_bytes = RSeq.lseq s_u8 (pub_u32 64ul)

type iv = RSeq.lseq s_u8 (pub_u32 12ul)

type key = RSeq.lseq s_u8 (pub_u32 32ul)

let state_to_bytes (x_1870 : state) : state_bytes =
  let r_1871 = RSeq.new_ 64ul () in
  let (r_1871) =
    foldi ((pub_u32 0ul)) (len (x_1870)) (fun (i_1872, (r_1871)) ->
      let bytes_1873 = s_u32_to_be_bytes (array_index (x_1870) (i_1872)) in
      let r_1871 =
        array_upd r_1871 (i_1872 * (pub_u32 4ul)) (
          array_index (bytes_1873) ((pub_u32 3ul)))
      in
      let r_1871 =
        array_upd r_1871 (i_1872 * (pub_u32 4ul) + (pub_u32 1ul)) (
          array_index (bytes_1873) ((pub_u32 2ul)))
      in
      let r_1871 =
        array_upd r_1871 (i_1872 * (pub_u32 4ul) + (pub_u32 2ul)) (
          array_index (bytes_1873) ((pub_u32 1ul)))
      in
      let r_1871 =
        array_upd r_1871 (i_1872 * (pub_u32 4ul) + (pub_u32 3ul)) (
          array_index (bytes_1873) ((pub_u32 0ul)))
      in
      (r_1871))
    (r_1871)
  in
  r_1871

let line
  (a_1874 : pub_uint32)
  (b_1875 : pub_uint32)
  (d_1876 : pub_uint32)
  (s_1877 : usize)
  (m_1878 : state)
  : state =
  let state_1879 = m_1878 in
  let state_1879 =
    array_upd state_1879 (a_1874) (
      array_index (state_1879) (a_1874) + array_index (state_1879) (b_1875))
  in
  let state_1879 =
    array_upd state_1879 (d_1876) (
      array_index (state_1879) (d_1876) ^ array_index (state_1879) (a_1874))
  in
  let state_1879 =
    array_upd state_1879 (d_1876) (
      rotate_left (array_index (state_1879) (d_1876)) (s_1877))
  in
  state_1879

let quarter_round
  (a_1880 : pub_uint32)
  (b_1881 : pub_uint32)
  (c_1882 : pub_uint32)
  (d_1883 : pub_uint32)
  (state_1884 : state)
  : state =
  let state_1885 =
    line (a_1880) (b_1881) (d_1883) ((pub_u32 16ul)) (state_1884)
  in
  let state_1886 =
    line (c_1882) (d_1883) (b_1881) ((pub_u32 12ul)) (state_1885)
  in
  let state_1887 =
    line (a_1880) (b_1881) (d_1883) ((pub_u32 8ul)) (state_1886)
  in
  line (c_1882) (d_1883) (b_1881) ((pub_u32 7ul)) (state_1887)

let double_round (state_1888 : state) : state =
  let state_1889 =
    quarter_round ((pub_u32 0x0ul)) ((pub_u32 0x4ul)) ((pub_u32 0x8ul)) (
      (pub_u32 0xcul)) (state_1888)
  in
  let state_1890 =
    quarter_round ((pub_u32 0x1ul)) ((pub_u32 0x5ul)) ((pub_u32 0x9ul)) (
      (pub_u32 0xdul)) (state_1889)
  in
  let state_1891 =
    quarter_round ((pub_u32 0x2ul)) ((pub_u32 0x6ul)) ((pub_u32 0xaul)) (
      (pub_u32 0xeul)) (state_1890)
  in
  let state_1892 =
    quarter_round ((pub_u32 0x3ul)) ((pub_u32 0x7ul)) ((pub_u32 0xbul)) (
      (pub_u32 0xful)) (state_1891)
  in
  let state_1893 =
    quarter_round ((pub_u32 0x0ul)) ((pub_u32 0x5ul)) ((pub_u32 0xaul)) (
      (pub_u32 0xful)) (state_1892)
  in
  let state_1894 =
    quarter_round ((pub_u32 0x1ul)) ((pub_u32 0x6ul)) ((pub_u32 0xbul)) (
      (pub_u32 0xcul)) (state_1893)
  in
  let state_1895 =
    quarter_round ((pub_u32 0x2ul)) ((pub_u32 0x7ul)) ((pub_u32 0x8ul)) (
      (pub_u32 0xdul)) (state_1894)
  in
  quarter_round ((pub_u32 0x3ul)) ((pub_u32 0x4ul)) ((pub_u32 0x9ul)) (
    (pub_u32 0xeul)) (state_1895)

let block_init (key_1896 : key) (ctr_1897 : s_u32) (iv_1898 : iv) : state =
  RSeq.from_list [
    s_u32 ((pub_u32 0x61707865ul));
    s_u32 ((pub_u32 0x3320646eul));
    s_u32 ((pub_u32 0x79622d32ul));
    s_u32 ((pub_u32 0x6b206574ul));
    s_u32_from_le_bytes (
      RSeq.from_slice_range (key_1896) (((pub_u32 0ul), (pub_u32 4ul))));
    s_u32_from_le_bytes (
      RSeq.from_slice_range (key_1896) (((pub_u32 4ul), (pub_u32 8ul))));
    s_u32_from_le_bytes (
      RSeq.from_slice_range (key_1896) (((pub_u32 8ul), (pub_u32 12ul))));
    s_u32_from_le_bytes (
      RSeq.from_slice_range (key_1896) (((pub_u32 12ul), (pub_u32 16ul))));
    s_u32_from_le_bytes (
      RSeq.from_slice_range (key_1896) (((pub_u32 16ul), (pub_u32 20ul))));
    s_u32_from_le_bytes (
      RSeq.from_slice_range (key_1896) (((pub_u32 20ul), (pub_u32 24ul))));
    s_u32_from_le_bytes (
      RSeq.from_slice_range (key_1896) (((pub_u32 24ul), (pub_u32 28ul))));
    s_u32_from_le_bytes (
      RSeq.from_slice_range (key_1896) (((pub_u32 28ul), (pub_u32 32ul))));
    ctr_1897;
    s_u32_from_le_bytes (
      RSeq.from_slice_range (iv_1898) (((pub_u32 0ul), (pub_u32 4ul))));
    s_u32_from_le_bytes (
      RSeq.from_slice_range (iv_1898) (((pub_u32 4ul), (pub_u32 8ul))));
    s_u32_from_le_bytes (
      RSeq.from_slice_range (iv_1898) (((pub_u32 8ul), (pub_u32 12ul))))
  ]

let block_inner (key_1899 : key) (ctr_1900 : s_u32) (iv_1901 : iv) : state =
  let st_1902 = block_init (key_1899) (ctr_1900) (iv_1901) in
  let state_1903 = st_1902 in
  let (state_1903) =
    foldi ((pub_u32 0ul)) ((pub_u32 10ul)) (fun (i_1904, (state_1903)) ->
      let state_1903 = double_round (state_1903) in
      (state_1903))
    (state_1903)
  in
  let (state_1903) =
    foldi ((pub_u32 0ul)) ((pub_u32 16ul)) (fun (i_1905, (state_1903)) ->
      let state_1903 =
        array_upd state_1903 (i_1905) (
          array_index (state_1903) (i_1905) + array_index (st_1902) (i_1905))
      in
      (state_1903))
    (state_1903)
  in
  state_1903

let block (key_1906 : key) (ctr_1907 : s_u32) (iv_1908 : iv) : state_bytes =
  let state_1909 = block_inner (key_1906) (ctr_1907) (iv_1908) in
  state_to_bytes (state_1909)

let chacha (key_1910 : key) (iv_1911 : iv) (m_1912 : byte_seq) : byte_seq =
  let ctr_1913 = s_u32 ((pub_u32 0x1ul)) in
  let blocks_out_1914 = RSeq.new_ (len (m_1912)) in
  let (blocks_out_1914, ctr_1913) =
    foldi ((pub_u32 0ul)) (num_chunks (m_1912) ((pub_u32 64ul))) (fun (
        i_1915,
        (blocks_out_1914, ctr_1913)
      ) ->
      let (block_len_1916, msg_block_1917) =
        get_chunk (m_1912) ((pub_u32 64ul)) (i_1915)
      in
      let key_block_1918 = block (key_1910) (ctr_1913) (iv_1911) in
      let msg_block_padded_1919 = RSeq.new_ 64ul () in
      let msg_block_padded_1920 =
        update_start (msg_block_padded_1919) (msg_block_1917)
      in
      let blocks_out_1914 =
        set_chunk (blocks_out_1914) ((pub_u32 64ul)) (i_1915) (
          slice_range (msg_block_padded_1920 ^ key_block_1918) (
            ((pub_u32 0ul), block_len_1916)))
      in
      let ctr_1913 = ctr_1913 + s_u32 ((pub_u32 0x1ul)) in
      (blocks_out_1914, ctr_1913))
    (blocks_out_1914, ctr_1913)
  in
  blocks_out_1914

