module Chacha20

open Rustspec
open FStar.Mul

module RSeq = Rustspec.Seq

type state = RSeq.lseq s_u32 16ul

type state_bytes = RSeq.lseq s_u8 64ul

type iv = RSeq.lseq s_u8 12ul

type key = RSeq.lseq s_u8 32ul

let state_to_bytes (x_1870 : state) : state_bytes =
  let r_1871 = RSeq.new_ 64ul () in
  let (r_1871) =
    foldi (0ul) (len (x_1870)) (fun (i_1872, (r_1871)) ->
      let bytes_1873 = s_u32_to_be_bytes (array_index (x_1870) (i_1872)) in
      let r_1871 =
        array_upd r_1871 (i_1872 * 4ul) (array_index (bytes_1873) (3ul))
      in
      let r_1871 =
        array_upd r_1871 (i_1872 * 4ul + 1ul) (array_index (bytes_1873) (2ul))
      in
      let r_1871 =
        array_upd r_1871 (i_1872 * 4ul + 2ul) (array_index (bytes_1873) (1ul))
      in
      let r_1871 =
        array_upd r_1871 (i_1872 * 4ul + 3ul) (array_index (bytes_1873) (0ul))
      in
      (r_1871))
    (r_1871)
  in
  r_1871

let line
  (a_1874 : u32)
  (b_1875 : u32)
  (d_1876 : u32)
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
  (a_1880 : u32)
  (b_1881 : u32)
  (c_1882 : u32)
  (d_1883 : u32)
  (state_1884 : state)
  : state =
  let state_1885 = line (a_1880) (b_1881) (d_1883) (16ul) (state_1884) in
  let state_1886 = line (c_1882) (d_1883) (b_1881) (12ul) (state_1885) in
  let state_1887 = line (a_1880) (b_1881) (d_1883) (8ul) (state_1886) in
  line (c_1882) (d_1883) (b_1881) (7ul) (state_1887)

let double_round (state_1888 : state) : state =
  let state_1889 = quarter_round (0ul) (4ul) (8ul) (12ul) (state_1888) in
  let state_1890 = quarter_round (1ul) (5ul) (9ul) (13ul) (state_1889) in
  let state_1891 = quarter_round (2ul) (6ul) (10ul) (14ul) (state_1890) in
  let state_1892 = quarter_round (3ul) (7ul) (11ul) (15ul) (state_1891) in
  let state_1893 = quarter_round (0ul) (5ul) (10ul) (15ul) (state_1892) in
  let state_1894 = quarter_round (1ul) (6ul) (11ul) (12ul) (state_1893) in
  let state_1895 = quarter_round (2ul) (7ul) (8ul) (13ul) (state_1894) in
  quarter_round (3ul) (4ul) (9ul) (14ul) (state_1895)

let block_init (key_1896 : key) (ctr_1897 : s_u32) (iv_1898 : iv) : state =
  RSeq.from_list [
    s_u32 (1634760805ul);
    s_u32 (857760878ul);
    s_u32 (2036477234ul);
    s_u32 (1797285236ul);
    s_u32_from_le_bytes (RSeq.from_slice_range (key_1896) ((0ul, 4ul)));
    s_u32_from_le_bytes (RSeq.from_slice_range (key_1896) ((4ul, 8ul)));
    s_u32_from_le_bytes (RSeq.from_slice_range (key_1896) ((8ul, 12ul)));
    s_u32_from_le_bytes (RSeq.from_slice_range (key_1896) ((12ul, 16ul)));
    s_u32_from_le_bytes (RSeq.from_slice_range (key_1896) ((16ul, 20ul)));
    s_u32_from_le_bytes (RSeq.from_slice_range (key_1896) ((20ul, 24ul)));
    s_u32_from_le_bytes (RSeq.from_slice_range (key_1896) ((24ul, 28ul)));
    s_u32_from_le_bytes (RSeq.from_slice_range (key_1896) ((28ul, 32ul)));
    ctr_1897;
    s_u32_from_le_bytes (RSeq.from_slice_range (iv_1898) ((0ul, 4ul)));
    s_u32_from_le_bytes (RSeq.from_slice_range (iv_1898) ((4ul, 8ul)));
    s_u32_from_le_bytes (RSeq.from_slice_range (iv_1898) ((8ul, 12ul)))
  ]

let block_inner (key_1899 : key) (ctr_1900 : s_u32) (iv_1901 : iv) : state =
  let st_1902 = block_init (key_1899) (ctr_1900) (iv_1901) in
  let state_1903 = st_1902 in
  let (state_1903) =
    foldi (0ul) (10ul) (fun (i_1904, (state_1903)) ->
      let state_1903 = double_round (state_1903) in
      (state_1903))
    (state_1903)
  in
  let (state_1903) =
    foldi (0ul) (16ul) (fun (i_1905, (state_1903)) ->
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
  let ctr_1913 = s_u32 (1ul) in
  let blocks_out_1914 = RSeq.new_ (len (m_1912)) in
  let (ctr_1913, blocks_out_1914) =
    foldi (0ul) (num_chunks (m_1912) (64ul)) (fun (
        i_1915,
        (ctr_1913, blocks_out_1914)
      ) ->
      let (block_len_1916, msg_block_1917) =
        get_chunk (m_1912) (64ul) (i_1915)
      in
      let key_block_1918 = block (key_1910) (ctr_1913) (iv_1911) in
      let msg_block_padded_1919 = RSeq.new_ 64ul () in
      let msg_block_padded_1920 =
        update_start (msg_block_padded_1919) (msg_block_1917)
      in
      let blocks_out_1914 =
        set_chunk (blocks_out_1914) (64ul) (i_1915) (
          slice_range (msg_block_padded_1920 ^ key_block_1918) (
            (0ul, block_len_1916)))
      in
      let ctr_1913 = ctr_1913 + s_u32 (1ul) in
      (ctr_1913, blocks_out_1914))
    (ctr_1913, blocks_out_1914)
  in
  blocks_out_1914

