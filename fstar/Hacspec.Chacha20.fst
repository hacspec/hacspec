module Hacspec.Chacha20

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open Hacspec.Lib
open FStar.Mul

type state = lseq (uint32) (usize 16)

type state_bytes = lseq (uint8) (usize 64)

type iv = lseq (uint8) (usize 12)

type key = lseq (uint8) (usize 32)

let state_to_bytes (x_1864 : state) : state_bytes =
  let r_1865 = seq_new_ 64 (secret (pub_u8 0x8)) in
  let (r_1865) =
    foldi (usize 0) (seq_len (x_1864)) (fun (i_1866, (r_1865)) ->
      let bytes_1867 = uint32_to_be_bytes (array_index (x_1864) (i_1866)) in
      let r_1865 =
        array_upd r_1865 ((i_1866) * (usize 4)) (
          array_index (bytes_1867) (usize 3))
      in
      let r_1865 =
        array_upd r_1865 (((i_1866) * (usize 4)) + (usize 1)) (
          array_index (bytes_1867) (usize 2))
      in
      let r_1865 =
        array_upd r_1865 (((i_1866) * (usize 4)) + (usize 2)) (
          array_index (bytes_1867) (usize 1))
      in
      let r_1865 =
        array_upd r_1865 (((i_1866) * (usize 4)) + (usize 3)) (
          array_index (bytes_1867) (usize 0))
      in
      (r_1865))
    (r_1865)
  in
  r_1865

let line
  (a_1868 : pub_uint32)
  (b_1869 : pub_uint32)
  (d_1870 : pub_uint32)
  (s_1871 : uint_size)
  (m_1872 : state)
  : state =
  let state_1873 = m_1872 in
  let state_1873 =
    array_upd state_1873 (a_1868) (
      (array_index (state_1873) (a_1868)) +. (
        array_index (state_1873) (b_1869)))
  in
  let state_1873 =
    array_upd state_1873 (d_1870) (
      (array_index (state_1873) (d_1870)) ^. (
        array_index (state_1873) (a_1868)))
  in
  let state_1873 =
    array_upd state_1873 (d_1870) (
      uint32_rotate_left (array_index (state_1873) (d_1870)) (s_1871))
  in
  state_1873

let quarter_round
  (a_1874 : pub_uint32)
  (b_1875 : pub_uint32)
  (c_1876 : pub_uint32)
  (d_1877 : pub_uint32)
  (state_1878 : state)
  : state =
  let state_1879 = line (a_1874) (b_1875) (d_1877) (usize 16) (state_1878) in
  let state_1880 = line (c_1876) (d_1877) (b_1875) (usize 12) (state_1879) in
  let state_1881 = line (a_1874) (b_1875) (d_1877) (usize 8) (state_1880) in
  line (c_1876) (d_1877) (b_1875) (usize 7) (state_1881)

let double_round (state_1882 : state) : state =
  let state_1883 =
    quarter_round (pub_u32 0x0) (pub_u32 0x4) (pub_u32 0x8) (pub_u32 0xc) (
      state_1882)
  in
  let state_1884 =
    quarter_round (pub_u32 0x1) (pub_u32 0x5) (pub_u32 0x9) (pub_u32 0xd) (
      state_1883)
  in
  let state_1885 =
    quarter_round (pub_u32 0x2) (pub_u32 0x6) (pub_u32 0xa) (pub_u32 0xe) (
      state_1884)
  in
  let state_1886 =
    quarter_round (pub_u32 0x3) (pub_u32 0x7) (pub_u32 0xb) (pub_u32 0xf) (
      state_1885)
  in
  let state_1887 =
    quarter_round (pub_u32 0x0) (pub_u32 0x5) (pub_u32 0xa) (pub_u32 0xf) (
      state_1886)
  in
  let state_1888 =
    quarter_round (pub_u32 0x1) (pub_u32 0x6) (pub_u32 0xb) (pub_u32 0xc) (
      state_1887)
  in
  let state_1889 =
    quarter_round (pub_u32 0x2) (pub_u32 0x7) (pub_u32 0x8) (pub_u32 0xd) (
      state_1888)
  in
  quarter_round (pub_u32 0x3) (pub_u32 0x4) (pub_u32 0x9) (pub_u32 0xe) (
    state_1889)

let block_init (key_1890 : key) (ctr_1891 : uint32) (iv_1892 : iv) : state =
  seq_from_list [
    secret (pub_u32 0x61707865);
    secret (pub_u32 0x3320646e);
    secret (pub_u32 0x79622d32);
    secret (pub_u32 0x6b206574);
    uint32_from_le_bytes (
      seq_from_slice_range 4 (key_1890) ((usize 0, usize 4)));
    uint32_from_le_bytes (
      seq_from_slice_range 4 (key_1890) ((usize 4, usize 8)));
    uint32_from_le_bytes (
      seq_from_slice_range 4 (key_1890) ((usize 8, usize 12)));
    uint32_from_le_bytes (
      seq_from_slice_range 4 (key_1890) ((usize 12, usize 16)));
    uint32_from_le_bytes (
      seq_from_slice_range 4 (key_1890) ((usize 16, usize 20)));
    uint32_from_le_bytes (
      seq_from_slice_range 4 (key_1890) ((usize 20, usize 24)));
    uint32_from_le_bytes (
      seq_from_slice_range 4 (key_1890) ((usize 24, usize 28)));
    uint32_from_le_bytes (
      seq_from_slice_range 4 (key_1890) ((usize 28, usize 32)));
    ctr_1891;
    uint32_from_le_bytes (
      seq_from_slice_range 4 (iv_1892) ((usize 0, usize 4)));
    uint32_from_le_bytes (
      seq_from_slice_range 4 (iv_1892) ((usize 4, usize 8)));
    uint32_from_le_bytes (
      seq_from_slice_range 4 (iv_1892) ((usize 8, usize 12)))
  ]

let block_inner (key_1893 : key) (ctr_1894 : uint32) (iv_1895 : iv) : state =
  let st_1896 = block_init (key_1893) (ctr_1894) (iv_1895) in
  let state_1897 = st_1896 in
  let (state_1897) =
    foldi (usize 0) (usize 10) (fun (i_1898, (state_1897)) ->
      let state_1897 = double_round (state_1897) in
      (state_1897))
    (state_1897)
  in
  let (state_1897) =
    foldi (usize 0) (usize 16) (fun (i_1899, (state_1897)) ->
      let state_1897 =
        array_upd state_1897 (i_1899) (
          (array_index (state_1897) (i_1899)) +. (
            array_index (st_1896) (i_1899)))
      in
      (state_1897))
    (state_1897)
  in
  state_1897

let block (key_1900 : key) (ctr_1901 : uint32) (iv_1902 : iv) : state_bytes =
  let state_1903 = block_inner (key_1900) (ctr_1901) (iv_1902) in
  state_to_bytes (state_1903)

let chacha (key_1904 : key) (iv_1905 : iv) (m_1906 : byte_seq) : byte_seq =
  let ctr_1907 = secret (pub_u32 0x1) in
  let blocks_out_1908 = seq_new_ (secret (pub_u8 0x8)) (seq_len (m_1906)) in
  let (blocks_out_1908, ctr_1907) =
    foldi (usize 0) (seq_num_chunks (m_1906) (usize 64)) (fun (
        i_1909,
        (blocks_out_1908, ctr_1907)
      ) ->
      let (block_len_1910, msg_block_1911) =
        seq_get_chunk (m_1906) (usize 64) (i_1909)
      in
      let key_block_1912 = block (key_1904) (ctr_1907) (iv_1905) in
      let msg_block_padded_1913 = seq_new_ 64 (secret (pub_u8 0x8)) in
      let msg_block_padded_1914 =
        seq_update_start (msg_block_padded_1913) (msg_block_1911)
      in
      let blocks_out_1908 =
        seq_set_chunk #uint8 (blocks_out_1908) (usize 64) (i_1909) (
          seq_slice_range ((msg_block_padded_1914) `seq_xor` (key_block_1912)) (
            (usize 0, block_len_1910)))
      in
      let ctr_1907 = (ctr_1907) +. (secret (pub_u32 0x1)) in
      (blocks_out_1908, ctr_1907))
    (blocks_out_1908, ctr_1907)
  in
  blocks_out_1908

