module Hacspec.Chacha20

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open Hacspec.Lib
open FStar.Mul

type state = lseq (uint32) (usize 16)

let state_idx =
  nat_mod (usize 16)

type state_bytes = lseq (uint8) (usize 64)

type iv = lseq (uint8) (usize 12)

type key = lseq (uint8) (usize 32)

let state_to_bytes (x_1874 : state) : state_bytes =
  let r_1875 = array_new_ (secret (pub_u8 0x8)) (64) in
  let (r_1875) =
    foldi (usize 0) (array_len (x_1874)) (fun i_1876 (r_1875) ->
      let bytes_1877 = uint32_to_be_bytes (array_index (x_1874) (i_1876)) in
      let r_1875 =
        array_upd r_1875 ((i_1876) * (usize 4)) (
          array_index (bytes_1877) (usize 3))
      in
      let r_1875 =
        array_upd r_1875 (((i_1876) * (usize 4)) + (usize 1)) (
          array_index (bytes_1877) (usize 2))
      in
      let r_1875 =
        array_upd r_1875 (((i_1876) * (usize 4)) + (usize 2)) (
          array_index (bytes_1877) (usize 1))
      in
      let r_1875 =
        array_upd r_1875 (((i_1876) * (usize 4)) + (usize 3)) (
          array_index (bytes_1877) (usize 0))
      in
      (r_1875))
    (r_1875)
  in
  r_1875

let line
  (a_1878 : state_idx)
  (b_1879 : state_idx)
  (d_1880 : state_idx)
  (s_1881 : uint_size)
  (m_1882 : state)
  : state =
  let state_1883 = m_1882 in
  let state_1883 =
    array_upd state_1883 (a_1878) (
      (array_index (state_1883) (a_1878)) +. (
        array_index (state_1883) (b_1879)))
  in
  let state_1883 =
    array_upd state_1883 (d_1880) (
      (array_index (state_1883) (d_1880)) ^. (
        array_index (state_1883) (a_1878)))
  in
  let state_1883 =
    array_upd state_1883 (d_1880) (
      uint32_rotate_left (array_index (state_1883) (d_1880)) (s_1881))
  in
  state_1883

let quarter_round
  (a_1884 : state_idx)
  (b_1885 : state_idx)
  (c_1886 : state_idx)
  (d_1887 : state_idx)
  (state_1888 : state)
  : state =
  let state_1889 = line (a_1884) (b_1885) (d_1887) (usize 16) (state_1888) in
  let state_1890 = line (c_1886) (d_1887) (b_1885) (usize 12) (state_1889) in
  let state_1891 = line (a_1884) (b_1885) (d_1887) (usize 8) (state_1890) in
  line (c_1886) (d_1887) (b_1885) (usize 7) (state_1891)

let double_round (state_1892 : state) : state =
  let state_1893 =
    quarter_round (usize 0) (usize 4) (usize 8) (usize 12) (state_1892)
  in
  let state_1894 =
    quarter_round (usize 1) (usize 5) (usize 9) (usize 13) (state_1893)
  in
  let state_1895 =
    quarter_round (usize 2) (usize 6) (usize 10) (usize 14) (state_1894)
  in
  let state_1896 =
    quarter_round (usize 3) (usize 7) (usize 11) (usize 15) (state_1895)
  in
  let state_1897 =
    quarter_round (usize 0) (usize 5) (usize 10) (usize 15) (state_1896)
  in
  let state_1898 =
    quarter_round (usize 1) (usize 6) (usize 11) (usize 12) (state_1897)
  in
  let state_1899 =
    quarter_round (usize 2) (usize 7) (usize 8) (usize 13) (state_1898)
  in
  quarter_round (usize 3) (usize 4) (usize 9) (usize 14) (state_1899)

let block_init (key_1900 : key) (ctr_1901 : uint32) (iv_1902 : iv) : state =
  array_from_list (
    let l =
      [
        secret (pub_u32 0x61707865);
        secret (pub_u32 0x3320646e);
        secret (pub_u32 0x79622d32);
        secret (pub_u32 0x6b206574);
        uint32_from_le_bytes (
          array_from_slice_range (key_1900) ((usize 0, usize 4)));
        uint32_from_le_bytes (
          array_from_slice_range (key_1900) ((usize 4, usize 8)));
        uint32_from_le_bytes (
          array_from_slice_range (key_1900) ((usize 8, usize 12)));
        uint32_from_le_bytes (
          array_from_slice_range (key_1900) ((usize 12, usize 16)));
        uint32_from_le_bytes (
          array_from_slice_range (key_1900) ((usize 16, usize 20)));
        uint32_from_le_bytes (
          array_from_slice_range (key_1900) ((usize 20, usize 24)));
        uint32_from_le_bytes (
          array_from_slice_range (key_1900) ((usize 24, usize 28)));
        uint32_from_le_bytes (
          array_from_slice_range (key_1900) ((usize 28, usize 32)));
        ctr_1901;
        uint32_from_le_bytes (
          array_from_slice_range (iv_1902) ((usize 0, usize 4)));
        uint32_from_le_bytes (
          array_from_slice_range (iv_1902) ((usize 4, usize 8)));
        uint32_from_le_bytes (
          array_from_slice_range (iv_1902) ((usize 8, usize 12)))
      ]
    in assert_norm (List.Tot.length l == 16); l)

let block_inner (key_1903 : key) (ctr_1904 : uint32) (iv_1905 : iv) : state =
  let st_1906 = block_init (key_1903) (ctr_1904) (iv_1905) in
  let state_1907 = st_1906 in
  let (state_1907) =
    foldi (usize 0) (usize 10) (fun i_1908 (state_1907) ->
      let state_1907 = double_round (state_1907) in
      (state_1907))
    (state_1907)
  in
  let (state_1907) =
    foldi (usize 0) (usize 16) (fun i_1909 (state_1907) ->
      let state_1907 =
        array_upd state_1907 (i_1909) (
          (array_index (state_1907) (i_1909)) +. (
            array_index (st_1906) (i_1909)))
      in
      (state_1907))
    (state_1907)
  in
  state_1907

let block (key_1910 : key) (ctr_1911 : uint32) (iv_1912 : iv) : state_bytes =
  let state_1913 = block_inner (key_1910) (ctr_1911) (iv_1912) in
  state_to_bytes (state_1913)

let chacha (key_1914 : key) (iv_1915 : iv) (m_1916 : byte_seq) : byte_seq =
  let ctr_1917 = secret (pub_u32 0x1) in
  let blocks_out_1918 = seq_new_ (secret (pub_u8 0x8)) (seq_len (m_1916)) in
  let (blocks_out_1918, ctr_1917) =
    foldi (usize 0) (seq_num_chunks (m_1916) (usize 64)) (fun i_1919 (
        blocks_out_1918,
        ctr_1917
      ) ->
      let (block_len_1920, msg_block_1921) =
        seq_get_chunk (m_1916) (usize 64) (i_1919)
      in
      let key_block_1922 = block (key_1914) (ctr_1917) (iv_1915) in
      let msg_block_padded_1923 = array_new_ (secret (pub_u8 0x8)) (64) in
      let msg_block_padded_1924 =
        array_update_start (msg_block_padded_1923) (msg_block_1921)
      in
      let blocks_out_1918 =
        seq_set_chunk (blocks_out_1918) (usize 64) (i_1919) (
          array_slice_range (
            (msg_block_padded_1924) `array_xor` (key_block_1922)) (
            (usize 0, block_len_1920)))
      in
      let ctr_1917 = (ctr_1917) +. (secret (pub_u32 0x1)) in
      (blocks_out_1918, ctr_1917))
    (blocks_out_1918, ctr_1917)
  in
  blocks_out_1918

