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

let state_to_bytes (x_1871 : state) : state_bytes =
  let r_1872 = array_new_ (secret (pub_u8 0x8)) (64) in
  let (r_1872) =
    foldi (usize 0) (array_len (x_1871)) (fun i_1873 (r_1872) ->
      let bytes_1874 = uint32_to_be_bytes (array_index (x_1871) (i_1873)) in
      let r_1872 =
        array_upd r_1872 ((i_1873) * (usize 4)) (
          array_index (bytes_1874) (usize 3))
      in
      let r_1872 =
        array_upd r_1872 (((i_1873) * (usize 4)) + (usize 1)) (
          array_index (bytes_1874) (usize 2))
      in
      let r_1872 =
        array_upd r_1872 (((i_1873) * (usize 4)) + (usize 2)) (
          array_index (bytes_1874) (usize 1))
      in
      let r_1872 =
        array_upd r_1872 (((i_1873) * (usize 4)) + (usize 3)) (
          array_index (bytes_1874) (usize 0))
      in
      (r_1872))
    (r_1872)
  in
  r_1872

let line
  (a_1875 : state_idx)
  (b_1876 : state_idx)
  (d_1877 : state_idx)
  (s_1878 : uint_size)
  (m_1879 : state)
  : state =
  let state_1880 = m_1879 in
  let state_1880 =
    array_upd state_1880 (a_1875) (
      (array_index (state_1880) (a_1875)) +. (
        array_index (state_1880) (b_1876)))
  in
  let state_1880 =
    array_upd state_1880 (d_1877) (
      (array_index (state_1880) (d_1877)) ^. (
        array_index (state_1880) (a_1875)))
  in
  let state_1880 =
    array_upd state_1880 (d_1877) (
      uint32_rotate_left (array_index (state_1880) (d_1877)) (s_1878))
  in
  state_1880

let quarter_round
  (a_1881 : state_idx)
  (b_1882 : state_idx)
  (c_1883 : state_idx)
  (d_1884 : state_idx)
  (state_1885 : state)
  : state =
  let state_1886 = line (a_1881) (b_1882) (d_1884) (usize 16) (state_1885) in
  let state_1887 = line (c_1883) (d_1884) (b_1882) (usize 12) (state_1886) in
  let state_1888 = line (a_1881) (b_1882) (d_1884) (usize 8) (state_1887) in
  line (c_1883) (d_1884) (b_1882) (usize 7) (state_1888)

let double_round (state_1889 : state) : state =
  let state_1890 =
    quarter_round (usize 0) (usize 4) (usize 8) (usize 12) (state_1889)
  in
  let state_1891 =
    quarter_round (usize 1) (usize 5) (usize 9) (usize 13) (state_1890)
  in
  let state_1892 =
    quarter_round (usize 2) (usize 6) (usize 10) (usize 14) (state_1891)
  in
  let state_1893 =
    quarter_round (usize 3) (usize 7) (usize 11) (usize 15) (state_1892)
  in
  let state_1894 =
    quarter_round (usize 0) (usize 5) (usize 10) (usize 15) (state_1893)
  in
  let state_1895 =
    quarter_round (usize 1) (usize 6) (usize 11) (usize 12) (state_1894)
  in
  let state_1896 =
    quarter_round (usize 2) (usize 7) (usize 8) (usize 13) (state_1895)
  in
  quarter_round (usize 3) (usize 4) (usize 9) (usize 14) (state_1896)

let block_init (key_1897 : key) (ctr_1898 : uint32) (iv_1899 : iv) : state =
  array_from_list (
    let l =
      [
        secret (pub_u32 0x61707865);
        secret (pub_u32 0x3320646e);
        secret (pub_u32 0x79622d32);
        secret (pub_u32 0x6b206574);
        uint32_from_le_bytes (
          array_from_slice_range (key_1897) ((usize 0, usize 4)));
        uint32_from_le_bytes (
          array_from_slice_range (key_1897) ((usize 4, usize 8)));
        uint32_from_le_bytes (
          array_from_slice_range (key_1897) ((usize 8, usize 12)));
        uint32_from_le_bytes (
          array_from_slice_range (key_1897) ((usize 12, usize 16)));
        uint32_from_le_bytes (
          array_from_slice_range (key_1897) ((usize 16, usize 20)));
        uint32_from_le_bytes (
          array_from_slice_range (key_1897) ((usize 20, usize 24)));
        uint32_from_le_bytes (
          array_from_slice_range (key_1897) ((usize 24, usize 28)));
        uint32_from_le_bytes (
          array_from_slice_range (key_1897) ((usize 28, usize 32)));
        ctr_1898;
        uint32_from_le_bytes (
          array_from_slice_range (iv_1899) ((usize 0, usize 4)));
        uint32_from_le_bytes (
          array_from_slice_range (iv_1899) ((usize 4, usize 8)));
        uint32_from_le_bytes (
          array_from_slice_range (iv_1899) ((usize 8, usize 12)))
      ]
    in assert_norm (List.Tot.length l == 16); l)

let block_inner (key_1900 : key) (ctr_1901 : uint32) (iv_1902 : iv) : state =
  let st_1903 = block_init (key_1900) (ctr_1901) (iv_1902) in
  let state_1904 = st_1903 in
  let (state_1904) =
    foldi (usize 0) (usize 10) (fun i_1905 (state_1904) ->
      let state_1904 = double_round (state_1904) in
      (state_1904))
    (state_1904)
  in
  let (state_1904) =
    foldi (usize 0) (usize 16) (fun i_1906 (state_1904) ->
      let state_1904 =
        array_upd state_1904 (i_1906) (
          (array_index (state_1904) (i_1906)) +. (
            array_index (st_1903) (i_1906)))
      in
      (state_1904))
    (state_1904)
  in
  state_1904

let block (key_1907 : key) (ctr_1908 : uint32) (iv_1909 : iv) : state_bytes =
  let state_1910 = block_inner (key_1907) (ctr_1908) (iv_1909) in
  state_to_bytes (state_1910)

let chacha (key_1911 : key) (iv_1912 : iv) (m_1913 : byte_seq) : byte_seq =
  let ctr_1914 = secret (pub_u32 0x1) in
  let blocks_out_1915 = seq_new_ (secret (pub_u8 0x8)) (seq_len (m_1913)) in
  let (blocks_out_1915, ctr_1914) =
    foldi (usize 0) (seq_num_chunks (m_1913) (usize 64)) (fun i_1916 (
        blocks_out_1915,
        ctr_1914
      ) ->
      let (block_len_1917, msg_block_1918) =
        seq_get_chunk (m_1913) (usize 64) (i_1916)
      in
      let key_block_1919 = block (key_1911) (ctr_1914) (iv_1912) in
      let msg_block_padded_1920 = array_new_ (secret (pub_u8 0x8)) (64) in
      let msg_block_padded_1921 =
        array_update_start (msg_block_padded_1920) (msg_block_1918)
      in
      let blocks_out_1915 =
        seq_set_chunk (blocks_out_1915) (usize 64) (i_1916) (
          array_slice_range (
            (msg_block_padded_1921) `array_xor` (key_block_1919)) (
            (usize 0, block_len_1917)))
      in
      let ctr_1914 = (ctr_1914) +. (secret (pub_u32 0x1)) in
      (blocks_out_1915, ctr_1914))
    (blocks_out_1915, ctr_1914)
  in
  blocks_out_1915

