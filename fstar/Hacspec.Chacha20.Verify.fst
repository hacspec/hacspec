module Hacspec.Chacha20.Verify

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open Hacspec.Lib
open FStar.Mul

type state = lseq (uint32) (usize 16)

type state_bytes = lseq (uint8) (usize 64)

type iv = lseq (uint8) (usize 12)

type key = lseq (uint8) (usize 32)

let state_to_bytes (x_1870 : state) : state_bytes =
  let r_1871 = seq_new_ 64 (u8 0) in
  let (r_1871) =
    foldi (usize 0) (seq_len x_1870) (fun (i_1872, (r_1871)) ->
      let bytes_1873 = uint32_to_be_bytes (array_index (x_1870) (i_1872)) in
      let r_1871 =
        array_upd r_1871 ((i_1872) * (usize 4)) (
          array_index (bytes_1873) (usize 3))
      in
      let r_1871 =
        array_upd r_1871 (((i_1872) * (usize 4)) + (usize 1)) (
          array_index (bytes_1873) (usize 2))
      in
      let r_1871 =
        array_upd r_1871 (((i_1872) * (usize 4)) + (usize 2)) (
          array_index (bytes_1873) (usize 1))
      in
      let r_1871 =
        array_upd r_1871 (((i_1872) * (usize 4)) + (usize 3)) (
          array_index (bytes_1873) (usize 0))
      in
      (r_1871))
    (r_1871)
  in
  r_1871

type state_range = u:uint_size {u < 16}
let line
  (a_1874 : state_range)
  (b_1875 : state_range)
  (d_1876 : state_range)
  (s_1877 : rotval U32)
  (m_1878 : state)
  : state =
  let state_1879 = m_1878 in
  let state_1879 =
    array_upd state_1879 (a_1874) (
      (array_index (state_1879) (a_1874)) +. (
        array_index (state_1879) (b_1875)))
  in
  let state_1879 =
    array_upd state_1879 (d_1876) (
      (array_index (state_1879) (d_1876)) ^. (
        array_index (state_1879) (a_1874)))
  in
  let state_1879 =
    array_upd state_1879 (d_1876) (
      rotate_left (array_index (state_1879) (d_1876)) (s_1877))
  in
  state_1879

let quarter_round
  (a_1880 : state_range)
  (b_1881 : state_range)
  (c_1882 : state_range)
  (d_1883 : state_range)
  (state_1884 : state)
  : state =
  let state_1885 = line (a_1880) (b_1881) (d_1883) (pub_u32 16) (state_1884) in
  let state_1886 = line (c_1882) (d_1883) (b_1881) (pub_u32 12) (state_1885) in
  let state_1887 = line (a_1880) (b_1881) (d_1883) (pub_u32 8) (state_1886) in
  line (c_1882) (d_1883) (b_1881) (pub_u32 7) (state_1887)

(* Copied from Spec.Chacha.fst: *)
type st = lseq uint32 16
type idx = n:size_nat{n < 16}
type shuffle = state -> Tot state
let op_At f g = fun x -> g (f x)

let hacl_line (a:idx) (b:idx) (d:idx) (s:rotval U32) (m:st) : Tot st =
  let open Lib.Sequence in
  let m = m.[a] <- (m.[a] +. m.[b]) in
  let m = m.[d] <- (m.[d] ^. m.[a]) in
  let m = m.[d] <- (m.[d] <<<. s) in m

let line_lemma a b d s m : Lemma (a <> d ==> line a b d s m == hacl_line a b d s m) = ()
(*  let open Lib.Sequence in
  let st1 = line a b d s m in
  let st2 = hacl_line a b d s m in
  assert (a <> d ==> st1.[a] == m.[a] +. m.[b]);
  Lib.Sequence.eq_intro (line a b d s m) (hacl_line a b d s m) *)

let hacl_quarter_round a b c d : Tot shuffle =
  let open Lib.IntTypes in
  hacl_line a b d (size 16) @
  hacl_line c d b (size 12) @
  hacl_line a b d (size 8)  @
  hacl_line c d b (size 7)

let quarter_round_lemma a b c d st :
  Lemma ((a <> d /\ c <> b) ==> quarter_round a b c d st == hacl_quarter_round a b c d st) =
  ()
(*  Lib.Sequence.eq_intro (quarter_round a b c d st) (hacl_quarter_round a b c d st) *)
(* End of equiv proof demo *)


let double_round (state_1888 : state) : state =
  let state_1889 =
    quarter_round (usize 0x0) (usize 0x4) (usize 0x8) (usize 0xc) (
      state_1888)
  in
  let state_1890 =
    quarter_round (usize 0x1) (usize 0x5) (usize 0x9) (usize 0xd) (
      state_1889)
  in
  let state_1891 =
    quarter_round (usize 0x2) (usize 0x6) (usize 0xa) (usize 0xe) (
      state_1890)
  in
  let state_1892 =
    quarter_round (usize 0x3) (usize 0x7) (usize 0xb) (usize 0xf) (
      state_1891)
  in
  let state_1893 =
    quarter_round (usize 0x0) (usize 0x5) (usize 0xa) (usize 0xf) (
      state_1892)
  in
  let state_1894 =
    quarter_round (usize 0x1) (usize 0x6) (usize 0xb) (usize 0xc) (
      state_1893)
  in
  let state_1895 =
    quarter_round (usize 0x2) (usize 0x7) (usize 0x8) (usize 0xd) (
      state_1894)
  in
  quarter_round (usize 0x3) (usize 0x4) (usize 0x9) (usize 0xe) (
    state_1895)

let block_init (key_1896 : key) (ctr_1897 : uint32) (iv_1898 : iv) : state =
  let l = [
    secret (pub_u32 0x61707865);
    secret (pub_u32 0x3320646e);
    secret (pub_u32 0x79622d32);
    secret (pub_u32 0x6b206574);
    uint32_from_le_bytes (
      seq_from_slice_range 4 (key_1896) ((usize 0, usize 4)));
    uint32_from_le_bytes (
      seq_from_slice_range 4 (key_1896) ((usize 4, usize 8)));
    uint32_from_le_bytes (
      seq_from_slice_range 4 (key_1896) ((usize 8, usize 12)));
    uint32_from_le_bytes (
      seq_from_slice_range 4 (key_1896) ((usize 12, usize 16)));
    uint32_from_le_bytes (
      seq_from_slice_range 4 (key_1896) ((usize 16, usize 20)));
    uint32_from_le_bytes (
      seq_from_slice_range 4 (key_1896) ((usize 20, usize 24)));
    uint32_from_le_bytes (
      seq_from_slice_range 4 (key_1896) ((usize 24, usize 28)));
    uint32_from_le_bytes (
      seq_from_slice_range 4 (key_1896) ((usize 28, usize 32)));
    ctr_1897;
    uint32_from_le_bytes (
      seq_from_slice_range 4 (iv_1898) ((usize 0, usize 4)));
    uint32_from_le_bytes (
      seq_from_slice_range 4 (iv_1898) ((usize 4, usize 8)));
    uint32_from_le_bytes (
      seq_from_slice_range 4 (iv_1898) ((usize 8, usize 12)))
  ] in
  assert_norm (List.Tot.length l == 16);
  seq_from_list l

let block_inner (key_1899 : key) (ctr_1900 : uint32) (iv_1901 : iv) : state =
  let st_1902 = block_init (key_1899) (ctr_1900) (iv_1901) in
  let state_1903 = st_1902 in
  let (state_1903) =
    foldi (usize 0) (usize 10) (fun (i_1904, (state_1903)) ->
      let state_1903 = double_round (state_1903) in
      (state_1903))
    (state_1903)
  in
  let (state_1903) =
    foldi (usize 0) (usize 16) (fun (i_1905, (state_1903)) ->
      let state_1903 =
        array_upd state_1903 (i_1905) (
          (array_index (state_1903) (i_1905)) +. (
            array_index (st_1902) (i_1905)))
      in
      (state_1903))
    (state_1903)
  in
  state_1903

let block (key_1906 : key) (ctr_1907 : uint32) (iv_1908 : iv) : state_bytes =
  let state_1909 = block_inner (key_1906) (ctr_1907) (iv_1908) in
  state_to_bytes (state_1909)

(* TODO: working on below *)
let chacha (key_1910 : key) (iv_1911 : iv) (m_1912 : byte_seq{seq_len m_1912 <= max_size_t}) : byte_seq =
  let ctr_1913 = secret (pub_u32 0x1) in
  let blocks_out_1914 = seq_new_ (seq_len (m_1912)) (u8 0) in
  let (blocks_out_1914, ctr_1913) =
    foldi (usize 0) (seq_num_chunks (m_1912) (usize 64)) (fun (
        i_1915,
        (blocks_out_1914, ctr_1913)
      ) ->
      let (block_len_1916, msg_block_1917) =
        seq_get_chunk (m_1912) (usize 64) (i_1915)
      in
      let key_block_1918 = block (key_1910) (ctr_1913) (iv_1911) in
      let msg_block_padded_1919 = seq_new_ 64 (u8 0) in
      let msg_block_padded_1920 =
        seq_update_start (msg_block_padded_1919) (msg_block_1917)
      in
      let blocks_out_1914 =
        seq_set_chunk #uint8 (blocks_out_1914) (usize 64) (i_1915) (
          seq_slice_range ((msg_block_padded_1920) `seq_xor` (key_block_1918)) (
            (usize 0, block_len_1916)))
      in
      let ctr_1913 = (ctr_1913) +. (secret (pub_u32 0x1)) in
      (blocks_out_1914, ctr_1913))
    (blocks_out_1914, ctr_1913)
  in
  blocks_out_1914

