module Poly1305

module R = Rustspec

let blocksize : UInt32.t =
  16ul

type block = Seq.lseq u8 blocksize

type tag = Seq.lseq UInt8.t blocksize

type field_canvas = Seq.lseq UInt8.t 272ul



let key_gen (key : key) (iv : iv) : key =
  let block = block (key) (u32 (0ul)) (iv) in
  Seq.from_slice_range (block) ((0ul, 32ul))

let encode_r (r : block) : field_element =
  let r_128 = Seq.from_slice (r) (0ul) (blocksize) in
  let r_uint = u128_from_le_bytes (r_128) in
  let r_uint =
    r_uint & u128 (UInt128.uint_to_t 21267647620597763993911028882763415551)
  in
  Seq.from_secret_literal (r_uint)

let encode (block : byte_seq) : field_element =
  let block_len = len in
  let block_as_u128 = Seq.from_slice (block) (0ul) (min (16ul) (block_len)) in
  let w_elem = Seq.from_secret_literal (u128_from_le_bytes (block_as_u128)) in
  let l_elem = Seq.from_canvas (Seq.pow2 (8ul * block_len)) in
  w_elem + l_elem

let poly_inner (m : byte_seq) (r : field_element) : field_element =
  let acc = Seq.from_literal (UInt128.uint_to_t 0) in
  let (acc) =
    foldi (0ul) (num_chunks (blocksize)) (fun (i, (acc)) ->
      let (_, block) = get_chunk (blocksize) (i) in
      let acc = acc + encode (block) * r in
      (acc))
    (acc)
  in
  acc

let poly (m : byte_seq) (key : key) : tag =
  let s_elem =
    Seq.from_secret_literal (
      u128_from_le_bytes (Seq.from_slice (key) (blocksize) (blocksize)))
  in
  let r_elem = encode_r (Seq.from_slice_range (key) ((0ul, blocksize))) in
  let a = poly_inner (m) (r_elem) in
  let n = a + s_elem in
  let n_v = to_public_byte_seq_le in
  let tag = Seq.new () in
  let (tag) =
    foldi (0ul) (min (len) (len)) (fun (i, (tag)) ->
      let tag = array_upd tag (i) (array_index (n_v) (i)) in
      (tag))
    (tag)
  in
  tag

let poly_mac (m : byte_seq) (key : key) (iv : iv) : tag =
  let mac_key = key_gen (key) (iv) in
  poly (m) (mac_key)

