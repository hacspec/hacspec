module Chacha20

open Rustspec

type state = Seq.lseq u32 16ul

type state_bytes = Seq.lseq u8 64ul

type iv = Seq.lseq u8 12ul

type key = Seq.lseq u8 32ul

let state_to_bytes (x : state) : state_bytes =
  let r = Seq.new () in
  let (r) =
    foldi (0ul) (len) (fun (i, (r)) ->
      let bytes = u32_to_be_bytes (array_index (x) (i)) in
      let r = array_upd r (i * 4ul) (array_index (bytes) (3ul)) in
      let r = array_upd r (i * 4ul + 1ul) (array_index (bytes) (2ul)) in
      let r = array_upd r (i * 4ul + 2ul) (array_index (bytes) (1ul)) in
      let r = array_upd r (i * 4ul + 3ul) (array_index (bytes) (0ul)) in
      (r))
    (r)
  in
  r

let line
  (a : UInt32.t)
  (b : UInt32.t)
  (d : UInt32.t)
  (s : UInt32.t)
  (m : state)
  : state =
  let state = m in
  let state =
    array_upd state (a) (array_index (state) (a) + array_index (state) (b))
  in
  let state =
    array_upd state (d) (array_index (state) (d) ^ array_index (state) (a))
  in
  let state = array_upd state (d) (rotate_left (s)) in
  state

let quarter_round
  (a : UInt32.t)
  (b : UInt32.t)
  (c : UInt32.t)
  (d : UInt32.t)
  (state : state)
  : state =
  let state = line (a) (b) (d) (16ul) (state) in
  let state = line (c) (d) (b) (12ul) (state) in
  let state = line (a) (b) (d) (8ul) (state) in
  line (c) (d) (b) (7ul) (state)

let double_round (state : state) : state =
  let state = quarter_round (0ul) (4ul) (8ul) (12ul) (state) in
  let state = quarter_round (1ul) (5ul) (9ul) (13ul) (state) in
  let state = quarter_round (2ul) (6ul) (10ul) (14ul) (state) in
  let state = quarter_round (3ul) (7ul) (11ul) (15ul) (state) in
  let state = quarter_round (0ul) (5ul) (10ul) (15ul) (state) in
  let state = quarter_round (1ul) (6ul) (11ul) (12ul) (state) in
  let state = quarter_round (2ul) (7ul) (8ul) (13ul) (state) in
  quarter_round (3ul) (4ul) (9ul) (14ul) (state)

let block_init (key : key) (ctr : u32) (iv : iv) : state =
  Seq.from_list [
    u32 (1634760805ul);
    u32 (857760878ul);
    u32 (2036477234ul);
    u32 (1797285236ul);
    u32_from_le_bytes (Seq.from_slice_range (key) ((0ul, 4ul)));
    u32_from_le_bytes (Seq.from_slice_range (key) ((4ul, 8ul)));
    u32_from_le_bytes (Seq.from_slice_range (key) ((8ul, 12ul)));
    u32_from_le_bytes (Seq.from_slice_range (key) ((12ul, 16ul)));
    u32_from_le_bytes (Seq.from_slice_range (key) ((16ul, 20ul)));
    u32_from_le_bytes (Seq.from_slice_range (key) ((20ul, 24ul)));
    u32_from_le_bytes (Seq.from_slice_range (key) ((24ul, 28ul)));
    u32_from_le_bytes (Seq.from_slice_range (key) ((28ul, 32ul)));
    ctr;
    u32_from_le_bytes (Seq.from_slice_range (iv) ((0ul, 4ul)));
    u32_from_le_bytes (Seq.from_slice_range (iv) ((4ul, 8ul)));
    u32_from_le_bytes (Seq.from_slice_range (iv) ((8ul, 12ul)))
  ]

let block_inner (key : key) (ctr : u32) (iv : iv) : state =
  let st = block_init (key) (ctr) (iv) in
  let state = st in
  let (state) =
    foldi (0ul) (10ul) (fun (i, (state)) ->
      let state = double_round (state) in
      (state))
    (state)
  in
  let (state) =
    foldi (0ul) (16ul) (fun (i, (state)) ->
      let state =
        array_upd state (i) (array_index (state) (i) + array_index (st) (i))
      in
      (state))
    (state)
  in
  state

let block (key : key) (ctr : u32) (iv : iv) : state_bytes =
  let state = block_inner (key) (ctr) (iv) in
  state_to_bytes (state)

let chacha (key : key) (iv : iv) (m : byte_seq) : byte_seq =
  let ctr = u32 (1ul) in
  let blocks_out = Seq.new (len) in
  let (blocks_out, ctr) =
    foldi (0ul) (num_chunks (64ul)) (fun (i, (blocks_out, ctr)) ->
      let (block_len, msg_block) = get_chunk (64ul) (i) in
      let key_block = block (key) (ctr) (iv) in
      let msg_block_padded = Seq.new () in
      let msg_block_padded = update_start (msg_block) in
      let blocks_out = set_chunk (64ul) (i) (slice_range ((0ul, block_len))) in
      let ctr = ctr + u32 (1ul) in
      (blocks_out, ctr))
    (blocks_out, ctr)
  in
  blocks_out

