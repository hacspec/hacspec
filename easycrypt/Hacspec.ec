require import List Int IntDiv CoreMap AllCore.
require import Array3 Array4 Array8 Array16 Array32 Array64.
require import WArray64.

from Jasmin require import JModel JMemory JArray.

type uint8 = W8.t.
type uint32 = W32.t.
type uint_size = int.

clone export PolyArray as Sequence.

op seq_new_ (init: 'a) (size: int) : 'a Sequence.t.

op seq_len (x: 'a Sequence.t) : int.

op seq_num_chunks (x: 'a Sequence.t) (chunk_size: int) : int.

op seq_get_chunk (x: 'a Sequence.t) (chunk_size: int) (chunk_num: int) : int * 'a Sequence.t.

op seq_set_chunk (x: 'a Sequence.t) (chunk_size: int) (chunk_num: int) (chunk: 'a Sequence.t) : 'a Sequence.t.


op nat_mod i n = 0 <= i < n.

op secret (x : 'a) : 'a = x.

op pub_u8 x = W8.of_int x.
op pub_u32 x = W32.of_int x.

op array_16_size (x: 'a Array16.t) : int = 16.

op array_16_from_seq (size: int) (x: 'a Sequence.t) : 'a Array16.t.

op array_64_update_start (s: 'a Array64.t) (x: 'a Sequence.t) : 'a Array64.t.

op uint32_to_be_bytes (x: uint32) : uint8 Array4.t.

op uint32_from_le_bytes (x: uint8 Array4.t) : uint32.

op uint32_rotate_left (x: uint32) (rotval: int) : uint32.

op foldi (low: int) (hi: int) (f: int -> 'a -> 'a) (init: 'a) : 'a.

op array_64_new_ (init: 'a) : 'a Array64.t.

op array_16_len (x: 'a Array16.t) : int = 16.

op array_4_from_slice_range (x: 'a Sequence.t) (start_end : int * int) : 'a Array4.t.

op seq_concat (x: 'a Sequence.t) (y: 'a Sequence.t) : 'a Sequence.t.

type byte_seq = uint8 Sequence.t.

op array_64_xor (xor: 'a -> 'a -> 'a) (x: 'a Array64.t) (y: 'a Array64.t) : 'a Array64.t.

op array_64_slice_range (x: 'a Array64.t) (start_end: int * int) : 'a Sequence.t.