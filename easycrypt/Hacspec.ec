require import List Int IntDiv CoreMap AllCore.
require import Array3 Array4 Array8 Array16 Array32 Array64.
require import WArray64.

from Jasmin require import JModel JMemory JArray.

type uint8 = W8.t.
type uint32 = W32.t.
type uint_size = int.

clone export PolyArray as Sequence.

op seq_new_ (init: 'a) (size: int) : 'a Sequence.t.

op nat_mod i n = 0 <= i < n.

op secret (x : 'a) : 'a = x.

op pub_u8 x = W8.of_int x.
op pub_u32 x = W32.of_int x.

op array_16_size (x: 'a Array16.t) : int = 16.

op uint32_to_be_bytes (x: uint32) : uint8 Array4.t.

op uint32_rotate_left (x: uint32) (rotval: int) : uint32.

op foldi (low: int) (hi: int) (f: int -> 'a -> 'a) (init: 'a) : 'a.

op array_64_new_ (init: 'a) : 'a Array64.t.

op array_16_len (x: 'a Array16.t) : int = 16.