require import List Int IntDiv CoreMap AllCore.
require import Array3 Array4 Array8 Array16 Array32 Array64.
require import WArray64.

from Jasmin require import JModel JMemory JArray.

type uint8 = W8.t.
type uint32 = W32.t.

op nat_mod i n = 0 <= i < n.

op secret (x : 'a) : 'a = x.

op pub_u8 x = W8.of_int x.

op array_16_size (x: 'a Array16.t) : int = 16.

op uint32_to_be_bytes (x: uint32) : uint8 Array4.t.

op foldi (low: int) (hi: int) (f: int -> 'a -> 'a) (init: 'a) : 'a.

op array_64_new_ (init: 'a) : 'a Array64.t.

op array_16_len (x: 'a Array16.t) : int = 16.