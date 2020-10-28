require import List Int IntDiv CoreMap AllCore.
require import Array3 Array8 Array12 Array16 Array32 Array64.
require import WArray64.

from Jasmin require import JModel JMemory JArray.
require import Hacspec.


type state = uint32 Array16.t.

op state_idx i =
  nat_mod (16) i.

type state_bytes = uint8 Array64.t.

type iv = uint8 Array12.t.

type key = uint8 Array32.t.
