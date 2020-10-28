require import List Int IntDiv CoreMap AllCore.
require import Array3 Array8 Array16.
require import WArray64.

from Jasmin require import JModel JMemory JArray.

type uint8 = W8.t.
type uint32 = W32.t.

op nat_mod i n = 0 <= i < n.
