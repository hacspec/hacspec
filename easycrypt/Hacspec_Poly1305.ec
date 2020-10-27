
require import List Int IntExtra IntDiv CoreMap Real.
from Jasmin require import JModel.
require import Zp.
import Zp.


type Zp_msg = zp list. 

op poly1305_loop (r : zp) (m : Zp_msg) (n : int) =
  foldl (fun h i => (h + oget (onth m i)) * r) Zp.zero (iota_ 0 n).

op poly1305_ref (r : zp) (s : int) (m : Zp_msg) =
  let n = size m in
  let h' = poly1305_loop r m n
      in  (((asint h') %% 2^128) + s) %% 2^128.
