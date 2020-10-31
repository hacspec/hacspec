require import List Int IntDiv CoreMap AllCore.
require import Array3 Array4 Array8 Array12 Array16 Array32 Array64.
require import WArray64.

from Jasmin require import JModel JMemory JArray.
require import Hacspec.


type state = uint32 Array16.t.

op state_idx i =
  nat_mod (16) i.

type state_bytes = uint8 Array64.t.

type iv = uint8 Array12.t.

type key = uint8 Array32.t.

op state_to_bytes (x_0 : state) : state_bytes =
  let r_1 = array_64_new_ (secret (pub_u8 8)) in
  let r_1 =
    foldi (0) (array_16_len (x_0)) (fun i_2 (r_1 : 
      (* *) uint8 Array64.t
    ) =>
      let bytes_3 = uint32_to_be_bytes (x_0.[i_2]) in
      let r_1 = r_1.[((i_2) * (4)) <- (bytes_3.[3])] in
      let r_1 = r_1.[(((i_2) * (4)) + (1)) <- (bytes_3.[2])] in
      let r_1 = r_1.[(((i_2) * (4)) + (2)) <- (bytes_3.[1])] in
      let r_1 = r_1.[(((i_2) * (4)) + (3)) <- (bytes_3.[0])] in
      r_1)
    r_1
  in
  r_1.
