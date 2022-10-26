module Submod2

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

let error_value_v : pub_uint8 =
  pub_u8 0x0

type res_t = (uint_size & uint_size)

