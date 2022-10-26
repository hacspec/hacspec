module Submod1

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Another.Submod1.File

noeq type my_tuple_type_t =
| MyTupleType_my_tuple_type_t : (pub_uint16 & pub_uint8) -> my_tuple_type_t

