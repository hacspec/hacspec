module Copy

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

noeq type my_struct_t =
| MyStruct_my_struct_t : uint_size -> my_struct_t

let other (x_0 : my_struct_t) : my_struct_t =
  x_0

let first () : my_struct_t =
  let s_1 : my_struct_t =
    MyStruct_my_struct_t (usize 0)
  in
  let s_copy_2 : my_struct_t =
    other (s_1)
  in
  let MyStruct_my_struct_t (s_copy2_3) : my_struct_t =
    s_1
  in
  other (s_1)

