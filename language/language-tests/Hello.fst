module Hello

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

noeq type foo_t =
| CaseX_foo_t : foo_t
| CaseY_foo_t : (uint8 & seq pub_uint32) -> foo_t

noeq type bar_t =
| Bar_bar_t : pub_uint32 -> bar_t

let baz (x_0 : foo_t) : bar_t =
  let z_1 : bar_t =
    Bar_bar_t (pub_u32 0x0)
  in
  let Bar_bar_t (z_2) : bar_t =
    z_1
  in
  let y_3 : foo_t =
    begin match x_0 with
    | CaseX_foo_t -> CaseY_foo_t (
      (secret (cast U8 PUB (z_2)), seq_new_ (pub_u32 0x0) (usize 1)))
    | CaseY_foo_t (a_4, b_5) -> CaseY_foo_t (
      ((a_4) +. (secret (pub_u8 0x1)), b_5)) end
  in
  begin match y_3 with
  | CaseX_foo_t -> Bar_bar_t (pub_u32 0x0)
  | CaseY_foo_t (a_6, b_7) -> Bar_bar_t (
    uint32_declassify (uint32_from_uint8 (a_6))) end

let baz_im (x_8 : foo_t) : unit =
  let z_9 : bar_t =
    Bar_bar_t (pub_u32 0x0)
  in
  let Bar_bar_t (z_10) : bar_t =
    z_9
  in
  let a_11 : pub_uint8 =
    cast U8 PUB (z_10)
  in
  ()

