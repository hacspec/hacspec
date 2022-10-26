module Option

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

let foo (x_0 : (option (option uint32))) : uint32 =
  let y_1 : (option uint32) =
    None
  in
  let z_2 : (option (option uint32)) =
    Some (y_1)
  in
  begin match x_0 with
  | None -> secret (pub_u32 0x0)
  | Some x_3 -> option_unwrap (x_3) end

