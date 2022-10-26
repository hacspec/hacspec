module Loops

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

type my_integer_type_t = uint_size

let foo (x_0 : my_integer_type_t) : uint_size =
  let (x_0) =
    foldi (usize 0) (x_0) (fun i_1 (x_0) ->
      let x_0 =
        i_1
      in
      (x_0))
    (x_0)
  in
  x_0

type my_uint32_integer_type_t = pub_uint32

let baz (x_2 : my_uint32_integer_type_t) : my_uint32_integer_type_t =
  let (x_2) =
    foldi (usize 0) (v (cast U32 PUB (x_2))) (fun i_3 (x_2) ->
      let x_2 =
        pub_u32 (i_3)
      in
      (x_2))
    (x_2)
  in
  x_2

let bar (x_4 : uint32) : uint32 =
  let y_5 : uint32 =
    x_4
  in
  let (y_5) =
    foldi (usize 0) (usize 5) (fun _ (y_5) ->
      let y_5 =
        (y_5) +. (secret (pub_u32 0x1))
      in
      (y_5))
    (y_5)
  in
  y_5

let foobar (x_6 : pub_uint32) : (result pub_uint32 pub_uint32) =
  let y_7 : pub_uint32 =
    x_6
  in
  begin match (
    foldi_result (usize 0) (usize 5) (fun _ (y_7) ->
      begin match (
        if (y_7) >. (pub_u32 0x64) then begin
          begin match (Err (y_7)) with
          | Err x -> Err x
          | Ok  (_ : pub_uint32) ->
            Ok (()) end
        end else begin Ok (())
        end) with
      | Err x -> Err x
      | Ok  (()) ->
        let y_7 =
          (y_7) +. (pub_u32 0x1)
        in
        Ok ((y_7)) end)
    (y_7)) with
  | Err x -> Err x
  | Ok  ((y_7)) ->
    Ok (y_7) end

