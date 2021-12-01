module QuestionMark

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

let foo (x_0 : bool) : (result pub_uint64 uint8) =
  if (x_0) then (Ok (pub_u64 0x2a)) else (Err (secret (pub_u8 0x0)))

let bar () : (result pub_uint64 uint8) =
  match (foo (false)) with
  | Err x -> Err x
  | Ok  x_1 : pub_uint64 ->
    Ok ((x_1) +. (pub_u64 0x1))

let fizzbaz () : (result pub_uint64 uint8) =
  match (foo (false)) with
  | Err x -> Err x
  | Ok  x_2 : pub_uint64 ->
    match (foo (true)) with
    | Err x -> Err x
    | Ok  y_3 : pub_uint64 ->
      Ok ((x_2) +. (y_3))

let fizzbazbaz () : (result pub_uint64 uint8) =
  match (foo (false)) with
  | Err x -> Err x
  | Ok  x_4 : pub_uint64 ->
    match (foo (true)) with
    | Err x -> Err x
    | Ok  y_5 : pub_uint64 ->
      let x_4 =
        (x_4) +. (y_5)
      in
      match (foo (false)) with | Err x -> Err x | Ok  y_5 -> Ok ((x_4) +. (y_5))

let fizzbazbazbar (s_6 : seq pub_uint64) : (result pub_uint64 uint8) =
  match (foo (false)) with
  | Err x -> Err x
  | Ok  y_7 : pub_uint64 ->
    match (foo (true)) with
    | Err x -> Err x
    | Ok  tmp_9 ->
      let s_6 =
        seq_upd s_6 (usize 0) tmp_9
      in
      Ok ((seq_index (s_6) (usize 0)) +. (y_7))

let baz () : (result pub_uint32 uint8) =
  match (foo (false)) with
  | Err x -> Err x
  | Ok  x_10 : pub_uint64 ->
    let out_11 : pub_uint32 =
      pub_u32 0x0
    in
    match (
      if (true) || (false) then begin
        match (foo (true)) with
        | Err x -> Err x
        | Ok  y_12 : pub_uint64 ->
          match (foo ((false) || (true))) with
          | Err x -> Err x
          | Ok  _ : pub_uint64 ->
            Ok ((out_11))
      end else begin
        match (foo ((false) && (true))) with
        | Err x -> Err x
        | Ok  _ : pub_uint64 ->
          let out_11 =
            (cast U32 PUB (x_10)) +. (pub_u32 0x1)
          in
          Ok ((out_11))
      end) with
    | Err x -> Err x
    | Ok  (out_11) ->
      Ok (out_11)

let fizzbar () : (result pub_uint32 uint8) =
  match (foo (false)) with
  | Err x -> Err x
  | Ok  x_13 : pub_uint64 ->
    let out_14 : pub_uint32 =
      pub_u32 0x0
    in
    match (
      foldi_result (usize 0) (usize 200) (fun i_15 (out_14) ->
        match (foo (true)) with
        | Err x -> Err x
        | Ok  y_16 : pub_uint64 ->
          let out_14 =
            ((pub_u32 (i_15)) +. (cast U32 PUB (y_16))) +. (out_14)
          in
          Ok ((out_14)))
      (out_14)) with
    | Err x -> Err x
    | Ok  (out_14) ->
      Ok (out_14)

let fizzbarbuzz () : (result pub_uint32 uint8) =
  match (foo (false)) with
  | Err x -> Err x
  | Ok  x_17 : pub_uint64 ->
    let out_18 : pub_uint32 =
      pub_u32 0x0
    in
    match (
      foldi_result (usize 0) (usize 200) (fun i_19 (out_18) ->
        match (
          if (true) || (false) then begin
            match (foo (true)) with
            | Err x -> Err x
            | Ok  y_20 : pub_uint64 ->
              let out_18 =
                (cast U32 PUB (y_20)) +. (out_18)
              in
              match (foo ((false) || (true))) with
              | Err x -> Err x
              | Ok  _ : pub_uint64 ->
                Ok ((out_18))
          end else begin
            match (foo ((false) && (true))) with
            | Err x -> Err x
            | Ok  _ : pub_uint64 ->
              let out_18 =
                (cast U32 PUB (x_17)) +. (pub_u32 (i_19))
              in
              Ok ((out_18))
          end) with
        | Err x -> Err x
        | Ok  (out_18) ->
          Ok ((out_18)))
      (out_18)) with
    | Err x -> Err x
    | Ok  (out_18) ->
      Ok (out_18)

