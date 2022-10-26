module Question.Mark

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

let foo_option (x_0 : bool) : (option pub_uint64) =
  if (x_0) then (Some (pub_u64 0x2a)) else (None)

let bar_option () : (option pub_uint64) =
  begin match (foo_option (false)) with
  | Err x -> Err x
  | Ok  (x_1 : pub_uint64) ->
    Some ((x_1) +. (pub_u64 0x1)) end

let foo (x_2 : bool) : (result pub_uint64 uint8) =
  if (x_2) then (Ok (pub_u64 0x2a)) else (Err (secret (pub_u8 0x0)))

let bar () : (result pub_uint64 uint8) =
  begin match (foo (false)) with
  | Err x -> Err x
  | Ok  (x_3 : pub_uint64) ->
    Ok ((x_3) +. (pub_u64 0x1)) end

let fizzbaz () : (result pub_uint64 uint8) =
  begin match (foo (false)) with
  | Err x -> Err x
  | Ok  (x_4 : pub_uint64) ->
    begin match (foo (true)) with
    | Err x -> Err x
    | Ok  (y_5 : pub_uint64) ->
      Ok ((x_4) +. (y_5)) end end

let fizzbazbaz () : (result pub_uint64 uint8) =
  begin match (foo (false)) with
  | Err x -> Err x
  | Ok  (x_6 : pub_uint64) ->
    begin match (foo (true)) with
    | Err x -> Err x
    | Ok  (y_7 : pub_uint64) ->
      let x_6 =
        (x_6) +. (y_7)
      in
      begin match (foo (false)) with
      | Err x -> Err x
      | Ok  (y_7) ->
        Ok ((x_6) +. (y_7)) end end end

let fizzbazbazbar (s_8 : seq pub_uint64) : (result pub_uint64 uint8) =
  begin match (foo (false)) with
  | Err x -> Err x
  | Ok  (y_9 : pub_uint64) ->
    begin match (foo (true)) with
    | Err x -> Err x
    | Ok  (tmp_11) ->
      let s_8 =
        seq_upd s_8 (usize 0) tmp_11
      in
      Ok ((seq_index (s_8) (usize 0)) +. (y_9)) end end

let baz () : (result pub_uint32 uint8) =
  begin match (foo (false)) with
  | Err x -> Err x
  | Ok  (x_12 : pub_uint64) ->
    let out_13 : pub_uint32 =
      pub_u32 0x0
    in
    begin match (
      if (true) || (false) then begin
        begin match (foo (true)) with
        | Err x -> Err x
        | Ok  (y_14 : pub_uint64) ->
          begin match (foo ((false) || (true))) with
          | Err x -> Err x
          | Ok  (_ : pub_uint64) ->
            Ok ((out_13)) end end
      end else begin
        begin match (foo ((false) && (true))) with
        | Err x -> Err x
        | Ok  (_ : pub_uint64) ->
          let out_13 =
            (cast U32 PUB (x_12)) +. (pub_u32 0x1)
          in
          Ok ((out_13)) end
      end) with
    | Err x -> Err x
    | Ok  ((out_13)) ->
      Ok (out_13) end end

let fizzbar () : (result pub_uint32 uint8) =
  begin match (foo (false)) with
  | Err x -> Err x
  | Ok  (x_15 : pub_uint64) ->
    let out_16 : pub_uint32 =
      pub_u32 0x0
    in
    begin match (
      foldi_result (usize 0) (usize 200) (fun i_17 (out_16) ->
        begin match (foo (true)) with
        | Err x -> Err x
        | Ok  (y_18 : pub_uint64) ->
          let out_16 =
            ((pub_u32 (i_17)) +. (cast U32 PUB (y_18))) +. (out_16)
          in
          Ok ((out_16)) end)
      (out_16)) with
    | Err x -> Err x
    | Ok  ((out_16)) ->
      Ok (out_16) end end

let fizzbarbuzz () : (result pub_uint32 uint8) =
  begin match (foo (false)) with
  | Err x -> Err x
  | Ok  (x_19 : pub_uint64) ->
    let out_20 : pub_uint32 =
      pub_u32 0x0
    in
    begin match (
      foldi_result (usize 0) (usize 200) (fun i_21 (out_20) ->
        begin match (
          if (true) || (false) then begin
            begin match (foo (true)) with
            | Err x -> Err x
            | Ok  (y_22 : pub_uint64) ->
              let out_20 =
                (cast U32 PUB (y_22)) +. (out_20)
              in
              begin match (foo ((false) || (true))) with
              | Err x -> Err x
              | Ok  (_ : pub_uint64) ->
                Ok ((out_20)) end end
          end else begin
            begin match (foo ((false) && (true))) with
            | Err x -> Err x
            | Ok  (_ : pub_uint64) ->
              let out_20 =
                (cast U32 PUB (x_19)) +. (pub_u32 (i_21))
              in
              Ok ((out_20)) end
          end) with
        | Err x -> Err x
        | Ok  ((out_20)) ->
          Ok ((out_20)) end)
      (out_20)) with
    | Err x -> Err x
    | Ok  ((out_20)) ->
      Ok (out_20) end end

type alias_t = (result pub_uint32 uint8)

let alias_test () : alias_t =
  begin match (
    if true then begin
      begin match (Err (secret (pub_u8 0x0))) with
      | Err x -> Err x
      | Ok  (_ : pub_uint32) ->
        Ok (()) end
    end else begin Ok (())
    end) with
  | Err x -> Err x
  | Ok  (()) ->
    Ok (pub_u32 0x1) end

