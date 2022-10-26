module Question.Mark

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

let foo (x_0 : bool) : (result pub_uint64 uint8) =
  if (x_0) then (Ok (pub_u64 0x2a)) else (Err (secret (pub_u8 0x0)))

let bar () : (result pub_uint64 uint8) =
  begin match (foo (false)) with
  | Err x -> Err x
  | Ok  (x_1 : pub_uint64) ->
    Ok ((x_1) +. (pub_u64 0x1)) end

let fizzbaz () : (result pub_uint64 uint8) =
  begin match (foo (false)) with
  | Err x -> Err x
  | Ok  (x_2 : pub_uint64) ->
    begin match (foo (true)) with
    | Err x -> Err x
    | Ok  (y_3 : pub_uint64) ->
      Ok ((x_2) +. (y_3)) end end

let fizzbazbaz () : (result pub_uint64 uint8) =
  begin match (foo (false)) with
  | Err x -> Err x
  | Ok  (x_4 : pub_uint64) ->
    begin match (foo (true)) with
    | Err x -> Err x
    | Ok  (y_5 : pub_uint64) ->
      let x_4 =
        (x_4) +. (y_5)
      in
      begin match (foo (false)) with
      | Err x -> Err x
      | Ok  (y_5) ->
        Ok ((x_4) +. (y_5)) end end end

let fizzbazbazbar (s_6 : seq pub_uint64) : (result pub_uint64 uint8) =
  begin match (foo (false)) with
  | Err x -> Err x
  | Ok  (y_7 : pub_uint64) ->
    begin match (foo (true)) with
    | Err x -> Err x
    | Ok  (tmp_9) ->
      let s_6 =
        seq_upd s_6 (usize 0) tmp_9
      in
      Ok ((seq_index (s_6) (usize 0)) +. (y_7)) end end

let baz () : (result pub_uint32 uint8) =
  begin match (foo (false)) with
  | Err x -> Err x
  | Ok  (x_10 : pub_uint64) ->
    let out_11 : pub_uint32 =
      pub_u32 0x0
    in
    begin match (
      if (true) || (false) then begin
        begin match (foo (true)) with
        | Err x -> Err x
        | Ok  (y_12 : pub_uint64) ->
          begin match (foo ((false) || (true))) with
          | Err x -> Err x
          | Ok  (_ : pub_uint64) ->
            Ok ((out_11)) end end
      end else begin
        begin match (foo ((false) && (true))) with
        | Err x -> Err x
        | Ok  (_ : pub_uint64) ->
          let out_11 =
            (cast U32 PUB (x_10)) +. (pub_u32 0x1)
          in
          Ok ((out_11)) end
      end) with
    | Err x -> Err x
    | Ok  ((out_11)) ->
      Ok (out_11) end end

let fizzbar () : (result pub_uint32 uint8) =
  begin match (foo (false)) with
  | Err x -> Err x
  | Ok  (x_13 : pub_uint64) ->
    let out_14 : pub_uint32 =
      pub_u32 0x0
    in
    begin match (
      foldi_result (usize 0) (usize 200) (fun i_15 (out_14) ->
        begin match (foo (true)) with
        | Err x -> Err x
        | Ok  (y_16 : pub_uint64) ->
          let out_14 =
            ((pub_u32 (i_15)) +. (cast U32 PUB (y_16))) +. (out_14)
          in
          Ok ((out_14)) end)
      (out_14)) with
    | Err x -> Err x
    | Ok  ((out_14)) ->
      Ok (out_14) end end

let fizzbarbuzz () : (result pub_uint32 uint8) =
  begin match (foo (false)) with
  | Err x -> Err x
  | Ok  (x_17 : pub_uint64) ->
    let out_18 : pub_uint32 =
      pub_u32 0x0
    in
    begin match (
      foldi_result (usize 0) (usize 200) (fun i_19 (out_18) ->
        begin match (
          if (true) || (false) then begin
            begin match (foo (true)) with
            | Err x -> Err x
            | Ok  (y_20 : pub_uint64) ->
              begin match (
                let? mvar_21 = Ok (true) in 
                let? mvar_22 = foo (mvar_21) in 
                let? mvar_23 = Ok (pub_u32 0x3) in Ok (
                  (
                    ((cast U32 PUB (y_20)) +. (cast U32 PUB (mvar_22))) +. (
                      out_18)) +. (mvar_23))) with
              | Err x -> Err x
              | Ok  (out_18) ->
                begin match (foo ((false) || (true))) with
                | Err x -> Err x
                | Ok  (_ : pub_uint64) ->
                  Ok ((out_18)) end end end
          end else begin
            begin match (foo ((false) && (true))) with
            | Err x -> Err x
            | Ok  (_ : pub_uint64) ->
              let out_18 =
                (cast U32 PUB (x_17)) +. (pub_u32 (i_19))
              in
              Ok ((out_18)) end
          end) with
        | Err x -> Err x
        | Ok  ((out_18)) ->
          Ok ((out_18)) end)
      (out_18)) with
    | Err x -> Err x
    | Ok  ((out_18)) ->
      Ok (out_18) end end

let inline_question_marks () : (result pub_uint64 uint8) =
  let a_24 : (result pub_uint64 uint8) =
    Ok (pub_u64 0x64)
  in
  let b_25 : (result pub_uint64 uint8) =
    Ok (pub_u64 0x32)
  in
  let c_26 : (result (result pub_uint64 uint8) uint8) =
    Ok (Ok (pub_u64 0x64))
  in
  begin match (
    let? mvar_28 = c_26 in let? mvar_29 = begin match mvar_28 with
    | Ok x_30 -> let? mvar_31 = a_24 in if ((mvar_31) >. (pub_u64 0xa)) then (
      Ok (pub_u64 0x7b)) else (
      let? mvar_32 = b_25 in Ok ((mvar_32) +. (pub_u64 0x3)))
    | Err x_33 -> let? mvar_9 = b_25 in 
    let? mvar_34 = a_24 in Ok (
      ((mvar_9) +. (pub_u64 0x1)) +. (mvar_34)) end in Ok (mvar_29)) with
  | Err x -> Err x
  | Ok  (x_27 : pub_uint64) ->
    Ok (x_27) end

