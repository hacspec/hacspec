module Hacspec.Lib.Seq

module LSeq = Lib.Sequence

open Hacspec.Lib.Int

type lseq (a: Type) (len: uint_size) = LSeq.lseq a len

type seq (a: Type)  = LSeq.seq a

type byte_seq = seq uint8

(**** Array manipulation *)

assume val new_ (#a: Type) (len: uint_size) (_: unit) : lseq a len

assume val array_index (#a: Type) (#len: uint_size) (s: lseq a len) (i: uint_size{i < len}) : a

assume val array_upd (#a: Type) (#len: uint_size) (s: lseq a len) (i: uint_size{i < len})
 (new_v: a) : lseq a len

assume val from_slice (#a: Type) (input: seq a) (start: uint_size) (new_len: uint_size) : lseq a new_len

let len (#a: Type) (s: seq a) = LSeq.length s

(**** Integers to arrays *)

assume val uint128_from_le_bytes (input: lseq uint8 (usize 16)) : uint128
