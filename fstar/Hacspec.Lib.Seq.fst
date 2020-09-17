module Hacspec.Lib.Seq

module LSeq = Lib.Sequence

open Hacspec.Lib.Int

type lseq (a: Type) (len: uint_size) = LSeq.lseq a len

type byte_seq (len: uint_size) = lseq uint8 len

(**** Array manipulation *)

assume val new_ (#a: Type) (len: uint_size) (_: unit) : lseq a len

assume val array_index (#a: Type) (#len: uint_size) (s: lseq a len) (i: uint_size{i < len}) : a

assume val array_upd (#a: Type) (#len: uint_size) (s: lseq a len) (i: uint_size{i < len})
 (new_v: a) : lseq a len

assume val from_slice (#a: Type) (#len: uint_size) (input: lseq a len) (start: uint_size) (new_len: uint_size) : lseq a new_len

let len (#a: Type) (#len: uint_size) (s: lseq a len) = len

(**** Integers to arrays *)

assume val uint128_from_le_bytes (input: lseq uint8 (usize 16)) : uint128
