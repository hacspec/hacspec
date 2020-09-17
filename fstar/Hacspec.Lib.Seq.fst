module Hacspec.Lib.Seq

module LSeq = Lib.Sequence

open Hacspec.Lib.Int

type lseq (a: Type) (len: uint_size) = LSeq.lseq a len

type seq (a: Type)  = LSeq.seq a

type byte_seq = seq uint8

(**** Array manipulation *)

assume val new_ (#a: Type) (len: uint_size) (_: unit) : lseq a len

assume val array_index (#a: Type) (s: seq a) (i: uint_size{i < LSeq.length s}) : a

assume val array_upd (#a: Type) (#len: uint_size) (s: lseq a len) (i: uint_size{i < len})
 (new_v: a) : lseq a len

assume val from_slice (#a: Type) (out_len: uint_size) (input: seq a) (start: uint_size) (slice_len: uint_size{slice_len <= out_len}) : lseq a out_len

assume val from_slice_range
  (#a: Type)
  (out_len: uint_size)
  (input: seq a)
  (start_end: (uint_size & uint_size))
    : lseq a out_len


let len (#a: Type) (s: seq a) = LSeq.length s

(**** Chunking *)

assume val num_chunks (#a: Type) (s: seq a) (chunk_len: uint_size) : uint_size

assume val get_chunk (#a: Type) (s: seq a) (chunk_len: uint_size) (chunk_num: uint_size)
  : Pure (uint_size & seq a)
    (requires (True))
    (ensures (fun (real_len, out) -> len out == real_len))

(**** Integers to arrays *)

assume val uint128_from_le_bytes (input: lseq uint8 (usize 16)) : uint128
