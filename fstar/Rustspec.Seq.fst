module Rustspec.Seq

open Rustspec.Int

type lseq (a: Type) (len: usize) = FStar.Seq.lseq a (UInt32.v len)

assume val new_ (#a: Type) (len: usize) (_: unit) : lseq a len

assume val array_index (#a: Type) (#len: usize) (s: lseq a len) (i: usize{UInt32.v i < UInt32.v len}) : a

assume val array_upd (#a: Type) (#len: usize) (s: lseq a len) (i: usize{UInt32.v i < UInt32.v len})
 (new_v: a) : lseq a len

let len (#a: Type) (#len: usize) (s: lseq a len) = len
