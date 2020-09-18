module Hacspec.Lib

(*** Integers *)

include Lib.IntTypes

(**** Usize  *)

let uint_size = range_t U32
let int_size = range_t S32

unfold
let usize (n:range_t U32) : u:uint_size{u == n} = n

unfold
let isize (n:range_t S32) : u:int_size{u == n} = n

(**** Public integers *)

unfold
let pub_u8 (n:range_t U8) : u:pub_uint8{v u == n} = uint #U8 #PUB n

unfold
let pub_i8 (n:range_t S8) : u:pub_int8{v u == n} = sint #S8 #PUB n

unfold
let pub_u16 (n:range_t U16) : u:pub_uint16{v u == n} = uint #U16 #PUB n

unfold
let pub_i16 (n:range_t S16) : u:pub_int16{v u == n} = sint #S16 #PUB n

unfold
let pub_u32 (n:range_t U32) : u:pub_uint32{v u == n} = uint #U32 #PUB n

unfold
let pub_i32 (n:range_t S32) : u:pub_int32{v u == n} = sint #S32 #PUB n

unfold
let pub_u64 (n:range_t U64) : u:pub_uint64{v u == n} = uint #U64 #PUB n

unfold
let pub_i64 (n:range_t S64) : u:pub_int64{v u == n} = sint #S64 #PUB n

unfold
let pub_u128 (n:range_t U128) : u:pub_uint128{v u == n} = uint #U128 #PUB n

unfold
let pub_i128 (n:range_t S128) : u:pub_int128{v u == n} = sint #S128 #PUB n

(**** Operations *)

assume val uint32_rotate_left (x: uint32) (rot_val: nat) : uint32

(*** Seq *)

module LSeq = Lib.Sequence

type lseq (a: Type) (len: uint_size) = LSeq.lseq a len

type seq (a: Type)  = LSeq.seq a

type byte_seq = seq uint8

assume val seq_from_list (#a: Type) (l: list a) : seq a

assume val uint32_to_be_bytes : uint32 -> lseq uint8 4
assume val uint32_from_le_bytes : lseq uint8 4 -> uint32


(**** Array manipulation *)

assume val seq_new_ (#a: Type) (len: uint_size) : lseq a len

assume val array_index (#a: Type) (s: seq a) (i: uint_size{i < LSeq.length s}) : a

assume val array_upd (#a: Type) (s: seq a) (i: uint_size) (new_v: a) : seq a

assume val seq_from_slice (#a: Type) (out_len: uint_size) (input: seq a) (start: uint_size) (slice_len: uint_size{slice_len <= out_len}) : lseq a out_len

assume val seq_from_slice_range
  (#a: Type)
  (out_len: uint_size)
  (input: seq a)
  (start_end: (uint_size & uint_size))
    : lseq a out_len

assume val seq_slice_range (#a: Type) (input: seq a) (start_end: (uint_size & uint_size)) : seq a

assume val seq_update_start (#a: Type) (s: seq a) (start_s: seq a) : seq a

let seq_len (#a: Type) (s: seq a) = LSeq.length s

(**** Chunking *)

assume val seq_num_chunks (#a: Type) (s: seq a) (chunk_len: uint_size) : uint_size

assume val seq_get_chunk (#a: Type) (s: seq a) (chunk_len: uint_size) (chunk_num: uint_size)
  : Pure (uint_size & seq a)
    (requires (True))
    (ensures (fun (real_len, out) -> seq_len out == real_len))

assume val seq_set_chunk
  (#a: Type)
  (s: seq a)
  (chunk_len: uint_size)
  (chunk_num: uint_size)
  (chunk: lseq a chunk_len)
    : Pure (seq a)
      (requires (True))
      (ensures (fun out -> seq_len out == seq_len s))

(**** Numeric operations *)

assume val seq_xor (#a: Type) (s1: seq a) (s2 : seq a) : seq a

(**** Integers to arrays *)

assume val uint128_from_le_bytes (input: lseq uint8 (usize 16)) : uint128

(*** Loops *)

assume val foldi (#acc: Type) (lo: uint_size) (hi: uint_size) (f: (uint_size & acc) -> acc) (init: acc) : acc


(*** Nats *)

let nat_mod (n: nat) = x:nat{x < n}

assume val nat_from_secret_literal (x:uint128) : n:nat{v x == n}

assume val nat_from_literal (x:pub_uint128) : n:nat{v x == n}

assume val nat_to_public_byte_seq_le (n:nat) : seq pub_uint8

let nat_pow2 (x: nat) : nat = pow2 x
