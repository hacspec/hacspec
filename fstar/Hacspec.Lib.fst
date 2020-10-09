module Hacspec.Lib

open FStar.Mul

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

assume val uint32_rotate_left (u: uint32) (s: uint_size) : uint32

(*** Seq *)

module LSeq = Lib.Sequence
module LBSeq = Lib.ByteSequence

let lseq (a: Type) (len: uint_size) = LSeq.lseq a len

let seq (a: Type) = s:LSeq.seq a{range (LSeq.length s) U32}

let seq_len (#a: Type) (s: seq a) : nat = Seq.length s

let seq_new_ (#a: Type) (init:a) (len: uint_size) : lseq a len =
  Seq.create len init

unfold let byte_seq = seq uint8

let array_from_list
  (#a: Type)
  (l: list a{List.Tot.length l <= max_size_t})
    : lseq a (List.Tot.length l)
  =
  LSeq.of_list l

let uint32_to_be_bytes (x: uint32) : lseq uint8 4 =
  LBSeq.uint_to_bytes_be x

let  uint32_from_le_bytes (s: lseq uint8 4) : uint32 =
  LBSeq.uint_from_bytes_be s

(**** Array manipulation *)


let array_new_ (#a: Type) (init:a) (len: uint_size)  : lseq a len =
  LSeq.create len init

let array_index (#a: Type) (#len:uint_size) (s: lseq a len) (i: uint_size{i < len}) : a =
  LSeq.index s i

let array_upd (#a: Type) (#len:uint_size) (s: lseq a len) (i: uint_size{i < len}) (new_v: a) : lseq a len = LSeq.upd s i new_v

let array_from_seq
  (#a: Type)
  (out_len:uint_size)
  (input: seq a{Seq.length input = out_len})
    : lseq a out_len
  = input

let array_from_slice
  (#a: Type)
  (input: seq a)
  (start: uint_size)
  (slice_len: uint_size{start + slice_len <= LSeq.length input})
    : lseq a slice_len
  =
  Seq.slice input start (start + slice_len)

let array_slice
  (#a: Type)
  (input: seq a)
  (start: uint_size)
  (slice_len: uint_size{start + slice_len <= LSeq.length input})
    : lseq a slice_len
  =
  Seq.slice input start (start + slice_len)

let array_from_slice_range
  (#a: Type)
  (input: seq a)
  (start_fin: (uint_size & uint_size){
     fst start_fin >= 0 /\ snd start_fin <= LSeq.length input /\ snd start_fin >= fst start_fin
   })
    : lseq a (snd start_fin - fst start_fin)
  =
  let (start, fin) = start_fin in
  Seq.slice input start fin

let array_slice_range
  (#a: Type)
  (#len:uint_size)
  (input: lseq a len)
  (start_fin:(uint_size & uint_size){
    fst start_fin >= 0 /\ snd start_fin <= len /\ snd start_fin >= fst start_fin
  })
    : lseq a (snd start_fin - fst start_fin)
  =
  let (start, fin) = start_fin in
  LSeq.slice input start fin

let array_update_start
  (#a: Type)
  (#len: uint_size)
  (s: lseq a len)
  (start_s: seq a{Seq.length start_s <= len})
    : lseq a len
  =
  LSeq.update_sub s 0 (Seq.length start_s) start_s

let array_len  (#a: Type) (#len: uint_size) (s: lseq a len) = len

(**** Seq manipulation *)

let seq_slice
  (#a: Type)
  (s: seq a)
  (start: uint_size)
  (len: uint_size{start + len < LSeq.length s})
    : lseq a len
  =
  LSeq.slice #a #(Seq.length s) s start (start + len)

(**** Chunking *)

let seq_num_chunks (#a: Type) (s: seq a) (chunk_len: uint_size{chunk_len > 0}) : uint_size =
  (Seq.length s + chunk_len - 1) / chunk_len

let seq_chunk_len
  (#a: Type)
  (s: seq a)
  (chunk_len: uint_size)
  (chunk_num: uint_size{chunk_len * chunk_num <= Seq.length s})
    : Tot (out_len:uint_size{out_len <= chunk_len})
  =
  let idx_start = chunk_len * chunk_num in
  if idx_start + chunk_len > Seq.length s then
    Seq.length s - idx_start
  else
    chunk_len

let seq_chunk_same_len_same_chunk_len
  (#a: Type)
  (s1 s2: seq a)
  (chunk_len: uint_size)
  (chunk_num: uint_size)
  : Lemma
    (requires (LSeq.length s1 = LSeq.length s2 /\ chunk_len * chunk_num <= Seq.length s1))
    (ensures (seq_chunk_len s1 chunk_len chunk_num = seq_chunk_len s2 chunk_len chunk_num))
    [SMTPat (seq_chunk_len s1 chunk_len chunk_num); SMTPat (seq_chunk_len s2 chunk_len chunk_num)]
  =
  ()

let seq_get_chunk
  (#a: Type)
  (s: seq a)
  (chunk_len: uint_size)
  (chunk_num: uint_size)
  : Pure (uint_size & seq a)
    (requires (chunk_len * chunk_num <= Seq.length s))
    (ensures (fun (out_len, chunk) ->
      out_len = seq_chunk_len s chunk_len chunk_num /\ LSeq.length chunk = out_len
    ))
  =
  let idx_start = chunk_len * chunk_num in
  let out_len = seq_chunk_len s chunk_len chunk_num in
  (out_len, LSeq.slice #a #(Seq.length s)
    s idx_start (idx_start + seq_chunk_len s chunk_len chunk_num))

let seq_set_chunk
  (#a: Type)
  (#len:uint_size)
  (s: lseq a len)
  (chunk_len: uint_size)
  (chunk_num: uint_size)
  (chunk: seq a )
    : Pure (lseq a len)
      (requires (
        chunk_len * chunk_num <= Seq.length s /\
        LSeq.length chunk = seq_chunk_len s chunk_len chunk_num
      ))
      (ensures (fun out -> True))
  =
  let idx_start = chunk_len * chunk_num in
  let out_len = seq_chunk_len s chunk_len chunk_num in
  LSeq.update_sub s idx_start out_len chunk

(**** Numeric operations *)

assume val array_xor (#a: Type) (#len: uint_size) (s1: lseq a len) (s2 : lseq a len) : lseq a len

(**** Integers to arrays *)

assume val uint128_from_le_bytes (input: seq uint8{LSeq.length input <= 16}) : uint128

(*** Loops *)

assume val foldi (#acc: Type) (lo: uint_size) (hi: uint_size) (f: (i:uint_size{i < hi}) -> acc -> acc) (init: acc) : acc


(*** Nats *)

let nat_mod (n: nat) = x:nat{x < n}

val (+%) (#n:pos) (a:nat_mod n) (b:nat_mod n) : nat_mod n
let (+%) #n a b = (a + b) % n

val ( *% ) (#n:pos) (a:nat_mod n) (b:nat_mod n) : nat_mod n
let ( *% ) #n a b = (a * b) % n

assume val nat_from_secret_literal (m:pos) (x:uint128{v x < m}) : n:nat_mod m{v x == n}

assume val nat_from_literal (m: pos) (x:pub_uint128{v x < m}) : n:nat_mod m{v x == n}

let nat_to_public_byte_seq_le (n: pos)  (len: uint_size) (x: nat_mod n) : lseq pub_uint8 len =
  let n' = n % (pow2 (8 * len)) in
  Lib.ByteSequence.nat_to_bytes_le len n'

let nat_pow2 (m:pos) (x: nat{pow2 x < m}) : nat_mod m = pow2 x
