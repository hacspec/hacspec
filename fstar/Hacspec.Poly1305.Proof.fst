module Hacspec.Poly1305.Proof

open Hacspec.Lib
open FStar.Mul

module Orig = Spec.Poly1305
module New = Hacspec.Poly1305.Edited
module Seq = Lib.Sequence

#set-options "--fuel 0 --ifuel 0 --z3rlimit 30"

let poly1305_encode_r_equiv (b:New.poly_block)
  : Lemma (New.poly1305_encode_r b ==
           Orig.poly1305_encode_r b)
           [SMTPat (New.poly1305_encode_r b)] =
  let n_1 = uint128_from_le_bytes (array_from_seq (16) (b)) in
  let n_2 = (n_1) &. (secret (pub_u128 0xffffffc0ffffffc0ffffffc0fffffff)) in
  let n_3 = nat_from_secret_literal (0x03fffffffffffffffffffffffffffffffb) (n_1) in

  let lo = Lib.ByteSequence.uint_from_bytes_le (Lib.Sequence.sub b 0 8) in
  let hi = Lib.ByteSequence.uint_from_bytes_le (Lib.Sequence.sub b 8 8) in
  let mask0 = u64 0x0ffffffc0fffffff in
  let mask1 = u64 0x0ffffffc0ffffffc in
  let lo = lo &. mask0 in
  let hi = hi &. mask1 in
  assert_norm (pow2 128 < pow2 130 - 5);
  let res = (uint_v hi * pow2 64 + uint_v lo) in
  admit()


let prime_equiv:_:unit{Orig.prime == 0x03fffffffffffffffffffffffffffffffb} =
  assert_norm(Orig.prime == 0x03fffffffffffffffffffffffffffffffb)

let poly1305_encode_block_equiv (b:New.poly_block)
  : Lemma (New.poly1305_encode_block b == Orig.encode (seq_len b) b)
           [SMTPat (New.poly1305_encode_block b)] =
    Lib.ByteSequence.lemma_reveal_uint_to_bytes_le #U128 #SEC (b <: Lib.ByteSequence.lbytes 16)


let poly1305_encode_last_equiv (b:New.sub_block)
  : Lemma (New.poly1305_encode_last (seq_len b) b == Orig.encode (seq_len b) b)
           [SMTPat (New.poly1305_encode_last (seq_len b) b)] =
    admit()


let poly1305_init_equiv (k:New.poly_key)
  : Lemma (let (a,r,k') = New.poly1305_init k in
           let (a',r') = Orig.poly1305_init k in
           a == a' /\ r == r' /\ k' == k)
           [SMTPat (New.poly1305_init k)] =
           ()

let poly1305_update_block_equiv (b:New.poly_block) (st:New.poly_state)
  : Lemma (let (a,r,k) = st in
           let a' = Orig.poly1305_update1 r (seq_len b) b a in
           New.poly1305_update_block b st == (a',r,k))
           [SMTPat (New.poly1305_update_block b st)]
           = ()

let poly1305_update_blocks_equiv (m:byte_seq) (st:New.poly_state)
  : Lemma (let (a,r,k) = st in
           let (a',_,_) = New.poly1305_update_blocks m st in
           let nblocks = seq_len m / 16 in
           let m' = Lib.Sequence.sub #_ #(seq_len m) m 0 (nblocks * 16) in
           a' == Lib.Sequence.repeat_blocks_multi 16 m' (Orig.poly1305_update1 r 16) a) 
           [SMTPat (New.poly1305_update_blocks m st)]
           =
           admit()


let poly1305_update_last_equiv (b:New.sub_block{seq_len b < 16}) (st:New.poly_state)
  : Lemma (let (a,r,k) = st in
           let a' = Orig.poly1305_update_last r (seq_len b) b a in
           New.poly1305_update_last (seq_len b) b st == (a',r,k))
           [SMTPat (New.poly1305_update_last (seq_len b) b st)]
           = ()

let poly1305_finish_equiv (st:New.poly_state)
  : Lemma (let (a,r,k) = st in
           New.poly1305_finish st == Orig.poly1305_finish k a)
           [SMTPat (New.poly1305_finish st)] =
           admit()

let poly1305_update_equiv (m:byte_seq) (st:New.poly_state)
  : Lemma (let (a,r,k) = st in
           let a' = Orig.poly1305_update m a r in
           New.poly1305_update m st == (a',r,k))
           [SMTPat (New.poly1305_update m st)]
           =
          admit()

let poly1305_mac_equiv (m:byte_seq) (k:New.poly_key)
  : Lemma (New.poly1305 m k == Orig.poly1305_mac m k) =
    ()
