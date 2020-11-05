module Hacspec.Chacha20.Proof

open Hacspec.Lib
open FStar.Mul

module Orig = Spec.Chacha20
module New = Hacspec.Chacha20

#set-options "--fuel 0 --ifuel 0 --z3rlimit 30"

let line_equiv
  (a : New.state_idx)
  (b : New.state_idx)
  (d : New.state_idx)
  (s : uint_size{
  (**) s > 0 /\ s < 32
  })
  (m : New.state)
    : Lemma (New.chacha_line a b d s m == Orig.line a b d (size s) m)
  [SMTPat (New.chacha_line a b d s m)]
  =
  assert(New.chacha_line a b d s m `Seq.equal` Orig.line a b d (size s) m)

let quarter_round_equiv
  (a : New.state_idx)
  (b : New.state_idx)
  (c : New.state_idx)
  (d : New.state_idx)
  (state : New.state)
    : Lemma (New.chacha_quarter_round a b c d state == Orig.quarter_round a b c d state)
  [SMTPat (New.chacha_quarter_round a b c d state)]
  =
  ()

let double_round_equiv (state: New.state)
    : Lemma (New.chacha_double_round state == Orig.double_round state)
  [SMTPat (New.chacha_double_round state)]
  =
  ()

let constants_equiv ()
    : Lemma (forall (i:nat{i < 4}).
      v (Seq.index (New.chacha20_constants_init ()) i) ==
      v (Seq.index Orig.chacha20_constants i)
    )
  =
  (* Why can't F* find this ? Orig.chacha20c_constants = [c0; c1; c2; c3] *)
  assume(v Orig.c0 == v (Seq.index Orig.chacha20_constants 0));
  assume(v Orig.c1 == v (Seq.index Orig.chacha20_constants 1));
  assume(v Orig.c2 == v (Seq.index Orig.chacha20_constants 2));
  assume(v Orig.c3 == v (Seq.index Orig.chacha20_constants 3))

let key_to_u32s_equiv (key: New.key)
    : Lemma (New.chacha20_key_to_u32s key == Lib.ByteSequence.uints_from_bytes_le #U32 #SEC #8 key)
  [SMTPat (New.chacha20_key_to_u32s key)]
  =
  let aux (i:nat{i < 8}) : Lemma (
    Seq.index (New.chacha20_key_to_u32s key) i ==
    Seq.index (Lib.ByteSequence.uints_from_bytes_le #U32 #SEC #8 key) i
  ) =
    Lib.ByteSequence.index_uints_from_bytes_le #U32 #SEC #8 key i
  in
  Classical.forall_intro aux;
  assert(
    New.chacha20_key_to_u32s key `Seq.equal`
    Lib.ByteSequence.uints_from_bytes_le #U32 #SEC #8 key
  )

let iv_to_u32s_equiv (iv: New.iv)
    : Lemma (New.chacha20_iv_to_u32s iv == Lib.ByteSequence.uints_from_bytes_le #U32 #SEC #3 iv)
  [SMTPat (New.chacha20_iv_to_u32s iv)]
  =
  let aux (i:nat{i < 3}) : Lemma (
    Seq.index (New.chacha20_iv_to_u32s iv) i ==
    Seq.index (Lib.ByteSequence.uints_from_bytes_le #U32 #SEC #3 iv) i
  ) =
    Lib.ByteSequence.index_uints_from_bytes_le #U32 #SEC #3 iv i
  in
  Classical.forall_intro aux;
  assert(
    New.chacha20_iv_to_u32s iv `Seq.equal`
    Lib.ByteSequence.uints_from_bytes_le #U32 #SEC #3 iv
  )

let ctr_to_seq_equiv (ctr: uint32)
    : Lemma (New.chacha20_ctr_to_seq ctr == Seq.init 1 (fun _ -> ctr))
  [SMTPat (New.chacha20_ctr_to_seq ctr)]
  =
  assert(New.chacha20_ctr_to_seq ctr `Seq.equal` Seq.init 1 (fun _ -> ctr))

#push-options "--fuel 0 --ifuel 0 --z3rlimit 1000"
let chacha_block_init_equiv (key: New.key) (ctr: uint32) (iv: New.iv)
    : Lemma (New.chacha_block_init key ctr iv == Orig.chacha20_init key iv (v ctr))
  =
  let aux (i:nat{i < 16}) : Lemma (
    Seq.index (New.chacha_block_init key ctr iv) i ==
    Seq.index (Orig.chacha20_init key iv (v ctr)) i
  ) =
    (* concat makes it hard to verify... *)
    if i < 4 then admit()
    else if i < 12 then admit()
    else if i = 12 then admit()
    else if i < 16 then admit()
  in
  Classical.forall_intro aux;
  assert(New.chacha_block_init key ctr iv `Seq.equal` Orig.chacha20_init key iv (v ctr))
#pop-options
