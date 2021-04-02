module Hacspec.Chacha20.Proof

open Hacspec.Lib
open FStar.Mul

module Orig = Spec.Chacha20
module New = Hacspec.Chacha20.Edited
module Seq = Lib.Sequence

#set-options "--fuel 0 --ifuel 0 --z3rlimit 30"

let line_equiv
  (a : New.state_idx)
  (b : New.state_idx)
  (d : New.state_idx)
  (s : uint_size{
  (**) s > 0 /\ s < 32
  })
  (m : New.state)
    : Lemma (New.chacha20_line a b d s m == Orig.line a b d (size s) m)
  [SMTPat (New.chacha20_line a b d s m)]
  =
  assert(New.chacha20_line a b d s m `Seq.equal` Orig.line a b d (size s) m)

let quarter_round_equiv
  (a : New.state_idx)
  (b : New.state_idx)
  (c : New.state_idx)
  (d : New.state_idx)
  (state : New.state)
    : Lemma (New.chacha20_quarter_round a b c d state == Orig.quarter_round a b c d state)
  [SMTPat (New.chacha20_quarter_round a b c d state)]
  =
  ()

let double_round_equiv (state: New.state)
    : Lemma (New.chacha20_double_round state == Orig.double_round state)
  [SMTPat (New.chacha20_double_round state)]
  =
  ()


let rounds_equiv (state: New.state)
    : Lemma (New.chacha20_rounds state == Orig.rounds state)
  [SMTPat (New.chacha20_rounds state)]
  =
  fold_extensionality 10 New.chacha20_double_round Orig.double_round state

let core_equiv (ctr:uint32) (state: New.state)
    : Lemma (New.chacha20_core ctr state == Orig.chacha20_core (v ctr) state)
  [SMTPat (New.chacha20_core ctr state)]
  =
    let s0 = state in
    let s1 = array_upd state (usize 12) (
                      (array_index (s0) (usize 12)) +. (ctr)) in
    let k = New.chacha20_rounds s1 in
    let ka = k `array_add (+.)` s1 in
    let kb = k `array_add (+.)` s0 in
    let kb' = array_upd kb (usize 12) (
                      (array_index (kb) (usize 12)) +. (ctr)) in
    assert (u32 (v ctr) == ctr);
    assert(Orig.chacha20_add_counter s0 (v ctr) == s1);
    assert(Orig.rounds s1 == New.chacha20_rounds s1);
    assert(Orig.sum_state k s0 == kb);
    assert(Orig.chacha20_add_counter kb (v ctr) == kb');
    assert(ka == New.chacha20_core ctr state);
    assert(kb' == Orig.chacha20_core (v ctr) state);
    assert(forall i. i <> 12 ==> s0.[i] ==  s1.[i]);
    assert(forall i. i <> 12 ==> ka.[i] ==  kb.[i]);
    assert(forall i. i <> 12 ==> ka.[i] ==  kb'.[i]);
    assert(s1.[12] ==  s0.[12] +. ctr);
    assert(ka.[12] ==  k.[12] +. s1.[12]);
    assert(kb.[12] ==  k.[12] +. s0.[12]);
    assert(kb'.[12] ==  k.[12] +. s0.[12] +. ctr);
    assert(kb'.[12] ==  k.[12] +. (s0.[12] +. ctr));
    assert(kb'.[12] ==  k.[12] +. s1.[12]);
    assert(forall i. i >= 0 /\ i < 16 ==> ka.[i] ==  kb'.[i]);
    Lib.Sequence.eq_intro ka kb'


let constants_equiv ()
    : Lemma (New.chacha20_constants_init() == Lib.Sequence.map secret Orig.chacha20_constants)
  =
  let l = [Orig.c0;Orig.c1;Orig.c2;Orig.c3] in
  assert_norm(List.Tot.length l == 4);
  assert_norm(List.Tot.index l 0 == Orig.c0);
  assert_norm(List.Tot.index l 1 == Orig.c1);
  assert_norm(List.Tot.index l 2 == Orig.c2);
  assert_norm(List.Tot.index l 3 == Orig.c3);
  Lib.Sequence.eq_intro (New.chacha20_constants_init ()) (Lib.Sequence.map secret Orig.chacha20_constants)

let chacha20_init_equiv (key: New.cha_cha_key) (iv:New.cha_cha_iv) (ctr:uint32)
    : Lemma (New.chacha20_init key iv ctr ==
             Orig.chacha20_init key iv (v ctr))
            [SMTPat (New.chacha20_init key iv ctr)]
  = let new_init = New.chacha20_init key iv ctr in
    let old_init = Orig.chacha20_init key iv (v ctr) in
    constants_equiv();
    Lib.Sequence.eq_intro new_init old_init

let chacha20_key_block_equiv (state: New.state)
    : Lemma (New.chacha20_key_block state ==
             Orig.chacha20_key_block state)
            [SMTPat (New.chacha20_key_block state)] =
            ()

let chacha20_key_block0_equiv (key: New.cha_cha_key) (iv:New.cha_cha_iv)
    : Lemma (New.chacha20_key_block0 key iv ==
             Orig.chacha20_key_block0 key iv)
            [SMTPat (New.chacha20_key_block0 key iv)] =
            ()

let chacha20_encrypt_block_equiv (state: New.state) (ctr:uint32) (plain:New.block)
    : Lemma (New.chacha20_encrypt_block state ctr plain ==
             Orig.chacha20_encrypt_block state (v ctr) plain)
            [SMTPat (New.chacha20_encrypt_block state ctr plain)] =
            ()


let chacha20_encrypt_last_equiv (state: New.state) (ctr:uint32) (plain:byte_seq{seq_len plain < 64})
    : Lemma (New.chacha20_encrypt_last state ctr plain ==
             Orig.chacha20_encrypt_last state (v ctr) (seq_len plain) plain)
            [SMTPat (New.chacha20_encrypt_last state ctr plain)] =
    let orig_last = Orig.chacha20_encrypt_last state (v ctr) (seq_len plain) plain in
    let new_last = New.chacha20_encrypt_last state ctr plain in
    Lib.Sequence.eq_intro orig_last new_last


let chacha20_update_equiv (state: New.state) (m:byte_seq)
    : Lemma (New.chacha20_update state m ==
             Orig.chacha20_update state m)
            [SMTPat (New.chacha20_update state m)] = admit()


let chacha20_equiv (key : New.cha_cha_key) (iv : New.cha_cha_iv) (ctr : pub_uint32) (m : byte_seq)
  : Lemma (New.chacha20 key iv ctr m ==
           Orig.chacha20_encrypt_bytes key iv (v ctr) m) = ()
