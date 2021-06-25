use hacspec_lib::*;

const U32_BITS: usize = 4 * 8;
const N_QUEUES: usize = 20;
const N_THREADS: usize = 30;
const SENTINEL: u8 = 0xFFu8;

#[derive(Clone, Copy, Debug)]
pub struct RunqueueId(u8);
#[derive(Clone, Copy, Debug)]
pub struct ThreadId(u8);

public_bytes!(Tail, N_QUEUES);
public_bytes!(NextIds, N_THREADS);

#[derive(Clone, Copy, Debug)]
pub struct Clist(Tail, NextIds);

pub fn clist_new() -> Clist {
    let mut tail = Tail::new();
    for i in 0..tail.len() {
        tail[i] = SENTINEL;
    }
    let mut next_idxs = NextIds::new();
    for i in 0..next_idxs.len() {
        next_idxs[i] = SENTINEL;
    }
    Clist(tail, next_idxs)
}

pub fn clist_is_empty(x: &Clist, rq: RunqueueId) -> bool {
    let RunqueueId(rq) = rq;
    let Clist(tail, _next_ids) = x;
    tail[rq] == SENTINEL
}

pub fn clist_push(x: Clist, n: ThreadId, rq: RunqueueId) -> Clist {
    let RunqueueId(rq) = rq;
    let ThreadId(n) = n;
    let Clist(mut tail, mut next_idxs) = x;
    if next_idxs[n] == SENTINEL {
        if tail[rq] == SENTINEL {
            // rq is empty, link both tail and n.next to n
            tail[rq] = n;
            next_idxs[n] = n;
        } else {
            // rq has an entry already, so
            // 1. n.next = old_tail.next ("first" in list)
            next_idxs[n] = next_idxs[tail[rq]];
            // 2. old_tail.next = n
            next_idxs[tail[rq]] = n;
            // 3. tail = n
            tail[rq] = n;
        }
    }
    Clist(tail, next_idxs)
}

pub fn clist_pop_head(x: Clist, rq: RunqueueId) -> (Clist, Option<u8>) {
    let RunqueueId(rq) = rq;
    let Clist(mut tail, mut next_idxs) = x;
    let mut out: Option<u8> = Option::<u8>::None;
    if tail[rq] == SENTINEL {
        // rq is empty, do nothing
    } else {
        let head = next_idxs[tail[rq]];
        if head == tail[rq] {
            // rq's tail bites itself, so there's only one entry.
            // so, clear tail.
            tail[rq] = SENTINEL;
            // rq is now empty
        } else {
            // rq has multiple entries,
            // so set tail.next to head.next (second in list)
            next_idxs[tail[rq]] = next_idxs[head];
        }

        // now clear head's next value
        next_idxs[head] = SENTINEL;
        out = Option::<u8>::Some(head);
    }
    (Clist(tail, next_idxs), out)
}

pub fn clist_peek_head(x: Clist, rq: RunqueueId) -> Option<u8> {
    let RunqueueId(rq) = rq;
    let Clist(tail, next_idxs) = x;
    if tail[rq] == SENTINEL {
        Option::<u8>::None
    } else {
        Option::<u8>::Some(next_idxs[tail[rq]])
    }
}

pub fn clist_advance(x: Clist, rq: RunqueueId) -> Clist {
    let RunqueueId(rq) = rq;
    let Clist(mut tail, next_idxs) = x;
    if tail[rq] != SENTINEL {
        tail[rq] = next_idxs[tail[rq]];
    }
    Clist(tail, next_idxs)
}
