use hacspec_lib::*;

array!(State, 16, u32);

pub fn line(a: u32, b: u32, d: u32, s: usize, m: State) -> State {
    let mut state = m;
    // TODO: we can't write += or ^= here right now :(
    state[a] = state[a] + state[b];
    state[d] = state[d] ^ state[a];
    state[d] = state[d] >> s;
    state
}
