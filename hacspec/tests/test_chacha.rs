use hacspec_lib::*;

array!(State, 16, u32);

pub fn line(a: u32, b: u32, d: u32, s: u32, m: State) -> State {
    let mut state = m;
    state[a] = state[a] + state[b];
    state[d] = state[d] ^ state[a];
    state[d] = state[d] >> s;
    let (chunk_size, mut chunk) = state.get_chunk(2usize, 4usize);
    if chunk_size < 4usize {
        chunk[b - d] = chunk[a] >> 4u32;
    }
    State::new().update_start(&chunk)
}
