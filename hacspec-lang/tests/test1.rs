use hacspec::prelude::*;

fn dummy_hacspec_func(x: u32, y: u32, a: Seq<u32>) -> u32 {
    let mut z = x - y;
    let (c, d) = (z + 1u32, z - 1u32);
    let mut a: Seq<u32> = a;
    a[1usize] = y + c - d;
    if a[1usize] == 0u32 {
        z = z + 2u32 * y + a[0usize];
    };
    z
}

fn main() {
    let v = Seq::new(2usize);
    dummy_hacspec_func(2u32, 3u32, v);
}
