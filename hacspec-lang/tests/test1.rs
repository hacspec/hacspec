use hacspec::prelude::*;

fn dummy_hacspec_func(x: u32, y: u32, a: Seq<u32>) -> u32 {
    let mut z = x - y;
    let mut z1 = x + y;
    let (c, d) = (z + 1u32, z - 1u32);
    let mut a: Seq<u32> = a;
    a[1usize] = y + c - d;
    if a[1usize] == 0u32 {
        let z = z + 2u32 * y + a[0usize];
    } else {
        z1 = z - 2u32;
    };
    for u in 0usize..2usize {
        a[u] = a[u] + 1u32;
        z = a[u + 1usize];
    }
    z
}