
fn dummy_hacspec_func(x: u32, y: u32, a: Vec<u32>) -> u32 {
    let mut z = x - y;
    let (c, d) = (z + 1u32, z - 1u32);
    let mut a = a;
    a[1usize] = y +c - d;
    z = z + 2u32 * y+ a[0usize];
    z
}

fn main() {
    let v = Vec::new();
    dummy_hacspec_func(2u32, 3u32, v);
}
