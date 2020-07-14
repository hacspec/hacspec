fn dummy_hacspec_func(x: u32, y: u32, a: &[u32]) -> u32 {
    let mut z = x - y;
    z = z + 2 * y+ a[0];
    z
}

fn main() {
    dummy_hacspec_func(2, 3, &[0,1,2]);
}
