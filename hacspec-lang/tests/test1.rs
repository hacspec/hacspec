fn dummy_hacspec_func(x_y: (u32, u32)) -> u32 {
    let (x,y) = x_y;
    x + y
}

fn main() {
    dummy_hacspec_func((2,3));
}
