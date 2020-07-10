fn dummy_hacspec_func(x: u32, y:&u32) -> u32 {
    x + y
}

fn main() {
    dummy_hacspec_func(2,&3);
}
