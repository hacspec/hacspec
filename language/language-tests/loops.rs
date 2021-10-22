type MyIntegerType = usize;

pub fn foo(mut x: MyIntegerType) -> usize {
    for i in 0..x {
        x = i
    }
    x
}
