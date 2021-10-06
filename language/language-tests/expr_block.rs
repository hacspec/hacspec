pub fn foo(x: Option<u32>) -> bool {
    match x {
        Option::<u32>::None => {
            // hello, world!
            false
        }
        Option::<u32>::Some(_) => true,
    }
}
