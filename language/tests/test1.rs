use hacspec_lib::*;

fn foo(_a: Seq<u32>) -> Seq<u32> {
    Seq::<u32>::new(2)
}

pub fn bar(a: &(Seq<u32>, u32)) -> Seq<u32> {
    let (a1, _a2) = a;
    a1.clone()
}

fn baz(a: &Seq<u32>, _b: &Seq<u32>) -> Seq<u32> {
    a.clone()
}

pub fn dummy_hacspec_func(x: u32, y: u32, a: Seq<u32>) -> u32 {
    let mut z = x - y;
    let mut z1 = x + y;
    // let _ = bar(&(a, 1));
    let a = baz(&a, &a);
    let (c, d) = (z + 1u32, z - 1u32);
    let a: Seq<u32> = a;
    let mut a = a.update_start(&Seq::<u32>::new(3));
    a = foo(a);
    a[1] = y + c - d;
    if a[1] == 0u32 {
        let z1 = z + 2u32 * y + a[0];
        z = z - z1;
    } else {
        z1 = z - 2u32;
    };
    for u in 0..2 {
        a[u] = a[u] + 1u32;
        z = a[u + 1];
    }
    z ^ z1
}
