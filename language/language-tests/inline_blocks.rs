use hacspec_lib::*;

fn simple(x: usize) -> u64 {
    let x = 3 + match x {
        0 => {
            let a = 0;
            let b = 1;
            ({
                let c = 2;
                a + c
            }) + b
        }
        _ => {
            let c = 123;
            c + 10
        }
    };
    x as u64
}

fn foo() -> Result<u8, u16> {
    Result::<u8, u16>::Ok(8u8)
}

fn result(x: Result<u8, u16>) -> Result<u8, u16> {
    let test = match 1 {
        1 => {
            let x = foo()?;
            let y = foo()?;
            let z = foo()?;
            x + y + z
        }
        _ => foo()?,
    };
    Result::<u8, u16>::Ok(test)
}
