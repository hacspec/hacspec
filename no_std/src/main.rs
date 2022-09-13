#![no_std]
#![no_main]
#![feature(default_alloc_error_handler)]

use static_alloc::Bump;

#[global_allocator]
static A: Bump<[u8; 1 << 10]> = Bump::uninit();

use cortex_m_rt::entry;
use cortex_m_semihosting::{
    debug::{self, EXIT_SUCCESS},
    hprintln as println,
};

use panic_semihosting as _;

use hacspec_lib as _;

#[entry]
fn main() -> ! {
    // testing output
    println!("Hello, hacspec!");

    // testing asserts
    assert!(1 == 1);

    // exit via semihosting call
    debug::exit(EXIT_SUCCESS);

    // the cortex_m_rt `entry` macro requires `main()` to never return
    loop {}
}
