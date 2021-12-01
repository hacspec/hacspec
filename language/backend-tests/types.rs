use hacspec_lib::*;

fn bool_true() -> bool {
    true
}

fn bool_false() -> bool {
    false
}

fn num_u8() -> u8 {
    100u8
}

fn num_u16() -> u16 {
    100u16
}

fn num_u32() -> u32 {
    100u32
}

fn num_u64() -> u64 {
    100u64
}

fn num_u128() -> u128 {
    100u128
}

fn num_usize() -> usize {
    100usize
}

fn num_i8() -> i8 {
    100i8
}

fn num_i16() -> i16 {
    100i16
}

fn num_i32() -> i32 {
    100i32
}

fn num_i64() -> i64 {
    100i64
}

fn num_i128() -> i128 {
    100i128
}

fn num_isize() -> isize {
    100isize
}
    
// Disallowed: f32, f64

// Disallowed (return &str):
// fn string() -> &'static str {
//     "hello world"
// }

// Cannot be done ?
// fn string(a : &str) -> String {
//     // "hello world".to_string()
//     // String::from("hello world")
//     String::from(a)
// }

// Disallowed: char
// Disallowed: Never — ! — a type with no values

fn tuple() -> (bool, i64, ()) {
    (false, num_i64(), ())
}

array!(my_array, 5, u64);
fn array () -> my_array {
    my_array ([0u64,1u64,2u64,3u64,4u64])
}

fn sequence () -> Seq<u64> {
    Seq::<u64>::new(0)
}

// Structs with fields are forbidden in hacspec
// struct my_struct {
    
// }

// fn my_struct_fn () -> my_struct {
//     my_struct {}
// }

// FOLLOWING FAILS: pub struct my_tuple_struct (pub bool, pub Seq<u64>);
// names must be cased correctly!
pub struct MyTupleStruct (pub bool, pub Seq<u64>);

fn my_tuple_struct_fn () -> MyTupleStruct {
    MyTupleStruct (true, sequence())
}

enum MyEnum {
    First,
    Second (u64),
    Third (bool)
}

fn my_enum_fn (inp : MyEnum) -> MyEnum {
    match inp {
        MyEnum::First => MyEnum::Second (0u64),
        MyEnum::Second (_) => MyEnum::Third (false),
        MyEnum::Third (_) => MyEnum::First
    }
}

// Disallowed: Union
// Disallowed?: Closures

// TODO:
// * Pointer types:
// ** References
// ** Raw pointers
// ** Function pointers

// Disallowed:
// * Trait types:
// ** Trait objects
// ** Impl trait
