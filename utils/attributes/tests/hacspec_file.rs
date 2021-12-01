use hacspec_attributes::hacspec_unsafe;

#[hacspec_unsafe]
#[allow(dead_code)]
fn test_unsafe_hacspec() {}

#[hacspec_unsafe(outside)]
#[allow(dead_code)]
fn test_outside_hacspec() {}
