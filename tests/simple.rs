use std::convert::TryFrom;

#[enumber::convert]
#[repr(u16)]
enum OpenExample {
    First = 1,
    Second = 2,
    Third = 23,
}

#[enumber::convert]
enum ClosedExample {
    One = 1,
    Two = 2,
    Five = 5,
    Other(u8),
}

#[test]
fn test_open_from_num_canfail() {
    assert!(OpenExample::try_from(45).is_err());
}
