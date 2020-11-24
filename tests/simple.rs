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

#[enumber::convert]
#[repr(u8)]
#[exhaustive]
#[derive(Debug)]
pub enum LogLevel {
    All = 0x00..=0x1f,
    Trace = 0x20..=0x3f,
    Debug = 0x40..=0x5f,
    Normal = 0x60..=0x7f,
    Info = 0x80..=0x9f,
    Warn = 0xa0..=0xbf,
    Error = 0xc0..=0xff,
}

#[test]
fn test_open_from_num_canfail() {
    assert!(OpenExample::try_from(45).is_err());
}

#[test]
fn check_from_hex() {
    use std::str::FromStr;
    match LogLevel::from_str("0xa3") {
        Ok(v) => match v {
            LogLevel::Warn(n) if n == 0xa3 => {}
            t => panic!("Unexpected parsed value: {:?}", t),
        },
        Err(e) => panic!(e),
    }
}
