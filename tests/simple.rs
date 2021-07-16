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

#[enumber::into]
#[repr(usize)]
#[derive(Debug)]
enum IpAddr {
    #[value(4)] V4(u8, u8, u8, u8),
    #[value(6)] V6(String),
}

#[derive(Debug)]
struct Fingerprint {
    value: Box<[u8]>,
}

#[enumber::into]
#[repr(usize)]
#[derive(Debug)]
enum Errors {
    CannotLoadCryptoLibrary(String) = 0x110,
    InitSqlite3WithoutMutex = 0x120,
    AmbiguousName(String, String) = 0x202,
    CannotDeleteKey(Fingerprint, String) = 0x212,
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

#[test]
fn test_ip_addr() {
    assert_eq!(4 as usize, IpAddr::V4(192, 168, 1, 1).into());
    assert_eq!(6 as usize, IpAddr::V6("1::".into()).into());
}

#[test]
fn test_errors() {
    assert_eq!(0x110 as usize,
               Errors::CannotLoadCryptoLibrary("file not found".into()).into());
    assert_eq!(0x120 as usize,
               Errors::InitSqlite3WithoutMutex.into());
    assert_eq!(0x202 as usize,
               Errors::AmbiguousName("a".into(), "123".into()).into());
    assert_eq!(0x212 as usize,
               Errors::CannotDeleteKey(
                   Fingerprint { value: b"1234".to_vec().into_boxed_slice() },
                   "Key does not exists".into()).into());
}
