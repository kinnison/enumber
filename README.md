# enumber

![BSD 3 Clause](https://img.shields.io/github/license/kinnison/enumber.svg)
![Main build status](https://github.com/kinnison/enumber/workflows/main/badge.svg)
![Latest docs](https://docs.rs/enumber/badge.svg)
![Crates.IO](https://img.shields.io/crates/v/enumber.svg)

`enumber` is a procedural macro crate which helps you to work with enums whose
purpose it is to represent numbers (for example when parsing complex binary
logs) or strange wire protocols.

```rust
#[enumber::convert]
pub enum Flags {
    EnableCompression = 1,
    EnableTLS = 2,
    Other(usize),
}
```
