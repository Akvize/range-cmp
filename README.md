# range_cmp

[![Crates.io][crates-badge]][crates-url]
[![MIT licensed][mit-badge]][mit-url]
[![Apache licensed][apache-badge]][apache-url]
[![Build Status][actions-badge]][actions-url]

[crates-badge]: https://img.shields.io/crates/v/range-cmp.svg
[crates-url]: https://crates.io/crates/range-cmp
[mit-badge]: https://img.shields.io/badge/license-MIT-blue.svg
[mit-url]: https://github.com/Akvize/range-cmp/blob/master/LICENSE-MIT
[apache-badge]: https://img.shields.io/badge/license-APACHE-blue.svg
[apache-url]: https://github.com/Akvize/range-cmp/blob/master/LICENSE-APACHE
[actions-badge]: https://github.com/Akvize/range-cmp/actions/workflows/ci.yml/badge.svg
[actions-url]: https://github.com/Akvize/range-cmp/actions/workflows/ci.yml

[Docs](https://docs.rs/reconcile/latest/range-cmp/)

This Rust crate provides the `RangeComparable` trait on all types that
implement `Ord`. This traits exposes a `rcmp` associated method
that allows comparing a value with a range of values:

```rust
use range_cmp::{RangeComparable, RangeOrdering};
assert_eq!(15.rcmp(20..30), RangeOrdering::Below);
assert_eq!(25.rcmp(20..30), RangeOrdering::Inside);
assert_eq!(35.rcmp(20..30), RangeOrdering::Above);
```
## Empty ranges handling

This crate _does not_ strictly handle empty ranges, 
which are not mathematically comparable. In this case, 
range_cmp will show different behavior depending on
the representation of the empty range. For instance:

```rust
assert_eq!(30.range_cmp(45..35), RangeOrdering::Below);
assert_eq!(30.range_cmp(25..15), RangeOrdering::Above);
assert_eq!(0.range_cmp(0..0), RangeOrdering::Above);
```
