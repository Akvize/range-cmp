# range_cmp

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