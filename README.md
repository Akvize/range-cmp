# range_cmp

This Rust crate provides the `RangeComparable` trait on all types that
implement `PartialOrd`. This traits exposes a `range_cmp` associated method
that allows comparing a value with a range of values:

```rust
use range_cmp::{RangeComparable, RangeOrdering};
assert_eq!(15.range_cmp(20..30), RangeOrdering::Below);
assert_eq!(25.range_cmp(20..30), RangeOrdering::Inside);
assert_eq!(35.range_cmp(20..30), RangeOrdering::Above);
```
