// Copyright 2023 Developers of the range_cmp project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! This crate provides the [`RangeOrd`] trait on all types that implement [`Ord`].
//! This traits exposes a [`rcmp`](RangeOrd::rcmp) associated method that allows
//! comparing a value with a range of values:
//!
//! ```
//! use range_cmp::{RangeOrd, RangeOrdering};
//! assert_eq!(15.rcmp(20..30), RangeOrdering::Below);
//! assert_eq!(25.rcmp(20..30), RangeOrdering::Inside);
//! assert_eq!(35.rcmp(20..30), RangeOrdering::Above);
//! ```

use std::borrow::Borrow;
use std::ops::{Bound, RangeBounds};

/// Return type for [`RangeOrd::rcmp`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum RangeOrdering {
    /// The value is below (all) the range. For instance, `-1` is below the range `0..42`.
    Below,
    /// The value is contained inside the range. For instance, `34` is inside the range `0..42`.
    Inside,
    /// The value is above (all) the range. For instance, `314` is above the range `0..42`.
    Above,
}

// suggestion from @benschulz https://internals.rust-lang.org/t/implement-rangebounds-for-range/19704/3
/// Helper trait to allow passing a range as either a owned value or a reference.
///
/// For instance:
///
/// ```
/// use std::ops::RangeBounds;
/// use range_cmp::BorrowRange;
/// fn f<T, R: RangeBounds<T>, B: BorrowRange<T, R>>(range: B) {
///     let range = range.borrow();
///     // ...
/// }
/// ```
///
/// With concrete type such as [`i32`], this would be achieved by taking a generic type `T` with
/// the bound `T: Borrow<i32>`. So we might be tempted to do the same with the [`RangeBounds`]
/// trait:
///
/// ```
/// use std::borrow::Borrow;
/// use std::ops::RangeBounds;
/// fn f<R: RangeBounds<i32>, B: Borrow<R>>(range: B) {
///     let range = range.borrow();
///     // ...
/// }
/// f(0..42)
/// ```
///
/// However, this fails to compile when passing a reference:
///
/// ```compile_fail,E0282
/// # use std::borrow::Borrow;
/// # use std::ops::RangeBounds;
/// # fn f<R: RangeBounds<i32>, B: Borrow<R>>(range: B) {
/// #     let range = range.borrow();
/// #     // ...
/// # }
/// f(&(0..42))
/// ```
///
/// The compilation output is:
///
/// ```shell
///   | f(&(0..42))
///   | ^ cannot infer type of the type parameter `R` declared on the function `f`
/// ```
///
/// Indeed, although we understand we want to pass a [`Range`](std::ops::Range)`<`[`i32`]`>` by
/// reference, the compiler need to assume that other types could yield a
/// `&`[`Range`](std::ops::Range)`<`[`i32`]`>` when borrowed.
pub trait BorrowRange<T: ?Sized, R>: Borrow<R> {}
impl<T, R: RangeBounds<T>> BorrowRange<T, R> for R {}
impl<T, R: RangeBounds<T>> BorrowRange<T, R> for &R {}

/// Trait to provide the [`rcmp`](RangeOrd::rcmp) method, which allows comparing
/// the type to a range. A blanket implementation is provided for all types that implement the
/// [`Ord`] trait.
pub trait RangeOrd {
    /// Compare the value to a range of values. Returns whether the value is below, inside or above
    /// the range.
    ///
    /// ```
    /// use range_cmp::{RangeOrd, RangeOrdering};
    /// assert_eq!(15.rcmp(20..30), RangeOrdering::Below);
    /// assert_eq!(25.rcmp(20..30), RangeOrdering::Inside);
    /// assert_eq!(35.rcmp(20..30), RangeOrdering::Above);
    /// ```
    fn rcmp<R: RangeBounds<Self>, B: BorrowRange<Self, R>>(&self, range: B) -> RangeOrdering;
}

impl<T: Ord> RangeOrd for T {
    fn rcmp<R: RangeBounds<Self>, B: BorrowRange<Self, R>>(&self, range: B) -> RangeOrdering {
        let range = range.borrow();

        if range.contains(self) {
            return RangeOrdering::Inside;
        }

        if match range.start_bound() {
            Bound::Included(key) => self < key,
            Bound::Excluded(key) => self <= key,
            _ => false,
        } {
            return RangeOrdering::Below;
        }

        if match range.end_bound() {
            Bound::Included(key) => self > key,
            Bound::Excluded(key) => self >= key,
            _ => false,
        } {
            return RangeOrdering::Above;
        }

        unreachable!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn range_full() {
        // 1 is inside ]-inf, inf[
        assert_eq!(1.rcmp(..), RangeOrdering::Inside);
    }

    #[test]
    fn range_from() {
        // 1 is inside [1, +inf[
        assert_eq!(1.rcmp(1..), RangeOrdering::Inside);
        assert_eq!(1.rcmp(&1..), RangeOrdering::Inside);

        // 1 is below [2, +inf[
        assert_eq!(1.rcmp(2..), RangeOrdering::Below);
        assert_eq!(1.rcmp(&2..), RangeOrdering::Below);
    }

    #[test]
    fn range_to() {
        // 1 is above ]-inf, 1[
        assert_eq!(1.rcmp(..1), RangeOrdering::Above);
        assert_eq!(1.rcmp(..&1), RangeOrdering::Above);

        // 1 is inside ]-inf, 2[
        assert_eq!(1.rcmp(..2), RangeOrdering::Inside);
        assert_eq!(1.rcmp(..&2), RangeOrdering::Inside);
    }

    #[test]
    fn range() {
        // 1 is above [0, 1[
        assert_eq!(1.rcmp(0..1), RangeOrdering::Above);
        assert_eq!(1.rcmp(&0..&1), RangeOrdering::Above);

        // 1 is inside [1, 2[
        assert_eq!(1.rcmp(1..2), RangeOrdering::Inside);
        assert_eq!(1.rcmp(&1..&2), RangeOrdering::Inside);

        // 1 is below [2, 3[
        assert_eq!(1.rcmp(2..3), RangeOrdering::Below);
        assert_eq!(1.rcmp(&2..&3), RangeOrdering::Below);
    }

    #[test]
    fn range_inclusive() {
        // 1 is above [0, 0]
        assert_eq!(1.rcmp(0..=0), RangeOrdering::Above);
        assert_eq!(1.rcmp(&0..=&0), RangeOrdering::Above);

        // 1 is inside [1, 1]
        assert_eq!(1.rcmp(1..=1), RangeOrdering::Inside);
        assert_eq!(1.rcmp(&1..=&1), RangeOrdering::Inside);

        // 1 is below [2, 2]
        assert_eq!(1.rcmp(2..=2), RangeOrdering::Below);
        assert_eq!(1.rcmp(&2..=&2), RangeOrdering::Below);
    }

    #[test]
    fn range_to_inclusive() {
        // 1 is above ]-inf, 0]
        assert_eq!(1.rcmp(..=0), RangeOrdering::Above);
        assert_eq!(1.rcmp(..=&0), RangeOrdering::Above);

        // 1 is inside ]-inf, 1
        assert_eq!(1.rcmp(..=1), RangeOrdering::Inside);
        assert_eq!(1.rcmp(..=&1), RangeOrdering::Inside);
    }

    #[test]
    fn bounds_full() {
        // 1 is inside ]-inf, inf[
        let bounds: (Bound<i32>, Bound<i32>) = (Bound::Unbounded, Bound::Unbounded);
        assert_eq!(1.rcmp(bounds), RangeOrdering::Inside);
    }

    #[test]
    fn bounds_from() {
        // 1 is inside [1, +inf[
        let bounds = (Bound::Included(1), Bound::Unbounded);
        assert_eq!(1.rcmp(bounds), RangeOrdering::Inside);

        let bounds = (Bound::Included(&1), Bound::Unbounded);
        assert_eq!(1.rcmp(bounds), RangeOrdering::Inside);

        // 1 is below [2, +inf[
        let bounds = (Bound::Included(2), Bound::Unbounded);
        assert_eq!(1.rcmp(bounds), RangeOrdering::Below);

        let bounds = (Bound::Included(&2), Bound::Unbounded);
        assert_eq!(1.rcmp(bounds), RangeOrdering::Below);
    }

    #[test]
    fn bounds_to() {
        // 1 is above ]-inf, 1[
        let bounds = (Bound::Unbounded, Bound::Excluded(1));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Above);

        let bounds = (Bound::Unbounded, Bound::Excluded(&1));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Above);

        // 1 is inside ]-inf, 2[
        let bounds = (Bound::Unbounded, Bound::Excluded(2));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Inside);

        let bounds = (Bound::Unbounded, Bound::Excluded(&2));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Inside);
    }

    #[test]
    fn bounds() {
        // 1 is above [0, 1[
        let bounds = (Bound::Included(0), Bound::Excluded(1));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Above);

        let bounds = (Bound::Included(&0), Bound::Excluded(&1));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Above);

        // 1 is inside [1, 2[
        let bounds = (Bound::Included(1), Bound::Excluded(2));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Inside);

        let bounds = (Bound::Included(&1), Bound::Excluded(&2));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Inside);

        // 1 is below [2, 3[
        let bounds = (Bound::Included(2), Bound::Excluded(3));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Below);

        let bounds = (Bound::Included(&2), Bound::Excluded(&3));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Below);
    }

    #[test]
    fn bounds_inclusive() {
        // 1 is above [0, 0]
        let bounds = (Bound::Included(0), Bound::Included(0));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Above);

        let bounds = (Bound::Included(&0), Bound::Included(&0));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Above);

        // 1 is inside [1, 1]
        let bounds = (Bound::Included(1), Bound::Included(1));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Inside);

        let bounds = (Bound::Included(&1), Bound::Included(&1));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Inside);

        // 1 is below [2, 2]
        let bounds = (Bound::Included(2), Bound::Included(2));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Below);

        let bounds = (Bound::Included(&2), Bound::Included(&2));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Below);
    }

    #[test]
    fn bounds_to_inclusive() {
        // 1 is above ]-inf, 0]
        let bounds = (Bound::Unbounded, Bound::Included(0));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Above);

        let bounds = (Bound::Unbounded, Bound::Included(&0));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Above);

        // 1 is inside ]-inf, 1]
        let bounds = (Bound::Unbounded, Bound::Included(1));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Inside);

        let bounds = (Bound::Unbounded, Bound::Included(&1));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Inside);
    }

    #[test]
    fn bounds_exclusive_inclusive() {
        // 1 is above ]-1, 0]
        let bounds: (Bound<i32>, Bound<i32>) = (Bound::Excluded(-1), Bound::Included(0));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Above);

        let bounds: (Bound<&i32>, Bound<&i32>) = (Bound::Excluded(&-1), Bound::Included(&0));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Above);

        // 1 is inside ]0, 1]
        let bounds: (Bound<i32>, Bound<i32>) = (Bound::Excluded(0), Bound::Included(1));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Inside);

        let bounds: (Bound<&i32>, Bound<&i32>) = (Bound::Excluded(&0), Bound::Included(&1));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Inside);

        // 1 is below ]1, 2]
        let bounds: (Bound<i32>, Bound<i32>) = (Bound::Excluded(1), Bound::Included(2));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Below);

        let bounds: (Bound<&i32>, Bound<&i32>) = (Bound::Excluded(&1), Bound::Included(&2));
        assert_eq!(1.rcmp(bounds), RangeOrdering::Below);
    }

    #[test]
    fn bounds_as_reference() {
        let bounds = 0..2;
        assert_eq!(1.rcmp(&bounds), RangeOrdering::Inside);
        assert_eq!(1.rcmp(bounds), RangeOrdering::Inside);
    }

    #[test]
    fn empty_ranges() {
        // 0 is above [0, 0[
        assert_eq!(0.rcmp(0..0), RangeOrdering::Above);
        assert_eq!(0.rcmp(&0..&0), RangeOrdering::Above);

        // 0u32 is above [-inf, 0u32[
        assert_eq!(0.rcmp(..0u32), RangeOrdering::Above);
        assert_eq!(0.rcmp(..&0u32), RangeOrdering::Above);

        // 30 is below [45, 35[
        assert_eq!(30.rcmp(45..35), RangeOrdering::Below);
        assert_eq!(30.rcmp(&45..&35), RangeOrdering::Below);

        // 30 is above [25, 15[
        assert_eq!(30.rcmp(25..15), RangeOrdering::Above);
        assert_eq!(30.rcmp(&25..&15), RangeOrdering::Above);
    }
}
