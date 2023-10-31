use std::borrow::Borrow;
use std::ops::{Bound, RangeBounds};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum RangeOrdering {
    Below,
    Inside,
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
/// With concrete type such as [`i32`], this would be achieved by taking a generic type `T` with the
/// bound `T: Bound<i32>`. So we might be tempted to do the same with the
/// [`RangeBounds`](std::ops::RangeBounds) trait:
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

pub trait RangeComparable {
    fn range_cmp<R: RangeBounds<Self>, B: BorrowRange<Self, R>>(&self, range: B) -> RangeOrdering;
}

impl<T: PartialOrd> RangeComparable for T {
    fn range_cmp<R: RangeBounds<Self>, B: BorrowRange<Self, R>>(&self, range: B) -> RangeOrdering {
        let range = range.borrow();
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
        RangeOrdering::Inside
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn range_full() {
        // 1 is inside ]-inf, inf[
        assert_eq!(1.range_cmp(..), RangeOrdering::Inside);
    }

    #[test]
    fn range_from() {
        // 1 is inside [1, +inf[
        assert_eq!(1.range_cmp(1..), RangeOrdering::Inside);
        assert_eq!(1.range_cmp(&1..), RangeOrdering::Inside);

        // 1 is below [2, +inf[
        assert_eq!(1.range_cmp(2..), RangeOrdering::Below);
        assert_eq!(1.range_cmp(&2..), RangeOrdering::Below);
    }

    #[test]
    fn range_to() {
        // 1 is above ]-inf, 1[
        assert_eq!(1.range_cmp(..1), RangeOrdering::Above);
        assert_eq!(1.range_cmp(..&1), RangeOrdering::Above);

        // 1 is inside ]-inf, 2[
        assert_eq!(1.range_cmp(..2), RangeOrdering::Inside);
        assert_eq!(1.range_cmp(..&2), RangeOrdering::Inside);
    }

    #[test]
    fn range() {
        // 1 is above [0, 1[
        assert_eq!(1.range_cmp(0..1), RangeOrdering::Above);
        assert_eq!(1.range_cmp(&0..&1), RangeOrdering::Above);

        // 1 is inside [1, 2[
        assert_eq!(1.range_cmp(1..2), RangeOrdering::Inside);
        assert_eq!(1.range_cmp(&1..&2), RangeOrdering::Inside);

        // 1 is below [2, 3[
        assert_eq!(1.range_cmp(2..3), RangeOrdering::Below);
        assert_eq!(1.range_cmp(&2..&3), RangeOrdering::Below);
    }

    #[test]
    fn range_inclusive() {
        // 1 is above [0, 0]
        assert_eq!(1.range_cmp(0..=0), RangeOrdering::Above);
        assert_eq!(1.range_cmp(&0..=&0), RangeOrdering::Above);

        // 1 is inside [1, 1]
        assert_eq!(1.range_cmp(1..=1), RangeOrdering::Inside);
        assert_eq!(1.range_cmp(&1..=&1), RangeOrdering::Inside);

        // 1 is below [2, 2]
        assert_eq!(1.range_cmp(2..=2), RangeOrdering::Below);
        assert_eq!(1.range_cmp(&2..=&2), RangeOrdering::Below);
    }

    #[test]
    fn range_to_inclusive() {
        // 1 is above ]-inf, 0]
        assert_eq!(1.range_cmp(..=0), RangeOrdering::Above);
        assert_eq!(1.range_cmp(..=&0), RangeOrdering::Above);

        // 1 is inside ]-inf, 1
        assert_eq!(1.range_cmp(..=1), RangeOrdering::Inside);
        assert_eq!(1.range_cmp(..=&1), RangeOrdering::Inside);
    }

    #[test]
    fn bounds_full() {
        // 1 is inside ]-inf, inf[
        let bounds: (Bound<i32>, Bound<i32>) = (Bound::Unbounded, Bound::Unbounded);
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Inside);
    }

    #[test]
    fn bounds_from() {
        // 1 is inside [1, +inf[
        let bounds = (Bound::Included(1), Bound::Unbounded);
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Inside);

        let bounds = (Bound::Included(&1), Bound::Unbounded);
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Inside);

        // 1 is below [2, +inf[
        let bounds = (Bound::Included(2), Bound::Unbounded);
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Below);

        let bounds = (Bound::Included(&2), Bound::Unbounded);
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Below);
    }

    #[test]
    fn bounds_to() {
        // 1 is above ]-inf, 1[
        let bounds = (Bound::Included(1), Bound::Unbounded);
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Inside);

        let bounds = (Bound::Included(&1), Bound::Unbounded);
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Inside);

        // 1 is inside ]-inf, 2[
        let bounds = (Bound::Included(2), Bound::Unbounded);
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Below);

        let bounds = (Bound::Included(&2), Bound::Unbounded);
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Below);
    }

    #[test]
    fn bounds() {
        // 1 is above [0, 1[
        let bounds = (Bound::Included(0), Bound::Excluded(1));
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Above);

        let bounds = (Bound::Included(&0), Bound::Excluded(&1));
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Above);

        // 1 is inside [1, 2[
        let bounds = (Bound::Included(1), Bound::Excluded(2));
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Inside);

        let bounds = (Bound::Included(&1), Bound::Excluded(&2));
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Inside);

        // 1 is below [2, 3[
        let bounds = (Bound::Included(2), Bound::Excluded(3));
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Below);

        let bounds = (Bound::Included(&2), Bound::Excluded(&3));
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Below);
    }

    #[test]
    fn bounds_inclusive() {
        // 1 is above [0, 0]
        let bounds = (Bound::Included(0), Bound::Included(0));
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Above);

        let bounds = (Bound::Included(&0), Bound::Included(&0));
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Above);

        // 1 is inside [1, 1]
        let bounds = (Bound::Included(1), Bound::Included(1));
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Inside);

        let bounds = (Bound::Included(&1), Bound::Included(&1));
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Inside);

        // 1 is below [2, 2]
        let bounds = (Bound::Included(2), Bound::Included(2));
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Below);

        let bounds = (Bound::Included(&2), Bound::Included(&2));
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Below);
    }

    #[test]
    fn bounds_to_inclusive() {
        // 1 is above ]-inf, 0]
        let bounds = (Bound::Unbounded, Bound::Included(0));
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Above);

        let bounds = (Bound::Unbounded, Bound::Included(&0));
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Above);

        // 1 is inside ]-inf, 1]
        let bounds = (Bound::Unbounded, Bound::Included(1));
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Inside);

        let bounds = (Bound::Unbounded, Bound::Included(&1));
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Inside);
    }

    #[test]
    fn bounds_exclusive_inclusive() {
        // 1 is above ]-1, 0]
        let bounds: (Bound<i32>, Bound<i32>) = (Bound::Excluded(-1), Bound::Included(0));
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Above);

        let bounds: (Bound<&i32>, Bound<&i32>) = (Bound::Excluded(&-1), Bound::Included(&0));
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Above);

        // 1 is inside ]0, 1]
        let bounds: (Bound<i32>, Bound<i32>) = (Bound::Excluded(0), Bound::Included(1));
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Inside);

        let bounds: (Bound<&i32>, Bound<&i32>) = (Bound::Excluded(&0), Bound::Included(&1));
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Inside);

        // 1 is below ]1, 2]
        let bounds: (Bound<i32>, Bound<i32>) = (Bound::Excluded(1), Bound::Included(2));
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Below);

        let bounds: (Bound<&i32>, Bound<&i32>) = (Bound::Excluded(&1), Bound::Included(&2));
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Below);
    }

    #[test]
    fn bounds_as_reference() {
        let bounds = 0..2;
        assert_eq!(1.range_cmp(&bounds), RangeOrdering::Inside);
        assert_eq!(1.range_cmp(bounds), RangeOrdering::Inside);
    }
}
