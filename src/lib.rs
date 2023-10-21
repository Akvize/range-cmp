use std::ops::{Bound, RangeBounds};

#[derive(Debug, Eq, PartialEq)]
pub enum RangeOrdering {
    Below,
    Inside,
    Above,
}

pub trait RangeComparable {
    type T: PartialOrd;
    fn range_cmp<R: RangeBounds<Self::T>>(&self, range: &R) -> RangeOrdering;
}

impl<T: PartialOrd> RangeComparable for T {
    type T = T;
    fn range_cmp<R: RangeBounds<T>>(&self, range: &R) -> RangeOrdering {
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

