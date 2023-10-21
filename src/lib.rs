use std::ops::RangeBounds;

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
