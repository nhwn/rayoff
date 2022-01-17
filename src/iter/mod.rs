mod range;
mod slice;
mod inclusive;

pub use range::{
    ChunkedRangeU8,
    ChunkedRangeI8,
    ChunkedRangeU16,
    ChunkedRangeI16,
    ChunkedRangeU32,
    ChunkedRangeI32,
    ChunkedRangeU64,
    ChunkedRangeI64,
    ChunkedRangeUsize,
    ChunkedRangeIsize,
};
pub use slice::{ChunkedSlice, ChunkedSliceMut};
pub use inclusive::{
    ChunkedRangeInclusiveU8,
    ChunkedRangeInclusiveI8,
    ChunkedRangeInclusiveU16,
    ChunkedRangeInclusiveI16,
    ChunkedRangeInclusiveU32,
    ChunkedRangeInclusiveI32,
    ChunkedRangeInclusiveU64,
    ChunkedRangeInclusiveI64,
    ChunkedRangeInclusiveUsize,
    ChunkedRangeInclusiveIsize,
};

