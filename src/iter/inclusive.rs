use crate::Divvy;
use std::ops::RangeInclusive;
use std::iter::FusedIterator;
use std::mem;

macro_rules! impl_inclusive {
    ($($(#[$m:meta])? $name:ident, $t:ty, $wide:ty)+) => {
        $(
            $(#[$m])?
            #[derive(Debug)]
            #[doc = concat!("Created by calling [`divvy`](`Divvy::divvy`) on a [`RangeInclusive<", stringify!($t),">`].")]
            pub struct $name {
                start: $wide,
                end: $wide,
                threshold: $wide,
                step: $wide,
            }
            $(#[$m])?
            impl Iterator for $name {
                type Item = RangeInclusive<$t>;
                #[inline]
                fn next(&mut self) -> Option<Self::Item> {
                    let len = self.end - self.start;
                    if len == 0 {
                        None
                    } else {
                        let step = if len > self.threshold {
                            self.step + 1
                        } else {
                            self.step
                        };
                        // The -1 accounts for the inclusive upper bound.
                        let ret = self.start as $t..=(self.start + step - 1) as $t;
                        self.start += step;
                        Some(ret)
                    }
                }
                #[inline]
                fn size_hint(&self) -> (usize, Option<usize>) {
                    let len = self.end - self.start;
                    let len = if len > self.threshold {
                        let rem = len - self.threshold;
                        let big = rem / (self.step + 1);
                        big + self.threshold.checked_div(self.step).unwrap_or(0)
                    } else {
                        len.checked_div(self.step).unwrap_or(0)
                    };
                    if let Some(len) = usize::try_from(len).ok() {
                        (len, Some(len))
                    } else {
                        (usize::MAX, None)
                    }
                }
            }
            $(#[$m])?
            impl FusedIterator for $name {}
            $(#[$m])?
            impl Divvy for RangeInclusive<$t> {
                type Chunk = RangeInclusive<$t>;
                type Output = $name;

                fn divvy(self, n: usize) -> Self::Output {
                    let n = <$t>::try_from(n).expect(concat!("number of chunks must fit in a ", stringify!($t))) as $wide;
                    assert_ne!(n, 0, "number of chunks must be nonzero");
                    let (mut start, mut end) = self.into_inner();
                    if start > end {
                        mem::swap(&mut start, &mut end);
                    }
                    let start = start as $wide;
                    // The +1 accounts for the inclusive upper bound.
                    let end = end as $wide + 1;
                     
                    let t = end - start;
                    let q = t / n;
                    let r = t % n;
                    $name {
                        start,
                        end,
                        step: q,
                        threshold: t - r * (q + 1),
                    }
                }
            }
        )+
    }
}

impl_inclusive! {
    ChunkedRangeInclusiveU8, u8, u16
    ChunkedRangeInclusiveU16, u16, u32
    ChunkedRangeInclusiveU32, u32, u64
    ChunkedRangeInclusiveU64, u64, u128
    #[cfg(target_pointer_width = "64")]
    ChunkedRangeInclusiveUsize, usize, u128
    #[cfg(target_pointer_width = "32")]
    ChunkedRangeInclusiveUsize, usize, u64
    #[cfg(target_pointer_width = "16")]
    ChunkedRangeInclusiveUsize, usize, u32
    ChunkedRangeInclusiveI8, i8, i16
    ChunkedRangeInclusiveI16, i16, i32
    ChunkedRangeInclusiveI32, i32, i64
    ChunkedRangeInclusiveI64, i64, i128
    #[cfg(target_pointer_width = "64")]
    ChunkedRangeInclusiveIsize, isize, i128
    #[cfg(target_pointer_width = "32")]
    ChunkedRangeInclusiveIsize, isize, i64
    #[cfg(target_pointer_width = "16")]
    ChunkedRangeInclusiveIsize, isize, i32
    // TODO: support u128 and i128
}

#[cfg(test)]
mod test {
    use crate::Divvy;

    #[test]
    fn t_lt_n() {
        const T: usize = 2;
        const N: usize = 4;
        let mut it = (0..=T).divvy(N);
        assert_eq!(it.next(), Some(0..=0));
        assert_eq!(it.next(), Some(1..=1));
        assert_eq!(it.next(), Some(2..=2));
        assert_eq!(it.next(), None);
    }
    #[test]
    fn t_eq_n() {
        const T: usize = 3;
        const N: usize = 4;
        let mut it = (0..=T).divvy(N);
        assert_eq!(it.next(), Some(0..=0));
        assert_eq!(it.next(), Some(1..=1));
        assert_eq!(it.next(), Some(2..=2));
        assert_eq!(it.next(), Some(3..=3));
        assert_eq!(it.next(), None);
    }
    #[test]
    fn t_gt_n() {
        const T: usize = 4;
        const N: usize = 4;
        let mut it = (0..=T).divvy(N);
        assert_eq!(it.next(), Some(0..=1));
        assert_eq!(it.next(), Some(2..=2));
        assert_eq!(it.next(), Some(3..=3));
        assert_eq!(it.next(), Some(4..=4));
        assert_eq!(it.next(), None);
    }
    #[test]
    fn n_divides_t() {
        const T: usize = 7;
        const N: usize = 4;
        let mut it = (0..=T).divvy(N);
        assert_eq!(it.next(), Some(0..=1));
        assert_eq!(it.next(), Some(2..=3));
        assert_eq!(it.next(), Some(4..=5));
        assert_eq!(it.next(), Some(6..=7));
        assert_eq!(it.next(), None);
    }
    #[test]
    fn realistic() {
        const T: usize = 10179;
        const N: usize = 8;
        let mut it = (0..=T).divvy(N);
        assert_eq!(it.next(), Some(1273 * 0..=1273 * 1 - 1));
        assert_eq!(it.next(), Some(1273 * 1..=1273 * 2 - 1));
        assert_eq!(it.next(), Some(1273 * 2..=1273 * 3 - 1));
        assert_eq!(it.next(), Some(1273 * 3..=1273 * 4 - 1));
        assert_eq!(it.next(), Some(1273 * 4 + 1272 * 0..=1273 * 4 + 1272 * 1 - 1));
        assert_eq!(it.next(), Some(1273 * 4 + 1272 * 1..=1273 * 4 + 1272 * 2 - 1));
        assert_eq!(it.next(), Some(1273 * 4 + 1272 * 2..=1273 * 4 + 1272 * 3 - 1));
        assert_eq!(it.next(), Some(1273 * 4 + 1272 * 3..=1273 * 4 + 1272 * 4 - 1));
        assert_eq!(it.next(), None);
    }
}
