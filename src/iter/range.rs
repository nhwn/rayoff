use crate::Divvy;
use std::iter::FusedIterator;
use std::ops::Range;
use std::mem;

macro_rules! impl_exclusive {
    ($($(#[$m:meta])? $name:ident, $t:ty, $wide:ty)+) => {
        $(
            $(#[$m])?
            #[derive(Debug)]
            #[doc = concat!("Created by calling [`divvy`](`Divvy::divvy`) on a [`Range<", stringify!($t),">`].")]
            pub struct $name {
                start: $wide,
                end: $wide,
                threshold: $wide,
                step: $wide,
            }
            $(#[$m])?
            impl Iterator for $name {
                type Item = Range<$t>;
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
                        let ret = self.start as $t..(self.start + step) as $t;
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
            impl Divvy for Range<$t> {
                type Chunk = Range<$t>;
                type Output = $name;

                fn divvy(self, n: usize) -> Self::Output {
                    let n = <$t>::try_from(n).expect(concat!("number of chunks must fit in a ", stringify!($t))) as $wide;
                    assert_ne!(n, 0, "number of chunks must be nonzero");
                    let mut start = self.start as $wide;
                    let mut end = self.end as $wide;
                    if start > end {
                        mem::swap(&mut start, &mut end);
                    }
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

impl_exclusive! {
    ChunkedRangeU8, u8, u8
    ChunkedRangeU16, u16, u16
    ChunkedRangeU32, u32, u32
    ChunkedRangeU64, u64, u64
    ChunkedRangeUsize, usize, usize
    ChunkedRangeU128, u128, u128
    ChunkedRangeI8, i8, i16
    ChunkedRangeI16, i16, i32
    ChunkedRangeI32, i32, i64
    ChunkedRangeI64, i64, i128
    #[cfg(target_pointer_width = "64")]
    ChunkedRangeIsize, isize, i128
    #[cfg(target_pointer_width = "32")]
    ChunkedRangeIsize, isize, i64
    #[cfg(target_pointer_width = "16")]
    ChunkedRangeIsize, isize, i32
    // TODO: suport i128
}

#[cfg(test)]
mod test {
    use crate::Divvy;

    #[test]
    fn t_lt_n() {
        const T: usize = 3;
        const N: usize = 4;
        let mut it = (0..T).divvy(N);
        assert_eq!(it.next(), Some(0..1));
        assert_eq!(it.next(), Some(1..2));
        assert_eq!(it.next(), Some(2..3));
        assert_eq!(it.next(), None);
    }
    #[test]
    fn t_eq_n() {
        const T: usize = 4;
        const N: usize = 4;
        let mut it = (0..T).divvy(N);
        assert_eq!(it.next(), Some(0..1));
        assert_eq!(it.next(), Some(1..2));
        assert_eq!(it.next(), Some(2..3));
        assert_eq!(it.next(), Some(3..4));
        assert_eq!(it.next(), None);
    }
    #[test]
    fn t_gt_n() {
        const T: usize = 5;
        const N: usize = 4;
        let mut it = (0..T).divvy(N);
        assert_eq!(it.next(), Some(0..2));
        assert_eq!(it.next(), Some(2..3));
        assert_eq!(it.next(), Some(3..4));
        assert_eq!(it.next(), Some(4..5));
        assert_eq!(it.next(), None);
    }
    #[test]
    fn n_divides_t() {
        const T: usize = 8;
        const N: usize = 4;
        let mut it = (0..T).divvy(N);
        assert_eq!(it.next(), Some(0..2));
        assert_eq!(it.next(), Some(2..4));
        assert_eq!(it.next(), Some(4..6));
        assert_eq!(it.next(), Some(6..8));
        assert_eq!(it.next(), None);
    }
    #[test]
    fn realistic() {
        const T: usize = 10180;
        const N: usize = 8;
        let mut it = (0..T).divvy(N);
        assert_eq!(it.next(), Some(1273 * 0..1273 * 1));
        assert_eq!(it.next(), Some(1273 * 1..1273 * 2));
        assert_eq!(it.next(), Some(1273 * 2..1273 * 3));
        assert_eq!(it.next(), Some(1273 * 3..1273 * 4));
        assert_eq!(it.next(), Some(1273 * 4 + 1272 * 0..1273 * 4 + 1272 * 1));
        assert_eq!(it.next(), Some(1273 * 4 + 1272 * 1..1273 * 4 + 1272 * 2));
        assert_eq!(it.next(), Some(1273 * 4 + 1272 * 2..1273 * 4 + 1272 * 3));
        assert_eq!(it.next(), Some(1273 * 4 + 1272 * 3..1273 * 4 + 1272 * 4));
        assert_eq!(it.next(), None);
    }
}
