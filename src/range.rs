use crate::Divvy;
use std::fmt::Debug;
use std::iter::FusedIterator;
use std::mem;
use std::ops::Range;

#[derive(Debug)]
/// Created by calling [`Divvy::divvy`]on a [`Range`] of `u8`, `u16`, `u32`,
/// `u64`, `usize`, or `u128`.
pub struct ChunkedRange<T> {
    range: Range<T>,
    step: T,
    threshold: T,
}

macro_rules! impl_unsigned {
    ($($t:ty)+) => {
        $(
            impl Iterator for ChunkedRange<$t> {
                type Item = Range<$t>;
                #[inline]
                fn next(&mut self) -> Option<Self::Item> {
                    let len = self.range.end - self.range.start;
                    if len == 0 {
                        None
                    } else {
                        let step = if len > self.threshold {
                            self.step + 1
                        } else {
                            self.step
                        };
                        let ret = Range {
                            start: self.range.start,
                            end: self.range.start + step,
                        };
                        self.range.start += step;
                        Some(ret)
                    }
                }
            }

            impl FusedIterator for ChunkedRange<$t> {}

            impl Divvy for Range<$t> {
                type Chunk = Range<$t>;
                type Output = ChunkedRange<$t>;

                fn divvy(mut self, n: usize) -> Self::Output {
                    let n = <$t>::try_from(n).expect(concat!("number of chunks must fit in a ", stringify!($t)));
                    assert_ne!(n, 0, "number of chunks must be nonzero");
                    if self.start > self.end {
                        mem::swap(&mut self.start, &mut self.end);
                    }

                    let t = self.end - self.start;
                    let q = t / n;
                    let r = t % n;
                    ChunkedRange {
                        range: self,
                        step: q,
                        threshold: t - r * (q + 1),
                    }
                }
            }
        )+
    }
}

impl_unsigned! {u8 u16 u32 u64 u128 usize}

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
