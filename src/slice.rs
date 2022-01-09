use crate::Divvy;
use core::iter::FusedIterator;
use std::fmt::Debug;
use std::mem::take;

#[derive(Debug)]
pub struct ChunkedSlice<'a, T> {
    slice: &'a [T],
    step: usize,
    threshold: usize,
}

#[derive(Debug)]
pub struct ChunkedSliceMut<'a, T> {
    slice: &'a mut [T],
    step: usize,
    threshold: usize,
}

fn slice_len(len: usize, step: usize, threshold: usize) -> usize {
    if len > threshold {
        let rem = len - threshold;
        // Technically, this could panic from overflow -> division by zero, but getting
        // a step that big should be extremely rare.
        let big = rem / (step + 1);
        big + threshold.checked_div(step).unwrap_or(0)
    } else {
        // We know len <= threshold, so the length consists of just small steps.
        len.checked_div(step).unwrap_or(0)
    }
}

impl<'a, T> ChunkedSlice<'a, T> {
    pub fn new(slice: &'a [T], n: usize) -> Self {
        assert_ne!(n, 0, "number of chunks must be nonzero");
        let t = slice.len();
        let q = t / n;
        let r = t % n;
        ChunkedSlice {
            slice,
            step: q,
            threshold: t - r * (q + 1),
        }
    }
    pub fn len(&self) -> usize {
        slice_len(self.slice.len(), self.step, self.threshold)
    }
}

impl<'a, T> Iterator for ChunkedSlice<'a, T> {
    type Item = &'a [T];
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let len = self.slice.len();
        if len == 0 {
            None
        } else {
            let step = if len > self.threshold {
                self.step + 1
            } else {
                self.step
            };
            // SAFETY: we always have step <= self.slice.len()
            let (ret, new) = unsafe { self.slice.split_at_unchecked(step) };
            self.slice = new;
            Some(ret)
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl<'a, T> ExactSizeIterator for ChunkedSlice<'a, T> {
    #[inline]
    fn len(&self) -> usize {
        self.len()
    }
}

impl<'a, T> FusedIterator for ChunkedSlice<'a, T> {}

impl<'a, T> ChunkedSliceMut<'a, T> {
    pub fn new(slice: &'a mut [T], n: usize) -> Self {
        assert_ne!(n, 0, "number of chunks must be nonzero");
        let t = slice.len();
        let q = t / n;
        let r = t % n;
        ChunkedSliceMut {
            slice,
            step: q,
            threshold: t - r * (q + 1),
        }
    }
    pub fn len(&self) -> usize {
        slice_len(self.slice.len(), self.step, self.threshold)
    }
}

impl<'a, T> Iterator for ChunkedSliceMut<'a, T> {
    type Item = &'a mut [T];
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let len = self.slice.len();
        if len == 0 {
            None
        } else {
            let step = if len > self.threshold {
                self.step + 1
            } else {
                self.step
            };
            let tmp = take(&mut self.slice);
            // SAFETY: we always have step <= self.slice.len()
            let (ret, new) = unsafe { tmp.split_at_mut_unchecked(step) };
            self.slice = new;
            Some(ret)
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl<'a, T> ExactSizeIterator for ChunkedSliceMut<'a, T> {
    #[inline]
    fn len(&self) -> usize {
        self.len()
    }
}

impl<'a, T> FusedIterator for ChunkedSliceMut<'a, T> {}

impl<'a, T> Divvy for &'a [T] {
    type Chunk = &'a [T];
    type Output = ChunkedSlice<'a, T>;
    fn divvy(self, n: usize) -> Self::Output {
        ChunkedSlice::new(self, n)
    }
}

impl<'a, T> Divvy for &'a mut [T] {
    type Chunk = &'a mut [T];
    type Output = ChunkedSliceMut<'a, T>;
    fn divvy(self, n: usize) -> Self::Output {
        ChunkedSliceMut::new(self, n)
    }
}

#[cfg(test)]
mod tests {
    use crate::Divvy;
    #[test]
    fn t_lt_n() {
        const T: usize = 3;
        const N: usize = 4;
        let mut arr = [0usize; T];
        for (i, s) in arr.iter_mut().enumerate() {
            *s = i;
        }
        let mut arr = arr.divvy(N);
        assert_eq!(arr.next(), Some(&[0][..]));
        assert_eq!(arr.next(), Some(&[1][..]));
        assert_eq!(arr.next(), Some(&[2][..]));
        assert_eq!(arr.next(), None);
    }
    #[test]
    fn t_eq_n() {
        const T: usize = 4;
        const N: usize = 4;
        let mut arr = [0usize; T];
        for (i, s) in arr.iter_mut().enumerate() {
            *s = i;
        }
        let mut arr = arr.divvy(N);
        assert_eq!(arr.next(), Some(&[0][..]));
        assert_eq!(arr.next(), Some(&[1][..]));
        assert_eq!(arr.next(), Some(&[2][..]));
        assert_eq!(arr.next(), Some(&[3][..]));
        assert_eq!(arr.next(), None);
    }
    #[test]
    fn t_gt_n() {
        const T: usize = 5;
        const N: usize = 4;
        let mut arr = [0usize; T];
        for (i, s) in arr.iter_mut().enumerate() {
            *s = i;
        }
        let mut arr = arr.divvy(N);
        assert_eq!(arr.next(), Some(&[0, 1][..]));
        assert_eq!(arr.next(), Some(&[2][..]));
        assert_eq!(arr.next(), Some(&[3][..]));
        assert_eq!(arr.next(), Some(&[4][..]));
        assert_eq!(arr.next(), None);
    }
    #[test]
    fn n_divides_t() {
        const T: usize = 8;
        const N: usize = 4;
        let mut arr = [0usize; T];
        for (i, s) in arr.iter_mut().enumerate() {
            *s = i;
        }
        let mut arr = arr.divvy(N);
        assert_eq!(arr.next(), Some(&[0, 1][..]));
        assert_eq!(arr.next(), Some(&[2, 3][..]));
        assert_eq!(arr.next(), Some(&[4, 5][..]));
        assert_eq!(arr.next(), Some(&[6, 7][..]));
        assert_eq!(arr.next(), None);
    }
    #[test]
    fn realistic() {
        const T: usize = 10180;
        const N: usize = 8;
        let mut arr = [0usize; T].divvy(N);
        assert_eq!(arr.next().unwrap().len(), 1273);
        assert_eq!(arr.next().unwrap().len(), 1273);
        assert_eq!(arr.next().unwrap().len(), 1273);
        assert_eq!(arr.next().unwrap().len(), 1273);
        assert_eq!(arr.next().unwrap().len(), 1272);
        assert_eq!(arr.next().unwrap().len(), 1272);
        assert_eq!(arr.next().unwrap().len(), 1272);
        assert_eq!(arr.next().unwrap().len(), 1272);
        assert_eq!(arr.next(), None);
    }
    #[test]
    fn t_lt_n_len() {
        const T: usize = 3;
        const N: usize = 4;
        let mut arr = [0usize; T].divvy(N);
        assert_eq!(arr.len(), 3);
        arr.next().unwrap();
        assert_eq!(arr.len(), 2);
        arr.next().unwrap();
        assert_eq!(arr.len(), 1);
        arr.next().unwrap();
        assert_eq!(arr.len(), 0);
        assert_eq!(arr.next(), None);
    }
    #[test]
    fn t_eq_n_len() {
        const T: usize = 4;
        const N: usize = 4;
        let mut arr = [0usize; T].divvy(N);
        assert_eq!(arr.len(), 4);
        arr.next().unwrap();
        assert_eq!(arr.len(), 3);
        arr.next().unwrap();
        assert_eq!(arr.len(), 2);
        arr.next().unwrap();
        assert_eq!(arr.len(), 1);
        arr.next().unwrap();
        assert_eq!(arr.len(), 0);
        assert_eq!(arr.next(), None);
    }
    #[test]
    fn t_gt_n_len() {
        const T: usize = 5;
        const N: usize = 4;
        let mut arr = [0usize; T].divvy(N);
        assert_eq!(arr.len(), 4);
        arr.next().unwrap();
        assert_eq!(arr.len(), 3);
        arr.next().unwrap();
        assert_eq!(arr.len(), 2);
        arr.next().unwrap();
        assert_eq!(arr.len(), 1);
        arr.next().unwrap();
        assert_eq!(arr.len(), 0);
        assert_eq!(arr.next(), None);
    }
}
