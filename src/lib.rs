#![forbid(missing_docs)]
#![feature(thread_spawn_unchecked)]
#![feature(slice_split_at_unchecked)]

#![doc = include_str!("../README.md")]

mod raw;
/// Various chunked iterator types.
pub mod iter;

use raw::spawn_threads;
use std::cell::Cell;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread::available_parallelism;

/// Extension trait that provides utilities for chunking up iterators.
///
/// # Implementation Details
/// Implementors of [`Divvy`] in this crate produce chunks according to the
/// following formula:
/// ```rust
/// use std::iter::repeat;
///
/// // `t` is the number of items
/// // `n` is the number of chunks to produce
/// fn get_chunk_sizes(t: usize, n: usize) -> impl Iterator<Item = usize> {
///     assert_ne!(n, 0, "must have nonzero chunks");
///     let q = t / n;
///     let r = t % n;
///     repeat(q + 1)
///         .take(r)
///         .chain(repeat(q).take((t - r * (q + 1)).checked_div(q).unwrap_or(0)))
/// }
/// ```
/// This guarantees that the chunk sizes will differ by at most one. If `t < n`,
/// then only `t` chunks of size `1` are produced. If `t == 0`, no chunks are
/// produced.
pub trait Divvy
where
    Self::Output: Iterator<Item = Self::Chunk>,
    Self: Sized,
{
    /// A type that gets sent to independent threads.
    type Chunk;
    /// An iterator that yields chunks.
    type Output;
    /// Chunks up an iterator into _at most_ `n` chunks (see [here](`crate::Divvy#implementation-details`)
    /// for implementation details).
    ///
    /// # Panics
    /// Implementors in this crate will panic if `n` is zero. Implementors for
    /// ranges over primitive types will also panic if `n` doesn't fit in
    /// the respective primitive type.
    fn divvy(self, n: usize) -> Self::Output;
    /// Convenience method that passes a reasonable number of threads to
    /// [`divvy`](`Divvy::divvy`) based on the available parallelism of the
    /// host platform. In most cases, this is the number of logical cores --
    /// see the docs of [`available_parallelism`](`std::thread::available_parallelism`)
    /// for details.
    ///
    /// # Panics
    /// Panics if [`available_parallelism`](`std::thread::available_parallelism`)
    /// returns an error. The panicking conditions for [`divvy`](`Divvy::divvy`) also apply.
    fn divvy_cpus(self) -> Self::Output {
        self.divvy(available_parallelism().unwrap().get())
    }
}

/// Extension trait that provides utilities for iterating over chunked iterators in parallel. 
///
/// # Implementation Note
/// These methods will create a new thread for each chunk, so prefer to use
/// chunks produced by [`divvy_cpus`](`Divvy::divvy_cpus`) over
/// [`divvy`](`Divvy::divvy`) unless you need finer control. 
///
/// # Panics
/// The provided default methods will panic if thread creation fails or if the
/// closure arguments panic.
pub trait IteratorExt<T, C>
where
    Self: Iterator<Item = C> + Sized,
    C: IntoIterator<Item = T> + Send,
{
    /// Calls a closure on each element of each chunk.
    ///
    /// # Implementation Details
    ///
    /// The order in which calls occur relative to
    /// each other is unspecified and should not be relied on.
    ///
    /// # Example
    /// ```rust
    /// # use rayoff::*;
    /// (0..1000usize).divvy_cpus().par_for_each(|x| {
    ///     if x.is_power_of_two() {
    ///         println!("{} is a power of 2", x);
    ///     }
    /// });
    /// ```
    fn par_for_each(self, f: impl Fn(T) + Sync) {
        let f = &f;
        let panicked = &Cell::new(false);
        spawn_threads(self, |chunk| chunk.into_iter().for_each(f), drop, panicked)
    }
    /// Calls a closure on each element of each chunk, returning the mapped
    /// value if the call returns [`Some`].
    ///
    /// # Implementation Details
    ///
    /// When one thread finds a [`Some`], the other threads will stop iteration
    /// on a best-effort basis. It is not an error for multiple calls to
    /// successfully find a value, but only one will be returned -- the
    /// choice is unspecified and should not be relied on.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use rayoff::*;
    /// let arr = ["one", "2", "three", "4", "5"];
    /// let result = arr
    ///     .divvy_cpus()
    ///     .find_map_any(|x| x.parse::<usize>().ok())
    ///     .unwrap();
    ///
    /// assert!(result == 2 || result == 3 || result == 4);
    /// ```
    fn find_map_any<F, U>(self, f: F) -> Option<U>
    where
        F: Fn(T) -> Option<U> + Sync,
        U: Send,
    {
        let f = &f;
        let done = &AtomicBool::new(false);
        let panicked = &Cell::new(false);
        spawn_threads(
            self,
            |chunk| {
                // We manually implement find_map(), so we can truly return early.
                for x in chunk {
                    // We don't make any guarantees on when we stop iteration, so
                    // Ordering::Relaxed is fine (we just need atomicity).
                    if done.load(Ordering::Relaxed) {
                        return None;
                    } else {
                        let ret = f(x);
                        if ret.is_some() {
                            done.store(true, Ordering::Relaxed);
                            return ret;
                        }
                    }
                }
                None
            },
            |mut x| x.find_map(|x| x),
            panicked,
        )
    }
    /// Calls a closure on each element of each chunk, returning all mapped
    /// values from calls that return [`Some`].
    ///
    /// # Implementation Details
    /// Iteration will halt when all chunks are exhausted.
    /// The order of returned values is unspecified and should not be relied on.
    /// # Example
    ///
    /// ```rust
    /// # use rayoff::*;
    /// let arr = ["one", "2", "three", "4", "5"];
    /// let result = arr
    ///     .divvy_cpus()
    ///     .find_map_all(|x| x.parse::<usize>().ok());
    ///
    /// assert!(result.contains(&2));
    /// assert!(result.contains(&4));
    /// assert!(result.contains(&5));
    /// ```
    fn find_map_all<F, U>(self, f: F) -> Vec<U>
    where
        F: Fn(T) -> Option<U> + Sync,
        U: Send,
    {
        let f = &f;
        let panicked = &Cell::new(false);
        spawn_threads(
            self,
            |chunk| chunk.into_iter().filter_map(f).collect::<Vec<_>>(),
            |x| x.into_iter().flat_map(|x| x.into_iter()).collect(),
            panicked,
        )
    }
    /// Returns the first element that matches the provided predicate, if any.
    ///
    /// # Implementation Details
    /// When one thread finds a match, the other threads will stop iteration on
    /// a best-effort basis. It is not an error for multiple calls to find a
    /// matching element, but only one will be returned -- the choice is
    /// unspecified and should not be relied on.
    ///
    /// # Example
    /// ```rust
    /// # use rayoff::*;
    /// let result = (0..1000usize)
    ///     .divvy_cpus()
    ///     .find_any(|x| x.is_power_of_two());
    ///
    /// assert!(result.unwrap().is_power_of_two());
    /// ```
    fn find_any<F>(self, f: F) -> Option<T>
    where
        F: Fn(&T) -> bool + Sync,
        T: Send,
    {
        self.find_map_any(|x| f(&x).then(move || x))
    }
    /// Returns all elements that matches the provided predicate.
    ///
    /// # Implementation Details
    /// Iteration will halt when all chunks are exhausted. The order of returned
    /// values is unspecified and should not be relied on.
    ///
    /// # Example
    /// ```rust
    /// # use rayoff::*;
    /// let result = (0..1000usize)
    ///     .divvy_cpus()
    ///     .find_all(|x| x.is_power_of_two());
    ///
    /// assert!(result.iter().all(|x| x.is_power_of_two()));
    /// ```
    fn find_all<F>(self, f: F) -> Vec<T>
    where
        F: Fn(&T) -> bool + Sync,
        T: Send,
    {
        self.find_map_all(|x| f(&x).then(move || x))
    }
    /// Low-level API for manually implementing mapping and reducing.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use rayoff::*;
    /// let sum = (0..1000usize)
    ///     .divvy_cpus()
    ///     .map_reduce(|chunk| chunk.sum::<usize>(), 0usize, |acc, cur| acc + cur);
    ///
    /// assert_eq!(sum, (0..1000usize).sum());
    /// ```
    fn map_reduce<M, R, S, U>(self, map: M, state: S, reduce: R) -> S
    where
        M: Fn(C) -> U + Sync,
        U: Send,
        R: FnMut(S, U) -> S,
    {
        let panicked = &Cell::new(false);
        spawn_threads(self, map, |it| it.fold(state, reduce), panicked)
    }
}

impl<T, C, I> IteratorExt<T, C> for I
where
    I: Iterator<Item = C> + Sized,
    C: IntoIterator<Item = T> + Send,
{
}
