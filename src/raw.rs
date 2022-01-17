use std::cell::Cell;
use std::iter::Map;
use std::thread::{Builder, JoinHandle};
use std::vec::IntoIter;

/// Wrapper type around the JoinGuard iterator to ensure it runs to completion,
/// even if the calling thread panics. This ensures that the invariant of
/// spawn_unchecked() is upheld when we panic while reducing.
pub(crate) struct IteratorGuard<'a, T: Send>(
    #[allow(clippy::type_complexity)]
    Map<IntoIter<JoinGuard<'a, T>>, fn(JoinGuard<'a, T>) -> T>,
);

impl<T: Send> Iterator for IteratorGuard<'_, T> {
    type Item = T;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<T: Send> Drop for IteratorGuard<'_, T> {
    fn drop(&mut self) {
        // We manually need to exhaust the iterator. The joining logic is deferred to
        // the Drop impl of JoinGuard.
        while self.0.next().is_some() {}
    }
}

/// Wrapper type around JoinHandle to ensure a thread is joined, even if the
/// calling thread panics. This ensures that the invariant of spawn_unchecked()
/// is upheld when spawn_unchecked().unwrap() panics.
struct JoinGuard<'a, T: Send> {
    handle: Option<JoinHandle<T>>,
    panicked: &'a Cell<bool>,
}

impl<'a, T: Send> JoinGuard<'a, T> {
    fn new(handle: JoinHandle<T>, panicked: &'a Cell<bool>) -> Self {
        Self {
            handle: Some(handle),
            panicked,
        }
    }
    fn join(mut self) -> T {
        // SAFETY: take() will always return Some since this join() is the only way to
        // acquire ownership of the handle from safe code (other than the destructer).
        let handle = unsafe { self.handle.take().unwrap_unchecked() };
        // We don't immediately unwrap after joining in case a previous child thread
        // already panicked; this avoids a double panic.
        let ret = handle.join();
        if ret.is_err() {
            self.panicked.set(true);
        }
        ret.unwrap()
        // The destructer here will be a no-op since the handle is now None.
    }
}

impl<T: Send> Drop for JoinGuard<'_, T> {
    fn drop(&mut self) {
        // The handle will still be Some if:
        // 1. We don't exhaust the reducing iterator over the return values. NOTE: this
        //    alone does not satisfy the invariant of joining each thread in this case, 
        //    since Map is lazy (we must explicitly run the iterator to completion).
        // 2. We panicked during collection into a Vec inside spawn_unchecked().unwrap().
        // 3. One of the threads panicked during execution.
        if let Some(x) = self.handle.take() {
            let handle = x.join();
            // If we haven't panicked yet, then we won't have a double panic if we unwrap on
            // an Err here.
            if !self.panicked.get() {
                self.panicked.set(true);
                let _ = handle.unwrap();
            }
        }
    }
}

/// This would be unsound if it were public, since malicious implementations of
/// the reducer could leak the iterator, which would circumvent the guards and
/// allow threads to access freed memory.
// TODO: Instead of the &Cell<bool> nonsense, we could just collect the joined
// handles into a Vec<Result<T, _>>, then map over the unwrapped values. This
// kills 2 birds with one stone; we get guaranteed safety (this would be allowed
// to be public), and we wouldn't need to keep track of whether or not we
// panicked. This would need to be benched, though.
pub(crate) fn spawn_threads<'a, I, M, R, T, U, V>(
    it: I,
    map: M,
    reduce: R,
    panicked: &'a Cell<bool>,
) -> V
where
    I: Iterator<Item = T>,
    I::Item: Send,
    M: Fn(I::Item) -> U + Sync,
    U: Send,
    R: FnOnce(IteratorGuard<'a, U>) -> V,
{
    let map = &map;
    let it = it
        .map(|chunk| {
            // SAFETY: The guard ensures the thread is joined before any referenced locals
            // go out of scope.  We move to prevent `chunk` from going out of scope.
            let handle = unsafe { Builder::new().spawn_unchecked(move || map(chunk)).unwrap() };
            JoinGuard::new(handle, panicked)
        })
        // This allocation is necessary because we need to create all of the handles before we can
        // join them (otherwise, we would block on the first thread and get no parallelism).
        .collect::<Vec<_>>()
        .into_iter()
        .map(JoinGuard::join as _);
    reduce(IteratorGuard(it))
}
