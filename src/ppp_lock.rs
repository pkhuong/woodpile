//! The `ppp_lock` module defines traits to access the value in a [`Arc<Mutex<T>>`]
//! with higher-order [`Update<T>::update`] or [`TryUpdate<T>::try_update`]
//! methods.  The higher-order interface lets the methods implement a fast path
//! for single-reference mutable (i.e., exclusively owned) [`Arc`]s.
//!
//! Using the `ppp_lock` traits avoids atomics for private owners (single-reference
//! `&mut Arc<Mutex<T>>`), while incurring marginal additional overhead when the
//! object is actually shared (multi-reference `Arc`)... and the traits, with their
//! higher-order methods, complicate access compared to regular locking.
//!
//! Exposing this logic via extension traits preserves all the usual programming
//! patterns around [`Arc`] and [`Mutex`], including [`Mutex::lock`] on const `&Arc`.
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::MutexGuard;
use std::sync::PoisonError;

/// The value passed to the [`Update<T>::update`] callback: either a mutable
/// reference, or a [`PoisonError`].
pub type UpdateArg<'a, T> = Result<&'a mut T, PoisonError<MutexGuard<'a, T>>>;

/// [`Update`] is a trait to update a mutable value in-place, by calling `f`
/// with a mutable reference to the value.
///
/// There is an implementation for [`Arc<Mutex<T>>`] with a fast path
/// for the single-refcount case.
pub trait Update<T> {
    /// Acquires an exclusive lock on `self` and calls `f` with a
    /// mutable reference to the locked value, or a [`PoisonError`].
    ///
    /// This method may block forever.
    fn update<R>(&mut self, f: impl FnOnce(UpdateArg<T>) -> R) -> R;

    /// Acquires an exclusive lock on `self` and calls `f` with
    /// a mutable reference to the locked value.
    ///
    /// Panics if the lock is poisoned.
    ///
    /// Like [`Update<T>::update`], this method may block forever.
    fn update_or_panic<R>(&mut self, f: impl FnOnce(&mut T) -> R) -> R {
        self.update(|result| f(result.expect("lock poisoned")))
    }
}

/// The value passed to the [`TryUpdate<T>::try_update`] callback: an optional
/// mutable reference, or a [`PoisonError`].
pub type TryUpdateArg<'a, T> = Result<Option<&'a mut T>, PoisonError<MutexGuard<'a, T>>>;

/// [`TryUpdate`] is a trait to update a mutable value in-place, by
/// calling `f` with a mutable reference to the value.  Unlike
/// [`Update::update`], [`TryUpdate::try_update`] is wait-free.
///
/// There is an implementation for [`Arc<Mutex<T>>`] with a fast path
/// for the single-refcount case.
pub trait TryUpdate<T> {
    /// Attempts to acquire an exclusive lock on `self` and calls `f` with a
    /// mutable reference to the locked value if the lock was successfully
    /// acquired, `None` if the operation would block, or a [`PoisonError`].
    ///
    /// This method is wait-free.
    fn try_update<R>(&mut self, cb: impl FnOnce(TryUpdateArg<T>) -> R) -> R;

    /// Attempts to acquire an exclusive lock on `self` and calls `f` with a
    /// mutable reference to the locked value if the lock was successfully
    /// acquired, or `None` if the operation would block.
    ///
    /// Panics if the lock is poisoned.
    ///
    /// This method is wait-free.
    fn try_update_or_panic<R>(&mut self, f: impl FnOnce(Option<&mut T>) -> R) -> R {
        self.try_update(|result| f(result.expect("lock poisoned")))
    }

    /// Attempts to acquire an exclusive lock on `self` and calls `f` with a
    /// mutable reference to the locked value if the lock was successfully
    /// acquired, and `None` otherwise (the operation would block or the lock is
    /// poisoned).
    ///
    /// This method is wait-free.
    fn try_update_flatten<R>(&mut self, f: impl FnOnce(Option<&mut T>) -> R) -> R {
        self.try_update(|result| f(result.ok().flatten()))
    }
}

enum PPPGuard<'life, T> {
    Ref(&'life mut T),
    Guard(MutexGuard<'life, T>),
}

impl<T> Update<T> for Arc<Mutex<T>> {
    fn update<R>(&mut self, f: impl FnOnce(UpdateArg<T>) -> R) -> R {
        let mut wrapper: Result<PPPGuard<T>, _>;

        // Try the happy path.
        if let Some(Ok(reference)) = Arc::get_mut(self).map(Mutex::get_mut) {
            wrapper = Ok(PPPGuard::Ref(reference));
        } else {
            // And just do the slow thing if that doesn't work.
            wrapper = match self.lock() {
                Ok(guard) => Ok(PPPGuard::Guard(guard)),
                Err(e) => Err(e),
            };
        };

        // We need the wrapper to keep the LockGuard alive around the call to `f`.
        let ret: UpdateArg<T> = match wrapper {
            Err(e) => Err(e),
            Ok(ref mut guard) => match guard {
                PPPGuard::Ref(reference) => Ok(reference),
                PPPGuard::Guard(guard) => Ok(guard),
            },
        };
        f(ret)
    }
}

impl<T> TryUpdate<T> for Arc<Mutex<T>> {
    fn try_update<R>(&mut self, f: impl FnOnce(TryUpdateArg<T>) -> R) -> R {
        use std::sync::TryLockError;
        let mut wrapper: Result<Option<PPPGuard<T>>, _>;

        // Try the happy path.
        if let Some(Ok(reference)) = Arc::get_mut(self).map(Mutex::get_mut) {
            wrapper = Ok(Some(PPPGuard::Ref(reference)));
        } else {
            // And just do the slow thing if that doesn't work.
            wrapper = match self.try_lock() {
                Ok(guard) => Ok(Some(PPPGuard::Guard(guard))),
                Err(TryLockError::WouldBlock) => Ok(None),
                Err(TryLockError::Poisoned(poisoned)) => Err(poisoned),
            };
        };

        let ret: TryUpdateArg<T> = match wrapper {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some(ref mut guard)) => match guard {
                PPPGuard::Ref(reference) => Ok(Some(reference)),
                PPPGuard::Guard(guard) => Ok(Some(guard)),
            },
        };
        f(ret)
    }
}

// Exercise the fast (private) path for `update`
#[test]
fn test_update_fast() {
    let mut counter = Arc::new(Mutex::new(0usize));

    assert_eq!(
        counter.update_or_panic(|count| {
            *count += 1;
            *count
        }),
        1
    );
    assert_eq!(*counter.lock().unwrap(), 1);
}

// Exercise the fast (private) path for `try_update`
#[test]
fn test_try_update_fast() {
    let mut counter = Arc::new(Mutex::new(0usize));

    assert_eq!(
        counter.try_update_or_panic(|count| {
            let count = count.expect("must succeed");
            *count += 10;
            2
        }),
        2
    );
    assert_eq!(*counter.lock().unwrap(), 10);
}

// Exercise the slow (shared) path for `update`
#[test]
fn test_update_slow() {
    let mut counter = Arc::new(Mutex::new(0usize));
    let _counter2 = counter.clone();

    assert_eq!(
        counter.update_or_panic(|count| {
            *count += 1;
            *count
        }),
        1
    );
    assert_eq!(*counter.lock().unwrap(), 1);
}

// Exercise the slow (shared) path for `try_update`
#[test]
fn test_try_update_slow() {
    let mut counter = Arc::new(Mutex::new(0usize));
    let _counter2 = counter.clone();

    assert_eq!(
        counter.try_update_flatten(|count| {
            let count = count.expect("must succeed");
            *count += 10;
            2
        }),
        2
    );
    assert_eq!(*counter.lock().unwrap(), 10);
}

// Make sure try_update while locked fails gracefully.
#[test]
fn test_try_update_fail() {
    let mut counter = Arc::new(Mutex::new(0usize));
    let mut counter2 = counter.clone();

    counter.update_or_panic(|count| {
        *count = 42;
        counter2.try_update_or_panic(|count| assert_eq!(count, None));
    });
    assert_eq!(*counter.lock().unwrap(), 42);
    assert_eq!(*counter2.lock().unwrap(), 42);
}
