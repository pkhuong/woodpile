//! The `sliding_deque` crate defines the [`SlidingDeque`] and [`SortedDeque`]
//! container wrappers.
//!
//! The base [`SlidingDeque`] is similar to the standard [`VecDeque`], but
//! only allows pushing to the back of the queue (consumers can still pull
//! from both ends), and always keeps the elements ordered in a single
//! contiguous slice.  Unlike [`VecDeque`], [`SlidingDeque`] is defined as a
//! wrapper over an arbitrary container type; this crate comes with support
//! for [`Vec`] for the regular case, and [`SmallVec`] for queues that are
//! usually small.
//!
//! A [`SlidingDeque`] may only be used on (mem)Copy-able items, and tends to
//! waste more memory than a regular [`VecDeque`], in order to amortise
//! keeping elements in a contiguous slice.  The constant factors may however
//! be lower for [`SlidingDeque`] than [`VecDeque`], especially for workloads
//! that benefit from the ability to access all the elements in a single
//! ordered slice.
//!
//! The [`SortedDeque`] wrapper extends [`SlidingDeque`] to simple use cases
//! where items are always inserted in sorted order, and *usually* but not
//! always removed from the ends (e.g., in FIFO order).  It makes the most
//! sense for small datasets, when storing the sorted collection in, e.g., a
//! [`SmallVec`], is important.
//!
//! # Examples
//!
//! ```rust
//! use sliding_deque::SlidingSmallVec;
//!
//! let mut deque : SlidingSmallVec<[u32; 4]> = SlidingSmallVec::new();
//! deque.push_back(1);
//! deque.push_back(2);
//! assert_eq!(deque.pop_front(), Some(1));
//! assert_eq!(&*deque, &[2]);
//! ```
//!
//! ```rust
//! use sliding_deque::SortedDeque;
//!
//! let mut sorted_deque: SortedDeque<Vec<(u32, Option<()>)>> = Default::default();
//! // Insertions must be in order! It's a programmer error to insert out-of-order,
//! // or to insert the same value twice, so the method panics on violations.
//! sorted_deque.push_back_or_panic((1, Some(())));
//! sorted_deque.push_back_or_panic((3, Some(())));
//! sorted_deque.push_back_or_panic((4, Some(())));
//!
//! assert_eq!(sorted_deque.find(&1), Some(&(1, Some(()))));
//! assert_eq!(sorted_deque.find(&2), None);
//! assert_eq!(sorted_deque.find(&3), Some(&(3, Some(()))));
//! assert_eq!(sorted_deque.find(&4), Some(&(4, Some(()))));
//!
//! sorted_deque.remove(&3);
//! assert_eq!(sorted_deque.find(&3), None);
//!
//! assert_eq!(sorted_deque.pop_first(), Some((1, Some(()))));
//! assert_eq!(sorted_deque.find(&1), None);
//!
//! assert_eq!(sorted_deque.first(), Some(&(4, Some(()))));
//! assert_eq!(sorted_deque.last(), Some(&(4, Some(()))));
//! ```
//!
//! [`VecDeque`]: std::collections::VecDeque
//! [`SmallVec`]: smallvec::SmallVec

mod sliding_deque;
mod sorted_deque;

pub use sliding_deque::SlidingDeque;
pub use sliding_deque::SlidingSmallVec;
pub use sliding_deque::SlidingVec;

pub use sorted_deque::SortedDeque;

pub mod traits {
    //! The `traits` module contains optional traits to extend the default
    //! functionality in the `sliding_deque` crate.
    //!
    //! Basic usage should not need to implement these traits, but they are
    //! useful (the `SortedDeque` traits in particular) for complex use cases.

    pub use crate::sliding_deque::PushTruncateContainer;
    pub use crate::sorted_deque::SortedDequeComparator;
    pub use crate::sorted_deque::SortedDequeItem;
    pub use crate::sorted_deque::SortedDequeMarker;
}
