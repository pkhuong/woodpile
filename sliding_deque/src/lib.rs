//! The `sliding_deque` crate defines the [`SlidingDeque`] and
//! [`SortedDeque`] container wrappers.
//!
//! The base [`SlidingDeque`] is similar to the standard [`VecDeque`],
//! but only allows pushing to the back of the queue (consumers can
//! still pull from both ends), and always keeps the elements ordered
//! in a single contiguous slice.  Unlike [`VecDeque`],
//! `[SlidingDeque`] is defined as a wrapper over an arbitrary
//! container type; this crate comes with support for [`Vec`] for the
//! regular case, and [`SmallVec`] for queues that are usually small.
//!
//! A [`SlidingDeque`] may only be used on (mem)Copy-able items, and
//! tends to waste more memory than a regular `VecDeque`.  The constant
//! factors may however be lower for `SlidingDeque` than `VecDeque`,
//! especially for workloads that benefit from the ability to access
//! all the elements in a single ordered slice.
//!
//! The [`SortedDeque`] wrapper extends the [`SlidingDeque`] to simple
//! use cases where items are always inserted in sorted order, and
//! *usually* but not always removed from the ends (e.g., in FIFO
//! order).  It makes the most sense for small datasets, when storing
//! the sorted collection in, e.g., a [`SmallVec`], is important.
//!
//! [`VecDeque`]: [`std::collection::VecDeque`]
//! [`SmallVec`]: [`smallvec::SmallVec`]

mod sliding_deque;
mod sorted_deque;

pub use sliding_deque::PushTruncateContainer;
pub use sliding_deque::SlidingDeque;
pub use sliding_deque::SlidingSmallVec;
pub use sliding_deque::SlidingVec;

pub use sorted_deque::SortedDeque;
pub use sorted_deque::SortedDequeComparator;
pub use sorted_deque::SortedDequeItem;
pub use sorted_deque::SortedDequeMarker;
