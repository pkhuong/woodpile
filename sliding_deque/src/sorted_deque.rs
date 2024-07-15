//! The `sorted_deque` module exposes the [`SortedDeque`]
//! container, as well as associated traits.
//!
//! A [`SortedDeque`] wraps a [`SlidingDeque`] to implement a special
//! case of sorted containers:
//!
//! - values may only be inserted at the end (i.e., in strictly ascending order)
//! - values may be searched (with binary search)
//! - values may be marked as logically deleted, but are only physically deleted
//!   when they're the first or last value in FIFO (sorted) order.
//!
//! Insertion amortises to constant time, lookups are logarithmic time (although
//! we must take into account items that are logically but not yet physically
//! deleted), and deletion takes as much time as a lookup plus some amortised
//! constant-time overhead.
use std::cmp::Ordering;

use crate::sliding_deque::PushTruncateContainer;
use crate::SlidingDeque;

/// In the general case, a [`SortedDeque`] accepts an object that
/// implements the methods we need on an arbitrary type.
///
/// There is a blanket definition for `(Key, Option<Value>)` pairs where
/// the pair is [`Copy`]able, and the `Key` implements [`Ord`].
///
/// There is also a default definition for types that implement
/// [`SortedDequeItem`].
pub trait SortedDequeComparator<T> {
    /// Items have a key for comparisons.  The simple case is
    /// that the whole `T` is the comparison key, but it makes
    /// sense to have a subset of the item as a key, e.g., for
    /// key-value pairs.
    ///
    /// Lookup operations work in terms of `Key`, not `T`.
    type Key;

    /// We can extract a comparison key from an item.
    ///
    /// The key is returned by value to allow complex extraction
    /// logic, and because `T` must be copyable to fit in a
    /// [`SlidingDeque`]
    fn extract_key(&self, item: &T) -> Self::Key;

    /// And we can compare keys.
    fn cmp(&self, x: &Self::Key, y: &Self::Key) -> std::cmp::Ordering;

    /// Check whether an item is erased.
    ///
    /// Defaults to always false; should be overridden when
    /// `SortedDequeMarker` is implemented.
    #[inline(always)]
    fn is_erased(&self, item: &T) -> bool {
        let _ = item;
        false
    }
}

/// A [`SortedDequeMarker`] is a [`SortedDequeComparator`] that can also
/// mark items as deleted.
///
/// There is a blanket definition for `(Key, Option<Value>)` pairs where
/// the pair is [`Copy`]able, and the `Key` implements [`Ord`]: a `None`
/// value represents a logically deleted item.
///
/// There is also a default definition for types that implement
/// [`SortedDequeItem`].
pub trait SortedDequeMarker<T>: SortedDequeComparator<T> {
    /// We can mark an item as erased.
    ///
    /// Implementors of this trait must also implement
    /// [`SortedDequeComparator::is_erased`].
    fn mark_erased(&self, item: &mut T);
}

/// In the simple case [`SortedDeque`] supports any type that
/// implements [`Ord`] and the new `mark_erased` / `is_erased`
/// operations: we'll just compare the whole object.
pub trait SortedDequeItem: Ord {
    /// Marks the item as erased.
    fn mark_erased(&mut self);

    /// Determines wheter the item was erased.
    fn is_erased(&self) -> bool;
}

/// And from `SortedDequeItem`, we can implement a stateless
/// `SortedDequeMarker`.
impl<T: SortedDequeItem + Copy> SortedDequeComparator<T> for () {
    type Key = T;

    #[inline(always)]
    fn extract_key(&self, item: &T) -> T {
        *item
    }

    #[inline(always)]
    fn cmp(&self, x: &T, y: &T) -> Ordering {
        x.cmp(y)
    }

    #[inline(always)]
    fn is_erased(&self, item: &T) -> bool {
        item.is_erased()
    }
}

impl<T: SortedDequeItem + Copy> SortedDequeMarker<T> for () {
    #[inline(always)]
    fn mark_erased(&self, item: &mut T) {
        item.mark_erased();
        assert!(item.is_erased());
    }
}

/// We also have an easy implementation for pairs of key and optional value.
impl<Key: Copy + Ord, Value: Copy> SortedDequeComparator<(Key, Option<Value>)> for () {
    type Key = Key;

    #[inline(always)]
    fn extract_key(&self, item: &(Key, Option<Value>)) -> Key {
        item.0
    }

    #[inline(always)]
    fn cmp(&self, x: &Key, y: &Key) -> Ordering {
        x.cmp(y)
    }

    #[inline(always)]
    fn is_erased(&self, item: &(Key, Option<Value>)) -> bool {
        item.1.is_none()
    }
}

impl<Key: Copy + Ord, Value: Copy> SortedDequeMarker<(Key, Option<Value>)> for () {
    #[inline(always)]
    fn mark_erased(&self, item: &mut (Key, Option<Value>)) {
        item.1 = None;
    }
}

/// A [`SortedDeque`] is a contiguous container wrapped in a restricted
/// sorted container.
///
/// Items may be:
///
/// - inserted in strictly increasing order at the end in amortised constant time
/// - popped from either end in amortised constant time
/// - searched for in logarithmic time (as a function of *physically* live items)
/// - removed in amortised logarithmic time (modulo some additional slowdown
///   in the search until the items are removed physically)
///
/// We could also periodically compact away items that were deleted logically
/// but not yet physically, at an amortised constant-time cost.  That is not
/// currently implemented because we expect most deletions to happen in FIFO
/// order, in which case amortised sweeping is a useless complication.
#[derive(Clone, Debug)]
pub struct SortedDeque<Container, Marker = ()>
where
    Container: PushTruncateContainer + Clone + Default,
    <Container as PushTruncateContainer>::Item: Copy,
    Marker: SortedDequeComparator<<Container as PushTruncateContainer>::Item> + Clone,
{
    /// Values in the `items` deque may be logically erased, except for the
    /// first/last: we always clean up from both ends.
    items: SlidingDeque<Container>,
    marker: Marker,
}

impl<Container, Marker> Default for SortedDeque<Container, Marker>
where
    Container: PushTruncateContainer + Clone + Default,
    Container::Item: Copy,
    Marker: SortedDequeComparator<Container::Item> + Clone + Default,
{
    #[inline(always)]
    fn default() -> Self {
        Self::new(Default::default(), Default::default())
    }
}

impl<Container, Marker> SortedDeque<Container, Marker>
where
    Container: PushTruncateContainer + Clone + Default,
    Container::Item: Copy,
    Marker: SortedDequeComparator<Container::Item> + Clone,
{
    /// Creates a fresh `SortedDeque` from the given `items` and `marker`.
    #[must_use]
    #[inline(always)]
    pub fn new(items: Container, marker: Marker) -> Self {
        Self {
            items: items.into(),
            marker,
        }
    }

    /// Pushes `item` to the end of the [`SortedDeque`].
    ///
    /// Panics if the `item` isn't strictly greater than the
    /// last element, if any.
    ///
    /// No-ops if `item` is already erased.
    pub fn push_back_or_panic(&mut self, item: Container::Item) {
        self.check_rep();
        if self.marker.is_erased(&item) {
            return;
        }

        if let Some(back) = self.items.back() {
            assert_eq!(
                self.marker.cmp(
                    &self.marker.extract_key(back),
                    &self.marker.extract_key(&item)
                ),
                Ordering::Less
            );
        }

        self.items.push_back(item);
        self.check_rep();
    }

    /// Removes all items from `self`.
    #[inline(always)]
    pub fn clear(&mut self) {
        self.check_rep();

        self.items.clear();
        self.check_rep();
    }

    /// Determines whether we have no item in the container.
    #[must_use]
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.check_rep();

        self.items.is_empty()
    }

    /// Returns an iterator for the (non-erased) items in the [`SortedDeque`],
    /// in FIFO (and thus sorted) order.
    #[inline(always)]
    pub fn iter(&self) -> impl Iterator<Item = &Container::Item> {
        self.check_rep();

        self.items
            .iter()
            .filter(|item| !self.marker.is_erased(item))
    }

    /// Returns the first (least-valued) item, if we have one.
    #[must_use]
    #[inline(always)]
    pub fn first(&self) -> Option<&Container::Item> {
        self.check_rep();

        self.items.front()
    }

    /// Consumes and returns the first item.
    #[inline(never)]
    pub fn pop_first(&mut self) -> Option<Container::Item> {
        self.check_rep();

        let ret = self.items.pop_front()?;
        self.cleanup_front();

        self.check_rep();

        Some(ret)
    }

    /// Returns the last (highest valued) item, if we have one
    #[must_use]
    #[inline(always)]
    pub fn last(&self) -> Option<&Container::Item> {
        self.check_rep();

        self.items.back()
    }

    /// Consumes and returns the last item.
    #[inline(never)]
    pub fn pop_last(&mut self) -> Option<Container::Item> {
        self.check_rep();

        let ret = self.items.pop_back()?;
        self.cleanup_back();

        self.check_rep();

        Some(ret)
    }

    /// Looks for the item that matches `key`.
    #[must_use]
    pub fn find(&self, key: &Marker::Key) -> Option<&Container::Item> {
        self.check_rep();

        let idx = self.find_index(key)?;

        let item = &self.items[idx];

        self.check_rep();

        if self.marker.is_erased(item) {
            None
        } else {
            Some(item)
        }
    }

    /// Find the index of the item that corresponds to `key`, if any.
    #[must_use]
    #[inline(always)]
    fn find_index(&self, key: &Marker::Key) -> Option<usize> {
        let comparator = |item| self.marker.cmp(&self.marker.extract_key(item), key);
        self.items.binary_search_by(comparator).ok()
    }

    /// Removes any newly exposed erased item at the back of the underlying deque.
    #[inline(always)]
    fn cleanup_back(&mut self) {
        while let Some(back) = self.items.back() {
            if !self.marker.is_erased(back) {
                break;
            }

            self.items.pop_back();
        }
    }

    /// Removes any newly exposed erased item at the front of the underlying deque.
    #[inline(always)]
    fn cleanup_front(&mut self) {
        let mut to_drop = usize::MAX;
        // Find the index of the first non-deleted item
        for (idx, item) in self.items.iter().enumerate() {
            if !self.marker.is_erased(item) {
                to_drop = idx;
                break;
            }
        }

        let _ = self.items.advance(to_drop);
    }

    #[inline(always)]
    #[cfg_attr(test, mutants::skip)] // obviously, removing checks will not be detected.
    fn check_rep(&self) {
        // First item, if any, must not be erased.
        debug_assert_ne!(
            self.items.front().map(|x| self.marker.is_erased(x)),
            Some(true)
        );

        // Last item, if any, must not be erased.
        debug_assert_ne!(
            self.items.back().map(|x| self.marker.is_erased(x)),
            Some(true)
        );
    }
}

impl<Container, Marker> SortedDeque<Container, Marker>
where
    Container: PushTruncateContainer + Clone + Default,
    Container::Item: Copy,
    Marker: SortedDequeMarker<Container::Item> + Clone,
{
    /// Looks for the item that matches `key`, and removes it
    /// if it is found.
    ///
    /// Once removed, an item will not be found again.
    #[inline(never)]
    pub fn remove(&mut self, key: &Marker::Key) -> Option<Container::Item> {
        let len = self.items.len();
        let idx = self.find_index(key)?;

        let item = &mut self.items[idx];
        if self.marker.is_erased(item) {
            return None;
        }

        if idx == 0 {
            // The `pop_first` method is better for large batches;
            // prefer to call that if we removed the last item.
            self.pop_first()
        } else if idx == len - 1 {
            self.pop_last()
        } else {
            // Deletion from the middle, can only erase logically.
            let ret = *item;

            self.marker.mark_erased(item);
            assert!(self.marker.is_erased(item));
            Some(ret)
        }
    }
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, Ord, PartialOrd, Eq, PartialEq)]
struct TestItem {
    key: u32,
    value: Option<std::num::NonZeroU32>,
}

#[cfg(test)]
impl SortedDequeItem for TestItem {
    fn mark_erased(&mut self) {
        self.value = None
    }

    fn is_erased(&self) -> bool {
        self.value.is_none()
    }
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, Ord, PartialOrd, Eq, PartialEq)]
struct KeyOnlyTestItem {
    key: u32,
}

#[cfg(test)]
impl SortedDequeComparator<KeyOnlyTestItem> for () {
    type Key = u32;

    #[inline(always)]
    fn extract_key(&self, item: &KeyOnlyTestItem) -> Self::Key {
        item.key
    }

    #[inline(always)]
    fn cmp(&self, x: &u32, y: &u32) -> std::cmp::Ordering {
        x.cmp(y)
    }
}

#[test]
fn test_happy_path_miri() {
    let mut deque: SortedDeque<Vec<TestItem>> = Default::default();

    assert!(deque.is_empty());
    assert_eq!(deque.first(), None);
    assert_eq!(deque.pop_first(), None);
    assert_eq!(deque.last(), None);
    assert_eq!(deque.pop_last(), None);

    let item = TestItem {
        key: 0,
        value: Some(1.try_into().unwrap()),
    };
    assert_eq!(deque.find(&item), None);
    assert_eq!(deque.iter().copied().collect::<Vec<_>>(), []);

    deque.push_back_or_panic(item);
    assert!(!deque.is_empty());
    assert_eq!(deque.iter().copied().collect::<Vec<_>>(), [item]);

    // Clearing should work
    deque.clear();
    assert!(deque.is_empty());
    assert_eq!(deque.iter().copied().collect::<Vec<_>>(), []);

    // Put it back in.
    deque.push_back_or_panic(item);
    assert_eq!(deque.first(), Some(&item));
    assert_eq!(deque.last(), Some(&item));

    assert_eq!(deque.find(&item), Some(&item));
    // No false match.
    assert_eq!(
        deque.find(&TestItem {
            key: 1,
            value: Some(1.try_into().unwrap())
        }),
        None
    );
    assert_eq!(
        deque.find(&TestItem {
            key: 0,
            value: None
        }),
        None
    );

    assert_eq!(deque.remove(&item), Some(item));

    assert!(deque.is_empty());
}

#[test]
fn test_happy_path_key_only_miri() {
    let mut deque: SortedDeque<Vec<KeyOnlyTestItem>> = Default::default();

    assert!(deque.is_empty());
    assert_eq!(deque.first(), None);
    assert_eq!(deque.pop_first(), None);
    assert_eq!(deque.last(), None);
    assert_eq!(deque.pop_last(), None);

    let item = KeyOnlyTestItem { key: 0 };
    assert_eq!(deque.find(&0), None);
    assert_eq!(deque.iter().copied().collect::<Vec<_>>(), []);

    deque.push_back_or_panic(item);
    assert!(!deque.is_empty());
    assert_eq!(deque.iter().copied().collect::<Vec<_>>(), [item]);

    // Clearing should work
    deque.clear();
    assert!(deque.is_empty());
    assert_eq!(deque.iter().copied().collect::<Vec<_>>(), []);

    // Put it back in.
    deque.push_back_or_panic(item);
    assert_eq!(deque.first(), Some(&item));
    assert_eq!(deque.last(), Some(&item));

    // No false match.
    assert_eq!(deque.find(&1), None);
}

#[test]
fn test_remove_middle_miri() {
    let mut deque: SortedDeque<Vec<TestItem>> = Default::default();

    let items = [
        TestItem {
            key: 0,
            value: Some(1.try_into().unwrap()),
        },
        TestItem {
            key: 1,
            value: Some(1.try_into().unwrap()),
        },
        TestItem {
            key: 2,
            value: Some(1.try_into().unwrap()),
        },
        // This one is already deleted, should no-op.
        TestItem {
            key: 0,
            value: None,
        },
    ];
    assert_eq!(deque.find(&items[0]), None);

    deque.push_back_or_panic(items[0]);
    deque.push_back_or_panic(items[1]);
    deque.push_back_or_panic(items[2]);
    deque.push_back_or_panic(items[3]);

    assert_eq!(deque.iter().map(|x| x.key).collect::<Vec<_>>(), [0, 1, 2]);

    assert!(!deque.is_empty());

    assert_eq!(deque.first(), Some(&items[0]));
    assert_eq!(deque.last(), Some(&items[2]));

    assert_eq!(deque.find(&items[0]), Some(&items[0]));
    assert_eq!(deque.find(&items[1]), Some(&items[1]));
    assert_eq!(deque.find(&items[2]), Some(&items[2]));
    assert_eq!(deque.find(&items[3]), None);

    assert_eq!(deque.remove(&items[1]), Some(items[1]));
    assert_eq!(deque.iter().map(|x| x.key).collect::<Vec<_>>(), [0, 2]);

    assert_eq!(deque.find(&items[0]), Some(&items[0]));
    assert_eq!(deque.find(&items[1]), None);
    assert_eq!(deque.find(&items[2]), Some(&items[2]));

    assert_eq!(deque.remove(&items[0]), Some(items[0]));

    assert_eq!(deque.first(), Some(&items[2]));
    assert_eq!(deque.last(), Some(&items[2]));

    assert_eq!(deque.remove(&items[2]), Some(items[2]));

    assert!(deque.is_empty());
}

#[test]
fn test_remove_middle_then_pop_miri() {
    let mut deque: SortedDeque<Vec<TestItem>> = Default::default();

    let items = [
        TestItem {
            key: 0,
            value: Some(1.try_into().unwrap()),
        },
        TestItem {
            key: 1,
            value: Some(1.try_into().unwrap()),
        },
        TestItem {
            key: 2,
            value: Some(1.try_into().unwrap()),
        },
    ];
    assert_eq!(deque.find(&items[0]), None);

    deque.push_back_or_panic(items[0]);
    deque.push_back_or_panic(items[1]);
    deque.push_back_or_panic(items[2]);

    assert!(!deque.is_empty());

    assert_eq!(deque.first(), Some(&items[0]));
    assert_eq!(deque.last(), Some(&items[2]));

    assert_eq!(deque.find(&items[0]), Some(&items[0]));
    assert_eq!(deque.find(&items[1]), Some(&items[1]));
    assert_eq!(deque.find(&items[2]), Some(&items[2]));

    assert_eq!(deque.remove(&items[1]), Some(items[1]));

    assert_eq!(deque.find(&items[0]), Some(&items[0]));
    assert_eq!(deque.find(&items[1]), None);
    assert_eq!(deque.find(&items[2]), Some(&items[2]));

    assert_eq!(deque.pop_last(), Some(items[2]));

    assert_eq!(deque.find(&items[0]), Some(&items[0]));
    assert_eq!(deque.find(&items[1]), None);
    assert_eq!(deque.find(&items[2]), None);
    assert_eq!(deque.pop_first(), Some(items[0]));

    assert!(deque.is_empty());
}

#[test]
fn test_key_val_miri() {
    type Entry = (u32, Option<()>);
    let mut deque: SortedDeque<smallvec::SmallVec<[Entry; 4]>> = Default::default();

    deque.push_back_or_panic((1, Some(())));
    deque.push_back_or_panic((2, Some(())));
    deque.push_back_or_panic((1, None));
    deque.push_back_or_panic((3, Some(())));

    assert_eq!(deque.find(&0), None);
    assert_eq!(deque.remove(&0), None);

    assert_eq!(deque.find(&1), Some(&(1, Some(()))));
    assert_eq!(deque.find(&2), Some(&(2, Some(()))));
    assert_eq!(deque.find(&3), Some(&(3, Some(()))));
    assert_eq!(deque.find(&4), None);

    assert_eq!(deque.remove(&2), Some((2, Some(()))));
    assert_eq!(deque.remove(&2), None);

    assert_eq!(deque.find(&1), Some(&(1, Some(()))));
    assert_eq!(deque.find(&2), None);
    assert_eq!(deque.find(&3), Some(&(3, Some(()))));

    assert_eq!(deque.remove(&3), Some((3, Some(()))));
    assert_eq!(deque.find(&3), None);

    assert_eq!(deque.remove(&1), Some((1, Some(()))));

    assert!(deque.is_empty());
}

#[test]
#[should_panic(expected = "left: Greater")]
fn test_push_back_or_panic_miri() {
    let mut deque: SortedDeque<Vec<TestItem>> = Default::default();

    let item1 = TestItem {
        key: 1,
        value: Some(1.try_into().unwrap()),
    };
    let item2 = TestItem {
        key: 2,
        value: Some(2.try_into().unwrap()),
    };
    let item3 = TestItem {
        key: 1,
        value: Some(3.try_into().unwrap()),
    }; // Not strictly greater

    deque.push_back_or_panic(item1);
    deque.push_back_or_panic(item2);

    // This should panic
    deque.push_back_or_panic(item3);
}

#[test]
fn test_pop_first_and_last_miri() {
    let mut deque: SortedDeque<Vec<TestItem>> = Default::default();

    let item1 = TestItem {
        key: 1,
        value: Some(1.try_into().unwrap()),
    };
    let item2 = TestItem {
        key: 2,
        value: Some(2.try_into().unwrap()),
    };

    deque.push_back_or_panic(item1);
    deque.push_back_or_panic(item2);

    assert_eq!(deque.pop_first(), Some(item1));
    assert_eq!(deque.pop_last(), Some(item2));
    assert!(deque.is_empty());
}

#[test]
fn test_erasure_logic_miri() {
    let mut deque: SortedDeque<Vec<TestItem>> = Default::default();

    let item1 = TestItem {
        key: 1,
        value: Some(1.try_into().unwrap()),
    };
    let item2 = TestItem {
        key: 2,
        value: Some(2.try_into().unwrap()),
    };

    deque.push_back_or_panic(item1);
    deque.push_back_or_panic(item2);

    deque.remove(&item2);

    assert_eq!(deque.find(&item2), None);
}

#[test]
fn test_find_miri() {
    let mut deque: SortedDeque<Vec<TestItem>> = Default::default();

    let item1 = TestItem {
        key: 1,
        value: Some(1.try_into().unwrap()),
    };
    let item2 = TestItem {
        key: 2,
        value: Some(2.try_into().unwrap()),
    };

    deque.push_back_or_panic(item1);
    deque.push_back_or_panic(item2);

    assert_eq!(deque.find(&item1), Some(&item1));
    assert_eq!(deque.find(&item2), Some(&item2));
    assert_eq!(
        deque.find(&TestItem {
            key: 3,
            value: None
        }),
        None
    );
}

#[test]
fn test_cleanup_methods_miri() {
    let mut deque: SortedDeque<Vec<TestItem>> = Default::default();

    let item1 = TestItem {
        key: 1,
        value: Some(1.try_into().unwrap()),
    };
    let item2 = TestItem {
        key: 2,
        value: Some(2.try_into().unwrap()),
    };

    deque.push_back_or_panic(item1);
    deque.push_back_or_panic(item2);

    assert_eq!(deque.remove(&item2), Some(item2));
    deque.cleanup_back();

    assert_eq!(deque.last(), Some(&item1));
    assert_eq!(deque.find(&item2), None);
}
