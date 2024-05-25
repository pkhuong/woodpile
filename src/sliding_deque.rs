//! The `sliding_deque` module defines the [`SlidingDeque`] container
//! wrapper.  It's similar to the standard
//! [`std::collections::VecDeque`], but accepts multiple underlying
//! container types ([`Vec`] for the regular case, and [`SmallVec`]
//! for queues that are usually small), and maintains the elements in
//! order, in a single contiguous slice.
use smallvec::SmallVec;

/// In order to implement a sliding deque, we need an underlying
/// container that can push/pop from the end, truncate to a prefix
/// of the elements, and expose its contents as a contiguous slice.
pub trait PushTruncateContainer {
    /// The type of each value in the container.
    type Item;

    /// Pushes `value` to the end of the container.
    fn push(&mut self, value: Self::Item);
    /// Pops the last value in the container
    fn pop(&mut self) -> Option<Self::Item>;
    /// Shrinks the container to the first `len` elements
    fn truncate(&mut self, len: usize);

    /// Returns a single contiguous slice for the container's
    /// elements, in order.
    fn slice(&self) -> &[Self::Item];

    /// Returns a single contiguous mutable slice for the container's
    /// elements, in order.
    fn slice_mut(&mut self) -> &mut [Self::Item];
}

/// A [`SlidingDeque`] wraps a vector-like container with amortised
/// constant-time push to the end, and augments it with an amortised
/// constant-time consumption from the front.
///
/// Pushing forwards to the underlying container's `push` method.
///
/// Consuming from the front increments a read pointer and periodically
/// shifts the container's contents forward, over consumed elements,
/// also in amortised constant time.
///
/// The [`SlidingDeque`] internally wastes up to half the space on
/// consumed but yet unshifted elements; a typical growable container
/// will waste up to half of its own space on buffer space for `push`.
/// In total, we can expect up to 4x space overhead for a SlidingDeque
/// (i.e., the maximum heap footprint will be up to 4x the maximum
/// number of logically live items in the container).
#[derive(Clone, Debug, Default)]
pub struct SlidingDeque<Container>
where
    Container: PushTruncateContainer + Clone + Default,
    <Container as PushTruncateContainer>::Item: Copy,
{
    consumed_prefix: usize,
    container: Container,
}

/// A [`SlidingVec`] where the backing storage is a [`Vec<T>`]
pub type SlidingVec<T> = SlidingDeque<Vec<T>>;

/// A [`SlidingVec`] where the backing storage is a [`SmallVec<SliceType>`],
/// e.g., `SlidingSmallVec<[u32; 8]>`.
#[allow(dead_code)]
pub type SlidingSmallVec<SliceType> = SlidingDeque<SmallVec<SliceType>>;

impl<Container: PushTruncateContainer + Clone + Default> SlidingDeque<Container>
where
    <Container as PushTruncateContainer>::Item: Copy,
{
    /// Creates a new empty [`SlidingDeque`]
    #[inline(always)]
    pub fn new() -> Self {
        Default::default()
    }

    /// Pushes `item` to the back of the [`SlidingDeque`]
    #[inline(always)]
    pub fn push_back(&mut self, item: Container::Item) {
        self.container.push(item)
    }

    /// Returns a reference to the first element in the [`SlidingDeque`],
    /// if any.
    #[inline(always)]
    pub fn front(&self) -> Option<&Container::Item> {
        self.first()
    }

    /// Returns a mutable reference to the first element in the
    /// [`SlidingDeque`], if any.
    #[inline(always)]
    pub fn front_mut(&mut self) -> Option<&mut Container::Item> {
        self.first_mut()
    }

    /// Consumes and returns the first element in the
    /// [`SlidingDeque`], if any.
    #[inline(always)]
    pub fn pop_front(&mut self) -> Option<Container::Item> {
        let ret = *self.front()?;
        self.consumed_prefix += 1;
        self.maybe_slide();
        Some(ret)
    }

    /// Returns a reference to the last element in the [`SlidingDeque`],
    /// if any.
    #[inline(always)]
    pub fn back(&self) -> Option<&Container::Item> {
        self.last()
    }

    /// Returns a mutable reference to the last element in the
    /// [`SlidingDeque`], if any.
    #[inline(always)]
    pub fn back_mut(&mut self) -> Option<&mut Container::Item> {
        self.last_mut()
    }

    /// Consumes and returns the last element in the [`SlidingDeque`],
    /// if any.
    #[inline(always)]
    pub fn pop_back(&mut self) -> Option<Container::Item> {
        // This checks that we haven't consumed all the elements.
        let ret = *self.back()?;

        self.container.pop().expect("must be non-empty");

        // We did some work if we get here; check if we reached
        // an empty state.
        if self.is_empty() {
            self.clear();
        }

        Some(ret)
    }

    /// Consumes the first `count` elements in the [`SlidingDeque`].
    ///
    /// Returns the actual number of elements consumed, which may
    /// be less than `count` if we ran out of values.
    #[inline(always)]
    #[must_use]
    pub fn advance(&mut self, count: usize) -> usize {
        let to_consume = self
            .container
            .slice()
            .len()
            .saturating_sub(self.consumed_prefix)
            .min(count);

        self.consumed_prefix += to_consume;
        self.maybe_slide();

        to_consume
    }

    /// Removes all elements from this [`SlidingDeque`], and restores
    /// the internal state to the optimal empty state.
    #[inline(always)]
    pub fn clear(&mut self) {
        self.container.truncate(0);
        self.consumed_prefix = 0;
    }

    #[inline(always)]
    fn maybe_slide(&mut self) {
        // Either there's enough slots pending cleanup to justify the slide, or
        // the cleanup will be constant-time.
        if (self.consumed_prefix >= self.container.slice().len() / 2) | self.is_empty() {
            self.slide();
        }
    }

    /// Removes any previously consumed value from the container.
    ///
    /// This does not change the logical contents of the deque, and is
    /// merely a space optimisation (at the expense of time).
    #[inline(never)]
    pub fn slide(&mut self) {
        #[cfg(not(test))]
        if self.consumed_prefix == 0 {
            return;
        }

        self.container
            .slice_mut()
            .copy_within(self.consumed_prefix.., 0);
        self.container.truncate(
            self.container
                .slice()
                .len()
                .saturating_sub(self.consumed_prefix),
        );
        self.consumed_prefix = 0;
    }
}

impl<Container> std::ops::Deref for SlidingDeque<Container>
where
    Container: PushTruncateContainer + Clone + Default,
    <Container as PushTruncateContainer>::Item: Copy,
{
    type Target = [<Container as PushTruncateContainer>::Item];

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.container.slice()[self.consumed_prefix..]
    }
}

impl<Container> std::ops::DerefMut for SlidingDeque<Container>
where
    Container: PushTruncateContainer + Clone + Default,
    <Container as PushTruncateContainer>::Item: Copy,
{
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.container.slice_mut()[self.consumed_prefix..]
    }
}

impl<Container> From<Container> for SlidingDeque<Container>
where
    Container: PushTruncateContainer + Clone + Default,
    <Container as PushTruncateContainer>::Item: Copy,
{
    #[inline(always)]
    fn from(container: Container) -> SlidingDeque<Container> {
        SlidingDeque {
            consumed_prefix: 0,
            container,
        }
    }
}

impl<T: Copy> PushTruncateContainer for Vec<T> {
    type Item = T;

    #[inline(always)]
    fn push(&mut self, value: T) {
        self.push(value)
    }

    #[inline(always)]
    fn pop(&mut self) -> Option<Self::Item> {
        self.pop()
    }

    #[inline(always)]
    fn truncate(&mut self, len: usize) {
        self.truncate(len)
    }

    #[inline(always)]
    fn slice(&self) -> &[T] {
        self
    }

    #[inline(always)]
    fn slice_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<A> PushTruncateContainer for SmallVec<A>
where
    A: smallvec::Array,
    <A as smallvec::Array>::Item: Copy,
{
    type Item = <A as smallvec::Array>::Item;

    #[inline(always)]
    fn push(&mut self, value: Self::Item) {
        self.push(value)
    }

    #[inline(always)]
    fn pop(&mut self) -> Option<Self::Item> {
        self.pop()
    }

    #[inline(always)]
    fn truncate(&mut self, len: usize) {
        self.truncate(len)
    }

    #[inline(always)]
    fn slice(&self) -> &[Self::Item] {
        self
    }

    #[inline(always)]
    fn slice_mut(&mut self) -> &mut [Self::Item] {
        self
    }
}

#[test]
fn test_vec_miri() {
    let mut deque = SlidingDeque::<Vec<u32>>::new();

    // Initially empty
    assert_eq!(&*deque, &[]);
    assert_eq!(deque.len(), 0);
    assert!(deque.is_empty());
    assert_eq!(deque.front(), None);
    assert_eq!(deque.pop_front(), None);
    assert_eq!(deque.back(), None);
    assert_eq!(deque.pop_back(), None);

    // sliding does nothing
    deque.slide();

    assert_eq!(deque.advance(10), 0);

    deque.push_back(1);
    assert_eq!(&*deque, &[1]);
    assert_eq!(deque.len(), 1);
    assert!(!deque.is_empty());
    assert_eq!(deque.front().copied(), Some(1));

    // We can overwrite the slice.
    deque[0] = 42;
    assert_eq!(&*deque, &[42]);
    assert_eq!(&*deque, &[42]);
    assert_eq!(deque.len(), 1);
    assert!(!deque.is_empty());

    // we can peek at the front.
    assert_eq!(deque.front().copied(), Some(42));

    // And pop the back
    assert_eq!(deque.pop_back(), Some(42));

    deque.slide();
}

#[test]
fn test_vec_pop_back_miri() {
    let mut deque = SlidingDeque::<Vec<u32>>::new();

    deque.push_back(0);
    deque.push_back(1);

    assert_eq!(deque.pop_back(), Some(1));
    assert_eq!(deque.pop_back(), Some(0));
    assert_eq!(deque.pop_back(), None);
}

#[test]
fn test_vec_pop_advance_miri() {
    let mut deque = SlidingDeque::<Vec<u32>>::new();

    deque.push_back(0);
    deque.push_back(1);

    assert_eq!(deque.pop_back(), Some(1));
    assert_eq!(deque.advance(2), 1);
    assert_eq!(deque.pop_back(), None);
}

#[test]
fn test_vec_advance_miri() {
    let mut deque = SlidingDeque::<Vec<u32>>::new();

    deque.push_back(0);
    deque.push_back(1);

    let _ = deque.advance(1);
    assert_eq!(deque.pop_back(), Some(1));
    assert_eq!(deque.pop_back(), None);
}

#[test]
fn test_vec_advance2_miri() {
    let mut deque = SlidingDeque::<Vec<u32>>::new();

    deque.push_back(0);
    deque.push_back(1);

    let _ = deque.advance(2);
    assert_eq!(deque.pop_back(), None);
}

#[test]
fn test_smallvec_miri() {
    let mut deque = SlidingDeque::<SmallVec<[u8; 8]>>::new();

    // Initially empty
    assert_eq!(&*deque, &[]);
    assert_eq!(deque.len(), 0);
    assert!(deque.is_empty());
    assert_eq!(deque.front(), None);
    assert_eq!(deque.pop_front(), None);

    assert_eq!(deque.advance(10), 0);

    deque.push_back(1);
    assert_eq!(&*deque, &[1]);
    assert_eq!(deque.len(), 1);
    assert!(!deque.is_empty());
    assert_eq!(deque.front().copied(), Some(1));

    // We can overwrite the slice.
    *deque.front_mut().unwrap() = 42;
    assert_eq!(&*deque, &[42]);
    assert_eq!(&*deque, &[42]);
    assert_eq!(deque.len(), 1);
    assert!(!deque.is_empty());

    deque.push_back(2);
    deque.push_back(3);
    deque.push_back(4);

    assert_eq!(&*deque, &[42, 2, 3, 4]);

    // we can peek at the front.
    assert_eq!(deque.front().copied(), Some(42));
    assert_eq!(deque.pop_front(), Some(42));
    assert_eq!(&*deque, &[2, 3, 4]);

    // Sliding forward doesn't change the contents.
    deque.slide();
    assert_eq!(&*deque, &[2, 3, 4]);

    assert_eq!(deque.pop_back(), Some(4));
    assert_eq!(&*deque, &[2, 3]);

    *deque.back_mut().unwrap() = 10;
    assert_eq!(&*deque, &[2, 10]);
}

#[test]
fn test_from_vec_miri() {
    let mut deque: SlidingDeque<Vec<u8>> = vec![0u8].into();

    assert_eq!(deque.pop_front(), Some(0u8));
    assert!(deque.is_empty());
}
