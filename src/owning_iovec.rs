use std::io::IoSlice;
use std::num::NonZeroUsize;

use smallvec::SmallVec;

use crate::byte_arena::ByteArena;
use crate::sliding_deque::SlidingDeque;
use crate::sorted_deque::SortedDeque;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct BackrefInfo {
    slice_index: u64,  // Global iov index
    begin: usize,      // Range in the target iov
    len: NonZeroUsize, // Size of the range
}

/// The first value is the key, the logical byte index of the backreference
/// in the [`GlobalDeque`]
type Backref = (u64, Option<BackrefInfo>);

/// Each [`OwningIovecBackref`] represents a capability to
/// backfill some bytes owned by an [`OwningIovec`].
///
/// They are returned by [`OwningIovec::register_patch`], and
/// backfilled by [`OwningIovec::backfill`].  Backreference are not
/// clonable, so cloning an `OwningIovec` that has in-flight
/// backreferences isn't super useful.
///
/// A default-constructed [`OwningIovecBackref`] represents a 0-sized
/// backpatch.
#[derive(Debug, Default)]
#[repr(transparent)]
#[must_use]
pub struct OwningIovecBackref(Option<(u64, BackrefInfo)>);

impl OwningIovecBackref {
    pub fn len(&self) -> usize {
        match self.0 {
            Some((_, info)) => info.len.into(),
            None => 0,
        }
    }
}

/// The `GlobalDeque` is a `SlidingDeque` of `IoSlice` that tracks the
/// current logical (monotonically icnreasing) position and size, and
/// maps between that and the physical locations, taking into account
/// the `IoSlice`s and bytes consumed.
///
/// The usage of the `this` lifetime can be unsound; we rely on constraints
/// on the surrounding [`OwningIovec`] to avoid dangling slices.
#[derive(Debug, Default, Clone)]
struct GlobalDeque<'this> {
    slices: SlidingDeque<Vec<IoSlice<'this>>>,
    logical_size: u64,
    consumed_size: u64,
    consumed_slices: u64,
}

impl<'this> GlobalDeque<'this> {
    fn new(slices: Vec<IoSlice<'this>>) -> Self {
        let logical_size = slices.iter().map(|slice| slice.len() as u64).sum();
        GlobalDeque {
            slices: slices.into(),
            logical_size,
            consumed_size: 0,
            consumed_slices: 0,
        }
    }

    fn push(&mut self, slice: IoSlice<'this>) {
        self.logical_size += slice.len() as u64;
        self.slices.push_back(slice);
    }

    fn last_logical_slice_index(&self) -> u64 {
        self.consumed_slices + (self.slices.len() as u64) - 1
    }

    fn get_logical_slice(&self, index: u64) -> Option<IoSlice<'this>> {
        let index = index
            .wrapping_sub(self.consumed_slices)
            .min(usize::MAX as u64) as usize;

        self.slices.get(index).copied()
    }

    /// Gets the prefix of slices we can look at *before* the logical slice index
    /// `end_logical_slice`.
    fn get_logical_prefix(&self, end_logical_slice: Option<u64>) -> &[IoSlice<'this>] {
        let end_logical_slice = end_logical_slice.unwrap_or(u64::MAX);
        let remainder = end_logical_slice - self.consumed_slices;
        let take = remainder.min(self.slices.len() as u64) as usize;

        &self.slices[..take]
    }

    fn consume(&mut self, count: usize) -> usize {
        let count = count.min(self.slices.len());

        let consumed_size: u64 = self.slices[..count]
            .iter()
            .map(|slice| slice.len() as u64)
            .sum();
        self.consumed_size += consumed_size;
        self.consumed_slices += count as u64;

        let consumed = self.slices.advance(count);
        assert_eq!(consumed, count);

        count
    }

    fn num_slices(&self) -> usize {
        self.slices.len()
    }

    // Returns the total number of bytes in the slices.
    fn total_size(&self) -> usize {
        (self.logical_size - self.consumed_size) as usize
    }

    fn maybe_collapse_last_pair(
        &mut self,
        collapse: impl FnOnce(IoSlice<'this>, IoSlice<'this>) -> Option<IoSlice<'this>>,
    ) {
        let len = self.slices.len();
        if len < 2 {
            return;
        }

        if let Some(merger) = collapse(self.slices[len - 2], self.slices[len - 1]) {
            self.slices.pop_back();
            *self.slices.back_mut().unwrap() = merger;
        }
    }
}

/// An [`OwningIovec`] is a [`Vec<IoSlice<>>`] that may optionally own
/// some of it slices' pointees.  Some of the owned pointees may be
/// backpatched after the fact, and it's possible to peek at and consume
/// the first `IoSlice`s that aren't pending backpatching.
///
/// Internally, owned slices are allocated from an internal arena that
/// lives at least as long as the [`OwningIovec`] itself.  It's safe
/// to treat the owned slices as `IoSlice<'this>` because
/// [`OwningIovec::iovs()`] and [`OwningIovec::front()`] constrain
/// `&'this self` to live at least as long the [`IoSlice`]s.
#[derive(Debug, Default, Clone)]
pub struct OwningIovec<'this> {
    slices: GlobalDeque<'this>,

    // We allocate from `arena`, but only to stick values in `iovs`,
    // and this `ByteArena` is static for the lifetime of the
    // `OwningIovec`.
    arena: ByteArena,
    backrefs: SortedDeque<SmallVec<[Backref; 4]>>, // Pending backrefs
}

impl<'this> Drop for OwningIovec<'this> {
    fn drop(&mut self) {
        // Clear the slices *before* the arena is destroyed: we don't
        // want dangling pointers.
        self.slices = Default::default();
    }
}

/// Always copy when the source is at most this long.
const SMALL_COPY: usize = 64;

/// Copy when the source is at most this long and we'd extend the last IoSlice.
const MAX_OPPORTUNISTIC_COPY: usize = 256;

impl<'this> OwningIovec<'this> {
    /// Creates an empty instance that will allocate from its fresh
    /// private arena.
    pub fn new() -> Self {
        Default::default()
    }

    /// Creates an empty instance that will allocate from `arena`
    pub fn new_from_arena(arena: ByteArena) -> Self {
        OwningIovec::new_from_slices(Vec::new(), Some(arena))
    }

    /// Creates a new instance with these initial [`IoSlice`]s
    /// and the arena, if provided; uses a fresh arena if [`None`].
    pub fn new_from_slices(mut slices: Vec<IoSlice<'this>>, arena: Option<ByteArena>) -> Self {
        slices.retain(|slice| slice.len() > 0);
        OwningIovec {
            slices: GlobalDeque::new(slices),
            arena: arena.unwrap_or_default(),
            backrefs: Default::default(),
        }
    }

    /// Flushes the underlying [`[u8]`] arena's allocation cache.
    pub fn flush_arena_cache(&mut self) {
        self.arena.flush_cache();
    }

    /// Ensures we have room for `len` contiguous bytes in the
    /// underlying [`[u8]`] arena's allocation cache.
    pub fn ensure_arena_capacity(&mut self, len: usize) {
        self.arena.ensure_capacity(len);
    }

    /// Returns the underlying arena.  There is no mutable getter
    /// to avoid messing up lifetimes by assigning to `self.arena`.
    pub fn arena(&self) -> &ByteArena {
        &self.arena
    }

    /// Returns a prefix of the owned slices such that none of the
    /// returned slices contain a backpatch.
    pub fn stable_prefix(&'this self) -> &'this [IoSlice<'this>] {
        // Unwrap because, if we have an element, its value is `Some`.
        let stop_slice_index = self
            .backrefs
            .first()
            .map(|backref| backref.1.unwrap().slice_index);
        self.slices.get_logical_prefix(stop_slice_index)
    }

    /// Peeks at the next stable IoSlice
    pub fn front(&'this self) -> Option<IoSlice<'this>> {
        self.stable_prefix().first().copied()
    }

    /// Pops the first IoSlice.  Panics if the [`OwningIovec`] has no stable prefix.
    pub fn pop_front(&mut self) {
        let consumed = self.consume(1);
        assert_eq!(consumed, 1);
    }

    /// Pops up to the next `consumed` `IoSlice`s returned by [`Self::stable_prefix`].
    ///
    /// Returns the number of slices consumed
    pub fn consume(&mut self, count: usize) -> usize {
        self.slices.consume(count)
    }

    /// The [`OwningIovec::iovs`] method is the only way to borrow
    /// [`IoSlice`]s from an [`OwningIovec`]. The lifetime constraints
    /// ensure that the return value outlives neither `this` nor `self`.
    ///
    /// Returns the stable prefix if some backrefs are still in flight.
    pub fn iovs(
        &'this self,
    ) -> std::result::Result<&'this [IoSlice<'this>], &'this [IoSlice<'this>]> {
        let ret = self.stable_prefix();
        if self.backrefs.is_empty() {
            Ok(ret)
        } else {
            Err(ret)
        }
    }

    /// Returns the number of slices in the [`OwningIovec`].
    pub fn len(&self) -> usize {
        self.slices.num_slices()
    }

    /// Determines whether the [`OwningIovec`] contains 0 slices.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the total number of bytes in `self.iovs`.
    pub fn total_size(&self) -> usize {
        self.slices.total_size()
    }

    /// Pushes `slice` to the internal vector of [`IoSlice`]s.
    ///
    /// Small slices are copied, large ones borrowed, and
    /// medium-sized one may be copied when it makes sense.
    ///
    /// This method takes constant amortised time wrt `slice.len()`.
    pub fn push(&mut self, slice: &'this [u8]) {
        if slice.is_empty() {
            return;
        }

        let small = slice.len() <= SMALL_COPY;
        let appendable = (slice.len() <= MAX_OPPORTUNISTIC_COPY)
            & (!self.is_empty())  // Can't extend an empty iovec
            & (self.slices.slices.last().map(|slice| self.arena.is_last(slice)) == Some(true))
            & (self.arena.remaining() >= slice.len());

        if small | appendable {
            self.push_copy(slice);
        } else {
            self.push_borrowed(slice);
        }
    }

    /// Pushes `slice` to the internal vector of [`IoSlice`],
    /// without copying the contents.
    ///
    /// This method takes constant amortised time wrt `slice.len()`.
    pub fn push_borrowed(&mut self, slice: &'this [u8]) {
        if slice.is_empty() {
            return;
        }

        self.slices.push(IoSlice::new(slice));
        self.optimize();
    }

    /// Pushes a copy of `src` to the internal vector of [`IoSlice`].
    ///
    /// This method takes lines time wrt `slice.len()`.
    pub fn push_copy(&mut self, src: &[u8]) {
        if src.is_empty() {
            return;
        }

        let slice = unsafe { self.arena.copy(src) };
        self.slices.push(IoSlice::new(slice));
        self.optimize();
    }

    /// Extends the internal vector of [`IoSlice`]s with each item in `iovs`.
    pub fn extend(&mut self, iovs: impl IntoIterator<Item = IoSlice<'this>>) {
        for iov in iovs {
            if iov.is_empty() {
                continue;
            }

            self.slices.push(iov);
            self.optimize();
        }
    }

    /// Returns the contents of this iovec as a single [`Vec<u8>`].
    ///
    /// Returns the stable contents as an error if there is any backreference in flight.
    pub fn flatten(&self) -> std::result::Result<Vec<u8>, Vec<u8>> {
        self.flatten_into(Vec::with_capacity(self.total_size()))
    }

    /// Appends the contents of this iovec so `dst`.
    ///
    /// Returns the stable contents as an error if there is any backreference in flight.
    pub fn flatten_into(&self, mut dst: Vec<u8>) -> std::result::Result<Vec<u8>, Vec<u8>> {
        dst.reserve(self.total_size());
        for iov in self.stable_prefix() {
            dst.extend_from_slice(iov);
        }

        if self.backrefs.is_empty() {
            Ok(dst)
        } else {
            Err(dst)
        }
    }

    /// Registers a backreference at the current write location, with
    /// the `pattern`'s size.
    pub fn register_patch(&mut self, pattern: &[u8]) -> OwningIovecBackref {
        if pattern.is_empty() {
            return OwningIovecBackref(None);
        }

        // XXX: this assumes the optimisation process only tries to merge
        // the most recently pushed slice with the immediately preceding one.
        self.push_copy(pattern);
        assert!(!self.is_empty());

        let pattern_size = pattern.len();
        let logical_index = self.slices.logical_size - (pattern_size as u64);
        let info = BackrefInfo {
            slice_index: self.slices.last_logical_slice_index(),
            begin: self.slices.slices.last().unwrap().len() - pattern_size,
            len: NonZeroUsize::try_from(pattern_size).unwrap(), // We checked for emptiness above
        };
        self.backrefs.push_back((logical_index, Some(info)));
        OwningIovecBackref(Some((logical_index, info)))
    }

    /// Backpopulates a backreference created for this [`OwningIovec`].
    ///
    /// Panics if `src` does not match the backreference's size, or if
    /// the backref does not come from the [`OwningIovec`].
    pub fn backfill(&mut self, backref: OwningIovecBackref, src: &[u8]) {
        let (logical_index, info) = match backref.0 {
            None => {
                // Can only have empty backref.
                assert_eq!(src, &[]);
                return;
            }
            Some(backref) => backref,
        };

        assert_eq!(usize::from(info.len), src.len());
        let backref_found_in_instance = self
            .backrefs
            .remove(&logical_index)
            .expect("backref not found");
        assert_eq!(backref_found_in_instance, (logical_index, Some(info)));

        let target = self
            .slices
            .get_logical_slice(info.slice_index)
            .expect("must still be present");
        // SAFETY: IoSlice and IoSliceMut are ABI compatible with iovec/WSABUf,
        // we have exclusive ownership over ourself + our slices, and we know
        // the backref maps to an owned allocation (made with `push_copy`).
        let mut target: std::io::IoSliceMut = unsafe { std::mem::transmute(target) };

        assert!(info.begin + src.len() <= target.len());
        for (idx, byte) in src.iter().copied().enumerate() {
            target[info.begin + idx] = byte;
        }
    }

    /// Attempts to join together the last two slices in `self.iovs()`
    /// if it's definitely safe to do so.  This method onl works on
    /// the last two slices because we call it whenever a slice is
    /// pushed to `self.iovs`.
    fn optimize(&mut self) {
        self.slices.maybe_collapse_last_pair(|left, right| {
            let joined = unsafe { self.arena.try_join(&left, &right) }?;
            Some(IoSlice::new(joined))
        });
    }
}

impl<'life> IntoIterator for &'life OwningIovec<'life> {
    type Item = &'life IoSlice<'life>;
    type IntoIter = std::slice::Iter<'life, IoSlice<'life>>;

    fn into_iter(self) -> std::slice::Iter<'life, IoSlice<'life>> {
        self.stable_prefix().iter()
    }
}

impl<'life> FromIterator<IoSlice<'life>> for OwningIovec<'life> {
    fn from_iter<T: IntoIterator<Item = IoSlice<'life>>>(iter: T) -> OwningIovec<'life> {
        let slices: Vec<IoSlice<'life>> = iter.into_iter().collect();

        OwningIovec::new_from_slices(slices, None)
    }
}

impl<'life> FromIterator<&'life IoSlice<'life>> for OwningIovec<'life> {
    #[inline(always)]
    fn from_iter<T: IntoIterator<Item = &'life IoSlice<'life>>>(iter: T) -> OwningIovec<'life> {
        OwningIovec::from_iter(iter.into_iter().copied())
    }
}

// Exercise simple iovec optimisation
#[test]
fn test_happy_optimize() {
    use std::io::Write;

    let mut iovs: OwningIovec = vec![&b""[..]].into_iter().map(IoSlice::new).collect();

    // We don't do anything for zero-sized slices
    iovs.push_borrowed(b"");
    iovs.push_copy(b"");
    iovs.push(b"");
    assert!(iovs.is_empty());

    // Push small slices
    iovs.push_borrowed(b"000");

    // Copy a bunch of slices that can be concatenated in place.
    iovs.ensure_arena_capacity(10);
    iovs.push_copy(b"123");
    iovs.ensure_arena_capacity(7);
    iovs.push_copy(b"456");
    iovs.push(b"7");
    iovs.push_borrowed(b"aaa");

    // We expect 3 ioslices:
    // 1 for the initial `push_borrowed`,
    // 1 for the "123", "456", then "7" (optimised as copy)
    // 1 for the final `push_borrowed`
    assert_eq!(iovs.len(), 3);
    assert_eq!(iovs.total_size(), 13);

    let mut dst = Vec::new();
    assert_eq!(
        dst.write_vectored(iovs.iovs().unwrap())
            .expect("must_succeed"),
        13
    );

    assert_eq!(dst, b"0001234567aaa");
}

// Make sure we don't optimize when there's a gap.
#[test]
fn test_no_optimize_gap() {
    let slices = [IoSlice::new(&b""[..])];
    let mut iovs: OwningIovec = slices.iter().collect();

    iovs.push_borrowed(b"000");
    iovs.push_copy(b"123");
    // Create a gap in the copied allocations.
    unsafe { iovs.arena.copy(b"xxx") };
    iovs.push_copy(b"456");
    iovs.push_borrowed(b"aaa");

    assert_eq!(iovs.len(), 4);
    assert_eq!(iovs.total_size(), 12);

    assert_eq!(iovs.flatten_into(vec![0x42]).unwrap(), b"\x42000123456aaa");
}

// Make sure we *don't* optimize when the arena's cache
// is reused for another `OwningIovec`.
#[test]
fn test_no_optimize_flush() {
    let mut iovs = OwningIovec::new();

    iovs.push_borrowed(b"000");
    iovs.push_copy(b"123");

    // Mess with the cached allocation
    iovs.flush_arena_cache();
    iovs.clone().push_copy(b"123");

    // Shouldn't merge with the previous.
    iovs.push_copy(b"456");
    iovs.push_borrowed(b"aaa");

    assert_eq!(iovs.len(), 4);
    assert_eq!(iovs.total_size(), 12);

    assert_eq!(iovs.flatten().unwrap(), b"000123456aaa");
}

// Exercise the `extend` method.
#[test]
fn test_extend() {
    use std::io::Write;

    let mut iovs2 = OwningIovec::new();
    let mut iovs = OwningIovec::new();

    iovs.push_borrowed(b"000");
    iovs2.push_copy(b"123");
    iovs2.push_copy(b"456");
    iovs.extend(iovs2.into_iter().copied());

    // We don't expect empty slices, but we should still drop them on
    // the floot.
    iovs.extend([IoSlice::new(&[0u8][..0])]);
    iovs.push_borrowed(b"aaa");

    assert_eq!(iovs.len(), 3);
    assert_eq!(iovs.total_size(), 12);

    let mut dst = Vec::new();
    assert_eq!(
        dst.write_vectored(iovs.iovs().unwrap())
            .expect("must_succeed"),
        12
    );

    assert_eq!(dst, b"000123456aaa");
}

// Make sure we can reuse arenas for multiple OwningIovec
#[test]
fn test_inherit() {
    use std::io::Write;

    let arena = ByteArena::new();
    let mut iovs2 = OwningIovec::new_from_arena(arena.clone());
    let mut iovs = OwningIovec::new_from_arena(arena);

    iovs.push(b"000");
    iovs2.push_copy(b"123");
    iovs2.push_copy(b"456");
    iovs.extend(iovs2.into_iter().copied());
    iovs.push(b"aaa");

    assert!(iovs.len() <= 3);
    assert_eq!(iovs.total_size(), 12);

    let mut dst = Vec::new();
    assert_eq!(
        dst.write_vectored(iovs.iovs().unwrap())
            .expect("must_succeed"),
        12
    );

    assert_eq!(dst, b"000123456aaa");
}

// Make sure we can clone another iov's arena
#[test]
fn test_inherit2() {
    use std::io::Write;

    let mut iovs2 = OwningIovec::new();
    let mut iovs = OwningIovec::new_from_arena(iovs2.arena().clone());

    iovs.push(b"000");
    iovs2.push_copy(b"123");
    iovs2.push_copy(b"456");
    iovs.extend(iovs2.iovs().unwrap().iter().copied());
    iovs.push(b"aaa");

    assert!(iovs.len() <= 3);
    assert_eq!(iovs.total_size(), 12);

    let mut dst = Vec::new();
    assert_eq!(
        dst.write_vectored(iovs.iovs().unwrap())
            .expect("must_succeed"),
        12
    );

    assert_eq!(dst, b"000123456aaa");
}

// Make sure we merge a 128-byte `push` with the previous owned slice.
#[test]
fn test_medium_write_merge() {
    use std::io::Write;

    let mut iovs = OwningIovec::new();

    iovs.push_copy(&[1u8; 3]);
    iovs.push(&[1u8; 128]);

    assert_eq!(iovs.len(), 1);
    assert_eq!(iovs.total_size(), 131);

    let mut dst = Vec::new();
    assert_eq!(
        dst.write_vectored(iovs.iovs().unwrap())
            .expect("must_succeed"),
        131
    );

    assert_eq!(dst, [1u8; 131]);
}

// Make sure we gracefully handle the case where the final copy doesn't fit in the
// the previous copy's arena, so can't be merged.
#[test]
fn test_medium_write_disjoint() {
    use std::io::Write;

    let mut iovs = OwningIovec::new_from_slices(vec![IoSlice::new(&[1u8; 3])], None);
    iovs.push_copy(&[1u8; 128]);
    iovs.flush_arena_cache();
    iovs.push_copy(&[1u8; 4096]);

    assert_eq!(iovs.len(), 3);
    assert_eq!(iovs.total_size(), 3 + 128 + 4096);

    let mut dst = Vec::new();
    assert_eq!(
        dst.write_vectored(iovs.iovs().unwrap())
            .expect("must_succeed"),
        3 + 128 + 4096
    );

    assert_eq!(dst, [1u8; 3 + 128 + 4096]);
}

// `push` should borrow for larger slices.
#[test]
fn test_large_write() {
    use std::io::Write;

    let mut iovs = OwningIovec::new();

    iovs.push_copy(&[1u8; 3]);
    iovs.push(&[1u8; 1024]);
    iovs.push_copy(&[1u8; 4093]);
    iovs.flush_arena_cache();

    assert_eq!(iovs.len(), 3);
    assert_eq!(iovs.total_size(), 3 + 1024 + 4093);

    let mut dst = Vec::new();
    assert_eq!(
        dst.write_vectored(iovs.iovs().unwrap())
            .expect("must_succeed"),
        3 + 1024 + 4093
    );

    assert_eq!(dst, [1u8; 3 + 1024 + 4093]);
}

// Backref happy path
#[test]
fn test_backref() {
    let mut iovs = OwningIovec::new();

    // Special safe case: empty patch.
    let empty = iovs.register_patch(&[]);

    assert!(iovs.iovs().is_ok());

    let backref = iovs.register_patch(&[0u8]);
    iovs.push(b"123");
    let other_backref = iovs.register_patch(&[0u8; 2]);
    iovs.push(b"56789");

    assert!(iovs.front().is_none());
    assert!(iovs.iovs().is_err());

    iovs.backfill(backref, b"a");
    assert!(iovs.iovs().is_err());
    assert!(iovs.flatten().is_err());
    assert!(iovs.front().is_none());

    iovs.backfill(other_backref, b"bb");

    assert!(iovs.iovs().is_ok());
    assert!(iovs.front().is_some());
    assert_eq!(&*iovs.front().unwrap(), b"a123bb56789");

    assert_eq!(iovs.flatten().unwrap(), b"a123bb56789");

    iovs.backfill(empty, b"");
    assert_eq!(iovs.flatten().unwrap(), b"a123bb56789");

    iovs.pop_front();

    assert!(iovs.is_empty());
}

// Make sure we still do the right thing when slices around the backref are borrowed.
#[test]
fn test_backref_borrowed() {
    let mut iovs = OwningIovec::new();

    let backref = iovs.register_patch(&[0u8]);
    iovs.push_borrowed(b"123");
    let other_backref = iovs.register_patch(&[0u8; 2]);
    iovs.push(b"56789");

    assert!(iovs.iovs().is_err());

    iovs.backfill(backref, b"a");
    assert!(iovs.iovs().is_err());
    // We can read the first slice now.
    assert_eq!(&*iovs.front().unwrap(), b"a");

    iovs.backfill(other_backref, b"bb");

    assert!(iovs.iovs().is_ok());

    assert_eq!(iovs.flatten().unwrap(), b"a123bb56789");
}

// Make sure we still do the right thing when slices around the backref are borrowed.
#[test]
fn test_backref_borrowed2() {
    let mut iovs = OwningIovec::new();

    let backref = iovs.register_patch(&[0u8]);
    iovs.push(b"123");
    let other_backref = iovs.register_patch(&[0u8; 2]);
    iovs.push_borrowed(b"56789");

    assert!(iovs.iovs().is_err());

    iovs.backfill(backref, b"a");
    assert!(iovs.iovs().is_err());
    assert!(iovs.front().is_none()); // still waiting for the second backref

    iovs.backfill(other_backref, b"bb");
    assert_eq!(&*iovs.front().unwrap(), b"a123bb");

    assert!(iovs.iovs().is_ok());

    assert_eq!(iovs.flatten().unwrap(), b"a123bb56789");
}

// Make sure we still do the right thing when all slices around the backref are borrowed.
#[test]
fn test_backref_all_borrowed() {
    let mut iovs = OwningIovec::new();

    let backref = iovs.register_patch(&[0u8]);
    iovs.push_borrowed(b"123");
    let other_backref = iovs.register_patch(&[0u8; 2]);
    iovs.push_borrowed(b"56789");

    assert!(iovs.iovs().is_err());

    iovs.backfill(backref, b"a");
    assert!(iovs.iovs().is_err());
    assert_eq!(&*iovs.front().unwrap(), b"a");

    iovs.backfill(other_backref, b"bb");

    assert!(iovs.iovs().is_ok());

    assert_eq!(iovs.flatten().unwrap(), b"a123bb56789");

    assert_eq!(&*iovs.front().unwrap(), b"a");
    iovs.pop_front();
    assert_eq!(&*iovs.front().unwrap(), b"123");
    iovs.pop_front();

    assert_eq!(iovs.len(), 2);
    assert_eq!(iovs.total_size(), 2 + 5);

    assert_eq!(iovs.flatten().unwrap(), b"bb56789");
}
