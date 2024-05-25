use std::io::IoSlice;
use std::num::NonZeroUsize;

use smallvec::SmallVec;

use super::byte_arena::Anchor;
use super::byte_arena::ByteArena;
use super::global_deque::GlobalDeque;
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
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.0.map(|(_, info)| info.len.into()).unwrap_or(0)
    }
}

/// An [`OwningIovec`] is a [`Vec<IoSlice<>>`] that may optionally own
/// some of it slices' pointees.  Some of the owned pointees may be
/// backpatched after the fact, and it's possible to peek at and consume
/// the first `IoSlice`s that aren't waiting for a backpatch.
///
/// Internally, owned slices are allocated from an internal arena
/// with `Arc` to the backing allocations tracked internally.
#[derive(Debug, Default, Clone)]
pub struct OwningIovec<'this> {
    // The `GlobalDeque` manages the mapping between slices and
    // Anchors, but is oblivious to backreferences.  Always bound
    // check *that* before accessing `slices`.
    //
    // XXX: we internally guarantee to never push empty slices in
    // there, and the global deque itself skips empty slices.
    slices: GlobalDeque<'this>,

    // We allocate from `arena`, but only to stick values in `iovs`,
    // and this `ByteArena` is static for the lifetime of the
    // `OwningIovec`.
    arena: ByteArena,
    backrefs: SortedDeque<SmallVec<[Backref; 4]>>, // Pending backrefs
}

/// Conceptually, [`ConsumingIovec`] is a mutable reference to an
/// [`OwningIovec`] that only exposes consuming operations (i.e.,
/// can't put slices in).  It can also be derefed as a const ref
/// to [`OwningIovec`], for read-only methods.  The 'a lifetime
/// stands for the inner `OwningIovec`'s lifetime, which must
/// not exceed the slice's.
///
/// This dataflow means we only want covariance (like regular references).
#[derive(Debug)]
#[repr(transparent)]
// We do not need a PhantomData<OwningIovec<'a>> because `ConsumingIovec`
// does not own the `OwningIovec` (and further `OwningIovec` does not
// look at the 'life-slices' contents when it drops).
// (https://github.com/rust-lang/rfcs/blob/master/text/0769-sound-generic-drop.md#phantom-data).
//
// NonNull is safe because we do want covariance in 'a.
pub struct ConsumingIovec<'a>(std::ptr::NonNull<OwningIovec<'a>>);

impl<'a> ConsumingIovec<'a> {
    /// ConsumingIovec does not implement Clone, and iovec accepts a
    /// mutable reference, so this internal pointer must be an
    /// exclusive reference to the pointee.  It's safe to convert back
    /// to &mut, because this wrapper acts like &mut &mut.
    ///
    /// We know the `OwningIovec` itself is only safe to keep around
    /// for `'a`.  We also know the slices' lifetime is at least as wide,
    /// so we force them to `'a` too; there's no lost functionality
    /// because read-side methods restrict the slices' lifetime to the
    /// same as the `OwningIovec` (to take into account owned slices).
    #[inline(always)]
    fn iovec(&'a mut self) -> &'a mut OwningIovec<'a> {
        unsafe { self.0.as_mut() }
    }
}

impl<'a> std::convert::From<&'a mut OwningIovec<'_>> for ConsumingIovec<'a> {
    // It's important to constraint the `&mut OwningIovec` with `'a`:
    // the slices can have an arbitrary wider lifetime than the OwningIovec,
    // (e.g., `OwningIovec<'static>`).  For reading purposes, it's safe
    // to narrow the slices' lifetime to the same `'a` as the iovec:
    // we only borrow/copy slices out of the iovec, and all const methods
    // force the output slices' lifetime to match the iovec's.
    #[inline(always)]
    fn from(iovec: &'a mut OwningIovec<'_>) -> ConsumingIovec<'a> {
        ConsumingIovec(iovec.into())
    }
}

// No DerefMut because the whole point of `ConsumingIovec` is to
// only allow the consuming subset of mutable methods.
impl<'a> std::ops::Deref for ConsumingIovec<'a> {
    type Target = OwningIovec<'a>;

    #[inline(always)]
    fn deref(&self) -> &OwningIovec<'a> {
        unsafe { self.0.as_ref() }
    }
}

/// Always copy when the source is at most this long.
const SMALL_COPY: usize = 64;

/// Copy when the source is at most this long and we'd extend the last IoSlice.
const MAX_OPPORTUNISTIC_COPY: usize = 256;

fn ioslice_len(slice: IoSlice<'_>) -> usize {
    let iov: libc::iovec = unsafe { std::mem::transmute(slice) };
    iov.iov_len
}

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
            ..Default::default()
        }
    }

    #[inline(always)]
    pub fn arena(&mut self) -> &mut ByteArena {
        &mut self.arena
    }

    #[inline(always)]
    pub fn consumer(&mut self) -> ConsumingIovec<'_> {
        self.into()
    }

    /// Replaces `self` with a default-constructued [`OwningIovec`] and
    /// returns the initial `self`.
    pub fn take(&mut self) -> Self {
        let mut ret = Default::default();
        std::mem::swap(self, &mut ret);
        ret
    }

    pub fn clear(&mut self) {
        self.slices.clear();
        self.backrefs.clear();
    }

    /// Pushes `slice` to the internal vector of [`IoSlice`]s.
    ///
    /// Small slices are copied, large ones borrowed, and
    /// medium-sized one may be copied when it makes sense.
    ///
    /// This method takes constant amortised time wrt `slice.len()`.
    pub fn push(&mut self, slice: &'this [u8]) {
        let small = slice.len() <= SMALL_COPY;
        let appendable = (slice.len() <= MAX_OPPORTUNISTIC_COPY)
            & (self.arena.remaining() >= slice.len())
            & (self
                .slices
                .last_slice()
                .map(|slice| self.arena.is_last(slice))
                == Some(true));

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

        self.slices.push_borrowed(IoSlice::new(slice));
        self.optimize();
    }

    /// Pushes a copy of `src` to the internal vector of [`IoSlice`].
    ///
    /// This method takes lines time wrt `slice.len()`.
    pub fn push_copy(&mut self, src: &[u8]) {
        if src.is_empty() {
            return;
        }

        let last_anchor = self.slices.last_anchor();
        let (slice, anchor) = unsafe { self.arena.copy(src, last_anchor) };
        self.slices.push((slice, anchor));
        self.optimize();
    }

    /// Extends the internal vector of [`IoSlice`]s with each item in `iovs`.
    pub fn extend(&mut self, iovs: impl IntoIterator<Item = IoSlice<'this>>) {
        for iov in iovs {
            if iov.is_empty() {
                continue;
            }

            self.slices.push_borrowed(iov);
            self.optimize();
        }
    }

    pub fn push_anchor(&mut self, anchor: Anchor) {
        self.slices.push_anchor(anchor);
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
        let logical_index = self.slices.logical_size() - (pattern_size as u64);
        let info = BackrefInfo {
            slice_index: self.slices.last_logical_slice_index(),
            begin: ioslice_len(self.slices.last_slice().unwrap()) - pattern_size,
            len: NonZeroUsize::try_from(pattern_size).unwrap(), // We checked for emptiness above
        };
        self.backrefs
            .push_back_or_panic((logical_index, Some(info)));
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
        let target: libc::iovec = unsafe { std::mem::transmute(target) };

        assert!(info.begin + src.len() <= target.iov_len);
        let dst = target.iov_base as *mut u8;
        let dst = unsafe { dst.add(info.begin) };
        unsafe { std::ptr::copy(src.as_ptr(), dst, src.len()) };
    }

    /// Attempts to join together the last two slices in `self.iovs()`
    /// if it's definitely safe to do so.  This method onl works on
    /// the last two slices because we call it whenever a slice is
    /// pushed to `self.iovs`.
    fn optimize(&mut self) {
        self.slices
            .maybe_collapse_last_pair(|left, right| unsafe { self.arena.try_join(left, right) });
    }
}

// pure read methods
impl OwningIovec<'_> {
    #[inline(always)]
    pub fn has_pending_backrefs(&self) -> bool {
        !self.backrefs.is_empty()
    }

    /// Returns a prefix of the owned slices such that none of the
    /// returned slices contain a backpatch.
    #[inline(always)]
    pub fn stable_prefix(&self) -> &[IoSlice<'_>] {
        // Unwrap because, if we have an element, its value is `Some`.
        let stop_slice_index = self
            .backrefs
            .first()
            .map(|backref| backref.1.unwrap().slice_index);
        self.slices.get_logical_prefix(stop_slice_index)
    }

    /// Peeks at the next stable IoSlice
    #[inline(always)]
    pub fn front(&self) -> Option<IoSlice<'_>> {
        self.stable_prefix().first().copied()
    }

    /// The [`OwningIovec::iovs`] method is the only way to borrow
    /// [`IoSlice`]s from an [`OwningIovec`]. The lifetime constraints
    /// ensure that the return value outlives neither `this` nor `self`.
    ///
    /// Returns the stable prefix if some backrefs are still in flight.
    #[inline(always)]
    pub fn iovs(&self) -> std::result::Result<&[IoSlice<'_>], &[IoSlice<'_>]> {
        let ret = self.stable_prefix();
        if self.has_pending_backrefs() {
            Err(ret)
        } else {
            Ok(ret)
        }
    }

    /// Returns the number of slices in the [`OwningIovec`].
    ///
    /// This includes slices that are still waiting for a backpatch.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.slices.num_slices()
    }

    /// Determines whether the [`OwningIovec`] contains 0 slices.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the total number of bytes in `self.iovs`.
    ///
    /// This includes slices that are still waiting for a backpatch.
    #[inline(always)]
    pub fn total_size(&self) -> usize {
        self.slices.total_size()
    }

    /// Returns the contents of this iovec as a single [`Vec<u8>`].
    ///
    /// Returns the stable contents as an error if there is any backreference in flight.
    #[inline(always)]
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

        if self.has_pending_backrefs() {
            Err(dst)
        } else {
            Ok(dst)
        }
    }
}

impl<'a> ConsumingIovec<'a> {
    /// Returns a reference to the underlying arena.
    #[inline(always)]
    pub fn arena(&'a mut self) -> &'a mut ByteArena {
        &mut self.iovec().arena
    }

    /// Returns the underlying arena.
    pub fn take_arena(&'a mut self) -> ByteArena {
        self.swap_arena(Default::default())
    }

    pub fn swap_arena(&'a mut self, mut arena: ByteArena) -> ByteArena {
        std::mem::swap(&mut arena, self.arena());
        arena
    }

    /// Pops the first IoSlice.  Panics if the [`OwningIovec`] has no stable prefix.
    pub fn pop_front(&'a mut self) {
        let consumed = self.consume(1);
        assert_eq!(consumed, 1);
    }

    /// Pops up to the next `count` `IoSlice`s returned by [`OwningIovec::stable_prefix`].
    ///
    /// Returns the number of slices consumed.
    #[inline(always)]
    pub fn consume(&'a mut self, count: usize) -> usize {
        let num_slices = self.stable_prefix().len();
        self.iovec().slices.consume(count.min(num_slices))
    }

    /// Pops up to the next `count` bytes in the slices returned by [`OwningIovec::stable_prefix`].
    ///
    /// Returns the number of bytes consumed.
    pub fn advance_slices(&'a mut self, count: usize) -> usize {
        let mut stable_count = 0;
        for slice in self.stable_prefix() {
            let size = slice.len();
            if size >= count - stable_count {
                stable_count = count;
                break;
            }

            stable_count += size;
        }

        self.iovec().slices.consume_by_bytes(stable_count)
    }
}

impl<'life> IntoIterator for &'life OwningIovec<'_> {
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
fn test_happy_optimize_miri() {
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
    iovs.arena().ensure_capacity(10);
    iovs.push_copy(b"123");
    iovs.arena().ensure_capacity(7);
    iovs.push_copy(b"456");
    iovs.push(b"7");
    iovs.push_borrowed(b"aaa");
    iovs.push_anchor(Default::default());

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

    // now consume 4 bytes.
    assert_eq!(iovs.consumer().advance_slices(4), 4);
    assert_eq!(iovs.len(), 2);
    assert_eq!(iovs.total_size(), 9);

    assert_eq!(iovs.flatten().unwrap(), b"234567aaa");

    assert_eq!(iovs.consumer().advance_slices(100), 9);
    assert!(iovs.is_empty());
    assert_eq!(iovs.len(), 0);
    assert_eq!(iovs.total_size(), 0);
    assert_eq!(iovs.flatten().unwrap(), b"");

    assert_eq!(iovs.consumer().advance_slices(100), 0);
    assert_eq!(iovs.flatten().unwrap(), b"");
}

// Make sure we don't optimize when there's a gap.
#[test]
fn test_no_optimize_gap_miri() {
    let slices = [IoSlice::new(&b""[..])];
    let mut iovs: OwningIovec = slices.iter().collect();

    iovs.push_borrowed(b"000");
    iovs.push_copy(b"123");
    // Create a gap in the copied allocations.
    let _ = unsafe { iovs.arena.copy(b"xxx", None) };
    iovs.push_copy(b"456");
    iovs.push_borrowed(b"aaa");

    // Force a realloc, make sure this doesn't do weird stuff.
    let mut arena = iovs.consumer().take_arena();
    arena.ensure_capacity(10000);
    iovs.consumer().swap_arena(arena);

    assert_eq!(iovs.len(), 4);
    assert_eq!(iovs.total_size(), 12);

    assert_eq!(iovs.flatten_into(vec![0x42]).unwrap(), b"\x42000123456aaa");
}

// Make sure we *don't* optimize when the arena's cache
// is reused for another `OwningIovec`.
#[test]
fn test_no_optimize_flush_miri() {
    let mut iovs = OwningIovec::new();

    iovs.push_borrowed(b"000");
    iovs.push_copy(b"123");

    // Mess with the cached allocation
    iovs.arena().flush_cache();
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
fn test_extend_miri() {
    use std::io::Write;

    let mut iovs2 = OwningIovec::new();
    let mut iovs = OwningIovec::new();

    iovs.push_borrowed(b"000");
    iovs2.push_copy(b"123");
    iovs2.push_copy(b"456");
    iovs.extend(iovs2.into_iter().copied());

    // We don't expect empty slices, but we should still drop them on
    // the floot.
    iovs.extend([IoSlice::new(&[0u8][..0]), IoSlice::new(&[0u8])]);
    iovs.push_borrowed(b"aaa");

    assert_eq!(iovs.len(), 4);
    assert_eq!(iovs.total_size(), 13);

    let mut dst = Vec::new();
    assert_eq!(
        dst.write_vectored(iovs.iovs().unwrap())
            .expect("must_succeed"),
        13
    );

    assert_eq!(dst, b"000123456\x00aaa");
}

// Make sure we can reuse arenas for multiple OwningIovec
#[test]
fn test_inherit_miri() {
    use std::io::Write;

    let mut iovs2 = OwningIovec::new();
    let mut iovs = OwningIovec::new();

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

// Make sure we can steal another iov's arena
#[test]
fn test_inherit2_miri() {
    use std::io::Write;

    let mut iovs2;
    let mut iovs = OwningIovec::new();

    iovs.push(b"000");
    iovs2 = OwningIovec::new_from_arena(iovs.consumer().take_arena());
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
fn test_medium_write_merge_miri() {
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
fn test_medium_write_disjoint_miri() {
    use std::io::Write;

    let mut iovs = OwningIovec::new_from_slices(vec![IoSlice::new(&[1u8; 3])], None);
    iovs.push_copy(&[1u8; 128]);
    iovs.arena().flush_cache();
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
fn test_large_write_miri() {
    use std::io::Write;

    let mut iovs = OwningIovec::new();

    iovs.push_copy(&[1u8; 3]);
    iovs.push(&[1u8; 1024]);
    iovs.push_copy(&[1u8; 4093]);
    iovs.arena().flush_cache();

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
fn test_backref_miri() {
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

    iovs.consumer().pop_front();

    assert!(iovs.is_empty());
}

// Make sure we still do the right thing when slices around the backref are borrowed.
#[test]
fn test_backref_borrowed_miri() {
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
fn test_backref_borrowed2_miri() {
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
fn test_backref_all_borrowed_miri() {
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
    iovs.consumer().pop_front();
    assert_eq!(&*iovs.front().unwrap(), b"123");
    iovs.consumer().pop_front();

    assert_eq!(iovs.len(), 2);
    assert_eq!(iovs.total_size(), 2 + 5);

    assert_eq!(iovs.flatten().unwrap(), b"bb56789");
}
