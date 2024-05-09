//! A `byte_arena` is an arena for [`[u8]`] slices.  It is very
//! closely inspired by rustc's `DroplessArena`, except that multiple
//! arenas can share the share underlying backing store (but
//! allocation caches are private).
//!
//! It is only meant for internal use, and lies by returning `'static`
//! lifetime values. The only user, `OwningIovec`, guarantees that the
//! returned allocations don't outlive the arena's backing store.
#![deny(unsafe_op_in_unsafe_fn)]
mod alloc_cache;
mod anchor;

use std::io::Read;
use std::mem::MaybeUninit;
use std::num::NonZeroUsize;
use std::sync::atomic::Ordering;

use alloc_cache::AllocCache;
pub use anchor::Anchor;

/// A [`ByteArena`] manages allocation caches (bump pointer regions).
#[derive(Debug, Default)]
pub struct ByteArena {
    cache: Option<AllocCache>,
}

/// An [`AnchoredSlice`] is a slice backed by an internal anchor.
pub struct AnchoredSlice {
    slice: &'static [u8], // actually lives as long as `anchor`.
    anchor: Anchor,
}

impl Clone for ByteArena {
    fn clone(&self) -> ByteArena {
        // Can't clone the `AllocCache`.
        Default::default()
    }
}

/// We try to allocate chunks from this geometrically growing size sequence..
const BUMP_REGION_SIZE_SEQUENCE: [usize; 9] = [
    1 << 12,
    1 << 13,
    1 << 14,
    1 << 15,
    1 << 16,
    1 << 17,
    1 << 18,
    1 << 19,
    1 << 20,
];

/// We round to 4KB
const BUMP_REGION_SIZE_FACTOR: usize = 4096;

// Whenever we allocate from a [`ByteArena`], the allocation is associated
// with an `Anchor`.  Each anchor has a sticky optional reference to the
// backing chunk; when all anchors (and the allocation cache) are dropped,
// the backing memory automatically released.  The [`std::sync::Arc`] in
// `Anchor` is heavy-weight, so each may stand for multiple allocations.
//
// The relationship between `Anchor`s and [`ByteArena`] allocations isn't
// easy to express in the Rust typesystem, so we instead expose an unsafe
// interface; this type is only expected to be used via [`crate::OwningIovec`].

impl ByteArena {
    /// Creates a fresh arena, with a fresh backing store.
    #[inline(always)]
    pub fn new() -> ByteArena {
        Default::default()
    }

    /// Returns the current number of live (allocated, not yet freed)
    /// backing arena chunks for all [`ByteArena`] in the process.
    pub fn num_live_chunks() -> usize {
        anchor::NUM_LIVE_CHUNKS.load(Ordering::Relaxed)
    }

    /// Returns the total size in bytes of live (allocated, not yet freed)
    /// backing arena chunks for all [`ByteArena`] in the process.
    pub fn num_live_bytes() -> usize {
        anchor::NUM_LIVE_BYTES.load(Ordering::Relaxed)
    }

    /// Flushes the arena's internal allocation cache.
    #[inline(never)] // The destructor can turn into a lot of code.
    pub fn flush_cache(&mut self) {
        self.cache = None;
    }

    /// Returns the number of bytes left in the current allocation cache.
    #[inline(always)]
    pub fn remaining(&self) -> usize {
        match &self.cache {
            Some(cache) => cache.remaining(),
            None => 0,
        }
    }

    /// Determines whether `slice` was the last slice allocated by the
    /// [`ByteArena`]'s current allocation cache.
    #[inline(always)]
    pub fn is_last(&self, slice: &[u8]) -> bool {
        match &self.cache {
            Some(cache) => {
                unsafe { self.contains(slice) }.is_some()
                    & (slice.as_ptr_range().end as usize == cache.next_alloc_address())
            }
            None => false,
        }
    }

    /// Ensure the current allocation cache has room for at least `len` bytes.
    #[inline(always)]
    pub fn ensure_capacity(&mut self, len: usize) {
        self.ensure_capacity_internal(len);
    }

    #[inline(never)]
    fn ensure_capacity_internal(&mut self, len: usize) -> &mut AllocCache {
        let (ok, initial_size) = match self.cache.as_mut() {
            Some(cache) => {
                let initial_size = cache.initial_size();
                (cache.remaining() >= len, initial_size)
            }
            None => (false, 0),
        };

        if ok {
            // We just checked that the cache is non-empty and has enough room.
            self.cache.as_mut().unwrap()
        } else {
            // Drop the old one before allocating a new cache.
            self.cache = None;

            // Find the "ideal" size if we have to allocate fresh.
            let hint = Self::find_hint_size(len, initial_size);
            let cache = AllocCache::new(len, hint);
            assert!(cache.remaining() >= len);
            self.cache.insert(cache)
        }
    }

    /// Find the "ideal" chunk size if we have to allocate a fresh chunk.
    fn find_hint_size(len: usize, prev_capacity: usize) -> usize {
        let max_size_sequence = *BUMP_REGION_SIZE_SEQUENCE.last().unwrap();

        if len >= max_size_sequence {
            // We're asking a large capacity, just round that up to a multiple of BUMP_REGION_SIZE_FACTOR
            let hint = len
                .div_ceil(BUMP_REGION_SIZE_FACTOR)
                .saturating_mul(BUMP_REGION_SIZE_FACTOR);
            assert!(hint >= len);
            return hint;
        }

        if prev_capacity >= max_size_sequence {
            // We're already at the max size, stay there.
            assert!(len < max_size_sequence);

            let hint = max_size_sequence;
            assert!(hint >= len);
            return hint;
        }

        // len < max_size_sequence, initial_size < max_size_sequence
        let wanted = prev_capacity.saturating_add(1).max(len);
        assert!(wanted <= max_size_sequence);

        // Default to `max_size_sequence`
        let mut hint = max_size_sequence;
        // But try to find the first element in the size sequence that's at least equal to `wanted`.
        for size in BUMP_REGION_SIZE_SEQUENCE {
            if size >= wanted {
                hint = size;
                break;
            }
        }

        assert!(hint >= len);
        // We must grow if we get here.
        assert!(hint > prev_capacity);

        hint
    }

    /// Checks whether `slice` definitely comes from this [`ByteArena`]'s backing storage.
    ///
    /// If so, returns a static lifetime slice.
    ///
    /// # Safety
    ///
    /// The return value's lifetime is a lie.  This method should only be used in
    /// `try_join`.
    #[inline(always)]
    unsafe fn contains(&self, slice: &[u8]) -> Option<&'static [u8]> {
        let range = &self.cache.as_ref()?.range();
        let endpoints = slice.as_ptr_range();

        if (range.start <= (endpoints.start as usize)) & ((endpoints.end as usize) <= range.end) {
            Some(unsafe { std::slice::from_raw_parts(endpoints.start, slice.len()) })
        } else {
            None
        }
    }

    /// Checks whether `left` and `right` are adjacent subslices that
    /// definitely come from the same underlying allocation.
    ///
    /// If so, returns a static lifetime slice for their concatenation.
    ///
    /// # Safety
    ///
    /// The return value must not outlast the slices' anchor(s).  The
    /// static lifetime is a lie.
    #[inline(always)]
    pub(super) unsafe fn try_join(&self, left: &[u8], right: &[u8]) -> Option<&'static [u8]> {
        if let (Some(left), Some(right)) = unsafe { (self.contains(left), self.contains(right)) } {
            if left.as_ptr_range().end == right.as_ptr_range().start {
                let start = left.as_ptr_range().start;
                let total_size = left.len() + right.len();
                return Some(unsafe { std::slice::from_raw_parts(start, total_size) });
            }
        }

        None
    }

    /// Internal slow path for `alloc`: we make sure there's capacity for `len`
    /// bytes and ask for that many.
    #[inline(never)]
    fn grow_and_alloc(
        &mut self,
        len: usize,
        old_anchor: Option<&mut Anchor>,
    ) -> (&'static mut [MaybeUninit<u8>], Option<Anchor>) {
        let cache = self.ensure_capacity_internal(len);
        // we just ensured capacity
        unsafe { cache.alloc_or_die(len, old_anchor) }
    }

    /// Allocates a slice of `len` bytes from this [`ByteArena`].
    ///
    /// When `old_anchor` is provided and matches the current backing
    /// chunk, increments its internal allocation count.  Otherwise,
    /// returns a fresh anchor.
    ///
    /// # Safety
    ///
    /// The return value must not outlast the `old_anchor` or the new
    /// anchor.  We lie with `'static` because `OwningIovec` just has
    /// to get it right.
    #[inline(always)]
    pub(super) unsafe fn alloc(
        &mut self,
        len: NonZeroUsize,
        old_anchor: Option<&mut Anchor>,
    ) -> (&'static mut [MaybeUninit<u8>], Option<Anchor>) {
        // The cache grabs bytes from a slice that belongs to
        // `self.backing`, so the storage lives at least as long as
        // the anchor.
        let len: usize = len.into();
        if self.remaining() >= len {
            let cache = self.cache.as_mut().expect("capacity > 0");
            // we already checked for capacity
            unsafe { cache.alloc_or_die(len, old_anchor) }
        } else {
            self.grow_and_alloc(len, old_anchor)
        }
    }

    /// Allocates a copy of `src` from this `ByteArena`.  Panics if
    /// `src` is empty.
    ///
    /// When `old_anchor` is provided and matches the current backing
    /// chunk, increments its internal allocation count.  Otherwise,
    /// returns a fresh anchor.
    ///
    /// # Safety
    ///
    /// The return value must not outlast the `old_anchor` or the new
    /// anchor.  We lie with `'static` because `OwningIovec` just has
    /// to get it right.
    pub(super) unsafe fn copy(
        &mut self,
        src: &[u8],
        old_anchor: Option<&mut Anchor>,
    ) -> (&'static mut [u8], Option<Anchor>) {
        // zero-sized allocation and memcpy have surprising aliasing consequences.
        assert!(!src.is_empty());

        let (dst, anchor) =
            unsafe { self.alloc(NonZeroUsize::new(src.len()).unwrap(), old_anchor) };

        let dst_ptr = dst.as_mut_ptr() as *mut u8;
        let len = dst.len();

        assert_eq!(len, src.len());
        unsafe { dst_ptr.copy_from_nonoverlapping(src.as_ptr(), len) };
        (
            unsafe { std::slice::from_raw_parts_mut(dst_ptr, len) },
            anchor,
        )
    }
}

impl AnchoredSlice {
    pub fn slice(&self) -> &[u8] {
        self.slice
    }

    pub unsafe fn components(self) -> (&'static [u8], Anchor) {
        (self.slice, self.anchor)
    }
}

impl ByteArena {
    pub fn read_n(
        &mut self,
        src: impl Read,
        count: usize,
        max_attempts: NonZeroUsize,
    ) -> std::io::Result<AnchoredSlice> {
        const EMPTY: [u8; 0] = [];
        if count == 0 {
            return Ok(AnchoredSlice {
                slice: &EMPTY,
                anchor: Default::default(),
            });
        }

        let (raw_slice, anchor) = unsafe { self.alloc(NonZeroUsize::new(count).unwrap(), None) };
        assert_eq!(raw_slice.len(), count);
        let slice: &'static mut [u8] =
            unsafe { std::slice::from_raw_parts_mut(raw_slice.as_mut_ptr() as *mut u8, count) };

        match self.read_n_impl(src, slice, max_attempts) {
            Ok(slice) => {
                self.cache
                    .as_mut()
                    .unwrap()
                    .release_or_die(&raw_slice[slice.len()..]);
                Ok(AnchoredSlice {
                    slice,
                    anchor: anchor.unwrap_or_default(),
                })
            }
            Err(e) => {
                // We just got an allocation, the cache isn't empty.
                self.cache.as_mut().unwrap().release_or_die(raw_slice);
                Err(e)
            }
        }
    }

    fn read_n_impl(
        &mut self,
        mut src: impl Read,
        slice: &'static mut [u8],
        max_attempts: NonZeroUsize,
    ) -> std::io::Result<&'static [u8]> {
        slice.fill(0); // XXX: unfortunately...
        let mut got = 0usize;

        for _ in 0..max_attempts.get() {
            let ret = src.read(&mut slice[got..]);

            match ret {
                Ok(count) => {
                    got += count;
                    if count == 0 {
                        break; // EOF
                    }
                }
                Err(e) => {
                    if got == 0 {
                        return Err(e);
                    } else if e.kind() != std::io::ErrorKind::Interrupted {
                        break;
                    }
                }
            }

            if got == slice.len() {
                break;
            }
        }

        Ok(&slice[..got])
    }
}

// This is mostly an internal class.  It's really tested through its
// main user, `owning_iovec`.

// Check that we correctly round up to at least the allocation size,
// and don't consider the previous capacity when doing so.
#[test]
fn test_size_sequence_large() {
    // Huge allocation -> just round up.
    assert_eq!(ByteArena::find_hint_size(2_000_000, 4096), 2002944);
    assert_eq!(2002944, 489 * 4096);

    // Same, regardless of the previous size
    assert_eq!(
        ByteArena::find_hint_size(2 * 1024 * 1024, 4_000_000),
        2 * 1024 * 1024
    );
}

// Check that we don't try to grow past the maximum region size when
// the mandatory size is small.
#[test]
fn test_size_sequence_grow_capped() {
    // Small allocation, but large initial size.  Stay at the max value.
    let max = *BUMP_REGION_SIZE_SEQUENCE.last().unwrap();
    assert_eq!(ByteArena::find_hint_size(1, max - 1), max);
    assert_eq!(ByteArena::find_hint_size(1, max), max);
    assert_eq!(ByteArena::find_hint_size(4096, 2_000_000), max);
}

// Check that we grow geometrically.
#[test]
fn test_size_sequence_grow() {
    assert_eq!(
        ByteArena::find_hint_size(1, 0),
        *BUMP_REGION_SIZE_SEQUENCE.first().unwrap()
    );

    let max = *BUMP_REGION_SIZE_SEQUENCE.last().unwrap();
    for value in BUMP_REGION_SIZE_SEQUENCE.iter().copied() {
        let hint = ByteArena::find_hint_size(1, value);
        if value == max {
            assert_eq!(hint, max);
        } else {
            assert!(hint > value);
            // Growth must be geometric.
            assert_eq!(hint, 2 * value);
            assert!(hint <= max);
        }
    }
}
