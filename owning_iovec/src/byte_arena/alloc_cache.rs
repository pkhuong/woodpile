#![deny(unsafe_op_in_unsafe_fn)]

use std::io::IoSlice;
use std::mem::MaybeUninit;
use std::ops::Range;
use std::sync::Arc;

use super::anchor::Anchor;
use super::anchor::Chunk;
use super::ioslice;

/// An [`AllocCache`] is a bump pointer in a range of pre-allocated
/// [`MaybeUninit<u8>`].
///
/// Whenever `AllocCache` returns a slice, it also ensures an
/// [`Anchor`] is responsible for keeping the slice's backing memory
/// alive.
#[derive(Debug)]
pub struct AllocCache {
    bump: *mut MaybeUninit<u8>,
    range: Range<*mut MaybeUninit<u8>>, // XXX: redundant with `backing`.
    backing: Arc<Chunk>,                // Backing memory for `AllocCache`.
}

// AllocCache is thread-compatible
unsafe impl Send for AllocCache {}
unsafe impl Sync for AllocCache {}

impl AllocCache {
    /// Returns a fresh [`AllocCAche`] that has capacity at least equal to `wanted`,
    /// and equal to `hint` if possible.
    #[must_use]
    pub fn new(wanted: usize, hint: usize) -> AllocCache {
        let capacity = hint.max(wanted);
        assert!(capacity >= wanted);
        let mut storage = Vec::<MaybeUninit<u8>>::with_capacity(capacity);
        // SAFETY: MaybeUninit is always "initialised"
        unsafe { storage.set_len(capacity) };
        let mut chunk = Chunk::new(storage.into_boxed_slice());
        let range = chunk.as_mut_ptr_range();

        AllocCache {
            bump: range.start,
            range,
            backing: Arc::new(chunk),
        }
    }

    /// Returns the initial capacity allocated for the backing chunk
    /// (i.e., the size of the backing chunk).
    #[must_use]
    #[inline(always)]
    pub fn initial_size(&self) -> usize {
        (self.range.end as usize) - (self.range.start as usize)
    }

    /// Returns the address range for the backing chunk.
    #[must_use]
    #[inline(always)]
    pub fn range(&self) -> Range<usize> {
        Range {
            start: self.range.start as usize,
            end: self.range.end as usize,
        }
    }

    /// Returns the address of the next allocationn (one past the
    /// end of the most recent allocation).
    #[must_use]
    #[inline(always)]
    pub fn next_alloc_address(&self) -> usize {
        self.bump as usize
    }

    /// Returns the amount of space remaining in the backing chunk.
    #[must_use]
    #[inline(always)]
    pub fn remaining(&self) -> usize {
        assert!(self.range.start <= self.bump);
        assert!(self.bump <= self.range.end);
        let bump = self.bump as usize;
        let end = self.range.end as usize;

        assert!(bump <= end);
        end - bump
    }

    /// Allocates `wanted > 0` bytes and either makes `old_anchor`
    /// hold onto the returned slice's backing memory, or returns
    /// a fresh [`Anchor`].
    ///
    /// The caller *must* ensure `self.remaining() >= wanted` before
    /// calling this method.
    ///
    /// The `'static` lifetime on the slice is a lie; it lives as
    /// long as either `old_anchor`, or `anchor`.
    #[must_use]
    #[inline(always)]
    pub unsafe fn alloc_or_die(
        &mut self,
        wanted: usize,
        old_anchor: Option<&mut Anchor>,
    ) -> (IoSlice<'static>, Option<Anchor>) {
        assert!(self.range.start <= self.bump);
        assert!(self.bump <= self.range.end);

        let bump = self.bump as usize;
        let end = self.range.end as usize;
        assert!(end - bump >= wanted);

        // SAFETY: bump + wanted <= end
        let ret = ioslice::make_ioslice(self.bump as *mut u8, wanted);
        self.bump = unsafe { self.bump.add(wanted) };

        // Avoid cloning `self.backing` if possible.
        let anchor = Anchor::merge_ref_or_create(old_anchor, &self.backing);
        (ret, anchor)
    }

    /// Marks the bytes in `remainder` as available for new allocations.
    ///
    /// This `remainder` slice must come from allocation cache and stop
    /// right at the current bump pointer.
    pub fn release_or_die(&mut self, remainder: IoSlice<'_>) {
        let (base, len) = ioslice::ioslice_components(remainder);
        let addr = base as usize;
        let end_addr = addr + len;

        // The start address must be strictly in the backing chunk, unless
        // we have an empty remainder (at the tail of the chunk).
        assert!(self.range().contains(&addr) | remainder.is_empty());
        assert_eq!(self.bump as usize, end_addr);

        // SAFETY: `remainder` is fully in the backing chunk.
        self.bump = unsafe { self.bump.sub(len) };
    }
}

#[test]
fn test_new_miri() {
    let cache = AllocCache::new(10, 20);
    assert_eq!(cache.initial_size(), 20);
    assert_eq!(cache.remaining(), 20);
}

#[test]
fn test_alloc_or_die_miri() {
    let mut cache = AllocCache::new(10, 20);
    let (slice, anchor) = unsafe { cache.alloc_or_die(5, None) };
    assert_eq!(slice.len(), 5);
    assert!(anchor.is_some());
    assert_eq!(cache.remaining(), 15);
}

#[test]
fn test_release_or_die_miri() {
    let mut cache = AllocCache::new(10, 20);
    let (slice, _anchor) = unsafe { cache.alloc_or_die(5, None) };
    cache.release_or_die(slice);
    assert_eq!(cache.remaining(), 20);
}

#[test]
fn test_release_or_die_empty_miri() {
    let mut cache = AllocCache::new(20, 20);
    let (slice, _anchor) = unsafe { cache.alloc_or_die(20, None) };
    cache.release_or_die(IoSlice::new(&slice[20..]));
    assert_eq!(cache.remaining(), 0);
}

#[test]
fn test_alloc_and_release_miri() {
    let mut cache = AllocCache::new(10, 20);
    let (slice1, anchor1) = unsafe { cache.alloc_or_die(5, None) };
    let (slice2, _anchor2) = unsafe { cache.alloc_or_die(10, Some(&mut anchor1.unwrap())) };
    assert_eq!(slice1.len(), 5);
    assert_eq!(slice2.len(), 10);
    assert_eq!(cache.remaining(), 5);
    cache.release_or_die(slice2);
    assert_eq!(cache.remaining(), 15);
}

#[test]
#[should_panic(expected = "end - bump >= wanted")]
fn test_alloc_too_large_miri() {
    let mut cache = AllocCache::new(10, 20);
    let _result = unsafe { cache.alloc_or_die(21, None) };
}

#[test]
#[should_panic(expected = "assertion failed")]
fn test_release_invalid_slice_miri() {
    let mut cache = AllocCache::new(10, 20);
    let mut vec = Vec::with_capacity(5);

    // Assume init to make clippy happy. Hopefully MIRI
    // can still see that it wasn't actually initialised:
    // we shouldn't read from the bad slice.
    for slot in vec.spare_capacity_mut() {
        unsafe { slot.assume_init_mut() };
    }
    unsafe { vec.set_len(5) };

    let slice = IoSlice::new(&vec);
    cache.release_or_die(slice);
}
