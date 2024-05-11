#![deny(unsafe_op_in_unsafe_fn)]

use std::mem::MaybeUninit;
use std::ops::Range;
use std::sync::Arc;

use super::anchor::Anchor;
use super::anchor::Chunk;

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
    #[inline(always)]
    pub fn initial_size(&self) -> usize {
        (self.range.end as usize) - (self.range.start as usize)
    }

    /// Returns the address range for the backing chunk.
    #[inline(always)]
    pub fn range(&self) -> Range<usize> {
        Range {
            start: self.range.start as usize,
            end: self.range.end as usize,
        }
    }

    /// Returns the address of the next allocationn (one past the
    /// end of the most recent allocation).
    #[inline(always)]
    pub fn next_alloc_address(&self) -> usize {
        self.bump as usize
    }

    /// Returns the amount of space remaining in the backing chunk.
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
    #[inline(always)]
    pub unsafe fn alloc_or_die(
        &mut self,
        wanted: usize,
        old_anchor: Option<&mut Anchor>,
    ) -> (&'static mut [MaybeUninit<u8>], Option<Anchor>) {
        assert!(self.range.start <= self.bump);
        assert!(self.bump <= self.range.end);

        let bump = self.bump as usize;
        let end = self.range.end as usize;
        assert!(end - bump >= wanted);

        // SAFETY: bump + wanted <= end
        let ret = unsafe { std::slice::from_raw_parts_mut(self.bump, wanted) };
        self.bump = unsafe { self.bump.add(wanted) };

        // Avoid cloning `self.backing` if possible.
        let anchor = Anchor::merge_ref_or_create(old_anchor, &self.backing);
        (ret, anchor)
    }

    /// Marks the bytes in `remainder` as available for new allocations.
    ///
    /// This `remainder` slice must come from allocation cache and stop
    /// right at the current bump pointer.
    pub fn release_or_die(&mut self, remainder: &[MaybeUninit<u8>]) {
        let addr = remainder.as_ptr() as usize;
        let end_addr = addr + remainder.len();

        assert!(self.range().contains(&addr));
        assert_eq!(self.bump as usize, end_addr);

        // SAFETY: `remainder` is fully in the backing chunk.
        self.bump = unsafe { self.bump.sub(remainder.len()) };
    }
}
