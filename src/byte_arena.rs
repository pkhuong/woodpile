//! A `byte_arena` is an arena for [`[u8]`] slices.  It is very
//! closely inspired by rustc's `DroplessArena`, except that multiple
//! arenas can share the share underlying backing store (but
//! allocation caches are private).
//!
//! It is only meant for internal use, and lies by returning `'static`
//! lifetime values. The only user, `OwningIovec`, guarantees that the
//! returned allocations don't outlive the arena's backing store.
#![deny(unsafe_op_in_unsafe_fn)]

use std::mem::MaybeUninit;
use std::num::NonZeroUsize;
use std::ops::Range;
use std::ptr::NonNull;
use std::sync::Arc;
use std::sync::Mutex;

/// A [`ByteArena`] consists of an allocation cache (a bump pointer region)
/// and a potentially shared `BackingStore`.  All `AllocCache`s for a given
/// [`ByteArena`] come from its `BackingStore`, and partition out subslices
/// from allocations owned by the `BackingStore`.
///
/// This type is only expected to be used via [`crate::OwningIovec`]
#[derive(Debug, Default)]
pub struct ByteArena {
    cache: AllocCache,
    backing: Arc<Mutex<BackingStore>>,
}

/// An [`AllocCache`] is a bump pointer in a range of pre-allocated [`MaybeUninit<u8>`].
#[derive(Debug)]
struct AllocCache {
    bump: *mut MaybeUninit<u8>,
    range: Range<*mut MaybeUninit<u8>>,
}

/// Conceptually, [`Chunk`] is a `Box<[u8]>`, but we convert to/from
/// [`NonNull`] at construction and destruction in order to avoid
/// aliasing footguns.
#[derive(Debug)]
struct Chunk {
    storage: NonNull<[MaybeUninit<u8>]>,
}

/// We don't use the raw pointer until it's time to `Drop`.
unsafe impl Send for Chunk {}
unsafe impl Sync for Chunk {}

impl Drop for Chunk {
    fn drop(&mut self) {
        unsafe { std::mem::drop(Box::from_raw(self.storage.as_mut())) }
    }
}

#[derive(Default, Debug)]
struct BackingStore {
    caches: Option<AllocCache>, // Only one cache for now
    chunks: Vec<Chunk>,
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

impl ByteArena {
    /// Creates a fresh arena, with a fresh backing store.
    #[inline(always)]
    pub fn new() -> ByteArena {
        Default::default()
    }

    /// Flushes the arena's internal allocation cache.
    #[inline(never)]
    pub fn flush_cache(&mut self) {
        use crate::ppp_lock::Update;

        if self.remaining() == 0 {
            return;
        }

        let mut cache = Default::default();
        std::mem::swap(&mut cache, &mut self.cache);
        self.backing
            .update_or_panic(|backing| backing.release_cache(cache));
    }

    /// Returns the number of bytes left in the current allocation cache.
    #[inline(always)]
    pub fn remaining(&self) -> usize {
        self.cache.remaining()
    }

    /// Determines whether `slice` was the last slice allocated by the
    /// [`ByteArena`]'s current allocation cache.
    #[inline(always)]
    pub fn is_last(&self, slice: &[u8]) -> bool {
        unsafe { self.contains(slice) }.is_some()
            & (slice.as_ptr_range().end == (self.cache.bump as *const _))
    }

    /// Ensure the current allocation cache has room for at least `len` bytes.
    #[inline(never)]
    pub fn ensure_capacity(&mut self, len: usize) {
        use crate::ppp_lock::Update;

        if self.remaining() >= len {
            return;
        }

        let mut cache = Default::default();
        std::mem::swap(&mut cache, &mut self.cache);

        // Find the "ideal" size if we have to allocate fresh.
        let hint = Self::find_hint_size(len, cache.initial_size());
        let new_cache = self.backing.update_or_panic(|backing| {
            backing.release_cache(cache);
            backing.acquire_cache(len, hint)
        });

        self.cache = new_cache;
        assert!(self.cache.remaining() >= len);
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
    /// The return value must not outlast the `ByteArena`.  We lie with `'static`
    /// because `ByteArena` is used in the self-referential `OwningIovec` class.
    #[inline(always)]
    pub(crate) unsafe fn contains(&self, slice: &[u8]) -> Option<&'static [u8]> {
        let range = &self.cache.range;
        let endpoints = slice.as_ptr_range();

        if ((range.start as usize) <= (endpoints.start as usize))
            & ((endpoints.end as usize) <= (range.end as usize))
        {
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
    /// The return value must not outlast the `ByteArena`.  We lie with `'static`
    /// because `ByteArena` is used in the self-referential `OwningIovec` class.
    #[inline(always)]
    pub(crate) unsafe fn try_join(&self, left: &[u8], right: &[u8]) -> Option<&'static [u8]> {
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
    fn grow_and_alloc(&mut self, len: usize) -> &'static mut [MaybeUninit<u8>] {
        self.ensure_capacity(len);
        unsafe { self.cache.try_alloc(len) }.expect("we just allocated capacity")
    }

    /// Allocates a slice of `len` bytes from this [`ByteArena`].
    ///
    /// # Safety
    ///
    /// The return value must not outlast the `ByteArena`.  We lie with `'static`
    /// because `ByteArena` is used in the self-referential `OwningIovec` class.
    #[inline(always)]
    pub(crate) unsafe fn alloc(&mut self, len: NonZeroUsize) -> &'static mut [MaybeUninit<u8>] {
        // The cache grabs bytes from a slice that belongs to
        // `self.backing`, so the storage lives at least as long as
        // `self`.
        let len: usize = len.into();
        if let Some(ret) = unsafe { self.cache.try_alloc(len) } {
            ret
        } else {
            self.grow_and_alloc(len)
        }
    }

    /// Allocates a copy of `src` from this `ByteArena`.  Panics if `src` is empty.
    ///
    /// # Safety
    ///
    /// The return value must not outlast the `ByteArena`.  We lie with `'static`
    /// because `ByteArena` is used in the self-referential `OwningIovec` class.
    #[inline(always)]
    pub(crate) unsafe fn copy(&mut self, src: &[u8]) -> &'static mut [u8] {
        // zero-sized allocation and memcpy have surprising aliasing consequences.
        assert!(!src.is_empty());

        let dst = unsafe { self.alloc(NonZeroUsize::new(src.len()).unwrap()) };

        let dst_ptr = dst.as_mut_ptr() as *mut u8;
        let len = dst.len();

        assert_eq!(len, src.len());
        unsafe { dst_ptr.copy_from_nonoverlapping(src.as_ptr(), len) };
        unsafe { std::slice::from_raw_parts_mut(dst_ptr, len) }
    }
}

impl Drop for ByteArena {
    fn drop(&mut self) {
        use crate::ppp_lock::TryUpdate;
        let mut cache: AllocCache = Default::default();
        std::mem::swap(&mut cache, &mut self.cache);

        // Don't block just to recycle a cache
        self.backing.try_update_flatten(|backing| {
            if let Some(backing) = backing {
                backing.release_cache(cache);
            }
        });
    }
}

impl Clone for ByteArena {
    fn clone(&self) -> ByteArena {
        ByteArena {
            cache: Default::default(),
            backing: self.backing.clone(),
        }
    }
}

// AllocCache is thread-compatible
unsafe impl Send for AllocCache {}
unsafe impl Sync for AllocCache {}

impl AllocCache {
    #[inline(always)]
    fn initial_size(&self) -> usize {
        (self.range.end as usize) - (self.range.start as usize)
    }

    #[inline(always)]
    fn remaining(&self) -> usize {
        assert!(self.range.start <= self.bump);
        assert!(self.bump <= self.range.end);
        let bump = self.bump as usize;
        let end = self.range.end as usize;

        assert!(bump <= end);
        end - bump
    }

    #[inline(always)]
    unsafe fn try_alloc(&mut self, wanted: usize) -> Option<&'static mut [MaybeUninit<u8>]> {
        assert!(self.range.start <= self.bump);
        assert!(self.bump <= self.range.end);

        let bump = self.bump as usize;
        let end = self.range.end as usize;

        if end - bump >= wanted {
            // SAFETY: bump + wanted <= end
            let ret = unsafe { std::slice::from_raw_parts_mut(self.bump, wanted) };
            self.bump = unsafe { self.bump.add(wanted) };
            Some(ret)
        } else {
            None
        }
    }
}

impl Default for AllocCache {
    #[inline(always)]
    fn default() -> Self {
        AllocCache {
            range: Range {
                start: std::ptr::null_mut(),
                end: std::ptr::null_mut(),
            },
            bump: std::ptr::null_mut(),
        }
    }
}

impl BackingStore {
    fn release_cache(&mut self, cache: AllocCache) {
        if cache.remaining() > 0 {
            self.caches = Some(cache);
        }
    }

    #[inline(never)]
    fn acquire_cache(&mut self, wanted: usize, hint: usize) -> AllocCache {
        // Use the cache if we can
        if matches!(self.caches.as_ref().map(AllocCache::remaining),
                    Some(remaining) if remaining >= wanted)
        {
            return self
                .caches
                .take()
                .expect("we just checked that we have a cache");
        }

        // Hafta create a fresh chunk.

        // We must return a slice for at least `wanted` bytes, and ideally at least `hint`.
        let capacity = hint.max(wanted);
        assert!(capacity >= wanted);
        let mut storage = Vec::<MaybeUninit<u8>>::with_capacity(capacity);
        // SAFETY: MaybeUninit is always "initialised"
        unsafe { storage.set_len(capacity) };
        let mut chunk = storage.into_boxed_slice();
        let range = chunk.as_mut_ptr_range();
        let chunk = Chunk {
            storage: NonNull::from(Box::leak(chunk)),
        };
        self.chunks.push(chunk);

        AllocCache {
            bump: range.start,
            range,
        }
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
