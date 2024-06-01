//! Allocations in a `ByteArena` consist of `u8` slices kept alive by an [`Anchor`].
//! Each anchor contains an [`Arc<Chunk>`], which keeps a backing allocation
//! alive.  One [`Arc`] per allocation would be wasteful, so each [`Anchor`]
//! may be responsible for any number of slices.
//!
//! The relationship between slices and [`Anchor`]s is hard to express
//! in Rust, so we instead expose an unsafe *internal* interface with
//! `&'static` slices, and wrap in the simpler `OwningIovec`.

use std::mem::MaybeUninit;
use std::num::NonZeroUsize;
use std::ptr::NonNull;
use std::sync::atomic::AtomicUsize;
use std::sync::Arc;

pub static NUM_LIVE_CHUNKS: AtomicUsize = AtomicUsize::new(0);
pub static NUM_LIVE_BYTES: AtomicUsize = AtomicUsize::new(0);

/// Conceptually, [`Chunk`] is a `Box<[u8]>`, but we convert to/from
/// [`NonNull`] at construction and destruction in order to avoid
/// aliasing footguns.
#[derive(Debug)]
pub struct Chunk {
    storage: NonNull<[MaybeUninit<u8>]>,
}

impl Chunk {
    #[must_use]
    pub fn new(storage: Box<[MaybeUninit<u8>]>) -> Chunk {
        use std::sync::atomic::Ordering;
        NUM_LIVE_CHUNKS.fetch_add(1, Ordering::Relaxed);
        NUM_LIVE_BYTES.fetch_add(storage.len(), Ordering::Relaxed);

        Chunk {
            storage: NonNull::from(Box::leak(storage)),
        }
    }

    #[must_use]
    #[inline(always)]
    pub fn as_mut_ptr_range(&mut self) -> std::ops::Range<*mut MaybeUninit<u8>> {
        unsafe { self.storage.as_mut() }.as_mut_ptr_range()
    }
}

// We don't use the raw pointer until it's time to `Drop`.
unsafe impl Send for Chunk {}
unsafe impl Sync for Chunk {}

impl Drop for Chunk {
    fn drop(&mut self) {
        use std::sync::atomic::Ordering;

        let storage = unsafe { Box::from_raw(self.storage.as_mut()) };
        let capacity = storage.len();
        std::mem::drop(storage);

        NUM_LIVE_CHUNKS.fetch_sub(1, Ordering::Relaxed);
        NUM_LIVE_BYTES.fetch_sub(capacity, Ordering::Relaxed);
    }
}

/// Each [`Anchor`] keeps a chunk of backing memory alive on behalf of a
/// number of allocations.
#[derive(Clone, Debug, Default)]
pub struct Anchor {
    count: usize,              // Number of slices that are backed by this [`Anchor`]
    chunk: Option<Arc<Chunk>>, // Sticky once populated
}

impl Anchor {
    /// Constructs a fresh anchor with a strictly positive use count.  The
    /// positive `count` isn't a requirement, and the value *will* hit zero
    /// during normal operations, but it's usually a programming mistake to
    /// initialise an [`Anchor`] with a zero (ref) count.
    #[must_use]
    #[inline(always)]
    fn new(count: NonZeroUsize, chunk: Arc<Chunk>) -> Self {
        Anchor {
            count: count.into(),
            chunk: Some(chunk),
        }
    }

    /// Constructs a fresh anchor with no backing chunk.
    ///
    /// An anchor may start out with no backing chunk when it's used to
    /// represent the ownership of borrowed slices.  It's safe to attach a
    /// chunk to an `Anchor` after the fact: in the worst case, this only
    /// extends the chunk's lifetime.  That's why it's also safe to increment
    /// `count` when a borrowed slice is attached to an [`Anchor`].
    #[must_use]
    #[inline(always)]
    pub fn new_with_count(count: NonZeroUsize) -> Self {
        Anchor {
            count: count.into(),
            chunk: None,
        }
    }

    /// Returns the number of slices backed by this `Anchor`.
    #[must_use]
    #[inline(always)]
    pub fn count(&self) -> usize {
        self.count
    }

    /// Increments the number of slices backed by this `Anchor`.
    #[inline(always)]
    pub fn increment_count(&mut self) {
        self.count += 1
    }

    /// Decrements the internal (reference) count by up to `decrement`:
    /// the `count` value stops at 0.
    ///
    /// Returns the extra value in `decrement` that could not be
    /// subtracted from `count`.
    #[inline(always)]
    pub fn decrement_count(&mut self, decrement: usize) -> usize {
        let can_take = self.count.min(decrement);
        self.count -= can_take;
        decrement - can_take
    }

    /// Determins whether this [`Anchor`] holds on to the same
    /// [`Chunk`] as `chunk`.
    #[must_use]
    #[inline(always)]
    fn is_same_chunk(&self, chunk: &Arc<Chunk>) -> bool {
        match self.chunk.as_ref() {
            Some(this) => Arc::ptr_eq(this, chunk),
            None => false,
        }
    }

    /// Increments `count` in `anchor` if it's populated and matches `chunk`.
    ///
    /// Returns a fresh anchor otherwise.
    #[must_use]
    pub fn merge_ref_or_create(anchor: Option<&mut Self>, chunk: &Arc<Chunk>) -> Option<Self> {
        let success = match anchor {
            Some(anchor) if anchor.is_same_chunk(chunk) => {
                anchor.count += 1;
                true
            }
            _ => false,
        };

        if success {
            None
        } else {
            Some(Anchor::new(NonZeroUsize::new(1).unwrap(), chunk.clone()))
        }
    }
}
