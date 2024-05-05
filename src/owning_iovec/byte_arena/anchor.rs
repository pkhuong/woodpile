use std::mem::MaybeUninit;
use std::num::NonZeroUsize;
use std::ptr::NonNull;
use std::sync::Arc;

/// Conceptually, [`Chunk`] is a `Box<[u8]>`, but we convert to/from
/// [`NonNull`] at construction and destruction in order to avoid
/// aliasing footguns.
#[derive(Debug)]
pub struct Chunk {
    storage: NonNull<[MaybeUninit<u8>]>,
}

impl Chunk {
    pub fn new(storage: Box<[MaybeUninit<u8>]>) -> Chunk {
        Chunk {
            storage: NonNull::from(Box::leak(storage)),
        }
    }
}

// We don't use the raw pointer until it's time to `Drop`.
unsafe impl Send for Chunk {}
unsafe impl Sync for Chunk {}

impl Drop for Chunk {
    fn drop(&mut self) {
        unsafe { std::mem::drop(Box::from_raw(self.storage.as_mut())) }
    }
}

/// Each [`Anchor`] keeps a chunk of backing memory alive on behalf of
/// a number of allocations.
#[derive(Clone, Debug, Default)]
pub struct Anchor {
    count: usize,
    chunk: Option<Arc<Chunk>>,
}

impl Anchor {
    #[inline(always)]
    fn new(count: NonZeroUsize, chunk: Arc<Chunk>) -> Self {
        Anchor {
            count: count.into(),
            chunk: Some(chunk),
        }
    }

    #[inline(always)]
    pub fn new_with_count(count: NonZeroUsize) -> Self {
        Anchor {
            count: count.into(),
            chunk: None,
        }
    }

    #[inline(always)]
    pub fn count(&self) -> usize {
        self.count
    }

    #[inline(always)]
    pub fn increment_count(&mut self) {
        self.count += 1
    }

    #[inline(always)]
    pub fn decrement_count(&mut self, decrement: usize) -> usize {
        let can_take = self.count.min(decrement);
        self.count -= can_take;
        decrement - can_take
    }

    fn is_same_chunk(&self, chunk: &Arc<Chunk>) -> bool {
        match self.chunk.as_ref() {
            Some(this) => Arc::ptr_eq(this, chunk),
            None => false,
        }
    }

    /// Increments `count` in `anchor` if it's populated and matches `chunk`.
    ///
    /// Returns a fresh anchor otherwise.
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
