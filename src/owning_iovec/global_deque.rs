use std::collections::VecDeque;
use std::io::IoSlice;
use std::num::NonZeroUsize;

use super::byte_arena::Anchor;
use crate::sliding_deque::SlidingVec;

/// The `GlobalDeque` is a `SlidingDeque` of `IoSlice` that tracks the
/// current logical (monotonically increasing) position and size, and
/// maps between that and the physical locations, taking into account
/// the `IoSlice`s and bytes consumed.
///
/// Each slice is also backed by one [`Anchor`] in `anchors`.  Slices
/// (and anchors) may be appended to the end of the [`GlobalDeque`],
/// merged at the end, or consumed from the front.  The caller ([`OwningIovec`])
/// is responsible for capping consumption if it holds backreferences
/// into `slices`.
///
/// The usage of the `this` lifetime can be unsound; we rely on constraints
/// on the surrounding [`OwningIovec`] to avoid dangling slices.
#[derive(Debug, Default, Clone)]
pub struct GlobalDeque<'this> {
    slices: SlidingVec<IoSlice<'this>>,
    anchors: VecDeque<Anchor>, // Each anchor is responsible for a contiguous number (> 0) of slices.
    logical_size: u64,
    consumed_size: u64,
    consumed_slices: u64,
}

impl<'this> GlobalDeque<'this> {
    pub fn new(slices: Vec<IoSlice<'this>>) -> Self {
        let logical_size = slices.iter().map(|slice| slice.len() as u64).sum();
        let mut anchors = VecDeque::new();

        if !slices.is_empty() {
            let count = NonZeroUsize::new(slices.len()).expect("slices isn't empty");
            anchors.push_back(Anchor::new_with_count(count));
        }

        GlobalDeque {
            slices: slices.into(),
            anchors,
            logical_size,
            consumed_size: 0,
            consumed_slices: 0,
        }
    }

    /// Pushes a new slice at the end of the deque.  If we have an anchor
    /// it's pushed to the back of the anchor deque; otherwise, we assume
    /// the current last anchor has been mutated in place to take the
    /// new slice into account.
    pub fn push(&mut self, entry: (IoSlice<'this>, Option<Anchor>)) {
        let (slice, anchor) = entry;
        self.logical_size += slice.len() as u64;
        self.slices.push_back(slice);
        if let Some(anchor) = anchor {
            self.anchors.push_back(anchor);
        } else {
            assert!(!self.anchors.is_empty());
        }
    }

    /// Pushes a borrowed slice (guaranteed to outlive the `GlobalDeque`)
    /// at the end of the deque.
    pub fn push_borrowed(&mut self, slice: IoSlice<'this>) {
        self.logical_size += slice.len() as u64;
        self.slices.push_back(slice);

        if self.anchors.is_empty() {
            self.anchors.push_back(Default::default());
        }

        self.anchors.back_mut().unwrap().increment_count();
    }

    pub fn push_anchor(&mut self, mut anchor: Anchor) {
        anchor.decrement_count(anchor.count());
        self.anchors.push_back(anchor);
    }

    #[inline(always)]
    pub fn last_anchor(&mut self) -> Option<&mut Anchor> {
        self.anchors.back_mut()
    }

    #[inline(always)]
    pub fn last_slice(&self) -> Option<IoSlice<'this>> {
        self.slices.last().copied()
    }

    #[inline(always)]
    pub fn logical_size(&self) -> u64 {
        self.logical_size
    }

    #[inline(always)]
    pub fn last_logical_slice_index(&self) -> u64 {
        self.consumed_slices + (self.slices.len() as u64) - 1
    }

    #[inline(always)]
    pub fn get_logical_slice(&self, index: u64) -> Option<IoSlice<'this>> {
        let index = index
            .wrapping_sub(self.consumed_slices)
            .min(usize::MAX as u64) as usize;

        self.slices.get(index).copied()
    }

    /// Gets the prefix of slices we can look at *before* the logical slice index
    /// `end_logical_slice`.
    #[inline(always)]
    pub fn get_logical_prefix(&self, end_logical_slice: Option<u64>) -> &[IoSlice<'this>] {
        let end_logical_slice = end_logical_slice.unwrap_or(u64::MAX);
        let remainder = end_logical_slice - self.consumed_slices;
        let take = remainder.min(self.slices.len() as u64) as usize;

        &self.slices[..take]
    }

    /// Drops the first `count` slices in the deque.
    #[inline(never)]
    pub fn consume(&mut self, count: usize) -> usize {
        let count = count.min(self.slices.len());

        let consumed_size: u64 = self.slices[..count]
            .iter()
            .map(|slice| slice.len() as u64)
            .sum();
        self.consumed_size += consumed_size;
        self.consumed_slices += count as u64;

        let consumed = self.slices.advance(count);
        assert_eq!(consumed, count);

        let mut num_to_drain = consumed;
        while num_to_drain > 0 {
            let front = self
                .anchors
                .front_mut()
                .expect("must have front if we consumed some slices");
            num_to_drain = front.decrement_count(num_to_drain);
            if front.count() == 0 {
                // We made progress!
                self.anchors.pop_front();
            } else {
                // Or we're done.
                assert_eq!(num_to_drain, 0);
            }
        }

        // Drop any zero-count anchor at the front.
        while let Some(anchor) = self.anchors.front() {
            if anchor.count() > 0 {
                break;
            }

            self.anchors.pop_front();
        }

        // slices js empty iff anchors are as well.
        assert!(self.slices.is_empty() == self.anchors.is_empty());

        count
    }

    /// Drops the first `count` bytes in the deque.  Any partially consumed
    /// final slice is advanced in place.
    #[inline(never)]
    pub fn consume_by_bytes(&mut self, count: usize) -> usize {
        let mut consumed = 0;

        while consumed < count {
            let slice = self
                .slices
                .front_mut()
                .expect("OwningIovec bound-checks upstream");

            let len = slice.len();
            let num_to_consume = (count - consumed).min(slice.len());
            let ptr = slice.as_ptr();

            let new_slice = unsafe {
                std::slice::from_raw_parts(ptr.add(num_to_consume), len - num_to_consume)
            };
            if new_slice.is_empty() {
                // XXX: should we consume the full sized slices in bulk?
                self.consume(1);
            } else {
                *slice = IoSlice::new(new_slice);
                self.consumed_size += num_to_consume as u64;
                assert_eq!(num_to_consume, count - consumed);
            }

            consumed += num_to_consume;
        }

        consumed
    }

    /// Returns the total number of slices.
    #[inline(always)]
    pub fn num_slices(&self) -> usize {
        self.slices.len()
    }

    /// Returns the total number of bytes in the slices.
    #[inline(always)]
    pub fn total_size(&self) -> usize {
        (self.logical_size - self.consumed_size) as usize
    }

    /// Attempts to collapse the last two slices in the deque into a
    /// single slice, if it's safe to do so.
    pub fn maybe_collapse_last_pair(
        &mut self,
        collapse: impl FnOnce(IoSlice<'this>, IoSlice<'this>) -> Option<IoSlice<'this>>,
    ) {
        let len = self.slices.len();
        if len < 2 {
            return;
        }

        let anchor = self
            .anchors
            .back_mut()
            .expect("must have anchor for slices");
        assert!(anchor.count() > 0);
        if anchor.count() < 2 {
            return;
        }

        if let Some(merger) = collapse(self.slices[len - 2], self.slices[len - 1]) {
            self.slices.pop_back();
            *self.slices.back_mut().unwrap() = merger;
            // We can only collapse when the two slices are from the same
            // chunk, so we only had one for both anchor.
            anchor.decrement_count(1);
        }
    }
}
