use std::collections::VecDeque;
use std::io::IoSlice;
use std::num::NonZeroUsize;

use super::byte_arena::Anchor;
use crate::sliding_deque::SlidingVec;

/// The `GlobalDeque` is a `SlidingDeque` of `IoSlice` that tracks the
/// current logical (monotonically icnreasing) position and size, and
/// maps between that and the physical locations, taking into account
/// the `IoSlice`s and bytes consumed.
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

    pub fn push_borrowed(&mut self, slice: IoSlice<'this>) {
        self.logical_size += slice.len() as u64;
        self.slices.push_back(slice);

        if self.anchors.is_empty() {
            self.anchors.push_back(Default::default());
        }

        self.anchors.back_mut().unwrap().increment_count();
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

        count
    }

    #[inline(always)]
    pub fn num_slices(&self) -> usize {
        self.slices.len()
    }

    // Returns the total number of bytes in the slices.
    #[inline(always)]
    pub fn total_size(&self) -> usize {
        (self.logical_size - self.consumed_size) as usize
    }

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
