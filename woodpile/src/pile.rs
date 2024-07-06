use std::collections::BTreeSet;
use std::collections::HashMap;
use std::io::Result;
use std::path::PathBuf;
use std::sync::Arc;

use vouched_time::VouchedTime;

use crate::pile_reader;

pub type Record = pile_reader::Record;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PileState {
    /// Still reading new records
    Active,
    /// Epoch is closed, just wait for the finalized result
    Pending,
    /// Fully finalized, no need for more I/O
    Finalized,
}

#[derive(Clone, Debug)]
pub struct Pile {
    log_directory: Arc<PathBuf>,
    time_bucket: time::PrimitiveDateTime,
    progress_so_far: HashMap<PathBuf, u64>,
    cache: BTreeSet<Arc<Record>>,
    state: PileState,
}

impl Pile {
    pub fn new(log_directory: Arc<PathBuf>, time_bucket: time::PrimitiveDateTime) -> Pile {
        Pile {
            log_directory,
            time_bucket,
            progress_so_far: HashMap::new(),
            cache: BTreeSet::new(),
            state: PileState::Active,
        }
    }

    // Determines whether the pile is in the same state as a newly created instance.
    #[inline(always)]
    pub fn is_at_initial_state(&self) -> bool {
        self.cache.is_empty() & self.progress_so_far.is_empty() & (self.state == PileState::Active)
    }

    pub fn update(
        &mut self,
        now: VouchedTime,
        options: pile_reader::PileReaderOptions,
    ) -> Result<()> {
        let reader = match self.state {
            // Active => just keep reading.
            PileState::Active => pile_reader::PileReader::open(
                (*self.log_directory).clone(),
                self.time_bucket,
                now,
                options,
                Some(&self.progress_so_far),
            )?,
            // Pending => wait for a summary
            PileState::Pending => pile_reader::PileReader::open_summary(
                (*self.log_directory).clone(),
                self.time_bucket,
                now,
                options,
                Some(&self.progress_so_far),
            )?,
            // Finalized => nothing to do.
            PileState::Finalized => return Ok(()),
        };

        let mut update_unstable = |mut reader: pile_reader::PileReader| -> Result<()> {
            for record in reader.iter() {
                self.cache.insert(Arc::new(record?));
            }

            for (key, offset) in reader.into_offsets() {
                self.progress_so_far.insert(key, offset);
            }

            Ok(())
        };

        match reader {
            pile_reader::PileReaderState::Peek(reader) => {
                if self.state == PileState::Active {
                    update_unstable(reader)?;
                }
            }
            pile_reader::PileReaderState::Pending(reader) => {
                if self.state == PileState::Active {
                    update_unstable(reader)?;

                    self.state = PileState::Pending;
                }
            }
            pile_reader::PileReaderState::Stable(reader) => {
                // Insert any *new* record.
                for record in reader {
                    self.cache.insert(Arc::new(record?));
                }

                // Don't need this anymore.
                self.progress_so_far = HashMap::new();
                self.state = PileState::Finalized;
            }
            pile_reader::PileReaderState::StableRecovery(reader) => {
                // Re-read everything.
                self.cache.clear();
                self.progress_so_far.clear();
                for record in reader {
                    self.cache.insert(Arc::new(record?));
                }

                // Won't need this again.
                self.progress_so_far = HashMap::new();
                self.state = PileState::Finalized;
            }
        }

        Ok(())
    }

    pub fn range(
        &self,
        range: &impl std::ops::RangeBounds<time::PrimitiveDateTime>,
    ) -> impl Iterator<Item = &Arc<Record>> {
        use std::ops::Bound;

        fn min_record(timestamp: time::PrimitiveDateTime) -> Record {
            Record {
                timestamp,
                record_id: [0u8; 16],
                checksum: [0u8; 32],
                payload: Box::new([]),
            }
        }

        fn max_record(timestamp: time::PrimitiveDateTime) -> Record {
            Record {
                timestamp,
                record_id: [255u8; 16],
                checksum: [255u8; 32],
                payload: Box::new([]),
            }
        }

        let start = match range.start_bound() {
            Bound::Included(timestamp) => Bound::Included(min_record(*timestamp)),
            Bound::Excluded(timestamp) => Bound::Excluded(max_record(*timestamp)),
            Bound::Unbounded => Bound::Unbounded,
        };

        let end = match range.end_bound() {
            Bound::Included(timestamp) => Bound::Included(max_record(*timestamp)),
            Bound::Excluded(timestamp) => Bound::Excluded(min_record(*timestamp)),
            Bound::Unbounded => Bound::Unbounded,
        };

        self.cache.range((start, end))
    }
}
