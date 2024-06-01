use std::collections::BTreeSet;
use std::collections::HashMap;
use std::io::Result;
use std::path::PathBuf;
use std::sync::Arc;

pub type Record = crate::pile_reader::Record;

#[derive(Clone, Debug)]
pub struct Pile {
    log_directory: Arc<PathBuf>,
    time_bucket: time::PrimitiveDateTime,
    progress_so_far: HashMap<PathBuf, u64>,
    cache: BTreeSet<Record>,
    finalized: bool,
}

impl Pile {
    pub fn new(log_directory: Arc<PathBuf>, time_bucket: time::PrimitiveDateTime) -> Pile {
        Pile {
            log_directory,
            time_bucket,
            progress_so_far: HashMap::new(),
            cache: BTreeSet::new(),
            finalized: false,
        }
    }

    pub fn update(
        &mut self,
        now: crate::VouchedTime,
        options: crate::pile_reader::PileReaderOptions,
    ) -> Result<()> {
        if self.finalized {
            return Ok(());
        }

        let reader = crate::pile_reader::PileReader::open(
            (*self.log_directory).clone(),
            self.time_bucket,
            now,
            options,
            Some(&self.progress_so_far),
        )?;

        match reader {
            crate::pile_reader::PileReaderState::Stable(reader) => {
                // XXX: it would make sense to derive an index from the snapshot,
                // and filted based on that.
                self.cache.clear();
                self.progress_so_far.clear();
                for record in reader {
                    self.cache.insert(record?);
                }
                self.finalized = true;
            }
            crate::pile_reader::PileReaderState::Peek(mut reader) => {
                for record in reader.iter() {
                    self.cache.insert(record?);
                }

                for (key, offset) in reader.into_offsets() {
                    self.progress_so_far.insert(key, offset);
                }
            }
        }

        Ok(())
    }

    pub fn range(
        &self,
        range: impl std::ops::RangeBounds<time::PrimitiveDateTime>,
    ) -> impl Iterator<Item = &Record> {
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
