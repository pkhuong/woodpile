//! The `pile_reader` module defines the low-level logic to (re)read
//! from all the log shard files in a given pile (time bucket)
//! directory.
use std::collections::HashMap;
use std::fs::File;
use std::io::Result;
use std::ops::Range;
use std::path::PathBuf;

use time::Duration;

use crate::shard_reader::ShardReader;

pub type Record = crate::shard_reader::Record;

pub const DEFAULT_MAX_RECORD_SIZE: usize = 1024 * 1024 + 1024; // 1 MB plus some overhead.

/// Default time between the official write deadline, and readers forcibly closing
/// the pile directory.  In the worst case, a writer acquires its lease just as we
/// switch to a fresh pile directory.  That pile can remain open for slightly less
/// than 10 seconds (EPOCH_WRITE_DURATION + CLOCK_ERROR_BOUND + EPOCH_WRITE_LEEWAY).
/// If we then wait 9 seconds, writes can stay indeterminate for up to 19 seconds.
///
/// That's OK, as long as leases are clearly longer than 19 seconds (e.g., 30 seconds),
/// and renewed before there are less than 20 seconds left.
pub const DEFAULT_FORCE_CLOSE_GRACE_PERIOD: Duration = Duration::seconds(9);

/// A [`PileReader`] grabs all the records from *one* timestamped directory in a log.
///
/// It acts as an iterator over all the records in the directory's log files.
#[derive(Debug)]
pub struct PileReader {
    // The second value is the ranges of encoded bytes in the
    // underlying file we read to yield the records so far.
    current_reader: Option<(ShardReader<File>, Range<u64>)>,
    pile_dir: PathBuf,
    // index in `source_files` for the *next* source path
    next_source_file: usize,
    // Vector of source file path and offset where to start reads;
    // the PathBuf is the suffix after `pile_dir`.
    source_files: Vec<(PathBuf, u64)>,
    max_record_size: usize,
}

/// How should a [`PileReader`] interact with the filesystem that
/// backs the pile epoch subdirectory?
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PileReaderMode {
    /// Error out instead of writing to the subdirectory
    ReadOnly,
    /// Write to the subdirectory without fsync (default, because we
    /// expect reliable remote NFS)
    Unsynced,
    /// Write to the subdirectory and (mostly) fsync where needed
    Fsync,
}

#[derive(Clone, Copy, Debug)]
pub struct PileReaderOptions {
    /// In read-only mode, creating a new [`PileReader`] never
    /// (directly, atime updates could still happen) writes to files
    /// or modifies the pile's directory structure.  When a pile would
    /// *have* to be closed due to `force_close_grace_period`, [`PileReader::open`]
    /// instead returns an error, with `ErrorKind::Other`.
    pub mode: PileReaderMode,
    /// Records larger than this many bytes will be dropped without
    /// reconstructing in memory
    pub max_record_size: usize,
    /// Forcibly close any timestamped pile once more than the grace
    /// period has elapsed since that pile's write deadline.  Strictly
    /// speaking, this knob does not impact the correctness of reads,
    /// but see the documentation for [`DEFAULT_FORCE_CLOSE_GRACE_PERIOD`]
    /// for the interaction with leases.
    ///
    /// In general, a larger value here helps avoid a slow path in readers,
    /// as long as a background process closes pile directories promptly.
    pub force_close_grace_period: Duration,
}

impl Default for PileReaderOptions {
    fn default() -> PileReaderOptions {
        PileReaderOptions {
            mode: PileReaderMode::Unsynced,
            max_record_size: DEFAULT_MAX_RECORD_SIZE,
            force_close_grace_period: DEFAULT_FORCE_CLOSE_GRACE_PERIOD,
        }
    }
}

/// When we open a pile directory with [`PileReader::open`], we may or
/// may not have a stable snapshot.
///
/// If we have a snapshot, the reader's state is `PileReaderState::Stable`:
/// all records in the reader are guaranteed to have made it to the pile.
///
/// Otherwise, the reader is a `PilereaderState::Peek`, and we may
/// find records that will disappear once in a `Stable` state.
/// However, assuming correct lease management, these transient records
/// will be associated with timestamps after the most recent lease
/// acquisition (i.e., with a lease that's still in flight).  By the
/// time the lease is released, the pile will have a stable snapshot.
#[derive(Debug)]
pub enum PileReaderState {
    /// In a `Peek` state, the [`PileReader`] may yield transient
    /// records that will eventually disappear.
    Peek(PileReader),
    /// In a `Stable` state, the [`PileReader`] only yields records
    /// that have successfully been committed.
    Stable(StablePileReader),
}

/// A `StablePileReader` is a `PileReader` that only returns records
/// that are guaranteed to have committed.
#[derive(Debug)]
pub struct StablePileReader {
    inner: PileReader,
}

impl From<PileReaderState> for PileReader {
    #[inline(always)]
    fn from(value: PileReaderState) -> PileReader {
        match value {
            PileReaderState::Peek(reader) => reader,
            PileReaderState::Stable(reader) => reader.into(),
        }
    }
}

impl TryFrom<PileReaderState> for StablePileReader {
    type Error = &'static str;

    fn try_from(value: PileReaderState) -> std::result::Result<StablePileReader, &'static str> {
        match value {
            PileReaderState::Peek(_) => Err("PileReaderState is Peek"),
            PileReaderState::Stable(reader) => Ok(reader),
        }
    }
}

impl From<StablePileReader> for PileReader {
    #[inline(always)]
    fn from(value: StablePileReader) -> PileReader {
        value.inner
    }
}

impl std::ops::Deref for PileReaderState {
    type Target = PileReader;

    #[inline(always)]
    fn deref(&self) -> &PileReader {
        match self {
            PileReaderState::Peek(reader) => reader,
            PileReaderState::Stable(reader) => reader,
        }
    }
}

impl std::ops::DerefMut for PileReaderState {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut PileReader {
        match self {
            PileReaderState::Peek(reader) => reader,
            PileReaderState::Stable(reader) => reader,
        }
    }
}

impl std::ops::Deref for StablePileReader {
    type Target = PileReader;

    #[inline(always)]
    fn deref(&self) -> &PileReader {
        &self.inner
    }
}

impl std::ops::DerefMut for StablePileReader {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut PileReader {
        &mut self.inner
    }
}

impl PileReader {
    /// Creates a new `PileReader` from a vector of pairs, where
    /// the first element is the path to the log file, and the second
    /// is the byte offset at which we should start reading records.
    ///
    /// If `max_record_size` is provided, records with a decoded size
    /// larger than that maximum value are dropped on the fly.  If
    /// `max_record_size` is `None`, we use [`DEFAULT_MAX_RECORD_SIZE`].
    pub fn new_from_source_files(
        pile_dir: PathBuf,
        source_files: Vec<(PathBuf, u64)>,
        max_record_size: Option<usize>,
    ) -> Self {
        PileReader {
            current_reader: None,
            pile_dir,
            next_source_file: 0,
            source_files,
            max_record_size: max_record_size.unwrap_or(DEFAULT_MAX_RECORD_SIZE),
        }
    }

    /// Attempts to create a new `PileReader` for the (primary) pile
    /// that contains data for `time` in `log_directory`.
    ///
    /// The `start_offsets`, if provided, map from file path to the
    /// offset at which we can find fresh records.
    pub fn open(
        log_directory: PathBuf,
        time: time::PrimitiveDateTime,
        now: crate::VouchedTime,
        options: PileReaderOptions,
        start_offsets: Option<&HashMap<PathBuf, u64>>,
    ) -> Result<PileReaderState> {
        let empty = HashMap::new();
        let start_offsets = start_offsets.unwrap_or(&empty);
        let (pile_dir, write_deadline) = crate::construct_epoch_subdirectory(log_directory, time);

        // Generating the path for the summary file also flushes the NFS caches if
        // necessary (just enough so we don't get spurious ENOENT on the hierarchy).
        let summary_path = crate::close::closed_subdir_summary_path(pile_dir.clone());

        // Handle a missing directory like an empty pile.
        if matches!(pile_dir.metadata(), Err(e) if e.kind() == std::io::ErrorKind::NotFound) {
            return Ok(PileReaderState::Peek(PileReader::new_from_source_files(
                pile_dir,
                vec![],
                Some(options.max_record_size),
            )));
        }

        let close_time = write_deadline
            .saturating_add(crate::EPOCH_WRITE_LEEWAY)
            .saturating_add(crate::CLOCK_ERROR_BOUND)
            .saturating_add(options.force_close_grace_period.max(time::Duration::ZERO));

        if now.get_local_time() > close_time {
            // Must forcibly close the directory.

            // Can't do that in read-only mode.
            if options.mode == PileReaderMode::ReadOnly {
                return Err(std::io::Error::other(
                    "Pile directory past closing time, but PileReader is read-only.",
                ));
            }

            let fsync = options.mode == PileReaderMode::Fsync;
            let _ = crate::close::close_epoch_subdir(
                pile_dir.clone(),
                now,
                crate::close::CloseEpochOptions { fsync },
            )?;
        }

        let mut logs: Vec<(PathBuf, u64)> = Vec::new();

        let mut pile_dir_dirents = pile_dir.read_dir()?.peekable();
        // Force an initial read, which should reliably flush any
        // cached NFS handle.
        let _ = pile_dir_dirents.peek();

        // See if we have a summary file.
        if summary_path.is_file() {
            let path = summary_path
                .strip_prefix(&pile_dir)
                .expect("summary file must be under pile dir")
                .to_path_buf();
            let start_offset = start_offsets.get(&path).copied().unwrap_or(0);
            logs.push((path, start_offset));
        }

        // If we have one path in the `logs` vector, we have a stable
        // snapshot.
        let stable = !logs.is_empty();

        // If we don't have a summary file, go for the individual log files.
        if logs.is_empty() {
            logs = pile_dir_dirents
                .map(|item| -> Result<Option<(PathBuf, u64)>> {
                    let name = item?.file_name();
                    assert_eq!(crate::LOG_EXTENSION, "log");
                    if name.as_encoded_bytes().ends_with(b".log") {
                        let path = PathBuf::from(name);
                        let start_offset = start_offsets.get(&path).copied().unwrap_or(0);
                        Ok(Some((path, start_offset)))
                    } else {
                        Ok(None)
                    }
                })
                .flat_map(|item| item.transpose())
                .collect::<Result<Vec<_>>>()?;
        }

        logs.sort();

        let reader =
            PileReader::new_from_source_files(pile_dir, logs, Some(options.max_record_size));
        Ok(if stable {
            PileReaderState::Stable(StablePileReader { inner: reader })
        } else {
            PileReaderState::Peek(reader)
        })
    }

    /// Returns the current mapping from log file path to start offset
    /// where we may find fresh records.
    ///
    /// Each PathBuf is relative to the pile directory.
    pub fn start_offsets(&self) -> &[(PathBuf, u64)] {
        &self.source_files
    }

    /// Returns the current mapping from log file path to start offset
    /// where we may find fresh records.
    ///
    /// Each PathBuf is relative to the pile directory.
    pub fn into_offset(self) -> Vec<(PathBuf, u64)> {
        self.source_files
    }

    /// Returns whether the pile directory is empty.
    ///
    /// N.B., a non-empty `PileReader` may yield 0 record in the end.
    pub fn is_empty(&self) -> bool {
        self.source_files.is_empty()
    }

    /// Attempts to decode the next record in the pile.  Returns
    /// `Ok(None)` once we're reached the end of the pile.
    pub fn next_record(&mut self) -> Result<Option<Record>> {
        loop {
            if self.current_reader.is_none() {
                use std::io::Seek;
                use std::io::SeekFrom;

                // No reader, get a fresh one.
                let Some((path, offset)) = self.source_files.get(self.next_source_file) else {
                    return Ok(None);
                };

                self.next_source_file += 1;

                let offset = *offset;
                let mut file = File::open(self.pile_dir.join(path))?;
                // We cap at the current file size so that, if we find a
                // partial record, it'll always be at the end: if we were
                // to race with multiple writes and catch up at the end,
                // we wouldn't revisit the hole in the middle.
                let meta = file.metadata()?;
                file.seek(SeekFrom::Start(offset))?;
                self.current_reader = Some((
                    ShardReader::new(
                        file,
                        self.max_record_size,
                        Some(meta.len().saturating_sub(offset)),
                    ),
                    offset..offset,
                ));
            }

            let (reader, range) = self
                .current_reader
                .as_mut()
                .expect("we just put a reader in");

            assert!(self.next_source_file > 0);
            let max_offset = &mut self.source_files[self.next_source_file - 1].1;

            if let Some((record, record_range)) = reader.next_record()? {
                range.end = range.start + record_range.end;
                *max_offset = range.end;
                return Ok(Some(record));
            }

            // The `current_reader` doesn't know about the bytes we `seek`ed past.
            *max_offset = range.end.max(range.start + reader.last_sentinel_offset());
            self.current_reader = None;
        }
    }

    /// `PileReader` is an iterator, but it can be useful to
    /// explicitly convert it to a mutable reference instead of
    /// a by-value iterator.
    pub fn iter(&mut self) -> &mut PileReader {
        self
    }
}

impl std::iter::Iterator for PileReader {
    type Item = Result<Record>;

    #[inline(always)]
    fn next(&mut self) -> Option<Result<Record>> {
        self.next_record().transpose()
    }
}

impl std::iter::Iterator for PileReaderState {
    type Item = Result<Record>;

    #[inline(always)]
    fn next(&mut self) -> Option<Result<Record>> {
        self.next_record().transpose()
    }
}

impl std::iter::Iterator for StablePileReader {
    type Item = Result<Record>;

    #[inline(always)]
    fn next(&mut self) -> Option<Result<Record>> {
        self.next_record().transpose()
    }
}

/// Read from an open epoch with one log file should contain its contents.
#[cfg(not(miri))]
#[test]
fn test_read_one_file() {
    use crate::shard_writer::ShardWriter;
    use test_dir::{DirBuilder, FileType, TestDir};
    use time::macros::datetime;

    let temp = TestDir::temp().create("test_read_one_file", FileType::Dir);

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let begin = crate::VouchedTime::new(
        datetime!(2024-04-07 16:01:32),
        1712505692000,
        vouch_params.vouch(1712505692000),
    )
    .unwrap();

    let mut writer = ShardWriter::open(
        temp.path("test_read_one_file"),
        "foo",
        &[1u8; 16],
        begin,
        Default::default(),
    )
    .expect("creating shard writer should succeed");
    writer
        .write(b"test contents 1")
        .expect("setup write should succeed");
    writer
        .commit_or_panic_if_unclear(|| begin.get_local_time())
        .expect("setup commit must succeed");

    let read_time = crate::VouchedTime::new(
        datetime!(2024-04-07 16:01:38), // Writes should stop :39
        1712505698000,
        vouch_params.vouch(1712505698000),
    )
    .unwrap();
    let mut reader = PileReader::open(
        temp.path("test_read_one_file"),
        begin.get_local_time(),
        read_time,
        Default::default(),
        None,
    )
    .expect("open should succeed");

    assert!(matches!(&reader, PileReaderState::Peek(_)));

    assert_eq!(
        (&mut reader)
            .collect::<Result<Vec<_>>>()
            .expect("should succeed"),
        vec![Record {
            record_id: [1u8; 16],
            timestamp: datetime!(2024-04-07 16:01:32),
            checksum: [
                156, 171, 198, 229, 179, 177, 248, 92, 33, 67, 230, 112, 115, 81, 97, 230, 218, 48,
                227, 113, 94, 132, 251, 188, 1, 196, 21, 31, 52, 217, 219, 43
            ],
            payload: Box::from(&b"test contents 1"[..])
        }]
    );

    assert!(std::convert::TryInto::<StablePileReader>::try_into(reader).is_err());
}

/// Read from an inexistent epoch.
#[cfg(not(miri))]
#[test]
fn test_read_empty() {
    use test_dir::{DirBuilder, FileType, TestDir};
    use time::macros::datetime;

    let temp = TestDir::temp().create("test_read_one_file", FileType::Dir);

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let begin = crate::VouchedTime::new(
        datetime!(2024-04-07 16:01:32),
        1712505692000,
        vouch_params.vouch(1712505692000),
    )
    .unwrap();

    let read_time = crate::VouchedTime::new(
        datetime!(2024-04-07 16:01:38), // Writes should stop :39
        1712505698000,
        vouch_params.vouch(1712505698000),
    )
    .unwrap();
    let mut reader = PileReader::open(
        temp.path("test_read_one_file"),
        begin.get_local_time(),
        read_time,
        Default::default(),
        None,
    )
    .expect("open should succeed");

    assert!(reader.is_empty());

    assert!(matches!(&reader, PileReaderState::Peek(_)));

    assert_eq!(
        (&mut reader)
            .collect::<Result<Vec<_>>>()
            .expect("should succeed"),
        vec![]
    );

    assert!(std::convert::TryInto::<StablePileReader>::try_into(reader).is_err());
}

// Read from a file; append some more, read the rest.
#[cfg(not(miri))]
#[test]
fn test_read_one_file_append() {
    use crate::shard_writer::ShardWriter;
    use test_dir::{DirBuilder, FileType, TestDir};
    use time::macros::datetime;

    let temp = TestDir::temp().create("test_read_one_file", FileType::Dir);

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let begin = crate::VouchedTime::new(
        datetime!(2024-04-07 16:01:32),
        1712505692000,
        vouch_params.vouch(1712505692000),
    )
    .unwrap();

    let subdir = crate::construct_epoch_subdirectory(
        "./test_read_one_file_append".into(),
        datetime!(2024-04-07 16:01:32),
    )
    .0
    .into_os_string()
    .into_string()
    .unwrap();

    // Write one record

    let mut writer = ShardWriter::open(
        temp.path("test_read_one_file_append"),
        "foo",
        &[1u8; 16],
        begin,
        Default::default(),
    )
    .expect("creating shard writer should succeed");
    writer
        .write(b"test contents 1")
        .expect("setup write should succeed");
    writer
        .commit_or_panic_if_unclear(|| begin.get_local_time())
        .expect("setup commit must succeed");

    let read_time = crate::VouchedTime::new(
        datetime!(2024-04-07 16:01:38), // Writes should stop :39
        1712505698000,
        vouch_params.vouch(1712505698000),
    )
    .unwrap();

    // Read the record
    let reader = PileReader::open(
        temp.path("test_read_one_file_append"),
        begin.get_local_time(),
        read_time,
        Default::default(),
        None,
    )
    .expect("open should succeed");

    let mut reader: PileReader = reader.into();

    assert_eq!(
        reader
            .iter()
            .collect::<Result<Vec<_>>>()
            .expect("should succeed"),
        vec![Record {
            record_id: [1u8; 16],
            timestamp: datetime!(2024-04-07 16:01:32),
            checksum: [
                156, 171, 198, 229, 179, 177, 248, 92, 33, 67, 230, 112, 115, 81, 97, 230, 218, 48,
                227, 113, 94, 132, 251, 188, 1, 196, 21, 31, 52, 217, 219, 43
            ],
            payload: Box::from(&b"test contents 1"[..])
        }]
    );

    // 2 bytes for the sentinel, 1 byte for stuffing, then 64 bytes metadata and 15 bytes payload.
    assert_eq!(reader.start_offsets()[0].1, 2 + 1 + 64 + 15);

    let offsets: HashMap<_, _> = reader.start_offsets().iter().cloned().collect();

    // Append garbage (looks like a bad record and a partial record).
    {
        use std::io::Write;
        let path = temp.path(&format!("{}/foo.log", &subdir));

        let mut file = std::fs::OpenOptions::new()
            .append(true)
            .truncate(false)
            .open(path)
            .unwrap();
        // First HCOBS sequence is complete, but a short record.
        // Second HCOBS sequence is partial.
        file.write_all(b"\xFE\xFD\x00\xFE\xFD\x10garbage")
            .expect("should succeed");
    }

    // Read the record
    let mut reader = PileReader::open(
        temp.path("test_read_one_file_append"),
        begin.get_local_time(),
        read_time,
        Default::default(),
        Some(&offsets),
    )
    .expect("open should succeed");

    assert_eq!(
        reader
            .iter()
            .collect::<Result<Vec<_>>>()
            .expect("should succeed"),
        vec![]
    );
    // And the only impact on the start offset is that we skip to the
    // last stuff sequence sentinel when they're consecutive (i.e, we
    // re-read trailing partial records, in case they become valid).
    assert_eq!(
        reader.start_offsets(),
        offsets
            .iter()
            .map(|kv| (kv.0.clone(), kv.1 + 3 + 2))
            .collect::<Vec<_>>()
    );

    // And another reader, from scratch, to confirm there's nothing special
    // about starting the read on garbage.
    {
        let mut scratch_reader = PileReader::open(
            temp.path("test_read_one_file_append"),
            begin.get_local_time(),
            read_time,
            Default::default(),
            None,
        )
        .expect("open should succeed");

        assert_eq!(
            scratch_reader
                .iter()
                .collect::<Result<Vec<_>>>()
                .expect("should succeed")
                .len(),
            1
        );
        assert_eq!(scratch_reader.start_offsets(), reader.start_offsets());
    }

    // Write a new record
    let begin = crate::VouchedTime::new(
        datetime!(2024-04-07 16:01:33),
        1712505692000,
        vouch_params.vouch(1712505692000),
    )
    .unwrap();
    let mut writer = ShardWriter::open(
        temp.path("test_read_one_file_append"),
        "foo",
        &[2u8; 16],
        begin,
        Default::default(),
    )
    .expect("creating shard writer should succeed");
    writer
        .write(b"test contents 2")
        .expect("setup write should succeed");
    writer
        .commit_or_panic_if_unclear(|| begin.get_local_time())
        .expect("setup commit must succeed");

    // Resume reading
    let mut reader = PileReader::open(
        temp.path("test_read_one_file_append"),
        begin.get_local_time(),
        read_time,
        Default::default(),
        Some(&offsets),
    )
    .expect("open should succeed");

    assert_eq!(
        reader
            .iter()
            .collect::<Result<Vec<_>>>()
            .expect("should succeed"),
        vec![Record {
            record_id: [2u8; 16],
            timestamp: datetime!(2024-04-07 16:01:33),
            checksum: [
                94, 156, 9, 209, 89, 38, 59, 57, 232, 105, 212, 249, 5, 137, 253, 81, 184, 124, 4,
                49, 213, 186, 27, 128, 207, 253, 23, 94, 173, 188, 104, 159
            ],
            payload: Box::from(&b"test contents 2"[..])
        }]
    );

    let offsets: HashMap<_, _> = reader.start_offsets().iter().cloned().collect();

    // Trying to read again should yield nothing.
    let mut reader = PileReader::open(
        temp.path("test_read_one_file_append"),
        begin.get_local_time(),
        read_time,
        Default::default(),
        Some(&offsets),
    )
    .expect("open should succeed");

    assert_eq!(
        reader
            .iter()
            .collect::<Result<Vec<_>>>()
            .expect("should succeed"),
        vec![]
    );

    // But reading from scratch should have everything
    let mut reader = PileReader::open(
        temp.path("test_read_one_file_append"),
        begin.get_local_time(),
        read_time,
        Default::default(),
        None,
    )
    .expect("open should succeed");

    assert_eq!(
        reader
            .iter()
            .collect::<Result<Vec<_>>>()
            .expect("should succeed"),
        vec![
            Record {
                record_id: [1u8; 16],
                timestamp: datetime!(2024-04-07 16:01:32),
                checksum: [
                    156, 171, 198, 229, 179, 177, 248, 92, 33, 67, 230, 112, 115, 81, 97, 230, 218,
                    48, 227, 113, 94, 132, 251, 188, 1, 196, 21, 31, 52, 217, 219, 43
                ],
                payload: Box::from(&b"test contents 1"[..])
            },
            Record {
                record_id: [2u8; 16],
                timestamp: datetime!(2024-04-07 16:01:33),
                checksum: [
                    94, 156, 9, 209, 89, 38, 59, 57, 232, 105, 212, 249, 5, 137, 253, 81, 184, 124,
                    4, 49, 213, 186, 27, 128, 207, 253, 23, 94, 173, 188, 104, 159
                ],
                payload: Box::from(&b"test contents 2"[..])
            }
        ]
    );
}

/// Read from an open epoch with two log files should contain their contents.
///
/// Moreover, non-log files should be ignored.
#[cfg(not(miri))]
#[test]
fn test_read_two_files() {
    use crate::shard_writer::ShardWriter;
    use test_dir::{DirBuilder, FileType, TestDir};
    use time::macros::datetime;

    let temp = TestDir::temp().create("test_read_two_files", FileType::Dir);

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    {
        let begin = crate::VouchedTime::new(
            datetime!(2024-04-07 16:01:32),
            1712505692000,
            vouch_params.vouch(1712505692000),
        )
        .unwrap();

        let mut writer = ShardWriter::open(
            temp.path("test_read_two_files"),
            "foo",
            &[1u8; 16],
            begin,
            Default::default(),
        )
        .expect("creating shard writer should succeed");
        writer
            .write(b"test contents 1")
            .expect("setup write should succeed");
        writer
            .commit_or_panic_if_unclear(|| begin.get_local_time())
            .expect("setup commit must succeed");
    }

    // second write

    let begin = crate::VouchedTime::new(
        datetime!(2024-04-07 16:01:33),
        1712505693000,
        vouch_params.vouch(1712505693000),
    )
    .unwrap();
    let mut writer = ShardWriter::open(
        temp.path("test_read_two_files"),
        "bar",
        &[2u8; 16],
        begin,
        Default::default(),
    )
    .expect("creating shard writer should succeed");
    writer
        .write(b"test contents 2")
        .expect("setup write should succeed");
    writer
        .commit_or_panic_if_unclear(|| begin.get_local_time())
        .expect("setup commit must succeed");

    let read_time = crate::VouchedTime::new(
        datetime!(2024-04-07 16:01:38), // Writes should stop :39
        1712505698000,
        vouch_params.vouch(1712505698000),
    )
    .unwrap();
    let mut reader = PileReader::open(
        temp.path("test_read_two_files"),
        begin.get_local_time(),
        read_time,
        Default::default(),
        None,
    )
    .expect("open should succeed");

    assert_eq!(
        reader
            .iter()
            .collect::<Result<Vec<_>>>()
            .expect("should succeed"),
        vec![
            Record {
                record_id: [2u8; 16],
                timestamp: datetime!(2024-04-07 16:01:33),
                checksum: [
                    94, 156, 9, 209, 89, 38, 59, 57, 232, 105, 212, 249, 5, 137, 253, 81, 184, 124,
                    4, 49, 213, 186, 27, 128, 207, 253, 23, 94, 173, 188, 104, 159
                ],
                payload: Box::from(&b"test contents 2"[..])
            },
            Record {
                record_id: [1u8; 16],
                timestamp: datetime!(2024-04-07 16:01:32),
                checksum: [
                    156, 171, 198, 229, 179, 177, 248, 92, 33, 67, 230, 112, 115, 81, 97, 230, 218,
                    48, 227, 113, 94, 132, 251, 188, 1, 196, 21, 31, 52, 217, 219, 43
                ],
                payload: Box::from(&b"test contents 1"[..])
            }
        ]
    );

    // Now create a dummy non-log file.  The contents shouldn't change.
    {
        let subdir = crate::construct_epoch_subdirectory(
            temp.path("test_read_two_files"),
            begin.get_local_time(),
        )
        .0;

        let mut src = subdir.clone();
        let mut dst = subdir;

        src.push("foo.log");
        dst.push("quux.notalog");
        std::fs::copy(&src, &dst).expect("copy should succeed");
    }

    // Read again. Same contents, without duplicates.
    let mut reader = PileReader::open(
        temp.path("test_read_two_files"),
        begin.get_local_time(),
        read_time,
        Default::default(),
        None,
    )
    .expect("open should succeed");

    assert_eq!(
        reader
            .iter()
            .collect::<Result<Vec<_>>>()
            .expect("should succeed"),
        vec![
            Record {
                record_id: [2u8; 16],
                timestamp: datetime!(2024-04-07 16:01:33),
                checksum: [
                    94, 156, 9, 209, 89, 38, 59, 57, 232, 105, 212, 249, 5, 137, 253, 81, 184, 124,
                    4, 49, 213, 186, 27, 128, 207, 253, 23, 94, 173, 188, 104, 159
                ],
                payload: Box::from(&b"test contents 2"[..])
            },
            Record {
                record_id: [1u8; 16],
                timestamp: datetime!(2024-04-07 16:01:32),
                checksum: [
                    156, 171, 198, 229, 179, 177, 248, 92, 33, 67, 230, 112, 115, 81, 97, 230, 218,
                    48, 227, 113, 94, 132, 251, 188, 1, 196, 21, 31, 52, 217, 219, 43
                ],
                payload: Box::from(&b"test contents 1"[..])
            }
        ]
    );
}

/// Read from a closed epoch with two log files with a summary file
/// should yield the two files' contents (once).
#[cfg(not(miri))]
#[test]
fn test_read_two_files_summary() {
    use crate::shard_writer::ShardWriter;
    use test_dir::{DirBuilder, FileType, TestDir};
    use time::macros::datetime;

    let temp = TestDir::temp().create("test_read_two_files_summary", FileType::Dir);

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    {
        let begin = crate::VouchedTime::new(
            datetime!(2024-04-07 16:01:32),
            1712505692000,
            vouch_params.vouch(1712505692000),
        )
        .unwrap();

        let mut writer = ShardWriter::open(
            temp.path("test_read_two_files_summary"),
            "foo",
            &[1u8; 16],
            begin,
            Default::default(),
        )
        .expect("creating shard writer should succeed");
        writer
            .write(b"test contents 1")
            .expect("setup write should succeed");
        writer
            .commit_or_panic_if_unclear(|| begin.get_local_time())
            .expect("setup commit must succeed");
    }

    // second write
    let begin = crate::VouchedTime::new(
        datetime!(2024-04-07 16:01:33),
        1712505693000,
        vouch_params.vouch(1712505693000),
    )
    .unwrap();
    let mut writer = ShardWriter::open(
        temp.path("test_read_two_files_summary"),
        "bar",
        &[2u8; 16],
        begin,
        Default::default(),
    )
    .expect("creating shard writer should succeed");
    writer
        .write(b"test contents 2")
        .expect("setup write should succeed");
    writer
        .commit_or_panic_if_unclear(|| begin.get_local_time())
        .expect("setup commit must succeed");

    let read_time = crate::VouchedTime::new(
        datetime!(2024-04-07 16:01:40), // Writes should stop :39
        1712505700000,
        vouch_params.vouch(1712505700000),
    )
    .unwrap();

    // Closing should succeed.
    assert_eq!(
        crate::close::close_epoch_subdir(
            crate::construct_epoch_subdirectory(
                temp.path("test_read_two_files_summary"),
                begin.get_local_time()
            )
            .0,
            read_time,
            Default::default()
        )
        .unwrap(),
        None
    );

    let mut reader = PileReader::open(
        temp.path("test_read_two_files_summary"),
        begin.get_local_time(),
        read_time,
        Default::default(),
        None,
    )
    .expect("open should succeed");

    assert!(matches!(&reader, PileReaderState::Stable(_)));

    // Make sure we can convert.
    let _: &PileReader = &reader;
    let _: &mut PileReader = &mut reader;

    let mut results = (&mut reader)
        .collect::<Result<Vec<_>>>()
        .expect("should succeed");
    results.sort();
    assert_eq!(
        results,
        vec![
            Record {
                record_id: [1u8; 16],
                timestamp: datetime!(2024-04-07 16:01:32),
                checksum: [
                    156, 171, 198, 229, 179, 177, 248, 92, 33, 67, 230, 112, 115, 81, 97, 230, 218,
                    48, 227, 113, 94, 132, 251, 188, 1, 196, 21, 31, 52, 217, 219, 43
                ],
                payload: Box::from(&b"test contents 1"[..])
            },
            Record {
                record_id: [2u8; 16],
                timestamp: datetime!(2024-04-07 16:01:33),
                checksum: [
                    94, 156, 9, 209, 89, 38, 59, 57, 232, 105, 212, 249, 5, 137, 253, 81, 184, 124,
                    4, 49, 213, 186, 27, 128, 207, 253, 23, 94, 173, 188, 104, 159
                ],
                payload: Box::from(&b"test contents 2"[..])
            },
        ]
    );

    // Make sure we can convert by value.
    let reader: StablePileReader = reader.try_into().unwrap();
    let _: PileReader = reader.into();

    // Let the Drop traits clean up
    let subdir = crate::construct_epoch_subdirectory(
        "./test_read_two_files_summary".into(),
        datetime!(2024-04-07 16:01:32),
    )
    .0
    .into_os_string()
    .into_string()
    .unwrap();
    let temp_dir = temp.path(&subdir);
    let mut perms = std::fs::metadata(&temp_dir).unwrap().permissions();
    #[allow(clippy::permissions_set_readonly_false)]
    perms.set_readonly(false);
    std::fs::set_permissions(&temp_dir, perms).unwrap();
}

/// Read from a very old open epoch with two log files should yield
/// the two files' contents (once).
#[cfg(not(miri))]
#[test]
fn test_read_two_files_stale() {
    use crate::shard_writer::ShardWriter;
    use test_dir::{DirBuilder, FileType, TestDir};
    use time::macros::datetime;

    let temp = TestDir::temp().create("test_read_two_files_stale", FileType::Dir);

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    {
        let begin = crate::VouchedTime::new(
            datetime!(2024-04-07 16:01:32),
            1712505692000,
            vouch_params.vouch(1712505692000),
        )
        .unwrap();

        let mut writer = ShardWriter::open(
            temp.path("test_read_two_files_stale"),
            "foo",
            &[1u8; 16],
            begin,
            Default::default(),
        )
        .expect("creating shard writer should succeed");
        writer
            .write(b"test contents 1")
            .expect("setup write should succeed");
        writer
            .commit_or_panic_if_unclear(|| begin.get_local_time())
            .expect("setup commit must succeed");
    }

    // second write
    let begin = crate::VouchedTime::new(
        datetime!(2024-04-07 16:01:33),
        1712505693000,
        vouch_params.vouch(1712505693000),
    )
    .unwrap();
    let mut writer = ShardWriter::open(
        temp.path("test_read_two_files_stale"),
        "bar",
        &[2u8; 16],
        begin,
        Default::default(),
    )
    .expect("creating shard writer should succeed");
    writer
        .write(b"test contents 2")
        .expect("setup write should succeed");
    writer
        .commit_or_panic_if_unclear(|| begin.get_local_time())
        .expect("setup commit must succeed");

    let read_time = crate::VouchedTime::new(
        datetime!(2024-04-07 16:01:55), // Writes should stop :39
        1712505715000,
        vouch_params.vouch(1712505715000),
    )
    .unwrap();

    // A read-only open should now fail.
    assert!(PileReader::open(
        temp.path("test_read_two_files_stale"),
        begin.get_local_time(),
        read_time,
        PileReaderOptions {
            mode: PileReaderMode::ReadOnly,
            ..Default::default()
        },
        None,
    )
    .is_err());

    // A regular open should succeed.
    let reader = PileReader::open(
        temp.path("test_read_two_files_stale"),
        begin.get_local_time(),
        read_time,
        Default::default(),
        None,
    )
    .expect("open should succeed");

    assert!(matches!(&reader, PileReaderState::Stable(_)));

    let reader: StablePileReader = reader.try_into().unwrap();
    let mut results = reader.collect::<Result<Vec<_>>>().expect("should succeed");
    results.sort();
    assert_eq!(
        results,
        vec![
            Record {
                record_id: [1u8; 16],
                timestamp: datetime!(2024-04-07 16:01:32),
                checksum: [
                    156, 171, 198, 229, 179, 177, 248, 92, 33, 67, 230, 112, 115, 81, 97, 230, 218,
                    48, 227, 113, 94, 132, 251, 188, 1, 196, 21, 31, 52, 217, 219, 43
                ],
                payload: Box::from(&b"test contents 1"[..])
            },
            Record {
                record_id: [2u8; 16],
                timestamp: datetime!(2024-04-07 16:01:33),
                checksum: [
                    94, 156, 9, 209, 89, 38, 59, 57, 232, 105, 212, 249, 5, 137, 253, 81, 184, 124,
                    4, 49, 213, 186, 27, 128, 207, 253, 23, 94, 173, 188, 104, 159
                ],
                payload: Box::from(&b"test contents 2"[..])
            },
        ]
    );

    // See if we can convert.
    let reader = PileReader::open(
        temp.path("test_read_two_files_stale"),
        begin.get_local_time(),
        read_time,
        Default::default(),
        None,
    )
    .expect("open should succeed");
    let _: PileReader = reader.into();

    let subdir = crate::construct_epoch_subdirectory(
        "./test_read_two_files_stale".into(),
        datetime!(2024-04-07 16:01:32),
    )
    .0
    .into_os_string()
    .into_string()
    .unwrap();

    assert!(
        crate::close::epoch_subdir_is_being_closed(temp.path(&subdir)).expect("should succeed")
    );

    // Let the Drop traits clean up
    let temp_dir = temp.path(&subdir);
    let mut perms = std::fs::metadata(&temp_dir).unwrap().permissions();
    #[allow(clippy::permissions_set_readonly_false)]
    perms.set_readonly(false);
    std::fs::set_permissions(&temp_dir, perms).unwrap();
}
