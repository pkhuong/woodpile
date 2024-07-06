//! The `shard_writer` module defines the low-level logic to write and
//! commit a single record to a shard in a pile directory (time
//! bucket).
use std::ffi::OsStr;
use std::io::Result;
use std::io::Write;
use std::path::PathBuf;

use hcobs::Encoder;
use hcobs::STUFF_SEQUENCE;
use owning_iovec::OwningIovec;
use time::PrimitiveDateTime;

use crate::epoch_writer::EpochWriter;
use vouched_time::VouchedTime;

/// Option struct for [`ShardWriter::open`].
pub type ShardWriterOptions = crate::epoch_writer::EpochWriterOptions;

/// The hash key used to generate the records' Blake3 checksum.
///
/// While this value is part of the interface, it is not exposed
/// because accidentally using it for a different purpose could
/// cause strange failures.
const BLAKE3_KEY: [u8; 32] = *b"Woodpile record checksum hashkey";

/// Only do something when flushing out once we have this many
/// buffered bytes to write.
const MIN_WRITE_SIZE: usize = 1024 * 1024;

/// A [`ShardWriter`] implements the logic to attempt to publish a single record
/// to a given shard in a log directory.
///
/// Each record consists of, in order:
///  1. an opaque 16-byte logical id
///  2. the logical time at which the record must be visible, in
///     nanoseconds since epoch (written as 16 little-endian bytes)
///  3. an arbitrary payload
///  4. A 32-byte Blake3 checksum
///
/// The records are written out in a (hybrid) consistent overhead
/// byte-stuffed encoding, with the 2-byte [`STUFF_SEQUENCE`] `[0xFE,
/// 0xFD]` before and after the stuffed record.
///
/// This serialisation format is self-synchronising and self-validating;
/// the Blake3 checksum can also serve as a physical deduplication key,
/// while the deduplication id may either be fully random, or double as
/// a logical deduplication key.
pub struct ShardWriter {
    encoder: Encoder<'static>,
    writer: EpochWriter,
    hasher: blake3::Hasher,
}

impl ShardWriter {
    /// Attempts to open the shard `filename` under `directory`, as of `now`,
    /// in order to write a single record with `logical_id` and commit time
    /// `now`.
    ///
    /// The `path_cache`, if populated, must come from an earlier call to
    /// `ShardWriter::open`.
    ///
    /// When this function errors out, we have yet to write anything
    /// to disk, so failure is nilpotent.  Failure may happen because
    /// of I/O errors, or because `now` is too far in the past.
    pub fn open(
        directory: PathBuf,
        filename: impl AsRef<OsStr>,
        logical_id: &[u8; 16],
        now: VouchedTime,
        options: ShardWriterOptions,
        path_cache: &mut Option<Box<(PathBuf, PrimitiveDateTime)>>,
    ) -> Result<ShardWriter> {
        fn doit(
            directory: PathBuf,
            filename: &OsStr,
            logical_id: &[u8; 16],
            now: VouchedTime,
            options: ShardWriterOptions,
            path_cache: &mut Option<Box<(PathBuf, PrimitiveDateTime)>>,
        ) -> Result<ShardWriter> {
            let writer = EpochWriter::open(directory, filename, now, options, path_cache)?;
            let mut iovec = OwningIovec::new();
            iovec.push_copy(&STUFF_SEQUENCE);

            let mut ret = ShardWriter {
                encoder: Encoder::new_from_iovec(iovec),
                writer,
                hasher: blake3::Hasher::new_keyed(&BLAKE3_KEY),
            };

            ret.write_impl(logical_id);
            let ts: [u8; 16] = now
                .get_local_time()
                .assume_utc()
                .unix_timestamp_nanos()
                .to_le_bytes();
            ret.write_impl(&ts);
            Ok(ret)
        }

        doit(
            directory,
            filename.as_ref(),
            logical_id,
            now,
            options,
            path_cache,
        )
    }

    /// Checks whether `now` is still before the shard file's deadline.
    ///
    /// Returns Ok(()) if so, and an error if `now` is too late.
    ///
    /// This method is useful to abort early when processing is
    /// already too slow, but is never necessary for correctness.
    ///
    /// When a [`ShardWriter`] errors out here, the record on disk
    /// is never valid, and the write may be safely retried.
    pub fn check_deadline(&self, now: time::PrimitiveDateTime) -> Result<()> {
        self.writer.check_deadline(now)
    }

    /// Attempts to append `buf` to the record; flushes to the destination
    /// (without `fsync`) file automatically when the buffer grows large.
    ///
    /// This function can only error out on I/O; on error, the record
    /// on disk is never valid, and the write may be safely retried.
    pub fn write(&mut self, buf: &[u8]) -> Result<usize> {
        self.write_impl(buf);
        // If we're definitely past the min write size, try to flush.
        if self.encoder.consumer().total_size() >= 2 * MIN_WRITE_SIZE {
            self.flush_impl(MIN_WRITE_SIZE)?;
        }

        Ok(buf.len())
    }

    /// Attempts to flush any encoded buffered data.
    ///
    /// This function can only error out on I/O; on error, the record
    /// on disk is never valid, and the write may be safely retried.
    pub fn flush(&mut self) -> Result<()> {
        self.flush_impl(1)
    }

    fn write_impl(&mut self, buf: &[u8]) {
        self.hasher.update(buf);
        self.encoder.encode_copy(buf);
    }

    /// Flushes encoded data to the shard file if we have at least
    /// `min_write` bytes to flush.
    fn flush_impl(&mut self, min_write: usize) -> Result<()> {
        let consumer = self.encoder.consumer();
        let to_write = consumer.stable_prefix();

        // XXX: round down to a multiple of `MIN_WRITE_SIZE`?
        let byte_count: usize = to_write.iter().map(|x| x.len()).sum();
        if byte_count < min_write {
            return Ok(());
        }

        let written = loop {
            match self.writer.file().write_vectored(to_write) {
                Ok(written) => break written,
                Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
                Err(e) => return Err(e),
            }
        };
        self.encoder.consumer().advance_slices(written);
        if written == 0 && byte_count > 0 {
            Err(std::io::Error::new(
                std::io::ErrorKind::WriteZero,
                "shard destination is full",
            ))
        } else {
            Ok(())
        }
    }

    /// Attempts to write out and commit all the data written so far
    /// as a complete record; the `now_provider` must return the current
    /// time; any large error here should not affect system correctness,
    /// but may result in the caller incorrectly assuming the commit failed
    /// or succeeeded.
    ///
    /// Returns two level of [`Result`]. The outer level represents nilpotent
    /// I/O errors; any error there guarantees the record did not commit.
    /// The inner level represent potentially non-idempotent failure; any
    /// error there means the record may or may not have committed successfully.
    ///
    /// `Ok(Ok(()))` guarantees success. `Err(_)` guarantees failure. `Ok(Err(_))`
    /// could go either way.
    pub fn commit_with_false_alarm(
        self,
        mut now_provider: impl FnMut() -> time::PrimitiveDateTime,
    ) -> Result<Result<()>> {
        let hash: [u8; 32] = *self.hasher.finalize().as_bytes();
        let mut encoder = self.encoder;
        // force a copy to merge with the stuff sequence terminator.
        encoder.encode_copy(&hash);

        let mut iovec = encoder.finish(); // XXX: rename to finalize?
        iovec.push_copy(&STUFF_SEQUENCE);

        let mut writer = self.writer;

        assert_eq!(
            iovec.total_size(),
            iovec
                .iovs()
                .expect("no backpatch left")
                .iter()
                .map(|x| x.len())
                .sum()
        );

        // If we have at least this many bytes left, failure is OK.
        let final_byte_count = std::cmp::min(
            // We could have an unexpected success if we're only missing
            // the STUFF_SEQUENCE terminator.
            //
            // We definitely don't expect success if the hash is
            // missing... and we add another 2 bytes just in case
            // the hash comes right at the end of a chunk.
            hash.len() + 2 * STUFF_SEQUENCE.len(),
            // Of course, if we don't even have that many bytes to
            // write, that's also a useful upper bound: we know we
            // have yet to write out the hash.
            iovec.total_size(),
        );

        // Try to update our base time if necessary.
        vouched_time::nfs_voucher::maybe_observe_file_time(writer.file());

        // Attempt to write out the whole iovec.
        let result = (|| {
            while iovec.total_size() > 0 {
                let to_write = iovec.iovs().expect("no backpatch left");
                assert!(!to_write.iter().any(|x| x.is_empty()));
                assert!(!to_write.is_empty());

                if iovec.total_size() >= final_byte_count {
                    writer.check_deadline(now_provider())?;
                }

                let written = writer.write_vectored(to_write)?;

                assert!(written <= iovec.total_size());
                if written == 0 {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::WriteZero,
                        "shard destination is full",
                    ));
                }

                iovec.consumer().advance_slices(written);
            }

            Ok(())
        })();

        // Classify the error: if the failure happened early enough
        // (with at least final_byte_count left to write), this is
        // a retryable error.  Otherwise, we could have an unexpected
        // success.
        match result {
            Err(e) => {
                if iovec.total_size() >= final_byte_count {
                    // Enough bytes left to write that the record is definitely invalid.
                    Err(e)
                } else {
                    // We don't know
                    Ok(Err(e))
                }
            }
            Ok(()) => {
                // If we succeeded, there must be nothing left to write.
                assert_eq!(iovec.total_size(), 0);
                // Any failure at this stage could still result in a
                // valid record; the outer result must be `Ok`.
                Ok(match writer.close() {
                    Ok(commit) => commit.confirm(now_provider()),
                    Err(e) => Err(e),
                })
            }
        }
    }

    /// Attempts to write out and commit all the data written so far
    /// as a complete record; the `now_provider` must return the current
    /// time; any large error here should not affect system correctness,
    /// but may result in the caller incorrectly assuming the commit failed
    /// or succeeeded.
    ///
    /// Returns with an error if the record was definitely not committed.
    /// Returns `Ok(())` if the record was definitely committed.  Panics
    /// if the failure could have gone either way.
    pub fn commit_or_panic_if_unclear(
        self,
        now_provider: impl FnMut() -> time::PrimitiveDateTime,
    ) -> Result<()> {
        self.commit_with_false_alarm(now_provider)?
            .expect("ShardWriter::commit_or_panic_if_unclear may or may not have failed");

        Ok(())
    }
}

impl std::io::Write for ShardWriter {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        ShardWriter::write(self, buf)
    }

    fn flush(&mut self) -> Result<()> {
        ShardWriter::flush(self)
    }
}

// See what happens when we just write a small record.
#[cfg(not(miri))]
#[test]
fn test_shard_writer_simple() {
    use std::io::Write;
    use std::path::Path;
    use test_dir::{DirBuilder, TestDir};
    use time::macros::datetime;

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let now = VouchedTime::new(
        datetime!(2024-04-21 00:58:46.1),
        1713661126000,
        vouch_params.vouch(1713661126000),
    )
    .unwrap();

    let temp = TestDir::temp();
    let subdir = format!("./simple/2024-04-21/00/58:45-{:x}", 1713661132);
    let deadline = time::OffsetDateTime::from_unix_timestamp(1713661132).unwrap();
    let deadline = time::PrimitiveDateTime::new(deadline.date(), deadline.time());

    assert_eq!(
        crate::construct_epoch_subdirectory(
            Path::new("./simple").to_owned(),
            datetime!(2024-04-21 00:58:46.1)
        ),
        (Path::new(&subdir).to_owned(), deadline)
    );

    let mut path_cache = None;

    let mut writer = ShardWriter::open(
        temp.path("./simple"),
        "records",
        &[0u8; 16],
        now,
        ShardWriterOptions { fsync: false },
        &mut path_cache,
    )
    .expect("open should succeed");

    writer
        .check_deadline(now.get_local_time())
        .expect("must not be too late");

    assert_eq!(Write::write(&mut writer, b"1234").unwrap(), 4);
    Write::flush(&mut writer).expect("must succeed");
    writer
        .commit_or_panic_if_unclear(|| now.get_local_time())
        .expect("must succeed");

    let mut file_path = temp.path(&subdir);
    file_path.push("records.log");
    let contents = std::fs::read(&file_path).expect("read must succeed");

    assert_eq!(contents[..2], hcobs::STUFF_SEQUENCE);
    assert_eq!(contents[contents.len() - 2..], hcobs::STUFF_SEQUENCE);

    let mut decoder = hcobs::Decoder::new();
    decoder
        .decode(&contents[2..contents.len() - 2])
        .expect("decoding should succeed");
    let contents = decoder
        .finish()
        .unwrap()
        .flatten()
        .expect("no backref left");

    // First we have the id.
    assert_eq!(&contents[0..16], [0u8; 16]);
    // Then the timestamp
    assert_eq!(
        &contents[16..32],
        now.get_local_time()
            .assume_utc()
            .unix_timestamp_nanos()
            .to_le_bytes()
    );
    // the actual payload...
    assert_eq!(&contents[32..36], b"1234");

    let mut hasher = blake3::Hasher::new_keyed(&BLAKE3_KEY);
    hasher.update(&contents[..36]);
    let hash = *hasher.finalize().as_bytes();
    assert_eq!(&contents[36..], hash);
}

// Write two short records.
#[cfg(not(miri))]
#[test]
fn test_shard_writer_append() {
    use std::io::Write;
    use std::path::Path;
    use test_dir::{DirBuilder, TestDir};
    use time::macros::datetime;

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let now = VouchedTime::new(
        datetime!(2024-04-21 00:58:46.1),
        1713661126000,
        vouch_params.vouch(1713661126000),
    )
    .unwrap();

    let temp = TestDir::temp();
    let subdir = format!("./shard_writer_append/2024-04-21/00/58:45-{:x}", 1713661132);
    let deadline = time::OffsetDateTime::from_unix_timestamp(1713661132).unwrap();
    let deadline = time::PrimitiveDateTime::new(deadline.date(), deadline.time());

    assert_eq!(
        crate::construct_epoch_subdirectory(
            Path::new("./shard_writer_append").to_owned(),
            datetime!(2024-04-21 00:58:46.1)
        ),
        (Path::new(&subdir).to_owned(), deadline)
    );

    let mut path_cache = None;

    let mut writer = ShardWriter::open(
        temp.path("./shard_writer_append"),
        "records",
        &[0u8; 16],
        now,
        ShardWriterOptions { fsync: false },
        &mut path_cache,
    )
    .expect("open should succeed");

    assert_eq!(Write::write(&mut writer, b"1234").unwrap(), 4);
    writer
        .commit_or_panic_if_unclear(|| now.get_local_time())
        .expect("must succeed");

    let then = VouchedTime::new(
        datetime!(2024-04-21 00:58:46.5),
        1713661126000,
        vouch_params.vouch(1713661126000),
    )
    .unwrap();

    let mut writer = ShardWriter::open(
        temp.path("./shard_writer_append"),
        "records",
        &[1u8; 16],
        then,
        ShardWriterOptions { fsync: false },
        &mut path_cache,
    )
    .expect("open should succeed");

    assert_eq!(Write::write(&mut writer, b"abcd").unwrap(), 4);
    writer
        .commit_or_panic_if_unclear(|| then.get_local_time())
        .expect("must succeed");

    let mut file_path = temp.path(&subdir);
    file_path.push("records.log");
    let contents = std::fs::read(&file_path).expect("read must succeed");

    let expected: &[&[u8]] = &[
        &hcobs::STUFF_SEQUENCE,
        &[68u8], // 32 + 4 + 32
        &[0u8; 16],
        &now.get_local_time()
            .assume_utc()
            .unix_timestamp_nanos()
            .to_le_bytes(),
        b"1234",
        &[
            100, 125, 17, 5, 134, 197, 11, 182, 56, 55, 179, 46, 136, 201, 34, 40, 143, 186, 10,
            14, 178, 53, 104, 75, 0, 61, 166, 1, 8, 1, 212, 35,
        ],
        &hcobs::STUFF_SEQUENCE,
        &hcobs::STUFF_SEQUENCE,
        &[68u8],
        &[1u8; 16],
        &then
            .get_local_time()
            .assume_utc()
            .unix_timestamp_nanos()
            .to_le_bytes(),
        b"abcd",
        &[
            201, 51, 72, 200, 211, 235, 24, 12, 15, 157, 35, 77, 38, 138, 38, 12, 249, 224, 10,
            116, 254, 193, 18, 166, 237, 158, 230, 191, 137, 20, 82, 130,
        ],
        &hcobs::STUFF_SEQUENCE,
    ];
    assert_eq!(contents, expected.concat());
}

// Exercise the large write code paths
#[cfg(not(miri))]
#[test]
fn test_shard_writer_large() {
    use std::io::Write;
    use std::path::Path;
    use test_dir::{DirBuilder, TestDir};
    use time::macros::datetime;

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let now = VouchedTime::new(
        datetime!(2024-04-21 00:58:46.1),
        1713661126000,
        vouch_params.vouch(1713661126000),
    )
    .unwrap();

    let temp = TestDir::temp();
    let subdir = format!("./shard_writer_large/2024-04-21/00/58:45-{:x}", 1713661132);
    let deadline = time::OffsetDateTime::from_unix_timestamp(1713661132).unwrap();
    let deadline = time::PrimitiveDateTime::new(deadline.date(), deadline.time());

    assert_eq!(
        crate::construct_epoch_subdirectory(
            Path::new("./shard_writer_large").to_owned(),
            datetime!(2024-04-21 00:58:46.1)
        ),
        (Path::new(&subdir).to_owned(), deadline)
    );

    let mut writer = ShardWriter::open(
        temp.path("./shard_writer_large"),
        "records",
        &[0u8; 16],
        now,
        ShardWriterOptions { fsync: false },
        &mut None,
    )
    .expect("open should succeed");

    writer
        .check_deadline(now.get_local_time())
        .expect("must not be too late");

    for _ in 0..4096 {
        assert_eq!(Write::write(&mut writer, &[1u8; 1024]).unwrap(), 1024);
    }

    writer
        .commit_or_panic_if_unclear(|| now.get_local_time())
        .expect("must succeed");

    let mut file_path = temp.path(&subdir);
    file_path.push("records.log");
    let contents = std::fs::read(&file_path).expect("read must succeed");

    assert_eq!(contents[..2], hcobs::STUFF_SEQUENCE);
    assert_eq!(contents[contents.len() - 2..], hcobs::STUFF_SEQUENCE);

    let mut decoder = hcobs::Decoder::new();
    decoder
        .decode(&contents[2..contents.len() - 2])
        .expect("decoding should succeed");
    let contents = decoder
        .finish()
        .unwrap()
        .flatten()
        .expect("no backref left");
    assert_eq!(contents.len(), 32 + 4096 * 1024 + 32);

    // First we have the id.
    assert_eq!(&contents[0..16], [0u8; 16]);
    // Then the timestamp
    assert_eq!(
        &contents[16..32],
        now.get_local_time()
            .assume_utc()
            .unix_timestamp_nanos()
            .to_le_bytes()
    );

    // The payload should all be 1s.
    for byte in &contents[32..32 + 4096 * 1024] {
        assert_eq!(*byte, 1);
    }

    // And the hash should match.
    let mut hasher = blake3::Hasher::new_keyed(&BLAKE3_KEY);
    hasher.update(&contents[..32 + 4096 * 1024]);
    let hash = *hasher.finalize().as_bytes();
    assert_eq!(&contents[32 + 4096 * 1024..], hash);
}

// Detect early that we were too slow.
#[cfg(not(miri))]
#[test]
fn test_shard_writer_early_late() {
    use std::io::Write;
    use std::path::Path;
    use test_dir::{DirBuilder, TestDir};
    use time::macros::datetime;

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let now = VouchedTime::new(
        datetime!(2024-04-21 00:58:46.1),
        1713661126000,
        vouch_params.vouch(1713661126000),
    )
    .unwrap();

    let temp = TestDir::temp();
    let subdir = format!(
        "./shard_writer_early_late/2024-04-21/00/58:45-{:x}",
        1713661132
    );
    let deadline = time::OffsetDateTime::from_unix_timestamp(1713661132).unwrap();
    let deadline = time::PrimitiveDateTime::new(deadline.date(), deadline.time());

    assert_eq!(
        crate::construct_epoch_subdirectory(
            Path::new("./shard_writer_early_late").to_owned(),
            datetime!(2024-04-21 00:58:46.1)
        ),
        (Path::new(&subdir).to_owned(), deadline)
    );

    let mut writer = ShardWriter::open(
        temp.path("./shard_writer_early_late"),
        "records",
        &[0u8; 16],
        now,
        ShardWriterOptions { fsync: false },
        &mut None,
    )
    .expect("open should succeed");

    writer
        .check_deadline(now.get_local_time())
        .expect("must not be too late");

    assert_eq!(Write::write(&mut writer, b"1234").unwrap(), 4);
    Write::flush(&mut writer).expect("must succeed");
    assert!(writer.commit_or_panic_if_unclear(|| deadline).is_err());
}

// Realise too late that we were slow
#[cfg(not(miri))]
#[test]
fn test_shard_writer_late_late() {
    use std::io::Write;
    use std::path::Path;
    use test_dir::{DirBuilder, TestDir};
    use time::macros::datetime;

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let now = VouchedTime::new(
        datetime!(2024-04-21 00:58:46.1),
        1713661126000,
        vouch_params.vouch(1713661126000),
    )
    .unwrap();

    let temp = TestDir::temp();
    let subdir = format!(
        "./shard_writer_late_late/2024-04-21/00/58:45-{:x}",
        1713661132
    );
    let deadline = time::OffsetDateTime::from_unix_timestamp(1713661132).unwrap();
    let deadline = time::PrimitiveDateTime::new(deadline.date(), deadline.time());

    assert_eq!(
        crate::construct_epoch_subdirectory(
            Path::new("./shard_writer_late_late").to_owned(),
            datetime!(2024-04-21 00:58:46.1)
        ),
        (Path::new(&subdir).to_owned(), deadline)
    );

    let mut writer = ShardWriter::open(
        temp.path("./shard_writer_late_late"),
        "records",
        &[0u8; 16],
        now,
        ShardWriterOptions { fsync: false },
        &mut None,
    )
    .expect("open should succeed");

    writer
        .check_deadline(now.get_local_time())
        .expect("must not be too late");

    assert_eq!(Write::write(&mut writer, b"1234").unwrap(), 4);
    Write::flush(&mut writer).expect("must succeed");

    let past_deadline = VouchedTime::new(
        datetime!(2024-04-21 00:58:55),
        1713661133000,
        vouch_params.vouch(1713661133000),
    )
    .unwrap();

    crate::close::close_epoch_subdir(
        temp.path(&subdir),
        past_deadline,
        crate::close::CloseEpochOptions { fsync: false },
    )
    .expect("must succeed");
    let mut i = 0usize;
    let now_provider = || {
        if i < 1 {
            i += 1;
            now.get_local_time()
        } else {
            past_deadline.get_local_time()
        }
    };
    assert!(writer
        .commit_with_false_alarm(now_provider)
        .expect("succeed early")
        .is_err());
}
