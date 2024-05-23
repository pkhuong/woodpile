//! The `shard_reader` module defines the low-level logic to
//! decode and validate [`Record`]s from a single log file.
use crate::hcobs::StreamReader;

use std::fs::File;
use std::io::IoSlice;
use std::io::Result;
use std::ops::Range;

/// The hash key used to generate the records' Blake3 checksum.
///
/// See shard_writer.rs
const BLAKE3_KEY: [u8; 32] = *b"Woodpile record checksum hashkey";

/// Reading records from a woodpile bag yields these structs.
///
/// A record is only generated when the checksum recomputed from
/// the contents matches the checksum on disk.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Record {
    pub record_id: [u8; 16],
    pub timestamp: time::PrimitiveDateTime,
    pub checksum: [u8; 32],
    pub payload: Box<[u8]>,
}

/// A [`ShardReader`] attempts to decode [`Record`]s sequentially
/// from a [`std::io::Read`].
#[derive(Debug)]
pub struct ShardReader<R: std::io::Read = File> {
    stream_reader: StreamReader,
    file: R,
    max_record_size: usize,
    max_file_offset: u64,
}

struct SliceReader<'this> {
    slices: &'this [IoSlice<'this>],
    slice_idx: usize,
    byte_idx: usize,
    hasher: blake3::Hasher,
}

impl<'this> SliceReader<'this> {
    pub fn new(slices: &'this [IoSlice<'this>]) -> Self {
        Self {
            slices,
            slice_idx: 0,
            byte_idx: 0,
            hasher: blake3::Hasher::new_keyed(&BLAKE3_KEY),
        }
    }

    pub fn hasher(&self) -> &blake3::Hasher {
        &self.hasher
    }
}

impl std::io::Read for SliceReader<'_> {
    fn read(&mut self, mut dst: &mut [u8]) -> Result<usize> {
        let mut written = 0;
        while !dst.is_empty() {
            let Some(slice) = self.slices.get(self.slice_idx) else {
                break;
            };

            let remaining = &slice[self.byte_idx..];
            let to_write = remaining.len().min(dst.len());
            dst[..to_write].copy_from_slice(&remaining[..to_write]);
            self.hasher.update(&remaining[..to_write]);
            written += to_write;

            self.byte_idx += to_write;
            dst = &mut dst[to_write..];

            if self.byte_idx >= slice.len() {
                self.slice_idx += 1;
                self.byte_idx = 0;
            }
        }

        Ok(written)
    }
}

impl<R: std::io::Read> ShardReader<R> {
    /// Creates a new [`ShardReader`] that reads from `file`, stops decoding records when their
    /// size exceeds `max_record_size`, and stops reading records when they would start at or
    /// after `max_file_offset` bytes (defaults to [`u64::MAX`]) read from `file`.
    pub fn new(file: R, max_record_size: usize, max_file_offset: Option<u64>) -> ShardReader<R> {
        ShardReader {
            stream_reader: StreamReader::new(),
            file,
            max_record_size,
            max_file_offset: max_file_offset.unwrap_or(u64::MAX),
        }
    }

    /// Attempts to decode the next record in the underlying reader.
    ///
    /// Returns a [`std::io::Error`] only when the underlying [`std::io::Read`] does.
    ///
    /// Otherwise, keeps pumping until we find a valid record (correct format, size
    /// does not exceed `max_record_size`, and the Blake3 checksum matches), or returns
    /// `Ok(None)` if we reached the end of the file or any new record would start at
    /// or after `max_file_offset`.
    pub fn next_record(&mut self) -> Result<Option<(Record, Range<u64>)>> {
        use std::io::Read;
        let judge = StreamReader::chunk_judge(self.max_record_size, Some(self.max_file_offset));
        loop {
            let Some((slices, range)) =
                self.stream_reader
                    .next_record_bytes(&mut self.file, &judge, None)?
            else {
                return Ok(None);
            };

            let total_size = slices.iter().map(|x| x.len()).sum::<usize>();
            // We need at least 32 bytes for the header, and 32 for the checksum.
            if total_size < 64 {
                continue;
            }

            let mut reader = SliceReader::new(slices);

            let mut record_id = [0u8; 16];
            let mut timestamp_le = [0u8; 16];
            // We already checked.
            reader
                .read_exact(&mut record_id)
                .expect("must have room for header");
            reader
                .read_exact(&mut timestamp_le)
                .expect("must have room for header");

            let Ok(timestamp) =
                time::OffsetDateTime::from_unix_timestamp_nanos(i128::from_le_bytes(timestamp_le))
            else {
                continue;
            };

            let mut dst = vec![0; total_size - 64];
            reader
                .read_exact(&mut dst)
                .expect("must have room for data");

            let checksum = reader.hasher().finalize();
            let mut footer = [0u8; 32];
            reader
                .read_exact(&mut footer)
                .expect("must have room for footer");

            // We should be at EOF.
            {
                let mut dst = [0u8; 1];
                assert_eq!(reader.read(&mut dst).expect("should succeed"), 0);
            }

            if checksum == blake3::Hash::from_bytes(footer) {
                let ret = Record {
                    record_id,
                    timestamp: time::PrimitiveDateTime::new(timestamp.date(), timestamp.time()),
                    checksum: *checksum.as_bytes(),
                    payload: dst.into_boxed_slice(),
                };

                return Ok(Some((ret, range)));
            }
        }
    }

    /// [`ShardReader`] is an [`std::iter::Iterator`].
    pub fn iter(self) -> Self {
        self
    }
}

impl<R: std::io::Read> std::iter::Iterator for ShardReader<R> {
    type Item = Result<(Record, Range<u64>)>;

    fn next(&mut self) -> Option<Result<(Record, Range<u64>)>> {
        self.next_record().transpose()
    }
}

// Simple happy path: write two records, read two records.
#[test]
fn test_shard_reader() {
    use time::macros::datetime;

    // See shard_writer.rs's `test_shard_writer_append`
    let expected: &[&[u8]] = &[
        &crate::hcobs::STUFF_SEQUENCE,
        &[68u8], // 32 + 4 + 32
        &[0u8; 16],
        &datetime!(2024-04-21 00:58:46.1)
            .assume_utc()
            .unix_timestamp_nanos()
            .to_le_bytes(),
        b"1234",
        &[
            100, 125, 17, 5, 134, 197, 11, 182, 56, 55, 179, 46, 136, 201, 34, 40, 143, 186, 10,
            14, 178, 53, 104, 75, 0, 61, 166, 1, 8, 1, 212, 35,
        ],
        &crate::hcobs::STUFF_SEQUENCE,
        &crate::hcobs::STUFF_SEQUENCE,
        &[68u8],
        &[1u8; 16],
        &datetime!(2024-04-21 00:58:46.5)
            .assume_utc()
            .unix_timestamp_nanos()
            .to_le_bytes(),
        b"abcd",
        &[
            201, 51, 72, 200, 211, 235, 24, 12, 15, 157, 35, 77, 38, 138, 38, 12, 249, 224, 10,
            116, 254, 193, 18, 166, 237, 158, 230, 191, 137, 20, 82, 130,
        ],
        &crate::hcobs::STUFF_SEQUENCE,
    ];

    let contents = &expected.concat()[..];

    let reader = ShardReader::new(contents, 1000, None);
    assert_eq!(
        reader
            .iter()
            .collect::<Result<Vec<_>>>()
            .expect("must succeed"),
        [
            (
                Record {
                    record_id: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                    timestamp: datetime!(2024-04-21 0:58:46.1),
                    checksum: [
                        100, 125, 17, 5, 134, 197, 11, 182, 56, 55, 179, 46, 136, 201, 34, 40, 143,
                        186, 10, 14, 178, 53, 104, 75, 0, 61, 166, 1, 8, 1, 212, 35
                    ],
                    payload: vec![49, 50, 51, 52].into_boxed_slice()
                },
                2..71
            ),
            (
                Record {
                    record_id: [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
                    timestamp: datetime!(2024-04-21 0:58:46.5),
                    checksum: [
                        201, 51, 72, 200, 211, 235, 24, 12, 15, 157, 35, 77, 38, 138, 38, 12, 249,
                        224, 10, 116, 254, 193, 18, 166, 237, 158, 230, 191, 137, 20, 82, 130
                    ],
                    payload: vec![97, 98, 99, 100].into_boxed_slice()
                },
                75..144
            )
        ]
    );
}

// Same contents, but the max record size is smaller. should drop everything.
#[test]
fn test_shard_reader_large() {
    use time::macros::datetime;

    // See shard_writer.rs's `test_shard_writer_append`
    let expected: &[&[u8]] = &[
        &crate::hcobs::STUFF_SEQUENCE,
        &[68u8], // 32 + 4 + 32
        &[0u8; 16],
        &datetime!(2024-04-21 00:58:46.1)
            .assume_utc()
            .unix_timestamp_nanos()
            .to_le_bytes(),
        b"1234",
        &[
            100, 125, 17, 5, 134, 197, 11, 182, 56, 55, 179, 46, 136, 201, 34, 40, 143, 186, 10,
            14, 178, 53, 104, 75, 0, 61, 166, 1, 8, 1, 212, 35,
        ],
        &crate::hcobs::STUFF_SEQUENCE,
        &crate::hcobs::STUFF_SEQUENCE,
        &[68u8],
        &[1u8; 16],
        &datetime!(2024-04-21 00:58:46.5)
            .assume_utc()
            .unix_timestamp_nanos()
            .to_le_bytes(),
        b"abcd",
        &[
            201, 51, 72, 200, 211, 235, 24, 12, 15, 157, 35, 77, 38, 138, 38, 12, 249, 224, 10,
            116, 254, 193, 18, 166, 237, 158, 230, 191, 137, 20, 82, 130,
        ],
        &crate::hcobs::STUFF_SEQUENCE,
    ];

    let contents = &expected.concat()[..];

    let reader = ShardReader::new(contents, 64, None);
    assert_eq!(
        reader
            .iter()
            .collect::<Result<Vec<_>>>()
            .expect("must succeed"),
        []
    );
}

// Flip each bit.  We should always drop a message, and never
// accept extra messages.
#[cfg(not(miri))] // Too slow with miri; run it manually if needed.
#[test]
fn test_shard_reader_corrupt_slow() {
    use time::macros::datetime;

    // See shard_writer.rs's `test_shard_writer_append`
    let expected: &[&[u8]] = &[
        &crate::hcobs::STUFF_SEQUENCE,
        &[68u8], // 32 + 4 + 32
        &[0u8; 16],
        &datetime!(2024-04-21 00:58:46.1)
            .assume_utc()
            .unix_timestamp_nanos()
            .to_le_bytes(),
        b"1234",
        &[
            100, 125, 17, 5, 134, 197, 11, 182, 56, 55, 179, 46, 136, 201, 34, 40, 143, 186, 10,
            14, 178, 53, 104, 75, 0, 61, 166, 1, 8, 1, 212, 35,
        ],
        &crate::hcobs::STUFF_SEQUENCE,
        &crate::hcobs::STUFF_SEQUENCE,
        &[68u8],
        &[1u8; 16],
        &datetime!(2024-04-21 00:58:46.5)
            .assume_utc()
            .unix_timestamp_nanos()
            .to_le_bytes(),
        b"abcd",
        &[
            201, 51, 72, 200, 211, 235, 24, 12, 15, 157, 35, 77, 38, 138, 38, 12, 249, 224, 10,
            116, 254, 193, 18, 166, 237, 158, 230, 191, 137, 20, 82, 130,
        ],
        &crate::hcobs::STUFF_SEQUENCE,
    ];

    let contents: &mut [u8] = &mut expected.concat()[..];

    let vanilla = ShardReader::new(&*contents, 1000, None)
        .iter()
        .collect::<Result<Vec<_>>>()
        .expect("must succeed");

    for idx in 0..contents.len() {
        for bit in 0..8 {
            contents[idx] ^= 1u8 << bit;

            let corrupt = ShardReader::new(&*contents, 1000, None)
                .iter()
                .collect::<Result<Vec<_>>>()
                .expect("must succeed");

            // Flipping one bit should only affect one record.
            assert_ne!(corrupt, []);
            assert_ne!(corrupt, vanilla);
            for record in corrupt {
                assert!(vanilla.contains(&record));
            }

            contents[idx] ^= 1u8 << bit;
        }
    }
}

// Valid stuffed bytes, but invalid record. Should be dropped.
#[test]
fn test_shard_reader_short_record() {
    let expected: &[&[u8]] = &[
        &crate::hcobs::STUFF_SEQUENCE,
        &[16u8],
        &[0u8; 16],
        &crate::hcobs::STUFF_SEQUENCE,
        &crate::hcobs::STUFF_SEQUENCE,
    ];

    let contents = &expected.concat()[..];

    // Nothing should go through.
    assert_eq!(
        ShardReader::new(contents, 1000, None)
            .iter()
            .collect::<Result<Vec<_>>>()
            .expect("must succeed"),
        []
    );
}

// Error should be bubbled up.
#[test]
fn test_shard_reader_error() {
    struct Reader {
        payload: &'static [u8],
    }

    impl std::io::Read for Reader {
        fn read(&mut self, dst: &mut [u8]) -> Result<usize> {
            if self.payload.is_empty() {
                Err(std::io::Error::other("bad"))
            } else {
                let to_read = self.payload.len().min(dst.len());
                dst[..to_read].copy_from_slice(&self.payload[..to_read]);
                self.payload = &self.payload[to_read..];
                Ok(to_read)
            }
        }
    }

    let reader = Reader {
        payload: &crate::hcobs::STUFF_SEQUENCE,
    };

    // Nothing should go through.
    assert!(ShardReader::new(reader, 1000, None).next_record().is_err());
}
