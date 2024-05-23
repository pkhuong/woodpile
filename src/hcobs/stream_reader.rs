use std::io::IoSlice;
use std::io::Result;
use std::num::NonZeroUsize;
use std::ops::Range;

use super::Decoder;
use super::STUFF_SEQUENCE;
use crate::AnchoredSlice;
use crate::ByteArena;
use crate::ConsumingIovec;
use crate::OwningIovec;

const DEFAULT_BLOCK_SIZE: usize = 512 * 1024;

#[cfg(test)]
const TEST_BLOCK_SIZE: Option<usize> = Some(3);

/// A [`StreamReader`] buffers reads from [`std::io::Read`]s and
/// yields the decoded contents of valid COBS-encoded records,
/// assuming [`STUFF_SEQUENCE`] separators.
#[derive(Clone, Debug, Default)]
pub struct StreamReader {
    iovec: OwningIovec<'static>,
    chunker: StreamChunker,
}

/// The [`StreamReader`] periodically invokes a function to determine
/// what to do with the current COBS-encoded record.  This enum describes
/// the potential actions.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StreamAction {
    /// Keep decoding the record
    KeepGoing,
    /// Skip to the next record
    SkipRecord,
    /// Stop with EOF right away
    Stop,
}

#[derive(Clone, Debug, Default)]
struct StreamChunker {
    buf: AnchoredSlice,
    offset: u64,
}

#[derive(Debug)]
enum Chunk {
    Sentinel(u64),
    Eof,
    Data((u64, AnchoredSlice)),
}

impl StreamChunker {
    pub fn pump(
        &mut self,
        arena: &mut ByteArena,
        mut reader: impl std::io::Read,
        io_block_size: usize,
    ) -> Result<Chunk> {
        use std::io::Read;
        while self.buf.slice().len() < 2 {
            let buf = self.buf.take();

            let initial_length = buf.slice().len();
            let mut slice = buf.slice();
            let concat = (&mut slice).chain(&mut reader);

            let buf = arena.read_n(concat, io_block_size, NonZeroUsize::MAX)?;
            if buf.slice().len() == initial_length {
                // No progress, must be Eof.
                if buf.slice().is_empty() {
                    return Ok(Chunk::Eof);
                } else {
                    self.offset += buf.slice().len() as u64;
                    return Ok(Chunk::Data((self.offset, buf)));
                }
            }

            self.buf = buf;
        }

        assert!(self.buf.slice().len() >= 2);

        if self.buf.slice()[0..2] == super::STUFF_SEQUENCE {
            self.offset += 2;
            self.buf.skip_prefix(2);
            return Ok(Chunk::Sentinel(self.offset));
        }

        let split_pos = if let Some(idx) = super::find_stuff_sequence(self.buf.slice()) {
            // Split at the stuff sequence if we have one.
            idx
        } else if *self.buf.slice().last().unwrap() == STUFF_SEQUENCE[0] {
            // Split just before the last byte if it could be part of a stuff sequence
            self.buf.slice().len() - 1
        } else {
            // otherwise, take the whole slice.
            self.buf.slice().len()
        };

        // We already checked for that case.
        assert_ne!(split_pos, 0);

        let prefix;
        (prefix, self.buf) = self.buf.take().split_at(split_pos);

        self.offset += prefix.slice().len() as u64;
        Ok(Chunk::Data((self.offset, prefix)))
    }
}

impl StreamReader {
    /// Returns a fresh default-constructed [`StreamReader`]
    pub fn new() -> Self {
        Default::default()
    }

    /// Returns a judge function for COBS-encoded records.
    ///
    /// Records whose size exceeds `max_record_size` are skipped, and
    /// decoding stops when we see [`STUFF_SEQUENCE`] delimiter for a new
    /// record that would start at or after `limit_offset` in the encoded
    /// bytes.
    pub fn chunk_judge(
        max_record_size: usize,
        limit_offset: Option<u64>,
    ) -> impl Fn(Range<u64>, ConsumingIovec<'_>) -> StreamAction {
        let limit_offset = limit_offset.unwrap_or(u64::MAX);

        move |range, iovec| {
            if range.start >= limit_offset {
                StreamAction::Stop
            } else if iovec.total_size() > max_record_size {
                StreamAction::SkipRecord
            } else {
                StreamAction::KeepGoing
            }
        }
    }

    /// Attempts to decode the next [`STUFF_SEQUENCE`] delimited record
    /// from `reader`.
    ///
    /// Calls the `record_judge` with the current byte range in the
    /// stuffed input for the record the bytes decoded so far in order
    /// to know what to do: keep attempting to decode the record, skip
    /// the record, or stop reading (i.e., EOF).
    ///
    /// Returns an IO error if `reader` does, and None on EOF.  Otherwise,
    /// returns a pair of:
    ///  - a slice of `[IoSlice`] whose concatenation is the record's contents
    ///  - the number of bytes reads so far (including stuff sequence bytes,
    ///    earlier skipped or invalid records, and the bytes in the [`IoSlice`]s.
    pub fn next_record_bytes(
        &mut self,
        mut reader: impl std::io::Read,
        mut record_judge: impl FnMut(Range<u64>, ConsumingIovec<'_>) -> StreamAction,
        io_block_size: Option<usize>,
    ) -> Result<Option<(&[IoSlice<'_>], Range<u64>)>> {
        #[derive(PartialEq, Eq)]
        enum State {
            // We start here, until we hit a non-STUFF_SEQUENCE byte
            SkipSentinel,
            // Then keep decoding...
            DecodeRecord,
            // Until we hit an invalid encoded sequence, or the judge
            // tells us to skip.
            SkipRecord,
        }

        let io_block_size = io_block_size.unwrap_or(DEFAULT_BLOCK_SIZE);

        'retry: loop {
            self.iovec.clear();
            let mut decoder = Decoder::new_from_iovec(self.iovec.take());

            let mut state = State::SkipSentinel;
            let mut range = 0u64..0u64;
            loop {
                assert_eq!(range.is_empty(), state == State::SkipSentinel);

                match self
                    .chunker
                    .pump(decoder.consumer().arena(), &mut reader, io_block_size)?
                {
                    Chunk::Sentinel(offset) => {
                        match state {
                            State::SkipSentinel => range = offset..offset,
                            // We hit a sentinel, so the record is complete.
                            State::DecodeRecord | State::SkipRecord => break,
                        }
                    }
                    Chunk::Eof => {
                        // We hit EOF and didn't find any data chunk.  Bail.
                        if range.is_empty() {
                            return Ok(None);
                        }

                        break;
                    }
                    Chunk::Data((offset, slice)) => {
                        // data slices are non-empty.
                        assert!(!slice.slice().is_empty());

                        match state {
                            // We were in SkipSentinel state, so this is a new record.
                            State::SkipSentinel => {
                                let start = offset - (slice.slice().len() as u64);
                                range = start..start;
                                state = State::DecodeRecord
                            }
                            State::DecodeRecord => {}
                            // Don't `continue`: let the judge have at it and decide if it's
                            // time to just stop decoding.
                            State::SkipRecord => {}
                        }

                        // Try to decode if we should
                        if state == State::DecodeRecord && decoder.decode_anchored(slice).is_err() {
                            // And skip the rest of the record if it's invalid.
                            state = State::SkipRecord;
                        }

                        range.end = offset;
                    }
                }

                match record_judge(range.clone(), decoder.consumer()) {
                    StreamAction::KeepGoing => {}
                    StreamAction::SkipRecord => state = State::SkipRecord,
                    StreamAction::Stop => return Ok(None),
                }
            }

            // We only get here from a DecodeRecord state (or EOF and range non-empty)
            assert_ne!(&range.start, &range.end);

            if state == State::SkipRecord {
                self.iovec = decoder.take_iovec();
                continue 'retry;
            }

            let Ok(iovec) = decoder.finish() else {
                continue 'retry;
            };

            self.iovec = iovec;
            return Ok(Some((self.iovec.iovs().expect("no backpatch left"), range)));
        }
    }
}

// Check that we can read a couple COBS records.
#[test]
fn test_stream_reader_miri() {
    let payload: &[&[u8]] = &[
        b"\x01a", // Missing stuff sequence here
        &STUFF_SEQUENCE,
        b"\x02bc",
        &STUFF_SEQUENCE,
        &STUFF_SEQUENCE,
        b"\x03def",
        &STUFF_SEQUENCE,
        &STUFF_SEQUENCE, // extra stuff sequence
        &STUFF_SEQUENCE,
        b"\x03ghijk", // invalid
        &STUFF_SEQUENCE,
        b"\xffghijk", // invalid
        &STUFF_SEQUENCE,
        &STUFF_SEQUENCE,
        b"\x071234567", // too long
        &STUFF_SEQUENCE,
        &STUFF_SEQUENCE,
        b"\x01z",
        // missing stuff sequence here
    ];
    let judge = StreamReader::chunk_judge(4, None);
    let mut payload = &payload.concat()[..];

    let mut reader = StreamReader::new();
    let (slices, pos) = reader
        .next_record_bytes(&mut payload, &judge, TEST_BLOCK_SIZE)
        .expect("must succeed")
        .expect("must have data");
    assert_eq!(pos, 0..2);

    assert_eq!(
        slices
            .iter()
            .flat_map(|x| -> &[u8] { x })
            .copied()
            .collect::<Vec<u8>>(),
        b"a"
    );

    let (slices, pos) = reader
        .next_record_bytes(&mut payload, &judge, TEST_BLOCK_SIZE)
        .expect("must succeed")
        .expect("must have data");
    assert_eq!(pos, 4..7);

    assert_eq!(
        slices
            .iter()
            .flat_map(|x| -> &[u8] { x })
            .copied()
            .collect::<Vec<u8>>(),
        b"bc"
    );

    let (slices, pos) = reader
        .next_record_bytes(&mut payload, &judge, TEST_BLOCK_SIZE)
        .expect("must succeed")
        .expect("must have data");
    assert_eq!(pos, 11..15);

    assert_eq!(
        slices
            .iter()
            .flat_map(|x| -> &[u8] { x })
            .copied()
            .collect::<Vec<u8>>(),
        b"def"
    );

    let (slices, pos) = reader
        .next_record_bytes(&mut payload, &judge, TEST_BLOCK_SIZE)
        .expect("must succeed")
        .expect("must have data");
    assert_eq!(pos, 51..53);

    assert_eq!(
        slices
            .iter()
            .flat_map(|x| -> &[u8] { x })
            .copied()
            .collect::<Vec<u8>>(),
        b"z"
    );

    // Should hit EOF
    assert!(reader
        .next_record_bytes(&mut payload, &judge, TEST_BLOCK_SIZE)
        .expect("must succeed")
        .is_none());
    // And stay there
    assert!(reader
        .next_record_bytes(&mut payload, &judge, TEST_BLOCK_SIZE)
        .expect("must succeed")
        .is_none());
}

// Confirm that we can stop reading after an offset.
#[test]
fn test_stream_reader_partial_miri() {
    let contents: &[&[u8]] = &[b"\x01a", &STUFF_SEQUENCE, b"\x02bc"];
    let mut payload = &contents.concat()[..];

    let judge = StreamReader::chunk_judge(usize::MAX, None);
    let mut reader = StreamReader::new();
    let (slices, pos) = reader
        .next_record_bytes(&mut payload, &judge, TEST_BLOCK_SIZE)
        .expect("must succeed")
        .expect("must have data");
    assert_eq!(pos, 0..2);
    assert_eq!(
        slices
            .iter()
            .flat_map(|x| -> &[u8] { x })
            .copied()
            .collect::<Vec<u8>>(),
        b"a"
    );
    let (slices, pos) = reader
        .next_record_bytes(&mut payload, &judge, TEST_BLOCK_SIZE)
        .expect("must succeed")
        .expect("must have data");
    assert_eq!(pos, 4..7);

    assert_eq!(
        slices
            .iter()
            .flat_map(|x| -> &[u8] { x })
            .copied()
            .collect::<Vec<u8>>(),
        b"bc"
    );

    // Should hit EOF
    assert!(reader
        .next_record_bytes(&mut payload, &judge, TEST_BLOCK_SIZE)
        .expect("must succeed")
        .is_none());

    // Now do the same thing, but stop after byte 1.
    let judge = StreamReader::chunk_judge(usize::MAX, Some(1u64));
    let mut payload = &contents.concat()[..];
    let mut reader = StreamReader::new();
    let (slices, pos) = reader
        .next_record_bytes(&mut payload, &judge, TEST_BLOCK_SIZE)
        .expect("must succeed")
        .expect("must have data");
    assert_eq!(pos, 0..2);
    assert_eq!(
        slices
            .iter()
            .flat_map(|x| -> &[u8] { x })
            .copied()
            .collect::<Vec<u8>>(),
        b"a"
    );

    // Should immediately hit EOF
    assert!(reader
        .next_record_bytes(&mut payload, &judge, TEST_BLOCK_SIZE)
        .expect("must succeed")
        .is_none());

    // Stop after byte 1, on a stuff sequence.
    let contents: &[&[u8]] = &[b"\x01a", &STUFF_SEQUENCE, &STUFF_SEQUENCE, b"\x02bc"];

    let judge = StreamReader::chunk_judge(usize::MAX, Some(1u64));
    let mut payload = &contents.concat()[..];
    let mut reader = StreamReader::new();
    let (slices, pos) = reader
        .next_record_bytes(&mut payload, &judge, TEST_BLOCK_SIZE)
        .expect("must succeed")
        .expect("must have data");
    assert_eq!(pos, 0..2);
    assert_eq!(
        slices
            .iter()
            .flat_map(|x| -> &[u8] { x })
            .copied()
            .collect::<Vec<u8>>(),
        b"a"
    );

    // Should immediately hit EOF
    assert!(reader
        .next_record_bytes(&mut payload, &judge, TEST_BLOCK_SIZE)
        .expect("must succeed")
        .is_none());
}

// Empty file should direct return EOF
#[test]
fn test_stream_reader_empty_miri() {
    let mut payload: &[u8] = &[];

    let mut reader = StreamReader::new();
    assert!(reader
        .next_record_bytes(
            &mut payload,
            StreamReader::chunk_judge(usize::MAX, None),
            TEST_BLOCK_SIZE
        )
        .expect("must succeed")
        .is_none());
}

// Only a stuff sequence -> return EOF
#[test]
fn test_stream_reader_stuff_only_miri() {
    let mut payload = &STUFF_SEQUENCE[..];

    let mut reader = StreamReader::new();
    assert!(reader
        .next_record_bytes(
            &mut payload,
            StreamReader::chunk_judge(usize::MAX, None),
            TEST_BLOCK_SIZE
        )
        .expect("must succeed")
        .is_none());
}

// Couple stuff sequence -> data, should decode fine.
#[test]
fn test_stream_reader_many_stuff_miri() {
    let payload: &[&[u8]] = &[&STUFF_SEQUENCE, &STUFF_SEQUENCE, b"\x00"];

    let mut payload = &payload.concat()[..];
    let mut reader = StreamReader::new();
    let (slices, pos) = reader
        .next_record_bytes(
            &mut payload,
            StreamReader::chunk_judge(usize::MAX, None),
            TEST_BLOCK_SIZE,
        )
        .expect("must succeed")
        .expect("must have data");

    assert_eq!(slices.len(), 0);
    assert_eq!(pos, 4..5);
}

// Only one message should decode fine.
#[test]
fn test_stream_reader_one_message_miri() {
    let mut payload = &b"\x01a"[..];

    let mut reader = StreamReader::new();

    let (slices, pos) = reader
        .next_record_bytes(
            &mut payload,
            StreamReader::chunk_judge(usize::MAX, None),
            TEST_BLOCK_SIZE,
        )
        .expect("must succeed")
        .expect("must have data");
    assert_eq!(pos, 0..2);
    assert_eq!(
        slices
            .iter()
            .flat_map(|x| -> &[u8] { x })
            .copied()
            .collect::<Vec<u8>>(),
        b"a"
    );

    assert!(reader
        .next_record_bytes(
            &mut payload,
            StreamReader::chunk_judge(usize::MAX, None),
            TEST_BLOCK_SIZE
        )
        .expect("must succeed")
        .is_none());
}

// Rruncated messages should be skipped.
#[test]
fn test_stream_reader_truncated_message_miri() {
    // Two truncated messages, one terminated by a stuff sequence,
    // another by EOF.
    let mut payload = &b"\x02a\xFE\xFD\x05b"[..];

    let mut reader = StreamReader::new();

    assert!(reader
        .next_record_bytes(
            &mut payload,
            StreamReader::chunk_judge(usize::MAX, None),
            TEST_BLOCK_SIZE
        )
        .expect("must succeed")
        .is_none());
}

// We should gracefully bubble up an error in the middle of a
// record.
#[test]
fn test_stream_reader_error_miri() {
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

    let mut payload = Reader {
        payload: b"\x01a\xFE\xFD\x00",
    };

    let mut reader = StreamReader::new();

    let (slices, pos) = reader
        .next_record_bytes(
            &mut payload,
            StreamReader::chunk_judge(usize::MAX, None),
            TEST_BLOCK_SIZE,
        )
        .expect("must succeed")
        .expect("must have data");
    assert_eq!(pos, 0..2);
    assert_eq!(
        slices
            .iter()
            .flat_map(|x| -> &[u8] { x })
            .copied()
            .collect::<Vec<u8>>(),
        b"a"
    );

    assert!(reader
        .next_record_bytes(
            &mut payload,
            StreamReader::chunk_judge(usize::MAX, None),
            TEST_BLOCK_SIZE
        )
        .is_err());
}
