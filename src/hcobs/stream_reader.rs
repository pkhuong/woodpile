use std::io::IoSlice;
use std::io::Result;
use std::num::NonZeroUsize;

use super::Decoder;
use super::STUFF_SEQUENCE;
use crate::AnchoredSlice;
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
        iovec: &mut OwningIovec<'_>,
        mut reader: impl std::io::Read,
        io_block_size: usize,
    ) -> Result<Chunk> {
        use std::io::Read;
        while self.buf.slice().len() < 2 {
            let buf = self.buf.take();

            let initial_length = buf.slice().len();
            let mut slice = buf.slice();
            let concat = (&mut slice).chain(&mut reader);

            let buf = iovec.arena_read_n(concat, io_block_size, NonZeroUsize::MAX)?;
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

    /// Clears internal buffered state that has already been returned
    /// as record contents.
    pub fn reset_iovec(&mut self) {
        self.iovec = OwningIovec::new_from_arena(self.iovec.take().take_arena())
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
    ) -> impl Fn(u64, usize, &[IoSlice<'_>]) -> StreamAction {
        let limit_offset = limit_offset.unwrap_or(u64::MAX);

        move |offset, size, _slices| {
            if size == 0 && offset >= limit_offset {
                StreamAction::Stop
            } else if size > max_record_size {
                StreamAction::SkipRecord
            } else {
                StreamAction::KeepGoing
            }
        }
    }

    /// Attempts to decode the next [`STUFF_SEQUENCE`] delimited record
    /// from `reader`.
    ///
    /// Calls the `record_judge` with the current byte offset and the number
    /// of bytes decoded so far, and the bytes decoded so far, to know what
    /// to do: keep attempting to decode the record, skip the record, or
    /// stop reading (i.e., EOF).
    ///
    /// Returns an IO error if `reader` does, and None on EOF.  Otherwise,
    /// returns a pair of:
    ///  - a slice of `[IoSlice`] whose concatenation is the record's contents
    ///  - the number of bytes reads so far (including stuff sequence bytes,
    ///    earlier skipped or invalid records, and the bytes in the [`IoSlice`]s.
    pub fn next_record_bytes(
        &mut self,
        mut reader: impl std::io::Read,
        mut record_judge: impl FnMut(u64, usize, &[IoSlice<'_>]) -> StreamAction,
        io_block_size: Option<usize>,
    ) -> Result<Option<(&[IoSlice<'_>], u64)>> {
        'retry: loop {
            let io_block_size = io_block_size.unwrap_or(DEFAULT_BLOCK_SIZE);
            self.reset_iovec();
            let mut decoder = Decoder::new_from_iovec(self.iovec.take());
            let mut skip_sentinel = true; // true until we hit a non-STUFF_SEQUENCE byte.
            let mut last_pos = 0;
            let mut skip_record = false; // True if we want to drop the record.
            loop {
                let pos;
                match self
                    .chunker
                    .pump(decoder.iovec(), &mut reader, io_block_size)?
                {
                    Chunk::Sentinel(offset) => {
                        pos = offset;
                        if !skip_sentinel {
                            break;
                        }

                        // We skipped a delimiter, so we're reading a fresh record now
                        skip_record = false;
                    }
                    Chunk::Eof => {
                        // We hit EOF and didn't find any data chunk.  Bail.
                        if last_pos == 0 {
                            return Ok(None);
                        }

                        break;
                    }
                    Chunk::Data((offset, slice)) => {
                        // Give the judge one last chance if this is the first data chunk.
                        if last_pos == 0
                            && record_judge(offset - slice.slice().len() as u64, 0, &[])
                                == StreamAction::Stop
                        {
                            return Ok(None);
                        }

                        // slice is non-empty, so offset > 0,
                        pos = offset;
                        skip_sentinel = false;
                        last_pos = offset;

                        if skip_record {
                            continue;
                        }

                        if decoder.decode_anchored(slice).is_err() {
                            skip_record = true;
                        }
                    }
                }

                match record_judge(
                    pos,
                    decoder.iovec().total_size(),
                    decoder.iovec().stable_prefix(),
                ) {
                    StreamAction::KeepGoing => {}
                    StreamAction::SkipRecord => {
                        skip_record = true;
                    }
                    StreamAction::Stop => return Ok(None),
                }
            }

            assert_ne!(last_pos, 0);

            if skip_record {
                self.iovec = decoder.iovec().take();
                continue 'retry;
            }

            let Ok(iovec) = decoder.finish() else {
                continue 'retry;
            };

            self.iovec = iovec;
            return Ok(Some((
                self.iovec.iovs().expect("no backpatch left"),
                last_pos,
            )));
        }
    }
}

// Check that we can read a couple COBS records.
#[test]
fn test_stream_reader() {
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
    assert_eq!(pos, 2);

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
    assert_eq!(pos, 7);

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
    assert_eq!(pos, 15);

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
    assert_eq!(pos, 53);

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
fn test_stream_reader_partial() {
    let contents: &[&[u8]] = &[b"\x01a", &STUFF_SEQUENCE, b"\x02bc"];
    let mut payload = &contents.concat()[..];

    let judge = StreamReader::chunk_judge(usize::MAX, None);
    let mut reader = StreamReader::new();
    let (slices, pos) = reader
        .next_record_bytes(&mut payload, &judge, TEST_BLOCK_SIZE)
        .expect("must succeed")
        .expect("must have data");
    assert_eq!(pos, 2);
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
    assert_eq!(pos, 7);

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
    assert_eq!(pos, 2);
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
    assert_eq!(pos, 2);
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
fn test_stream_reader_empty() {
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
fn test_stream_reader_stuff_only() {
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
fn test_stream_reader_many_stuff() {
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
    assert_eq!(pos, 5);
}

// Only one message should decode fine.
#[test]
fn test_stream_reader_one_message() {
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
    assert_eq!(pos, 2);
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
fn test_stream_reader_truncated_message() {
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
fn test_stream_reader_error() {
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
    assert_eq!(pos, 2);
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
