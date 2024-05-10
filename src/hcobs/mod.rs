//! This module implements the hybrid consistent-overhead byte/word
//! stuffing scheme of <https://pvk.ca/Blog/2021/01/11/stuff-your-logs/>,
//! with an incremental interface.
mod decoder;
mod encoder;

use std::io::Read;
use std::io::Result;
use std::num::NonZeroUsize;

use crate::AnchoredSlice;
use crate::OwningIovec;
use decoder::DecoderState;
use encoder::EncoderState;

/// The encoding radix for size headers in the hybrid byte stuffing scheme.
pub const RADIX: usize = 0xfd;
#[allow(clippy::assertions_on_constants)]
const _: () = assert!(RADIX == 253);

/// The forbidden (stuff) sentinel sequence that is removed by encoding
/// and restored by decoding.
pub const STUFF_SEQUENCE: [u8; 2] = [0xfe, 0xfd];

#[derive(Clone, Copy)]
struct Parameters {
    max_initial_size: NonZeroUsize,
    max_subsequent_size: NonZeroUsize,
}

const PROD_PARAMS: Parameters = Parameters {
    max_initial_size: unsafe { NonZeroUsize::new_unchecked(RADIX - 1) },
    max_subsequent_size: unsafe { NonZeroUsize::new_unchecked((RADIX * RADIX) - 1) },
};

#[cfg(test)]
const TEST_PARAMS: Parameters = Parameters {
    max_initial_size: unsafe { NonZeroUsize::new_unchecked(3) },
    max_subsequent_size: unsafe { NonZeroUsize::new_unchecked(5) },
};

/// Returns the index (for the first byte) for the first occurrence of
/// [`STUFF_SEQUENCE`] in the input `bytes`, or `None` if the stuff
/// sequence can't be found.
#[inline(never)]
pub fn find_stuff_sequence(bytes: &[u8]) -> Option<usize> {
    for (idx, window) in bytes.windows(2).enumerate() {
        if window == STUFF_SEQUENCE {
            return Some(idx);
        }
    }

    None
}

/// Byte stuffs arbitrary inputs incrementally.
#[derive(Debug)]
pub struct Encoder<'this> {
    state: EncoderState,
    iovec: OwningIovec<'this>,
}

impl<'this> Default for Encoder<'this> {
    fn default() -> Self {
        Encoder::new()
    }
}

impl<'this> Encoder<'this> {
    /// Returns a new encoder with a fresh [`OwningIovec`].
    pub fn new() -> Self {
        Encoder::new_from_iovec(OwningIovec::new())
    }

    /// Returns a new encoder with a pre-existing [`OwningIovec`].
    pub fn new_from_iovec(mut iovec: OwningIovec<'this>) -> Self {
        Encoder {
            state: EncoderState::new(&mut iovec, PROD_PARAMS),
            iovec,
        }
    }

    /// Returns the underlying [`OwningIovec`]
    ///
    /// Useful to consume incrementally from the output.
    #[must_use]
    pub fn iovec(&mut self) -> &mut OwningIovec<'this> {
        &mut self.iovec
    }

    /// Appends `data` to the bytes to encode.
    ///
    /// This method tries to avoid copying large `data`.
    pub fn encode(&mut self, data: &'this [u8]) {
        let mut state = Default::default();
        std::mem::swap(&mut state, &mut self.state);
        self.state = state.encode_borrow(&mut self.iovec, PROD_PARAMS, data);
    }

    /// Appends `data` to the bytes to encode.
    pub fn encode_copy(&mut self, data: &[u8]) {
        let mut state = Default::default();
        std::mem::swap(&mut state, &mut self.state);
        self.state = state.encode_copy(&mut self.iovec, PROD_PARAMS, data);
    }

    /// Appends the bytes in `data` to the bytes to encode.
    pub fn encode_anchored(&mut self, data: AnchoredSlice) {
        let (slice, anchor) = unsafe { data.components() };

        self.encode(slice);
        self.iovec.push_anchor(anchor);
    }

    /// Convenience wrapper around `self.iovec().arena_read_n` and [`Self::encode_anchored`].
    ///
    /// Reads up to `count` bytes from `reader` with up to `attempts` calls, then
    /// encodes the bytes read.
    ///
    /// On success. returns the number of bytes read from `reader`.  Failure can
    /// only happen during reading.
    pub fn encode_read(
        &mut self,
        reader: impl Read,
        count: usize,
        attempts: NonZeroUsize,
    ) -> Result<usize> {
        let anchored_slice = self.iovec.arena_read_n(reader, count, attempts)?;
        assert!(anchored_slice.slice().len() <= count);
        let ret = anchored_slice.slice().len();

        self.encode_anchored(anchored_slice);
        Ok(ret)
    }

    /// Flushes any pending encoding bytes and returns the underlying
    /// [`OwningIovec`].
    #[must_use]
    pub fn finish(mut self) -> OwningIovec<'this> {
        self.state.terminate(&mut self.iovec);
        self.iovec
    }
}

/// Attempts to decode byte-stuffed data incrementally.
#[derive(Debug)]
pub struct Decoder<'this> {
    state: DecoderState,
    iovec: OwningIovec<'this>,
}

impl<'this> Default for Decoder<'this> {
    fn default() -> Self {
        Decoder::new()
    }
}

impl<'this> Decoder<'this> {
    /// Returns a new decoder with a fresh [`OwningIovec`].
    pub fn new() -> Self {
        Decoder::new_from_iovec(OwningIovec::new())
    }

    /// Returns a new decoder with a pre-existing [`OwningIovec`].
    pub fn new_from_iovec(iovec: OwningIovec<'this>) -> Self {
        Decoder {
            state: DecoderState::new(),
            iovec,
        }
    }

    /// Returns the underlying [`OwningIovec`].
    ///
    /// Useful to consume incrementally from the output.
    #[must_use]
    pub fn iovec(&mut self) -> &mut OwningIovec<'this> {
        &mut self.iovec
    }

    /// Appends `data` to the bytes to decode.
    ///
    /// This methods tries to avoid copying large `data`.
    pub fn decode(&mut self, data: &'this [u8]) -> Result<()> {
        let mut state = Default::default();
        std::mem::swap(&mut state, &mut self.state);
        self.state = state.decode_borrow(&mut self.iovec, PROD_PARAMS, data)?;
        Ok(())
    }

    /// Appends `data` to the bytes to decode.
    pub fn decode_copy(&mut self, data: &[u8]) -> Result<()> {
        let mut state = Default::default();
        std::mem::swap(&mut state, &mut self.state);
        self.state = state.decode_copy(&mut self.iovec, PROD_PARAMS, data)?;
        Ok(())
    }

    /// Appends the contents of `data` to the bytes to decode.
    pub fn decode_anchored(&mut self, data: AnchoredSlice) -> Result<()> {
        let (slice, anchor) = unsafe { data.components() };

        let ret = self.decode(slice);
        self.iovec.push_anchor(anchor);
        ret
    }

    /// Convenience wrapper around `self.iovec().arena_read_n` and [`Self::decode_anchored`].
    ///
    /// Reads up to `count` bytes from `reader` with up to `attempts` calls, then
    /// attempts to decode the bytes read.
    ///
    /// On success. returns the number of bytes read from `reader`.  Failure could
    /// happen during reading or decoding.
    pub fn decode_read(
        &mut self,
        reader: impl Read,
        count: usize,
        attempts: NonZeroUsize,
    ) -> Result<usize> {
        let anchored_slice = self.iovec.arena_read_n(reader, count, attempts)?;
        assert!(anchored_slice.slice().len() <= count);
        let len = anchored_slice.slice().len();

        self.decode_anchored(anchored_slice).and(Ok(len))
    }

    /// Returns the underlying `OwningIovec`, if the input is complete.
    pub fn finish(self) -> Result<OwningIovec<'this>> {
        self.state.terminate()?;
        Ok(self.iovec)
    }
}

#[cfg(test)]
struct BadReader {
    count: usize, // first invocation is successful.
}

#[cfg(test)]
impl Read for BadReader {
    fn read(&mut self, dst: &mut [u8]) -> Result<usize> {
        self.count += 1;
        match self.count {
            1 => {
                let mut reader = &b"7"[..];
                reader.read(dst)
            }
            2 => Err(std::io::Error::new(
                std::io::ErrorKind::Interrupted,
                "interrupted",
            )),
            3 => {
                let mut reader = &b"89"[..];
                reader.read(dst)
            }
            5 => {
                let mut reader = &b""[..];
                reader.read(dst)
            }
            _ => Err(std::io::Error::other("bad read")),
        }
    }
}

// Smoke test the public interface.
#[test]
fn smoke_test() {
    let mut encoder: Encoder<'_> = Default::default();

    encoder.iovec().ensure_arena_capacity(10);
    encoder.encode(b"123");
    encoder.encode_copy(b"456");
    assert!(encoder
        .encode_read(BadReader { count: 10 }, 3, NonZeroUsize::new(1).unwrap())
        .is_err()); // Bad read should no-op
    assert_eq!(
        encoder
            .encode_read(BadReader { count: 10 }, 0, NonZeroUsize::new(1).unwrap())
            .unwrap(),
        0
    ); // 0-sized reads succeed
    assert_eq!(
        encoder
            .encode_read(BadReader { count: 4 }, 3, NonZeroUsize::new(1).unwrap())
            .unwrap(),
        0
    ); // EOF read succeed
    assert!(encoder
        .encode_read(BadReader { count: 1 }, 3, NonZeroUsize::new(1).unwrap())
        .is_err()); // EINTR fails
    assert_eq!(
        encoder
            .encode_read(BadReader { count: 0 }, 4, NonZeroUsize::new(5).unwrap())
            .expect("read must succeed"),
        3
    ); // handle short reads

    assert_eq!(
        encoder
            .encode_read(BadReader { count: 0 }, 3, NonZeroUsize::new(5).unwrap())
            .expect("read must succeed"),
        3
    ); // exact reads also work

    let iovec = encoder.finish();
    assert_eq!(
        iovec.flatten().expect("no backpatch left"),
        b"\x0c123456789789"
    );

    // decode
    {
        let mut decoder: Decoder<'_> = Default::default();
        for slice in iovec.into_iter() {
            decoder.decode(slice).expect("success");
        }

        // Can peek
        assert_eq!(
            decoder.iovec().flatten().expect("no backpatch left"),
            b"123456789789"
        );

        // Termination succeeds
        let output = decoder.finish().expect("success");
        assert_eq!(
            output.flatten().expect("no backpatch left"),
            b"123456789789"
        );
    }

    // decode copy
    {
        let mut decoder: Decoder<'_> = Default::default();
        for slice in iovec.into_iter() {
            decoder.decode_copy(slice).expect("success");
        }

        assert_eq!(
            decoder.iovec().flatten().expect("no backpatch left"),
            b"123456789789"
        );

        let output = decoder.finish().expect("success");
        assert_eq!(
            output.flatten().expect("no backpatch left"),
            b"123456789789"
        );
    }

    // decode read
    {
        let mut decoder: Decoder<'_> = Default::default();

        // Bad read should no-op
        assert!(decoder
            .decode_read(BadReader { count: 10 }, 3, NonZeroUsize::new(1).unwrap())
            .is_err());

        for slice in iovec.into_iter() {
            let slice: &[u8] = slice;
            decoder
                .decode_read(slice, slice.len(), NonZeroUsize::new(1).unwrap())
                .expect("success");
        }

        assert_eq!(
            decoder.iovec().flatten().expect("no backpatch left"),
            b"123456789789"
        );

        let output = decoder.finish().expect("success");
        assert_eq!(
            output.flatten().expect("no backpatch left"),
            b"123456789789"
        );
    }
}

// make sure we can consume incrementally with the prod interface.
#[test]
fn prod_peek() {
    let mut encoder: Encoder<'_> = Default::default();

    // The initial cache is 4KB, write that much.
    for _ in 0..1024 {
        encoder.encode(b"\x00\x00\x00\x00");
    }

    // Force the chunk to end.
    encoder.encode(b"\xFE\xFD");

    let header: &[u8] = b"\xfc";
    let zeros = vec![0u8; 4000];
    let second_header: &[u8] = b"\x31\x0f";
    // 252 zeros, then 4096 - 252 = 3844 zeros.
    let expected = [header, &zeros[..252], second_header, &zeros[..3844]].concat();

    assert_eq!(encoder.iovec().stable_prefix().len(), 1);

    assert_eq!(
        &encoder
            .iovec()
            .stable_prefix()
            .iter()
            .flat_map(|x| -> &[u8] { x })
            .copied()
            .collect::<Vec<u8>>(),
        // Only 4095 because the last 4-byte write goes directly to the
        // next arena chunk instead of spltting.
        &expected[0..4095]
    );

    assert_eq!(encoder.iovec().consume(1), 1);

    let iovec = encoder.finish();
    assert_eq!(
        iovec.flatten().expect("no backpatch left"),
        [
            0, 0, 0, 0, // final 4-byte write
            0, 0
        ] // terminator
    );
}

// Exercise error handling in decoding.
#[test]
fn prod_decode_bad() {
    {
        let mut decoder: Decoder<'_> = Default::default();

        // Bad data.
        assert!(decoder.decode(b"\xff").is_err());
    }

    {
        let mut decoder: Decoder<'_> = Default::default();

        // Same, with decode_copy
        assert!(decoder.decode_copy(b"\xff").is_err());
    }

    {
        let mut decoder: Decoder<'_> = Default::default();

        // Truncated chunk
        decoder.decode(b"\xfc").expect("ok");
        decoder.decode_copy(&vec![0u8; 253]).expect("ok");

        // Missing the next chunk.
        assert!(decoder.finish().is_err());
    }
}

#[cfg(test)]
use rusty_fork::rusty_fork_test;

#[cfg(test)]
rusty_fork_test! {
    #[test]
    fn prod_encode_streaming() {
        assert_eq!(crate::ByteArena::num_live_chunks(), 0);
        assert_eq!(crate::ByteArena::num_live_bytes(), 0);

        let mut encoder: Encoder<'_> = Default::default();
        let payload = [1u8; 1000];

        for _ in 0..10000 {
            encoder.encode_copy(&payload);
            let prefix = encoder.iovec().stable_prefix();
            if !prefix.is_empty() {
                let len = prefix.len();
                encoder.iovec().consume(len);
            }
        }

        assert!(crate::ByteArena::num_live_chunks() <= 2);
        assert!(crate::ByteArena::num_live_bytes() <= 2 * 1024 * 1024);

        std::mem::drop(encoder);

        assert_eq!(crate::ByteArena::num_live_chunks(), 0);
        assert_eq!(crate::ByteArena::num_live_bytes(), 0);
    }

    #[test]
    fn prod_decode_streaming() {
        assert_eq!(crate::ByteArena::num_live_chunks(), 0);
        assert_eq!(crate::ByteArena::num_live_bytes(), 0);

        let mut decoded_size = 0usize;
        let payload = [1u8; 1000];
        let mut encoder: Encoder<'_> = Default::default();

        let mut decoder: Decoder<'_> = Default::default();

        for _ in 0..10000 {
            encoder.encode(&payload);
            let prefix = encoder.iovec().stable_prefix();
            for slice in prefix {
                decoder.decode_copy(slice).expect("ok");
            }

            let len = prefix.len();
            encoder.iovec().consume(len);

            let prefix = decoder.iovec().stable_prefix();
            for slice in prefix {
                let slice: &[u8] = slice;
                decoded_size += slice.len();
                for byte in slice {
                    assert_eq!(*byte, 1u8);
                }
            }
            let len = prefix.len();
            decoder.iovec().consume(len);
        }

        assert!(crate::ByteArena::num_live_chunks() <= 3);
        assert!(crate::ByteArena::num_live_bytes() <= 3 * 1024 * 1024);

        let tail = encoder.finish().flatten().expect("no backpatch left");
        decoder.decode_copy(&tail).expect("valid");

        assert!(crate::ByteArena::num_live_chunks() <= 2);
        assert!(crate::ByteArena::num_live_bytes() <= 2 * 1024 * 1024);

        let decoded_tail = decoder.finish().unwrap().flatten().unwrap();
        decoded_size += decoded_tail.len();
        for byte in decoded_tail {
            assert_eq!(byte, 1u8);
        }

        assert_eq!(decoded_size, 10_000 * payload.len());

        assert_eq!(crate::ByteArena::num_live_chunks(), 0);
        assert_eq!(crate::ByteArena::num_live_bytes(), 0);
    }
}
