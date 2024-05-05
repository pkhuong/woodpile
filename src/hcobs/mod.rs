//! This module implements the hybrid consistent-overhead byte/word
//! stuffing scheme of <https://pvk.ca/Blog/2021/01/11/stuff-your-logs/>,
//! with an incremental interface.
mod encoder;

use std::num::NonZeroUsize;

use crate::OwningIovec;
use encoder::EncoderState;

pub const RADIX: usize = 0xfd;
#[allow(clippy::assertions_on_constants)]
const _: () = assert!(RADIX == 253);
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

#[inline(never)]
pub fn find_stuff_sequence(bytes: &[u8]) -> Option<usize> {
    for (idx, window) in bytes.windows(2).enumerate() {
        if window == STUFF_SEQUENCE {
            return Some(idx);
        }
    }

    None
}

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
    pub fn new() -> Self {
        Encoder::new_from_iovec(OwningIovec::new())
    }

    pub fn new_from_iovec(mut iovec: OwningIovec<'this>) -> Self {
        Encoder {
            state: EncoderState::new(&mut iovec, PROD_PARAMS),
            iovec,
        }
    }

    pub fn iovec(&mut self) -> &mut OwningIovec<'this> {
        &mut self.iovec
    }

    pub fn encode(&mut self, data: &'this [u8]) {
        let mut state = Default::default();
        std::mem::swap(&mut state, &mut self.state);
        self.state = state.encode_borrow(&mut self.iovec, PROD_PARAMS, data);
    }

    pub fn encode_copy(&mut self, data: &[u8]) {
        let mut state = Default::default();
        std::mem::swap(&mut state, &mut self.state);
        self.state = state.encode_copy(&mut self.iovec, PROD_PARAMS, data);
    }

    #[must_use]
    pub fn finish(mut self) -> OwningIovec<'this> {
        self.state.terminate(&mut self.iovec);
        self.iovec
    }
}

// Smoke test the public interface.
#[test]
fn smoke_test() {
    let mut encoder: Encoder<'_> = Default::default();

    encoder.iovec().ensure_arena_capacity(10);
    encoder.encode(b"123");
    encoder.encode_copy(b"456");

    let iovec = encoder.finish();
    assert_eq!(iovec.flatten().expect("no backpatch left"), b"\x06123456");
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
