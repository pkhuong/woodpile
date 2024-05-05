use crate::hcobs::find_stuff_sequence;
use crate::hcobs::Parameters;
use crate::hcobs::PROD_PARAMS;
use crate::hcobs::RADIX;
use crate::hcobs::STUFF_SEQUENCE;
#[cfg(test)]
use crate::hcobs::TEST_PARAMS;

use std::num::NonZeroUsize;

use crate::owning_iovec::OwningIovecBackref;
use crate::OwningIovec;

#[derive(Debug)]
pub struct EncoderState {
    max_chunk_size: NonZeroUsize,
    current_chunk_size: usize,
    maybe_mid_stuff: bool,
    backref: OwningIovecBackref,
}

impl Default for EncoderState {
    fn default() -> Self {
        EncoderState {
            max_chunk_size: PROD_PARAMS.max_initial_size,
            current_chunk_size: 0,
            maybe_mid_stuff: false,
            backref: Default::default(),
        }
    }
}

impl EncoderState {
    pub fn new(iovec: &mut OwningIovec<'_>, params: Parameters) -> Self {
        EncoderState {
            max_chunk_size: params.max_initial_size,
            current_chunk_size: 0,
            maybe_mid_stuff: false,
            backref: iovec.register_patch(&[0u8]),
        }
    }

    fn new_subsequent(iovec: &mut OwningIovec<'_>, params: Parameters) -> Self {
        EncoderState {
            max_chunk_size: params.max_subsequent_size,
            current_chunk_size: 0,
            maybe_mid_stuff: false,
            backref: iovec.register_patch(&[0u8, 0u8]),
        }
    }

    pub fn encode_borrow<'slices>(
        mut self,
        iovec: &mut OwningIovec<'slices>,
        params: Parameters,
        mut input: &'slices [u8],
    ) -> Self {
        while !input.is_empty() {
            // If `maybe_mid_stuff`, we're buffering one byte, because it's
            // equal to `STUFF_SEQUENCE[0]`.
            let had_buffered_data = self.maybe_mid_stuff;
            let consumed;

            (self, consumed) = self.consume_once(iovec, params, input, |this, iovec, prefix| {
                this.write(iovec, &input[0..prefix]);
            });

            // Can't consume too much.
            assert!(consumed <= input.len());
            // We should usually consume something, but it's possible to not
            // consume anything if we instead dumped our internal buffered byte.
            assert!((consumed > 0) | (!self.maybe_mid_stuff & had_buffered_data));

            input = &input[consumed..];
        }

        self
    }

    pub fn encode_copy(
        mut self,
        iovec: &mut OwningIovec<'_>,
        params: Parameters,
        mut input: &[u8],
    ) -> Self {
        while !input.is_empty() {
            // If `maybe_mid_stuff`, we're buffering one byte, because it's
            // equal to `STUFF_SEQUENCE[0]`.
            let had_buffered_data = self.maybe_mid_stuff;
            let consumed;

            (self, consumed) = self.consume_once(iovec, params, input, |this, iovec, prefix| {
                this.copy(iovec, &input[0..prefix]);
            });

            // Can't consume too much.
            assert!(consumed <= input.len());
            // We should usually consume something, but it's possible to not
            // consume anything if we instead dumped our internal buffered byte.
            assert!((consumed > 0) | (!self.maybe_mid_stuff & had_buffered_data));

            input = &input[consumed..];
        }

        self
    }

    pub fn terminate(mut self, iovec: &mut OwningIovec<'_>) {
        if self.maybe_mid_stuff {
            self.write_partial_stuff_sequence(iovec);
        }

        assert!(self.current_chunk_size < self.max_chunk_size.get());
        Self::encode_header(self.current_chunk_size, iovec, self.backref);
    }

    fn encode_header(chunk_size: usize, iovec: &mut OwningIovec<'_>, backref: OwningIovecBackref) {
        assert!(chunk_size < RADIX * RADIX);

        let header = [(chunk_size % RADIX) as u8, (chunk_size / RADIX) as u8, 0];
        let len = backref.len();
        assert!((1..=2).contains(&len));
        assert!(header[len] == 0);

        iovec.backfill(backref, &header[0..len]);
    }

    #[inline(never)]
    fn write<'slices>(&mut self, iovec: &mut OwningIovec<'slices>, payload: &'slices [u8]) {
        if payload.is_empty() {
            return;
        }

        iovec.push(payload);
        self.current_chunk_size += payload.len();
        assert!(self.current_chunk_size <= self.max_chunk_size.get());
    }

    #[inline(never)]
    fn copy(&mut self, iovec: &mut OwningIovec<'_>, payload: &[u8]) {
        if payload.is_empty() {
            return;
        }

        iovec.push_copy(payload);
        self.current_chunk_size += payload.len();
        assert!(self.current_chunk_size <= self.max_chunk_size.get());
    }

    #[inline(always)]
    fn write_partial_stuff_sequence(&mut self, iovec: &mut OwningIovec<'_>) {
        iovec.push_copy(&[STUFF_SEQUENCE[0]]);
        self.current_chunk_size += 1;
        assert!(self.current_chunk_size <= self.max_chunk_size.get());
    }

    fn consume_once<'slices>(
        mut self,
        iovec: &mut OwningIovec<'slices>,
        params: Parameters,
        mut input: &[u8],
        // writer writes the `usize` prefix of `input` to the iovec.
        writer: impl FnOnce(&mut Self, &mut OwningIovec<'slices>, usize),
    ) -> (Self, usize) {
        assert!(!input.is_empty());
        assert!(
            self.current_chunk_size + (self.maybe_mid_stuff as usize) < self.max_chunk_size.get()
        );

        // How many bytes we consumed before terminating the chunk
        let consumed = if self.maybe_mid_stuff & (input[0] == STUFF_SEQUENCE[1]) {
            // Completed a stuff between two slices sequence, write out the header!
            1
        } else {
            assert!(self.current_chunk_size < self.max_chunk_size.get());

            if self.maybe_mid_stuff {
                // We buffered the previous slice's last byte. Write it out.
                self.write_partial_stuff_sequence(iovec);
                // If this was the last byte, we would have flushed it.
                assert!(self.current_chunk_size < self.max_chunk_size.get());
            }

            let remaining = self.max_chunk_size.get() - self.current_chunk_size;
            input = &input[..input.len().min(remaining)];

            // remaining > 0 and input is initially non-empty.
            assert!(!input.is_empty());

            // See if we found the end of a chunk.
            let (num_to_write, consumed) = if let Some(index) = find_stuff_sequence(input) {
                // We found a stuff sequence before the mandatory end of chunk.
                (index, index + STUFF_SEQUENCE.len())
            } else if input.len() == remaining {
                // We got to the mandatory end of the chunk.
                (remaining, remaining)
            } else {
                // we're definitely not done with the chunk sequence.
                let ret = input.len();

                // If the slice's last byte matches the first of the stuff sequence,
                // we can't write it out just yet.
                self.maybe_mid_stuff = input[input.len() - 1] == STUFF_SEQUENCE[0];
                let to_copy = if self.maybe_mid_stuff { ret - 1 } else { ret };

                writer(&mut self, iovec, to_copy);

                assert!(
                    self.current_chunk_size + (self.maybe_mid_stuff as usize)
                        < self.max_chunk_size.get()
                );
                return (self, ret);
            };

            writer(&mut self, iovec, num_to_write);
            consumed
        };

        Self::encode_header(self.current_chunk_size, iovec, self.backref);
        (Self::new_subsequent(iovec, params), consumed)
    }
}

#[cfg(test)]
fn encode_with_test_params(bytes: &[u8]) -> Vec<u8> {
    let mut iovec = OwningIovec::new();
    let mut encoder = EncoderState::new(&mut iovec, TEST_PARAMS);

    encoder = encoder.encode_borrow(&mut iovec, TEST_PARAMS, bytes);
    encoder.terminate(&mut iovec);

    let ret = iovec.flatten().expect("no backpatch left");

    // Redundantly encode with copy and check it's the same result
    {
        let mut iovec = OwningIovec::new();
        let mut encoder = EncoderState::new(&mut iovec, TEST_PARAMS);

        encoder = encoder.encode_copy(&mut iovec, TEST_PARAMS, bytes);
        encoder.terminate(&mut iovec);

        assert_eq!(&iovec.flatten().expect("no backpatch left"), &ret);
    }

    ret
}

// Test some expected input/output pairs
#[test]
fn test_simple() {
    assert_eq!(encode_with_test_params(b""), b"\x00");
    assert_eq!(encode_with_test_params(b"1"), b"\x011");
    assert_eq!(encode_with_test_params(b"12"), b"\x0212");
    assert_eq!(encode_with_test_params(b"123"), b"\x03123\x00\x00");
    assert_eq!(encode_with_test_params(b"1234567"), b"\x03123\x04\x004567");
    assert_eq!(
        encode_with_test_params(b"12345678"),
        b"\x03123\x05\x0045678\x00\x00"
    );
    assert_eq!(
        encode_with_test_params(b"123456789"),
        b"\x03123\x05\x0045678\x01\x009"
    );
    assert_eq!(encode_with_test_params(b"\xFE\xFD"), b"\x00\x00\x00");
    assert_eq!(encode_with_test_params(b"1\xFE\xFD"), b"\x011\x00\x00");
    assert_eq!(
        encode_with_test_params(b"12\xFE\xFD"),
        b"\x0312\xFE\x01\x00\xFD"
    );
    assert_eq!(
        encode_with_test_params(b"123\xFE\xFD"),
        b"\x03123\x00\x00\x00\x00"
    );
    assert_eq!(
        encode_with_test_params(b"1234\xFE\xFD\xFE"),
        b"\x03123\x01\x004\x01\x00\xFE"
    );
    assert_eq!(
        encode_with_test_params(b"1234\xFE\xFE\xFD"),
        b"\x03123\x02\x004\xFE\x00\x00"
    );
    assert_eq!(
        encode_with_test_params(b"1234\xFE\xFE\xFE"),
        b"\x03123\x04\x004\xFE\xFE\xFE"
    );
    assert_eq!(
        encode_with_test_params(b"1234\xFD\xFD\xFD"),
        b"\x03123\x04\x004\xFD\xFD\xFD"
    );
}

// Split a bunch of test vectors in different places, make sure the
// the result is the same.
//
// The idea is that the encoding is deterministic function of the
// current state and the input slice, and that terminating the
// encoding captures the current state pretty well.
#[cfg(test)]
fn compare_encode_with_test_params(contiguous: &[u8], split: &[&[u8]]) {
    let contiguous_encoded = encode_with_test_params(contiguous);

    let mut iovec = OwningIovec::new();
    let mut encoder = EncoderState::new(&mut iovec, TEST_PARAMS);

    for subslice in split.iter().copied() {
        encoder = encoder.encode_copy(&mut iovec, TEST_PARAMS, subslice);
    }

    encoder.terminate(&mut iovec);

    let split_encoded = iovec.flatten().expect("no backpatch left");

    // Same thing with borrow and copy.
    for should_copy in [[false, false], [true, false], [false, true]] {
        // we already did copy everything
        let mut iovec = OwningIovec::new();
        let mut encoder = EncoderState::new(&mut iovec, TEST_PARAMS);

        for (idx, subslice) in split.iter().copied().enumerate() {
            if should_copy[idx % 2] {
                encoder = encoder.encode_borrow(&mut iovec, TEST_PARAMS, subslice);
            } else {
                encoder = encoder.encode_copy(&mut iovec, TEST_PARAMS, subslice);
            }
        }

        encoder.terminate(&mut iovec);

        assert_eq!(
            &split_encoded,
            &iovec.flatten().unwrap() // ,
                                      // "should_copy={:?}",
                                      // should_copy
        );
    }

    assert_eq!(
        contiguous_encoded,
        split_encoded // ,
                      // "contiguous={:?}\nsplit={:?}\n => {:?}\n => {:?}",
                      // contiguous, split, contiguous_encoded, split_encoded
    );
}

#[test]
fn test_split() {
    let patterns = &[
        b"123456789abcdef",
        b"12345678\xFE\xFD\xFEabcd",
        b"12345678\xFE\xFE\xFEabcd",
        b"12345678\xFD\xFD\xFDabcd",
        b"12345678\xFD\xFE\xFDabcd",
    ];

    for pattern in patterns {
        for start in 0..pattern.len() {
            for end in (start + 1)..=pattern.len() {
                for mid in start..=end {
                    compare_encode_with_test_params(
                        &pattern[start..end],
                        &[&pattern[start..mid], &pattern[mid..end]],
                    );
                }
            }
        }
    }
}
