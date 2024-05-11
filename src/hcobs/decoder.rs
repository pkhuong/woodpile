use crate::hcobs::Parameters;
use crate::hcobs::RADIX;
use crate::hcobs::STUFF_SEQUENCE;
#[cfg(test)]
use crate::hcobs::TEST_PARAMS;

use std::io::Result;
use std::num::NonZeroU32;

use crate::OwningIovec;

#[derive(Debug, Eq, PartialEq)]
pub struct InitialState {}

#[derive(Debug, Eq, PartialEq)]
pub struct BeforeChunk {
    insert_stuff_sequence: bool,
}

#[derive(Debug, Eq, PartialEq)]
pub struct MidHeader {
    initial_byte: u8,
}

#[derive(Debug, Eq, PartialEq)]
pub struct InChunk {
    remaining: NonZeroU32,
    terminate_with_stuff_sequence: bool,
}

#[derive(Debug, Eq, PartialEq)]
pub enum DecoderState {
    InitialState(InitialState),
    BeforeChunk(BeforeChunk),
    MidHeader(MidHeader),
    InChunk(InChunk),
}

impl Default for DecoderState {
    fn default() -> Self {
        DecoderState::new()
    }
}

impl DecoderState {
    pub fn new() -> DecoderState {
        DecoderState::InitialState(InitialState {})
    }

    pub fn terminate(self) -> Result<()> {
        match self {
            DecoderState::BeforeChunk(state) => {
                if state.insert_stuff_sequence {
                    // We must have a stuff sequence pending if we terminate
                    Ok(())
                } else {
                    Err(std::io::Error::other(
                        "should have short chunk before termination",
                    ))
                }
            }
            _ => Err(std::io::Error::other("decoding terminated mid-stream")),
        }
    }

    pub fn decode_borrow<'slices>(
        mut self,
        iovec: &mut OwningIovec<'slices>,
        params: Parameters,
        mut input: &'slices [u8],
    ) -> Result<Self> {
        while !input.is_empty() {
            let consumed;

            (self, consumed) = match self {
                DecoderState::InitialState(state) => state.decode(iovec, params, input)?,
                DecoderState::BeforeChunk(state) => state.decode(iovec, params, input)?,
                DecoderState::MidHeader(state) => state.decode(iovec, params, input)?,
                DecoderState::InChunk(state) => state.decode_borrow(iovec, params, input),
            };

            input = &input[consumed..];
        }

        Ok(self)
    }

    pub fn decode_copy(
        mut self,
        iovec: &mut OwningIovec<'_>,
        params: Parameters,
        mut input: &[u8],
    ) -> Result<Self> {
        while !input.is_empty() {
            let consumed;

            (self, consumed) = match self {
                DecoderState::InitialState(state) => state.decode(iovec, params, input)?,
                DecoderState::BeforeChunk(state) => state.decode(iovec, params, input)?,
                DecoderState::MidHeader(state) => state.decode(iovec, params, input)?,
                DecoderState::InChunk(state) => state.decode_copy(iovec, params, input),
            };

            input = &input[consumed..];
        }

        Ok(self)
    }
}

impl InitialState {
    fn decode(
        self,
        _iovec: &mut OwningIovec<'_>,
        params: Parameters,
        input: &[u8],
    ) -> Result<(DecoderState, usize)> {
        assert!(!input.is_empty());

        let chunk_size = input[0] as usize;
        let max_initial_size: usize = params.max_initial_size.into();
        if chunk_size > max_initial_size {
            return Err(std::io::Error::other("invalid initial chunk size"));
        }

        let terminate_with_stuff_sequence = chunk_size < max_initial_size;
        if chunk_size > 0 {
            Ok((
                DecoderState::InChunk(InChunk {
                    remaining: NonZeroU32::new(chunk_size as u32).unwrap(),
                    terminate_with_stuff_sequence,
                }),
                1,
            ))
        } else {
            Ok((
                DecoderState::BeforeChunk(BeforeChunk {
                    insert_stuff_sequence: terminate_with_stuff_sequence,
                }),
                1,
            ))
        }
    }
}

impl BeforeChunk {
    fn decode(
        self,
        iovec: &mut OwningIovec<'_>,
        _params: Parameters,
        input: &[u8],
    ) -> Result<(DecoderState, usize)> {
        assert!(!input.is_empty());

        if self.insert_stuff_sequence {
            iovec.push_copy(&STUFF_SEQUENCE);
        }

        let initial_byte = input[0];
        if initial_byte as usize >= RADIX {
            Err(std::io::Error::other("invalid chunk header first byte"))
        } else {
            Ok((DecoderState::MidHeader(MidHeader { initial_byte }), 1))
        }
    }
}

impl MidHeader {
    fn decode(
        self,
        _iovec: &mut OwningIovec<'_>,
        params: Parameters,
        input: &[u8],
    ) -> Result<(DecoderState, usize)> {
        assert!(!input.is_empty());

        let second_byte = input[0] as usize;
        if second_byte >= RADIX {
            return Err(std::io::Error::other("invalid chunk header second byte"));
        }

        let chunk_size = (self.initial_byte as usize) + (second_byte * RADIX);
        let max_subsequent_size: usize = params.max_subsequent_size.into();

        if chunk_size > max_subsequent_size {
            return Err(std::io::Error::other("invalid subsequent chunk size"));
        }

        let terminate_with_stuff_sequence = chunk_size < max_subsequent_size;
        if chunk_size > 0 {
            Ok((
                DecoderState::InChunk(InChunk {
                    remaining: NonZeroU32::new(chunk_size as u32).unwrap(),
                    terminate_with_stuff_sequence,
                }),
                1,
            ))
        } else {
            Ok((
                DecoderState::BeforeChunk(BeforeChunk {
                    insert_stuff_sequence: terminate_with_stuff_sequence,
                }),
                1,
            ))
        }
    }
}

impl InChunk {
    fn update(mut self, bytes_consumed: usize) -> (DecoderState, usize) {
        if bytes_consumed < self.remaining.get() as usize {
            self.remaining = NonZeroU32::new(self.remaining.get() - bytes_consumed as u32).unwrap();
            (DecoderState::InChunk(self), bytes_consumed)
        } else {
            assert_eq!(self.remaining.get(), bytes_consumed as u32);
            let insert_stuff_sequence = self.terminate_with_stuff_sequence;
            (
                DecoderState::BeforeChunk(BeforeChunk {
                    insert_stuff_sequence,
                }),
                bytes_consumed,
            )
        }
    }

    fn decode_borrow<'slices>(
        self,
        iovec: &mut OwningIovec<'slices>,
        _params: Parameters,
        input: &'slices [u8],
    ) -> (DecoderState, usize) {
        assert!(!input.is_empty());

        let bytes_consumed = input.len().min(self.remaining.get() as usize);
        iovec.push(&input[..bytes_consumed]);
        self.update(bytes_consumed)
    }

    fn decode_copy(
        self,
        iovec: &mut OwningIovec<'_>,
        _params: Parameters,
        input: &[u8],
    ) -> (DecoderState, usize) {
        assert!(!input.is_empty());

        let bytes_consumed = input.len().min(self.remaining.get() as usize);
        iovec.push_copy(&input[..bytes_consumed]);
        self.update(bytes_consumed)
    }
}

#[cfg(test)]
fn decode_with_test_params(bytes: &[u8]) -> Result<Vec<u8>> {
    let decode_one = || {
        let mut iovec = OwningIovec::new();
        let mut decoder = DecoderState::new();

        decoder = decoder.decode_borrow(&mut iovec, TEST_PARAMS, bytes)?;
        decoder.terminate()?;

        Ok(iovec.flatten().expect("no backpatch left"))
    };

    // Redundantly decode with copy and check it's the same result
    let decode_two = || -> Result<Vec<u8>> {
        let mut iovec = OwningIovec::new();
        let mut decoder: DecoderState = Default::default();

        for byte in bytes {
            decoder = decoder.decode_copy(&mut iovec, TEST_PARAMS, &[*byte])?;
        }

        decoder.terminate()?;

        Ok(iovec.flatten().expect("no backpatch left"))
    };

    let ret = decode_one();
    let redundant = decode_two();

    assert_eq!(ret.is_err(), redundant.is_err());
    ret
}

// Test some expected input/output pairs
#[test]
fn test_simple_miri() {
    assert_eq!(decode_with_test_params(b"\x00").unwrap(), b"");
    assert_eq!(decode_with_test_params(b"\x011").unwrap(), b"1");
    assert_eq!(decode_with_test_params(b"\x0212").unwrap(), b"12");
    assert_eq!(decode_with_test_params(b"\x03123\x00\x00").unwrap(), b"123");
    assert_eq!(
        decode_with_test_params(b"\x03123\x04\x004567").unwrap(),
        b"1234567"
    );
    assert_eq!(
        decode_with_test_params(b"\x03123\x05\x0045678\x00\x00").unwrap(),
        b"12345678"
    );
    assert_eq!(
        decode_with_test_params(b"\x03123\x05\x0045678\x01\x009").unwrap(),
        b"123456789"
    );
    assert_eq!(
        decode_with_test_params(b"\x00\x00\x00").unwrap(),
        b"\xFE\xFD"
    );
    assert_eq!(
        decode_with_test_params(b"\x011\x00\x00").unwrap(),
        b"1\xFE\xFD"
    );
    assert_eq!(
        decode_with_test_params(b"\x0312\xFE\x01\x00\xFD").unwrap(),
        b"12\xFE\xFD"
    );
    assert_eq!(
        decode_with_test_params(b"\x03123\x00\x00\x00\x00").unwrap(),
        b"123\xFE\xFD"
    );
    assert_eq!(
        decode_with_test_params(b"\x03123\x01\x004\x01\x00\xFE").unwrap(),
        b"1234\xFE\xFD\xFE"
    );
    assert_eq!(
        decode_with_test_params(b"\x03123\x02\x004\xFE\x00\x00").unwrap(),
        b"1234\xFE\xFE\xFD"
    );
    assert_eq!(
        decode_with_test_params(b"\x03123\x04\x004\xFE\xFE\xFE").unwrap(),
        b"1234\xFE\xFE\xFE"
    );
    assert_eq!(
        decode_with_test_params(b"\x03123\x04\x004\xFD\xFD\xFD").unwrap(),
        b"1234\xFD\xFD\xFD"
    );
}

#[test]
fn test_error_miri() {
    // Bad initial header

    // Truncated
    assert!(decode_with_test_params(b"\x01").is_err());
    // No terminating chunk
    assert!(decode_with_test_params(b"\x03123").is_err());

    // Bad radix
    assert!(decode_with_test_params(b"\xff").is_err());
    // Too long
    assert!(decode_with_test_params(b"\x0f").is_err());

    // Truncated first chunk
    assert!(decode_with_test_params(b"\x021").is_err());

    // No terminating chunk
    assert!(decode_with_test_params(b"\x03123").is_err());

    // Bad second header (first byte)
    assert!(decode_with_test_params(b"\x03123\xff").is_err());

    // Bad second header (second byte)
    assert!(decode_with_test_params(b"\x03123\x00\xff").is_err());

    // Bad second header (too large)
    assert!(decode_with_test_params(b"\x03123\x00\x01").is_err());

    // Truncated second chunk
    assert!(decode_with_test_params(b"\x03123\x01\x00").is_err());

    // No terminating chunk
    assert!(decode_with_test_params(b"\x03123\x05\x0045678").is_err());
}

#[cfg(test)]
fn compare_decode_with_test_params(
    contiguous: &[u8],
    initial: &[u8],
    last: &[u8],
    split: &[&[u8]],
) {
    let decode_zero = || -> Result<(DecoderState, Vec<u8>)> {
        let mut iovec = OwningIovec::new();
        let mut decoder = DecoderState::new();

        decoder = decoder.decode_borrow(&mut iovec, TEST_PARAMS, contiguous)?;

        Ok((decoder, iovec.flatten().expect("no backpatch left")))
    };

    let decode_one = || -> Result<(DecoderState, Vec<u8>)> {
        let mut iovec = OwningIovec::new();
        let mut decoder = DecoderState::new();

        decoder = decoder.decode_borrow(&mut iovec, TEST_PARAMS, initial)?;
        decoder = decoder.decode_borrow(&mut iovec, TEST_PARAMS, last)?;

        Ok((decoder, iovec.flatten().expect("no backpatch left")))
    };

    let decode_two = || -> Result<(DecoderState, Vec<u8>)> {
        let mut iovec = OwningIovec::new();
        let mut decoder = DecoderState::new();

        decoder = decoder.decode_copy(&mut iovec, TEST_PARAMS, initial)?;
        for (idx, slice) in split.iter().enumerate() {
            if (idx % 2) == 0 {
                decoder = decoder.decode_borrow(&mut iovec, TEST_PARAMS, slice)?;
            } else {
                decoder = decoder.decode_copy(&mut iovec, TEST_PARAMS, slice)?;
            }
        }

        Ok((decoder, iovec.flatten().expect("no backpatch left")))
    };

    let contiguous_result = decode_zero();
    let first_result = decode_one();
    let second_result = decode_two();

    assert_eq!(contiguous_result.is_err(), first_result.is_err());
    assert_eq!(first_result.is_err(), second_result.is_err());

    if first_result.is_ok() {
        let contiguous_result = contiguous_result.unwrap();
        let first_result = first_result.unwrap();
        let second_result = second_result.unwrap();

        assert_eq!(contiguous_result, first_result);
        assert_eq!(first_result, second_result);
    }
}

// Start decoding up to `start`, the fork decoding (one incremental, one not),
// and confirm we have the same final state.
#[test]
fn test_incremental_slow() {
    let patterns = &[
        b"\x03123\x02\x004\xFE\x00\x00",
        b"\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09",
        b"\x0212\x05\x0045678",
        b"\x00\x05\x0045678\x00\x00",
    ];

    #[cfg(miri)]
    let patterns = &patterns[..2];

    for pattern in patterns {
        for start in 0..pattern.len() {
            for end in (start + 1)..=pattern.len() {
                for mid in start..=end {
                    compare_decode_with_test_params(
                        &pattern[..end],
                        &pattern[..start],
                        &pattern[start..end],
                        &[&pattern[start..mid], &pattern[mid..end]],
                    );
                }
            }
        }
    }
}
