//! This module implements the hybrid consistent-overhead word
//! stuffing scheme of <https://pvk.ca/Blog/2021/01/11/stuff-your-logs/>,
//! with a minimally copy-optimised interface.

use std::io::IoSlice;
use std::io::Result;
use std::ops::Deref;

use crate::OwningIovec;
use smallvec::SmallVec;

const RADIX: usize = 0xfd;
#[allow(clippy::assertions_on_constants)]
const _: () = assert!(RADIX == 253);
const STUFF_HEADER: [u8; 2] = [0xfeu8, 0xfdu8];

#[derive(Clone, Copy)]
struct Parameters {
    max_initial_size: usize,
    max_subsequent_size: usize,
}

const PROD_PARAMS: Parameters = Parameters {
    max_initial_size: RADIX - 1,
    max_subsequent_size: (RADIX * RADIX) - 1,
};

/// Encodes the bytes in the concatenation of `slices` with a hybrid
/// consistent-overhead byte stuff scheme that avoids the stuffed
/// subsequence `0xFE 0xFD`.
///
/// Appends the encoded bytes to `dst` and returns the result.
#[must_use]
pub fn stuff_slices<'slice, T: Deref<Target = &'slice [u8]>>(
    slices: impl IntoIterator<Item = T>,
    dst: OwningIovec<'slice>,
) -> OwningIovec<'slice> {
    stuff_slices_with_params(PROD_PARAMS, slices, dst)
}

/// Encodes `slice` with a hybrid consistent-overhead byte stuff
/// scheme that avoids the stuffed subsequence `0xFE 0xFD`.
///
/// Appends the encoded bytes to `dst` and returns the result.
#[must_use]
#[inline(never)]
pub fn stuff_slice<'slice>(slice: &'slice [u8], dst: OwningIovec<'slice>) -> OwningIovec<'slice> {
    stuff_slices([slice].iter(), dst)
}

/// Attempts to decode the bytes in the concatenation of `slices` as
/// hybrid consistent-overhead byte stuffed data, as constructed by
/// [`stuff_slices`].
///
/// Appends the decoded bytes to `dst` and returns the result, or
/// an error if the bytes are incorrectly encoded.
pub fn unstuff_slices<'slice, T: Deref<Target = &'slice [u8]>>(
    slices: impl IntoIterator<Item = T>,
    dst: OwningIovec<'slice>,
) -> Result<OwningIovec<'slice>> {
    unstuff_slices_with_params(PROD_PARAMS, slices, dst)
}

/// Attempts to decode `slice` as hybrid consistent-overhead byte
/// stuffed data, as constructed by [`stuff_slices`].
///
/// Appends the decoded bytes to `dst` and returns the result, or
/// an error if the bytes are incorrectly encoded.
#[inline(never)]
pub fn unstuff_slice<'slice>(
    slice: &'slice [u8],
    dst: OwningIovec<'slice>,
) -> Result<OwningIovec<'slice>> {
    unstuff_slices([slice].iter(), dst)
}

#[inline(always)]
fn stuff_slices_with_params<'slice, T: Deref<Target = &'slice [u8]>>(
    params: Parameters,
    slices: impl IntoIterator<Item = T>,
    dst: OwningIovec<'slice>,
) -> OwningIovec<'slice> {
    stuff_segments(params, segment_slices(params, slices), dst)
}

#[inline(always)]
fn unstuff_slices_with_params<'slice, T: Deref<Target = &'slice [u8]>>(
    params: Parameters,
    slices: impl IntoIterator<Item = T>,
    mut dst: OwningIovec<'slice>,
) -> Result<OwningIovec<'slice>> {
    let other = std::io::Error::other;

    // `slices` is a peekable of non-empty slices.
    let read_byte = |slices: &mut std::iter::Peekable<_>| -> Result<u8> {
        if let Some(curr) = slices.peek_mut() {
            let curr: &mut &'slice [u8] = curr;
            assert!(!curr.is_empty());

            let ret = curr[0];
            *curr = &curr[1..];

            if curr.is_empty() {
                slices.next();
            }

            return Ok(ret);
        }

        Err(other("short stuffed sequence"))
    };

    let mut slices = slices
        .into_iter()
        .filter_map(|slice| -> Option<&'slice [u8]> {
            if slice.is_empty() {
                None
            } else {
                Some(&slice)
            }
        })
        .peekable();

    let mut chunk_size: usize = read_byte(&mut slices)? as usize;

    if chunk_size > params.max_initial_size {
        return Err(other("bad initial byte"));
    }

    // Do we need to write a STUFF_HEADER at the end of the chunk.
    let mut needs_header = chunk_size < params.max_initial_size;

    while slices.peek().is_some() {
        // We got to the end of a chunk.  Write out the STUFF_HEADER
        // if necessary, and find the new chunk size.
        if chunk_size == 0 {
            if needs_header {
                dst.push(&STUFF_HEADER);
            }

            let first = read_byte(&mut slices).expect("slices is non-empty") as usize;
            let second = read_byte(&mut slices)? as usize;

            if (first >= RADIX) | (second >= RADIX) {
                return Err(other("bad header byte"));
            }

            chunk_size = first + RADIX * second;

            if chunk_size > params.max_subsequent_size {
                return Err(other("bad header value"));
            }

            needs_header = chunk_size < params.max_subsequent_size;

            // We made *some* progress by reading 2 bytes.
            //
            // Let the next iteration handle the rest.
            if chunk_size == 0 {
                continue;
            }
        }

        assert!(chunk_size > 0);

        let curr = match slices.peek_mut() {
            Some(slice) => slice,
            None => return Err(other("short stuffed sequence")),
        };

        assert!(!curr.is_empty());

        let to_copy = curr.len().min(chunk_size);
        dst.push(&curr[..to_copy]);
        chunk_size -= to_copy;

        *curr = &curr[to_copy..];
        if curr.is_empty() {
            slices.next();
        }
    }

    if chunk_size > 0 {
        return Err(other("incomplete chunk"));
    }

    Ok(dst)
}

#[inline(never)]
fn find_header(slice: &[u8]) -> (bool, usize) {
    for (idx, window) in slice.windows(2).enumerate() {
        if window == STUFF_HEADER {
            return (true, idx);
        }
    }

    (false, slice.len())
}

// Segments the iterator of slices into an iterator of slices
// such that each slice is either the stuff header, or does
// not contain the stuff header.
#[inline(always)]
fn segment_slices<'slice, T: Deref<Target = &'slice [u8]>>(
    params: Parameters,
    slices: impl IntoIterator<Item = T>,
) -> impl Iterator<Item = &'slice [u8]> {
    let mut max_slice = params.max_initial_size;
    let mut last_byte: Option<&'slice [u8]> = None; // Slice of 1 item.

    // We internally buffer up to 16 slices (256 bytes) to avoid heap allocations
    // in the common case without blowing up the stack.
    //
    // This buffer is only used when a slice is very large, or when a
    // slice contains many instances of the `STUFF_HEADER` (hopefully rare).
    let segment_slice = move |slice: Option<&'slice [u8]>| -> SmallVec<[&'slice [u8]; 16]> {
        let mut ret = SmallVec::new();

        // Look for our EOF sentinel, None.
        let mut slice = match slice {
            Some(slice) => slice,
            None => {
                // Return any final buffered byte.
                if let Some(last) = last_byte.take() {
                    assert_eq!(last.len(), 1);
                    ret.push(last);
                }

                return ret;
            }
        };

        if slice.is_empty() {
            return ret;
        }

        // Check if the buffered byte + the first byte in `slice` yield the stuff header.
        if let Some(last) = last_byte.take() {
            // We only buffer when the last byte is equal to STUFF_HEADER[0]
            assert_eq!(last, [STUFF_HEADER[0]]);
            if slice[0] == STUFF_HEADER[1] {
                ret.push(&STUFF_HEADER);
                slice = &slice[1..];
            } else {
                ret.push(last);
            }
        }

        // If the last byte in `slice` could be part of a stuff
        // header, slice it off and buffer it.
        if !slice.is_empty() {
            let split = slice.len() - 1;

            if slice[split] == STUFF_HEADER[0] {
                last_byte = Some(&slice[split..]);
                slice = &slice[..split];
            }
        }

        if slice.is_empty() {
            return ret;
        }

        while !slice.is_empty() {
            if max_slice == 0 {
                max_slice = params.max_subsequent_size;
            }

            let max_len = slice.len().min(max_slice);
            let (found, end) = find_header(&slice[..max_len]);

            ret.push(&slice[..end]);
            max_slice -= end;
            slice = &slice[end..];

            if found {
                assert!(slice.len() >= 2);
                assert_eq!(slice[0..2], STUFF_HEADER);
                ret.push(&STUFF_HEADER);
                slice = &slice[2..];
                max_slice = params.max_subsequent_size;
            }
        }

        ret
    };

    slices
        .into_iter()
        .map(|slice| -> Option<&'slice [u8]> { Some(&slice) })
        .chain([None])
        .flat_map(segment_slice)
}

#[inline(always)]
fn stuff_segments<'slice>(
    params: Parameters,
    segments: impl IntoIterator<Item = &'slice [u8]>,
    mut dst: OwningIovec<'slice>,
) -> OwningIovec<'slice> {
    let mut initial_chunk = true;
    let mut encode_size = |size: usize, dst: &mut OwningIovec<'slice>| {
        if initial_chunk {
            assert!(size <= params.max_initial_size);
            assert!(size < RADIX);

            let header = [size as u8];
            dst.push_copy(&header);
        } else {
            assert!(size <= params.max_subsequent_size);
            assert!(size < RADIX * RADIX);
            // Little endian.
            let header = [(size % RADIX) as u8, (size / RADIX) as u8];
            dst.push_copy(&header);
        }

        initial_chunk = false;
    };

    let mut size_limit = params.max_initial_size;
    // Buffer slices in the here until we find a stuff header
    // or hit the size limit.
    let mut buf = SmallVec::<[&'slice [u8]; 16]>::new();
    let mut bufsz = 0usize; // sum of slice sizes in buf.

    assert!(bufsz < size_limit);
    for slice in segments.into_iter() {
        assert!(bufsz < size_limit);

        if slice.is_empty() {
            continue;
        }

        // We found the stuff sequence, flush a chunk.
        if slice == STUFF_HEADER {
            let chunk_size = bufsz;
            size_limit = params.max_subsequent_size;

            encode_size(chunk_size, &mut dst);
            dst.extend(buf.iter().map(|slice| IoSlice::new(slice)));
            buf.clear();
            bufsz = 0;

            continue;
        }

        assert!(bufsz < size_limit);
        let mut last = slice;
        let mut total_size = bufsz + slice.len();

        while total_size >= size_limit {
            let chunk_size = size_limit;
            assert!(chunk_size <= total_size);

            size_limit = params.max_subsequent_size;
            encode_size(chunk_size, &mut dst);

            // Write out the whole `buf`
            assert!(bufsz < chunk_size);
            dst.extend(buf.iter().map(|slice| IoSlice::new(slice)));
            total_size = total_size.checked_sub(bufsz).unwrap();
            let remaining_chunk_size = chunk_size.checked_sub(bufsz).unwrap();
            buf.clear();
            bufsz = 0;

            assert!(remaining_chunk_size <= last.len());
            dst.push(&last[..remaining_chunk_size]);
            last = &last[remaining_chunk_size..];

            total_size = total_size.checked_sub(remaining_chunk_size).unwrap();
        }

        if !last.is_empty() {
            bufsz += last.len();
            buf.push(last);
        }

        assert_eq!(bufsz, total_size);
        assert!(bufsz < size_limit);
    }

    assert!(bufsz < size_limit);
    // We always have a final (short) chunk
    encode_size(bufsz, &mut dst);
    dst.extend(buf.iter().map(|slice| IoSlice::new(slice)));

    dst
}

#[test]
fn test_stuff_slice() {
    let buf: &[u8] = b"1\xFE\xFD123";

    let encoded: &[u8] = &stuff_slice(buf, OwningIovec::new()).flatten().unwrap();

    assert_eq!(encoded, b"\x011\x03\x00123");

    let decoded = unstuff_slice(encoded, OwningIovec::new())
        .expect("valid")
        .flatten()
        .unwrap();
    assert_eq!(decoded, buf);
}

#[test]
fn test_stuff_slice_long() {
    let buf: &[u8] = &(0..1024).map(|i| i as u8).collect::<Vec<u8>>();

    let encoded: &[u8] = &stuff_slices([buf].iter(), OwningIovec::new())
        .flatten()
        .unwrap();

    let decoded = unstuff_slices([encoded].iter(), OwningIovec::new())
        .expect("valid")
        .flatten()
        .unwrap();
    assert_eq!(decoded, buf);
}

#[test]
fn test_stuff_slice_descending() {
    let buf: &[u8] = &(0..1024).map(|i| (256 - i) as u8).collect::<Vec<u8>>();

    let encoded: &[u8] = &stuff_slices([buf].iter(), OwningIovec::new())
        .flatten()
        .unwrap();

    let decoded = unstuff_slices([encoded].iter(), OwningIovec::new())
        .expect("valid")
        .flatten()
        .unwrap();
    assert_eq!(decoded, buf);
}

#[test]
fn test_stuff_slice_zero() {
    let buf: &[u8] = &(0..1024).map(|_| 0u8).collect::<Vec<u8>>();

    let encoded: &[u8] = &stuff_slices([buf].iter(), OwningIovec::new())
        .flatten()
        .unwrap();

    let decoded = unstuff_slices([encoded].iter(), OwningIovec::new())
        .expect("valid")
        .flatten()
        .unwrap();
    assert_eq!(decoded, buf);
}

#[test]
fn test_stuff_slice_fd() {
    let buf: &[u8] = &(0..1024).map(|_| 0xfdu8).collect::<Vec<u8>>();

    let encoded: &[u8] = &stuff_slices([buf].iter(), OwningIovec::new())
        .flatten()
        .unwrap();

    let decoded = unstuff_slices([encoded].iter(), OwningIovec::new())
        .expect("valid")
        .flatten()
        .unwrap();
    assert_eq!(decoded, buf);
}

#[test]
fn test_stuff_slice_fe() {
    let buf: &[u8] = &(0..1024).map(|_| 0xfeu8).collect::<Vec<u8>>();

    let encoded: &[u8] = &stuff_slices([buf].iter(), OwningIovec::new())
        .flatten()
        .unwrap();

    let decoded = unstuff_slices([encoded].iter(), OwningIovec::new())
        .expect("valid")
        .flatten()
        .unwrap();
    assert_eq!(decoded, buf);
}

#[test]
fn test_stuff_slice_headers() {
    let buf: &[u8] = &(0..1024)
        .flat_map(|_| [0xfdu8, 0xfeu8])
        .collect::<Vec<u8>>();

    let encoded: &[u8] = &stuff_slices([buf].iter(), OwningIovec::new())
        .flatten()
        .unwrap();

    let decoded = unstuff_slices([encoded].iter(), OwningIovec::new())
        .expect("valid")
        .flatten()
        .unwrap();
    assert_eq!(decoded, buf);
}

// Use these test parameters to shrink test cases.

#[cfg(test)]
const TEST_PARAMS: Parameters = Parameters {
    max_initial_size: 3,
    max_subsequent_size: 5,
};

// Simple cases

#[test]
fn test_codec_empty() {
    let buf: &[u8] = b"";
    let encoded: &[u8] = &stuff_slices_with_params(TEST_PARAMS, [buf].iter(), OwningIovec::new())
        .flatten()
        .unwrap();

    assert_eq!(encoded, b"\x00");

    let decoded = unstuff_slices_with_params(TEST_PARAMS, [encoded].iter(), OwningIovec::new())
        .expect("must succeed")
        .flatten()
        .unwrap();
    assert_eq!(decoded, buf);
}

#[test]
fn test_codec_one() {
    let buf: &[u8] = b"1";
    let encoded: &[u8] = &stuff_slices_with_params(TEST_PARAMS, [buf].iter(), OwningIovec::new())
        .flatten()
        .unwrap();

    assert_eq!(encoded, b"\x011");

    let decoded = unstuff_slices_with_params(TEST_PARAMS, [encoded].iter(), OwningIovec::new())
        .expect("must succeed")
        .flatten()
        .unwrap();
    assert_eq!(decoded, buf);
}

#[test]
fn test_codec_two() {
    let buf: &[u8] = b"12";
    let encoded: &[u8] = &stuff_slices_with_params(TEST_PARAMS, [buf].iter(), OwningIovec::new())
        .flatten()
        .unwrap();

    assert_eq!(encoded, b"\x0212");

    let decoded = unstuff_slices_with_params(TEST_PARAMS, [encoded].iter(), OwningIovec::new())
        .expect("must succeed")
        .flatten()
        .unwrap();
    assert_eq!(decoded, buf);
}

#[test]
fn test_codec_one_full_chunk() {
    let buf: &[u8] = b"123";
    let encoded: &[u8] = &stuff_slices_with_params(TEST_PARAMS, [buf].iter(), OwningIovec::new())
        .flatten()
        .unwrap();

    assert_eq!(encoded, b"\x03123\x00\x00");

    let decoded = unstuff_slices_with_params(TEST_PARAMS, [encoded].iter(), OwningIovec::new())
        .expect("must succeed")
        .flatten()
        .unwrap();
    assert_eq!(decoded, buf);
}

#[test]
fn test_codec_one_full_chunk_one_partial() {
    let buf: &[u8] = b"1234567";
    let encoded: &[u8] = &stuff_slices_with_params(TEST_PARAMS, [buf].iter(), OwningIovec::new())
        .flatten()
        .unwrap();

    assert_eq!(encoded, b"\x03123\x04\x004567");

    let decoded = unstuff_slices_with_params(TEST_PARAMS, [encoded].iter(), OwningIovec::new())
        .expect("must succeed")
        .flatten()
        .unwrap();
    assert_eq!(decoded, buf);
}

#[test]
fn test_codec_two_full_chunks() {
    let buf: &[u8] = b"12345678";
    let encoded: &[u8] = &stuff_slices_with_params(TEST_PARAMS, [buf].iter(), OwningIovec::new())
        .flatten()
        .unwrap();

    assert_eq!(encoded, b"\x03123\x05\x0045678\x00\x00");

    let decoded = unstuff_slices_with_params(TEST_PARAMS, [encoded].iter(), OwningIovec::new())
        .expect("must succeed")
        .flatten()
        .unwrap();
    assert_eq!(decoded, buf);
}

#[test]
fn test_codec_two_full_chunks_one_partial() {
    let buf: &[u8] = b"123456789";
    let encoded: &[u8] = &stuff_slices_with_params(TEST_PARAMS, [buf].iter(), OwningIovec::new())
        .flatten()
        .unwrap();

    assert_eq!(encoded, b"\x03123\x05\x0045678\x01\x009");

    let decoded = unstuff_slices_with_params(TEST_PARAMS, [encoded].iter(), OwningIovec::new())
        .expect("must succeed")
        .flatten()
        .unwrap();
    assert_eq!(decoded, buf);
}

#[test]
fn test_codec_stuff() {
    let buf: &[u8] = b"\xFE\xFD";
    let encoded: &[u8] = &stuff_slices_with_params(TEST_PARAMS, [buf].iter(), OwningIovec::new())
        .flatten()
        .unwrap();

    assert_eq!(encoded, b"\x00\x00\x00");

    let decoded = unstuff_slices_with_params(TEST_PARAMS, [encoded].iter(), OwningIovec::new())
        .expect("must succeed")
        .flatten()
        .unwrap();
    assert_eq!(decoded, buf);
}

#[test]
fn test_codec_prefix_stuff() {
    let buf: &[u8] = b"1\xFE\xFD";
    let encoded: &[u8] = &stuff_slices_with_params(TEST_PARAMS, [buf].iter(), OwningIovec::new())
        .flatten()
        .unwrap();

    assert_eq!(encoded, b"\x011\x00\x00");

    let decoded = unstuff_slices_with_params(TEST_PARAMS, [encoded].iter(), OwningIovec::new())
        .expect("must succeed")
        .flatten()
        .unwrap();
    assert_eq!(decoded, buf);
}

#[test]
fn test_codec_split_stuff() {
    let buf: &[u8] = b"12\xFE\xFD";
    let encoded: &[u8] = &stuff_slices_with_params(TEST_PARAMS, [buf].iter(), OwningIovec::new())
        .flatten()
        .unwrap();

    assert_eq!(encoded, b"\x0312\xFE\x01\x00\xFD");

    let decoded = unstuff_slices_with_params(TEST_PARAMS, [encoded].iter(), OwningIovec::new())
        .expect("must succeed")
        .flatten()
        .unwrap();
    assert_eq!(decoded, buf);
}

#[test]
fn test_codec_prefix_stuff_in_subsequent() {
    let buf: &[u8] = b"123\xFE\xFD";
    let encoded: &[u8] = &stuff_slices_with_params(TEST_PARAMS, [buf].iter(), OwningIovec::new())
        .flatten()
        .unwrap();

    assert_eq!(encoded, b"\x03123\x00\x00\x00\x00");

    let decoded = unstuff_slices_with_params(TEST_PARAMS, [encoded].iter(), OwningIovec::new())
        .expect("must succeed")
        .flatten()
        .unwrap();
    assert_eq!(decoded, buf);
}

#[test]
fn test_codec_prefix_stuff_in_subsequent_2() {
    let buf: &[u8] = b"1234\xFE\xFD\xFE";
    let encoded: &[u8] = &stuff_slices_with_params(TEST_PARAMS, [buf].iter(), OwningIovec::new())
        .flatten()
        .unwrap();

    assert_eq!(encoded, b"\x03123\x01\x004\x01\x00\xFE");

    let decoded = unstuff_slices_with_params(TEST_PARAMS, [encoded].iter(), OwningIovec::new())
        .expect("must succeed")
        .flatten()
        .unwrap();
    assert_eq!(decoded, buf);
}

#[test]
fn test_codec_prefix_stuff_in_subsequent_2_split() {
    let buf: &[u8] = b"1234\xFE\xFD\xFE";
    let encoded: &[u8] = &stuff_slices_with_params(
        TEST_PARAMS,
        [&buf[..5], &buf[5..]].iter(),
        OwningIovec::new(),
    )
    .flatten()
    .unwrap();

    assert_eq!(encoded, b"\x03123\x01\x004\x01\x00\xFE");

    let decoded = unstuff_slices_with_params(TEST_PARAMS, [encoded].iter(), OwningIovec::new())
        .expect("must succeed")
        .flatten()
        .unwrap();
    assert_eq!(decoded, buf);
}

#[test]
fn test_codec_prefix_stuff_in_subsequent_2_fully_split() {
    let buf: &[u8] = b"1234\xFE\xFD\xFE";
    let bufs: &[&[u8]] = &buf.windows(1).collect::<Vec<_>>();
    let encoded: &[u8] = &stuff_slices_with_params(TEST_PARAMS, bufs.iter(), OwningIovec::new())
        .flatten()
        .unwrap();

    assert_eq!(encoded, b"\x03123\x01\x004\x01\x00\xFE");

    let decoded = unstuff_slices_with_params(TEST_PARAMS, [encoded].iter(), OwningIovec::new())
        .expect("must succeed")
        .flatten()
        .unwrap();
    assert_eq!(decoded, buf);
}

#[test]
fn test_codec_prefix_stuff_fakeout() {
    let buf: &[u8] = b"1234\xFE\xFE\xFE";
    let encoded: &[u8] = &stuff_slices_with_params(
        TEST_PARAMS,
        [&buf[..5], &buf[5..]].iter(),
        OwningIovec::new(),
    )
    .flatten()
    .unwrap();

    assert_eq!(encoded, b"\x03123\x04\x004\xFE\xFE\xFE");

    let decoded = unstuff_slices_with_params(TEST_PARAMS, [encoded].iter(), OwningIovec::new())
        .expect("must succeed")
        .flatten()
        .unwrap();
    assert_eq!(decoded, buf);
}

#[test]
fn test_codec_prefix_stuff_fakeout2() {
    let buf: &[u8] = b"1234\xFD\xFD\xFD";
    let encoded: &[u8] = &stuff_slices_with_params(
        TEST_PARAMS,
        [&buf[..5], &buf[5..]].iter(),
        OwningIovec::new(),
    )
    .flatten()
    .unwrap();

    assert_eq!(encoded, b"\x03123\x04\x004\xFD\xFD\xFD");

    let decoded = unstuff_slices_with_params(TEST_PARAMS, [encoded].iter(), OwningIovec::new())
        .expect("must succeed")
        .flatten()
        .unwrap();
    assert_eq!(decoded, buf);
}

#[test]
fn test_decode_bad_bytes() {
    // We need at least a header
    assert!(
        unstuff_slices_with_params(TEST_PARAMS, [&[0u8][..0]].iter(), OwningIovec::new()).is_err()
    );
    // If we have a header for 1 byte, we need payload
    assert!(
        unstuff_slices_with_params(TEST_PARAMS, [&[1u8][..]].iter(), OwningIovec::new()).is_err()
    );
    // Higher than the radix
    assert!(
        unstuff_slices_with_params(PROD_PARAMS, [&[255u8][..]].iter(), OwningIovec::new()).is_err()
    );
    assert!(
        unstuff_slices_with_params(PROD_PARAMS, [&[254u8][..]].iter(), OwningIovec::new()).is_err()
    );
    assert!(
        unstuff_slices_with_params(PROD_PARAMS, [&[253u8][..]].iter(), OwningIovec::new()).is_err()
    );
    // Higher than the max value
    assert!(
        unstuff_slices_with_params(TEST_PARAMS, [&[4u8][..]].iter(), OwningIovec::new()).is_err()
    );
    // Short second header
    assert!(
        unstuff_slices_with_params(TEST_PARAMS, [&[0u8, 0u8][..]].iter(), OwningIovec::new())
            .is_err()
    );

    // Bad second header bytes
    assert!(unstuff_slices_with_params(
        PROD_PARAMS,
        [&[0u8, 255u8, 0u8][..]].iter(),
        OwningIovec::new()
    )
    .is_err());
    assert!(unstuff_slices_with_params(
        PROD_PARAMS,
        [&[0u8, 0u8, 254u8][..]].iter(),
        OwningIovec::new()
    )
    .is_err());
    assert!(unstuff_slices_with_params(
        PROD_PARAMS,
        [&[0u8, 253u8, 0u8][..]].iter(),
        OwningIovec::new()
    )
    .is_err());

    // Overly large second header value
    assert!(unstuff_slices_with_params(
        TEST_PARAMS,
        [&[0u8, 252u8, 252u8][..]].iter(),
        OwningIovec::new()
    )
    .is_err());

    // Missing payload in the second chunk.
    assert!(unstuff_slices_with_params(
        TEST_PARAMS,
        [&[0u8, 1u8, 0u8][..]].iter(),
        OwningIovec::new()
    )
    .is_err());

    // And split that all sorts of ways
    assert!(unstuff_slices_with_params(
        TEST_PARAMS,
        [&[0u8][..], &[1u8, 0u8][..]].iter(),
        OwningIovec::new()
    )
    .is_err());
    assert!(unstuff_slices_with_params(
        TEST_PARAMS,
        [&[0u8, 1u8][..], &[0u8][..]].iter(),
        OwningIovec::new()
    )
    .is_err());
    assert!(unstuff_slices_with_params(
        TEST_PARAMS,
        [&[0u8][..], &[1u8, 0u8][..]].iter(),
        OwningIovec::new()
    )
    .is_err());
    assert!(unstuff_slices_with_params(
        TEST_PARAMS,
        [&[0u8][..], &[2u8, 0u8, 4u8][..]].iter(),
        OwningIovec::new()
    )
    .is_err());
    assert!(unstuff_slices_with_params(
        TEST_PARAMS,
        [&[0u8][..], &[2u8][..], &[0u8, 4u8][..]].iter(),
        OwningIovec::new()
    )
    .is_err());
    assert!(unstuff_slices_with_params(
        TEST_PARAMS,
        [&[0u8][..], &[2u8, 0u8][..], &[4u8][..]].iter(),
        OwningIovec::new()
    )
    .is_err());
    assert!(unstuff_slices_with_params(
        TEST_PARAMS,
        [&[0u8][..], &[2u8][..], &[0u8][..], &[4u8][..]].iter(),
        OwningIovec::new()
    )
    .is_err());
}
