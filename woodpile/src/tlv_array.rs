//! The TLV array module exposes encoding and decoding code for a stream of
//! transposed type-length-value elements, and for a sequence of such streams.
//!
//! The type tags are 32-bit little-endian unsigned integers, and must appear
//! in non-decreasing order.  This format matches the message format in the 10th
//! version of the roughtime draft
//! <https://www.ietf.org/archive/id/draft-ietf-ntp-roughtime-10.html#name-message-format>
use std::borrow::Cow;
use std::io::Result;

use owning_iovec::ZeroCopySink;

/// Writes out a vector of tag-value pairs to `dst`
pub fn encode_array<'dst, 'slices>(
    mut dst: impl ZeroCopySink<'dst>,
    elements: &mut [(u32, Cow<'slices, [u8]>)],
) -> Result<()>
where
    'slices: 'dst,
{
    // u32::MAX would fit, but let's be nice to languages without
    // unsigned types, and also steer clear of wraparound conditions.
    if elements.len() > i32::MAX as usize {
        return Err(std::io::Error::other(
            "May only encode up to i32::MAX elements",
        ));
    }

    if elements.iter().any(|elt| elt.1.len() > i32::MAX as usize) {
        return Err(std::io::Error::other(
            "Each value may only span up to i32::MAX bytes",
        ));
    }

    if elements.iter().map(|elt| elt.1.len() as u64).sum::<u64>() > i32::MAX as u64 {
        return Err(std::io::Error::other(
            "May only encode up to i32::MAX bytes",
        ));
    }

    elements.sort_by_key(|elt| elt.0);

    // Number of pairs
    dst.append_copy(&(elements.len() as u32).to_le_bytes());

    // Write cumulative offsets, except for the first one (i.e., prefix sum of
    // value lengths, except for the last one)
    {
        let mut acc: Option<u32> = None;

        for (_tag, value) in elements.iter() {
            if let Some(acc) = acc.as_mut() {
                dst.append_copy(&acc.to_le_bytes());
                *acc += value.len() as u32;
            } else {
                // First iteration, do nothing
                acc = Some(value.len() as u32);
            }
        }
    }

    // Spit out the tags
    for (tag, _value) in elements.iter() {
        dst.append_copy(&tag.to_le_bytes());
    }

    // And now the values
    for (_tag, value) in elements.iter() {
        match value {
            Cow::Borrowed(value) => dst.append_borrow(value),
            Cow::Owned(value) => dst.append_copy(value),
        }
    }

    Ok(())
}

/// An array of 4 bytes, interpreted as a little endian u32.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct U32Le {
    bytes: [u8; 4],
}

impl U32Le {
    /// Returns the little endian value encoded in the 4 bytes.
    pub fn value(&self) -> u32 {
        u32::from_le_bytes(self.bytes)
    }
}

impl std::convert::From<&U32Le> for u32 {
    fn from(value: &U32Le) -> u32 {
        value.value()
    }
}

impl std::cmp::PartialOrd for U32Le {
    fn partial_cmp(&self, other: &U32Le) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl std::cmp::Ord for U32Le {
    fn cmp(&self, other: &U32Le) -> std::cmp::Ordering {
        self.value().cmp(&other.value())
    }
}

/// A `TLVArray` wraps a `Cow<[u8]>` with zero-copy accessors for an encoded
/// array of tag-value pairs.  The constructor performs linear-time validation
/// (on the header); after that, all method calls run in constant or logarithmic
/// (wrt the number of pairs) time.
pub struct TLVArray<'a> {
    num_values: usize,
    storage: Cow<'a, [u8]>,
}

fn slice_as_u32le(slice: &[u8]) -> &[U32Le] {
    let size = slice.len() / 4;
    unsafe { std::slice::from_raw_parts(slice.as_ptr().cast(), size) }
}

impl<'a> TLVArray<'a> {
    /// Wraps the slices of bytes `data` into a constant-time decoding wrapper.
    pub fn new(data: Cow<'a, [u8]>) -> Result<Self> {
        if data.len() < 4 {
            return Err(std::io::Error::other("Must have room for element count."));
        }

        let num_values = u32::from_le_bytes(data[0..4].try_into().unwrap()) as usize;

        // We need at least 4 * num_values for the tags, and 4 * num_values bytes
        // again for the value count + (n - 1) offsets.
        if 8 * num_values > data.len() {
            return Err(std::io::Error::other("Must have room for whole header."));
        }

        let ret = TLVArray {
            num_values,
            storage: data,
        };

        let ascending = |xs: &[U32Le]| {
            xs.iter()
                .zip(xs.iter().skip(1))
                .all(|(left, right)| left <= right)
        };

        if !ascending(ret.offsets()) {
            return Err(std::io::Error::other("Offsets must be non-decreasing."));
        }

        if !ascending(ret.tags()) {
            return Err(std::io::Error::other("Tags must be non-decreasing."));
        }

        if let Some(last_offset) = ret.offsets().last() {
            let total = (8 * num_values).checked_add(last_offset.value() as usize);
            if total.map(|val| val <= ret.storage.len()) != Some(true) {
                return Err(std::io::Error::other("Not enough room for values."));
            }
        }

        Ok(ret)
    }

    /// Returns an iterator for the key-value pairs in the array.
    pub fn iter(&self) -> impl std::iter::Iterator<Item = (u32, &[u8])> {
        use std::iter::once;

        let header = 8 * self.num_values;

        // We already checked for >= header bytes in storage.
        let starts = once(0u32).chain(self.offsets().iter().map(U32Le::value));
        let ends = self
            .offsets()
            .iter()
            .map(|x| x.value() as usize)
            .chain(once(self.storage.len() - header));
        let tags = self.tags().iter().map(U32Le::value);

        tags.zip(starts.zip(ends)).map(move |(tag, (start, end))| {
            let start = header + start as usize;
            let end = header + end;

            (tag, &self.storage[start..end])
        })
    }

    /// Returns the number of tag-value pairs in this `DecodedArray`.
    pub fn len(&self) -> usize {
        self.num_values
    }

    /// Returns whether this `DecoderArray` contains 0 tag-value pairs.
    pub fn is_empty(&self) -> bool {
        self.num_values == 0
    }

    /// Returns the `index`th tag-value pair.
    pub fn get(&self, index: usize) -> Option<(u32, &[u8])> {
        Some((self.tags().get(index)?.value(), self.get_storage(index)?))
    }

    /// Returns the value associated with key `wanted`, if any.
    pub fn find(&self, wanted: u32) -> Option<&[u8]> {
        self.get_storage(self.find_tag(wanted)?)
    }

    /// Returns the offsets of all but the first element, relative to the end of
    /// the offset and tags.
    pub fn offsets(&self) -> &[U32Le] {
        // Start at byte 4, and we have num_values - 1 of these 4-byte values
        slice_as_u32le(&self.storage[4..(4 * self.num_values).max(4)])
    }

    /// Returns values' tags, in order.  Tags are always sorted in non-decreasing
    /// order.
    pub fn tags(&self) -> &[U32Le] {
        slice_as_u32le(&self.storage[4 * self.num_values..8 * self.num_values])
    }

    /// Returns whether the tags in this `DecodedArray` match `expected` exactly.
    pub fn tags_match_exactly(&self, expected: impl IntoIterator<Item = u32>) -> bool {
        self.tags().iter().map(U32Le::value).eq(expected)
    }

    /// Returns the index of tag `wanted`, if any.
    pub fn find_tag(&self, wanted: u32) -> Option<usize> {
        self.tags().binary_search_by_key(&wanted, U32Le::value).ok()
    }

    /// Returns the value at `index`, if any.
    pub fn get_storage(&self, index: usize) -> Option<&[u8]> {
        let header = 8 * self.num_values;

        let offsets = self.offsets();
        let end = if index == offsets.len() {
            self.storage.len()
        } else {
            (offsets.get(index)?.value() as usize) + header
        };
        let start = if index == 0 {
            0
        } else {
            offsets.get(index - 1)?.value()
        };

        let start = header + start as usize;
        // Already bound-checked in the constructor
        Some(&self.storage[start..end])
    }
}

#[test]
fn test_encode() {
    let mut sink = owning_iovec::OwningIovec::new();

    encode_array(
        &mut sink,
        &mut [(1u32, b"asd".into()), (2u32, b"zxcv".to_vec().into())],
    )
    .expect("should succeed");

    let encoded_bytes = sink.flatten().expect("must be complete");
    let expected: &[&[u8]] = &[
        &2u32.to_le_bytes(), // value count
        &3u32.to_le_bytes(), // end of first value
        &1u32.to_le_bytes(), // first tag
        &2u32.to_le_bytes(), // second tag
        b"asd",              // first value
        b"zxcv",             // second value
    ];
    assert_eq!(encoded_bytes, expected.concat());
}

#[test]
fn test_decode() {
    let mut sink = owning_iovec::OwningIovec::new();

    encode_array(
        &mut sink,
        &mut [(1u32, b"asd".into()), (2u32, b"zxcv".into())],
    )
    .expect("should succeed");

    let encoded_bytes = sink.flatten().expect("must be complete");

    let array = TLVArray::new((&encoded_bytes).into()).expect("should parse");

    assert!(array.tags_match_exactly([1, 2]));
    assert!(!array.tags_match_exactly([1, 2, 3]));
    assert!(!array.tags_match_exactly([1]));

    eprintln!("{:?}", array.iter().collect::<Vec<_>>());

    assert!(array.iter().eq([(1u32, &b"asd"[..]), (2u32, &b"zxcv"[..])]));

    assert_eq!(array.len(), 2);
    assert!(!array.is_empty());

    assert_eq!(array.get(0), Some((1u32, &b"asd"[..])));
    assert_eq!(array.get(1), Some((2u32, &b"zxcv"[..])));
    assert_eq!(array.get(2), None);
    assert_eq!(array.get(usize::MAX), None);

    assert_eq!(array.get_storage(0), Some(&b"asd"[..]));
    assert_eq!(array.get_storage(1), Some(&b"zxcv"[..]));
    assert_eq!(array.get_storage(2), None);
    assert_eq!(array.get_storage(3), None);
    assert_eq!(array.get_storage(usize::MAX), None);

    assert_eq!(array.find_tag(1u32), Some(0));
    assert_eq!(array.find_tag(2u32), Some(1));
    assert_eq!(array.find_tag(0u32), None);
    assert_eq!(array.find_tag(3u32), None);
    assert_eq!(array.find_tag(u32::MAX), None);

    assert_eq!(array.find(0u32), None);
    assert_eq!(array.find(1u32), Some(&b"asd"[..]));
    assert_eq!(array.find(2u32), Some(&b"zxcv"[..]));
    assert_eq!(array.find(3u32), None);
}

#[test]
fn test_decode_empty() {
    assert!(TLVArray::new(b"\0\0\0\0".into())
        .expect("should succeed")
        .is_empty());
}

#[should_panic(expected = "room for element count")]
#[test]
fn test_decode_short() {
    // A truncated input should fail though.
    TLVArray::new(b"123".into()).unwrap();
}

#[should_panic(expected = "room for whole header")]
#[test]
fn test_decode_truncated_header() {
    // 2 entries, only room for 1 offset and 1 tag.
    TLVArray::new(
        [2u32.to_le_bytes(), 0u32.to_le_bytes(), 1u32.to_le_bytes()]
            .concat()
            .into(),
    )
    .unwrap();
}

#[should_panic(expected = "Offsets must be non-decreasing")]
#[test]
fn test_decode_decreasing_offsets() {
    TLVArray::new(
        [
            3u32.to_le_bytes(),
            2u32.to_le_bytes(),
            1u32.to_le_bytes(),
            10u32.to_le_bytes(),
            11u32.to_le_bytes(),
            12u32.to_le_bytes(),
            u32::MAX.to_le_bytes(), // payload
        ]
        .concat()
        .into(),
    )
    .unwrap();
}

#[should_panic(expected = "Tags must be non-decreasing")]
#[test]
fn test_decode_decreasing_tags() {
    TLVArray::new(
        [
            3u32.to_le_bytes(),
            0u32.to_le_bytes(),
            0u32.to_le_bytes(),
            10u32.to_le_bytes(),
            13u32.to_le_bytes(),
            12u32.to_le_bytes(),
        ]
        .concat()
        .into(),
    )
    .unwrap();
}

// We can't tell when the last payload was cut short!
#[test]
fn test_decode_truncated_last_payload() {
    let arr = TLVArray::new(
        [
            2u32.to_le_bytes(),
            4u32.to_le_bytes(),
            10u32.to_le_bytes(),
            13u32.to_le_bytes(),
            u32::MAX.to_le_bytes(),
        ]
        .concat()
        .into(),
    )
    .expect("should decode");

    assert_eq!(arr.find(10), Some(&u32::MAX.to_le_bytes()[..]));
    assert_eq!(arr.find(13), Some(&[][..]));
}

// But we can tell when deeper payloads were truncated.
#[should_panic(expected = "room for values")]
#[test]
fn test_decode_truncated_payload() {
    TLVArray::new(
        [
            2u32.to_le_bytes(),
            4u32.to_le_bytes(),
            10u32.to_le_bytes(),
            13u32.to_le_bytes(),
            u32::MAX.to_le_bytes(),
        ]
        .concat()[..18]
            .into(),
    )
    .unwrap();
}
