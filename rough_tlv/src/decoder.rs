//! The decode module implements a zero-copy associative map for
//! Roughtime-style messages (arrays of TLVs sorted on the tag).
use std::borrow::Cow;

use crate::Tag;

/// A [`MessageView`] wraps a `Cow<[u8]>` with zero-copy accessors
/// for a Rough TLV message (tag-value pairs).  The constructor performs
/// linear-time validation (on the header); after that, each method
/// call runs in constant or logarithmic (wrt the number of pairs) time.
///
/// ```
/// # use rough_tlv::Tag;
/// # use rough_tlv::ToRoughTLV;
/// # use rough_tlv::MessageWrapper;
/// # use rough_tlv::MessageView;
/// # let mut sink = owning_iovec::OwningIovec::new();
/// #
/// # let mut entries = [(Tag::new(b"TEST"), &b"asd"[..]), (2.into(), &b"zxcv"[..])];
/// # MessageWrapper::new_from_slice(&mut entries)
/// #    .unwrap()
/// #    .to_rough_tlv(&mut sink);
/// #
/// # let encoded_bytes = sink.flatten().expect("must be complete");
/// let encoded_bytes: &[u8] = &encoded_bytes;
/// let msg = MessageView::new(encoded_bytes.into()).expect("should validate");
///
/// assert_eq!(msg.find(b"TEST"), Some(&b"asd"[..]));
/// assert_eq!(msg.find(Tag::new_from_u32(2)), Some(&b"zxcv"[..]));
/// ```
#[repr(transparent)]
pub struct MessageView<'a> {
    storage: Cow<'a, [u8]>,
}

impl<'src> crate::ToRoughTLV<'src> for MessageView<'src> {
    #[inline(always)]
    fn to_rough_tlv<'dst, Sink>(&self, sink: &mut Sink)
    where
        Sink: owning_iovec::ZeroCopySink<'dst> + ?Sized,
        'src: 'dst,
    {
        self.storage.to_rough_tlv(sink)
    }

    #[inline(always)]
    fn rough_tlv_len(&self) -> usize {
        self.storage.rough_tlv_len()
    }
}

#[inline(always)]
fn slice_as_tags(slice: &[u8]) -> &[Tag] {
    let size = slice.len() / 4;
    // This is safe because `Tag` is a transparent wrapper for `[u8; 4]`.
    unsafe { std::slice::from_raw_parts(slice.as_ptr().cast(), size) }
}

/// Failure reasons for decoding bytes as a Roughtime TLV message
/// via [`MessageView::new`].
#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
pub enum DecodingError {
    /// We need at least 4 bytes to encode the number of fields (`u32`),
    /// and got fewer than that.
    ImpossibleHeader(usize),
    /// We don't have enough bytes for the number of fields.
    TruncatedHeader((u32, usize)),
    /// Some offsets aren't in increasing order.
    NonMonotonicOffsets((usize, u32, u32)),
    /// Some tags aren't in increasing order.
    NonMonotonicTags((usize, u32, u32)),
    /// We don't have enough bytes for the payloads, given the offsets.
    TruncatedPayload((u64, usize)),
}

impl std::fmt::Display for DecodingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use DecodingError::*;
        match self {
            ImpossibleHeader(size) => write!(
                f,
                "Rough TLV message is too short to hold the field count. size={}",
                size
            ),
            TruncatedHeader((fields, size)) => write!(
                f,
                "Rough TLV message is too short for the number of fields. count={} size={}",
                fields, size
            ),
            NonMonotonicOffsets((index, first, second)) => write!(
                f,
                "Rough TLV message has out-of-order offsets. rank={} offset={} next={}",
                index, first, second
            ),
            NonMonotonicTags((index, first, second)) => write!(
                f,
                "Rough TLV message has out-of-order tags. rank={} tag={} next={}",
                index, first, second
            ),
            TruncatedPayload((minimum, actual)) => write!(
                f,
                "Rough TLV message is too short for the payload size. min={} actual={}",
                minimum, actual
            ),
        }
    }
}

impl std::error::Error for DecodingError {}

impl<'a> MessageView<'a> {
    /// Wraps the slices of bytes `data` into a constant-time decoding wrapper.
    pub fn new(data: Cow<'a, [u8]>) -> Result<Self, DecodingError> {
        if data.len() < 4 {
            return Err(DecodingError::ImpossibleHeader(data.len()));
        }

        let num_values = u32::from_le_bytes(data[0..4].try_into().unwrap()) as u64;

        // We need at least 4 * num_values for the tags, and 4 * num_values bytes
        // again for the value count + (n - 1) offsets.
        if 8 * num_values > data.len() as u64 {
            return Err(DecodingError::TruncatedHeader((
                num_values as u32,
                data.len(),
            )));
        }

        let ret = MessageView { storage: data };

        let nonmonotonic = |xs: &[Tag]| {
            for (idx, (left, right)) in xs.iter().zip(xs.iter().skip(1)).enumerate() {
                if left > right {
                    return Some((idx, left.value(), right.value()));
                }
            }

            None
        };

        if let Some(witness) = nonmonotonic(ret.offsets()) {
            return Err(DecodingError::NonMonotonicOffsets(witness));
        }

        if let Some(witness) = nonmonotonic(ret.tags()) {
            return Err(DecodingError::NonMonotonicTags(witness));
        }

        if let Some(last_offset) = ret.offsets().last() {
            // num_values and `last_offset` are `u32`, so `total` won't overflow.
            let total = (8 * num_values) + (last_offset.value() as u64);
            if total > ret.storage.len() as u64 {
                return Err(DecodingError::TruncatedPayload((total, ret.storage.len())));
            }
        }

        Ok(ret)
    }

    /// Returns a reference to the underlying `Cow<[u8]>`.
    #[inline(always)]
    pub fn inner(&self) -> &Cow<'a, [u8]> {
        &self.storage
    }

    /// Extracts the underlying `Cow<[u8]>`.
    #[inline(always)]
    pub fn into_inner(self) -> Cow<'a, [u8]> {
        self.storage
    }

    /// Returns an iterator for the tag-value pairs in the message.
    ///
    /// The tags are always sorted in non-decreasing order.
    pub fn iter(&self) -> impl std::iter::Iterator<Item = (Tag, &[u8])> {
        use std::iter::once;

        let header = 8 * self.len();

        // We already checked for >= header bytes in storage.
        let starts = once(0u32).chain(self.offsets().iter().map(Tag::value));
        let ends = self
            .offsets()
            .iter()
            .map(|x| x.value() as usize)
            .chain(once(self.storage.len() - header));
        let tags = self.tags().iter();

        tags.zip(starts.zip(ends)).map(move |(tag, (start, end))| {
            let start = header + start as usize;
            let end = header + end;

            (*tag, &self.storage[start..end])
        })
    }

    /// Returns the number of tag-value pairs in this `Message`.
    #[inline(always)]
    pub fn len(&self) -> usize {
        // `MessageView::new` already made sure `storage` is large enough
        u32::from_le_bytes(self.storage[0..4].try_into().unwrap()) as usize
    }

    /// Returns whether this `Message` contains 0 tag-value pairs.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the `index`th tag-value pair.
    pub fn get(&self, index: usize) -> Option<(Tag, &[u8])> {
        Some((*self.tags().get(index)?, self.get_value(index)?))
    }

    /// Returns the value associated with tag `wanted`, if any.
    #[inline(always)]
    pub fn find(&self, wanted: impl Into<Tag>) -> Option<&[u8]> {
        self.get_value(self.find_tag(wanted)?)
    }

    /// Returns the offsets of all but the first element, relative to the end of
    /// the offset and tags.
    ///
    /// The `Tag` in the return type is an internal abuse of the type system,
    /// since we just need a wrapper for little-endian u32 with std::cmp::Ord.
    #[inline(always)]
    fn offsets(&self) -> &[Tag] {
        // Start at byte 4, and we have num_values - 1 of these 4-byte values
        slice_as_tags(&self.storage[4..(4 * self.len()).max(4)])
    }

    /// Returns values' tags, in order.  Tags are always sorted in non-decreasing
    /// order.
    #[inline(always)]
    pub fn tags(&self) -> &[Tag] {
        slice_as_tags(&self.storage[4 * self.len()..8 * self.len()])
    }

    /// Returns whether the tags in this `Message` match `expected` exactly.
    #[inline(always)]
    pub fn tags_match_exactly(&self, expected: impl IntoIterator<Item = Tag>) -> bool {
        self.tags().iter().copied().eq(expected)
    }

    /// Returns the index of tag `wanted`, if any.
    #[inline(always)]
    pub fn find_tag(&self, wanted: impl Into<Tag>) -> Option<usize> {
        fn doit(this: &MessageView, wanted: Tag) -> Option<usize> {
            this.tags().binary_search(&wanted).ok()
        }

        doit(self, wanted.into())
    }

    /// Returns the value at `index`, if any.
    pub fn get_value(&self, index: usize) -> Option<&[u8]> {
        let header = 8 * self.len();

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
fn test_decode_miri() {
    use crate::ToRoughTLV;
    let mut sink = owning_iovec::OwningIovec::new();

    let mut entries = [(1u32.into(), &b"asd"[..]), (2u32.into(), &b"zxcv"[..])];
    crate::MessageWrapper::new_from_slice(&mut entries)
        .unwrap()
        .to_rough_tlv(&mut sink);

    let encoded_bytes = sink.flatten().expect("must be complete");

    let msg = MessageView::new((&encoded_bytes).into()).expect("should parse");

    assert_eq!(msg.inner(), &encoded_bytes);

    // Re-encode the view
    assert_eq!(msg.rough_tlv_len(), encoded_bytes.len());
    {
        let mut new_sink = owning_iovec::OwningIovec::new();
        msg.to_rough_tlv(&mut new_sink);

        let reencoded_bytes = new_sink.flatten().expect("must be complete");
        assert_eq!(reencoded_bytes, encoded_bytes);
    }

    assert!(msg.tags_match_exactly([Tag::new_from_u32(1), 2.into()]));
    assert!(!msg.tags_match_exactly([1.into(), 2.into(), 3.into()]));
    assert!(!msg.tags_match_exactly([1.into()]));

    eprintln!("{:?}", msg.iter().collect::<Vec<_>>());

    assert!(msg.iter().eq([
        (Tag::new_from_u32(1), &b"asd"[..]),
        (Tag::new_from_u32(2), &b"zxcv"[..])
    ]));

    assert_eq!(msg.len(), 2);
    assert!(!msg.is_empty());

    assert_eq!(msg.get(0), Some((Tag::new_from_u32(1u32), &b"asd"[..])));
    assert_eq!(msg.get(1), Some((2u32.into(), &b"zxcv"[..])));
    assert_eq!(msg.get(2), None);
    assert_eq!(msg.get(usize::MAX), None);

    assert_eq!(msg.get_value(0), Some(&b"asd"[..]));
    assert_eq!(msg.get_value(1), Some(&b"zxcv"[..]));
    assert_eq!(msg.get_value(2), None);
    assert_eq!(msg.get_value(3), None);
    assert_eq!(msg.get_value(usize::MAX), None);

    assert_eq!(msg.find_tag(Tag::new_from_u32(1)), Some(0));
    assert_eq!(msg.find_tag(2u32), Some(1));
    assert_eq!(msg.find_tag(0u32), None);
    assert_eq!(msg.find_tag(3u32), None);
    assert_eq!(msg.find_tag(u32::MAX), None);

    assert_eq!(msg.find(0u32), None);
    assert_eq!(msg.find(Tag::new_from_u32(1)), Some(&b"asd"[..]));
    assert_eq!(msg.find(2), Some(&b"zxcv"[..]));
    assert_eq!(msg.find(3), None);

    assert_eq!(&msg.into_inner(), &encoded_bytes);
}

#[test]
fn test_decode_empty_miri() {
    assert!(MessageView::new(b"\0\0\0\0".into())
        .expect("should succeed")
        .is_empty());
}

#[should_panic(expected = "ImpossibleHeader")]
#[test]
fn test_decode_short_miri() {
    // A truncated input should fail though.
    MessageView::new(b"123".into())
        .map_err(std::io::Error::other)
        .unwrap();
}

#[should_panic(expected = "TruncatedHeader")]
#[test]
fn test_decode_truncated_header_miri() {
    // 2 entries, only room for 1 offset and 1 tag.
    MessageView::new(
        [2u32.to_le_bytes(), 0u32.to_le_bytes(), 1u32.to_le_bytes()]
            .concat()
            .into(),
    )
    .map_err(std::io::Error::other)
    .unwrap();
}

#[should_panic(expected = "NonMonotonicOffsets")]
#[test]
fn test_decode_decreasing_offsets_miri() {
    MessageView::new(
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
    .map_err(std::io::Error::other)
    .unwrap();
}

#[should_panic(expected = "NonMonotonicTags")]
#[test]
fn test_decode_decreasing_tags_miri() {
    MessageView::new(
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
    .map_err(std::io::Error::other)
    .unwrap();
}

// We can't tell when the last payload was cut short!
#[test]
fn test_decode_truncated_last_payload_miri() {
    let msg = MessageView::new(
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

    assert_eq!(
        msg.find(Tag::new_from_u32(10)),
        Some(&u32::MAX.to_le_bytes()[..])
    );
    assert_eq!(msg.find(13u32), Some(&[][..]));
}

// But we can tell when deeper payloads were truncated.
#[test]
fn test_decode_truncated_payload_miri() {
    let data = [
        2u32.to_le_bytes(),
        4u32.to_le_bytes(),
        10u32.to_le_bytes(),
        13u32.to_le_bytes(),
        u32::MAX.to_le_bytes(),
    ]
    .concat();
    let bad = MessageView::new(data[..18].into()).map_err(std::io::Error::other);

    assert!(format!("{}", bad.err().unwrap())
        .contains("Rough TLV message is too short for the payload size"));
}
