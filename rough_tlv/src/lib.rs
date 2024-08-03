//! Rough TLV implements a producer and a zero-copy reader for a
//! relaxation of the tagged message format defined in the
//! [Roughtime draft](https://www.ietf.org/archive/id/draft-ietf-ntp-roughtime-11.html#name-message-format).
//!
//! A Rough TLV message is a container of tag-value pairs, where the
//! tags are unsigned 32-bit integers, and the values are opaque byte
//! strings.  Tags must appear in ascending order, so it's not quite a
//! sequence of pairs, but tags may appear multiple times (for now),
//! so it's also not quite a dictionary.  A multidict, maybe.
//!
//! There are two deliberate differences between the format
//! implemented by the Rough TLV library and the one described in the
//! [Roughtime draft](https://www.ietf.org/archive/id/draft-ietf-ntp-roughtime-11.html#name-message-format):
//! Rough TLV allows arbitrary 32-bit integers as tags, instead of
//! requiring that tags correspond to NUL-padded ASCII upper case
//! strings (i.e., `[A-Z]{0,4}`), and Rough TLV currently allows
//! repeated tags (but does not expose them particularly
//! usefully). When parsing untrusted input, it probably makes more
//! sense to confirm that the array of tags matches one of a few known
//! patterns, rather than enforcing structural rules.
//!
//! One last implementation difference is that the Rough TLV *encoder*
//! handles at most `i32::MAX` tag-value pairs and at most `i32::MAX`
//! total bytes for each message.  The decoder is expected to
//! correctly use unsigned arithmetic, but Rough TLV targets
//! relatively short messages, so we prefer to steer clear of boundary
//! conditions.
//!
//! The encoding packs all metadata for a message in a header section
//! that only contains little-endian 32-bit unsigned integers,
//! followed by the values' bytes concatenated in order, as
//! illustrated by Figure 1 of
//! <https://www.ietf.org/archive/id/draft-ietf-ntp-roughtime-11.html#section-5-1>:
//!
//! ```text
//! 0                   1                   2                   3
//!  0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
//! +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//! |                   Number of pairs (uint32)                    |
//! +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//! |                                                               |
//! .                                                               .
//! .                     N-1 offsets (uint32)                      .
//! .                                                               .
//! |                                                               |
//! +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//! |                                                               |
//! .                                                               .
//! .                        N tags (uint32)                        .
//! .                                                               .
//! |                                                               |
//! +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//! |                                                               |
//! .                                                               .
//! .                            Values                             .
//! .                                                               .
//! |                                                               |
//! +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//! ```
//!
//! In other words, an encoded Rough TLV message always starts with
//! the number of tag-value pairs, `N`, as a little-endian `u32`.
//!
//! That pair count is followed by `N - 1` (rather, `max(0, N - 1)`)
//! offsets for the first byte of each value in the `Values` footer.
//! The first offset is elided because it's always 0.  Equivalently,
//! we have the running sum of value sizes (in bytes) for the first to
//! second-to-last value.  Each offset (partial sum) is again a
//! little-endian `u32`.
//!
//! Finally, we have the array of `N` tag values, as little-endian
//! `u32`.  The tags must be sorted in ascending (non-descending)
//! order.  This lets us efficiently search the array of tag values
//! without constructing an index.
//!
//! After this header of `2N` little-endian `u32`s, we simply find the
//! values concatenated in the same order as the tags.
//!
//! Importantly for larger payloads, the size of the *last* value
//! doesn't appear anywhere in the encoding: the last value implicitly
//! goes from the end of the second-to-last value to the end of the
//! message.  This can be useful for (semi-)streaming producers, like
//! Roughtime clients that must pad their requests to let the protocol
//! prevent UDP-based amplification.
mod decoder;
mod encoder;

pub use decoder::DecodingError;
pub use decoder::MessageView;

pub use encoder::EncodingError;
pub use encoder::MessageWrapper;
pub use encoder::ToRoughTLV;

/// A Rough TLV [`Tag`] is an array of 4 bytes, interpreted as a
/// little endian [`u32`].  A tag may be constructed from its [`u32`]
/// value, or from an array of 4 bytes.
///
/// There is also a bidirectional From/Into conversion between [`Tag`]
/// and [`u32`], for convenience.
///
/// [`Tag`]s implement [`std::cmp::Ord`] by comparing the *little endian*
/// values.
///
/// ```
/// # use rough_tlv::Tag;
/// // Test a few values from the roughtime draft
/// assert_eq!(Tag::new(b"ROOT").value(), 0x544f4f52);
/// assert_eq!(Tag::new(b"SIG\0").value(), 0x00474953);
/// assert_eq!(Tag::new(b"ZZZZ"), 0x5a5a5a5a.into());
/// ```
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct Tag {
    /// Little-endian representation of the 32-bit tag
    pub bytes: [u8; 4],
}

impl Tag {
    /// Returns a [`Tag`] with `bytes` as the encoded 32-bit tag
    pub fn new(bytes: &[u8; 4]) -> Self {
        Self { bytes: *bytes }
    }

    /// Returns a [`Tag`] with `value` as the 32-bit tag
    pub fn new_from_u32(value: u32) -> Self {
        value.into()
    }

    /// Returns the little-endian value encoded in the 4 bytes.
    pub fn value(&self) -> u32 {
        u32::from_le_bytes(self.bytes)
    }
}

impl std::convert::From<&u32> for Tag {
    fn from(value: &u32) -> Tag {
        (*value).into()
    }
}

impl std::convert::From<u32> for Tag {
    fn from(value: u32) -> Tag {
        Tag {
            bytes: value.to_le_bytes(),
        }
    }
}

impl std::convert::From<&Tag> for u32 {
    fn from(value: &Tag) -> u32 {
        (*value).into()
    }
}

impl std::convert::From<Tag> for u32 {
    fn from(value: Tag) -> u32 {
        value.value()
    }
}

impl std::cmp::PartialOrd for Tag {
    fn partial_cmp(&self, other: &Tag) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl std::cmp::Ord for Tag {
    fn cmp(&self, other: &Tag) -> std::cmp::Ordering {
        self.value().cmp(&other.value())
    }
}

#[test]
fn test_conversion_miri() {
    let x: Tag = 1u32.into();
    let y: Tag = (&1u32).into();

    assert_eq!(x, y);

    let value_x: u32 = x.into();
    let value_y: u32 = (&y).into();

    assert_eq!(value_x, 1);
    assert_eq!(value_y, 1);
}

#[test]
fn test_from_tag_miri() {
    for i in 0..1000u32 {
        let cur = Tag {
            bytes: i.to_le_bytes(),
        };
        let roundtrip: u32 = (&cur).into();
        assert_eq!(i, roundtrip);

        let next = Tag {
            bytes: (i + 1).to_le_bytes(),
        };
        assert_eq!(cur.cmp(&next), std::cmp::Ordering::Less);
    }
}

#[test]
fn test_comparison_miri() {
    let x: Tag = 3u32.into();
    let y: Tag = 100000002u32.into();

    assert_ne!(x, y);
    assert!(x < y);
    assert!(x <= y);
    assert!(y > x);
    assert!(y >= x);
}

#[test]
fn test_ascii_miri() {
    // A couple tags from the roughtime draft
    assert_eq!(Tag::new(b"SIG\0"), Tag::new_from_u32(0x00474953));
    assert_eq!(Tag::new(b"ROOT"), Tag::new_from_u32(0x544f4f52));
    assert_eq!(Tag::new(b"ZZZZ"), Tag::new_from_u32(0x5a5a5a5a));
}
