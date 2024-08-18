//! Implementors of `ToRoughTLV` implement `to_rough_tlv`, which dumps
//! their contents to a [`ZeroCopySink`].
use std::borrow::Cow;

use crate::Tag;
use owning_iovec::ZeroCopySink;

/// Implementors of `ToRoughTLV<'life>` can encode their contents to
/// `sink`, where the lifetime `dst` of the `sink` it at most `life`.
pub trait ToRoughTLV<'life> {
    /// Dump the encoded contents of `self` to `sink`, as a value in a
    /// Roughtime-style message.  In most cases, that's simply dumping
    /// the bytes.  When `self` is actually a Roughtime-style message,
    /// the encoded message must be dumped.
    fn to_rough_tlv<'dst, Sink>(&self, sink: &mut Sink)
    where
        'life: 'dst,
        Sink: ZeroCopySink<'dst> + ?Sized;

    /// Returns the number of bytes needed to encode the element in
    /// Rough TLV format.  This must match the total number of bytes
    /// written into `sink` by `to_rough_tlv`.
    fn rough_tlv_len(&self) -> usize;
}

impl<'life, T> ToRoughTLV<'life> for &T
where
    T: ToRoughTLV<'life>,
{
    #[inline(always)]
    fn to_rough_tlv<'dst, Sink>(&self, sink: &mut Sink)
    where
        'life: 'dst,
        Sink: ZeroCopySink<'dst> + ?Sized,
    {
        ToRoughTLV::to_rough_tlv(*self, sink)
    }

    #[inline(always)]
    fn rough_tlv_len(&self) -> usize {
        ToRoughTLV::rough_tlv_len(*self)
    }
}

impl<'life> ToRoughTLV<'life> for &[u8] {
    #[inline(always)]
    fn to_rough_tlv<'dst, Sink>(&self, sink: &mut Sink)
    where
        'life: 'dst,
        Sink: ZeroCopySink<'dst> + ?Sized,
    {
        sink.append_copy(self);
    }

    #[inline(always)]
    fn rough_tlv_len(&self) -> usize {
        self.len()
    }
}

impl<'life> ToRoughTLV<'life> for &str {
    #[inline(always)]
    fn to_rough_tlv<'dst, Sink>(&self, sink: &mut Sink)
    where
        'life: 'dst,
        Sink: ZeroCopySink<'dst> + ?Sized,
    {
        sink.append_copy(self.as_bytes());
    }

    #[inline(always)]
    fn rough_tlv_len(&self) -> usize {
        self.as_bytes().len()
    }
}

impl<'src> ToRoughTLV<'src> for Cow<'src, [u8]> {
    #[inline(always)]
    fn to_rough_tlv<'dst, Sink>(&self, sink: &mut Sink)
    where
        'src: 'dst,
        Sink: ZeroCopySink<'dst> + ?Sized,
    {
        match self {
            Cow::Borrowed(value) => sink.append_borrow(value),
            Cow::Owned(value) => sink.append_copy(value),
        };
    }

    #[inline(always)]
    fn rough_tlv_len(&self) -> usize {
        self.len()
    }
}

impl<'src> ToRoughTLV<'src> for Cow<'src, str> {
    fn to_rough_tlv<'dst, Sink>(&self, sink: &mut Sink)
    where
        'src: 'dst,
        Sink: ZeroCopySink<'dst> + ?Sized,
    {
        match self {
            Cow::Borrowed(value) => sink.append_borrow(value.as_bytes()),
            Cow::Owned(value) => sink.append_copy(value.as_bytes()),
        };
    }

    fn rough_tlv_len(&self) -> usize {
        self.as_bytes().len()
    }
}

/// Like Cow, except we don't have `to_owned()`.
#[derive(Debug)]
enum Entries<'this, Value> {
    Owned(Vec<(Tag, Value)>),
    Borrowed(&'this [(Tag, Value)]),
}

/// [`MessageWrapper`] wraps a slice or vector of `(Tag, Value)`,
/// where the `Value`s are bytes or otherwise implement [`ToRoughTLV`]
/// (i.e., may be encoded as bytes in Rough TLV format), and ensures
/// that the wrappee may be encoded as a Rough TLV message with the
/// given tags and encoded values.
///
/// Once constructed, [`MessageWrapper`]s can be encoded as Rough TLV
/// since they implements the [`ToRoughTLV`] trait.
/// ```
/// # use rough_tlv::Tag;
/// # use rough_tlv::ToRoughTLV;
/// # use rough_tlv::MessageWrapper;
/// # use rough_tlv::MessageView;
///
/// let mut sink = owning_iovec::OwningIovec::new();
///
/// let mut entries = [(Tag::new_from_u32(1), &b"asd"[..]), (2.into(), &b"zxcv"[..])];
/// MessageWrapper::new_from_slice(&mut entries)
///    .unwrap()
///    .to_rough_tlv(&mut sink);
///
/// let encoded_bytes = sink.flatten().expect("must be complete");
/// let expected: &[&[u8]] = &[
///     &2u32.to_le_bytes(), // value count
///     &3u32.to_le_bytes(), // end of first value
///     &1u32.to_le_bytes(), // first tag
///     &2u32.to_le_bytes(), // second tag
///     b"asd",              // first value
///     b"zxcv",             // second value
/// ];
/// assert_eq!(encoded_bytes, expected.concat());
/// ```
#[derive(Debug)]
pub struct MessageWrapper<'a, 'this, Value>
where
    Value: ToRoughTLV<'a>,
{
    len: usize,
    entries: Entries<'this, Value>,
    value_marker: std::marker::PhantomData<&'a [u8]>,
}

/// Failure reasons for wrapping values as a Roughtime TLV message via
/// [`MessageWrapper::new`], [`MessageWrapper::new_from_sorted`], or
/// [`MessageWrapper::new_from_slice`].
#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
pub enum EncodingError {
    /// Some tags aren't in increasing order.
    NonMonotonicTags((usize, u32, u32)),
    /// Too many key-value pairs in the messages (more than [`i32::MAX`]).
    TooManyElements(usize),
    /// An individual value exceeds the maximum payload size of [`i32::MAX`].
    ValueTooLarge((u32, usize)),
    /// The header and values concatenated together exceed the maximum
    /// payload total size of [`i32::MAX`].
    TotalTooLarge((u32, usize)),
}

impl std::fmt::Display for EncodingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use EncodingError::*;
        match self {
            NonMonotonicTags((index, first, second)) => write!(
                f,
                "Pre-sorted Rough TLV message has out-of-order tags. rank={} tag={} next={}",
                index, first, second
            ),
            TooManyElements(count) => write!(
                f,
                "Too many elements to encode as Rough TLV. count={} max={}",
                count,
                i32::MAX
            ),
            ValueTooLarge((index, size)) => write!(
                f,
                "Individual value exceeds maximum byte size. index={} size={} max={}",
                index,
                size,
                i32::MAX
            ),
            TotalTooLarge((count, size)) => write!(
                f,
                "Header and concatenated values exceed maximum byte size. count={} size={} max={}",
                count,
                size,
                i32::MAX
            ),
        }
    }
}

impl std::error::Error for EncodingError {}

impl<'a, 'this, Value: ToRoughTLV<'a>> MessageWrapper<'a, 'this, Value> {
    /// Returns a [`MessageWrapper`] wrapper for the input elements,
    /// after sorting them in-place if necessary.
    pub fn new(mut elements: Vec<(Tag, Value)>) -> Result<Self, EncodingError> {
        elements.sort_by_key(|x| x.0);
        Ok(Self {
            len: Self::compute_len(&elements)?,
            entries: Entries::Owned(elements),
            value_marker: Default::default(),
        })
    }

    /// Returns a [`MessageWrapper`] wrapper for the input elements if
    /// they're already sorted, and an error otherwise
    pub fn new_from_sorted(elements: &'this [(Tag, Value)]) -> Result<Self, EncodingError> {
        for (idx, (cur, next)) in elements.iter().zip(elements.iter().skip(1)).enumerate() {
            if cur.0 > next.0 {
                return Err(EncodingError::NonMonotonicTags((
                    idx,
                    cur.0.value(),
                    next.0.value(),
                )));
            }
        }

        Ok(Self {
            len: Self::compute_len(elements)?,
            entries: Entries::Borrowed(elements),
            value_marker: Default::default(),
        })
    }

    /// Returns a [`MessageWrapper`] wrapper for the input elements,
    /// after sorting them in-place if necessary.
    pub fn new_from_slice(elements: &'this mut [(Tag, Value)]) -> Result<Self, EncodingError> {
        elements.sort_by_key(|x| x.0);
        Ok(Self {
            len: Self::compute_len(elements)?,
            entries: Entries::Borrowed(elements),
            value_marker: Default::default(),
        })
    }

    /// Writes the Rough TLV encoded contents of this [`MessageWrapper`]
    /// to `sink`.
    pub fn encode<'dst, Sink>(&self, sink: &mut Sink)
    where
        'a: 'dst,
        Sink: ZeroCopySink<'dst> + ?Sized,
    {
        let elements: &[(Tag, Value)] = match &self.entries {
            Entries::Owned(vec) => vec,
            Entries::Borrowed(slice) => slice,
        };

        // Write number of pairs (the constructors already checked len <= i32::MAX).
        assert!(elements.len() <= i32::MAX as usize);
        sink.append_copy(&(elements.len() as u32).to_le_bytes());

        // Write the cumulative offsets (except the first one, always 0)
        {
            let mut acc: Option<u32> = None;
            for encoded_len in elements.iter().map(|x| x.1.rough_tlv_len()) {
                assert!(encoded_len <= i32::MAX as usize);
                match acc {
                    None => acc = Some(encoded_len as u32),
                    Some(sum) => {
                        sink.append_copy(&sum.to_le_bytes());
                        let sum = sum.saturating_add(encoded_len as u32);
                        assert!(sum <= i32::MAX as u32);

                        acc = Some(sum)
                    }
                }
            }
        }

        // Write out the tags
        for (tag, _) in elements.iter() {
            sink.append_copy(&tag.bytes);
        }

        // Write out the values
        for (_, value) in elements.iter() {
            value.to_rough_tlv(sink)
        }
    }

    fn compute_len(elements: &[(Tag, Value)]) -> Result<usize, EncodingError> {
        let mut ret = 0usize;

        // Start with 4 bytes for the number of pairs.
        ret += 4;
        if elements.len() > i32::MAX as usize {
            return Err(EncodingError::TooManyElements(elements.len()));
        }

        // We'll use saturating arithmetic here because we usize::MAX is too big anyway.

        // n - 1 offsets
        ret = ret.saturating_add(elements.len().saturating_sub(1).saturating_mul(4));
        // n tags
        ret = ret.saturating_add(elements.len().saturating_mul(4));

        // Sum the total sizes
        {
            let mut values_total_size = 0usize;

            for (rank, encoded_len) in elements.iter().map(|x| x.1.rough_tlv_len()).enumerate() {
                if encoded_len > i32::MAX as usize {
                    return Err(EncodingError::ValueTooLarge((rank as u32, encoded_len)));
                }

                values_total_size = values_total_size.saturating_add(encoded_len);
            }

            ret = ret.saturating_add(values_total_size);
        }

        if ret > i32::MAX as usize {
            // This also handles saturation.
            Err(EncodingError::TotalTooLarge((elements.len() as u32, ret)))
        } else {
            Ok(ret)
        }
    }
}

impl<'src, 'this, Value> ToRoughTLV<'src> for MessageWrapper<'src, 'this, Value>
where
    Value: ToRoughTLV<'src>,
{
    fn rough_tlv_len(&self) -> usize {
        self.len
    }

    fn to_rough_tlv<'dst, Sink>(&self, sink: &mut Sink)
    where
        'src: 'dst,
        Sink: ZeroCopySink<'dst> + ?Sized,
    {
        self.encode(sink);
    }
}

#[test]
fn test_encode_miri() {
    let mut sink = owning_iovec::OwningIovec::new();

    let message = MessageWrapper::<&[u8]>::new(vec![
        (2u32.into(), &b"zxcv"[..]),
        (1u32.into(), &b"asd"[..]),
    ])
    .unwrap();

    message.to_rough_tlv(&mut sink);

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
    assert_eq!(encoded_bytes.len(), message.rough_tlv_len());
}

#[test]
fn test_encode_empty_miri() {
    let mut sink = owning_iovec::OwningIovec::new();

    let message = MessageWrapper::<&[u8]>::new(vec![]).unwrap();

    message.to_rough_tlv(&mut sink);

    let encoded_bytes = sink.flatten().expect("must be complete");
    assert_eq!(encoded_bytes, 0u32.to_le_bytes());
}

#[test]
fn test_encode_nested_miri() {
    let mut sink = owning_iovec::OwningIovec::new();

    let x = MessageWrapper::<&[u8]>::new(vec![
        (2u32.into(), &b"zxcv"[..]),
        (1u32.into(), &b"asd"[..]),
    ])
    .unwrap();
    let wrapper = MessageWrapper::new(vec![(128u32.into(), &x)]).unwrap();

    wrapper.to_rough_tlv(&mut sink);

    let encoded_bytes = sink.flatten().expect("must be complete");
    let inner_expected: &[&[u8]] = &[
        &2u32.to_le_bytes(), // value count
        &3u32.to_le_bytes(), // end of first value
        &1u32.to_le_bytes(), // first tag
        &2u32.to_le_bytes(), // second tag
        b"asd",              // first value
        b"zxcv",             // second value
    ];

    let inner_encoded = inner_expected.concat();

    let expected: &[&[u8]] = &[
        &1u32.to_le_bytes(),   // value count
        &128u32.to_le_bytes(), // tag
        &inner_encoded[..],    // payload
    ];
    assert_eq!(encoded_bytes, expected.concat());
}

#[test]
fn test_encode_string_miri() {
    let mut sink = owning_iovec::OwningIovec::new();

    let mut entries = [(2u32.into(), "zxcv"), (1u32.into(), "asd")];
    MessageWrapper::<&str>::new_from_slice(&mut entries)
        .unwrap()
        .to_rough_tlv(&mut sink);

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

#[should_panic(expected = "NonMonotonicTags")]
#[test]
fn test_sorted_tag_unsorted_miri() {
    let payload = [
        (2u32.into(), b"asd".into()),
        (1u32.into(), b"zxcv".to_vec().into()),
    ];

    MessageWrapper::<Cow<[u8]>>::new_from_sorted(&payload).unwrap();
}

#[test]
fn test_encode_cow_miri() {
    let mut sink = owning_iovec::OwningIovec::new();

    let entries = [
        (1u32.into(), b"asd".into()),
        (2u32.into(), b"zxcv".to_vec().into()),
    ];
    MessageWrapper::<Cow<[u8]>>::new_from_sorted(&entries)
        .expect("is sorted")
        .to_rough_tlv(&mut sink);

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
fn test_encode_cow_string_miri() {
    let mut sink = owning_iovec::OwningIovec::new();

    let entries = [
        (1u32.into(), "asd".into()),
        (2u32.into(), "zxcv".to_string().into()),
        (10u32.into(), "123".to_string().into()),
    ];
    MessageWrapper::<Cow<str>>::new_from_sorted(&entries)
        .expect("is sorted")
        .to_rough_tlv(&mut sink);

    let encoded_bytes = sink.flatten().expect("must be complete");
    let expected: &[&[u8]] = &[
        &3u32.to_le_bytes(),  // value count
        &3u32.to_le_bytes(),  // end of first value
        &7u32.to_le_bytes(),  // end of second value
        &1u32.to_le_bytes(),  // first tag
        &2u32.to_le_bytes(),  // second tag
        &10u32.to_le_bytes(), // third tag
        b"asd",               // first value
        b"zxcv",              // second value
        b"123",               // third value
    ];
    assert_eq!(encoded_bytes, expected.concat());
}

#[test]
fn test_encode_nested_out_of_bounds_miri() {
    // 32 bytes
    let x0 = MessageWrapper::<&[u8]>::new(vec![
        (2u32.into(), &b"zxcvbnm,"[..]),
        (1u32.into(), &b"asdfghjk"[..]),
    ])
    .unwrap();

    //let x0 : & dyn ToRoughTLV<'static> = &x0;
    // ~ 2^7 bytes
    let x1 = MessageWrapper::new(vec![
        (1u32.into(), &x0),
        (2u32.into(), &x0),
        (3u32.into(), &x0),
        (4u32.into(), &x0),
        (5u32.into(), &x0),
        (6u32.into(), &x0),
        (7u32.into(), &x0),
        (8u32.into(), &x0),
    ])
    .unwrap();
    // 2^ 10 bytes
    let x2 = MessageWrapper::new(vec![
        (1u32.into(), &x1),
        (2u32.into(), &x1),
        (3u32.into(), &x1),
        (4u32.into(), &x1),
        (5u32.into(), &x1),
        (6u32.into(), &x1),
        (7u32.into(), &x1),
        (8u32.into(), &x1),
    ])
    .unwrap();
    // 2^13 bytes
    let x3 = MessageWrapper::new(vec![
        (1u32.into(), &x2),
        (2u32.into(), &x2),
        (3u32.into(), &x2),
        (4u32.into(), &x2),
        (5u32.into(), &x2),
        (6u32.into(), &x2),
        (7u32.into(), &x2),
        (8u32.into(), &x2),
    ])
    .unwrap();

    // 2^16 bytes
    let x4 = MessageWrapper::new(vec![
        (1u32.into(), &x3),
        (2u32.into(), &x3),
        (3u32.into(), &x3),
        (4u32.into(), &x3),
        (5u32.into(), &x3),
        (6u32.into(), &x3),
        (7u32.into(), &x3),
        (8u32.into(), &x3),
    ])
    .unwrap();
    // 2^19 bytes
    let x5 = MessageWrapper::new(vec![
        (1u32.into(), &x4),
        (2u32.into(), &x4),
        (3u32.into(), &x4),
        (4u32.into(), &x4),
        (5u32.into(), &x4),
        (6u32.into(), &x4),
        (7u32.into(), &x4),
        (8u32.into(), &x4),
    ])
    .unwrap();

    // 2^22 bytes
    let x6 = MessageWrapper::new(vec![
        (1u32.into(), &x5),
        (2u32.into(), &x5),
        (3u32.into(), &x5),
        (4u32.into(), &x5),
        (5u32.into(), &x5),
        (6u32.into(), &x5),
        (7u32.into(), &x5),
        (8u32.into(), &x5),
    ])
    .unwrap();

    // 2^25 bytes
    let x7 = MessageWrapper::new(vec![
        (1u32.into(), &x6),
        (2u32.into(), &x6),
        (3u32.into(), &x6),
        (4u32.into(), &x6),
        (5u32.into(), &x6),
        (6u32.into(), &x6),
        (7u32.into(), &x6),
        (8u32.into(), &x6),
    ])
    .unwrap();

    // 2^28 bytes
    let x8 = MessageWrapper::new(vec![
        (1u32.into(), &x7),
        (2u32.into(), &x7),
        (3u32.into(), &x7),
        (4u32.into(), &x7),
        (5u32.into(), &x7),
        (6u32.into(), &x7),
        (7u32.into(), &x7),
        (8u32.into(), &x7),
    ])
    .unwrap();

    assert_eq!(x8.rough_tlv_len(), 690262592);
    let bad = MessageWrapper::new(vec![
        (1u32.into(), &x8),
        (2u32.into(), &x8),
        (3u32.into(), &x8),
        (4u32.into(), &x8),
    ]);
    assert!(bad.is_err());

    let err = bad.err().unwrap();
    assert!(format!("{}", err).contains("concatenated values exceed maximum byte size"));

    let ok = MessageWrapper::new(vec![
        (1u32.into(), &x8),
        (2u32.into(), &x8),
        (3u32.into(), &x8),
    ]);
    assert!(ok.is_ok());
    assert_eq!(ok.unwrap().rough_tlv_len(), 2070787800);
}

#[test]
fn test_error_display_miri() {
    assert!(
        format!("{}", EncodingError::NonMonotonicTags((1, 3, 2))).contains("has out-of-order tags")
    );
    assert!(format!("{}", EncodingError::TooManyElements(11)).contains("Too many elements"));
    assert!(format!("{}", EncodingError::ValueTooLarge((1, 20)))
        .contains("value exceeds maximum byte size"));
    assert!(format!("{}", EncodingError::TotalTooLarge((10, 20)))
        .contains("concatenated values exceed maximum byte size"));
}
