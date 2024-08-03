//! The `owning_iovec` crate exposes an [`OwningIovec`] object that
//! supports on-the-fly production and consumption of bytes (i.e.,
//! like an in-memory pipe), along with supporting machinery.  Unlike
//! classical pipes or buffers, the [`OwningIovec`] works in terms
//! of slices, some of which may be borrowed without a byte copy.
//!
//! An [`OwningIovec`] may also own slices; the allocations that back
//! owned slices are tracked internally and released as the slices are
//! consumed.
//!
//! For producers, the [`OwningIovec`] also supports backreferences:
//! rather than each producer having to implement its own buffering,
//! producers may now pre-allocate mutable slices, and backfill them
//! after the fact.  On-the-fly consumption will be blocked from
//! consuming slices while the backpatch is still pending.
//!
//! Consumers get *asymptotic* on-the-fly consumption: there is no
//! guarantee that consumers can read a steady flow of bytes, even
//! when their producer generates bytes.  The guarantee is rather that
//! the amount of bytes buffered but not yet consumable in an
//! `[OwningIovec`] is bounded, as a constant multiple of the largest
//! slices lent to the [`OwningIovec`].
//!
//! Producers work with [`OwningIovec`], [`Backref`], and
//! [`AnchoredSlice`] (produced by [`ByteArena`]).
//!
//! Consumers handle [`ConsumingIovec`] or, if they must know that the
//! producer does not have any backreference in flight, [`StableIovec`].
mod byte_arena;
mod global_deque;
mod implementation;
mod ioslice;

pub use byte_arena::AnchoredSlice;
pub use byte_arena::ByteArena;
pub use implementation::Backref;
pub use implementation::ConsumingIovec;
pub use implementation::OwningIovec;
pub use implementation::StableIovec;

impl std::io::Read for ConsumingIovec<'_> {
    fn read(&mut self, mut dst: &mut [u8]) -> std::io::Result<usize> {
        let mut written = 0;
        while !dst.is_empty() {
            let Some(slice) = self.front() else {
                break;
            };

            let to_write = slice.len().min(dst.len());
            dst[..to_write].copy_from_slice(&slice[..to_write]);
            self.advance_slices(to_write);
            written += to_write;
            dst = &mut dst[to_write..];
        }

        Ok(written)
    }
}

/// A zero-copy sink can accept a byte slice and copy it to `self`,
/// or accept a slice with lifetime `'a` and borrow it into `self`.
pub trait ZeroCopySink<'a> {
    /// Appends a copy of `bytes` to the sink.
    fn append_copy(&mut self, bytes: &[u8]);

    /// Appends `bytes` to the `sink`; may (or may not) borrow `bytes`
    /// instead of copying it.
    fn append_borrow(&mut self, bytes: &'a [u8]);
}

impl<'wide, 'narrow, T> ZeroCopySink<'wide> for &mut T
where
    T: ZeroCopySink<'narrow>,
    'wide: 'narrow,
{
    fn append_copy(&mut self, bytes: &[u8]) {
        ZeroCopySink::<'narrow>::append_copy(*self, bytes);
    }

    fn append_borrow(&mut self, bytes: &'wide [u8]) {
        ZeroCopySink::<'narrow>::append_borrow(*self, bytes);
    }
}

impl<'a> ZeroCopySink<'a> for OwningIovec<'a> {
    fn append_copy(&mut self, bytes: &[u8]) {
        self.push_copy(bytes);
    }

    fn append_borrow(&mut self, bytes: &'a [u8]) {
        self.push(bytes);
    }
}

#[test]
fn test_read_miri() {
    use std::io::Read;

    let mut iovec = OwningIovec::new();
    iovec.push_copy(b"123");
    iovec.push(b"456");

    let mut dst = Vec::new();
    iovec
        .consumer()
        .read_to_end(&mut dst)
        .expect("should succeed");
    assert_eq!(dst, b"123456");
}

#[test]
fn test_read_short_miri() {
    use std::io::Read;

    let mut iovec = OwningIovec::new();
    iovec.push_copy(b"123");
    iovec.push(b"456");

    let mut dst = [0u8; 4];
    assert_eq!(iovec.consumer().read(&mut dst).expect("should succeed"), 4);
    assert_eq!(&dst, b"1234");
}

#[test]
fn test_append_miri() {
    let mut iovec = OwningIovec::new();

    {
        fn append_static(dst: &mut dyn ZeroCopySink<'static>) {
            dst.append_copy(b"123");
            dst.append_borrow(b"");
            dst.append_borrow(b"456");
            dst.append_copy(b"");
        }

        fn append_dyn<'a>(mut dst: &mut impl ZeroCopySink<'a>) {
            append_static(&mut dst);
        }

        append_dyn(&mut iovec);
    }

    assert_eq!(iovec.flatten().expect("no backref"), b"123456");
}
