//! Use the backing foreign type to manipulate [`IoSlice`]s without converting
//! back to regular slices: the conversion to slices introduces stacked borrow
//! constraints.
#[cfg(unix)]
mod unix {
    use std::io::IoSlice;

    const _: () =
        assert!(std::mem::size_of::<libc::iovec>() == std::mem::size_of::<IoSlice<'static>>());

    /// Creates an `IoSlice<'static>` from a raw pointer and length.
    ///
    /// # Safety
    ///
    /// The `'static` lifetime is a lie; the caller must ensure that the
    /// memory region pointed to by `base` with length `len` is valid for the
    /// lifetime of the returned `IoSlice`.
    #[must_use]
    #[inline]
    pub fn make_ioslice(base: *mut u8, len: usize) -> IoSlice<'static> {
        let ret = libc::iovec {
            iov_base: base as *mut _,
            iov_len: len,
        };

        unsafe { std::mem::transmute(ret) }
    }

    /// Returns the base pointer and length of the given `IoSlice<'_>`.
    #[must_use]
    #[inline]
    pub fn ioslice_components(slice: IoSlice<'_>) -> (*mut u8, usize) {
        let ret: libc::iovec = unsafe { std::mem::transmute(slice) };

        (ret.iov_base as *mut u8, ret.iov_len)
    }
}

#[cfg(unix)]
pub use unix::{ioslice_components, make_ioslice};

#[allow(unused)]
mod windows {
    use std::io::IoSlice;

    // https://learn.microsoft.com/en-us/windows/win32/api/ws2def/ns-ws2def-wsabuf
    //
    // typedef struct _WSABUF {
    //   ULONG len;
    //   CHAR  *buf;
    // } WSABUF, *LPWSABUF;
    struct WSABuf {
        len: u32, // Windows is LLP64, so ULONG is 32 bits.
        buf: *mut u8,
    }

    const _: () = assert!(std::mem::size_of::<WSABuf>() == std::mem::size_of::<IoSlice<'static>>());

    /// Creates an `IoSlice<'static>` from a raw pointer and length.
    ///
    /// # Safety
    ///
    /// The `'static` lifetime is a lie; the caller must ensure that the
    /// memory region pointed to by `base` with length `len` is valid for the
    /// lifetime of the returned `IoSlice`.
    #[must_use]
    #[inline]
    pub fn make_ioslice(base: *mut u8, len: usize) -> IoSlice<'static> {
        let ret = WSABuf {
            len: len
                .try_into()
                .expect("ioslice must not exceed 4 GB on windows"),
            buf: base,
        };

        unsafe { std::mem::transmute(ret) }
    }

    /// Returns the base pointer and length of the given `IoSlice<'_>`.
    #[must_use]
    #[inline]
    pub fn ioslice_components(slice: IoSlice<'_>) -> (*mut u8, usize) {
        let ret: WSABuf = unsafe { std::mem::transmute(slice) };

        (ret.buf, ret.len as usize)
    }
}

#[cfg(windows)]
pub use windows::{ioslice_components, make_ioslice};

#[test]
fn test_roundtrip_miri() {
    use std::io::IoSlice;

    let data = vec![1, 2, 3];
    let slice = IoSlice::new(&data);

    let (base, len) = ioslice_components(slice);
    assert_eq!(base as *const u8, data.as_ptr_range().start);
    assert_eq!(len, data.len());

    let new_slice = make_ioslice(base, len);
    assert_eq!(&*slice, &*new_slice);
    assert_eq!(slice.as_ptr(), new_slice.as_ptr());
    assert_eq!(slice.len(), new_slice.len());

    assert_eq!(ioslice_components(slice), ioslice_components(new_slice))
}
