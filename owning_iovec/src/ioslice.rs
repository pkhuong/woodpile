//! Use nix to manipulate [`IoSlice`]s without converting back to
//! regular slices: the conversion to slices introduces stacked borrow
//! constraints.
#[cfg(unix)]
mod unix {
    use std::io::IoSlice;

    #[must_use]
    #[inline]
    pub fn make_ioslice(base: *mut u8, len: usize) -> IoSlice<'static> {
        let ret = libc::iovec {
            iov_base: base as *mut _,
            iov_len: len,
        };

        unsafe { std::mem::transmute(ret) }
    }

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

    #[must_use]
    #[inline]
    pub fn ioslice_components(slice: IoSlice<'_>) -> (*mut u8, usize) {
        let ret: WSABuf = unsafe { std::mem::transmute(slice) };

        (ret.buf, ret.len as usize)
    }
}

#[cfg(windows)]
pub use windows::{ioslice_components, make_ioslice};
