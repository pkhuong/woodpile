//! The `trivial_zip_wrapper` crate wraps uncompressed ("`STORE`d")
//! files in ZIP-compatible metadata.  The one incompatibility is
//! that, in order to enable in-kernel copies, the CRC field is left
//! zeroed-out.
pub mod headers;

use std::io::Result;

/// A `ZipWrapperWriter` emits trivial STORED data in a Zip container.
///
/// The implementation avoids reading the source data (doesn't even
/// compute a CRC) to enable in-kernel copies.
#[derive(Debug)]
pub struct ZipWrapperWriter<F>
where
    F: std::io::Write + std::fmt::Debug,
{
    // One entry for each written file, with the name as the first
    // value, followed by the offset *of the local file header*
    // and the size *of the file*.
    contents: Vec<(String, u64, u64)>,
    written_so_far: u64,
    // All writes to `destination` must update `written_so_far`.
    destination: F,
}

impl<F> ZipWrapperWriter<F>
where
    F: std::io::Write + std::fmt::Debug,
{
    /// Creates a new `ZipWrapperWriter` that appends to `destination`.
    pub fn new(destination: F, initial_offset: u64) -> Self {
        Self {
            contents: Vec::new(),
            written_so_far: initial_offset,
            destination,
        }
    }

    /// Adds an entry for file `name` with `size` bytes from `payload` as the contents.
    pub fn copy_file(
        &mut self,
        name: String,
        payload: impl std::io::Read,
        size: u64,
    ) -> Result<()> {
        self.copy_file_impl(
            headers::construct_local_file_header(&name, size),
            name,
            payload,
            size,
        )
    }

    fn copy_file_impl(
        &mut self,
        header: Vec<u8>,
        name: String,
        payload: impl std::io::Read,
        size: u64,
    ) -> Result<()> {
        let offset = self.written_so_far;
        self.destination.write_all(&header)?;
        self.written_so_far += header.len() as u64;

        let copied = std::io::copy(&mut payload.take(size), &mut self.destination)?;
        self.written_so_far += copied;
        if copied != size {
            return Err(std::io::Error::new(
                std::io::ErrorKind::UnexpectedEof,
                "Short ZipWrapperWriter::copy_file",
            ));
        }

        self.contents.push((name, offset, size));
        Ok(())
    }

    /// Terminates the zip file and returns the output file on success.
    pub fn finish(mut self) -> Result<F> {
        // Reserve at least 80 bytes per file, and 100 bytes for the locators.
        let mut dst: Vec<u8> =
            Vec::with_capacity(self.contents.len().saturating_mul(80).saturating_add(100));

        for (name, offset, size) in self.contents.iter() {
            dst = headers::construct_central_directory_header(name, *offset, *size, dst);
        }

        let directory_size = dst.len() as u64;
        dst = headers::construct_central_directory_locator(
            self.contents.len(),
            self.written_so_far,
            directory_size,
            None,
            dst,
        );

        self.destination.write_all(&dst)?;
        Ok(self.destination)
    }
}

fn compute_padding(
    written_so_far: u64,
    header_size: usize,
    payload_alignment: u32,
    max_padding: u32,
) -> u32 {
    let payload_alignment = payload_alignment.max(1); // avoid division by 0

    let current_destination = written_so_far + header_size as u64;
    let current_misalignment = (current_destination % (payload_alignment as u64)) as u32;

    let mut padding = (payload_alignment - current_misalignment) % payload_alignment;

    while padding > max_padding {
        // Zero out the top bit to shrink `padding` while maximally preserving
        // zeroed out low bits in `written_so_far + header_size + padding`.
        padding -= 1u32 << padding.ilog2();
    }

    padding
}

impl<F> ZipWrapperWriter<F>
where
    F: std::io::Write + std::io::Seek + std::fmt::Debug,
{
    /// Like [`Self::copy_file`], except the payload is aligned to
    /// `payload_alignment`, or as close as possible without exceeding
    /// `max_padding`.
    ///
    /// The `payload_alignment` should be a power of 2, but other
    /// values will not crash.
    ///
    /// The padding will inserted before the zip local header, so the
    /// output is still a valid Zip file.
    pub fn copy_file_aligned(
        &mut self,
        name: String,
        payload: impl std::io::Read,
        size: u64,
        payload_alignment: u32,
        max_padding: u32,
    ) -> Result<()> {
        let header = headers::construct_local_file_header(&name, size);

        let padding = compute_padding(
            self.written_so_far,
            header.len(),
            payload_alignment,
            max_padding,
        );
        if padding > 0 {
            self.destination
                .seek(std::io::SeekFrom::Current(padding as i64))?;
            self.written_so_far += padding as u64;
        }

        self.copy_file_impl(header, name, payload, size)
    }
}

#[test]
fn test_compute_padding() {
    let header_size = 63usize;

    for current_offset in 0..1000 {
        for lg_alignment in 0..8 {
            for max_padding in 0..300 {
                let alignment = 1u32 << lg_alignment;
                let padding = compute_padding(current_offset, header_size, alignment, max_padding);
                assert!(padding <= max_padding);

                // If we didn't pad
                let baseline_position = current_offset + header_size as u64;
                let next = baseline_position.next_multiple_of(alignment as u64);
                if next - baseline_position <= max_padding as u64 || alignment <= max_padding {
                    // We'll start the payload write at current_offset + padding + header_size;
                    // that should be aligned!
                    assert_eq!(
                        (current_offset + padding as u64 + header_size as u64) % alignment as u64,
                        0
                    );
                }

                // Don't make things worse.
                let padded_position = baseline_position + padding as u64;
                assert!(padded_position.trailing_zeros() >= baseline_position.trailing_zeros());
                if padding > 0 {
                    assert!(padded_position.trailing_zeros() > baseline_position.trailing_zeros());
                }
            }
        }
    }
}

#[test]
fn test_zipper_wrapper_trivial() {
    let mut writer = ZipWrapperWriter::new(Vec::new(), 0);

    // Replicate https://blog.yaakov.online/zip64-go-big-or-go-home/

    writer
        .copy_file("README.txt".to_owned(), &b"Hello, World!"[..], 13)
        .expect("should work");

    let output = writer.finish().expect("should succeed");
    let expected: Vec<&[u8]> = vec![
        b"PK\x03\x04",       // signature
        b"\x2d\x00",         // version
        b"\x00\x00",         // flags
        b"\x00\x00",         // STORED
        b"\x00\x00",         // Time
        b"\x00\x00",         // Date
        b"\x00\x00\x00\x00", // CRC [ DUMMY ]
        b"\xFF\xFF\xFF\xFF", // dummy size
        b"\xFF\xFF\xFF\xFF", // dummy size
        b"\x0a\x00",         // 10 chars (README.txt)
        b"\x14\x00",         // 20 bytes for extra zip64 data
        b"README.txt",       // Filename
        b"\x01\x00",         // Zip64 tag
        b"\x10\x00",         // 16 bytes of zip64 data
        b"\x0d\x00\x00\x00", // 13 bytes of data
        b"\x00\x00\x00\x00",
        b"\x0d\x00\x00\x00", // 13 bytes of data
        b"\x00\x00\x00\x00",
        b"Hello, World!",    // Data
        b"PK\x01\x02",       // Directory record signature
        b"\x2d\x00",         // Version
        b"\x2d\x00",         // Version
        b"\x00\x00",         // Flags
        b"\x00\x00",         // STORED
        b"\x00\x00",         // Time
        b"\x00\x00",         // Date,
        b"\x00\x00\x00\x00", // CRC [ DUMMY ]
        b"\xFF\xFF\xFF\xFF", // dummy size
        b"\xFF\xFF\xFF\xFF", // dummy size
        b"\x0a\x00",         // 10-char name
        b"\x1c\x00",         // 28 extra bytes for zip64
        b"\x00\x00",         // 0 comment bytes
        b"\x00\x00",         // disk number
        b"\x00\x00",         // internal attributes
        b"\x00\x00\x00\x00", // external attributes
        b"\xff\xff\xff\xff", // dummy offset
        b"README.txt",       // filename
        b"\x01\x00",         // Zip64 tag
        b"\x18\x00",         // size of zip64 data
        b"\x0d\x00\x00\x00", // 13 bytes of data
        b"\x00\x00\x00\x00",
        b"\x0d\x00\x00\x00", // 13 bytes of data
        b"\x00\x00\x00\x00",
        b"\x00\x00\x00\x00", // Header offfset
        b"\x00\x00\x00\x00",
        b"PK\x06\x06",       // Zip64 end of directory records signature
        b"\x2c\x00\x00\x00", // Size of CDR
        b"\x00\x00\x00\x00",
        b"\x2d\x00",         // Version
        b"\x2d\x00",         // Version
        b"\x00\x00\x00\x00", // Disk number
        b"\x00\x00\x00\x00", // Disk number
        b"\x01\x00\x00\x00", // Number of records
        b"\x00\x00\x00\x00",
        b"\x01\x00\x00\x00", // Number of records
        b"\x00\x00\x00\x00",
        b"\x54\x00\x00\x00", // Size of central directory
        b"\x00\x00\x00\x00",
        b"\x49\x00\x00\x00", // Offset of central directory
        b"\x00\x00\x00\x00",
        b"PK\x06\x07",       // Zip64 end of central directory signature
        b"\x00\x00\x00\x00", // disk number
        b"\x9d\x00\x00\x00", // Offset of Zip64 EOCD signature
        b"\x00\x00\x00\x00",
        b"\x01\x00\x00\x00", // disk count
        b"PK\x05\x06",       // Regular end of central directory signature
        b"\x00\x00",         // disk number
        b"\x00\x00",         // disk number
        b"\xff\xff",         // Dummy # entries
        b"\xff\xff",         // Dummy # entries
        b"\xff\xff\xff\xff", // dummy size of central directory
        b"\xff\xff\xff\xff", // dummy offset of central directory
        b"\x00\x00",         // Comment size
    ];

    assert_eq!(output, expected.concat());

    let mut writer = ZipWrapperWriter::new(std::io::Cursor::new(Vec::new()), 0);
    writer
        .copy_file_aligned("README.txt".to_owned(), &b"Hello, World!"[..], 13, 64, 64)
        .expect("should work");

    let padded_output = writer.finish().expect("should succeed").into_inner();
    // The offsets in the central directory will differ, but the local header should be same,
    // modulo padding.
    assert_eq!(&padded_output[..128], [&[0u8; 4], &output[..124]].concat());
    assert_ne!(&padded_output[..], [&[0u8; 4], &output[..]].concat());

    // And the payload should be at an aligned position.
    assert_eq!(&padded_output[64..77], b"Hello, World!");
}
