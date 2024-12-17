//! The `header` struct contains models for the ZIP-format's headers.
//!
//! See <https://pkware.cachefly.net/webdocs/casestudies/APPNOTE.TXT>
//! APPNOTE.TXT - .ZIP File Format Specification Version 6.3.10

/// Constructs a Zip64 local header for "STORED" file with name
/// `filename` and total `size` bytes.
///
/// If `filename` exceeds u16::MAX bytes, it is truncated silently.
pub fn construct_local_file_header(filename: &str, size: u64) -> Vec<u8> {
    // XXX: silently clamp the filename, we can't have paths that long
    // in real life.
    let filename_len: u16 = filename.as_bytes().len().min(u16::MAX as usize) as u16;
    let filename = &filename.as_bytes()[..filename_len as usize];

    let expected_size = 30 + filename.len() + 20;
    let mut dst = Vec::with_capacity(expected_size);

    // 30 bytes for the local file header

    // 4.3.7  Local file header:
    //
    //    local file header signature     4 bytes  (0x04034b50)
    //    version needed to extract       2 bytes
    //    general purpose bit flag        2 bytes
    //    compression method              2 bytes
    //    last mod file time              2 bytes
    //    last mod file date              2 bytes
    //    crc-32                          4 bytes
    //    compressed size                 4 bytes
    //    uncompressed size               4 bytes
    //    file name length                2 bytes
    //    extra field length              2 bytes
    //
    //    file name (variable size)
    //    extra field (variable size)

    // Signature
    dst.extend_from_slice(b"PK\x03\x04");
    // Version 4.5 (for Zip64)
    dst.extend_from_slice(&45u16.to_le_bytes());
    // Flags XXX: should we set 13?
    dst.extend_from_slice(&0u16.to_le_bytes());
    // Compression method (STORE)
    dst.extend_from_slice(&0u16.to_le_bytes());
    // Time
    dst.extend_from_slice(&0u16.to_le_bytes());
    // Date
    dst.extend_from_slice(&0u16.to_le_bytes());
    // CRC
    dst.extend_from_slice(&0u32.to_le_bytes());
    // Uncompressed size (escape to zip64)
    dst.extend_from_slice(&u32::MAX.to_le_bytes());
    // Compressed size (escape to zip64)
    dst.extend_from_slice(&u32::MAX.to_le_bytes());
    // Filename length
    dst.extend_from_slice(&filename_len.to_le_bytes());
    // Extension size
    dst.extend_from_slice(&20u16.to_le_bytes());

    // file name
    dst.extend_from_slice(filename);

    // 20 bytes for the Zip64 extra field

    // 4.5.2 The current Header ID mappings defined by PKWARE are:
    //
    //    0x0001        Zip64 extended information extra field
    //  [...]

    // 4.5.3 -Zip64 Extended Information Extra Field (0x0001):
    //
    //       Note: all fields stored in Intel low-byte/high-byte order.
    //
    //         Value      Size       Description
    //         -----      ----       -----------
    // (ZIP64) 0x0001     2 bytes    Tag for this "extra" block type
    //         Size       2 bytes    Size of this "extra" block
    //         Original
    //         Size       8 bytes    Original uncompressed file size
    //         Compressed
    //         Size       8 bytes    Size of compressed data
    //         Relative Header
    //         Offset     8 bytes    Offset of local header record
    //         Disk Start
    //         Number     4 bytes    Number of the disk on which
    //                               this file starts

    // ZIP64 extension
    dst.extend_from_slice(&1u16.to_le_bytes());
    // We have 16 bytes of extra data
    dst.extend_from_slice(&16u16.to_le_bytes());
    // Uncompressed size
    dst.extend_from_slice(&size.to_le_bytes());
    // Compressed size
    dst.extend_from_slice(&size.to_le_bytes());
    // Other stuff is only for the central directory.

    debug_assert_eq!(dst.len(), expected_size);
    dst
}

/// Constructs the central (end of file) "header" for `filename`'s contents with header at
/// offset `header_offset` and *file size* `size`.
///
/// If `filename` exceeds u16::MAX bytes, it is truncated silently.
pub fn construct_central_directory_header(
    filename: &str,
    header_offset: u64,
    size: u64,
    mut dst: Vec<u8>,
) -> Vec<u8> {
    // XXX: silently clamp the filename, we can't have paths that long
    // in real life.
    let filename_len: u16 = filename.as_bytes().len().min(u16::MAX as usize) as u16;
    let filename = &filename.as_bytes()[..filename_len as usize];

    let initial_len = dst.len();
    let expected_size = 46 + filename.len() + 28;
    let _ = dst.try_reserve(expected_size);

    // 4.3.12  Central directory structure
    //   File header:

    // central file header signature   4 bytes  (0x02014b50)
    // version made by                 2 bytes
    // version needed to extract       2 bytes
    // general purpose bit flag        2 bytes
    // compression method              2 bytes
    // last mod file time              2 bytes
    // last mod file date              2 bytes
    // crc-32                          4 bytes
    // compressed size                 4 bytes
    // uncompressed size               4 bytes
    // file name length                2 bytes
    // extra field length              2 bytes
    // file comment length             2 bytes
    // disk number start               2 bytes
    // internal file attributes        2 bytes
    // external file attributes        4 bytes
    // relative offset of local header 4 bytes

    // file name (variable size)
    // extra field (variable size)
    // file comment (variable size)

    // Signature
    dst.extend_from_slice(b"PK\x01\x02");
    // Writer version 4.5
    dst.extend_from_slice(&45u16.to_le_bytes());
    // Reader version 4.5 (for Zip64)
    dst.extend_from_slice(&45u16.to_le_bytes());
    // Flags
    dst.extend_from_slice(&0u16.to_le_bytes());
    // Compression method (STORE)
    dst.extend_from_slice(&0u16.to_le_bytes());
    // Time
    dst.extend_from_slice(&0u16.to_le_bytes());
    // Date
    dst.extend_from_slice(&0u16.to_le_bytes());
    // CRC
    dst.extend_from_slice(&0u32.to_le_bytes());
    // Uncompressed size (escape to zip64)
    dst.extend_from_slice(&u32::MAX.to_le_bytes());
    // Compressed size (escape to zip64)
    dst.extend_from_slice(&u32::MAX.to_le_bytes());
    // Filename length
    dst.extend_from_slice(&filename_len.to_le_bytes());
    // Extra data (zip64)
    dst.extend_from_slice(&28u16.to_le_bytes());
    // Comment length
    dst.extend_from_slice(&0u16.to_le_bytes());
    // Disk number
    dst.extend_from_slice(&0u16.to_le_bytes());
    // Internal attributes
    dst.extend_from_slice(&0u16.to_le_bytes());
    // External attributes
    dst.extend_from_slice(&0u32.to_le_bytes());
    // Offset of local header (escape to zip64)
    dst.extend_from_slice(&u32::MAX.to_le_bytes());

    dst.extend_from_slice(filename);

    // 4.5.3 -Zip64 Extended Information Extra Field (0x0001):
    //
    //       Note: all fields stored in Intel low-byte/high-byte order.
    //
    //         Value      Size       Description
    //         -----      ----       -----------
    // (ZIP64) 0x0001     2 bytes    Tag for this "extra" block type
    //         Size       2 bytes    Size of this "extra" block
    //         Original
    //         Size       8 bytes    Original uncompressed file size
    //         Compressed
    //         Size       8 bytes    Size of compressed data
    //         Relative Header
    //         Offset     8 bytes    Offset of local header record
    //         Disk Start
    //         Number     4 bytes    Number of the disk on which
    //                               this file starts

    // Zip64 extension
    dst.extend_from_slice(&1u16.to_le_bytes());
    // 24 byte payload
    dst.extend_from_slice(&24u16.to_le_bytes());
    // Uncompressed size
    dst.extend_from_slice(&size.to_le_bytes());
    // Compressed size
    dst.extend_from_slice(&size.to_le_bytes());
    // Header start
    dst.extend_from_slice(&header_offset.to_le_bytes());

    debug_assert_eq!(dst.len() - initial_len, expected_size);
    dst
}

/// Constructs the locator trailer for a central directory of `num_records`
/// starting at `central_directory_offset` and spanning `central_directory_bytes`.
///
/// We expect the locator to be written at `dst_offset`, or right
/// after the central directory records by default.
pub fn construct_central_directory_locator(
    num_records: usize,
    central_directory_offset: u64,
    central_directory_bytes: u64,
    dst_offset: Option<u64>,
    mut dst: Vec<u8>,
) -> Vec<u8> {
    let dst_offset =
        dst_offset.unwrap_or(central_directory_offset.saturating_add(central_directory_bytes));

    let initial_len = dst.len();
    let expected_size = 56 + 20 + 22;
    let _ = dst.try_reserve(expected_size);

    // 4.3.14  Zip64 end of central directory record
    //
    //      zip64 end of central dir
    //      signature                       4 bytes  (0x06064b50)
    //      size of zip64 end of central
    //      directory record                8 bytes
    //      version made by                 2 bytes
    //      version needed to extract       2 bytes
    //      number of this disk             4 bytes
    //      number of the disk with the
    //      start of the central directory  4 bytes
    //      total number of entries in the
    //      central directory on this disk  8 bytes
    //      total number of entries in the
    //      central directory               8 bytes
    //      size of the central directory   8 bytes
    //      offset of start of central
    //      directory with respect to
    //      the starting disk number        8 bytes
    //      zip64 extensible data sector    (variable size)
    //
    //    4.3.14.1 The value stored into the "size of zip64 end of central
    //    directory record" SHOULD be the size of the remaining
    //    record and SHOULD NOT include the leading 12 bytes.
    //
    //    Size = SizeOfFixedFields + SizeOfVariableData - 12.

    // Signature (ZIP64)
    dst.extend_from_slice(b"PK\x06\x06");
    // Size of record
    dst.extend_from_slice(&44u64.to_le_bytes());
    // Writer version 4.5
    dst.extend_from_slice(&45u16.to_le_bytes());
    // Reader version 4.5 (for Zip64)
    dst.extend_from_slice(&45u16.to_le_bytes());
    // Disk number
    dst.extend_from_slice(&0u32.to_le_bytes());
    // Disk number for central directory
    dst.extend_from_slice(&0u32.to_le_bytes());
    // Number of central directory records on "this disk"
    dst.extend_from_slice(&(num_records as u64).to_le_bytes());
    // Number of central directory records in total
    dst.extend_from_slice(&(num_records as u64).to_le_bytes());
    dst.extend_from_slice(&central_directory_bytes.to_le_bytes());
    dst.extend_from_slice(&central_directory_offset.to_le_bytes());

    // 4.3.15 Zip64 end of central directory locator
    //
    //    zip64 end of central dir locator
    //    signature                       4 bytes  (0x07064b50)
    //    number of the disk with the
    //    start of the zip64 end of
    //    central directory               4 bytes
    //    relative offset of the zip64
    //    end of central directory record 8 bytes
    //    total number of disks           4 bytes

    // ZIP64 locator
    dst.extend_from_slice(b"PK\x06\x07");
    // Disk number
    dst.extend_from_slice(&0u32.to_le_bytes());
    dst.extend_from_slice(&dst_offset.to_le_bytes());
    // Total number of disks (1)
    dst.extend_from_slice(&1u32.to_le_bytes());

    // 4.3.16  End of central directory record:
    //
    //    end of central dir signature    4 bytes  (0x06054b50)
    //    number of this disk             2 bytes
    //    number of the disk with the
    //    start of the central directory  2 bytes
    //    total number of entries in the
    //    central directory on this disk  2 bytes
    //    total number of entries in
    //    the central directory           2 bytes
    //    size of the central directory   4 bytes
    //    offset of start of central
    //    directory with respect to
    //    the starting disk number        4 bytes
    //    .ZIP file comment length        2 bytes
    //    .ZIP file comment       (variable size)

    // End of record locator
    dst.extend_from_slice(b"PK\x05\x06");
    // Disk number
    dst.extend_from_slice(&0u16.to_le_bytes());
    // Disk with directory
    dst.extend_from_slice(&0u16.to_le_bytes());
    // Number of CDR entries on disk(defer to zip64)
    dst.extend_from_slice(&u16::MAX.to_le_bytes());
    // Number of CDR entries in total (defer to zip64)
    dst.extend_from_slice(&u16::MAX.to_le_bytes());
    // Size of central directory (defer to zip64)
    dst.extend_from_slice(&u32::MAX.to_le_bytes());
    // Offset of central directory (defer to zip64)
    dst.extend_from_slice(&u32::MAX.to_le_bytes());
    // Comment size (0)
    dst.extend_from_slice(&0u16.to_le_bytes());

    debug_assert_eq!(dst.len() - initial_len, expected_size);
    dst
}
