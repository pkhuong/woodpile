//! This module contains functions to close an epoch subdirectory for
//! further writes.  Closing an epoch generates a (first-write-wins)
//! snapshot of the contents of all the log files, at the time the
//! epoch was closed.  This lets all readers agree on the contents of
//! the subdirectory, once closed.
//!
//! N.B., a racy reader could observe data that only became visible
//! after the winning snapshot was constructed.  Similarly, a write
//! could succeed after the winning snapshot was constructed.  Both
//! readers and writers should look for current times late enough that
//! the epochs they just accessed might be in the middle of being
//! closed ([`epoch_subdir_is_being_closed`] returns true), and ensure
//! the epoch is actually closed (e.g., by sleeping for a bit and
//! calling [`close_epoch_subdir`]) and re-check their result: the
//! data read or written could have missed the winning snapshot.
use std::ffi::OsStr;
use std::io::Result;
use std::path::Path;
use std::path::PathBuf;

use trivial_zip_wrapper::ZipWrapperWriter;

use vouched_time::VouchedTime;

const IN_PROGRESS_MARKER: &str = "000started";
const SUMMARY_FILE: &str = "100summary.zip";
const SUMMARY_TMP_PREFIX: &str = ".woodpile_tmp_summary-";

/// Existence status for a given snapshot file.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum SnapshotFileStatus {
    /// File definitely exists as a file
    Present,
    /// File definitely doesn't exist
    Absent,
    /// Something else (some other error, path isn't a file...)
    Unknown,
}

/// Generates a path for the summary file in the pile epoch directory
/// `dir`.  Also returns whether the file exists.
///
/// When the file doesn't exist, recursively flushes NFS caches up to
/// the log directory to make sure this isn't just an NFS issue.
pub fn closed_subdir_summary_path(dir: PathBuf) -> (PathBuf, SnapshotFileStatus) {
    closed_subdir_file_path(dir, OsStr::new(SUMMARY_FILE))
}

/// Generates a path for snapshot `file` in the pile epoch directory
/// `dir`.  Also returns whether the file eixsts.
///
/// When the file doesn't exist, recursively flushes (NFS) caches up to
/// the log directory to make sure this isn't just an NFS issue.
pub fn closed_subdir_file_path(
    dir: PathBuf,
    file: impl AsRef<OsStr>,
) -> (PathBuf, SnapshotFileStatus) {
    fn flush_cache(dir: &Path) -> Result<bool> {
        match std::fs::File::open(dir) {
            Ok(_) => Ok(true),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(false),
            Err(e) => Err(e),
        }
    }

    // Returns whether `dir` might be extant.  Only returns `false`
    // when `dir` is definitely absent, even after flushing caches.
    fn flush_dirs(dir: Option<&Path>, depth_limit: usize) -> bool {
        let Some(dir) = dir else {
            return true;
        };

        if depth_limit > 0 {
            // If `open` succeeds, `dir` must exist.
            if std::fs::File::open(dir).is_ok() {
                return true;
            }

            // If the parent doesn't exist, we don't exist.
            if !flush_dirs(dir.parent(), depth_limit - 1) {
                return false;
            }
        }

        // When in doubt, we exist.
        flush_cache(dir).unwrap_or(true)
    }

    fn doit(dir: PathBuf, file: &OsStr) -> (PathBuf, SnapshotFileStatus) {
        let mut target = dir;
        target.push(file);

        let found = if target.is_file() {
            SnapshotFileStatus::Present
        } else if !flush_dirs(target.parent(), 3) {
            // log / date / hour / bucket.  If `log` doesn't exist,
            // give up.
            SnapshotFileStatus::Absent
        } else {
            match std::fs::metadata(&target) {
                Ok(stat) if stat.file_type().is_file() => SnapshotFileStatus::Present,
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => SnapshotFileStatus::Absent,
                _ => SnapshotFileStatus::Unknown,
            }
        };

        (target, found)
    }

    doit(dir, file.as_ref())
}

/// Determines whether an epoch has been or is being closed (snapshotted).
///
/// This function should only be called when `dir` exists.
///
/// An epoch is being closed if the IN_PROGRESS_MARKER exists in `dir.
pub fn epoch_subdir_is_being_closed(dir: PathBuf) -> Result<bool> {
    let mut marker = dir;
    marker.push(IN_PROGRESS_MARKER);

    // If the marker file exists, we're definitely being closed.
    #[cfg(not(test))]
    if marker.is_file() {
        return Ok(true);
    }

    let subdir = marker.parent().expect("we just pushed a child");

    // Open the directory, which happens to flush the NFS cache.
    let _ = std::fs::File::open(subdir);

    // Any negative cache has been cleared, and we can check
    // for the marker again.
    match std::fs::metadata(&marker) {
        Ok(_) => Ok(true),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(false),
        // Avoid `Path::exists` in order to propagate non-ENOENT failures.
        Err(e) => Err(e),
    }
}

/// Starts the first step of closing an epoch subdirectory.  Returns
/// the deadline after which [`start_closing_epoch_subdir`] can act; the
/// call did something when `now` is strictly after the return value.
///
/// This function should only be called when `subdir` exists.
///
/// Multiple calls to [`start_closing_epoch_subdir`] are idempotent,
/// and [`close_epoch_subdir`] itself calls [`start_closing_epoch_subdir`].
/// However, calling [`start_closing_epoch_subdir`] at the right time
/// (before [`close_epoch_subdir`]) can help late writers notice their
/// lateness... and the idempotent function doubles as a function to
/// find the local time at which we want to close it.
///
/// Ideally, closers call [`start_closing_epoch_subdir`] as soon as possible,
/// wait for [`crate::EPOCH_WRITE_LEEWAY`] to elapse, and call [`close_epoch_subdir`].
///
/// When in a hurry, closers can call [`close_epoch_subdir`] directly.
pub fn start_closing_epoch_subdir(
    subdir: PathBuf,
    now: VouchedTime,
) -> Result<time::PrimitiveDateTime> {
    let deadline = crate::get_epoch_close_time(&subdir)? + crate::CLOCK_ERROR_BOUND;

    if now.get_local_time() <= deadline {
        return Ok(deadline);
    }

    // OK, it's late enough, make all the log files read-only.

    fn make_read_only(target: &Path) -> Result<()> {
        let mut perms = std::fs::metadata(target)?.permissions();
        perms.set_readonly(true);
        std::fs::set_permissions(target, perms)
    }

    // Opportunistically attempts to make all existing files
    // read-only.  is just a courtesy to writers.
    fn make_subdir_readonly(mut subdir: PathBuf) -> Result<()> {
        for item in subdir.read_dir()?.flatten() {
            assert_eq!(crate::LOG_EXTENSION, "log");

            // Only mark log files read-only.
            if !item.file_name().as_encoded_bytes().ends_with(b".log") {
                continue;
            }

            if matches!(
                item.file_type(),
                Ok(t) if t.is_file()
            ) {
                subdir.push(item.file_name());
                let _ = make_read_only(&subdir);
                subdir.pop();
            }
        }

        Ok(())
    }

    let _ = make_subdir_readonly(subdir);
    Ok(deadline)
}

/// Options for [`close_epoch_subdir`].
#[derive(Clone, Copy, Debug, Default)]
pub struct CloseEpochOptions {
    /// Whether to fsync file and directory data.  The default is false,
    /// because we expect to target (reliable) NFS with close-to-open
    /// consistency.
    pub fsync: bool,
}

fn close_epoch_subdir_impl(
    subdir: PathBuf,
    now: VouchedTime,
    options: CloseEpochOptions,
) -> Result<Option<time::PrimitiveDateTime>> {
    use std::os::unix::fs::OpenOptionsExt;

    let maybe_sync = |path: &Path| {
        if options.fsync {
            std::fs::File::open(path)?.sync_all()
        } else {
            Ok(())
        }
    };

    let deadline = start_closing_epoch_subdir(subdir.clone(), now)? + crate::EPOCH_WRITE_LEEWAY;

    // Make sure it's late enough to close the epoch.
    if now.get_local_time() <= deadline {
        return Ok(Some(deadline));
    }

    // It's late enough, time to actually snapshot everything.

    let mut target = subdir;
    maybe_sync(&target)?;

    // Ensure the marker file exists.  This informs writers that any operation that completes
    // is at risk of being ignored by snapshotting.  In practice, writers assume their writes
    // are safe whenever they close the destination file and find `IN_PROGRESS_MARKER` doesn't
    // exist yet (or when their local time is safely before the epoch close deadline).
    {
        target.push(IN_PROGRESS_MARKER);
        let _ = std::fs::OpenOptions::new()
            .mode(0o666) // Rust won't let us create a read-only file...
            .create(true)
            .write(true)
            .truncate(false)
            .open(&target)?;
        target.pop();
        maybe_sync(&target)?;
    }

    // The epoch subdir is now marked as closed.
    assert!(epoch_subdir_is_being_closed(target.clone())?);

    // See if the summary file exists: if it does, we're done.
    {
        // Open the directory to flush the NFS cache.
        let _ = std::fs::File::open(&target)?;

        target.push(SUMMARY_FILE);
        if target.is_file() {
            // The summary file definitely exists, we're done.
            //
            // Otherwise, keep trying to create the target, any
            // persistent error will be reported below.
            return Ok(None);
        }

        target.pop();
    }

    // We'll go through all the files in the subdir and copy their
    // bytes to `SUMMARY_FILE`.
    let (summary, temp_path) = tempfile::Builder::new()
        .prefix(SUMMARY_TMP_PREFIX)
        .tempfile_in(&target)?
        .into_parts();

    let mut zip = ZipWrapperWriter::new(summary, 0);

    let mut zip_dst = PathBuf::from(target.file_name().expect("target exists")).to_owned();

    // Copy all the data files in `subdir` to the summary zip file.
    for item in target.read_dir()? {
        let item = item?;
        assert_eq!(crate::LOG_EXTENSION, "log");
        if item.file_name().as_encoded_bytes().ends_with(b".log") {
            target.push(item.file_name());
            zip_dst.push(item.file_name());
            let mut src = std::fs::File::open(&target)?;
            let len = src.metadata()?.len();

            // At most 12.5% wastage, but we need at least ~50 bytes
            // for Zip overhead, so we can afford a little bit more.
            let max_padding = ((len / 8) + 16).min(u32::MAX as u64) as u32;

            zip.copy_file_aligned(
                zip_dst.as_os_str().to_string_lossy().to_string(),
                &mut src,
                len,
                128 * 1024,  // Always try to align to 128K
                max_padding, // But limit padding to scale with payload size
            )?;

            zip_dst.pop();
            target.pop();
        }
    }

    let summary = zip.finish()?;

    // The summary tempfile is now fully populated. We
    // want to publish it at `target`.
    target.push(SUMMARY_FILE);

    // Finalize what we wrote in `summary`.

    // Make it read-only, which should also flush on NFS (v3?).
    {
        // Get permissions by stat-ing through `vouched_time`, to get a free
        // base time update if necessary.
        //
        // let mut perms = summary.as_file().metadata()?.permissions();
        use vouched_time::nfs_voucher::observe_file_time;
        let mut perms = observe_file_time(&summary)?.0.permissions();
        perms.set_readonly(true);
        summary.set_permissions(perms)?;
    }

    // Close the file before persisting it, for close-to-open
    // consistency.
    summary.sync_all()?;
    std::mem::drop(summary);

    temp_path.persist_noclobber(&target)?;
    Ok(None)
}

/// Attempts to remove the files in `directory` whose names start with `prefix`.
///
/// Silently accepts any error in the directory traversal and in
/// [`std::fs::remove_file()`]: we expect this function to be called
/// concurrently on the same `directory`.
fn cleanup_directory_by_prefix(mut directory: PathBuf, prefix: &str) -> Result<()> {
    let prefix = prefix.as_bytes();
    for item in directory.read_dir()?.flatten() {
        let name = item.file_name();
        if name.as_encoded_bytes().starts_with(prefix) {
            directory.push(name);
            let _ = std::fs::remove_file(&directory);
            directory.pop();
        }
    }

    Ok(())
}

/// Ensures an epoch subdirectory is closed, with a `SUMMARY_FILE`
/// (that should contain all the contents of the log files).  Returns
/// the time after which the function should be called if `now` is too
/// early, and [`None`] on success.
///
/// Concurrent calls to this function are safe: the first-write-wins nature
/// of `link(2)` ensure that the first call to complete is "sticky."
pub fn close_epoch_subdir(
    subdir: PathBuf,
    now: VouchedTime,
    options: CloseEpochOptions,
) -> Result<Option<time::PrimitiveDateTime>> {
    let (mut target, exists) = closed_subdir_summary_path(subdir.clone());

    // Quick check to see if we're already done here.
    let ret = if exists == SnapshotFileStatus::Present {
        None
    } else {
        let ret = close_epoch_subdir_impl(subdir, now, options);
        // Regardless of `ret`, we're done if the summary file
        // now exists.
        if target.is_file() {
            None
        } else {
            ret?
        }
    };

    if ret.is_none() {
        // The summary file exists, let's see what we want to do to the
        // directory.
        target.pop();

        // Any concurrent `close_epoch_subdir` is now bound to fail; clean up
        // all temporary summary files.
        let _ = cleanup_directory_by_prefix(target.clone(), SUMMARY_TMP_PREFIX);

        if options.fsync {
            // fsync the parent directory before declaring victory,
            // if fsyncs are enabled.
            std::fs::File::open(&target)?.sync_all()?;
        }
    }

    Ok(ret)
}

#[cfg(test)]
use zip::read::ZipArchive;

/// epoch_subdir_is_being_closed should return false on an empty epoch directory.
#[cfg(not(miri))]
#[test]
fn test_being_closed_empty() {
    use test_dir::{DirBuilder, FileType, TestDir};
    use time::macros::datetime;

    let subdir =
        crate::construct_epoch_subdirectory("./test".into(), datetime!(2024-04-07 16:01:32))
            .0
            .into_os_string()
            .into_string()
            .unwrap();
    assert_eq!(
        subdir,
        format!("./test/2024-04-07/16/01:30-{:x}", 1712505697)
    );
    let temp = TestDir::temp().create(&subdir, FileType::Dir);

    assert!(!epoch_subdir_is_being_closed(temp.path(&subdir)).unwrap());
}

/// epoch_subdir_is_being_closed should return true when the IN_PROGRESS_MARKER exists.
#[cfg(not(miri))]
#[test]
fn test_being_closed_marker() {
    use test_dir::{DirBuilder, FileType, TestDir};
    use time::macros::datetime;

    let subdir =
        crate::construct_epoch_subdirectory("./test_marker".into(), datetime!(2024-04-07 16:01:32))
            .0
            .into_os_string()
            .into_string()
            .unwrap();
    assert_eq!(
        subdir,
        format!("./test_marker/2024-04-07/16/01:30-{:x}", 1712505697)
    );
    let temp = TestDir::temp().create(&subdir, FileType::Dir).create(
        &format!("{}/{}", &subdir, IN_PROGRESS_MARKER),
        FileType::EmptyFile,
    );

    assert!(epoch_subdir_is_being_closed(temp.path(&subdir)).unwrap());
}

/// epoch_subdir_is_being_closed should return true when the IN_PROGRESS_MARKER exists,
/// even if there's extra stuff.
#[cfg(not(miri))]
#[test]
fn test_being_closed_marker_2() {
    use test_dir::{DirBuilder, FileType, TestDir};
    use time::macros::datetime;

    let subdir = crate::construct_epoch_subdirectory(
        "./test_marker_2".into(),
        datetime!(2024-04-07 16:01:32),
    )
    .0
    .into_os_string()
    .into_string()
    .unwrap();
    assert_eq!(
        subdir,
        format!("./test_marker_2/2024-04-07/16/01:30-{:x}", 1712505697)
    );
    let temp = TestDir::temp()
        .create(&subdir, FileType::Dir)
        .create(&format!("{}/00000dummy", &subdir), FileType::EmptyFile)
        .create(
            &format!("{}/{}", &subdir, IN_PROGRESS_MARKER),
            FileType::EmptyFile,
        );

    assert!(epoch_subdir_is_being_closed(temp.path(&subdir)).unwrap());
}

/// closing an epoch should always succeed when we have a SUMMARY_FILE,
/// even if the epoch isn't closed (the close-side code must avoid that
/// situation).
#[cfg(not(miri))]
#[test]
fn test_already_has_summary() {
    use test_dir::{DirBuilder, FileType, TestDir};
    use time::macros::datetime;

    let subdir = crate::construct_epoch_subdirectory(
        "./test_has_summary".into(),
        datetime!(2024-04-07 16:01:32),
    )
    .0
    .into_os_string()
    .into_string()
    .unwrap();
    assert_eq!(
        subdir,
        format!("./test_has_summary/2024-04-07/16/01:30-{:x}", 1712505697)
    );
    let temp = TestDir::temp().create(&subdir, FileType::Dir).create(
        &format!("{}/{}", &subdir, SUMMARY_FILE),
        FileType::EmptyFile,
    );

    assert!(!epoch_subdir_is_being_closed(temp.path(&subdir)).unwrap());

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    assert_eq!(
        close_epoch_subdir(
            temp.path(&subdir),
            VouchedTime::new(
                datetime!(2024-04-07 16:01:39.1),
                1712505699000,
                vouch_params.vouch(1712505699000),
            )
            .unwrap(),
            CloseEpochOptions { fsync: false }
        )
        .expect("must succeed"),
        None
    );

    assert_eq!(
        close_epoch_subdir_impl(
            temp.path(&subdir),
            VouchedTime::new(
                datetime!(2024-04-07 16:01:39.95),
                1712505699000,
                vouch_params.vouch(1712505699000),
            )
            .unwrap(),
            CloseEpochOptions { fsync: true }
        )
        .expect("must succeed"),
        None
    );
}

/// The epoch is still open after a successful call to `start_closing_epoch_subdir`,
/// although we expect the directory and its files to be read-only.
#[cfg(not(miri))]
#[test]
fn test_still_open_after_start() {
    use test_dir::{DirBuilder, FileType, TestDir};
    use time::macros::datetime;

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let subdir = crate::construct_epoch_subdirectory(
        "./test_open_after_start".into(),
        datetime!(2024-04-07 16:01:32),
    )
    .0
    .into_os_string()
    .into_string()
    .unwrap();
    assert_eq!(
        subdir,
        format!(
            "./test_open_after_start/2024-04-07/16/01:30-{:x}",
            1712505697
        )
    );
    let temp = TestDir::temp()
        .create(&subdir, FileType::Dir)
        .create(&format!("{}/foo.log", &subdir), FileType::RandomFile(100));

    // The new epoch directory is initially open.
    assert!(!epoch_subdir_is_being_closed(temp.path(&subdir)).unwrap());

    // start_closing_epoch_subdir succeeds
    assert_eq!(
        start_closing_epoch_subdir(
            temp.path(&subdir),
            VouchedTime::new(
                datetime!(2024-04-07 16:01:39.1),
                1712505699000,
                vouch_params.vouch(1712505699000),
            )
            .unwrap(),
        )
        .expect("must succeed"),
        datetime!(2024-04-07 16:01:30) + crate::EPOCH_WRITE_DURATION + crate::CLOCK_ERROR_BOUND
    );

    // The new epoch directory is *still* open.
    assert!(!epoch_subdir_is_being_closed(temp.path(&subdir)).unwrap());

    // The directory's contents are read-only
    assert!(
        std::fs::metadata(temp.path(&format!("{}/foo.log", &subdir)))
            .unwrap()
            .permissions()
            .readonly()
    );
    // But the directory is still writable.
    assert!(!std::fs::metadata(temp.path(&subdir))
        .unwrap()
        .permissions()
        .readonly());
}

/// An early call to `start_closing_epoch_subdir` should no-op and
/// return a deadline in the future.
#[cfg(not(miri))]
#[test]
fn test_reject_early_close() {
    use test_dir::{DirBuilder, FileType, TestDir};
    use time::macros::datetime;

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let subdir = crate::construct_epoch_subdirectory(
        "./test_reject_early".into(),
        datetime!(2024-04-07 16:01:32),
    )
    .0
    .into_os_string()
    .into_string()
    .unwrap();
    assert_eq!(
        subdir,
        format!("./test_reject_early/2024-04-07/16/01:30-{:x}", 1712505697)
    );
    let temp = TestDir::temp()
        .create(&subdir, FileType::Dir)
        .create(&format!("{}/foo.log", &subdir), FileType::RandomFile(100));

    // The new epoch directory is initially open.
    assert!(!epoch_subdir_is_being_closed(temp.path(&subdir)).unwrap());

    // start_closing_epoch_subdir succeeds
    let now = VouchedTime::new(
        datetime!(2024-04-07 16:01:38.9),
        1712505699000,
        vouch_params.vouch(1712505699000),
    )
    .unwrap();
    let wanted = start_closing_epoch_subdir(temp.path(&subdir), now).expect("must succeed");
    assert_eq!(
        wanted,
        datetime!(2024-04-07 16:01:30) + crate::EPOCH_WRITE_DURATION + crate::CLOCK_ERROR_BOUND
    );

    assert!(wanted > now.get_local_time());

    // The new epoch directory is *still* open.
    assert!(!epoch_subdir_is_being_closed(temp.path(&subdir)).unwrap());

    // The directory and its contents are still writable
    assert!(!std::fs::metadata(temp.path(&subdir))
        .unwrap()
        .permissions()
        .readonly());
    assert!(
        !std::fs::metadata(temp.path(&format!("{}/foo.log", &subdir)))
            .unwrap()
            .permissions()
            .readonly()
    );
}

/// Test that we remove the file that matches, and not the file that doesn't match.
#[cfg(not(miri))]
#[test]
fn test_cleanup_directory_by_prefix() {
    use test_dir::{DirBuilder, FileType, TestDir};
    let temp_file = format!("{}12345", SUMMARY_TMP_PREFIX);
    let temp = TestDir::temp()
        .create(IN_PROGRESS_MARKER, FileType::EmptyFile)
        .create(&temp_file, FileType::EmptyFile)
        .create(SUMMARY_FILE, FileType::EmptyFile);

    // The three files exist initially.
    assert!(temp.path(IN_PROGRESS_MARKER).exists());
    assert!(temp.path(&temp_file).exists());
    assert!(temp.path(SUMMARY_FILE).exists());

    cleanup_directory_by_prefix(temp.path(".").to_owned(), SUMMARY_TMP_PREFIX)
        .expect("should succeed");

    // The in-progress marker still exists.
    assert!(temp.path(IN_PROGRESS_MARKER).exists());
    // The temporary file is gone.
    assert!(!temp.path(&temp_file).exists());
    // The summary file still exists.
    assert!(temp.path(SUMMARY_FILE).exists());
}

/// An early call to `close_epoch_subdir` should no-op and return a deadline in the future.
#[cfg(not(miri))]
#[test]
fn test_reject_early_close_2() {
    use test_dir::{DirBuilder, FileType, TestDir};
    use time::macros::datetime;

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let subdir = crate::construct_epoch_subdirectory(
        "./test_reject_early_2".into(),
        datetime!(2024-04-07 16:01:32),
    )
    .0
    .into_os_string()
    .into_string()
    .unwrap();
    assert_eq!(
        subdir,
        format!("./test_reject_early_2/2024-04-07/16/01:30-{:x}", 1712505697)
    );
    let temp = TestDir::temp()
        .create(&subdir, FileType::Dir)
        .create(&format!("{}/foo.log", &subdir), FileType::RandomFile(100));

    // The new epoch directory is initially open.
    assert!(!epoch_subdir_is_being_closed(temp.path(&subdir)).unwrap());

    // start_closing_epoch_subdir succeeds
    let now = VouchedTime::new(
        datetime!(2024-04-07 16:01:38.9),
        1712505699000,
        vouch_params.vouch(1712505699000),
    )
    .unwrap();
    let wanted =
        close_epoch_subdir(temp.path(&subdir), now, Default::default()).expect("must succeed");
    assert_eq!(
        wanted,
        Some(
            datetime!(2024-04-07 16:01:30)
                + crate::EPOCH_WRITE_DURATION
                + crate::EPOCH_WRITE_LEEWAY
                + crate::CLOCK_ERROR_BOUND
        )
    );

    assert!(wanted.unwrap() > now.get_local_time());

    // The new epoch directory is *still* open.
    assert!(!epoch_subdir_is_being_closed(temp.path(&subdir)).unwrap());

    // The directory and its contents are still writable
    assert!(!std::fs::metadata(temp.path(&subdir))
        .unwrap()
        .permissions()
        .readonly());
    assert!(
        !std::fs::metadata(temp.path(&format!("{}/foo.log", &subdir)))
            .unwrap()
            .permissions()
            .readonly()
    );
}

/// An early call to `close_epoch_subdir` should no-op and return a deadline in the future,
/// even after a "good" call to `start_closing_epoch_subdir`.
#[cfg(not(miri))]
#[test]
fn test_reject_close_3() {
    use test_dir::{DirBuilder, FileType, TestDir};
    use time::macros::datetime;

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let subdir = crate::construct_epoch_subdirectory(
        "./test_reject_close_3".into(),
        datetime!(2024-04-07 16:01:32),
    )
    .0
    .into_os_string()
    .into_string()
    .unwrap();
    assert_eq!(
        subdir,
        format!("./test_reject_close_3/2024-04-07/16/01:30-{:x}", 1712505697)
    );
    let temp = TestDir::temp()
        .create(&subdir, FileType::Dir)
        .create(&format!("{}/foo.log", &subdir), FileType::RandomFile(100));

    // start_closing_epoch_subdir succeeds
    let now = VouchedTime::new(
        datetime!(2024-04-07 16:01:39.89),
        1712505699000,
        vouch_params.vouch(1712505699000),
    )
    .unwrap();
    start_closing_epoch_subdir(temp.path(&subdir), now).expect("should succeed");

    // close_epoch_subdir should succeed, with a deadline in the future.
    assert_eq!(
        close_epoch_subdir(temp.path(&subdir), now, CloseEpochOptions { fsync: true })
            .expect("should succeed"),
        Some(datetime!(2024-04-07 16:01:39.90))
    );

    assert!(!epoch_subdir_is_being_closed(temp.path(&subdir)).unwrap());

    // The directory's contents are read-only
    assert!(
        std::fs::metadata(temp.path(&format!("{}/foo.log", &subdir)))
            .unwrap()
            .permissions()
            .readonly()
    );
    // But the directory is still writable.
    assert!(!std::fs::metadata(temp.path(&subdir))
        .unwrap()
        .permissions()
        .readonly());
}

/// An early call to `close_epoch_subdir` should no-op and return a deadline in the future,
/// even if its internal call to `start_closing_epoch_subdir` succeeds.
#[cfg(not(miri))]
#[test]
fn test_reject_close_4() {
    use test_dir::{DirBuilder, FileType, TestDir};
    use time::macros::datetime;

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let subdir = crate::construct_epoch_subdirectory(
        "./test_reject_close_3".into(),
        datetime!(2024-04-07 16:01:32),
    )
    .0
    .into_os_string()
    .into_string()
    .unwrap();
    assert_eq!(
        subdir,
        format!("./test_reject_close_3/2024-04-07/16/01:30-{:x}", 1712505697)
    );
    let temp = TestDir::temp()
        .create(&subdir, FileType::Dir)
        .create(&format!("{}/foo.log", &subdir), FileType::RandomFile(100));

    let initial_summary_path = closed_subdir_summary_path(temp.path(&subdir)).0;

    // start_closing_epoch_subdir succeeds
    let now = VouchedTime::new(
        datetime!(2024-04-07 16:01:39.89),
        1712505699000,
        vouch_params.vouch(1712505699000),
    )
    .unwrap();

    // close_epoch_subdir should succeed, with a deadline in the future.
    assert_eq!(
        close_epoch_subdir(temp.path(&subdir), now, CloseEpochOptions { fsync: true })
            .expect("should succeed"),
        Some(datetime!(2024-04-07 16:01:39.90))
    );

    assert!(!epoch_subdir_is_being_closed(temp.path(&subdir)).unwrap());

    // The directory's contents are read-only
    assert!(
        std::fs::metadata(temp.path(&format!("{}/foo.log", &subdir)))
            .unwrap()
            .permissions()
            .readonly()
    );
    // But the directory is still writable.
    assert!(!std::fs::metadata(temp.path(&subdir))
        .unwrap()
        .permissions()
        .readonly());

    // the summary path hasn't changed
    assert_eq!(
        initial_summary_path,
        closed_subdir_summary_path(temp.path(&subdir)).0
    );
}

/// Closing an epoch with one log file should copy its contents to the summary file.
#[cfg(not(miri))]
#[test]
fn test_close_one_file() {
    use test_dir::{DirBuilder, FileType, TestDir};
    use time::macros::datetime;

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let subdir = crate::construct_epoch_subdirectory(
        "./test_close_one_file".into(),
        datetime!(2024-04-07 16:01:32),
    )
    .0
    .into_os_string()
    .into_string()
    .unwrap();
    assert_eq!(
        subdir,
        format!("./test_close_one_file/2024-04-07/16/01:30-{:x}", 1712505697)
    );

    let temp = TestDir::temp()
        .create(&subdir, FileType::Dir)
        .create(&format!("{}/foo.log", &subdir), FileType::RandomFile(100));

    let (summary_path, _depth) = closed_subdir_summary_path(temp.path(&subdir));

    // start_closing_epoch_subdir succeeds
    let now = VouchedTime::new(
        datetime!(2024-04-07 16:01:39.95),
        1712505699000,
        vouch_params.vouch(1712505699000),
    )
    .unwrap();
    start_closing_epoch_subdir(temp.path(&subdir), now).expect("should succeed");

    // The epoch is not yet marked as being closed.
    assert!(!epoch_subdir_is_being_closed(temp.path(&subdir)).unwrap());

    let dummy_temp_file = format!("{}/{}12345", &subdir, SUMMARY_TMP_PREFIX);
    std::fs::File::create(temp.path(&dummy_temp_file)).expect("creation should succeed");

    // close_epoch_subdir should succeed.
    assert_eq!(
        close_epoch_subdir(temp.path(&subdir), now, CloseEpochOptions { fsync: true })
            .expect("should succeed"),
        None
    );

    // The epoch is now marked as being closed.
    assert!(epoch_subdir_is_being_closed(temp.path(&subdir)).unwrap());

    let mut summary = ZipArchive::new(std::fs::File::open(summary_path).unwrap()).unwrap();
    // One file.
    assert_eq!(summary.len(), 1);
    for idx in 0..summary.len() {
        use std::io::Read;

        let mut entry = summary.by_index(idx).unwrap();

        assert!(entry.is_file());
        assert_eq!(
            entry.name(),
            format!(
                "{}/foo.log",
                Path::new(&subdir).file_name().unwrap().to_string_lossy()
            )
        );

        let mut summary_bytes = Vec::new();
        let _ = entry.read_to_end(&mut summary_bytes); // Disregard invalid CRC
        assert_eq!(
            std::fs::read(temp.path(&format!("{}/foo.log", &subdir))).unwrap(),
            summary_bytes
        );
    }

    // The dummy file should have been cleaned up.
    assert!(!temp.path(&dummy_temp_file).exists());
}

/// Closing an epoch with two log files should copy their contents to the summary file.
#[cfg(not(miri))]
#[test]
fn test_close_two_files() {
    use std::collections::HashMap;
    use test_dir::{DirBuilder, FileType, TestDir};
    use time::macros::datetime;

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let subdir = crate::construct_epoch_subdirectory(
        "./test_close_two_files".into(),
        datetime!(2024-04-07 16:01:32),
    )
    .0
    .into_os_string()
    .into_string()
    .unwrap();
    assert_eq!(
        subdir,
        format!(
            "./test_close_two_files/2024-04-07/16/01:30-{:x}",
            1712505697
        )
    );
    let temp = TestDir::temp()
        .create(&subdir, FileType::Dir)
        .create(&format!("{}/foo.log", &subdir), FileType::RandomFile(100))
        .create(&format!("{}/bar.log", &subdir), FileType::RandomFile(100));

    // start_closing_epoch_subdir succeeds
    let now = VouchedTime::new(
        datetime!(2024-04-07 16:01:39.95),
        1712505699000,
        vouch_params.vouch(1712505699000),
    )
    .unwrap();
    start_closing_epoch_subdir(temp.path(&subdir), now).expect("should succeed");

    // close_epoch_subdir should succeed.
    assert_eq!(
        close_epoch_subdir(temp.path(&subdir), now, CloseEpochOptions { fsync: false })
            .expect("should succeed"),
        None
    );

    let mut expected_contents: HashMap<String, Vec<u8>> = HashMap::new();

    {
        let base = Path::new(&subdir).file_name().unwrap().to_string_lossy();

        expected_contents.insert(
            format!("{}/foo.log", &base),
            std::fs::read(temp.path(&format!("{}/foo.log", &subdir))).unwrap(),
        );
        expected_contents.insert(
            format!("{}/bar.log", &base),
            std::fs::read(temp.path(&format!("{}/bar.log", &subdir))).unwrap(),
        );
    }

    let mut summary = ZipArchive::new(
        std::fs::File::open(closed_subdir_summary_path(temp.path(&subdir)).0).unwrap(),
    )
    .unwrap();
    // two files.
    assert_eq!(summary.len(), 2);
    for idx in 0..summary.len() {
        use std::io::Read;

        let mut entry = summary.by_index(idx).unwrap();

        assert!(entry.is_file());
        let mut summary_bytes = Vec::new();
        let _ = entry.read_to_end(&mut summary_bytes); // Disregard invalid CRC
        assert_eq!(expected_contents.get(entry.name()), Some(&summary_bytes));
    }
}

/// Closing an epoch twice in a row should succeed and find the correct values.
#[cfg(not(miri))]
#[test]
fn test_close_twice() {
    use std::collections::HashMap;
    use test_dir::{DirBuilder, FileType, TestDir};
    use time::macros::datetime;

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let subdir = crate::construct_epoch_subdirectory(
        "./test_close_twice".into(),
        datetime!(2024-04-07 16:01:32),
    )
    .0
    .into_os_string()
    .into_string()
    .unwrap();
    assert_eq!(
        subdir,
        format!("./test_close_twice/2024-04-07/16/01:30-{:x}", 1712505697)
    );
    let temp = TestDir::temp()
        .create(&subdir, FileType::Dir)
        .create(&format!("{}/foo.log", &subdir), FileType::RandomFile(100))
        .create(&format!("{}/bar.log", &subdir), FileType::RandomFile(80));

    // start_closing_epoch_subdir succeeds
    let now = VouchedTime::new(
        datetime!(2024-04-07 16:01:39.95),
        1712505699000,
        vouch_params.vouch(1712505699000),
    )
    .unwrap();

    // close_epoch_subdir should succeed.
    assert_eq!(
        close_epoch_subdir(temp.path(&subdir), now, CloseEpochOptions { fsync: false })
            .expect("should succeed"),
        None
    );

    // The summary file must now be read-only.
    let perms = std::fs::metadata(closed_subdir_summary_path(temp.path(&subdir)).0).unwrap();
    assert!(perms.permissions().readonly());

    // subsequent ones should succeed too
    assert_eq!(
        close_epoch_subdir(temp.path(&subdir), now, CloseEpochOptions { fsync: false })
            .expect("should succeed"),
        None
    );

    assert_eq!(
        close_epoch_subdir_impl(temp.path(&subdir), now, CloseEpochOptions { fsync: true })
            .expect("should succeed"),
        None
    );

    let mut expected_contents: HashMap<String, Vec<u8>> = HashMap::new();

    {
        let base = Path::new(&subdir).file_name().unwrap().to_string_lossy();

        expected_contents.insert(
            format!("{}/foo.log", &base),
            std::fs::read(temp.path(&format!("{}/foo.log", &subdir))).unwrap(),
        );
        expected_contents.insert(
            format!("{}/bar.log", &base),
            std::fs::read(temp.path(&format!("{}/bar.log", &subdir))).unwrap(),
        );
    }

    let mut summary = ZipArchive::new(
        std::fs::File::open(closed_subdir_summary_path(temp.path(&subdir)).0).unwrap(),
    )
    .unwrap();
    // two files.
    assert_eq!(summary.len(), 2);
    for idx in 0..summary.len() {
        use std::io::Read;

        let mut entry = summary.by_index(idx).unwrap();

        assert!(entry.is_file());
        let mut summary_bytes = Vec::new();
        let _ = entry.read_to_end(&mut summary_bytes); // Disregard invalid CRC
        assert_eq!(expected_contents.get(entry.name()), Some(&summary_bytes));
    }

    // The epoch is marked as being closed.
    assert!(epoch_subdir_is_being_closed(temp.path(&subdir)).unwrap());
}
