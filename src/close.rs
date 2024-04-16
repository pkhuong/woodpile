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
use std::io::Result;
use std::path::Path;
use std::path::PathBuf;

use crate::VouchedTime;

const SNAPSHOT_SUBDIR: &str = "snapshot";
const IN_PROGRESS_MARKER: &str = "000started";
const SUMMARY_FILE: &str = "100summary";
const SUMMARY_TMP_PREFIX: &str = ".woodpile_tmp_summary-";

/// Determines whether an epoch has been or is being closed (snapshotted).
///
/// An epoch is being closed if the IN_PROGRESS_MARKER in its
/// SNAPSHOT_SUBDIR exists.
pub fn epoch_subdir_is_being_closed(dir: PathBuf) -> Result<bool> {
    let mut marker = dir;
    marker.push(SNAPSHOT_SUBDIR);
    marker.push(IN_PROGRESS_MARKER);

    // If the marker file exists, we're definitely being closed.
    #[cfg(not(test))]
    if marker.is_file() {
        return Ok(true);
    }

    let subdir = marker.parent().expect("we just pushed a child");

    // The existence of the SNAPSHOT_SUBDIR doesn't mean anything, so
    // just create it unconditionally: that's simpler than trying to
    // flush the NFS cache at each level of the hierarchy.
    //
    // Any error here will be bubbled up by the code downstream.
    let _ = std::fs::create_dir_all(subdir);

    // Open the directory, which happens to flush the NFS cache.
    if let Some(item) = subdir.read_dir()?.next() {
        // Maybe the only item in the directory is the marker, if so,
        // we're done.
        if item?.file_name() == IN_PROGRESS_MARKER {
            Ok(true)
        } else {
            // Otherwise, any negative cache has been cleared, and we can check
            // for the marker again.
            match std::fs::metadata(&marker) {
                Ok(_) => Ok(true),
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(false),
                // Avoid `Path::exists` in order to propagate non-ENOENT failures.
                Err(e) => Err(e),
            }
        }
    } else {
        // We only get here if the directory is empty.  That means the
        // marker is absent (for now).
        Ok(false)
    }
}

/// Starts the first step of closing an epoch subdirectory.  Returns
/// the deadline after which [`start_closing_epoch_subdir`] can act; the
/// call did something when `now` is strictly after the return value.
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
    mut subdir: PathBuf,
    now: VouchedTime,
) -> Result<time::PrimitiveDateTime> {
    let deadline = crate::get_epoch_close_time(&subdir)? + crate::CLOCK_ERROR_BOUND;

    if now.get_local_time() <= deadline {
        return Ok(deadline);
    }

    // OK, it's late enough, make sure the snapshot directory exists,
    // then make everything (except that subdirectory) read-only.

    // Flush the NFS cache.
    let _ = subdir.read_dir()?.next();

    // The snapshot subdir must exist; that's the only guaranteed
    // postcondition when `now` is late enough.
    subdir.push(SNAPSHOT_SUBDIR);
    std::fs::create_dir_all(&subdir)?;
    subdir.pop();

    fn make_read_only(target: &Path) -> Result<()> {
        let mut perms = std::fs::metadata(target)?.permissions();
        perms.set_readonly(true);
        std::fs::set_permissions(target, perms)
    }

    // Opportunistically attempts to make everything except the
    // SNAPSHOT_SUBDIR read-only. We ignore errors because this
    // is just a courtesy to writers.
    fn make_subdir_readonly(mut subdir: PathBuf) -> Result<()> {
        let _ = make_read_only(&subdir);
        for item in subdir.read_dir()?.flatten() {
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

    // Enter the snapshot subdirectory
    target.push(SNAPSHOT_SUBDIR);

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
    assert!(epoch_subdir_is_being_closed(
        target.parent().expect("we just pushed a subdir").to_owned()
    )?);

    // See if the summary file exists: if it does, we're done.
    {
        // Open the directory to flush the NFS cache.
        if let Some(item) = target.read_dir()?.next() {
            let item = item?;
            if item.file_name() == SUMMARY_FILE {
                return Ok(None);
            }
        }

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
    // bytes to `$SNAPSHOT_SUBDIR/$SUMMARY_FILE`.
    let mut summary: tempfile::NamedTempFile = tempfile::Builder::new()
        .prefix(SUMMARY_TMP_PREFIX)
        .tempfile_in(&target)?;

    // Go back to `subdir`
    target.pop();

    // Copy all the data files in `subdir` to `summary`
    for item in target.read_dir()? {
        let item = item?;
        assert_eq!(crate::LOG_EXTENSION, "log");
        if item.file_name().as_encoded_bytes().ends_with(b".log") {
            target.push(item.file_name());
            let mut src = std::fs::File::open(&target)?;
            std::io::copy(&mut src, summary.as_file_mut())?;
            target.pop();
        }
    }

    // The summary tempfile is now fully populated. We
    // want to publish it at `target`.
    target.push(SNAPSHOT_SUBDIR);
    target.push(SUMMARY_FILE);

    // Finalize what we wrote in `summary`.

    // Make it read-only, which should also flush on NFS (v3?).
    {
        let mut perms = summary.as_file().metadata()?.permissions();
        perms.set_readonly(true);
        summary.as_file_mut().set_permissions(perms)?;
    }

    if options.fsync {
        summary.as_file().sync_all()?;
    }

    // Close the file before persisting it, for close-to-open
    // consistency.
    summary.into_temp_path().persist_noclobber(&target)?;
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
    let mut target = subdir.clone();
    target.push(SNAPSHOT_SUBDIR);
    target.push(SUMMARY_FILE);

    // Quick check to see if we're already done here.
    let ret = if target.is_file() {
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
        // The file exists, let's see what we want to do to the
        // `SNAPSHOT_SUBDIR`.
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

/// epoch_subdir_is_being_closed should return false on an empty epoch directory.
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

/// epoch_subdir_is_being_closed should still return false when the snapshot subdirectory
/// exists, but the IN_PROGRESS_MARKER file is absent.
#[test]
fn test_being_closed_not_yet() {
    use test_dir::{DirBuilder, FileType, TestDir};
    use time::macros::datetime;

    let subdir = crate::construct_epoch_subdirectory(
        "./test_not_yet".into(),
        datetime!(2024-04-07 16:01:32),
    )
    .0
    .into_os_string()
    .into_string()
    .unwrap();
    assert_eq!(
        subdir,
        format!("./test_not_yet/2024-04-07/16/01:30-{:x}", 1712505697)
    );
    let temp = TestDir::temp()
        .create(&subdir, FileType::Dir)
        .create(&format!("{}/{}", &subdir, SNAPSHOT_SUBDIR), FileType::Dir);

    assert!(!epoch_subdir_is_being_closed(temp.path(&subdir)).unwrap());
}

/// epoch_subdir_is_being_closed should return true when the IN_PROGRESS_MARKER exists
/// in the SNAPSHOT_SUBDIR.
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
    let temp = TestDir::temp()
        .create(&subdir, FileType::Dir)
        .create(&format!("{}/{}", &subdir, SNAPSHOT_SUBDIR), FileType::Dir)
        .create(
            &format!("{}/{}/{}", &subdir, SNAPSHOT_SUBDIR, IN_PROGRESS_MARKER),
            FileType::EmptyFile,
        );

    assert!(epoch_subdir_is_being_closed(temp.path(&subdir)).unwrap());
}

/// epoch_subdir_is_being_closed should return true when the IN_PROGRESS_MARKER exists
/// in the SNAPSHOT_SUBDIR, even if there's extra stuff in the SNAPSHOT_SUBDIR.
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
        .create(&format!("{}/{}", &subdir, SNAPSHOT_SUBDIR), FileType::Dir)
        .create(
            &format!("{}/{}/00000dummy", &subdir, SNAPSHOT_SUBDIR),
            FileType::EmptyFile,
        )
        .create(
            &format!("{}/{}/{}", &subdir, SNAPSHOT_SUBDIR, IN_PROGRESS_MARKER),
            FileType::EmptyFile,
        );

    assert!(epoch_subdir_is_being_closed(temp.path(&subdir)).unwrap());
}

/// closing an epoch should always succeed when we have a SUMMARY_FILE,
/// even if the epoch isn't closed (the close-side code must avoid that
/// situation).
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
    let temp = TestDir::temp()
        .create(&subdir, FileType::Dir)
        .create(&format!("{}/{}", &subdir, SNAPSHOT_SUBDIR), FileType::Dir)
        .create(
            &format!("{}/{}/{}", &subdir, SNAPSHOT_SUBDIR, SUMMARY_FILE),
            FileType::EmptyFile,
        );

    assert!(!epoch_subdir_is_being_closed(temp.path(&subdir)).unwrap());

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    assert_eq!(
        close_epoch_subdir(
            temp.path(&subdir),
            crate::VouchedTime::new(
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
            crate::VouchedTime::new(
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

    // Let the Drop traits clean up
    let temp_dir = temp.path(&subdir);
    let mut perms = std::fs::metadata(&temp_dir).unwrap().permissions();
    #[allow(clippy::permissions_set_readonly_false)]
    perms.set_readonly(false);
    std::fs::set_permissions(&temp_dir, perms).unwrap();
}

/// The epoch is still open after a successful call to `start_closing_epoch_subdir`,
/// although we expect the directory and its files to be read-only.
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
            crate::VouchedTime::new(
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

    // The directory and its contents are read-only
    assert!(std::fs::metadata(temp.path(&subdir))
        .unwrap()
        .permissions()
        .readonly());
    assert!(
        std::fs::metadata(temp.path(&format!("{}/foo.log", &subdir)))
            .unwrap()
            .permissions()
            .readonly()
    );
    // But the snapshot subdir is still writable.
    assert!(
        !std::fs::metadata(temp.path(&format!("{}/{}", &subdir, SNAPSHOT_SUBDIR)))
            .unwrap()
            .permissions()
            .readonly()
    );

    // Let the Drop traits clean up
    let temp_dir = temp.path(&subdir);
    let mut perms = std::fs::metadata(&temp_dir).unwrap().permissions();
    #[allow(clippy::permissions_set_readonly_false)]
    perms.set_readonly(false);
    std::fs::set_permissions(&temp_dir, perms).unwrap();
}

/// An early call to `start_closing_epoch_subdir` should no-op and
/// return a deadline in the future.
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
    let now = crate::VouchedTime::new(
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
    let now = crate::VouchedTime::new(
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
    let now = crate::VouchedTime::new(
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

    // The directory and its contents are read-only
    assert!(std::fs::metadata(temp.path(&subdir))
        .unwrap()
        .permissions()
        .readonly());
    assert!(
        std::fs::metadata(temp.path(&format!("{}/foo.log", &subdir)))
            .unwrap()
            .permissions()
            .readonly()
    );
    // But the snapshot subdir is still writable.
    assert!(
        !std::fs::metadata(temp.path(&format!("{}/{}", &subdir, SNAPSHOT_SUBDIR)))
            .unwrap()
            .permissions()
            .readonly()
    );

    // Let the Drop traits clean up
    let temp_dir = temp.path(&subdir);
    let mut perms = std::fs::metadata(&temp_dir).unwrap().permissions();
    #[allow(clippy::permissions_set_readonly_false)]
    perms.set_readonly(false);
    std::fs::set_permissions(&temp_dir, perms).unwrap();
}

/// An early call to `close_epoch_subdir` should no-op and return a deadline in the future,
/// even its internal call to `start_closing_epoch_subdir` succeeds.
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

    // start_closing_epoch_subdir succeeds
    let now = crate::VouchedTime::new(
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

    // The directory and its contents are read-only
    assert!(std::fs::metadata(temp.path(&subdir))
        .unwrap()
        .permissions()
        .readonly());
    assert!(
        std::fs::metadata(temp.path(&format!("{}/foo.log", &subdir)))
            .unwrap()
            .permissions()
            .readonly()
    );
    // But the snapshot subdir is still writable.
    assert!(
        !std::fs::metadata(temp.path(&format!("{}/{}", &subdir, SNAPSHOT_SUBDIR)))
            .unwrap()
            .permissions()
            .readonly()
    );

    // Let the Drop traits clean up
    let temp_dir = temp.path(&subdir);
    let mut perms = std::fs::metadata(&temp_dir).unwrap().permissions();
    #[allow(clippy::permissions_set_readonly_false)]
    perms.set_readonly(false);
    std::fs::set_permissions(&temp_dir, perms).unwrap();
}

/// Closing an epoch with one log file should copy its contents to the summary file.
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

    // start_closing_epoch_subdir succeeds
    let now = crate::VouchedTime::new(
        datetime!(2024-04-07 16:01:39.95),
        1712505699000,
        vouch_params.vouch(1712505699000),
    )
    .unwrap();
    start_closing_epoch_subdir(temp.path(&subdir), now).expect("should succeed");

    // The epoch is not yet marked as being closed.
    assert!(!epoch_subdir_is_being_closed(temp.path(&subdir)).unwrap());

    let dummy_temp_file = format!(
        "{}/{}/{}12345",
        &subdir, SNAPSHOT_SUBDIR, SUMMARY_TMP_PREFIX
    );
    std::fs::File::create(temp.path(&dummy_temp_file)).expect("creation should succeed");

    // close_epoch_subdir should succeed.
    assert_eq!(
        close_epoch_subdir(temp.path(&subdir), now, CloseEpochOptions { fsync: true })
            .expect("should succeed"),
        None
    );

    // The epoch is now marked as being closed.
    assert!(epoch_subdir_is_being_closed(temp.path(&subdir)).unwrap());

    assert_eq!(
        std::fs::read(temp.path(&format!("{}/foo.log", &subdir))).unwrap(),
        std::fs::read(temp.path(&format!("{}/{}/{}", &subdir, SNAPSHOT_SUBDIR, SUMMARY_FILE)))
            .unwrap()
    );

    // The dummy file should have been cleaned up.
    assert!(!temp.path(&dummy_temp_file).exists());

    // Let the Drop traits clean up
    let temp_dir = temp.path(&subdir);
    let mut perms = std::fs::metadata(&temp_dir).unwrap().permissions();
    #[allow(clippy::permissions_set_readonly_false)]
    perms.set_readonly(false);
    std::fs::set_permissions(&temp_dir, perms).unwrap();
}

/// Closing an epoch with two log files should copy their contents to the summary file.
#[test]
fn test_close_two_files() {
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
    let now = crate::VouchedTime::new(
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

    let foo_bytes = std::fs::read(temp.path(&format!("{}/foo.log", &subdir))).unwrap();
    let bar_bytes = std::fs::read(temp.path(&format!("{}/bar.log", &subdir))).unwrap();
    let snap =
        std::fs::read(temp.path(&format!("{}/{}/{}", &subdir, SNAPSHOT_SUBDIR, SUMMARY_FILE)))
            .unwrap();
    // The order in which the logs appear in the SUMMARY_FILE is unspecified.
    let match_ab = snap == [&*foo_bytes, &*bar_bytes].concat();
    let match_ba = snap == [bar_bytes, foo_bytes].concat();
    assert!(match_ab | match_ba);

    // Let the Drop traits clean up
    let temp_dir = temp.path(&subdir);
    let mut perms = std::fs::metadata(&temp_dir).unwrap().permissions();
    #[allow(clippy::permissions_set_readonly_false)]
    perms.set_readonly(false);
    std::fs::set_permissions(&temp_dir, perms).unwrap();
}

/// Closing an epoch twice in a row should succeed and find the correct values.
#[test]
fn test_close_twice() {
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
    let now = crate::VouchedTime::new(
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
    let perms =
        std::fs::metadata(temp.path(&format!("{}/{}/{}", &subdir, SNAPSHOT_SUBDIR, SUMMARY_FILE)))
            .unwrap();
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

    let foo_bytes = std::fs::read(temp.path(&format!("{}/foo.log", &subdir))).unwrap();
    let bar_bytes = std::fs::read(temp.path(&format!("{}/bar.log", &subdir))).unwrap();
    let snap =
        std::fs::read(temp.path(&format!("{}/{}/{}", &subdir, SNAPSHOT_SUBDIR, SUMMARY_FILE)))
            .unwrap();
    // The order in which the logs appear in the SUMMARY_FILE is unspecified.
    let match_ab = snap == [&*foo_bytes, &*bar_bytes].concat();
    let match_ba = snap == [bar_bytes, foo_bytes].concat();
    assert!(match_ab | match_ba);
    assert_eq!(snap.len(), 100 + 80);

    // The epoch is marked as being closed.
    assert!(epoch_subdir_is_being_closed(temp.path(&subdir)).unwrap());

    // Let the Drop traits clean up
    let temp_dir = temp.path(&subdir);
    let mut perms = std::fs::metadata(&temp_dir).unwrap().permissions();
    #[allow(clippy::permissions_set_readonly_false)]
    perms.set_readonly(false);
    std::fs::set_permissions(&temp_dir, perms).unwrap();
}
