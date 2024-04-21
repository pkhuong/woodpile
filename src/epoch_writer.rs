use std::ffi::OsStr;
use std::io::Result;
use std::path::PathBuf;
use time::PrimitiveDateTime;

use crate::close;
use crate::vouched_time::VouchedTime;
use crate::EPOCH_WRITE_LEEWAY;

/// Option struct for [`EpochWriter::open`].
#[derive(Clone, Copy, Debug, Default)]
pub struct EpochWriterOptions {
    /// Whether to fsync file and directory data.  The default is false,
    /// because we expect to target (reliable) NFS with close-to-open
    /// consistency.
    pub fsync: bool,
}

/// An [`EpochWriter`] implements the low-level protocol to write
/// *one* timestamped record to the corresponding epoch.
///
/// [`EpochWriter::open`] is fallible, but idempotent.  Each record
/// should be self-delimiting and self-validating; this will let
/// readers detect and skip aborted writes.  That in turn lets writes
/// be treated as idempotent until the final bytes.
///
/// To write a record, one must:
///
/// 1. [`EpochWriter::open()`] a writer in the target directory, with
///     a filename not used by any concurrent writer (e.g., that includes
///     the current hostname), and a [`VouchedTime`] for the record's
///     timestamp.
///
/// 2. Write all but the final bytes of the record (i.e., without the
///    key bytes necessary for a valid record) to [`EpochWriter::file()`].
///
/// 3. Confirm that the write deadline hasn't passed yet, with
///    [`EpochWriter::check_deadline()`].
///
/// Up until this point, the record isn't actually valid, so the operations
/// are idempotent.
///
/// 4. Actually write out the final bytes of the record to
///    [`EpochWriter::file()`].
///
/// At and after this point, any failure is impossible to interpret:
/// maybe all the written bytes have made / will make it to the
/// epoch's snapshot, or maybe they won't.  The only way to know for
/// sure is to close the epoch and check.
///
/// 5. Make sure the newly written record is visible with
///    [`EpochWriter::close()`].
///
/// 6. Check that the written record made it before the epoch
///    was closed with [`EpochCommit::confirm()`].
///
/// Success here means the record is globally visible and will
/// definitely make it to the epoch's eventual snapshot.  Failure at
/// steps 5 or 6 is impossible to interpret: we may or may not have
/// managed to write all the bytes just before the epoch was closed
/// and snapshotted.  Failure at step 4 *may* be interpretable (e.g.,
/// if we know not all the bytes were written), but it's probably
/// simpler to always treat it like steps 5 and 6.
///
/// When any of the (potentially) non-idempotent steps 4-6 fail, the
/// only way to determine what happened to the newly written record is
/// to ensure the epoch is closed, and read the snapshot.  The easiest
/// way to achieve that is usually to invoke the crash recovery code
/// path (e.g., by panicking).
#[derive(Debug)]
pub struct EpochWriter {
    path: PathBuf,
    dst: std::fs::File,
    deadline: PrimitiveDateTime,
    options: EpochWriterOptions,
}

/// An [`EpochCommit`] is a `must_use` type to remind API users that
/// even a successful [`EpochWriter::close()`] must be
/// [`EpochCommit::confirm()`]ed to know whether the record is
/// definitely globally visible.
#[must_use = "EpochCommit must be `confirm()`ed."]
pub struct EpochCommit {
    path: PathBuf,
    deadline: PrimitiveDateTime,
}

impl EpochWriter {
    /// Opens "filename.log" under the current time bucket for `directory`.
    /// This constructor accepts a [`VouchedTime`] because an incorrect `now`
    /// value may cause strange behaviour in other processes (for all other
    /// [`time::PrimitiveDateTime`] arguments, an incorrect value only result in
    /// a process lying to itself about the fate of its writes).
    ///
    /// Returns an [`EpochWriter`], or an error if anything went wrong.
    ///
    /// Any I/O performed before returning the error is idempotent.
    pub fn open(
        directory: PathBuf,
        filename: impl AsRef<OsStr>,
        now: VouchedTime,
        options: EpochWriterOptions,
    ) -> Result<EpochWriter> {
        let (mut path, deadline) =
            crate::construct_epoch_subdirectory(directory, now.get_local_time());

        // XXX: we should probably apply opt-in fsync here...
        std::fs::create_dir_all(&path)?;

        path.push(filename.as_ref());
        path.set_extension(crate::LOG_EXTENSION);

        let dst = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&path)?;

        if options.fsync {
            // fsync the directory to make sure the file is visible.
            //
            // XXX: maybe we should only do this if the file is empty?
            std::fs::File::open(path.parent().unwrap_or(std::path::Path::new("/")))?.sync_all()?;
        }

        Ok(EpochWriter {
            path,
            dst,
            deadline,
            options,
        })
    }

    /// Checks whether `now` is early enough compared to the deadline that we
    /// can still expect to successfully commit our write.  The value for `now`
    /// should be as up to date as possible.
    ///
    /// Returns an error iff `now` *may be* too late; in that case, an
    /// arbitrary subset of the bytes written so far may (eventually)
    /// be globally visible.
    pub fn check_deadline(&self, now: time::PrimitiveDateTime) -> Result<()> {
        if now >= self.deadline {
            Err(std::io::Error::other(format!(
                "EpochWriter past internal deadline; writes will likely fail. path={:?}",
                self.path
            )))
        } else {
            Ok(())
        }
    }

    /// Returns the underlying file object.  The final write to a
    /// [`EpochWriter::file()`] should be for just enough bytes to
    /// complete a valid record and performed only after a successful
    /// call to [`EpochWriter::check_deadline()`].
    pub fn file(&mut self) -> &mut std::fs::File {
        &mut self.dst
    }

    /// Attempts to close the destination file, which also makes the
    /// write visible on shared storage.
    ///
    /// On success, the return value must still be
    /// [`EpochCommit::confirm()`]ed.
    ///
    /// On error, an arbitrary subset of the written bytes may
    /// (eventually) be globally visible.
    pub fn close(self) -> Result<EpochCommit> {
        use std::os::fd::IntoRawFd;

        let file = self.dst;
        let ret = EpochCommit {
            path: self.path,
            deadline: self.deadline,
        };

        if self.options.fsync {
            file.sync_all()?;
        }

        nix::unistd::close(file.into_raw_fd())?;
        Ok(ret)
    }
}

/// An [`EpochCommit`] object serves as a reminder that the successful
/// result of [`EpochWriter::close()`] must still be
/// [`EpochCommit::confirm()`]ed.
impl EpochCommit {
    /// Determines whether a call to [`EpochWriter::close()`]
    /// definitely completed before the epoch was closed.  The value
    /// for `now` should be as up-to-date as possible, and taken
    /// *after* [`EpochWriter::close()`] has returned.
    ///
    /// When this method returns `()`, all the bytes written through
    /// the closed [`EpochWriter`] will be part of the epoch's global
    /// snapshot.
    ///
    /// On error, an arbitrary subset of the written bytes may
    /// (eventually) be part of the epoch's global snapshot.
    pub fn confirm(self, now: time::PrimitiveDateTime) -> Result<()> {
        let path = self.path;
        let parent = path
            .parent()
            .expect("we build a multi-level directory structure");
        let deadline = self.deadline;

        // If we're clearly before the time at which the epoch would
        // be snapshotted, it's all good.  Same if the subdirectory
        // isn't being closed yet.
        //
        // Otherwise, we don't know: the record could have made it to
        // the snapshot or not.  It's probably easiest to panic and
        // enter crash recovery logic.
        if now < deadline.saturating_add(EPOCH_WRITE_LEEWAY)
            || !close::epoch_subdir_is_being_closed(parent.to_owned())?
        {
            // We're way before the deadline, it's all good.
            Ok(())
        } else {
            Err(std::io::Error::other(format!(
                "EpochWriter closed write late.  Result may or may not be visible. path={:?}",
                path
            )))
        }
    }
}

// Test the simple happy path: open a log file, write some bytes, commit wayy before the deadline.
// Close the epoch, find the bytes in there.
#[test]
fn test_happy_path() {
    use std::io::Write;
    use std::path::Path;
    use test_dir::{DirBuilder, TestDir};
    use time::macros::datetime;

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let now = VouchedTime::new(
        datetime!(2024-04-21 00:58:46.1),
        1713661126000,
        vouch_params.vouch(1713661126000),
    )
    .unwrap();

    let temp = TestDir::temp();
    let subdir = format!("./happy/2024-04-21/00/58:45-{:x}", 1713661132);
    let deadline = time::OffsetDateTime::from_unix_timestamp(1713661132).unwrap();
    let deadline = time::PrimitiveDateTime::new(deadline.date(), deadline.time());

    assert_eq!(
        crate::construct_epoch_subdirectory(
            Path::new("./happy").to_owned(),
            datetime!(2024-04-21 00:58:46.1)
        ),
        (Path::new(&subdir).to_owned(), deadline)
    );

    let mut writer = EpochWriter::open(
        temp.path("./happy"),
        "records",
        now,
        EpochWriterOptions { fsync: false },
    )
    .expect("open should succeed");

    writer
        .check_deadline(datetime!(2024-04-21 00:58:47.1))
        .expect("should be before deadline");

    writer.file().write_all(b"123").expect("write must succeed");

    writer
        .check_deadline(datetime!(2024-04-21 00:58:48.1))
        .expect("should still be before deadline");

    writer.file().write_all(b"456").expect("write must succeed");

    let commit = writer.close().expect("close should succeed");
    commit
        .confirm(datetime!(2024-04-21 00:58:49.1))
        .expect("confirm should succeed");

    assert_eq!(
        std::fs::read(temp.path(&format!("{}/records.log", subdir))).expect("file should exist"),
        b"123456"
    );

    // Close the epoch
    assert_eq!(
        crate::close::close_epoch_subdir(
            temp.path(&subdir),
            VouchedTime::new(
                datetime!(2024-04-21 00:58:54.95),
                1713661134000,
                vouch_params.vouch(1713661134000),
            )
            .unwrap(),
            crate::close::CloseEpochOptions { fsync: false }
        )
        .expect("must succeed"),
        None
    );

    assert_eq!(
        std::fs::read(temp.path(&format!("{}/snapshot/100summary", subdir)))
            .expect("summary file should exist"),
        b"123456"
    );

    // Let the Drop traits clean up
    let temp_dir = temp.path(&subdir);
    let mut perms = std::fs::metadata(&temp_dir).unwrap().permissions();
    #[allow(clippy::permissions_set_readonly_false)]
    perms.set_readonly(false);
    std::fs::set_permissions(&temp_dir, perms).unwrap();
}

// Make sure we can append to a pre-existing log file.
#[test]
fn test_append() {
    use std::io::Write;
    use std::path::Path;
    use test_dir::{DirBuilder, TestDir};
    use time::macros::datetime;

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let now = VouchedTime::new(
        datetime!(2024-04-21 00:58:46.1),
        1713661126000,
        vouch_params.vouch(1713661126000),
    )
    .unwrap();

    let temp = TestDir::temp();
    let subdir = format!("./append/2024-04-21/00/58:45-{:x}", 1713661132);
    let deadline = time::OffsetDateTime::from_unix_timestamp(1713661132).unwrap();
    let deadline = time::PrimitiveDateTime::new(deadline.date(), deadline.time());

    assert_eq!(
        crate::construct_epoch_subdirectory(
            Path::new("./append").to_owned(),
            datetime!(2024-04-21 00:58:46.1)
        ),
        (Path::new(&subdir).to_owned(), deadline)
    );

    let mut writer = EpochWriter::open(
        temp.path("./append"),
        "multi-records",
        now,
        EpochWriterOptions { fsync: false },
    )
    .expect("open should succeed");
    writer.file().write_all(b"123").expect("write must succeed");
    writer
        .close()
        .expect("close should succeed")
        .confirm(datetime!(2024-04-21 00:58:46.2))
        .expect("confirm should succeed");

    let mut writer = EpochWriter::open(
        temp.path("./append"),
        "multi-records",
        now,
        EpochWriterOptions { fsync: false },
    )
    .expect("open should succeed");
    writer.file().write_all(b"456").expect("write must succeed");
    writer
        .close()
        .expect("close should succeed")
        .confirm(datetime!(2024-04-21 00:58:46.2))
        .expect("confirm should succeed");

    assert_eq!(
        std::fs::read(temp.path(&format!("{}/multi-records.log", subdir)))
            .expect("file should exist"),
        b"123456"
    );
}

// Tickle the `fsync: true` code
#[test]
fn test_fsync_path() {
    use std::io::Write;
    use std::path::Path;
    use test_dir::{DirBuilder, TestDir};
    use time::macros::datetime;

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let now = VouchedTime::new(
        datetime!(2024-04-21 00:58:46.1),
        1713661126000,
        vouch_params.vouch(1713661126000),
    )
    .unwrap();

    let temp = TestDir::temp();
    let subdir = format!("./fsync/2024-04-21/00/58:45-{:x}", 1713661132);
    let deadline = time::OffsetDateTime::from_unix_timestamp(1713661132).unwrap();
    let deadline = time::PrimitiveDateTime::new(deadline.date(), deadline.time());

    assert_eq!(
        crate::construct_epoch_subdirectory(
            Path::new("./fsync").to_owned(),
            datetime!(2024-04-21 00:58:46.1)
        ),
        (Path::new(&subdir).to_owned(), deadline)
    );

    let mut writer = EpochWriter::open(
        temp.path("./fsync"),
        "records",
        now,
        EpochWriterOptions { fsync: true },
    )
    .expect("open should succeed");

    writer
        .check_deadline(datetime!(2024-04-21 00:58:47.1))
        .expect("should be before deadline");

    writer.file().write_all(b"123").expect("write must succeed");

    writer
        .check_deadline(datetime!(2024-04-21 00:58:48.1))
        .expect("should still be before deadline");

    writer.file().write_all(b"456").expect("write must succeed");

    let commit = writer.close().expect("close should succeed");
    commit
        .confirm(datetime!(2024-04-21 00:58:49.1))
        .expect("confirm should succeed");

    assert_eq!(
        std::fs::read(temp.path(&format!("{}/records.log", subdir))).expect("file should exist"),
        b"123456"
    );

    // Let the Drop traits clean up
    let temp_dir = temp.path(&subdir);
    let mut perms = std::fs::metadata(&temp_dir).unwrap().permissions();
    #[allow(clippy::permissions_set_readonly_false)]
    perms.set_readonly(false);
    std::fs::set_permissions(&temp_dir, perms).unwrap();
}

// Confirm that `check_deadline()` does the thing.
#[test]
fn test_late_path() {
    use std::path::Path;
    use test_dir::{DirBuilder, TestDir};
    use time::macros::datetime;

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let now = VouchedTime::new(
        datetime!(2024-04-21 00:58:46.1),
        1713661126000,
        vouch_params.vouch(1713661126000),
    )
    .unwrap();

    let temp = TestDir::temp();
    let subdir = format!("./late/2024-04-21/00/58:45-{:x}", 1713661132);
    let deadline = time::OffsetDateTime::from_unix_timestamp(1713661132).unwrap();
    let deadline = time::PrimitiveDateTime::new(deadline.date(), deadline.time());

    assert_eq!(
        crate::construct_epoch_subdirectory(
            Path::new("./late").to_owned(),
            datetime!(2024-04-21 00:58:46.1)
        ),
        (Path::new(&subdir).to_owned(), deadline)
    );

    let writer = EpochWriter::open(
        temp.path("./late"),
        "records",
        now,
        EpochWriterOptions { fsync: false },
    )
    .expect("open should succeed");

    writer
        .check_deadline(datetime!(2024-04-21 00:58:50))
        .expect("expected regular deadline");
    writer
        .check_deadline(datetime!(2024-04-21 00:58:51.999))
        .expect("should be before deadline");

    // These are both at/after the deadline
    assert!(writer
        .check_deadline(datetime!(2024-04-21 00:58:52))
        .is_err());
    assert!(writer
        .check_deadline(datetime!(2024-04-21 00:58:53))
        .is_err());
}

// Exercise the lucky path, where the commit is late, but still before
// the closing process has begun.
#[test]
fn test_late_commit() {
    use std::io::Write;
    use std::path::Path;
    use test_dir::{DirBuilder, TestDir};
    use time::macros::datetime;

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let now = VouchedTime::new(
        datetime!(2024-04-21 00:58:46.1),
        1713661126000,
        vouch_params.vouch(1713661126000),
    )
    .unwrap();

    let temp = TestDir::temp();
    let subdir = format!("./late/2024-04-21/00/58:45-{:x}", 1713661132);
    let deadline = time::OffsetDateTime::from_unix_timestamp(1713661132).unwrap();
    let deadline = time::PrimitiveDateTime::new(deadline.date(), deadline.time());

    assert_eq!(
        crate::construct_epoch_subdirectory(
            Path::new("./late").to_owned(),
            datetime!(2024-04-21 00:58:46.1)
        ),
        (Path::new(&subdir).to_owned(), deadline)
    );

    let mut writer = EpochWriter::open(
        temp.path("./late"),
        "records",
        now,
        EpochWriterOptions { fsync: false },
    )
    .expect("open should succeed");

    writer
        .file()
        .write_all(b"123456")
        .expect("write must succeed");

    let commit = writer.close().expect("close should succeed");
    commit
        .confirm(datetime!(2024-04-21 00:59:49.1))
        .expect("confirm should succeed, despite slow commit");

    assert_eq!(
        std::fs::read(temp.path(&format!("{}/records.log", subdir))).expect("file should exist"),
        b"123456"
    );

    // Let the Drop traits clean up
    let temp_dir = temp.path(&subdir);
    let mut perms = std::fs::metadata(&temp_dir).unwrap().permissions();
    #[allow(clippy::permissions_set_readonly_false)]
    perms.set_readonly(false);
    std::fs::set_permissions(&temp_dir, perms).unwrap();
}

// Confirm that `open()` calls are rejected after a preliminary close.
#[test]
fn test_open_after_close() {
    use std::io::Write;
    use std::path::Path;
    use test_dir::{DirBuilder, TestDir};
    use time::macros::datetime;

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let now = VouchedTime::new(
        datetime!(2024-04-21 00:58:46.1),
        1713661126000,
        vouch_params.vouch(1713661126000),
    )
    .unwrap();

    let temp = TestDir::temp();
    let subdir = format!("./open_after_close/2024-04-21/00/58:45-{:x}", 1713661132);
    let deadline = time::OffsetDateTime::from_unix_timestamp(1713661132).unwrap();
    let deadline = time::PrimitiveDateTime::new(deadline.date(), deadline.time());

    assert_eq!(
        crate::construct_epoch_subdirectory(
            Path::new("./open_after_close").to_owned(),
            datetime!(2024-04-21 00:58:46.1)
        ),
        (Path::new(&subdir).to_owned(), deadline)
    );

    let mut writer = EpochWriter::open(
        temp.path("./open_after_close"),
        "first",
        now,
        EpochWriterOptions { fsync: false },
    )
    .expect("open should succeed");
    writer.file().write_all(b"123").expect("write must succeed");
    writer
        .close()
        .expect("close should succeed")
        .confirm(datetime!(2024-04-21 00:58:49.1))
        .expect("confirm should succeed");

    crate::close::start_closing_epoch_subdir(
        temp.path(&subdir),
        VouchedTime::new(
            datetime!(2024-04-21 00:58:54.95),
            1713661134000,
            vouch_params.vouch(1713661134000),
        )
        .unwrap(),
    )
    .expect("must succeed");

    // Reopening file should fail
    assert!(EpochWriter::open(
        temp.path("./open_after_close"),
        "first",
        now,
        EpochWriterOptions { fsync: false },
    )
    .is_err());
    // Opening new file should fail
    assert!(EpochWriter::open(
        temp.path("./open_after_close"),
        "second",
        now,
        EpochWriterOptions { fsync: false },
    )
    .is_err());

    assert_eq!(
        std::fs::read(temp.path(&format!("{}/first.log", subdir))).expect("file should exist"),
        b"123"
    );

    // Let the Drop traits clean up
    let temp_dir = temp.path(&subdir);
    let mut perms = std::fs::metadata(&temp_dir).unwrap().permissions();
    #[allow(clippy::permissions_set_readonly_false)]
    perms.set_readonly(false);
    std::fs::set_permissions(&temp_dir, perms).unwrap();
}

// Confirm that `commit` after close fails.
#[test]
fn test_commit_after_close() {
    use std::io::Write;
    use std::path::Path;
    use test_dir::{DirBuilder, TestDir};
    use time::macros::datetime;

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let now = VouchedTime::new(
        datetime!(2024-04-21 00:58:46.1),
        1713661126000,
        vouch_params.vouch(1713661126000),
    )
    .unwrap();

    let temp = TestDir::temp();
    let subdir = format!("./commit_after_close/2024-04-21/00/58:45-{:x}", 1713661132);
    let deadline = time::OffsetDateTime::from_unix_timestamp(1713661132).unwrap();
    let deadline = time::PrimitiveDateTime::new(deadline.date(), deadline.time());

    assert_eq!(
        crate::construct_epoch_subdirectory(
            Path::new("./commit_after_close").to_owned(),
            datetime!(2024-04-21 00:58:46.1)
        ),
        (Path::new(&subdir).to_owned(), deadline)
    );

    let mut writer = EpochWriter::open(
        temp.path("./commit_after_close"),
        "first",
        now,
        EpochWriterOptions { fsync: false },
    )
    .expect("open should succeed");
    writer.file().write_all(b"123").expect("write must succeed");
    let commit = writer.close().expect("close should succeed");

    assert_eq!(
        crate::close::close_epoch_subdir(
            temp.path(&subdir),
            VouchedTime::new(
                datetime!(2024-04-21 00:58:54.95),
                1713661134000,
                vouch_params.vouch(1713661134000),
            )
            .unwrap(),
            crate::close::CloseEpochOptions { fsync: false }
        )
        .expect("must succeed"),
        None
    );

    // commit should fail
    assert!(commit.confirm(datetime!(2024-04-21 00:58:55.1)).is_err());

    // Let the Drop traits clean up
    let temp_dir = temp.path(&subdir);
    let mut perms = std::fs::metadata(&temp_dir).unwrap().permissions();
    #[allow(clippy::permissions_set_readonly_false)]
    perms.set_readonly(false);
    std::fs::set_permissions(&temp_dir, perms).unwrap();
}

// Confirm that [`EpochWriter::close()`] after epoch close fails...
// at the commit step.
#[test]
fn test_close_after_close() {
    use std::io::Write;
    use std::path::Path;
    use test_dir::{DirBuilder, TestDir};
    use time::macros::datetime;

    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let now = VouchedTime::new(
        datetime!(2024-04-21 00:58:46.1),
        1713661126000,
        vouch_params.vouch(1713661126000),
    )
    .unwrap();

    let temp = TestDir::temp();
    let subdir = format!("./commit_after_close/2024-04-21/00/58:45-{:x}", 1713661132);
    let deadline = time::OffsetDateTime::from_unix_timestamp(1713661132).unwrap();
    let deadline = time::PrimitiveDateTime::new(deadline.date(), deadline.time());

    assert_eq!(
        crate::construct_epoch_subdirectory(
            Path::new("./commit_after_close").to_owned(),
            datetime!(2024-04-21 00:58:46.1)
        ),
        (Path::new(&subdir).to_owned(), deadline)
    );

    let mut writer = EpochWriter::open(
        temp.path("./commit_after_close"),
        "first",
        now,
        EpochWriterOptions { fsync: false },
    )
    .expect("open should succeed");
    writer.file().write_all(b"123").expect("write must succeed");
    assert_eq!(
        crate::close::close_epoch_subdir(
            temp.path(&subdir),
            VouchedTime::new(
                datetime!(2024-04-21 00:58:54.95),
                1713661134000,
                vouch_params.vouch(1713661134000),
            )
            .unwrap(),
            crate::close::CloseEpochOptions { fsync: false }
        )
        .expect("must succeed"),
        None
    );

    let commit = writer.close().expect("close should succeed");

    // commit should fail now
    assert!(commit.confirm(datetime!(2024-04-21 00:58:55.1)).is_err());

    // Let the Drop traits clean up
    let temp_dir = temp.path(&subdir);
    let mut perms = std::fs::metadata(&temp_dir).unwrap().permissions();
    #[allow(clippy::permissions_set_readonly_false)]
    perms.set_readonly(false);
    std::fs::set_permissions(&temp_dir, perms).unwrap();
}
