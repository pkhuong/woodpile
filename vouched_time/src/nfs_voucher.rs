//! The NFS vouched time backend uses a trusted filesystem's *ctime* to update
//! the time base.
//!
//! Most of the time, the time base can be updated off already opened files.
//! When the current time base seems far behind, this module can also trigger
//! an artificial mtime update.
//!
//! To use this module as a source of trusted base times for
//! [`crate::VouchedTime`], you must first add the path to the trusted paths
//! list.  This is done by calling [`add_trusted_path`] with the path for a
//! file on a filesystem with trusted ctime updates (e.g., a NFS server
//! similarly trusted by all peers). The `nfs_voucher` module will now trust
//! `ctime` for all files on the same device as that path.
//!
//! The current process must also have write access to the file at the trusted
//! path; that's used only to `touch` the file's atime, which forces a ctime
//! update).
//!
//! You can then pass [`get_base_time`] to [`crate::VouchedTime::now_or_die`]
//! to generate a fresh vouched time for the current time.  The
//! [`get_base_time`] function will perform I/O and block on some internal
//! locks to update the base time if it looks like the current base time would
//! result in a failure. Use [`get_base_time_unlocked`] to skip the I/O and
//! blocking, and always return the current base time, however stale it might
//! look.  This should only be used in niche situations where we've already
//! ensured the base time is up to date and blocking is forbidden.
//!
//! You may update the base time (and thue ensure [`get_base_time`] doesn't
//! block) by calling [`observe_file_time`] with a recently changed file on a
//! trusted device.  In general, it's always safe to call
//! [`observe_file_time`] with any file: the function disregards files on
//! untrusted devices, and base time updates are only applied when they
//! advance the base time.
use std::collections::BTreeMap;
use std::io::Result;
use std::path::PathBuf;
use std::sync::RwLock;

use crate::AtomicBaseTime;

// Trusted paths map from device id to path that is safe to touch.
static TRUSTED_PATHS: RwLock<BTreeMap<u64, PathBuf>> = RwLock::new(BTreeMap::new());

static BASE_TIME: AtomicBaseTime = AtomicBaseTime::new();

/// Adds `path` to the set of trusted paths for the NFS vouching module.
///
/// Any file stored on the same device as `path` is assumed to have a
/// trustworthy ctime.
///
/// The current process must have write access to that path, to force ctime updates.
#[inline(never)]
pub fn add_trusted_path(path: PathBuf) -> Result<()> {
    use std::os::unix::fs::MetadataExt;

    let file = std::fs::File::options()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .open(&path)?;
    let stat = file.metadata()?;
    let dev = stat.dev();
    // Check that we can actually use this path for base time updates.
    //
    // This call may fail for I/O, but should not fail
    // because the device isn't trusted (i.e., no `Ok(None)`).
    let _ = update_base_time(
        &file,
        UpdateOptions {
            blocking: false,
            touch: true,
            extra_device: Some(dev),
        },
    )?
    .1
    .expect("Path is trusted.");

    TRUSTED_PATHS.write().unwrap().insert(dev, path);
    Ok(())
}

const DEFAULT_LEEWAY_MS: u64 = 2 * crate::MAX_FORWARD_DISCREPANCY_MS / 3;
thread_local! {
    /// The last time we updated the base time, or decided we didn't need to.
    static LAST_UPDATE: std::cell::Cell<Option<std::time::Instant>> = Default::default();
}

/// Returns whether it's worth refreshing the current base time, because it's
/// (approximately) older than `leeway_ms`.
///
/// If `leeway_ms` is None, use an appropriate default.
pub fn should_refresh_base_time(leeway_ms: Option<u64>, now: Option<time::OffsetDateTime>) -> bool {
    if now.is_none() {
        if let Some(last_update) = LAST_UPDATE.get() {
            // We don't need that kind of precision, just bail early.
            if last_update.elapsed() < std::time::Duration::from_millis(100) {
                // TODO: should jitter
                return false;
            }
        }
    }

    // Either we'll update the base time, or we'll decide it's good enough; in
    // either case, we shouldn't need to update again for a while.
    LAST_UPDATE.set(Some(std::time::Instant::now()));

    let leeway_ms = leeway_ms.unwrap_or(DEFAULT_LEEWAY_MS);
    let now = now.unwrap_or_else(time::OffsetDateTime::now_utc);
    let wanted: u64 = (now.unix_timestamp_nanos() / 1_000_000).clamp(0, u64::MAX as i128) as u64;
    let (base_ms, _voucher) = get_base_time_unlocked(now).expect("_unlocked does not fail");

    // Refresh if the base time looks stale and we have some trusted paths to
    // refresh with.
    //
    // TODO: should jitter a little around here.
    wanted.saturating_sub(base_ms) > leeway_ms && !TRUSTED_PATHS.read().unwrap().is_empty()
}

/// Given an arbitrary file, attempts to advance the base time based on the
/// file's ctime.
///
/// Returns the base time and voucher derived from the file if it is on a
/// trusted device (see [`add_trusted_path`]) and the `stat` call succeeded.
/// That base time may differ from the one stored in memory under contention
/// or if the file's ctime is older than the current base time.
///
/// Returns `Ok(None)` if the file is not on a trusted device, and propagates
/// any I/O error from `stat` otherwise.
///
/// This function `stat`s the file, but is otherwise wait-free.
#[inline(always)]
pub fn observe_file_time(
    file: &std::fs::File,
) -> Result<(std::fs::Metadata, Option<(u64, raffle::Voucher)>)> {
    update_base_time(
        file,
        UpdateOptions {
            blocking: false,
            touch: false,
            extra_device: None,
        },
    )
}

/// Attempts to advance the base time based on `file`'s ctime, if it makes
/// sense to refresh the base time (no-ops otherwise).
pub fn maybe_observe_file_time(file: &std::fs::File) {
    if should_refresh_base_time(None, None) {
        let _ = observe_file_time(file);
    }
}

/// Attempts to update the base time if it is already stale (more than 1000
/// milliseconds behind).
#[inline(never)]
pub fn scan_base_time() -> Result<()> {
    // We want to be more aggressive than the default leeway, when explicitly
    // requesting a base time update.
    const _: () = assert!(1000 < DEFAULT_LEEWAY_MS);
    if should_refresh_base_time(Some(1000), None) {
        scan_for_base_time_impl()?;
    }

    Ok(())
}

/// Returns the current base time and voucher.
///
/// Does not attempt to move the base time forward if it looks stale,
/// but also never fails.
///
/// This function is lock-free.
#[inline(always)]
pub fn get_base_time_unlocked(_now: time::OffsetDateTime) -> Result<(u64, raffle::Voucher)> {
    Ok(BASE_TIME.snapshot())
}

/// Attempts to return an up-to-date base time and voucher.
///
/// Returns the current base time if it looks more than recent enough to match
/// the current time. Otherwise, attempts to update the base time by touching
/// some of the trusted paths and returns the first successful update.
///
/// This function fails when all update attempts fail, and when no trusted
/// path is defined.
///
/// This function is lock-free when the base time is up to date; if the base
/// time must be updated, that can be slow, and requires I/O and locking.
pub fn get_base_time(now: time::OffsetDateTime) -> Result<(u64, raffle::Voucher)> {
    if should_refresh_base_time(None, Some(now)) {
        scan_for_base_time_impl()
    } else {
        get_base_time_unlocked(now)
    }
}

#[inline(never)]
fn scan_for_base_time_impl() -> Result<(u64, raffle::Voucher)> {
    let mut err: Option<std::io::Error> = None;
    let trusted_paths = TRUSTED_PATHS.read().unwrap();
    for path in trusted_paths.values() {
        let file = std::fs::File::options()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(path)?;
        match update_base_time(
            &file,
            UpdateOptions {
                blocking: true,
                touch: true,
                extra_device: None,
            },
        ) {
            Ok((_, Some(update))) => return Ok(update),
            Ok(_) => {}
            Err(e) => {
                err.get_or_insert(e);
            }
        }
    }

    Err(err.unwrap_or_else(|| {
        std::io::Error::other(
            "no nfs_voucher trusted path (or all paths moved to a different device)",
        )
    }))
}

struct UpdateOptions {
    blocking: bool,
    touch: bool,
    extra_device: Option<u64>,
}

#[inline(never)]
fn update_base_time(
    file: &std::fs::File,
    options: UpdateOptions,
) -> Result<(std::fs::Metadata, Option<(u64, raffle::Voucher)>)> {
    use std::os::unix::fs::MetadataExt;

    if options.touch {
        file.set_times(std::fs::FileTimes::new().set_accessed(std::time::SystemTime::now()))?;
    }

    let begin = std::time::Instant::now();

    let stat = file.metadata()?;
    let dev = stat.dev();
    if !TRUSTED_PATHS.read().unwrap().contains_key(&dev) && options.extra_device != Some(dev) {
        return Ok((stat, None));
    }
    const VOUCH_PARAMS: raffle::VouchingParameters = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let millis_since_epoch = (stat.ctime() as u64)
        .saturating_mul(1000)
        .saturating_add((stat.ctime_nsec() as u64) / 1_000_000);
    let update = (millis_since_epoch, VOUCH_PARAMS.vouch(millis_since_epoch));

    let updated = if options.blocking {
        BASE_TIME.update(update);
        true
    } else {
        BASE_TIME.try_update(update)
    };

    if updated {
        LAST_UPDATE.set(Some(begin));
    }

    Ok((stat, Some(update)))
}

#[cfg(not(miri))]
#[test]
fn smoke_test() {
    use test_dir::{DirBuilder, TestDir};

    let temp = TestDir::temp();
    add_trusted_path(temp.path("test.file")).expect("should succeed");
    let _ = crate::VouchedTime::now_or_die(get_base_time_unlocked);

    // The base time is now invalid.
    std::thread::sleep(std::time::Duration::from_secs(4));

    // Confirm it's invalid.
    assert!(crate::VouchedTime::now(get_base_time_unlocked).is_err());
    // But we can pull the base time forward.
    let _ = crate::VouchedTime::now_or_die(get_base_time);
    let _ = crate::VouchedTime::now_or_die(get_base_time_unlocked);

    // Invalidate the base time again.
    std::thread::sleep(std::time::Duration::from_secs(4));
    assert!(crate::VouchedTime::now(get_base_time_unlocked).is_err());

    std::fs::write(temp.path("some_random_file"), b"123").unwrap();
    let file = std::fs::File::open(temp.path("some_random_file")).unwrap();
    // Update base time
    let _ = observe_file_time(&file).unwrap();
    let _ = crate::VouchedTime::now_or_die(get_base_time_unlocked);
}
