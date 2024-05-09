pub mod close;
pub mod epoch_writer;
pub mod hcobs;
mod owning_iovec;
pub mod sliding_deque;
pub mod sorted_deque;
mod vouched_time;

use std::io::Result;
use std::path::Path;
use std::path::PathBuf;
use time::Duration;

pub use owning_iovec::AnchoredSlice;
pub use owning_iovec::ByteArena;
pub use owning_iovec::OwningIovec;
pub use vouched_time::VouchedTime;
pub use vouched_time::MAX_BACKWARD_DISCREPANCY_MS;
pub use vouched_time::MAX_FORWARD_DISCREPANCY_MS;

/// We assume any two clocks differ by at most this many seconds.  We
/// try to avoid crashes when the actual error exceeds this value, but
/// there will be strange behaviour.
///
/// This error bound accounts for the maximum deterministic difference
/// of 1 second around leap seconds (each clock may be in the
/// "timezone" before or after the leap second, or smeared in the
/// middle), as well as clock synchronisation error on both sides.
///
/// The maximum round-trip times between two AWS regions is around
/// 400 ms, so a whole second of total clock error seems generous.
pub const CLOCK_ERROR_BOUND: Duration = Duration::new(2, 0);

/// The period at which we open a new epoch.  For example, the current
/// value for 5 means that we'll open an epoch at the top of the hour,
/// 00:00, then 5 second later at 00:05, etc.  It makes our life
/// simpler, especially around pea seconds, if this value is a factor
/// of 86400 (the number of seconds in a day), and at least 2.
const EPOCH_PERIOD: u32 = 5;

/// The amount of time we're allowed to use an epoch for writing.  This
/// is slightly more than the period to help slower writers, and to let
/// implementations delay creating new epochs for a little while and
/// avoid a coordinated DDoS.
///
/// At this point, closers are allowed to give an advance warning to
/// writers that the epoch is about to close.
pub const EPOCH_WRITE_DURATION: Duration = Duration::new(7, 0);

/// The amount of time an epoch may still be used for writes after
/// [`EPOCH_WRITE_DURATION`]. This leeway gives slow writers extra room.
///
/// Only after that time are closers allowed to start the snapshotting
/// process, and thus reject late writes.
pub const EPOCH_WRITE_LEEWAY: Duration = Duration::new(0, 900_000_000);

const LOG_EXTENSION: &str = "log";

// Check important properties for the constants above.
#[test]
fn check_time_relationships() {
    let epoch_period = Duration::new(EPOCH_PERIOD as i64, 0);
    assert!(epoch_period < EPOCH_WRITE_DURATION);
    assert!(EPOCH_WRITE_DURATION < EPOCH_WRITE_DURATION + EPOCH_WRITE_LEEWAY);

    // Even with the clock error bound, we don't expect more than one old not-yet-closed epoch.
    assert!(EPOCH_WRITE_DURATION + EPOCH_WRITE_LEEWAY + CLOCK_ERROR_BOUND < 2 * epoch_period);
    // In the worst case, vouched times can't be so far ahead of our time that the other host
    // will target epochs more than one period in the future.
    assert!(
        CLOCK_ERROR_BOUND
            + Duration::MILLISECOND * (vouched_time::MAX_FORWARD_DISCREPANCY_MS as f64)
            < epoch_period
    );
}

/// Parses the path for an epoch subdirectory to extract its close time, i.e.,
/// the time after which `EPOCH_WRITE_DURATION` has elapsed.
fn get_epoch_close_time(epoch: &Path) -> Result<time::PrimitiveDateTime> {
    let Some(name) = epoch.file_name() else {
        return Err(std::io::Error::other(format!(
            "epoch subdir does not have file name. epoch={:?}",
            epoch
        )));
    };

    let Some(name) = name.to_str() else {
        // We expect an ASCII name.
        return Err(std::io::Error::other(format!(
            "epoch subdir does not have UTF-8 file name. epoch={:?}",
            epoch
        )));
    };

    let Some((_left, right)) = name.rsplit_once('-') else {
        return Err(std::io::Error::other(format!(
            "epoch subdir name does not match %M:%S-[hex deadline]. epoch={:?}",
            epoch
        )));
    };

    let Ok(unix_ts) = u64::from_str_radix(right, 16) else {
        return Err(std::io::Error::other(format!(
            "epoch subdir name does not end in parsable hex deadline. epoch={:?}",
            epoch
        )));
    };

    if unix_ts > i64::MAX as u64 {
        return Err(std::io::Error::other(format!(
            "epoch subdir name has out-of-range deadline. epoch={:?} deadline={}",
            epoch, unix_ts
        )));
    }

    let Ok(result) = time::OffsetDateTime::from_unix_timestamp(unix_ts as i64) else {
        return Err(std::io::Error::other(format!(
            "epoch subdir name has unrepresentable deadline. epoch={:?} deadline={}",
            epoch, unix_ts
        )));
    };

    Ok(time::PrimitiveDateTime::new(result.date(), result.time()))
}

/// Returns the path where we expect to find the latest epoch
/// subdirectory that contains `now`, under `directory`, as
/// well as the epoch's write deadline.
pub fn construct_epoch_subdirectory(
    directory: PathBuf,
    now: time::PrimitiveDateTime,
) -> (PathBuf, time::PrimitiveDateTime) {
    let mut bag = directory;

    let unix = now.assume_utc().unix_timestamp();
    let granularity = EPOCH_PERIOD as i64;
    let deadline: i64 =
        (granularity * (unix / granularity)).saturating_add(EPOCH_WRITE_DURATION.whole_seconds());

    bag.push(format!("{}", now.date()));
    bag.push(format!("{:02}", now.hour()));
    bag.push(format!(
        "{:02}:{:02}-{:x}",
        now.minute(),
        EPOCH_PERIOD * (now.second() as u32 / EPOCH_PERIOD),
        deadline
    ));

    assert_eq!(
        get_epoch_close_time(&bag)
            .expect("Should construct a valid path")
            .assume_utc()
            .unix_timestamp(),
        deadline
    );

    let deadline = match time::OffsetDateTime::from_unix_timestamp(deadline) {
        Ok(deadline) => time::PrimitiveDateTime::new(deadline.date(), deadline.time()),
        Err(_) => time::PrimitiveDateTime::MAX,
    };

    (bag, deadline)
}

#[test]
fn test_epoch_bag_subdirectory() {
    use time::macros::datetime;

    assert_eq!(
        construct_epoch_subdirectory("/tmp/test".into(), datetime!(2024-04-07 16:01:32)),
        // Sun Apr  7 04:01:37 PM UTC 2024
        (
            PathBuf::from(format!("/tmp/test/2024-04-07/16/01:30-{:x}", 1712505697)),
            datetime!(2024-04-07 16:01:37)
        )
    );
    assert_eq!(
        construct_epoch_subdirectory("/tmp/test2/".into(), datetime!(2024-04-07 13:02:35)),
        // Sun Apr  7 01:02:42 PM UTC 2024
        (
            PathBuf::from(format!("/tmp/test2/2024-04-07/13/02:35-{:x}", 1712494962)),
            datetime!(2024-04-07 13:02:42)
        )
    );
}

#[test]
fn test_epoch_parsing_happy_path() {
    assert_eq!(
        get_epoch_close_time(&PathBuf::from(format!(
            "/tmp/test/2024-04-07/16/01:30-{:x}",
            1712505697
        )))
        .expect("must succeed")
        .assume_utc()
        .unix_timestamp(),
        1712505697
    );
}

#[test]
fn test_epoch_parsing_failure() {
    use std::ffi::OsStr;
    use std::os::unix::ffi::OsStrExt;
    assert!(format!(
        "{:?}",
        get_epoch_close_time(&PathBuf::from("/")).unwrap_err()
    )
    .contains("epoch subdir does not have file name"));

    assert!(format!(
        "{:?}",
        get_epoch_close_time(&PathBuf::from(OsStr::from_bytes(&[32u8, 255u8]))).unwrap_err()
    )
    .contains("epoch subdir does not have UTF-8 file name"));

    assert!(format!(
        "{:?}",
        get_epoch_close_time(&PathBuf::from("/tmp/test/2024-04-07/16/01:30_123")).unwrap_err()
    )
    .contains("epoch subdir name does not match"));

    assert!(format!(
        "{:?}",
        get_epoch_close_time(&PathBuf::from("/tmp/test/2024-04-07/16/01:30-")).unwrap_err()
    )
    .contains("epoch subdir name does not end in parsable hex deadline"));

    assert!(format!(
        "{:?}",
        get_epoch_close_time(&PathBuf::from("/tmp/test/2024-04-07/16/01:30-123gh")).unwrap_err()
    )
    .contains("epoch subdir name does not end in parsable hex deadline"));

    assert!(format!(
        "{:?}",
        get_epoch_close_time(&PathBuf::from(format!(
            "/tmp/test/2024-04-07/16/01:30-{:x}1",
            u64::MAX
        )))
        .unwrap_err()
    )
    .contains("epoch subdir name does not end in parsable hex deadline"));

    assert!(format!(
        "{:?}",
        get_epoch_close_time(&PathBuf::from(format!(
            "/tmp/test/2024-04-07/16/01:30-{:x}",
            u64::MAX
        )))
        .unwrap_err()
    )
    .contains("epoch subdir name has out-of-range deadline"));

    assert!(format!(
        "{:?}",
        get_epoch_close_time(&PathBuf::from(format!(
            "/tmp/test/2024-04-07/16/01:30-{:x}",
            i64::MAX
        )))
        .unwrap_err()
    )
    .contains("epoch subdir name has unrepresentable deadline"));
}
