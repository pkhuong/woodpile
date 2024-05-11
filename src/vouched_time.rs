use std::io::Result;

#[cfg(test)]
use time::macros::datetime;

/// We allow times that are at most slightly less than 3 seconds (3000
/// ms) ahead of the vouched time.  This tolerance is relatively tight
/// because it's important to avoid time travel from the future.
///
/// The value is slightly less than 3000 ms to account for rounding,
/// truncation, and off-by-ones.
pub const MAX_FORWARD_DISCREPANCY_MS: u64 = 2990;

/// We allow times that are most slightly less than 60 seconds (60 000 ms)
/// behind the vouched time.  This tolerance is loose because asynchronous
/// systems fundamentally have to deal with slow peers, and because a program
/// could always keep using a stale base time.
///
/// The value is slightly less than 60 000 ms to account for rounding,
/// truncation, and off-by-ones.
pub const MAX_BACKWARD_DISCREPANCY_MS: u64 = 59_900;

// Generated with `generate_raffle_parameters "woodpile vouched time"`
const BASE_TIME_CHECK: raffle::CheckingParameters =
    raffle::CheckingParameters::parse_or_die("CHECK-fc1da7b1b77c57cb-594b9cce3091464a");

/// A [`VouchedTime`] is the combination of a local [`time::PrimitiveDateTime`]
/// in UTC, and a [`raffle::Voucher`] for a [`u64`] base time (milliseconds since
/// Unix epoch) such that the local time is at most
/// [`MAX_BACKWARD_DISCREPANCY_MS`] behind the base time or
/// [`MAX_FORWARD_DISCREPANCY_MS`] ahead of the base time.  Once a
/// [`VouchedTime`] is constructed with a trusted base time, we assume it's not
/// (deliberately) too far in the future, and likely not too far in the past
/// either.
///
/// In this library, we use the term "local time" to explicitly refer to each
/// machine's approximation of UTC.
#[derive(Clone, Copy, Debug)]
pub struct VouchedTime {
    local_time: time::PrimitiveDateTime,
    base_time_ms: u64,
    voucher: raffle::Voucher,
}

impl VouchedTime {
    /// Constructs a new VouchedTime, or returns a reason why it's invalid.
    ///
    /// This only errors out when something's really wrong; consider using
    /// [`VouchedTime::new_or_die`].
    pub fn new(
        local_time: time::PrimitiveDateTime,
        base_time_ms: u64,
        voucher: raffle::Voucher,
    ) -> Result<VouchedTime> {
        Self::check(local_time, base_time_ms, voucher)?;
        let ret = VouchedTime {
            local_time,
            base_time_ms,
            voucher,
        };

        ret.check_or_die();
        Ok(ret)
    }

    pub fn new_or_die(
        local_time: time::PrimitiveDateTime,
        base_time_ms: u64,
        voucher: raffle::Voucher,
    ) -> VouchedTime {
        VouchedTime::new(local_time, base_time_ms, voucher)
            .expect("failed to construct VouchedTime")
    }

    /// Constructs a new VouchedTime based on the time returned by `base_time_provider`,
    /// or returns a reason why the operation failed.
    ///
    /// This only errors out when something's really wrong (or the `base_time_provider`
    /// errors out); consider using [`VouchedTime::now_or_die`].
    pub fn now(
        base_time_provider: impl FnOnce() -> Result<(u64, raffle::Voucher)>,
    ) -> Result<VouchedTime> {
        let (base_time_ms, voucher) = base_time_provider()?;
        let now = time::OffsetDateTime::now_utc();
        VouchedTime::new(
            time::PrimitiveDateTime::new(now.date(), now.time()),
            base_time_ms,
            voucher,
        )
    }

    pub fn now_or_die(
        base_time_provider: impl FnOnce() -> Result<(u64, raffle::Voucher)>,
    ) -> VouchedTime {
        VouchedTime::now(base_time_provider).expect("failed to construct VouchedTime")
    }

    /// Returns the local time stored in the `VouchedTime`.
    pub fn get_local_time(self) -> time::PrimitiveDateTime {
        self.check_or_die(); // Internal self-check before returning `local_time`.
        self.local_time
    }

    /// Checks the internal representation for validity.  Panics
    /// if anything's wrong: the constructors enforce the same conditions.
    pub fn check_or_die(self) {
        Self::check(self.local_time, self.base_time_ms, self.voucher)
            .expect("Constructed VouchedTime should be valid");
    }

    pub fn check(
        local_time: time::PrimitiveDateTime,
        base_time_ms: u64,
        voucher: raffle::Voucher,
    ) -> Result<()> {
        if !BASE_TIME_CHECK.check(base_time_ms, voucher) {
            return Err(std::io::Error::other("base_time does not match voucher"));
        }

        Self::check_vouched_time(
            local_time.assume_utc().unix_timestamp_nanos() / 1_000_000,
            base_time_ms,
        )
    }

    fn check_vouched_time(local_time_ms: i128, base_time_ms: u64) -> Result<()> {
        let other = std::io::Error::other;

        if local_time_ms < 0 {
            return Err(other("local_time is before the Unix epoch"));
        }

        if local_time_ms > u64::MAX as i128 {
            return Err(other("local time is out of range"));
        }

        let local_time_ms = local_time_ms as u64;
        // if local_time - base_time in [-MAX_BACKWARD_DISCREPANCY_MS, MAX_FORWARD_DISCREPANCY_MS]
        //
        // We subtract base_time_ns, and add MAX_BACKWARD_DISCREPANCY_MS.  This maps the
        // allowed range to `[0, MAX_BACKWARD_DISCREPANCY_MS + MAX_FORWARD_DISCREPANCY_MS]`.
        if local_time_ms
            .wrapping_sub(base_time_ms)
            .wrapping_add(MAX_BACKWARD_DISCREPANCY_MS)
            <= MAX_BACKWARD_DISCREPANCY_MS + MAX_FORWARD_DISCREPANCY_MS
        {
            return Ok(());
        }

        if local_time_ms > base_time_ms {
            return Err(other("local_time is too far ahead of base_time"));
        }

        Err(other("local_time is too far behind base_time"))
    }
}

// Check that we can construct `VouchedTime`s with an exact match on the base time.
#[test]
fn test_happy_path_miri() {
    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    // $ date -u -d@1713027659
    // Sat Apr 13 05:00:59 PM UTC 2024

    assert_eq!(
        VouchedTime::new_or_die(
            datetime!(2024-04-13 17:00:59),
            1713027659000,
            vouch_params.vouch(1713027659000)
        )
        .get_local_time(),
        datetime!(2024-04-13 17:00:59),
    );

    if !cfg!(miri) {
        let now = || {
            let now = (time::OffsetDateTime::now_utc().unix_timestamp_nanos() / 1_000_000) as u64;
            Ok((now, vouch_params.vouch(now)))
        };

        println!("{:?}", VouchedTime::now_or_die(now));
        println!("{:?}", VouchedTime::now(now).expect("must succeed"));
    }
}

// Go right at the end of the allowed discrepancy between the base time and the local time.
#[test]
fn test_limit_miri() {
    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    // $ date -u -d@1713027659
    // Sat Apr 13 05:00:59 PM UTC 2024

    // Construct a time ahead of the vouched time
    let time = VouchedTime::new(
        datetime!(2024-04-13 17:01:01.990),
        1713027659000,
        vouch_params.vouch(1713027659000),
    )
    .expect("should build");
    time.check_or_die();
    assert_eq!(time.get_local_time(), datetime!(2024-04-13 17:01:01.99));

    // One more millisecond, and it fails.
    assert!(VouchedTime::new(
        datetime!(2024-04-13 17:01:01.991),
        1713027659000,
        vouch_params.vouch(1713027659000),
    )
    .is_err());

    // Construct a time behind the vouched time
    let time = VouchedTime::new(
        datetime!(2024-04-13 16:59:59.100),
        1713027659000,
        vouch_params.vouch(1713027659000),
    )
    .expect("should build");
    time.check_or_die();
    assert_eq!(time.get_local_time(), datetime!(2024-04-13 16:59:59.100));

    // Another millisecond and it fails.
    assert!(VouchedTime::new(
        datetime!(2024-04-13 16:59:59.099),
        1713027659000,
        vouch_params.vouch(1713027659000),
    )
    .is_err());
}

#[test]
#[should_panic(expected = "failed to construct VouchedTime")]
fn test_panic_new_miri() {
    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    VouchedTime::new_or_die(
        datetime!(2024-04-12 17:01:01.990),
        1713027659000,
        vouch_params.vouch(1713027659000),
    );
}

#[cfg(not(miri))]
#[test]
#[should_panic(expected = "failed to construct VouchedTime")]
fn test_panic_now() {
    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let now = || {
        let now = (datetime!(2023-04-14 17:01:01.990)
            .assume_utc()
            .unix_timestamp_nanos()
            / 1_000_000) as u64;
        Ok((now, vouch_params.vouch(now)))
    };

    VouchedTime::now_or_die(now);
}

#[test]
#[should_panic(expected = "failed to construct VouchedTime")]
fn test_panic_now_bad_time_miri() {
    let now = || Err(std::io::Error::other("time callback failed"));

    VouchedTime::now_or_die(now);
}

// Reject bad vouchers.
#[test]
fn test_invalid_miri() {
    let vouch_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    // $ date -u -d@1713027659
    // Sat Apr 13 05:00:59 PM UTC 2024
    assert!(VouchedTime::new(
        datetime!(2024-04-13 17:00:59),
        1713027659000,
        vouch_params.vouch(1713027659000)
    )
    .is_ok());

    // Bad time
    assert!(format!(
        "{:?}",
        VouchedTime::new(
            datetime!(2024-04-13 17:00:59),
            1713027659001,
            vouch_params.vouch(1713027659000)
        )
        .unwrap_err()
    )
    .contains("base_time does not match voucher"));

    // Bad voucher
    assert!(format!(
        "{:?}",
        VouchedTime::new(
            datetime!(2024-04-13 17:00:59),
            1713027659000,
            vouch_params.vouch(1713027659001)
        )
        .unwrap_err()
    )
    .contains("base_time does not match voucher"));

    // randomly generated parameters
    let bad_params = raffle::VouchingParameters::parse_or_die(
        "VOUCH-d165ec246b320939-2067990c3fc0f62d-309ee23efd609c4b-45b19da4a316ca0e",
    );

    // Bad params
    assert!(format!(
        "{:?}",
        VouchedTime::new(
            datetime!(2024-04-13 17:00:59),
            1713027659000,
            bad_params.vouch(1713027659000)
        )
        .unwrap_err()
    )
    .contains("base_time does not match voucher"));
}

// Make sure we correctly handle (or at least reject) values beyond or
// at the edge of the representable range.
#[test]
fn test_boundaries_miri() {
    assert!(VouchedTime::check_vouched_time(
        time::PrimitiveDateTime::MAX
            .assume_utc()
            .unix_timestamp_nanos()
            / 1_000_000,
        u64::MAX
    )
    .is_err());
    assert!(VouchedTime::check_vouched_time(
        time::PrimitiveDateTime::MAX
            .assume_utc()
            .unix_timestamp_nanos()
            / 1_000_000,
        u64::MIN
    )
    .is_err());
    assert!(VouchedTime::check_vouched_time(
        time::PrimitiveDateTime::MIN
            .assume_utc()
            .unix_timestamp_nanos()
            / 1_000_000,
        u64::MIN
    )
    .is_err());
    assert!(VouchedTime::check_vouched_time(
        time::PrimitiveDateTime::MIN
            .assume_utc()
            .unix_timestamp_nanos()
            / 1_000_000,
        u64::MAX
    )
    .is_err());

    VouchedTime::check_vouched_time(0, 0).expect("should pass");
    VouchedTime::check_vouched_time(0, MAX_BACKWARD_DISCREPANCY_MS).expect("should pass");
    assert!(VouchedTime::check_vouched_time(0, MAX_BACKWARD_DISCREPANCY_MS + 1).is_err());
    VouchedTime::check_vouched_time(MAX_FORWARD_DISCREPANCY_MS as i128, 0).expect("should pass");
    assert!(VouchedTime::check_vouched_time(1 + MAX_FORWARD_DISCREPANCY_MS as i128, 0).is_err());

    // Negative timestamp -> reject.
    assert!(VouchedTime::check_vouched_time(-1, 0).is_err());
    assert!(VouchedTime::check_vouched_time(-1, u64::MAX).is_err());

    // Huge timestamps
    VouchedTime::check_vouched_time(u64::MAX as i128, u64::MAX).expect("should pass");
    assert!(VouchedTime::check_vouched_time(u64::MAX as i128 + 1, u64::MAX).is_err());
    VouchedTime::check_vouched_time((u64::MAX - MAX_BACKWARD_DISCREPANCY_MS) as i128, u64::MAX)
        .expect("should pass");
    assert!(VouchedTime::check_vouched_time(
        (u64::MAX - MAX_BACKWARD_DISCREPANCY_MS) as i128 - 1,
        u64::MAX
    )
    .is_err());

    VouchedTime::check_vouched_time(u64::MAX as i128, u64::MAX - MAX_FORWARD_DISCREPANCY_MS)
        .expect("should pass");
    assert!(VouchedTime::check_vouched_time(
        u64::MAX as i128,
        u64::MAX - MAX_FORWARD_DISCREPANCY_MS - 1
    )
    .is_err());
}
