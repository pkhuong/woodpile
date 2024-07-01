//! Implement a lock-free pair of base_time_ms and corresponding voucher
//! with two copies and a sequence number.
use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering;
use std::sync::Mutex;

#[derive(Debug)]
struct BaseTime {
    base_time_ms: AtomicU64,
    voucher: AtomicU64,
}

#[derive(Debug)]
struct WriteToken {}

/// An [`AtomicBaseTime`] is a lock-free pair of `base_time_ms` and
/// corresponding voucher.
///
/// Internally, it's implemented as a sequence number and two copies.
/// At any one time, the copy at `sequence % len` is stable (not being
/// written).  A read is valid if the sequence didn't change mid-snapshot.
#[derive(Debug)]
pub struct AtomicBaseTime {
    lock: Mutex<WriteToken>,
    // The snapshot at sequence % len is stable; the next one may be mid-update.
    sequence: AtomicU64,
    snapshots: [BaseTime; 2],
}

impl Default for AtomicBaseTime {
    fn default() -> Self {
        Self::new()
    }
}

const _: () = assert!(std::mem::size_of::<raffle::Voucher>() == std::mem::size_of::<u64>());

union TransmuteVoucher {
    bits: u64,
    voucher: raffle::Voucher,
}

impl BaseTime {
    /// Returns a new `BaseTime` initialised for the epoch.
    const fn new() -> Self {
        const VOUCH_PARAMS: raffle::VouchingParameters = raffle::VouchingParameters::parse_or_die(
            "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
        );

        let base_time_ms = 0u64;
        let voucher = VOUCH_PARAMS.vouch(base_time_ms);
        let voucher = unsafe { TransmuteVoucher { voucher }.bits };
        Self {
            base_time_ms: AtomicU64::new(base_time_ms),
            voucher: AtomicU64::new(voucher),
        }
    }

    /// Updates the internal value with release stores.
    ///
    /// The voucher must match base_time_ms.
    pub fn update(&self, base_time_ms: u64, voucher: raffle::Voucher) {
        assert!(crate::BASE_TIME_CHECK.check(base_time_ms, voucher));

        self.base_time_ms.store(base_time_ms, Ordering::Release);
        self.voucher.store(
            unsafe { TransmuteVoucher { voucher }.bits },
            Ordering::Release,
        );
    }

    /// Returns a snapshot of the current pair.
    ///
    /// The snapshot may be invalid when executed concurrently with an update.
    pub fn snapshot(&self) -> (u64, u64) {
        let bits = self.voucher.load(Ordering::Acquire);
        let base_time_ms = self.base_time_ms.load(Ordering::Acquire);

        // Can't check here because we might have a racy update.
        (base_time_ms, bits)
    }
}

impl AtomicBaseTime {
    /// Returns a new `AtomicBaseTime` instance initialised at the epoch.
    pub const fn new() -> Self {
        Self {
            lock: Mutex::new(WriteToken {}),
            sequence: AtomicU64::new(0),
            snapshots: [BaseTime::new(), BaseTime::new()],
        }
    }

    /// Returns the current sequence number.
    pub fn sequence(&self) -> u64 {
        self.sequence.load(Ordering::Relaxed)
    }

    /// Lock-freely takes a consistent snapshot of the `AtomicBaseTime`.
    ///
    /// The return value corresponds to the most recent `update`d pair
    /// on entry, or one of the values `update`d between entry and exit.
    pub fn snapshot(&self) -> (u64, raffle::Voucher) {
        let mut sequence = self.sequence.load(Ordering::Acquire);

        loop {
            let (base_time_ms, bits) =
                self.snapshots[(sequence as usize) % self.snapshots.len()].snapshot();
            let next_sequence = self.sequence.load(Ordering::Acquire);
            if sequence == next_sequence {
                // We got a good read, transmute!
                //
                // It would be safe to transmute earlier, since each 64-bit
                // load is atomic, but this is the general pattern.
                let voucher = unsafe { TransmuteVoucher { bits }.voucher };
                assert!(crate::BASE_TIME_CHECK.check(base_time_ms, voucher));

                return (base_time_ms, voucher);
            }

            sequence = next_sequence;
        }
    }

    /// Updates the value stored in the `AtomicBaseTime`.
    ///
    /// Calls serialise on an internal lock, but do not block
    /// `snapshot` calls.
    pub fn update(&self, update: (u64, raffle::Voucher)) {
        let mut token = loop {
            match self.lock.lock() {
                Ok(guard) => break guard,
                // The lock only serves for mutual exclusion, if it's
                // poisoned, the previous holder isn't updating.
                Err(_) => self.lock.clear_poison(),
            }
        };

        self.advance_once(&mut token, update);
    }

    /// Wait-free attempt at updating the value stored in the `AtomicBaseTime`.
    ///
    /// Returns whether the instance was updated.
    ///
    /// Calls still serialise on an internal lock, but they return `false`
    /// instead of blocking.
    pub fn try_update(&self, update: (u64, raffle::Voucher)) -> bool {
        use std::sync::TryLockError::*;

        let mut token = match self.lock.try_lock() {
            Ok(guard) => guard,
            Err(Poisoned(_)) => {
                self.lock.clear_poison();
                return false;
            }
            Err(WouldBlock) => return false,
        };

        self.advance_once(&mut token, update)
    }

    fn advance_once(&self, _token: &mut WriteToken, update: (u64, raffle::Voucher)) -> bool {
        let current = self.sequence.load(Ordering::Relaxed);
        let current_base_time_ms = self.snapshots[(current as usize) % self.snapshots.len()]
            .snapshot()
            .0;
        if update.0 < current_base_time_ms {
            // The update is older than the current value; skip it.
            return false;
        }

        let next = current.wrapping_add(1);
        let idx = (next as usize) % self.snapshots.len();

        self.snapshots[idx].update(update.0, update.1);
        self.sequence.store(next, Ordering::Release); // Commit the write
        true
    }
}

// Make sure this works.
#[cfg(test)]
static _BASE_TIME: AtomicBaseTime = AtomicBaseTime::new();

#[test]
fn test_smoke_miri() {
    const VOUCH_PARAMS: raffle::VouchingParameters = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let base_time: AtomicBaseTime = Default::default();
    assert_eq!(base_time.sequence(), 0);

    assert_eq!(base_time.snapshot().0, 0);

    {
        let (time, voucher) = base_time.snapshot();
        assert!(VOUCH_PARAMS.checking_parameters().check(time, voucher));
    }

    base_time.update((42, VOUCH_PARAMS.vouch(42)));
    assert_eq!(base_time.sequence(), 1);

    assert_eq!(base_time.snapshot().0, 42);
    {
        let (time, voucher) = base_time.snapshot();
        assert!(VOUCH_PARAMS.checking_parameters().check(time, voucher));
    }

    base_time.try_update((100, VOUCH_PARAMS.vouch(100)));
    assert_eq!(base_time.sequence(), 2);

    assert_eq!(base_time.snapshot().0, 100);
    {
        let (time, voucher) = base_time.snapshot();
        assert!(VOUCH_PARAMS.checking_parameters().check(time, voucher));
    }
}

#[test]
#[should_panic(expected = "BASE_TIME_CHECK.check")]
fn test_panic_miri() {
    const VOUCH_PARAMS: raffle::VouchingParameters = raffle::VouchingParameters::parse_or_die(
        "VOUCH-773ec2a0e62c20cd-f9e079b78e895091-fc1da7b1b77c57cb-594b9cce3091464a",
    );

    let base_time = AtomicBaseTime::new();

    base_time.update((42, VOUCH_PARAMS.vouch(43)));
}
