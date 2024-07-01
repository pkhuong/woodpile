//! NO DOC
use std::collections::BTreeSet;
use std::io::Result;
use std::path::Path;
use std::sync::Arc;

/// n=100000 min=2ms405µs208ns p1=3ms685µs176ns p5=4ms610µs257ns p50=9ms425µs977ns p90=18ms196µs67ns p95=22ms704µs798ns p99=34ms817µs536ns p999=59ms172µs212ns max=100ms237µs166ns

/// FSx v3 n=100016 min=5ms533µs644ns p1=7ms766µs623ns p5=9ms999µs130ns p50=22ms490µs773ns p90=40ms646µs65ns p95=47ms931µs588ns p99=63ms637µs992ns p999=83ms31µs28ns max=115ms230µs910ns
/// FSx v4 n=100007 min=5ms239µs856ns p1=7ms309µs183ns p5=9ms256µs786ns p50=20ms9µs484ns p90=34ms961µs534ns p95=40ms878µs156ns p99=55ms592µs822ns p999=84ms893µs564ns max=139ms708µs227ns

fn maintainer(log: woodpile::LogMaintainer) {
    loop {
        std::thread::sleep(std::time::Duration::from_millis(500));
        let _ = vouched_time::nfs_voucher::scan_base_time();
        let mut num_closed = 0usize;
        for (path, deadline) in log.enumerate_subdirs_lifo() {
            let now = time::OffsetDateTime::now_utc();
            let now = time::PrimitiveDateTime::new(now.date(), now.time());
            if now > deadline {
                if (now - deadline) >= time::Duration::seconds(60) {
                    break;
                }

                log.close_subdir(
                    &path,
                    vouched_time::VouchedTime::now_or_die(vouched_time::nfs_voucher::get_base_time),
                    Default::default(),
                )
                .unwrap();
                num_closed += 1;
                if num_closed >= 4 {
                    break;
                }
            }
        }
    }
}

/// SAD
fn main() -> Result<()> {
    let args = std::env::args().collect::<Vec<_>>();

    if args.len() != 2 {
        eprintln!("Usage: {} <log_path>", args[0]);
        std::process::exit(1);
    }

    let log_path = Path::new(&args[1]);
    std::fs::create_dir_all(log_path)?;

    vouched_time::nfs_voucher::add_trusted_path(log_path.join("ctime_flag"))?;

    let log = woodpile::Log::new(Arc::new(log_path.to_owned()));

    {
        let log_maintainer = log.clone().into_maintainer();
        std::thread::spawn(move || maintainer(log_maintainer));
    }

    let mut seen: BTreeSet<u128> = BTreeSet::new();
    let mut observations: Vec<time::Duration> = Vec::with_capacity(1_000_000);
    let mut observations_from_start: Vec<time::Duration> = Vec::with_capacity(1_000_000);
    let mut read_durations: Vec<time::Duration> = Vec::with_capacity(1_000_000);

    let mut reader = log.into_reader();
    let mut iter = 0u64;
    while observations.len() < 120_000 {
        let begin = std::time::Instant::now();
        let now = vouched_time::VouchedTime::now_or_die(vouched_time::nfs_voucher::get_base_time);
        reader
            .maintain_cache(now, time::Duration::seconds(10), Default::default())
            .unwrap();
        let end = time::OffsetDateTime::now_utc().unix_timestamp_nanos();

        let mut insertions = 0usize;
        for record in reader.range(..=now.get_local_time()) {
            let key = u128::from_le_bytes(record.record_id);
            if seen.insert(key) {
                let send_time = i128::from_le_bytes((&record.payload[0..16]).try_into().unwrap());
                observations.push(time::Duration::nanoseconds((end - send_time) as i64));
                observations_from_start.push(time::Duration::nanoseconds(
                    (now.get_local_time().assume_utc().unix_timestamp_nanos() - send_time) as i64,
                ));
                insertions += 1;
            }
        }

        if insertions > 0 {
            read_durations.push(time::Duration::nanoseconds(
                (end - now.get_local_time().assume_utc().unix_timestamp_nanos()) as i64,
            ));
        }

        if iter % 100 == 0 {
            println!(
                "Observations: {} {} {:?} -- {} {} {}",
                observations.len(),
                insertions,
                begin.elapsed(),
                observations.last().copied().unwrap_or(time::Duration::ZERO),
                observations_from_start
                    .last()
                    .copied()
                    .unwrap_or(time::Duration::ZERO),
                read_durations
                    .last()
                    .copied()
                    .unwrap_or(time::Duration::ZERO),
            );
        }

        iter += 1;
    }

    for observations in [
        &mut observations,
        &mut observations_from_start,
        &mut read_durations,
    ] {
        let skip: usize = if observations.len() > 100000 {
            20000
        } else {
            observations.len() / 20
        };
        let observations = &mut observations[skip..];
        observations.sort();
        println!(
            "n={} min={} p1={} p5={} p50={} p90={} p95={} p99={} p999={} max={}",
            observations.len(),
            observations[0],
            observations[observations.len() / 100],
            observations[5 * observations.len() / 100],
            observations[50 * observations.len() / 100],
            observations[90 * observations.len() / 100],
            observations[95 * observations.len() / 100],
            observations[99 * observations.len() / 100],
            observations[999 * observations.len() / 1000],
            observations[observations.len() - 1]
        );
    }

    Ok(())
}
