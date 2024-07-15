//! NO DOC
use std::collections::BTreeSet;
use std::io::Result;
use std::path::Path;
use std::sync::Arc;

// writer on single-box FSx shaves ~1 ms off writes.
// writer: n=100500 min=1ms879µs237ns p1=2ms94µs472ns p5=2ms181µs689ns p50=2ms491µs461ns p90=3ms945µs363ns p95=5ms95µs272ns p99=8ms858µs944ns p999=18ms796µs730ns max=45ms268µs840ns
// NO RESCAN
// reader: n=100000 min=2ms109µs61ns p1=2ms400µs360ns p5=2ms546µs958ns p50=5ms289µs322ns p90=9ms866µs65ns p95=13ms95µs154ns p99=23ms627µs114ns p999=45ms699µs664ns max=83ms225µs571ns
//         n=100000 min=1µs533ns p1=155µs311ns p5=464µs135ns p50=2ms328µs109ns p90=5ms426µs393ns p95=7ms66µs488ns p99=13ms862µs937ns p999=30ms554µs35ns max=80ms912µs729ns
//          n=85179 min=1ms7µs156ns p1=1ms330µs658ns p5=1ms487µs187ns p50=2ms258µs455ns p90=4ms726µs7ns p95=6ms244µs831ns p99=11ms191µs635ns p999=24ms644µs310ns max=60ms630µs437ns
// CURRENT
// reader: n=100000 min=2ms385µs727ns p1=3ms178µs37ns p5=3ms981µs82ns p50=8ms172µs514ns p90=15ms507µs824ns p95=20ms243µs508ns p99=35ms473µs181ns p999=63ms517µs392ns max=111ms153µs97ns
//         n=100000 min=2µs949ns p1=130µs23ns p5=406µs525ns p50=4ms91µs769ns p90=7ms662µs241ns p95=10ms539µs638ns p99=19ms847µs763ns p999=42ms510µs502ns max=85ms81µs869ns
//          n=84081 min=1ms644µs606ns p1=2ms440µs760ns p5=2ms833µs865ns p50=3ms951µs581ns p90=7ms408µs296ns p95=9ms257µs987ns p99=16ms211µs224ns p999=35ms7µs833ns max=85ms421µs217ns
//
// After optimisations:
// writer: n=100500 min=1ms804µs138ns p1=2ms29µs375ns p5=2ms117µs883ns p50=2ms379µs104ns p90=3ms102µs73ns p95=3ms899µs139ns p99=6ms481µs826ns p999=13ms453µs118ns max=153ms557µs328ns
// reader: n=100001 min=2ms627µs811ns p1=3ms168µs296ns p5=3ms740µs837ns p50=6ms983µs19ns p90=11ms437µs419ns p95=13ms476µs179ns p99=19ms867µs588ns p999=33ms949µs344ns max=58ms202µs577ns
//         n=100001 min=1µs669ns p1=133µs357ns p5=384µs839ns p50=3ms12µs799ns p90=6ms13µs91ns p95=7ms196µs567ns p99=11ms308µs669ns p999=21ms128µs278ns max=48ms84µs299ns
//          n=94583 min=1ms637µs709ns p1=2ms289µs641ns p5=2ms593µs213ns p50=3ms889µs145ns p90=5ms667µs825ns p95=6ms735µs590ns p99=10ms77µs496ns p999=17ms243µs175ns max=48ms198µs880ns
//
// EFS OneZone
// writer: n=100500 min=3ms429µs542ns p1=4ms186µs909ns p5=4ms453µs300ns p50=5ms346µs352ns p90=8ms48µs86ns p95=9ms110µs385ns p99=13ms450µs61ns p999=21ms854µs47ns max=58ms784µs471ns
// reader: n=100001 min=6ms15µs660ns p1=8ms999µs617ns p5=10ms373µs883ns p50=17ms189µs863ns p90=27ms216µs466ns p95=31ms691µs593ns p99=45ms857µs139ns p999=78ms411µs603ns max=123ms720µs5ns
//         n=100001 min=2µs127ns p1=878µs504ns p5=2ms21µs266ns p50=7ms321µs764ns p90=13ms295µs506ns p95=15ms561µs272ns p99=23ms833µs755ns p999=44ms574µs244ns max=91ms687µs279ns
//          n=53274 min=5ms448µs101ns p1=6ms313µs906ns p5=6ms967µs267ns p50=9ms807µs324ns p90=15ms158µs782ns p95=17ms838µs254ns p99=25ms921µs963ns p999=43ms573µs847ns max=83ms436µs398ns
fn maintainer(log: woodpile::LogMaintainer) {
    use std::collections::HashMap;
    use std::path::PathBuf;

    let mut pending_close: HashMap<PathBuf, time::PrimitiveDateTime> = HashMap::new();
    loop {
        std::thread::sleep(std::time::Duration::from_millis(1500));
        let _ = vouched_time::nfs_voucher::scan_base_time();
        for (path, deadline) in log.enumerate_subdirs_lifo() {
            let now = time::OffsetDateTime::now_utc();
            let now = time::PrimitiveDateTime::new(now.date(), now.time());
            if now > deadline {
                if (now - deadline) >= time::Duration::seconds(120) {
                    break;
                }

                if pending_close.contains_key(&path) {
                    break;
                }

                let begin = std::time::Instant::now();
                match log
                    .close_subdir(
                        &path,
                        vouched_time::VouchedTime::now_or_die(
                            vouched_time::nfs_voucher::get_base_time,
                        ),
                        Default::default(),
                    )
                    .unwrap()
                {
                    None => {} // Done!
                    Some(deadline) => {
                        pending_close.insert(path.clone(), deadline);
                        println!("Initial close {:?} in {:?}", path, begin.elapsed());
                    }
                }
            }
        }

        let mut closed_paths: Vec<PathBuf> = Vec::new();
        for (path, deadline) in pending_close.iter() {
            let now = time::OffsetDateTime::now_utc();
            let now = time::PrimitiveDateTime::new(now.date(), now.time());
            if now <= *deadline {
                continue;
            }

            let begin = std::time::Instant::now();
            println!("Begin close {:?} in {:?}", path, begin);

            if log
                .close_subdir(
                    path,
                    vouched_time::VouchedTime::now_or_die(vouched_time::nfs_voucher::get_base_time),
                    Default::default(),
                )
                .unwrap()
                .is_none()
            {
                closed_paths.push(path.clone());
                println!("Final close {:?} in {:?}", path, begin.elapsed());
            }
        }

        for path in closed_paths {
            pending_close.remove(&path);
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
        let begin_ts = time::OffsetDateTime::now_utc().unix_timestamp_nanos();

        let now = vouched_time::VouchedTime::now_or_die(vouched_time::nfs_voucher::get_base_time);
        let options = woodpile::CacheOptions {
            mode: woodpile::ReaderMode::ReadOnly,
            ..Default::default()
        };
        reader
            .maintain_cache(now, time::Duration::seconds(10), options)
            .unwrap();
        let end = time::OffsetDateTime::now_utc().unix_timestamp_nanos();

        let mut insertions = 0usize;
        for record in reader.range(..=now.get_local_time()) {
            let key = u128::from_le_bytes(record.record_id);
            if seen.insert(key) {
                let send_time = i128::from_le_bytes((&record.payload[0..16]).try_into().unwrap());
                observations.push(time::Duration::nanoseconds((end - send_time) as i64));
                observations_from_start
                    .push(time::Duration::nanoseconds((begin_ts - send_time) as i64));
                insertions += 1;
            }
        }

        if insertions > 0 {
            read_durations.push(time::Duration::nanoseconds((end - begin_ts) as i64));
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
