//! NO DOC
use std::io::Result;
use std::path::Path;
use std::sync::Arc;

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
    let mut writer = log.get_writer();
    let mut write_durations: Vec<time::Duration> = Vec::with_capacity(120500);

    let _padding = vec![1u8; 50 * 1024];

    let write_period = std::time::Duration::from_millis(5);
    let mut next_write = time::OffsetDateTime::now_utc();
    let mut had_to_sleep: bool = false;
    for i in 0..120_500 {
        let now = time::OffsetDateTime::now_utc();
        writer
            .write_or_panic(
                "test",
                &(i as u128).to_le_bytes(),
                || vouched_time::VouchedTime::now_or_die(vouched_time::nfs_voucher::get_base_time),
                Default::default(),
                // Stick `next_write` in the message to reflect coordinated omission.
                |dst| {
                    let ts = if had_to_sleep { next_write } else { now };
                    dst.write_all(&ts.unix_timestamp_nanos().to_le_bytes())?;
                    //dst.write_all(&_padding)?;
                    Ok(())
                },
            )
            .unwrap();
        write_durations.push(time::Duration::nanoseconds(
            (time::OffsetDateTime::now_utc().unix_timestamp_nanos() - now.unix_timestamp_nanos())
                as i64,
        ));

        if i % 100 == 0 {
            println!("{} {}", i + 1, write_durations.last().unwrap());
        }

        next_write += write_period;
        let duration = (next_write - time::OffsetDateTime::now_utc())
            .max(time::Duration::ZERO)
            .try_into()
            .unwrap();
        std::thread::sleep(duration);
        had_to_sleep = duration > std::time::Duration::ZERO;
    }

    let write_durations = &mut write_durations[20000..];
    write_durations.sort();
    println!(
        "n={} min={} p1={} p5={} p50={} p90={} p95={} p99={} p999={} max={}",
        write_durations.len(),
        write_durations[0],
        write_durations[write_durations.len() / 100],
        write_durations[5 * write_durations.len() / 100],
        write_durations[50 * write_durations.len() / 100],
        write_durations[90 * write_durations.len() / 100],
        write_durations[95 * write_durations.len() / 100],
        write_durations[99 * write_durations.len() / 100],
        write_durations[999 * write_durations.len() / 1000],
        write_durations[write_durations.len() - 1]
    );

    Ok(())
}
