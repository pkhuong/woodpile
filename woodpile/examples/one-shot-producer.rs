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

    let padding = vec![1u8; 50 * 1024];

    for i in 0..10 {
        writer
            .write_or_panic(
                "test",
                &(i as u128).to_le_bytes(),
                || vouched_time::VouchedTime::now_or_die(vouched_time::nfs_voucher::get_base_time),
                Default::default(),
                // Stick `next_write` in the message to reflect coordinated omission.
                |dst| dst.write_all(&padding),
            )
            .unwrap();
        println!("Iteration {}", i);
    }

    Ok(())
}
