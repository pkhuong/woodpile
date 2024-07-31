//! hcobs codec: decodes if argv[1] starts with "d", encodes otherwise
use std::io::Result;
use std::io::Write;
use std::num::NonZeroUsize;

const BUFSZ: usize = 512 * 1024;

fn decode() -> Result<()> {
    let mut decoder = hcobs::Decoder::new();
    let mut stdin = std::io::stdin().lock();
    let mut stdout = std::io::stdout().lock();

    let mut flush = |mut consumer: owning_iovec::ConsumingIovec, ret: Result<()>| -> Result<()> {
        loop {
            let prefix = consumer.stable_prefix();
            if prefix.is_empty() {
                return ret;
            }

            match stdout.write_vectored(prefix) {
                Ok(0) => {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::UnexpectedEof,
                        "failed to write to stdout",
                    ))
                }
                Ok(n) => assert_eq!(consumer.advance_slices(n), n),
                Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
                Err(e) => return Err(e),
            }
        }
    };

    loop {
        match decoder.decode_read(&mut stdin, BUFSZ, NonZeroUsize::new(100).unwrap()) {
            Ok(0) => {
                return flush(
                    decoder.finish().map_err(std::io::Error::other)?.consumer(),
                    Ok(()),
                )
            }
            Err(e) if e.kind() != std::io::ErrorKind::Interrupted => {
                return flush(
                    decoder.finish().map_err(std::io::Error::other)?.consumer(),
                    Err(e),
                )
            }
            _ => flush(decoder.consumer(), Ok(()))?,
        }
    }
}

fn encode() -> Result<()> {
    let mut encoder = hcobs::Encoder::new();
    let mut stdin = std::io::stdin().lock();
    let mut stdout = std::io::stdout().lock();

    let mut flush = |mut consumer: owning_iovec::ConsumingIovec, ret: Result<()>| -> Result<()> {
        loop {
            let prefix = consumer.stable_prefix();
            if prefix.is_empty() {
                return ret;
            }

            match stdout.write_vectored(prefix) {
                Ok(0) => {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::UnexpectedEof,
                        "failed to write to stdout",
                    ))
                }
                Ok(n) => assert_eq!(consumer.advance_slices(n), n),
                Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
                Err(e) => return Err(e),
            }
        }
    };

    loop {
        match encoder.encode_read(&mut stdin, BUFSZ, NonZeroUsize::new(100).unwrap()) {
            Ok(0) => return flush(encoder.finish().consumer(), Ok(())),
            Err(e) if e.kind() != std::io::ErrorKind::Interrupted => {
                return flush(encoder.finish().consumer(), Err(e))
            }
            _ => flush(encoder.consumer(), Ok(()))?,
        }
    }
}

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();

    if args
        .get(1)
        .map(|x| -> &str { x })
        .unwrap_or("")
        .starts_with('d')
    {
        decode()
    } else {
        encode()
    }
}
