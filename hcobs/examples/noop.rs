//! noop encoder: reads bytes from stdin and writes them to stdout
use std::io::Result;

const BUFSZ: usize = 512 * 1024;

fn main() -> Result<()> {
    use std::io::Read;
    use std::io::Write;
    let mut buf = vec![0u8; BUFSZ];
    let mut stdin = std::io::stdin().lock();
    let mut stdout = std::io::stdout().lock();

    loop {
        match stdin.read(&mut buf) {
            Ok(0) => break,
            Ok(count) => stdout.write_all(&buf[..count])?,
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            Err(e) => return Err(e),
        }
    }

    Ok(())
}
