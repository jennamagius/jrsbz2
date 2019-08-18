#[derive(structopt::StructOpt)]
struct Args {
    #[structopt(short = "d")]
    decompress: bool,
}

fn main() {
    env_logger::init();
    let args = <Args as structopt::StructOpt>::from_args();
    let mut buf = [0u8];
    let stdout = std::io::stdout();
    let mut stdout_lock = stdout.lock();
    let stdin = std::io::stdin();
    let mut stdin_lock = stdin.lock();
    if args.decompress {
        let mut decoder = jrsbz2::Decoder::default();
        loop {
            match std::io::Read::read(&mut stdin_lock, &mut buf) {
                Ok(1) => {
                    let result = decoder.push_byte(buf[0]).expect("decompression error");
                    std::io::Write::write_all(&mut stdout_lock, &result).expect("output error");
                }
                Ok(0) => {
                    log::trace!("No more to read");
                    break;
                }
                x => {
                    x.expect("input error");
                }
            }
        }
    } else {
        let mut encoder = jrsbz2::Encoder::default();
        loop {
            match std::io::Read::read(&mut stdin_lock, &mut buf) {
                Ok(1) => {
                    let result = encoder.push_byte(buf[0]).expect("compression error");
                    std::io::Write::write_all(&mut stdout_lock, &result).expect("output error");
                }
                Ok(0) => {
                    let result = encoder.finish().expect("compression finish error");
                    std::io::Write::write_all(&mut stdout_lock, &result).expect("output error");
                    break;
                }
                x => {
                    x.expect("input error");
                }
            }
        }
    }
}
