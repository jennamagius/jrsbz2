#[derive(structopt::StructOpt)]
struct Args {
    input_file: std::path::PathBuf,
}

fn main() {
    env_logger::init();
    let args = <Args as structopt::StructOpt>::from_args();
    let mut buf = [0u8];
    let mut file = std::fs::File::open(&args.input_file).unwrap();
    let mut decoder = jrsbz2::Decoder::default();
    let stdout = std::io::stdout();
    let mut stdout_lock = stdout.lock();
    loop {
        match std::io::Read::read(&mut file, &mut buf) {
            Ok(1) => {
                let result = decoder.push_byte(buf[0]).unwrap();
                std::io::Write::write_all(&mut stdout_lock, &result).unwrap();
            }
            Ok(0) => {
                break;
            }
            x => panic!("{:?}", x),
        }
    }
}
