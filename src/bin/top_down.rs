use clap::Parser;
use synthestitch::*;


fn main() {
    let args = Args::try_parse_from(std::env::args())
        .unwrap_or_else(|err| {
            eprintln!("{err}");
            std::process::exit(1);
        });
  
    dispatch_domain(&args, None);
}