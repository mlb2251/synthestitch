use clap::Parser;
use synthestitch::*;
use lambdas::domains::simple::*;
use lambdas::domains::prim_lists::*;




fn main() {

    let args = Args::parse();

    match &args.domain {
        DomainChoice::Simple => {
            run::<SimpleVal>(&args);
        },
        DomainChoice::List => {
            run::<ListVal>(&args);
        },
    }

}

