use synthestitch::top_down::*;
use std::fs::File;
use std::path::Path;
use clap::{Parser,ArgEnum};
use serde::Serialize;
use std::path::PathBuf;
use ordered_float::NotNan;
use serde_json::de::from_reader;
use lambdas::*;
use lambdas::domains::simple::*;
use lambdas::domains::prim_lists::*;
use synthestitch::task::*;



/// Synthesizer
#[derive(Parser, Debug, Serialize)]
#[clap(name = "Synthesizer")]
pub struct Args {
    /// json input file
    #[clap(short, long, parse(from_os_str))]
    pub file: Option<PathBuf>,

    /// json output file
    #[clap(short, long, parse(from_os_str), default_value = "out/out.json")]
    pub out: PathBuf,

    /// Domain to enumerate from
    #[clap(short, long, arg_enum, default_value = "list")]
    pub domain: DomainChoice,

    #[clap(flatten)]
    pub top_down_cfg: TopDownConfig,
}

#[derive(Debug, Clone, ArgEnum, Serialize)]
pub enum DomainChoice {
    List,
    Simple
}

#[derive(Debug, Clone, ArgEnum, Serialize)]
pub enum SynthChoice {
    TopDown,
    BottomUp,
}


fn parse_tasks<D: Domain>(path: &dyn AsRef<Path>) -> Vec<Task<D>> {
    let json: serde_json::Value = from_reader(File::open(path).expect("file not found")).expect("json deserializing error");
    let tasks: Vec<Task<D>> = json.as_array().unwrap().iter().map(|task| {
        Task::new(
            task["name"].as_str().unwrap().to_string(),
            task["tp"].as_str().unwrap().parse().unwrap(),
            task["ios"].as_array().unwrap().iter().map(|io| {
                let inputs: Vec<String> = io.as_array().unwrap()[0].as_array().unwrap().iter().map(|i| i.as_str().unwrap().to_string()).collect();
                let output: String = io.as_array().unwrap()[1].as_str().unwrap().to_string();
                IO::new(
                    // remove all spaces since prims cant have spaces within them
                    inputs.iter().map(|i| D::val_of_prim(&i.replace(" ", "").into()).expect(&format!("failed to parse {i} as a Val"))).collect(),
                    D::val_of_prim(&output.replace(" ", "").into()).unwrap()
                )
            }).collect(),
        )
    }).collect();
    tasks
}


fn main() {

    let args = Args::parse();

    match &args.domain {
        DomainChoice::Simple => {
            let tasks: Vec<Task<SimpleVal>> = args.file.as_ref().map(|path| parse_tasks(path)).unwrap_or(vec![]);
            uniform_top_down::<SimpleVal>(&tasks, &args)
        },
        DomainChoice::List => {
            let tasks: Vec<Task<ListVal>> = args.file.as_ref().map(|path| parse_tasks(path)).unwrap_or(vec![]);
            uniform_top_down::<ListVal>(&tasks, &args)
        },
    }

}

fn uniform_top_down<D: Domain>(tasks: &[Task<D>], args: &Args) {

    top_down_inplace::<D,_>(
        OrigamiModel::new(
            UniformModel::new(NotNan::new(0.).unwrap(),NotNan::new(0.).unwrap()),
            "fix_flip".into(),
            "fix".into()
        ),
        tasks,
        &args.top_down_cfg
    );
}
