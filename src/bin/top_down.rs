use colorful::Colorful;
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
    #[clap(parse(from_os_str))]
    pub file: Option<PathBuf>,

    /// json output file
    #[clap(short, long, parse(from_os_str), default_value = "out/out.json")]
    pub out: PathBuf,

    /// Domain to enumerate from
    #[clap(short, long, arg_enum, default_value = "list")]
    pub domain: DomainChoice,

    /// json solutions file (for debugging)
    #[clap(long, parse(from_os_str))]
    pub track_all: Option<PathBuf>,

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


fn parse_tasks<D: Domain>(path: &dyn AsRef<Path>, dsl: &DSL<D>) -> Vec<Task<D>> {
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
                    inputs.iter().map(|i| dsl.val_of_prim(&i.replace(" ", "").into()).expect(&format!("failed to parse {i} as a Val"))).collect(),
                    dsl.val_of_prim(&output.replace(" ", "").into()).unwrap()
                )
            }).collect(),
        )
    }).collect();
    tasks
}

fn parse_tracked(path: &dyn AsRef<Path>) -> Vec<(String,String)> {
    let json: serde_json::Value = from_reader(File::open(path).expect("file not found")).expect("json deserializing error");
    let task_soln: Vec<(String,String)> = json.as_array().unwrap().iter().map(|entry| (entry["task"].as_str().unwrap().to_string(),entry["soln"].as_str().unwrap().to_string())).collect();
    task_soln
}


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

fn run<D: Domain>(args: &Args) {
    let model = uniform_model();
    let dsl = D::new_dsl();
    let tasks: Vec<Task<D>> = args.file.as_ref().map(|path| parse_tasks(path,&dsl)).unwrap_or(vec![]);

    if let Some(track_all) =  &args.track_all {
        let to_track = parse_tracked(track_all);
        let mut hits = vec![];
        let mut misses = vec![];
        for (task_name, soln) in to_track {
            println!("Tracking {} -> {}", task_name, soln);
            let mut cfg = args.top_down_cfg.clone();
            cfg.track = Some(soln.clone());
            cfg.one_soln = true;
            cfg.min_ll = Some(-100.);
            let solns = top_down(&model, &dsl, &tasks, &cfg);
            if solns.is_empty() {
                misses.push((task_name, soln));
            } else {
                assert_eq!(solns.len(), 1);
                assert_eq!(solns[0].1.to_string(), strip_lambdas(&soln));
                hits.push((task_name, soln, solns[0].1.ll));
            }
        }
        println!("\n===SUMMARY===");
        println!("Hits: {}/{}", hits.len(), hits.len() + misses.len());
        hits.sort_by_key(|(_,_,ll)| -*ll);
        for (task_name, soln, ll) in hits {
            println!("{} {} [ll={}]: {}", "Solved".green(), task_name, ll,  soln);
        }
        for (task_name, soln) in misses {
            println!("{} {} -> {}", "Miss".red(), task_name, soln);
        }
        return
    }


    top_down(&model, &dsl, &tasks, &args.top_down_cfg);
}


fn uniform_model() -> impl ProbabilisticModel {
    OrigamiModel::new(
        SymmetryRuleModel::new(
                UniformModel::new(NotNan::new(0.).unwrap(),NotNan::new(0.).unwrap()),
                 &[(0,"car","cons"), // arg_idx, parent, child
                        (0,"car","empty"),
                        (0,"cdr","cons"),
                        (0,"cdr","empty"),
                        (0,"+","0"),
                        (1,"+","0"),
                        (1,"-","0"),
                        (0,"+","+"),
                        (0,"*","*"),
                        (0,"*","0"),
                        (1,"*","0"),
                        (0,"*","1"),
                        (1,"*","1"),
                        (0,"empty?","cons"),
                        (0,"empty?","empty")]),
        "fix1".into(),
        "fix".into()
    )
}
