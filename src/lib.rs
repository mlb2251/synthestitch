// pub mod bottom_up;
pub mod top_down;
pub mod task;
pub mod model;
mod util;
pub use {
    model::*,
    task::*,
    lambdas::*,
    util::*,
    ordered_float::NotNan,
    top_down::*,
};

use colorful::Colorful;
// use top_down::*;
use std::fs::File;
use std::path::Path;
use clap::{Parser,ArgEnum};
use serde::Serialize;
use std::path::PathBuf;
use serde_json::de::from_reader;
use serde_json::{json, Value};
use std::collections::BTreeMap;
use lambdas::domains::simple::*;
use lambdas::domains::prim_lists::*;


/// Synthesizer
#[derive(Parser, Debug, Serialize)]
#[clap(name = "Synthesizer")]
pub struct Args {
    /// json input file
    // #[clap(parse(from_os_str))]
    // pub file: Option<PathBuf>,
    #[clap(long, parse(from_os_str))]
    pub file: Option<std::path::PathBuf>,

    /// json output file
    #[clap(short, long, parse(from_os_str), default_value = "out/out.json")]
    pub out: PathBuf,

    /// Probabilistic Model to use
    #[clap(short, long, arg_enum, default_value = "uniform")]
    pub model: ModelChoice,

    /// Domain to enumerate from
    #[clap(short, long, arg_enum, default_value = "list")]
    pub domain: DomainChoice,

    /// json solutions file (for debugging)
    #[clap(long, parse(from_os_str))]
    pub track_all: Option<PathBuf>,

    #[clap(flatten)]
    pub top_down_cfg: TopDownConfig,

    /// Optional path to a JSON file with unigram probabilities
    #[clap(long)]
    pub unigrams_path: Option<String>,

    /// Probability fallback for primitives
    #[clap(long, default_value="0.0")]
    pub primitive_fallback: f32,

    /// Probability fallback for primitives
    #[clap(long, default_value="0.0")]
    pub variable_fallback: f32,

    //Optional path to a JSOn file with bigram probabilities
    #[clap(long)]
    pub bigrams_path: Option<String>
}

#[derive(Debug, Clone, ArgEnum, Serialize)]
pub enum ModelChoice {
    Uniform,
    Unigram,
    Bigram
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

fn parse_tracked(path: &dyn AsRef<Path>) -> Vec<(TaskName,String)> {
    let json: serde_json::Value = from_reader(File::open(path).expect("file not found")).expect("json deserializing error");
    let task_soln: Vec<(TaskName,String)> = json.as_array().unwrap().iter().map(|entry| (entry["task"].as_str().unwrap().into(),entry["soln"].as_str().unwrap().to_string())).collect();
    task_soln
}

pub fn dispatch_domain(args: &Args) -> String {

    match &args.domain {
        DomainChoice::Simple => {
            return dispatch_model::<SimpleVal>(args);
        },
        DomainChoice::List => {
            return dispatch_model::<ListVal>(args);
        },
    }
}

fn dispatch_model<D: Domain>(args: &Args) -> String {
    match &args.model {
        ModelChoice::Uniform => {
               let model = uniform_model();
               run::<D, _>(args, &model)
        },
        ModelChoice::Unigram => {
            let unigrams: std::collections::HashMap<String, f32> = if let Some(path) = args.unigrams_path.as_ref() {
                let json_str = std::fs::read_to_string(path)
                    .expect("Failed to read JSON file");
                serde_json::from_str(&json_str)
                    .expect("Failed to parse JSON file")
            } else {
                std::collections::HashMap::new()
            };  // get unigram probability table

            let prim_ll_fallback = NotNan::new(args.primitive_fallback).unwrap();
            let var_ll_fallback = NotNan::new(args.variable_fallback).unwrap();
            let model = unigram_model(unigrams, var_ll_fallback, prim_ll_fallback);
            run::<D, _>(args, &model)
        }
        ModelChoice::Bigram => {
            let bigrams: std::collections::HashMap<(String, usize, String), f32> = if let Some(path) = args.bigrams_path.as_ref() {
                let json_str = std::fs::read_to_string(path)
                    .expect("Failed to read bigram JSON file");

                let raw: std::collections::HashMap<String, f32> = serde_json::from_str(&json_str)
                    .expect("Failed to parse bigram JSON as flat string-keyed map");


                raw.into_iter()
                    .map(|(key, value)| {
                        let parts: Vec<&str> = key.split('|').collect();
                        assert_eq!(parts.len(), 3, "Malformed bigram key: {}", key);
                        let parent = parts[0].to_string();
                        let arg_idx = parts[1].parse::<usize>()
                            .expect("Invalid arg_idx in bigram key");
                        let current = parts[2].to_string();
                        ((parent, arg_idx, current), value)
                    })
                    .collect()
                    }  else {
                        std::collections::HashMap::new()
                };

            let fallback_ll = NotNan::new(args.primitive_fallback).unwrap();
            let model = bigram_model(bigrams, fallback_ll);
            run::<D, _>(args, &model)
        }
    }
}

fn run<D: Domain, M: ProbabilisticModel>(args: &Args, model : &M ) -> String { 
    let dsl = D::new_dsl();
    let tasks: Vec<Task<D>> = args.file.as_ref().map(|path| parse_tasks(path,&dsl)).unwrap_or(vec![]);

    if let Some(track_all) =  &args.track_all {
        let to_track = parse_tracked(track_all);
        let mut hits = vec![];
        let mut misses = vec![];
        for (task_name, target_soln) in to_track {
            println!("Tracking {} -> {}", task_name, target_soln);
            let mut cfg = args.top_down_cfg.clone();
            cfg.track = Some(target_soln.clone());
            cfg.one_soln = true;
            cfg.min_ll = Some(-100.);
            cfg.threads = 1;
            let search_progress = top_down(model, &dsl, &tasks, &cfg);
            let solns = search_progress.solutions;
            if solns[&task_name].is_empty() {
                misses.push((task_name, target_soln));
            } else {
                assert_eq!(solns[&task_name].len(), 1);
                let soln = solns[&task_name][0].clone();
                assert_eq!(soln.expr.to_string(), strip_lambdas(&target_soln));
                hits.push((task_name, soln));
            }
        }
        // println!("\n===SUMMARY===");
        // println!("Hits: {}/{}", hits.len(), hits.len() + misses.len());
        // hits.sort_by_key(|(_,soln)| -soln.ll);
        // for (task_name, soln) in hits {
        //     println!("{} {}: {}", "Solved".green(), task_name,  soln);
        // }
        // for (task_name, soln) in misses {
        //     println!("{} {} -> {}", "Miss".red(), task_name, soln);
        // }
        // return

        // Build a small JSON summary to return
        // let payload = json!({
        //     "summary": {
        //         "hits": hits.iter().map(|(t, s)| json!({"task": t, "ll": s.ll, "expr": s.expr.to_string()})).collect::<Vec<_>>(),
        //         "misses": misses.iter().map(|(t, target)| json!({"task": t, "target": target})).collect::<Vec<_>>(),
        //     }
        // });
        // return serde_json::to_string(&payload).unwrap();
    }


    // top_down(model, &dsl, &tasks, &args.top_down_cfg);
    // Normal enumeration path
    let search_progress = top_down(model, &dsl, &tasks, &args.top_down_cfg);

    // Convert solutions to JSON
    let mut sols_map: BTreeMap<String, Value> = BTreeMap::new();
    for (task, sols) in &search_progress.solutions {
        let items: Vec<Value> = sols.iter().map(|sol| {
            json!({ "ll": sol.ll.into_inner(), "expr": sol.expr.to_string() })
        }).collect();
        let key: String = task.as_ref().to_owned();
        sols_map.insert(key, Value::Array(items));
    }

    serde_json::to_string(&json!({ "solutions": sols_map })).unwrap()
}


fn uniform_model() -> impl ProbabilisticModel {
    // OrigamiModel::new(
        // SymmetryRuleModel::new(
                UniformModel::new(NotNan::new(0.).unwrap(),NotNan::new(0.).unwrap())//,
                //  &[(0,"car","cons"), // arg_idx, parent, child
                //         (0,"car","empty"),
                //         (0,"cdr","cons"),
                //         (0,"cdr","empty"),
                //         (0,"+","0"),
                //         (1,"+","0"),
                //         (1,"-","0"),
                //         (0,"+","+"),
                //         (0,"*","*"),
                //         (0,"*","0"),
                //         (1,"*","0"),
                //         (0,"*","1"),
                //         (1,"*","1"),
                //         (0,"empty?","cons"),
                //         (0,"empty?","empty")]),
    //     "fix1".into(),
    //     "fix".into()
    // )
}

fn unigram_model(
    unigrams: std::collections::HashMap<String, f32>,
    var_ll_fallback: NotNan<f32>,
    prim_ll_fallback: NotNan<f32>
    ) -> impl ProbabilisticModel {
        // OrigamiModel::new(
        //     SymmetryRuleModel::new(
                    UnigramModel::new(unigrams, var_ll_fallback, prim_ll_fallback)
        //             &[(0,"car","cons"), // arg_idx, parent, child
        //                     (0,"car","empty"),
        //                     (0,"cdr","cons"),
        //                     (0,"cdr","empty"),
        //                     (0,"+","0"),
        //                     (1,"+","0"),
        //                     (1,"-","0"),
        //                     (0,"+","+"),
        //                     (0,"*","*"),
        //                     (0,"*","0"),
        //                     (1,"*","0"),
        //                     (0,"*","1"),
        //                     (1,"*","1"),
        //                     (0,"empty?","cons"),
        //                     (0,"empty?","empty")]),
        //     "fix1".into(),
        //     "fix".into()
        // )
    }

fn bigram_model(
    bigrams: std::collections::HashMap<(String, usize, String), f32>,
    fallback_ll: NotNan<f32>,
    ) -> impl ProbabilisticModel {
        // OrigamiModel::new(
        //     SymmetryRuleModel::new(
                    BigramModel::new(bigrams, fallback_ll)
        //             &[(0,"car","cons"), // arg_idx, parent, child
        //                     (0,"car","empty"),
        //                     (0,"cdr","cons"),
        //                     (0,"cdr","empty"),
        //                     (0,"+","0"),
        //                     (1,"+","0"),
        //                     (1,"-","0"),
        //                     (0,"+","+"),
        //                     (0,"*","*"),
        //                     (0,"*","0"),
        //                     (1,"*","0"),
        //                     (0,"*","1"),
        //                     (1,"*","1"),
        //                     (0,"empty?","cons"),
        //                     (0,"empty?","empty")]),
        //     "fix1".into(),
        //     "fix".into()
        // )
    }