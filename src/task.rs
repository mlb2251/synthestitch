use std::{path::Path, fs::File};

use lambdas::*;
use serde_json::de::from_reader;

pub type TaskName = Symbol;

#[derive(Clone, Debug)]
pub struct Task<D: Domain> {
    pub name: TaskName,
    pub tp: SlowType,
    pub ios: Vec<IO<D>>
}

impl<D:Domain> Task<D> {
    pub fn new(name: &str, tp: SlowType, ios: Vec<IO<D>>) -> Task<D> {
        Task {name: name.into(), tp, ios}
    }
}

#[derive(Clone, Debug)]
pub struct IO<D: Domain> {
    pub inputs: Vec<Val<D>>,
    pub output: Val<D>
}

impl<D:Domain> IO<D> {
    pub fn new(inputs: Vec<Val<D>>, output: Val<D>) -> IO<D> {
        IO { inputs, output }
    }
}

pub fn parse_tasks<D: Domain>(path: &dyn AsRef<Path>, dsl: &DSL<D>) -> Vec<Task<D>> {
    let json: serde_json::Value = from_reader(File::open(path).expect("file not found")).expect("json deserializing error");
    let tasks: Vec<Task<D>> = json.as_array().unwrap().iter().map(|task| {
        Task::new(
            task["name"].as_str().unwrap(),
            task["tp"].as_str().unwrap().parse().unwrap(),
            task["ios"].as_array().unwrap().iter().map(|io| {
                let inputs: Vec<String> = io.as_array().unwrap()[0].as_array().unwrap().iter().map(|i| i.as_str().unwrap().to_string()).collect();
                let output: String = io.as_array().unwrap()[1].as_str().unwrap().to_string();
                IO::new(
                    // remove all spaces since prims cant have spaces within them
                    inputs.iter().map(|i| dsl.val_of_prim(&i.replace(" ", "").into()).unwrap_or_else(|| panic!("{}", "failed to parse {i} as a Val"))).collect(),
                    dsl.val_of_prim(&output.replace(" ", "").into()).unwrap()
                )
            }).collect(),
        )
    }).collect();
    tasks
}