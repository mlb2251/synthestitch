use lambdas::*;

#[derive(Clone)]
pub struct Task<D: Domain> {
    pub name: String,
    pub tp: SlowType,
    pub ios: Vec<IO<D>>
}

impl<D:Domain> Task<D> {
    pub fn new(name: String, tp: SlowType, ios: Vec<IO<D>>) -> Task<D> {
        Task {name, tp, ios}
    }
}

#[derive(Clone)]
pub struct IO<D: Domain> {
    pub inputs: Vec<Val<D>>,
    pub output: Val<D>
}

impl<D:Domain> IO<D> {
    pub fn new(inputs: Vec<Val<D>>, output: Val<D>) -> IO<D> {
        IO { inputs, output }
    }
}