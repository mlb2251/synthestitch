# Synthestitch


Run synthesis with 8 threads (should be ~4M expansion/s):
```
cargo run --release --bin=top_down -- data/origami/origami.json --threads 8
```
(defaults to 1 thread without the thread count)


Make sure all solutions can be found in origami:
```
cargo run --release --bin=top_down -- data/origami/origami.json --track-all=data/origami/origami_solutions.json
```

Flamegraphing on a ~30s example:
```
CARGO_PROFILE_RELEASE_DEBUG=1 cargo flamegraph --root --open --deterministic --output=flamegraph.svg --bin=top_down -- data/origami/origami_simple.json --num-solns=5
```
