cp "$1" Rust/Egg/src/scheduler.rs
lake build
(cd Lean/Egg/Benchmarks; ./bench.sh)
