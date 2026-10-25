use interpreter_become::match_loop::MatchInterpreter;
use js_compiler::JavascriptCompiler;
use js_runtime::JSRuntime;
use mark_sweep::{MarkSweep, MarkSweepConfig};
use vm_core::{Interpreter, VM};

fn run<I: Interpreter>(src: &str) {
    let vm = VM::new::<MarkSweep, I>(MarkSweepConfig::default())
        .unwrap()
        .add::<JSRuntime>()
        .unwrap();
    vm.arm_gc_stress();
    let mut thread = vm.attach();
    thread.eval::<JavascriptCompiler>(src).expect("script runs");
    assert!(thread.take_pending_exception().is_none(), "script threw");
}

fn source(relative: &str) -> String {
    [
        format!("{}/../{relative}", env!("CARGO_MANIFEST_DIR")),
        relative.to_string(),
    ]
    .iter()
    .find_map(|p| std::fs::read_to_string(p).ok())
    .unwrap_or_else(|| panic!("missing {relative}"))
}

#[test]
fn fannkuch() {
    run::<MatchInterpreter>(&source("benchmarks/fannkuch/fannkuch.js"));
}

#[test]
fn nbody() {
    run::<MatchInterpreter>(&source("benchmarks/nbody/nbody.js"));
}

/// Octane's harness objects are not part of the VM; deltablue only needs
/// the constructors so suite registration doesn't throw.
const PRELUDE: &str = r#"
function BenchmarkSuite() {}
function Benchmark() {}
function alert(m) { throw new Error("ALERT: " + m); }
"#;

#[test]
fn deltablue() {
    let src =
        format!("{PRELUDE}{}\ndeltaBlue();\n", source("benchmarks/octane/deltablue/deltablue.js"));
    run::<MatchInterpreter>(&src);
}
