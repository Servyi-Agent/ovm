//! Tiny JS runner for comparing the three interpreter shells.
//!
//!     cargo +nightly run --release --example bench_js -- <match|new|become> files...

use interpreter_become::BecomeInterpreter;
use interpreter_become::match_loop::MatchInterpreter as BecomeMatchInterpreter;
use interpreter_match_loop::MatchLoopInterpreter;
use js_compiler::{SourceMode, compile_js};
use js_runtime::JSRuntime;
use mark_sweep::{MarkSweep, MarkSweepConfig};
use vm_core::{Interpreter, VM};

fn run<I: Interpreter>(src: &str) {
    let vm = VM::new::<MarkSweep, I>(MarkSweepConfig::default())
        .expect("heap")
        .add::<JSRuntime>()
        .expect("js runtime");
    let mut thread = vm.attach();
    thread
        .run_source(src, compile_js, SourceMode::Script)
        .expect("script runs");
    if let Some(ex) = thread.take_pending_exception() {
        eprintln!("uncaught exception: {ex:?}");
        std::process::exit(1);
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let which = args.next().expect("interpreter name");
    let mut src = String::new();
    for path in args {
        src.push_str(&std::fs::read_to_string(&path).expect("read script"));
        src.push('\n');
    }
    match which.as_str() {
        "match" => run::<MatchLoopInterpreter>(&src),
        "become" => run::<BecomeInterpreter>(&src),
        "become_match" => run::<BecomeMatchInterpreter>(&src),
        other => panic!("unknown interpreter {other}"),
    }
}
