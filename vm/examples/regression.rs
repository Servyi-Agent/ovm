//! Run the local regression suite in `tests/regression`.
//!
//! Usage:
//!   cargo run -p vm --example regression
//!   cargo run -p vm --example regression -- tests/regression/issue-1-*.js
//!   KETTEVM_GC_STRESS=1 cargo run -p vm --example regression
//!
//! Every `.js` file under the given paths (except `harness/`) runs in a
//! fresh VM with `tests/regression/harness/assert.js` prepended.

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};

use mark_sweep::{MarkSweep, MarkSweepConfig};
use vm::{DefaultInterpreter, JSRuntime, JavascriptCompiler, VM};

fn main() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("vm crate has a parent")
        .to_path_buf();
    let regression = root.join("tests").join("regression");
    let harness = std::fs::read_to_string(regression.join("harness").join("assert.js"))
        .expect("tests/regression/harness/assert.js");

    let mut roots: Vec<PathBuf> = std::env::args().skip(1).map(PathBuf::from).collect();
    if roots.is_empty() {
        roots.push(regression);
    }

    let mut tests = Vec::new();
    for root in &roots {
        if root.is_dir() {
            collect(root, &mut tests);
        } else if root.extension().is_some_and(|e| e == "js") {
            tests.push(root.clone());
        }
    }
    tests.sort();

    if tests.is_empty() {
        eprintln!("regression: no tests found under {roots:?}");
        std::process::exit(1);
    }

    println!("running {} regression test(s)", tests.len());
    let mut failed = 0;
    for test in &tests {
        let name = test
            .strip_prefix(&root)
            .unwrap_or(test)
            .display()
            .to_string();
        let result = catch_unwind(AssertUnwindSafe(|| run_one(&harness, test)));
        match result {
            Ok(Ok(())) => println!("PASS {name}"),
            Ok(Err(error)) => {
                failed += 1;
                println!("FAIL {name}: {error}");
            }
            Err(_) => {
                failed += 1;
                println!("PANIC {name}");
            }
        }
    }

    println!(
        "\n{} passed, {} failed, {} total",
        tests.len() - failed,
        failed,
        tests.len()
    );
    if failed > 0 {
        std::process::exit(1);
    }
}

fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            if path.file_name().is_some_and(|name| name == "harness") {
                continue;
            }
            collect(&path, out);
        } else if path.extension().is_some_and(|e| e == "js") {
            out.push(path);
        }
    }
}

fn run_one(harness: &str, path: &Path) -> Result<(), String> {
    let source = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
    let program = format!("{harness}\n{source}");

    let vm = VM::new::<MarkSweep, DefaultInterpreter>(MarkSweepConfig::default())
        .map_err(|e| format!("{e:?}"))?
        .add::<JSRuntime>()
        .map_err(|e| format!("{e:?}"))?;
    if std::env::var_os("KETTEVM_GC_STRESS").is_some() {
        vm.arm_gc_stress();
    }
    let mut thread = vm.attach();
    let value = thread
        .eval::<JavascriptCompiler>(&program)
        .map_err(|e| e.to_string())?;

    let threw = {
        let heap = thread.heap();
        value == heap.known().exception.get(heap).raw()
    };
    if threw {
        let exception = thread
            .take_pending_exception()
            .map(|e| format!("{e:?}"))
            .unwrap_or_else(|| "uncaught exception".into());
        return Err(exception);
    }
    Ok(())
}
