pub use vm_core::*;

#[cfg(not(feature = "fast"))]
pub use ::interpreter::match_loop::MatchInterpreter;
/// Compatibility alias for the old crate's name.
#[cfg(not(feature = "fast"))]
pub use ::interpreter::match_loop::MatchInterpreter as MatchLoopInterpreter;
pub use vm_core::Interpreter;

#[cfg(feature = "fast")]
pub use ::interpreter::BecomeInterpreter;

/// The interpreter the `kettevm` binary runs on. Enabling the `fast` feature
/// (nightly-only) picks the tail-call interpreter; otherwise the portable
/// match-loop interpreter is used.
#[cfg(feature = "fast")]
pub type DefaultInterpreter = ::interpreter::BecomeInterpreter;
#[cfg(not(feature = "fast"))]
pub type DefaultInterpreter = ::interpreter::match_loop::MatchInterpreter;

pub use js_runtime::JSRuntime;
pub use kette_runtime::KetteRuntime;

pub use js_compiler::JavascriptCompiler;
pub use kette_compiler::KetteCompiler;

pub trait VmEval {
    fn eval<C: Compiler>(&self, source: &str) -> Result<Value, ScriptError>;
}

impl VmEval for VM {
    fn eval<C: Compiler>(&self, source: &str) -> Result<Value, ScriptError> {
        let mut thread = self.attach();
        thread.eval::<C>(source)
    }
}
