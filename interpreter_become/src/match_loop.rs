//! Sketch of the next match-loop interpreter: one stride-agnostic loop,
//! `step::<1>` for narrow instructions and `step::<2>` for wide ones.
//! Flow-free: hot state stays in locals; only `Ctx` owns interpreter state.

use bytecode::Opcode;

use vm_core::ic::{ElementHit, Hit, InlineCache, MonoProbe};
use vm_core::interpreter::{base, unwind};
use vm_core::proxy::Proxy;

use crate::RootsArg;
use crate::slow::{
    add_body, bitwise_body, compare_body, global_load_body, incdec_body, keyed_store_body,
    store_named_tail_body,
};
use crate::utils::{
    StagedCall, call_scatter_start, call_window_start, proxy_apply_staged, resolve_target,
};
use vm_core::{
    Acc, CallTarget, CallableInfoObject, Callee, Coercion, ContextObject, Convert, Ctx,
    DenseString, EntryFn, FrameMeta, Handle, HandleScope, HandleSlice, Heap, HostCtx, Interpreter,
    Key, LoadOutcome, Lookup, NativeIndex, Object, Ops, Regs, Smi, StoreSemantics, Tagged,
    Termination, ThreadState, Unwind, VM, Value, VmError, raise_runtime,
};

pub struct MatchInterpreter;

impl Interpreter for MatchInterpreter {
    const EXECUTE: EntryFn = execute;
}

#[inline(always)]
fn offset(code: *const u8, pc: usize) -> *const u8 {
    unsafe { code.add(pc) }
}

/// Successor sentinel meaning "this instruction threw". The faulting pc
/// rides in `Ctx::throw_pc`; the loop only compares the returned pointer.
#[inline(always)]
fn throw_ptr() -> *const u8 {
    usize::MAX as *const u8
}

/// Decode the current instruction into caller-named locals. `$op` is the
/// literal the handler matched, so both `operands().len()` and the
/// successor pointer fold at compile time. Macro hygiene forbids the
/// macro from binding `$ops`/`$next` itself, so — exactly like become's
/// exit macros — the caller passes the names in.
macro_rules! decode {
    ($op:ident, $ip:expr, $ops:ident, $next:ident) => {
        let $ops = Ops::<STRIDE>::new($ip, Opcode::$op);
        let $next =
            unsafe { $ip.add(base::<STRIDE>() + STRIDE * const { Opcode::$op.operands().len() }) };
    };
    ($op:ident, $ip:expr, $ctx:expr, $ops:ident, $next:ident, $pc:ident, $next_pc:ident) => {
        decode!($op, $ip, $ops, $next);
        let $pc = $ip as usize - $ctx.code_ptr() as usize;
        let $next_pc = $pc + ($next as usize - $ip as usize);
    };
}

/// The current and successor byte offsets, for a cold tail that must
/// re-enter after a possible collection.
macro_rules! offsets {
    ($ip:expr, $next:expr, $ctx:expr) => {{
        let pc = $ip as usize - $ctx.code_ptr() as usize;
        (pc, pc + ($next as usize - $ip as usize))
    }};
}

/// Exit to the decoded successor pointer.
macro_rules! next {
    ($next:expr) => {
        return $next
    };
}

/// Exit to an explicit instruction pointer (a jump target).
macro_rules! dispatch {
    ($p:expr) => {
        return $p
    };
}

/// Read the accumulator.
macro_rules! acc {
    ($acc:expr, $ctx:expr) => {
        $acc.get($ctx.heap())
    };
}

macro_rules! set_acc {
    ($acc:expr, $v:expr) => {
        *$acc = Acc::set($v)
    };
}

macro_rules! set_acc_smi {
    ($acc:expr, $bits:expr) => {
        *$acc = Acc::from_smi_bits($bits)
    };
}

/// Tail into a cold handler. The cold handler takes the same
/// `(ctx, ip, regs, acc, roots)` shape as a hot handler so the call site
/// reads like become's `tail!(path)`.
macro_rules! tail {
    ($slow:ident, $ip:expr, $regs:expr, $acc:expr, $ctx:expr, $roots:expr) => {
        return $slow::<STRIDE>($ip, $regs, $acc, $ctx, $roots)
    };
}

/// Fold a cold-tail result into the accumulator and re-enter at the
/// faulting instruction when it is the exception sentinel, or after the
/// instruction otherwise. The loop detects the sentinel in `acc` and
/// unwinds; a null successor means "return the accumulator".
macro_rules! reenter {
    ($ctx:expr, $acc:expr, $pc:expr, $next_pc:expr, $v:expr) => {{
        let v = $v;
        let raw = v.raw().to_bits();
        // Consume the value (and with it the heap borrow) before touching
        // `ctx` again; the sentinel word is then read through a fresh
        // shared borrow.
        *$acc = Acc::set(v);
        let sentinel = {
            let heap = $ctx.heap();
            heap.known().exception.as_tagged(heap).raw().to_bits()
        };
        $ctx.reload_code();
        if raw == sentinel {
            $ctx.set_throw_pc($pc);
            throw_ptr()
        } else {
            offset($ctx.code_ptr(), $next_pc)
        }
    }};
}

/// Raise a `VmError`, re-deriving the code pointer (materializing the
/// exception may collect), and re-enter at the faulting instruction.
macro_rules! raise {
    ($ctx:expr, $acc:expr, $pc:expr, $err:expr) => {{
        *$acc = Acc::set($ctx.raise_tag($err));
        $ctx.reload_code();
        $ctx.set_throw_pc($pc);
        throw_ptr()
    }};
}

pub fn execute<'a>(
    vm: &VM,
    heap: &'a mut Heap,
    state: &ThreadState,
    callable: Handle<'_, Object>,
    args: HandleSlice<'_>,
    new_target: Option<Handle<'_, Value>>,
) -> Result<Tagged<'a, Value>, VmError> {
    let stack = state.stack();

    let saved_top = stack.top();
    let was_active = state.is_frame_active();
    let outer = was_active.then(|| state.frame_base());

    state.handle_scope(|scope| {
        let result = start(vm, heap, state, callable, args, new_target)?;
        let rooted = scope.handle(result);

        stack.set_top(saved_top);
        if let Some(outer) = outer {
            state.set_frame_base(outer);
        } else {
            state.set_frame_active(false);
        }
        Ok(rooted.as_tagged(heap))
    })
}

fn start<'b>(
    vm: &'b VM,
    heap: &'b mut Heap,
    state: &'b ThreadState,
    callable: Handle<'_, Object>,
    args: HandleSlice<'_>,
    new_target: Option<Handle<'b, Value>>,
) -> Result<Tagged<'b, Value>, VmError> {
    match callable.as_tagged(heap).erase().call_target(heap) {
        None => Err(VmError::Type),
        Some(CallTarget::Proxy(_)) => Err(VmError::Type),
        Some(CallTarget::Native(rt)) => {
            let f = vm.runtime(rt);
            let nctx = HostCtx::new(vm, heap, state);
            Ok(f(nctx, new_target, args.as_args()))
        }
        Some(CallTarget::Bytecode {
            target,
            info,
            context,
            kind,
            ..
        }) => {
            if new_target.is_none() && kind.is_class_constructor() {
                return Err(VmError::Type);
            }
            let stack = state.stack();
            let new_target_value = match &new_target {
                Some(nt) => nt.as_tagged(heap).erase(),
                None => heap.known().undefined.as_tagged(heap).erase(),
            };
            let frame = stack.push_frame_values(
                heap,
                FrameMeta::ROOT,
                Callee {
                    callable: target.erase(),
                    info,
                    context: context.erase(),
                },
                new_target_value,
                args.as_tagged(),
            )?;
            state.set_frame_base(frame.base);
            state.set_frame_active(true);

            let mut ctx = Ctx::new(vm, state, heap, frame.base);
            let value = dispatch(&mut ctx)?;
            // Safety: `value` came from the rooted accumulator slot and `heap`
            // is still borrowed here.
            Ok(unsafe { Tagged::from_value_unchecked(value) })
        }
    }
}

fn dispatch<'h>(ctx: &mut Ctx<'h, 'h>) -> Result<Value, VmError> {
    let mut ip = ctx.code_ptr();
    let mut regs = unsafe { Regs::new(ctx.regs_ptr()) };
    let mut acc = Acc::set(ctx.heap().known().undefined.as_tagged(ctx.heap()).erase());
    let mut frame_base = ctx.frame_base();
    let roots = RootsArg::from_heap(ctx.heap());

    loop {
        step::<1>(ctx, &mut ip, &mut regs, &mut acc, &mut frame_base, roots);

        // A null successor is become's `return acc`: the execution is done.
        if ip.is_null() {
            return Ok(acc.get(ctx.heap()).raw());
        }

        // The throw sentinel is become's `throw_dispatch`: unwind from
        // the faulting pc recorded by the handler. Two pointer compares
        // are the whole per-instruction flow cost.
        if ip == throw_ptr() {
            match unwind(ctx, ctx.throw_pc()) {
                Unwind::Caught { pc, ex } => {
                    acc = Acc::set(ex);
                    frame_base = ctx.frame_base();
                    regs = unsafe { Regs::new(ctx.regs_ptr()) };
                    ctx.reload_code();
                    ip = offset(ctx.code_ptr(), pc);
                }
                Unwind::Escaped => {
                    return Ok(ctx
                        .heap()
                        .known()
                        .exception
                        .as_tagged(ctx.heap())
                        .erase()
                        .raw());
                }
            }
        }
    }
}

#[inline(always)]
fn step<'h, const STRIDE: usize>(
    ctx: &mut Ctx<'h, 'h>,
    ip: &mut *const u8,
    regs: &mut Regs,
    acc: &mut Acc,
    frame_base: &mut usize,
    roots: RootsArg<'h>,
) {
    let op = unsafe { Opcode::from_byte_unchecked(*(*ip).add(if STRIDE == 2 { 1 } else { 0 })) };

    *ip = match op {
        Opcode::Load => op_load::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::Store => op_store::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::LoadSmi => op_load_smi::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::LoadZero => op_load_zero::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::LoadConstant => op_load_constant::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::LoadUndefined => op_load_undefined::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::LoadNull => op_load_null::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::LoadTrue => op_load_true::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::LoadFalse => op_load_false::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::LoadHole => op_load_hole::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::LoadNewTarget => op_load_new_target::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::LoadContext => op_load_context::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::LoadCurrentClosure => {
            op_load_current_closure::<STRIDE>(*ip, *regs, acc, ctx, roots)
        }
        Opcode::LoadGlobal => op_load_global::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::LoadGlobalNoThrow => op_load_global_no_throw::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::LoadNamedProperty => op_load_named_property::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::LoadKeyedProperty => op_load_keyed_property::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::LoadKeyedPropertyReg => {
            op_load_keyed_property_reg::<STRIDE>(*ip, *regs, acc, ctx, roots)
        }
        Opcode::LoadElementImm => op_load_element_imm::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::Move => op_move::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::StoreGlobal => op_store_global::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::AddParent => op_add_parent::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::Delete => op_delete::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::Add => op_add::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::Sub => op_sub::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::AddImmediate => op_add_immediate::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::SubImmediate => op_sub_immediate::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::ShiftRightImmediate => {
            op_shift_right_immediate::<STRIDE>(*ip, *regs, acc, ctx, roots)
        }
        Opcode::IncLoc => op_inc_loc::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::DecLoc => op_dec_loc::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::Equal => op_equal::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::CompareJump => op_compare_jump::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::Jump => op_jump::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::JumpLoop => op_jump_loop::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::JumpIfTruthy => op_jump_if_truthy::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::JumpIfFalsy => op_jump_if_falsy::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::JumpIfNotUndefined => {
            op_jump_if_not_undefined::<STRIDE>(*ip, *regs, acc, ctx, roots)
        }
        Opcode::Throw => op_throw::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::CreateClosure => op_create_closure::<STRIDE>(*ip, *regs, acc, ctx, roots),
        Opcode::StoreKeyedProperty => {
            op_store_keyed_property::<STRIDE>(*ip, *regs, acc, ctx, roots, false)
        }
        Opcode::StoreKeyedPropertyNoShadow => {
            op_store_keyed_property::<STRIDE>(*ip, *regs, acc, ctx, roots, true)
        }
        Opcode::StoreNamedProperty => {
            op_store_named_property::<STRIDE>(*ip, *regs, acc, ctx, roots, false)
        }
        Opcode::StoreNamedPropertyNoShadow => {
            op_store_named_property::<STRIDE>(*ip, *regs, acc, ctx, roots, true)
        }
        Opcode::Call => {
            let next = op_call::<STRIDE>(*ip, *regs, acc, ctx, roots);
            *regs = unsafe { Regs::new(ctx.regs_ptr()) };
            *frame_base = ctx.frame_base();
            next
        }
        Opcode::CallNoFeedback => {
            let next = op_call_no_feedback::<STRIDE>(*ip, *regs, acc, ctx, roots);
            *regs = unsafe { Regs::new(ctx.regs_ptr()) };
            *frame_base = ctx.frame_base();
            next
        }
        Opcode::CallFunction0 => {
            let next = op_call_function::<STRIDE, 0>(*ip, *regs, acc, ctx, roots);
            *regs = unsafe { Regs::new(ctx.regs_ptr()) };
            *frame_base = ctx.frame_base();
            next
        }
        Opcode::CallFunction1 => {
            let next = op_call_function::<STRIDE, 1>(*ip, *regs, acc, ctx, roots);
            *regs = unsafe { Regs::new(ctx.regs_ptr()) };
            *frame_base = ctx.frame_base();
            next
        }
        Opcode::CallFunction2 => {
            let next = op_call_function::<STRIDE, 2>(*ip, *regs, acc, ctx, roots);
            *regs = unsafe { Regs::new(ctx.regs_ptr()) };
            *frame_base = ctx.frame_base();
            next
        }
        Opcode::CallMethod0 => {
            let next = op_call_method::<STRIDE, 0>(*ip, *regs, acc, ctx, roots);
            *regs = unsafe { Regs::new(ctx.regs_ptr()) };
            *frame_base = ctx.frame_base();
            next
        }
        Opcode::CallMethod1 => {
            let next = op_call_method::<STRIDE, 1>(*ip, *regs, acc, ctx, roots);
            *regs = unsafe { Regs::new(ctx.regs_ptr()) };
            *frame_base = ctx.frame_base();
            next
        }
        Opcode::CallMethod2 => {
            let next = op_call_method::<STRIDE, 2>(*ip, *regs, acc, ctx, roots);
            *regs = unsafe { Regs::new(ctx.regs_ptr()) };
            *frame_base = ctx.frame_base();
            next
        }
        Opcode::CallRuntime => {
            let next = op_call_runtime::<STRIDE>(*ip, *regs, acc, ctx, roots);
            *regs = unsafe { Regs::new(ctx.regs_ptr()) };
            *frame_base = ctx.frame_base();
            next
        }
        Opcode::Wide => {
            step::<2>(ctx, ip, regs, acc, frame_base, roots);
            *ip
        }
        Opcode::Return => {
            let next = op_return(*ip, *regs, acc, ctx, roots);
            *regs = unsafe { Regs::new(ctx.regs_ptr()) };
            *frame_base = ctx.frame_base();
            next
        }
        _ => unimplemented!("opcode {op:?} is not part of the new-interpreter sketch"),
    };
}

#[inline(always)]
fn op_load<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(Load, ip, ops, next);
    let r = ops.signed::<0>();
    set_acc!(acc, regs.get(r, ctx.heap()));
    next!(next)
}

#[inline(always)]
fn op_store<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(Store, ip, ops, next);
    regs.set(ops.signed::<0>(), acc.get(ctx.heap()));
    next!(next)
}

#[inline(always)]
fn op_load_smi<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(LoadSmi, ip, ops, next);
    set_acc!(acc, Smi::new(ops.signed::<0>() as i64).into_tagged());
    next!(next)
}

#[inline(always)]
fn op_load_zero<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(LoadZero, ip, _ops, next);
    set_acc!(acc, Smi::new(0).into_tagged());
    next!(next)
}

#[inline(always)]
fn op_load_constant<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(LoadConstant, ip, ops, next);
    let heap = ctx.heap();
    let idx = ops.unsigned::<0>();
    set_acc!(acc, ctx.constants_ref(heap).at(heap, idx));
    next!(next)
}

#[inline(always)]
fn op_load_undefined<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(LoadUndefined, ip, _ops, next);
    let heap = ctx.heap();
    set_acc!(acc, heap.known().undefined.as_tagged(heap).erase());
    next!(next)
}

#[inline(always)]
fn op_load_null<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(LoadNull, ip, _ops, next);
    let heap = ctx.heap();
    set_acc!(acc, heap.known().null.as_tagged(heap).erase());
    next!(next)
}

#[inline(always)]
fn op_load_true<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(LoadTrue, ip, _ops, next);
    let heap = ctx.heap();
    set_acc!(acc, heap.known().true_object.as_tagged(heap).erase());
    next!(next)
}

#[inline(always)]
fn op_load_false<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(LoadFalse, ip, _ops, next);
    let heap = ctx.heap();
    set_acc!(acc, heap.known().false_object.as_tagged(heap).erase());
    next!(next)
}

#[inline(always)]
fn op_load_hole<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(LoadHole, ip, _ops, next);
    let heap = ctx.heap();
    set_acc!(acc, heap.known().the_hole.as_tagged(heap).erase());
    next!(next)
}

#[inline(always)]
fn op_load_new_target<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(LoadNewTarget, ip, _ops, next);
    let heap = ctx.heap();
    set_acc!(
        acc,
        ctx.stack()
            .frame_header(ctx.frame_base())
            .new_target_slot()
            .get(heap)
    );
    next!(next)
}

#[inline(always)]
fn op_load_context<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(LoadContext, ip, _ops, next);
    let heap = ctx.heap();
    set_acc!(
        acc,
        ctx.stack()
            .frame_header(ctx.frame_base())
            .context_slot()
            .get(heap)
    );
    next!(next)
}

#[inline(always)]
fn op_load_current_closure<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(LoadCurrentClosure, ip, _ops, next);
    let heap = ctx.heap();
    set_acc!(
        acc,
        ctx.stack()
            .frame_header(ctx.frame_base())
            .callable_slot()
            .get(heap)
    );
    next!(next)
}

#[inline(always)]
fn op_load_global<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(LoadGlobal, ip, ops, next);
    let name_idx = ops.unsigned::<0>();
    let fb = ops.unsigned::<1>();
    let global = {
        let heap = ctx.heap();
        heap.known().global_object.as_tagged(heap).erase()
    };
    if let Some(Hit::Value(v)) =
        InlineCache::try_load(ctx.heap(), ctx.feedback_ref(ctx.heap()), fb, global)
    {
        set_acc!(acc, v);
        next!(next);
    }
    let base = ctx.frame_base();
    let (pc, next_pc) = offsets!(ip, next, ctx);
    let vm = ctx.vm();
    let state = ctx.state();
    let v = global_load_body(vm, ctx.heap_mut(), state, roots, base, name_idx, fb, true);
    reenter!(ctx, acc, pc, next_pc, v)
}

#[inline(always)]
fn op_load_global_no_throw<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(LoadGlobalNoThrow, ip, ops, next);
    let name_idx = ops.unsigned::<0>();
    let fb = ops.unsigned::<1>();
    let global = {
        let heap = ctx.heap();
        heap.known().global_object.as_tagged(heap).erase()
    };
    if let Some(Hit::Value(v)) =
        InlineCache::try_load(ctx.heap(), ctx.feedback_ref(ctx.heap()), fb, global)
    {
        set_acc!(acc, v);
        next!(next);
    }
    let base = ctx.frame_base();
    let (pc, next_pc) = offsets!(ip, next, ctx);
    let vm = ctx.vm();
    let state = ctx.state();
    let v = global_load_body(vm, ctx.heap_mut(), state, roots, base, name_idx, fb, false);
    reenter!(ctx, acc, pc, next_pc, v)
}

/// Named-load cold body, handle-rooted like become's `slow_named_load`:
/// every operand is a `Handle` before the heap is borrowed mutably.
fn named_load_body(
    vm: &VM,
    heap: &mut Heap,
    state: &ThreadState,
    scope: &HandleScope<'_>,
    base: usize,
    recv: Handle<'_, Value>,
    name_idx: usize,
    fb: usize,
) -> Acc {
    let name = scope.handle(
        state
            .stack()
            .frame_header(base)
            .constants(&*heap)
            .at(&*heap, name_idx)
            .erase()
            .as_name(),
    );
    if Proxy::is_proxy(heap, recv.as_tagged(heap)) {
        return match Proxy::get(vm, heap, state, recv, recv, name.erase()) {
            Ok(Coercion::Threw) => Acc::set(heap.known().exception.as_tagged(heap).erase()),
            Ok(Coercion::Value(v)) => Acc::set(v),
            Err(e) => Acc::set(raise_runtime(vm, heap, state, e)),
        };
    }
    let out = match recv
        .as_tagged(heap)
        .load_outcome(heap, name.as_tagged(heap))
    {
        Ok(LoadOutcome::Value(v)) => {
            let v = scope.handle(v);
            InlineCache::update_load(
                heap,
                scope,
                state
                    .stack()
                    .frame_header(base)
                    .feedback(&*heap)
                    .map(|v| scope.handle(v)),
                fb,
                recv.as_tagged(heap)
                    .as_heap_object()
                    .map(|o| scope.handle(o)),
                scope.handle(name.as_tagged(heap).erase().as_name()),
                true,
            );
            v
        }
        Ok(LoadOutcome::Getter(getter)) => {
            let getter = scope.handle(getter);
            let args = scope.stage(&[recv.as_tagged(heap).erase()]);
            return match HostCtx::enter(vm, heap, state, getter, args, None) {
                Ok(v) => Acc::set(v),
                Err(e) => Acc::set(raise_runtime(vm, heap, state, e)),
            };
        }
        Err(e) => return Acc::set(raise_runtime(vm, heap, state, e)),
    };
    Acc::set(out.as_tagged(heap).erase())
}

/// Keyed-load cold body, shared by `LoadKeyedProperty`,
/// `LoadKeyedPropertyReg` and `LoadElementImm` (the last passes the
/// constant index as `element_index`).
fn keyed_load_body(
    vm: &VM,
    heap: &mut Heap,
    state: &ThreadState,
    scope: &HandleScope<'_>,
    base: usize,
    recv: Handle<'_, Value>,
    raw_key: Handle<'_, Value>,
    fb: Option<usize>,
    element_index: Option<usize>,
) -> Acc {
    let key = match Object::to_property_key(vm, heap, state, raw_key) {
        Ok(Some(k)) => scope.handle(k),
        Ok(None) => return Acc::set(heap.known().exception.as_tagged(heap).erase()),
        Err(e) => return Acc::set(raise_runtime(vm, heap, state, e)),
    };
    if Proxy::is_proxy(heap, recv.as_tagged(heap)) {
        return match Proxy::get(vm, heap, state, recv, recv, key.erase()) {
            Ok(Coercion::Threw) => Acc::set(heap.known().exception.as_tagged(heap).erase()),
            Ok(Coercion::Value(v)) => Acc::set(v),
            Err(e) => Acc::set(raise_runtime(vm, heap, state, e)),
        };
    }
    let classified = match key.as_tagged(heap).erase().classify_key(heap) {
        Ok(Key::Element(i)) => Some(i),
        _ => None,
    }
    .or(element_index);
    if let Some(i) = classified {
        if let Some(fb) = fb {
            InlineCache::update_load_element(
                heap,
                scope,
                state
                    .stack()
                    .frame_header(base)
                    .feedback(&*heap)
                    .map(|v| scope.handle(v)),
                fb,
                Some(recv),
                i,
            );
        }
        if let Some(unit) = DenseString::index_element(heap, scope, recv, key) {
            return Acc::set(scope.handle(unit).as_tagged(heap).erase());
        }
    }
    let out = match recv
        .as_tagged(heap)
        .load_outcome_keyed(heap, key.as_tagged(heap))
    {
        Ok(LoadOutcome::Value(v)) => scope.handle(v),
        Ok(LoadOutcome::Getter(getter)) => {
            let getter = scope.handle(getter);
            let args = scope.stage(&[recv.as_tagged(heap).erase()]);
            return match HostCtx::enter(vm, heap, state, getter, args, None) {
                Ok(v) => Acc::set(v),
                Err(e) => Acc::set(raise_runtime(vm, heap, state, e)),
            };
        }
        Err(e) => return Acc::set(raise_runtime(vm, heap, state, e)),
    };
    Acc::set(out.as_tagged(heap).erase())
}

/// Numeric cold body over rooted operands.
fn numeric_body(
    vm: &VM,
    heap: &mut Heap,
    state: &ThreadState,
    lhs: Handle<'_, Value>,
    rhs: Handle<'_, Value>,
    f: fn(f64, f64) -> f64,
) -> Acc {
    match Object::numeric_op(vm, heap, state, lhs, rhs, f) {
        Ok(Some(v)) => Acc::set(v),
        Ok(None) => Acc::set(heap.known().exception.as_tagged(heap).erase()),
        Err(e) => Acc::set(raise_runtime(vm, heap, state, e)),
    }
}

#[inline(always)]
fn op_store_named_property<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
    no_shadow: bool,
) -> *const u8 {
    if no_shadow {
        decode!(StoreNamedPropertyNoShadow, ip, ctx, ops, next, pc, next_pc);
        store_named_common(ctx, ip, regs, acc, roots, ops, next, pc, next_pc, true)
    } else {
        decode!(StoreNamedProperty, ip, ctx, ops, next, pc, next_pc);
        store_named_common(ctx, ip, regs, acc, roots, ops, next, pc, next_pc, false)
    }
}

#[allow(clippy::too_many_arguments)]
fn store_named_common<'h, const STRIDE: usize>(
    ctx: &mut Ctx<'h, 'h>,
    _ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    roots: RootsArg<'h>,
    ops: Ops<STRIDE>,
    next: *const u8,
    pc: usize,
    next_pc: usize,
    no_shadow: bool,
) -> *const u8 {
    let recv_reg = ops.signed::<0>();
    let name_idx = ops.unsigned::<1>();
    let fb = ops.unsigned::<2>();
    let semantics = if no_shadow {
        StoreSemantics::WriteThrough
    } else {
        StoreSemantics::Shadow
    };

    if !no_shadow {
        let heap = ctx.heap();
        let recv = regs.get(recv_reg, heap);
        let name = ctx.constants_ref(heap).at(heap, name_idx).as_name();
        if InlineCache::try_store_fast(heap, ctx.feedback_ref(heap), fb, recv, name, acc!(acc, ctx))
        {
            next!(next);
        }
    }

    let base = ctx.frame_base();
    let mode = ctx.language_mode();
    let vm = ctx.vm();
    let state = ctx.state();
    let v = state.handle_scope(|scope| {
        let recv = scope.handle(regs.get(recv_reg, ctx.heap()));
        let value = scope.handle(acc!(acc, ctx));
        let name = scope.handle(
            ctx.constants_ref(ctx.heap())
                .at(ctx.heap(), name_idx)
                .as_name(),
        );
        store_named_tail_body(
            vm,
            ctx.heap_mut(),
            state,
            roots,
            base,
            recv,
            name,
            value,
            Some(fb),
            semantics,
            mode,
        )
    });
    reenter!(ctx, acc, pc, next_pc, v)
}

#[inline(always)]
fn op_store_global<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(StoreGlobal, ip, ctx, ops, _next, pc, next_pc);
    let name_idx = ops.unsigned::<0>();
    let base = ctx.frame_base();
    let mode = ctx.language_mode();
    let vm = ctx.vm();
    let state = ctx.state();
    let v = state.handle_scope(|scope| {
        let value = scope.handle(acc!(acc, ctx));
        let heap = ctx.heap_mut();
        let name = scope.handle(
            state
                .stack()
                .frame_header(base)
                .constants(&*heap)
                .at(&*heap, name_idx)
                .erase()
                .as_name(),
        );
        let global = scope.handle(heap.known().global_object.as_tagged(heap).erase());
        if mode.is_strict()
            && matches!(global.as_tagged(heap).lookup(heap, name.as_tagged(heap)), Lookup::NotFound)
        {
            return raise_runtime(vm, heap, state, VmError::Reference);
        }
        store_named_tail_body(
            vm,
            heap,
            state,
            roots,
            base,
            global,
            name,
            value,
            None,
            StoreSemantics::WriteThrough,
            mode,
        )
    });
    reenter!(ctx, acc, pc, next_pc, v)
}

#[inline(always)]
fn op_add_parent<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(AddParent, ip, ctx, ops, _next, pc, next_pc);
    let recv_reg = ops.signed::<0>();
    let name_idx = ops.unsigned::<1>();
    let base = ctx.frame_base();
    let vm = ctx.vm();
    let state = ctx.state();
    let v = state.handle_scope(|scope| {
        let receiver = scope.handle(regs.get(recv_reg, ctx.heap()));
        let value = scope.handle(acc!(acc, ctx));
        let heap = ctx.heap_mut();
        let name = scope.handle(
            state
                .stack()
                .frame_header(base)
                .constants(&*heap)
                .at(&*heap, name_idx)
                .erase()
                .as_name(),
        );
        let Some(receiver) = scope.cast::<Object>(heap, receiver.as_tagged(heap)) else {
            return Acc::set(raise_runtime(vm, heap, state, VmError::Type));
        };
        if let Err(e) = Object::add_parent(heap, &scope, receiver, name, value) {
            return Acc::set(raise_runtime(vm, heap, state, e));
        }
        Acc::set(value.as_tagged(heap).erase())
    });
    reenter!(ctx, acc, pc, next_pc, v.get(ctx.heap()))
}

#[inline(always)]
fn op_delete<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(Delete, ip, ctx, ops, _next, pc, next_pc);
    let mode = ctx.language_mode();
    let args = ctx
        .stack()
        .window(ctx.frame_base(), ops.signed::<0>(), ops.unsigned::<1>());
    let vm = ctx.vm();
    let state = ctx.state();
    let target = args.get_handle(ctx.heap(), 0);
    let key = args.get_handle(ctx.heap(), 1);
    let v =
        vm_core::intrinsics::delete_property_operator(vm, ctx.heap_mut(), state, target, key, mode);
    reenter!(ctx, acc, pc, next_pc, v)
}

#[inline(always)]
fn op_load_named_property<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(LoadNamedProperty, ip, ops, next);
    let recv_reg = ops.signed::<0>();
    let name_idx = ops.unsigned::<1>();
    let fb = ops.unsigned::<2>();
    let heap = ctx.heap();
    let recv = regs.get(recv_reg, heap);
    match InlineCache::probe_mono(heap, ctx.feedback_ref(heap), fb, recv) {
        MonoProbe::Value(v) => {
            set_acc!(acc, v);
            next!(next);
        }
        MonoProbe::Handler(obj, handler) => {
            if let Some(Hit::Value(v)) = InlineCache::apply_mono(heap, obj, handler) {
                set_acc!(acc, v);
                next!(next);
            }
        }
        MonoProbe::Poly {
            obj,
            map,
            pairs,
            start,
        } => {
            if let Some(Hit::Value(v)) = InlineCache::try_load_resume(heap, obj, map, pairs, start)
            {
                set_acc!(acc, v);
                next!(next);
            }
        }
        MonoProbe::Miss | MonoProbe::NotReceiver => {}
    }
    let (pc, next_pc) = offsets!(ip, next, ctx);
    let base = ctx.frame_base();
    let vm = ctx.vm();
    let state = ctx.state();
    let v = state.handle_scope(|scope| {
        let recv = scope.handle(regs.get(recv_reg, ctx.heap()));
        named_load_body(vm, ctx.heap_mut(), state, &scope, base, recv, name_idx, fb)
    });
    reenter!(ctx, acc, pc, next_pc, v.get(ctx.heap()))
}

#[inline(always)]
fn op_load_keyed_property<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(LoadKeyedProperty, ip, ops, next);
    let recv_reg = ops.signed::<0>();
    let fb = ops.unsigned::<1>();
    let heap = ctx.heap();
    let recv = regs.get(recv_reg, heap);
    let key = acc!(acc, ctx);
    if let Some(idx) = key.to_i64()
        && idx >= 0
    {
        if let Some(obj) = recv.as_heap_object()
            && let Some(v) = obj.as_ref().element_value_dense(heap, idx as usize)
        {
            set_acc!(acc, v);
            next!(next);
        }
        if let Some(ElementHit::Value(v)) =
            InlineCache::try_load_element(heap, ctx.feedback_ref(heap), fb, recv, idx as usize)
        {
            set_acc!(acc, v);
            next!(next);
        }
    }
    let (pc, next_pc) = offsets!(ip, next, ctx);
    let base = ctx.frame_base();
    let vm = ctx.vm();
    let state = ctx.state();
    let v = state.handle_scope(|scope| {
        let recv = scope.handle(regs.get(recv_reg, ctx.heap()));
        let key = scope.handle(acc!(acc, ctx));
        keyed_load_body(vm, ctx.heap_mut(), state, &scope, base, recv, key, Some(fb), None)
    });
    reenter!(ctx, acc, pc, next_pc, v.get(ctx.heap()))
}

#[inline(always)]
fn op_load_keyed_property_reg<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(LoadKeyedPropertyReg, ip, ops, next);
    let recv_reg = ops.signed::<0>();
    let key_reg = ops.signed::<1>();
    let fb = ops.unsigned::<2>();
    let heap = ctx.heap();
    let recv = regs.get(recv_reg, heap);
    let key = regs.get(key_reg, heap);
    if let Some(idx) = key.to_i64()
        && idx >= 0
    {
        if let Some(obj) = recv.as_heap_object()
            && let Some(v) = obj.as_ref().element_value_dense(heap, idx as usize)
        {
            set_acc!(acc, v);
            next!(next);
        }
        if let Some(ElementHit::Value(v)) =
            InlineCache::try_load_element(heap, ctx.feedback_ref(heap), fb, recv, idx as usize)
        {
            set_acc!(acc, v);
            next!(next);
        }
    }
    let (pc, next_pc) = offsets!(ip, next, ctx);
    let base = ctx.frame_base();
    let vm = ctx.vm();
    let state = ctx.state();
    let v = state.handle_scope(|scope| {
        let recv = scope.handle(regs.get(recv_reg, ctx.heap()));
        let key = scope.handle(regs.get(key_reg, ctx.heap()));
        keyed_load_body(vm, ctx.heap_mut(), state, &scope, base, recv, key, Some(fb), None)
    });
    reenter!(ctx, acc, pc, next_pc, v.get(ctx.heap()))
}

#[inline(always)]
fn op_load_element_imm<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(LoadElementImm, ip, ops, next);
    let recv_reg = ops.signed::<0>();
    let idx = ops.unsigned::<1>();
    let fb = ops.unsigned::<2>();
    let heap = ctx.heap();
    let recv = regs.get(recv_reg, heap);
    if let Some(obj) = recv.as_heap_object()
        && let Some(v) = obj.as_ref().element_value_dense(heap, idx)
    {
        set_acc!(acc, v);
        next!(next);
    }
    if let Some(ElementHit::Value(v)) =
        InlineCache::try_load_element(heap, ctx.feedback_ref(heap), fb, recv, idx)
    {
        set_acc!(acc, v);
        next!(next);
    }
    let (pc, next_pc) = offsets!(ip, next, ctx);
    let base = ctx.frame_base();
    let vm = ctx.vm();
    let state = ctx.state();
    let v = state.handle_scope(|scope| {
        let recv = scope.handle(regs.get(recv_reg, ctx.heap()));
        let key = scope.handle(Smi::new(idx as i64).into_tagged());
        keyed_load_body(vm, ctx.heap_mut(), state, &scope, base, recv, key, Some(fb), Some(idx))
    });
    reenter!(ctx, acc, pc, next_pc, v.get(ctx.heap()))
}

#[inline(always)]
fn op_move<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(Move, ip, ops, next);
    let dst = ops.signed::<0>();
    let src = ops.signed::<1>();
    regs.set(dst, regs.get(src, ctx.heap()));
    next!(next)
}

#[inline(always)]
#[allow(clippy::too_many_arguments)]
fn store_keyed_body<'h, const STRIDE: usize>(
    ctx: &mut Ctx<'h, 'h>,
    _ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    roots: RootsArg<'h>,
    ops: Ops<STRIDE>,
    next: *const u8,
    pc: usize,
    next_pc: usize,
    semantics: StoreSemantics,
) -> *const u8 {
    let recv_reg = ops.signed::<0>();
    let key_reg = ops.signed::<1>();
    let fb = ops.unsigned::<2>();
    {
        let heap = ctx.heap();
        let recv = regs.get(recv_reg, heap);
        let key = regs.get(key_reg, heap);
        let value = acc!(acc, ctx);
        if let Some(idx) = key.to_i64()
            && idx >= 0
        {
            if recv
                .store_array_element_in_place(heap, idx as usize, value)
                .is_ok()
            {
                next!(next);
            }
            if let Some(v) = InlineCache::try_store_element(
                heap,
                ctx.feedback_ref(heap),
                fb,
                recv,
                idx as usize,
                value,
            ) {
                set_acc!(acc, v);
                next!(next);
            }
        }
    }
    let base = ctx.frame_base();
    let mode = ctx.language_mode();
    let vm = ctx.vm();
    let state = ctx.state();
    let v = state.handle_scope(|scope| {
        let recv = scope.handle(regs.get(recv_reg, ctx.heap()));
        let key = scope.handle(regs.get(key_reg, ctx.heap()));
        let value = scope.handle(acc!(acc, ctx));
        keyed_store_body(
            vm,
            ctx.heap_mut(),
            state,
            roots,
            base,
            fb,
            recv,
            key,
            value,
            semantics,
            mode,
        )
    });
    reenter!(ctx, acc, pc, next_pc, v)
}

#[inline(always)]
fn op_store_keyed_property<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
    no_shadow: bool,
) -> *const u8 {
    if no_shadow {
        decode!(StoreKeyedPropertyNoShadow, ip, ctx, ops, next, pc, next_pc);
        store_keyed_body(
            ctx,
            ip,
            regs,
            acc,
            roots,
            ops,
            next,
            pc,
            next_pc,
            StoreSemantics::WriteThrough,
        )
    } else {
        decode!(StoreKeyedProperty, ip, ctx, ops, next, pc, next_pc);
        store_keyed_body(ctx, ip, regs, acc, roots, ops, next, pc, next_pc, StoreSemantics::Shadow)
    }
}

#[inline(always)]
fn op_add<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(Add, ip, ops, next);

    let heap = ctx.heap();
    let lhs = regs.get(ops.signed::<0>(), heap);
    if let (Some(a), Some(b)) = (lhs.smi_bits(), acc!(acc, ctx).smi_bits())
        && let Some(sum) = a.checked_add(b)
    {
        set_acc_smi!(acc, sum);
        next!(next);
    }

    if let (Some(a), Some(b)) = (lhs.as_number(heap), acc!(acc, ctx).as_number(heap)) {
        let sum = a + b;
        if let Some(s) = Smi::from_f64(sum) {
            set_acc!(acc, s.into_tagged());
            next!(next);
        }
        if let Some(v) = ctx.heap_mut().try_new_float(sum) {
            set_acc!(acc, v);
            next!(next);
        }
        return slow_box_add::<STRIDE>(ip, regs, acc, ctx, roots, sum);
    }

    tail!(slow_add, ip, regs, acc, ctx, roots)
}

#[cold]
fn slow_box_add<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
    sum: f64,
) -> *const u8 {
    decode!(Add, ip, ctx, ops, _next, pc, next_pc);
    let v = ctx.heap_mut().new_number(sum);
    reenter!(ctx, acc, pc, next_pc, v)
}

#[cold]
fn slow_box_sub<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
    diff: f64,
) -> *const u8 {
    decode!(Sub, ip, ctx, ops, _next, pc, next_pc);
    let v = ctx.heap_mut().new_number(diff);
    reenter!(ctx, acc, pc, next_pc, v)
}

#[cold]
fn slow_add<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(Add, ip, ctx, ops, next, pc, next_pc);
    let _ = next;
    let vm = ctx.vm();
    let thread = ctx.state();
    let v = thread.handle_scope(|scope| {
        let lhs = scope.handle(regs.get(ops.signed::<0>(), ctx.heap()));
        let rhs = scope.handle(acc!(acc, ctx));
        add_body(vm, ctx.heap_mut(), thread, roots, lhs, rhs)
    });
    reenter!(ctx, acc, pc, next_pc, v)
}

#[inline(always)]
fn op_sub<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(Sub, ip, ops, next);
    let heap = ctx.heap();
    let lhs = regs.get(ops.signed::<0>(), heap);
    if let (Some(a), Some(b)) = (lhs.smi_bits(), acc!(acc, ctx).smi_bits())
        && let Some(diff) = a.checked_sub(b)
    {
        set_acc_smi!(acc, diff);
        next!(next);
    }
    if let (Some(a), Some(b)) = (lhs.as_number(heap), acc!(acc, ctx).as_number(heap)) {
        let diff = a - b;
        if let Some(s) = Smi::from_f64(diff) {
            set_acc!(acc, s.into_tagged());
            next!(next);
        }
        if let Some(v) = ctx.heap_mut().try_new_float(diff) {
            set_acc!(acc, v);
            next!(next);
        }
        return slow_box_sub::<STRIDE>(ip, regs, acc, ctx, roots, diff);
    }
    tail!(slow_sub, ip, regs, acc, ctx, roots)
}

#[cold]
fn slow_sub<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(Sub, ip, ctx, ops, next, pc, next_pc);
    let _ = next;
    let vm = ctx.vm();
    let state = ctx.state();
    let v = state.handle_scope(|scope| {
        let lhs = scope.handle(regs.get(ops.signed::<0>(), ctx.heap()));
        let rhs = scope.handle(acc!(acc, ctx));
        numeric_body(vm, ctx.heap_mut(), state, lhs, rhs, |a, b| a - b)
    });
    reenter!(ctx, acc, pc, next_pc, v.get(ctx.heap()))
}

#[inline(always)]
fn op_add_immediate<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(AddImmediate, ip, ops, next);
    let lhs = regs.get(ops.signed::<0>(), ctx.heap());
    let imm = ops.signed::<1>();
    if let Some(bits) = lhs.smi_bits()
        && let Some(sum) = bits.checked_add((imm as i64) << 1)
    {
        set_acc_smi!(acc, sum);
        next!(next);
    }
    tail!(slow_add_immediate, ip, regs, acc, ctx, roots)
}

#[cold]
fn slow_add_immediate<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(AddImmediate, ip, ctx, ops, next, pc, next_pc);
    let _ = next;
    let imm = ops.signed::<1>();
    let vm = ctx.vm();
    let state = ctx.state();
    let v = state.handle_scope(|scope| {
        let lhs = scope.handle(regs.get(ops.signed::<0>(), ctx.heap()));
        let rhs = scope.handle(Smi::new(imm as i64).into_tagged());
        add_body(vm, ctx.heap_mut(), state, roots, lhs, rhs)
    });
    reenter!(ctx, acc, pc, next_pc, v)
}

#[inline(always)]
fn op_sub_immediate<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(SubImmediate, ip, ops, next);
    let lhs = regs.get(ops.signed::<0>(), ctx.heap());
    let imm = ops.signed::<1>();
    if let Some(bits) = lhs.smi_bits()
        && let Some(diff) = bits.checked_sub((imm as i64) << 1)
    {
        set_acc_smi!(acc, diff);
        next!(next);
    }
    tail!(slow_sub_immediate, ip, regs, acc, ctx, roots)
}

#[cold]
fn slow_sub_immediate<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(SubImmediate, ip, ctx, ops, next, pc, next_pc);
    let _ = next;
    let imm = ops.signed::<1>();
    let vm = ctx.vm();
    let state = ctx.state();
    let v = state.handle_scope(|scope| {
        let lhs = scope.handle(regs.get(ops.signed::<0>(), ctx.heap()));
        let rhs = scope.handle(Smi::new(imm as i64).into_tagged());
        numeric_body(vm, ctx.heap_mut(), state, lhs, rhs, |a, b| a - b)
    });
    reenter!(ctx, acc, pc, next_pc, v.get(ctx.heap()))
}

#[inline(always)]
fn op_shift_right_immediate<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(ShiftRightImmediate, ip, ops, next);
    let lhs = regs.get(ops.signed::<0>(), ctx.heap());
    let imm = ops.signed::<1>();
    if let Some(a) = lhs.to_i64() {
        set_acc!(acc, Smi::new((a as i32).wrapping_shr(imm as u32 & 31) as i64).into_tagged());
        next!(next);
    }
    tail!(slow_shift_right_immediate, ip, regs, acc, ctx, roots)
}

#[cold]
fn slow_shift_right_immediate<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(ShiftRightImmediate, ip, ctx, ops, next, pc, next_pc);
    let _ = next;
    let imm = ops.signed::<1>();
    let vm = ctx.vm();
    let state = ctx.state();
    let v = state.handle_scope(|scope| {
        let lhs = scope.handle(regs.get(ops.signed::<0>(), ctx.heap()));
        let rhs = scope.handle(Smi::new(imm as i64).into_tagged());
        bitwise_body(vm, ctx.heap_mut(), state, roots, 4, lhs, rhs)
    });
    reenter!(ctx, acc, pc, next_pc, v)
}

#[inline(always)]
fn op_inc_loc<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(IncLoc, ip, ops, next);
    let r = ops.signed::<0>();
    let heap = ctx.heap();
    let v = regs.get(r, heap);
    if let Some(bits) = v.smi_bits() {
        if let Some(new) = bits.checked_add(2) {
            regs.set(r, Tagged::from_smi_bits(new));
            set_acc_smi!(acc, bits);
            next!(next);
        }
    } else if let Some(n) = v.as_number(heap) {
        let new = n + 1.0;
        if let Some(s) = Smi::from_f64(new) {
            regs.set(r, s.into_tagged());
            set_acc!(acc, v);
            next!(next);
        }
        set_acc!(acc, v);
        if let Some(t) = ctx.heap_mut().try_new_float(new) {
            regs.set(r, t);
            next!(next);
        }
    }
    tail!(slow_inc_loc, ip, regs, acc, ctx, roots)
}

#[cold]
fn slow_inc_loc<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(IncLoc, ip, ctx, ops, next, pc, next_pc);
    let _ = next;
    let r = ops.signed::<0>();
    let vm = ctx.vm();
    let state = ctx.state();
    let v = state.handle_scope(|scope| {
        let old = scope.handle(regs.get(r, ctx.heap()));
        incdec_body(vm, ctx.heap_mut(), state, roots, regs, r, old, 1.0)
    });
    reenter!(ctx, acc, pc, next_pc, v)
}

#[inline(always)]
fn op_dec_loc<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(DecLoc, ip, ops, next);
    let r = ops.signed::<0>();
    let heap = ctx.heap();
    let v = regs.get(r, heap);
    if let Some(bits) = v.smi_bits() {
        if let Some(new) = bits.checked_sub(2) {
            regs.set(r, Tagged::from_smi_bits(new));
            set_acc_smi!(acc, bits);
            next!(next);
        }
    } else if let Some(n) = v.as_number(heap) {
        let new = n - 1.0;
        if let Some(s) = Smi::from_f64(new) {
            regs.set(r, s.into_tagged());
            set_acc!(acc, v);
            next!(next);
        }
        set_acc!(acc, v);
        if let Some(t) = ctx.heap_mut().try_new_float(new) {
            regs.set(r, t);
            next!(next);
        }
    }
    tail!(slow_dec_loc, ip, regs, acc, ctx, roots)
}

#[cold]
fn slow_dec_loc<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(DecLoc, ip, ctx, ops, next, pc, next_pc);
    let _ = next;
    let r = ops.signed::<0>();
    let vm = ctx.vm();
    let state = ctx.state();
    let v = state.handle_scope(|scope| {
        let old = scope.handle(regs.get(r, ctx.heap()));
        incdec_body(vm, ctx.heap_mut(), state, roots, regs, r, old, -1.0)
    });
    reenter!(ctx, acc, pc, next_pc, v)
}

#[inline(always)]
fn op_equal<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(Equal, ip, ops, next);
    let r = ops.signed::<0>();
    let fast = {
        let heap = ctx.heap();
        let other = regs.get(r, heap);
        match (acc!(acc, ctx).as_number(heap), other.as_number(heap)) {
            (Some(a), Some(b)) => Some(Convert::boolean(heap, a == b)),
            _ => None,
        }
    };
    if let Some(v) = fast {
        set_acc!(acc, v);
        next!(next);
    }
    let (pc, next_pc) = offsets!(ip, next, ctx);
    let vm = ctx.vm();
    let state = ctx.state();
    let v = state.handle_scope(|scope| {
        let lhs = scope.handle(acc!(acc, ctx));
        let rhs = scope.handle(regs.get(r, ctx.heap()));
        compare_body(vm, ctx.heap_mut(), state, roots, 0, lhs, rhs)
    });
    reenter!(ctx, acc, pc, next_pc, v)
}

#[inline(always)]
fn op_compare_jump<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(CompareJump, ip, ops, next);
    let r = ops.signed::<0>();
    let kind = ops.unsigned::<1>();
    let off = ops.signed::<2>();
    let cmp = (kind / 2) as u8;
    let falsy_jump = kind % 2 == 1;

    let fast = {
        let heap = ctx.heap();
        let other = regs.get(r, heap);
        match (acc!(acc, ctx).as_number(heap), other.as_number(heap)) {
            (Some(a), Some(b)) => Some(match cmp {
                0 | 1 => a == b,
                2 => a < b,
                3 => a <= b,
                4 => a > b,
                _ => a >= b,
            }),
            _ => None,
        }
    };
    if let Some(b) = fast {
        set_acc!(acc, Convert::boolean(ctx.heap(), b));
        if b != falsy_jump {
            dispatch!(unsafe { ip.offset(off as isize) });
        }
        next!(next);
    }

    let (pc, next_pc) = offsets!(ip, next, ctx);
    let vm = ctx.vm();
    let state = ctx.state();
    let v = state.handle_scope(|scope| {
        let lhs = scope.handle(acc!(acc, ctx));
        let rhs = scope.handle(regs.get(r, ctx.heap()));
        compare_body(vm, ctx.heap_mut(), state, roots, cmp, lhs, rhs)
    });
    let result = v;
    let raw = result.raw().to_bits();
    set_acc!(acc, result);
    let sentinel = {
        let heap = ctx.heap();
        heap.known().exception.as_tagged(heap).raw().to_bits()
    };
    ctx.reload_code();
    if raw == sentinel {
        ctx.set_throw_pc(pc);
        return throw_ptr();
    }
    let taken = acc!(acc, ctx).is_truthy(ctx.heap());
    let target_pc = (pc as isize + off as isize) as usize;
    if taken != falsy_jump {
        offset(ctx.code_ptr(), target_pc)
    } else {
        offset(ctx.code_ptr(), next_pc)
    }
}

#[inline(always)]
fn op_jump<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(Jump, ip, ops, _next);
    dispatch!(unsafe { ip.offset(ops.signed::<0>() as isize) })
}

#[inline(always)]
fn op_jump_if_truthy<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(JumpIfTruthy, ip, ops, next);
    if acc!(acc, ctx).is_truthy(ctx.heap()) {
        dispatch!(unsafe { ip.offset(ops.signed::<0>() as isize) });
    }
    next!(next)
}

#[inline(always)]
fn op_jump_if_falsy<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(JumpIfFalsy, ip, ops, next);
    if !acc!(acc, ctx).is_truthy(ctx.heap()) {
        dispatch!(unsafe { ip.offset(ops.signed::<0>() as isize) });
    }
    next!(next)
}

#[inline(always)]
fn op_jump_if_not_undefined<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(JumpIfNotUndefined, ip, ops, next);
    let undefined = {
        let heap = ctx.heap();
        heap.known().undefined.as_tagged(heap).erase()
    };
    if acc!(acc, ctx) != undefined {
        dispatch!(unsafe { ip.offset(ops.signed::<0>() as isize) });
    }
    next!(next)
}

#[inline(always)]
fn op_jump_loop<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(JumpLoop, ip, ctx, ops, _next, pc, _next_pc);
    let off = ops.signed::<0>();
    let target_pc = (pc as isize + off as isize) as usize;
    if ctx.safepoint_tick() {
        let state = ctx.state();
        // The accumulator is a raw local: park it in the rooted slot
        // before the poll, which may collect and move its payload.
        state.acc_slot().store(acc!(acc, ctx));
        let shutdown = ctx.heap_mut().safepoint_poll();
        ctx.reload_code();
        set_acc!(acc, state.acc_slot().get(ctx.heap()));
        if shutdown {
            state.set_termination(Termination::Shutdown);
            let undefined = {
                let heap = ctx.heap();
                heap.known().undefined.as_tagged(heap).erase()
            };
            state.set_pending_exception(undefined);
            ctx.set_throw_pc(pc);
            return throw_ptr();
        }
        return offset(ctx.code_ptr(), target_pc);
    }
    dispatch!(unsafe { ip.offset(off as isize) })
}

#[inline(always)]
fn op_throw<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(Throw, ip, _ops, _next);
    let pc = ip as usize - ctx.code_ptr() as usize;
    ctx.state().set_pending_exception(acc!(acc, ctx));
    ctx.set_throw_pc(pc);
    throw_ptr()
}

#[inline(always)]
fn op_create_closure<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(CreateClosure, ip, ctx, ops, _next, pc, next_pc);
    let info_idx = ops.unsigned::<0>();
    let vm = ctx.vm();
    let state = ctx.state();
    let base = ctx.frame_base();
    let v = state.handle_scope(|scope| {
        let heap = ctx.heap_mut();
        let Some(info) = scope.cast::<CallableInfoObject>(
            heap,
            state
                .stack()
                .frame_header(base)
                .constants(&*heap)
                .at(&*heap, info_idx),
        ) else {
            return Acc::set(raise_runtime(vm, heap, state, VmError::Type));
        };
        let context = scope
            .cast::<ContextObject>(heap, state.stack().frame_header(base).context_slot().get(heap))
            .expect("frame context slot holds a ContextObject");
        match Object::create_closure(heap, &scope, info, context) {
            Ok(obj) => Acc::set(obj.erase()),
            Err(e) => Acc::set(raise_runtime(vm, heap, state, e)),
        }
    });
    reenter!(ctx, acc, pc, next_pc, v.get(ctx.heap()))
}

/// Enter the exclusive phase of a resolved call, mirroring become's
/// `call_enter!`: a pushed frame needs only the local frame/register
/// refresh; native and proxy callees run now.
macro_rules! call_enter {
    (
        $ctx:expr,
        $regs:expr,
        $acc:expr,
        $pc:expr,
        $next_pc:expr,
        $roots:expr,
        $staged:expr
    ) => {{
        match $staged {
            Err(e) => raise!($ctx, $acc, $pc, e),
            Ok(StagedCall::Value(v)) => reenter!($ctx, $acc, $pc, $next_pc, v),
            Ok(StagedCall::Frame) => {
                // The step arm refreshes the loop's Regs/frame-base after
                // a call opcode; all this arm owns is the callee entry.
                let undefined = {
                    let heap = $ctx.heap();
                    heap.known().undefined.as_tagged(heap).erase()
                };
                *$acc = Acc::set(undefined);
                $ctx.code_ptr()
            }
            Ok(StagedCall::Native { rt, staged }) => {
                let v = $ctx.call_runtime(rt, staged);
                reenter!($ctx, $acc, $pc, $next_pc, v)
            }
            Ok(StagedCall::Proxy { callee_reg, staged }) => {
                let v = proxy_apply_staged($ctx, $roots, $regs, callee_reg, staged);
                reenter!($ctx, $acc, $pc, $next_pc, v)
            }
        }
    }};
}

#[inline(always)]
fn op_call<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(Call, ip, ctx, ops, _next, pc, next_pc);
    let callee = regs.get(ops.signed::<0>(), ctx.heap());
    let staged = call_window_start::<STRIDE>(
        ctx,
        roots,
        pc,
        ops.unsigned::<3>(),
        ops.signed::<0>(),
        callee,
        ops.signed::<1>(),
        ops.unsigned::<2>(),
    );
    call_enter!(ctx, regs, acc, pc, next_pc, roots, staged)
}

#[inline(always)]
fn op_call_no_feedback<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(CallNoFeedback, ip, ctx, ops, _next, pc, next_pc);
    let callee = regs.get(ops.signed::<0>(), ctx.heap());
    let staged = ctx
        .stack()
        .window(ctx.frame_base(), ops.signed::<1>(), ops.unsigned::<2>());
    let size = base::<STRIDE>() + STRIDE * const { Opcode::CallNoFeedback.operands().len() };
    let result = resolve_target(
        ctx,
        roots,
        pc,
        size,
        ops.signed::<0>(),
        callee.call_target(ctx.heap()),
        staged,
    );
    call_enter!(ctx, regs, acc, pc, next_pc, roots, result)
}

#[inline(always)]
fn op_call_runtime<'h, const STRIDE: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    decode!(CallRuntime, ip, ctx, ops, _next, pc, next_pc);
    let rt = NativeIndex(ops.unsigned::<0>());
    let args = ctx
        .stack()
        .window(ctx.frame_base(), ops.signed::<1>(), ops.unsigned::<2>());
    let v = ctx.call_runtime(rt, args);
    reenter!(ctx, acc, pc, next_pc, v)
}

#[inline(always)]
fn op_call_function<'h, const STRIDE: usize, const ARGC: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    match ARGC {
        0 => {
            decode!(CallFunction0, ip, ctx, ops, _next, pc, next_pc);
            let callee = regs.get(ops.signed::<0>(), ctx.heap());
            let staged = call_scatter_start::<STRIDE, false>(
                ctx,
                roots,
                pc,
                ops.unsigned::<1>(),
                ops.signed::<0>(),
                callee,
                roots
                    .known(ctx.heap())
                    .undefined
                    .as_tagged(ctx.heap())
                    .erase(),
                &[],
            );
            call_enter!(ctx, regs, acc, pc, next_pc, roots, staged)
        }
        1 => {
            decode!(CallFunction1, ip, ctx, ops, _next, pc, next_pc);
            let callee = regs.get(ops.signed::<0>(), ctx.heap());
            let arg0 = regs.get(ops.signed::<1>(), ctx.heap());
            let staged = call_scatter_start::<STRIDE, false>(
                ctx,
                roots,
                pc,
                ops.unsigned::<2>(),
                ops.signed::<0>(),
                callee,
                roots
                    .known(ctx.heap())
                    .undefined
                    .as_tagged(ctx.heap())
                    .erase(),
                &[arg0][..1],
            );
            call_enter!(ctx, regs, acc, pc, next_pc, roots, staged)
        }
        _ => {
            decode!(CallFunction2, ip, ctx, ops, _next, pc, next_pc);
            let callee = regs.get(ops.signed::<0>(), ctx.heap());
            let arg0 = regs.get(ops.signed::<1>(), ctx.heap());
            let arg1 = regs.get(ops.signed::<2>(), ctx.heap());
            let staged = call_scatter_start::<STRIDE, false>(
                ctx,
                roots,
                pc,
                ops.unsigned::<3>(),
                ops.signed::<0>(),
                callee,
                roots
                    .known(ctx.heap())
                    .undefined
                    .as_tagged(ctx.heap())
                    .erase(),
                &[arg0, arg1][..2],
            );
            call_enter!(ctx, regs, acc, pc, next_pc, roots, staged)
        }
    }
}

#[inline(always)]
fn op_call_method<'h, const STRIDE: usize, const ARGC: usize>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    match ARGC {
        0 => {
            decode!(CallMethod0, ip, ctx, ops, _next, pc, next_pc);
            let callee = regs.get(ops.signed::<0>(), ctx.heap());
            let recv = regs.get(ops.signed::<1>(), ctx.heap());
            let staged = call_scatter_start::<STRIDE, true>(
                ctx,
                roots,
                pc,
                ops.unsigned::<2>(),
                ops.signed::<0>(),
                callee,
                recv,
                &[],
            );
            call_enter!(ctx, regs, acc, pc, next_pc, roots, staged)
        }
        1 => {
            decode!(CallMethod1, ip, ctx, ops, _next, pc, next_pc);
            let callee = regs.get(ops.signed::<0>(), ctx.heap());
            let recv = regs.get(ops.signed::<1>(), ctx.heap());
            let arg0 = regs.get(ops.signed::<2>(), ctx.heap());
            let staged = call_scatter_start::<STRIDE, true>(
                ctx,
                roots,
                pc,
                ops.unsigned::<3>(),
                ops.signed::<0>(),
                callee,
                recv,
                &[arg0][..1],
            );
            call_enter!(ctx, regs, acc, pc, next_pc, roots, staged)
        }
        _ => {
            decode!(CallMethod2, ip, ctx, ops, _next, pc, next_pc);
            let callee = regs.get(ops.signed::<0>(), ctx.heap());
            let recv = regs.get(ops.signed::<1>(), ctx.heap());
            let arg0 = regs.get(ops.signed::<2>(), ctx.heap());
            let arg1 = regs.get(ops.signed::<3>(), ctx.heap());
            let staged = call_scatter_start::<STRIDE, true>(
                ctx,
                roots,
                pc,
                ops.unsigned::<4>(),
                ops.signed::<0>(),
                callee,
                recv,
                &[arg0, arg1][..2],
            );
            call_enter!(ctx, regs, acc, pc, next_pc, roots, staged)
        }
    }
}

#[inline(always)]
fn op_return<'h>(
    ip: *const u8,
    regs: Regs,
    acc: &mut Acc,
    ctx: &mut Ctx<'h, 'h>,
    roots: RootsArg<'h>,
) -> *const u8 {
    if ctx.frame_base() == ctx.base_anchor() {
        return core::ptr::null();
    }
    let caller = ctx.stack().pop_frame(ctx.frame_base());
    ctx.switch_frame(caller.base);
    offset(ctx.code_ptr(), caller.pc)
}
