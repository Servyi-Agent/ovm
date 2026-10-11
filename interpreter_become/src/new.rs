//! Epoch-ABI port playground: heap-owning `Ctx<'s, 'h>`, `Acc` word
//!
//! Parallel universe next to the live interpreter: a heap-owning `Ctx`,
//! raw-`Value` accumulator threading, and the first ported handlers.
//! NOT wired into dispatch — this file exists to compare the generated
//! assembly of `new::op_*` against the originals.
//!
//! rustfmt: plain `cargo fmt` owns this file (and the crate); the
//! crate-level `fn_call_width = 90` keeps the closure-style heads
//! (`handler!(name, Op, |bindings| { .. })`) on one line while the
//! bodies are formatted normally.
//!
//! not-yet-wired items are expected dead.
//!
//! Ported: Load, Store, Add (+ float path + slow paths), CallRuntime,
//! the `resume` edge, and throw routing. `throw_dispatch` folds the
//! frame walk in (unlike the original, whose `Unwind` result carried a
//! `Tagged` across the walk — here the taken exception is parked as an
//! `Acc` word, so the dispatch continuation re-takes `ctx` exclusively
//! with no borrow gymnastics). `size` in CallRuntime was dead in the
//! original and is dropped.

#![allow(dead_code)]

use bytecode::{OPERAND_SIZES_NARROW, OPERAND_SIZES_WIDE, Opcode};
use vm_core::{
    Coercion, Convert, DenseString, Handle, Heap, Hint, HostCtx, NativeIndex, Object, Register,
    Smi, Tagged, ThreadState, VM, Value, VmError, Word, raise_runtime,
};

use crate::{FloatReg, Ops, Regs, RootsArg, star_lookahead};

pub struct Ctx<'s, 'h> {
    vm: &'s VM,
    state: &'s ThreadState,
    heap: &'h mut Heap,
    /// Anchor of the frame `execute` entered: a return at this anchor ends
    /// the execution instead of unwinding into a caller.
    base_anchor: usize,
}

impl<'s, 'h> Ctx<'s, 'h> {
    #[inline(always)]
    pub fn new(vm: &'s VM, state: &'s ThreadState, heap: &'h mut Heap, base_anchor: usize) -> Self {
        Ctx {
            vm,
            state,
            heap,
            base_anchor,
        }
    }

    #[inline(always)]
    pub fn heap(&self) -> &Heap {
        self.heap
    }

    #[inline(always)]
    pub fn heap_mut(&mut self) -> &mut Heap {
        self.heap
    }

    #[inline(always)]
    pub fn vm(&self) -> &'s VM {
        self.vm
    }

    #[inline(always)]
    pub fn state(&self) -> &'s ThreadState {
        self.state
    }

    #[inline(always)]
    pub fn stack(&self) -> &'s vm_core::Stack {
        self.state.stack()
    }

    #[inline(always)]
    pub fn frame_base(&self) -> usize {
        self.state.frame_base()
    }

    #[inline(always)]
    pub fn base_anchor(&self) -> usize {
        self.base_anchor
    }

    /// Switch the current frame (after a push, pop, or unwind).
    #[inline(always)]
    pub fn set_frame_base(&self, base: usize) {
        self.state.set_frame_base(base);
    }

    #[inline(always)]
    pub fn code_ptr(&self) -> *const u8 {
        self.stack()
            .frame_header(self.frame_base())
            .code(self.heap())
            .as_ptr()
    }

    #[inline(always)]
    pub fn regs_ptr(&self) -> *mut Register {
        unsafe { self.stack().slots_ptr().add(self.frame_base()) }
    }

    #[inline(always)]
    pub fn exception_word(&self) -> Tagged<'_, Value> {
        self.heap().known().exception.as_tagged(self.heap()).erase()
    }

    #[inline(always)]
    pub fn is_throw(&self, acc: Acc) -> bool {
        acc.get(self.heap()).raw().to_bits() == self.exception_word().raw().to_bits()
    }

    #[inline(always)]
    pub fn undefined_word(&self) -> Tagged<'_, Value> {
        self.heap().known().undefined.as_tagged(self.heap()).erase()
    }

    #[inline(always)]
    pub fn raise_tag(&mut self, err: VmError) -> Acc {
        let (vm, state) = (self.vm, self.state);
        Acc::set(raise_runtime(vm, self.heap_mut(), state, err))
    }
}

#[derive(Clone, Copy)]
pub struct Acc(Value);

impl Acc {
    /// Set the accumulator from a live view. Safe: a view is fresh by
    /// construction (its shared heap borrow pins the no-GC window it
    /// was minted in).
    #[inline(always)]
    pub fn set(v: Tagged<'_, Value>) -> Self {
        Acc(v.raw())
    }

    #[inline(always)]
    pub fn from_smi_bits(bits: i64) -> Self {
        Acc(Value::from_bits(bits as Word))
    }

    /// Get the accumulator as a view under the current epoch.
    /// Acc becomes invalid after the first allocation!
    #[inline(always)]
    pub fn get<'h>(self, _heap: &'h Heap) -> Tagged<'h, Value> {
        // Safety: the dispatch-chain freshness invariant.
        unsafe { Tagged::from_value_unchecked(self.0) }
    }

    /// Smi payload bits; `None` for pointers. Pure word decode.
    #[inline(always)]
    pub fn smi_bits(self) -> Option<i64> {
        if self.0.is_smi() {
            Some(self.0.to_bits() as i64)
        } else {
            None
        }
    }
}

pub struct TableArg<'h>(pub &'static [Handler; 256], core::marker::PhantomData<&'h ()>);

impl<'h> TableArg<'h> {
    #[inline(always)]
    pub fn get(&self, op: u8) -> Handler {
        self.0[op as usize]
    }
}

pub type Handler = for<'h> extern "rust-preserve-none" fn(
    *const u8,
    Regs,
    Acc,
    &mut Ctx<'_, 'h>,
    TableArg<'h>,
    RootsArg<'h>,
    FloatReg,
) -> Acc;

macro_rules! dispatch {
    ($p:expr, $a:expr, $r:expr, $x:expr, $t:ident, $k:ident, $f:ident) => {{
        let h = $t.get(unsafe { *$p });
        become h($p, $r, $a, $x, $t, $k, $f)
    }};
}

macro_rules! next {
    ($op:ident, $ip:expr, $r:expr, $x:expr, $t:ident, $k:ident, $f:ident, $a:expr) => {{
        let p = $ip.wrapping_add(
            (if STRIDE == 2 { 2 } else { 1 }) + STRIDE * const { Opcode::$op.operands().len() },
        );
        #[cfg(feature = "star_fusion")]
        {
            if star_lookahead(Opcode::$op) && unsafe { *p } == Opcode::Store as u8 {
                let dst = unsafe { *p.add(1) } as i8 as i32;
                $r.set(dst, $a.get($x.heap()));
                dispatch!(unsafe { p.add(2) }, $a, $r, $x, $t, $k, $f)
            } else {
                dispatch!(p, $a, $r, $x, $t, $k, $f)
            }
        }
        #[cfg(not(feature = "star_fusion"))]
        {
            dispatch!(p, $a, $r, $x, $t, $k, $f)
        }
    }};
}

macro_rules! handler {
    ($name:ident, $op:ident, |$ip:ident, $ops:ident, $regs:ident, $acc:ident, $ctx:ident, $table:ident, $roots:ident, $float:ident| $body:block) => {
        #[rustc_align(32)]
        extern "rust-preserve-none" fn $name<'h, const STRIDE: usize>(
            $ip: *const u8,
            $regs: Regs,
            $acc: Acc,
            $ctx: &mut Ctx<'_, 'h>,
            $table: TableArg<'h>,
            $roots: RootsArg<'h>,
            $float: FloatReg,
        ) -> Acc {
            let $ops = Ops::<STRIDE>::new($ip, Opcode::$op);
            $body
        }
    };
}

/// The cold-path twin (its own name: the crate-wide
/// `skip_macro_invocations = ["slow_handler"]` shields slow.rs's
/// old-grammar invocations and would freeze these bodies too).
macro_rules! cold_handler {
    ($name:ident, |$ip:ident, $ops:ident, $regs:ident, $acc:ident, $ctx:ident, $float:ident| $body:block) => {
        #[cold]
        #[inline(never)]
        #[rustc_align(32)]
        extern "rust-preserve-none" fn $name<'h, const STRIDE: usize>(
            $ip: *const u8,
            $regs: Regs,
            $acc: Acc,
            $ctx: &mut Ctx<'_, 'h>,
            table: TableArg<'h>,
            roots: RootsArg<'h>,
            $float: FloatReg,
        ) -> Acc {
            // snapshot while `ip` still pairs with the current base
            let pc = $ip as usize - $ctx.code_ptr() as usize;
            // copy the shared state ref out (a field copy borrows
            // nothing): the acc slot stays reachable while the body
            // holds ctx exclusively
            let state: &ThreadState = $ctx.state;
            let acc_slot = state.acc_slot();
            let $ops = Ops::<STRIDE>::from_ip($ip);
            let v: Acc = $body;
            // an Acc is fresh at production, but the word cannot cross
            // the continuation's heap-exclusive use: park it in the
            // frame's acc slot (collector-updated) and re-read — safe
            // by construction
            acc_slot.store(v.get($ctx.heap()));
            let acc = Acc::set(acc_slot.get($ctx.heap()));
            become resume(
                unsafe { $ctx.code_ptr().add(pc) },
                $regs,
                acc,
                $ctx,
                table,
                roots,
                $float,
            )
        }
    };
}

#[inline(always)]
fn exception_word(heap: &Heap) -> Tagged<'_, Value> {
    heap.known().exception.as_tagged(heap).erase()
}

#[inline(always)]
fn slow_next_pc(ip: *const u8) -> *const u8 {
    let wide = unsafe { *ip } == Opcode::Wide as u8;
    let op = unsafe { *ip.add(wide as usize) } as usize;
    let size = if wide {
        *unsafe { OPERAND_SIZES_WIDE.get_unchecked(op) }
    } else {
        *unsafe { OPERAND_SIZES_NARROW.get_unchecked(op) }
    } as usize;
    unsafe { ip.add(wide as usize + 1 + size) }
}

extern "rust-preserve-none" fn op_trap<'h>(
    _ip: *const u8,
    _regs: Regs,
    _acc: Acc,
    _ctx: &mut Ctx<'_, 'h>,
    _table: TableArg<'h>,
    _roots: RootsArg<'h>,
    _float: FloatReg,
) -> Acc {
    unreachable!("trap opcode")
}

/// The after-slow-path re-entry edge.
#[inline(never)]
#[rustc_align(32)]
extern "rust-preserve-none" fn resume<'h>(
    fault_ip: *const u8,
    _regs: Regs,
    acc: Acc,
    ctx: &mut Ctx<'_, 'h>,
    table: TableArg<'h>,
    roots: RootsArg<'h>,
    float: FloatReg,
) -> Acc {
    if ctx.is_throw(acc) {
        become throw_dispatch(fault_ip, _regs, acc, ctx, table, roots, float)
    }
    // fault_ip is freshly re-derived by every resume caller, so it
    // still pairs with the current base
    let ip = slow_next_pc(fault_ip);
    let regs = unsafe { Regs::new(ctx.regs_ptr()) };
    let h = table.get(unsafe { *ip });
    become h(ip, regs, acc, ctx, table, roots, float)
}

#[cold]
#[inline(never)]
#[rustc_align(32)]
extern "rust-preserve-none" fn throw_dispatch<'h>(
    fault_ip: *const u8,
    _regs: Regs,
    _acc: Acc,
    ctx: &mut Ctx<'_, 'h>,
    table: TableArg<'h>,
    roots: RootsArg<'h>,
    float: FloatReg,
) -> Acc {
    let mut pc = fault_ip as usize - ctx.code_ptr() as usize;
    loop {
        let base = ctx.frame_base();
        let handled = if ctx.state().termination().is_some() {
            // A termination is not an exception: no handler (catch or
            // finally in any frame) may observe or intercept it.
            None
        } else {
            let callable = ctx
                .stack()
                .frame_header(base)
                .callable_slot()
                .get(ctx.heap());
            callable
                .as_heap_object()
                .and_then(|obj| obj.callable_info(ctx.heap()))
                .and_then(|info| info.handlers.get(ctx.heap()))
                .and_then(|handlers| handlers.lookup(pc))
        };
        if let Some(handler_pc) = handled {
            // park the word before the continuation re-takes ctx
            // exclusively: an Acc carries no heap borrow
            let ex = Acc::set(
                ctx.state()
                    .take_pending_exception_tagged(ctx.heap())
                    .expect("pending exception must be set while unwinding"),
            );
            let code = ctx.code_ptr();
            let regs = unsafe { Regs::new(ctx.regs_ptr()) };
            let ip = unsafe { code.add(handler_pc) };
            let h = table.get(unsafe { *ip });
            become h(ip, regs, ex, ctx, table, roots, float)
        }
        if base == ctx.base_anchor() {
            return Acc::set(ctx.exception_word());
        }
        let caller = ctx.stack().pop_frame(base);
        ctx.set_frame_base(caller.base);
        pc = caller.handler_pc;
    }
}

handler!(op_load, Load, |ip, ops, regs, acc, ctx, table, roots, float| {
    let r = ops.signed::<0>();
    next!(Load, ip, regs, ctx, table, roots, float, Acc::set(regs.get(r, ctx.heap())))
});

handler!(op_store, Store, |ip, ops, regs, acc, ctx, table, roots, float| {
    let r = ops.signed::<0>();
    regs.set(r, acc.get(ctx.heap()));
    next!(Store, ip, regs, ctx, table, roots, float, acc)
});

handler!(op_add, Add, |ip, ops, regs, acc, ctx, table, roots, float| {
    let r = ops.signed::<0>();
    let h = ctx.heap();
    let lhs = regs.get(r, h);
    if let (Some(a), Some(b)) = (lhs.smi_bits(), acc.smi_bits())
        && let Some(sum) = a.checked_add(b)
    {
        next!(Add, ip, regs, ctx, table, roots, float, Acc::from_smi_bits(sum))
    }
    if let (Some(a), Some(b)) = (lhs.as_number(h), acc.get(h).as_number(h)) {
        let sum = a + b;
        if let Some(s) = Smi::from_f64(sum) {
            next!(Add, ip, regs, ctx, table, roots, float, Acc::set(s.into_tagged()))
        }
        if let Some(v) = ctx.heap_mut().try_new_float(sum) {
            let acc = Acc::set(v);
            next!(Add, ip, regs, ctx, table, roots, float, acc)
        }
        become slow_box_number::<STRIDE>(ip, regs, acc, ctx, table, roots, FloatReg::new(sum))
    }
    become slow_add::<STRIDE>(ip, regs, acc, ctx, table, roots, float)
});

cold_handler!(slow_box_number, |_ip, _ops, _regs, _acc, ctx, _float| {
    Acc::set(ctx.heap_mut().new_number(_float.get()))
});

cold_handler!(slow_add, |_ip, ops, regs, acc, ctx, _float| {
    let state = ctx.state;
    state.handle_scope(|scope| {
        let lhs = scope.handle(regs.get(ops.signed::<0>(), ctx.heap()));
        let rhs = scope.handle(acc.get(ctx.heap()));
        add(ctx, lhs, rhs)
    })
});

fn add(ctx: &mut Ctx<'_, '_>, lhs: Handle<'_, Value>, rhs: Handle<'_, Value>) -> Acc {
    let vm = ctx.vm;
    let state = ctx.state;
    let heap = ctx.heap_mut();
    state.handle_scope(|scope| {
        let lhs = match Object::to_primitive(vm, heap, state, lhs, Hint::Default) {
            Ok(Coercion::Threw) => return Acc::set(exception_word(heap)),
            Ok(Coercion::Value(v)) => scope.handle(v),
            Err(e) => return Acc::set(raise_runtime(vm, heap, state, e)),
        };
        let rhs = match Object::to_primitive(vm, heap, state, rhs, Hint::Default) {
            Ok(Coercion::Threw) => return Acc::set(exception_word(heap)),
            Ok(Coercion::Value(v)) => scope.handle(v),
            Err(e) => return Acc::set(raise_runtime(vm, heap, state, e)),
        };
        if lhs.as_tagged(heap).get_as::<DenseString>(heap).is_some()
            || rhs.as_tagged(heap).get_as::<DenseString>(heap).is_some()
        {
            let a = match Convert::to_string(heap, &scope, lhs) {
                Ok(v) => scope.handle(v),
                Err(e) => return Acc::set(raise_runtime(vm, heap, state, e)),
            };
            let b = match Convert::to_string(heap, &scope, rhs) {
                Ok(v) => scope.handle(v),
                Err(e) => return Acc::set(raise_runtime(vm, heap, state, e)),
            };
            Acc::set(
                DenseString::concat(heap, &scope, a, b)
                    .as_tagged(heap)
                    .erase(),
            )
        } else {
            let a = match lhs.as_tagged(heap).to_number(heap) {
                Ok(v) => v,
                Err(e) => return Acc::set(raise_runtime(vm, heap, state, e)),
            };
            let b = match rhs.as_tagged(heap).to_number(heap) {
                Ok(v) => v,
                Err(e) => return Acc::set(raise_runtime(vm, heap, state, e)),
            };
            let sum = a + b;
            match Smi::from_f64(sum) {
                Some(s) => Acc::set(s.into_tagged()),
                None => Acc::set(heap.new_number(sum)),
            }
        }
    })
}

handler!(op_call_runtime, CallRuntime, |ip, ops, regs, acc, ctx, table, roots, float| {
    let pc = ip as usize - ctx.code_ptr() as usize;
    let rt = ops.unsigned::<0>();
    let base = ops.signed::<1>();
    let count = ops.unsigned::<2>();
    let (vm, state) = (ctx.vm, ctx.state);
    let f = vm.runtime(NativeIndex(rt));
    let args = state.stack().window(state.frame_base(), base, count);
    let nctx = HostCtx::new(vm, ctx.heap_mut(), state);
    let v = f(nctx, None, args);
    // the callee's result view is fresh, but a view may not cross the
    // continuation's heap-exclusive use — and raw()-ing it here would
    // just trade that for a freshness convention. Park it in the acc
    // slot (collector-updated) and re-read the raw word: safe even if
    // the continuation ever grows an allocation.
    let acc_slot = state.acc_slot();
    acc_slot.store(v);
    let w = Acc::set(acc_slot.get(ctx.heap()));
    become resume(unsafe { ctx.code_ptr().add(pc) }, regs, w, ctx, table, roots, float)
});

// ---------------------------------------------------------------------------
// table: forces monomorphization (STRIDE = 1) for codegen comparison

const fn new_table() -> [Handler; 256] {
    let mut t = [op_trap as Handler; 256];
    t[Opcode::Load as usize] = op_load::<1> as Handler;
    t[Opcode::Store as usize] = op_store::<1> as Handler;
    t[Opcode::Add as usize] = op_add::<1> as Handler;
    t[Opcode::CallRuntime as usize] = op_call_runtime::<1> as Handler;
    t
}

#[used]
pub static NEW_TABLE_NARROW: [Handler; 256] = new_table();
