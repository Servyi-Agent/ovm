#![allow(dead_code)]

use bytecode::Opcode;
use vm_core::{
    Coercion, Convert, DenseString, Handle, Heap, Hint, HostCtx, NativeIndex, Object, Register,
    Smi, Tagged, ThreadState, VM, Value, VmError, Word, raise_runtime,
};

use crate::{FloatReg, Ops, Regs, RootsArg, star_lookahead};

pub struct Ctx<'s, 'h> {
    vm: &'s VM,
    state: &'s ThreadState,
    heap: &'h mut Heap,
    /// Anchor of the frame `execute` entered
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
    pub fn raise_tag(&mut self, err: VmError) -> Acc {
        let (vm, state) = (self.vm, self.state);
        Acc::set(raise_runtime(vm, self.heap_mut(), state, err))
    }
}

#[derive(Clone, Copy)]
pub struct Acc(Value);

impl Acc {
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

macro_rules! reenter {
    ($op:ident, $pc:expr, $regs:expr, $acc:expr, $ctx:expr, $table:expr, $roots:expr, $float:expr) => {{
        let fault_ip = unsafe { $ctx.code_ptr().add($pc) };
        if $acc.get($ctx.heap()).raw().to_bits()
            == $ctx
                .heap()
                .known()
                .exception
                .as_tagged($ctx.heap())
                .erase()
                .raw()
                .to_bits()
        {
            become throw_dispatch(fault_ip, $regs, $acc, $ctx, $table, $roots, $float)
        }
        let p = fault_ip.wrapping_add(
            (if STRIDE == 2 { 2 } else { 1 }) + STRIDE * const { Opcode::$op.operands().len() },
        );
        let regs = unsafe { Regs::new($ctx.regs_ptr()) };
        let h = $table.get(unsafe { *p });
        become h(p, regs, $acc, $ctx, $table, $roots, $float)
    }};
}

macro_rules! next_slow {
    ($op:ident, $ip:expr, $regs:expr, $acc:expr, $ctx:expr, $table:expr, $roots:expr, $float:expr, $slow:path) => {{
        let pc = $ip as usize - $ctx.code_ptr() as usize;
        let v: Acc = $slow($ip, $regs, $acc, $ctx, $float);
        let state: &ThreadState = $ctx.state;
        let acc_slot = state.acc_slot();
        acc_slot.store(v.get($ctx.heap()));
        let acc = Acc::set(acc_slot.get($ctx.heap()));
        reenter!($op, pc, $regs, acc, $ctx, $table, $roots, $float)
    }};
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
            return Acc::set(ctx.heap().known().exception.as_tagged(ctx.heap()).erase());
        }
        let caller = ctx.stack().pop_frame(base);
        ctx.set_frame_base(caller.base);
        pc = caller.handler_pc;
    }
}

#[rustfmt::skip]
#[rustc_align(32)]
extern "rust-preserve-none" fn op_load<'h, const STRIDE: usize>(ip: *const u8, regs: Regs, acc: Acc, ctx: &mut Ctx<'_, 'h>, table: TableArg<'h>, roots: RootsArg<'h>, float: FloatReg) -> Acc {
    let ops = Ops::<STRIDE>::new(ip, Opcode::Load);
    let r = ops.signed::<0>();
    next!(Load, ip, regs, ctx, table, roots, float, Acc::set(regs.get(r, ctx.heap())))
}

#[rustfmt::skip]
#[rustc_align(32)]
extern "rust-preserve-none" fn op_store<'h, const STRIDE: usize>(ip: *const u8, regs: Regs, acc: Acc, ctx: &mut Ctx<'_, 'h>, table: TableArg<'h>, roots: RootsArg<'h>, float: FloatReg) -> Acc {
    let ops = Ops::<STRIDE>::new(ip, Opcode::Store);
    let r = ops.signed::<0>();
    regs.set(r, acc.get(ctx.heap()));
    next!(Store, ip, regs, ctx, table, roots, float, acc)
}

#[rustfmt::skip]
#[rustc_align(32)]
extern "rust-preserve-none" fn op_add<'h, const STRIDE: usize>(ip: *const u8, regs: Regs, acc: Acc, ctx: &mut Ctx<'_, 'h>, table: TableArg<'h>, roots: RootsArg<'h>, float: FloatReg) -> Acc {
    let ops = Ops::<STRIDE>::new(ip, Opcode::Add);
    let r = ops.signed::<0>();
    let h = ctx.heap();
    let lhs = regs.get(r, h);
    if let (Some(a), Some(b)) = (lhs.smi_bits(), acc.get(ctx.heap()).smi_bits())
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
        next_slow!(Add, ip, regs, acc, ctx, table, roots, FloatReg::new(sum), slow_box_number::<STRIDE>)
    }
    next_slow!(Add, ip, regs, acc, ctx, table, roots, float, slow_add::<STRIDE>)
}

#[cold]
#[rustfmt::skip]
fn slow_box_number<'h, const STRIDE: usize>(_ip: *const u8, _regs: Regs, _acc: Acc, ctx: &mut Ctx<'_, 'h>, float: FloatReg) -> Acc {
    Acc::set(ctx.heap_mut().new_number(float.get()))
}

#[cold]
#[rustfmt::skip]
fn slow_add<'h, const STRIDE: usize>(ip: *const u8, regs: Regs, acc: Acc, ctx: &mut Ctx<'_, 'h>, _float: FloatReg) -> Acc {
    let ops = Ops::<STRIDE>::from_ip(ip);
    let state = ctx.state;
    state.handle_scope(|scope| {
        let lhs = scope.handle(regs.get(ops.signed::<0>(), ctx.heap()));
        let rhs = scope.handle(acc.get(ctx.heap()));
        add(ctx, lhs, rhs)
    })
}

fn add(ctx: &mut Ctx<'_, '_>, lhs: Handle<'_, Value>, rhs: Handle<'_, Value>) -> Acc {
    let vm = ctx.vm;
    let state = ctx.state;
    let heap = ctx.heap_mut();
    state.handle_scope(|scope| {
        let lhs = match Object::to_primitive(vm, heap, state, lhs, Hint::Default) {
            Ok(Coercion::Threw) => return Acc::set(heap.known().exception.as_tagged(heap).erase()),
            Ok(Coercion::Value(v)) => scope.handle(v),
            Err(e) => return Acc::set(raise_runtime(vm, heap, state, e)),
        };
        let rhs = match Object::to_primitive(vm, heap, state, rhs, Hint::Default) {
            Ok(Coercion::Threw) => return Acc::set(heap.known().exception.as_tagged(heap).erase()),
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

#[rustfmt::skip]
#[rustc_align(32)]
extern "rust-preserve-none" fn op_call_runtime<'h, const STRIDE: usize>(ip: *const u8, regs: Regs, acc: Acc, ctx: &mut Ctx<'_, 'h>, table: TableArg<'h>, roots: RootsArg<'h>, float: FloatReg) -> Acc {
    let ops = Ops::<STRIDE>::new(ip, Opcode::CallRuntime);
    let pc = ip as usize - ctx.code_ptr() as usize;
    let rt = ops.unsigned::<0>();
    let base = ops.signed::<1>();
    let count = ops.unsigned::<2>();
    let (vm, state) = (ctx.vm, ctx.state);
    let f = vm.runtime(NativeIndex(rt));
    let args = state.stack().window(state.frame_base(), base, count);
    let nctx = HostCtx::new(vm, ctx.heap_mut(), state);
    let v = f(nctx, None, args);
    let acc_slot = state.acc_slot();
    acc_slot.store(v);
    let w = Acc::set(acc_slot.get(ctx.heap()));
    reenter!(CallRuntime, pc, regs, w, ctx, table, roots, float)
}

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
