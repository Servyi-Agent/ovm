use mark_sweep::{MarkSweep, MarkSweepConfig};
use vm::{
    FixedArray, Found, HandleSlice, Heap, Lookup, LookupActionGet, Object, PropertyDescriptor,
    SlotName, Smi, Tagged, Thread, VM, Value, find_in_chain,
};

fn smi(v: i64) -> Value {
    Smi::new(v).encode()
}

/// Safety helper: these tests only pass words that were loaded or
/// allocated under the very heap borrow they are re-anchored at, with no
/// collection in between.
unsafe fn anchored<'a>(_heap: &'a Heap, v: Value) -> Tagged<'a, Value> {
    unsafe { Tagged::<Value>::from_value_unchecked(v) }
}

/// A name tag from a raw word. Tests only: no collection may run between
/// the word's load and its consumption.
fn raw_name(w: Value) -> Tagged<'static, SlotName> {
    unsafe { Tagged::<Value>::from_value_unchecked(w) }.as_name()
}

fn thread() -> (VM, Thread) {
    let vm = VM::new::<MarkSweep, vm::DefaultInterpreter>(MarkSweepConfig::default()).unwrap();
    let thread = vm.attach();
    (vm, thread)
}

/// The well-known `null` word for `thread`'s heap.
fn null_word(thread: &mut Thread) -> Value {
    let heap = thread.heap();
    heap.known().null.get(heap).raw()
}

/// A fresh ordinary object with `proto` (any of the three shapes) and
/// integer-valued data properties.
fn object_with(thread: &mut Thread, proto: Value, props: &[(&str, i64)]) -> Value {
    thread.handle_scope(|thread, scope| {
        let map = thread.heap().known().object_initial_map.as_handle();
        let obj = thread
            .heap()
            .new_object(&scope, map, HandleSlice::EMPTY)
            .as_handle(&scope);
        // Safety: caller-supplied proto word, rooted before any allocation.
        let proto = scope.handle(unsafe { Tagged::<Value>::from_value_unchecked(proto) });
        Object::set_prototype(thread.heap(), &scope, obj, proto).unwrap();
        for (name, v) in props {
            let name = thread.intern(&scope, name);
            let name = scope.handle(name.as_tagged(thread.heap()));
            let value = scope.handle(Smi::new(*v));
            Object::add_own_property(
                thread.heap(),
                &scope,
                obj,
                name,
                PropertyDescriptor::data(value),
            )
            .unwrap();
        }
        obj.as_tagged(thread.heap()).raw()
    })
}

fn slot_name(thread: &mut Thread, name: &str) -> Tagged<'static, SlotName> {
    thread.handle_scope(|thread, scope| {
        let interned = thread.intern(&scope, name);
        let heap = thread.heap();
        raw_name(interned.as_tagged(heap).raw())
    })
}

fn parents_of(thread: &mut Thread, p1: Value, p2: Value) -> Value {
    thread.handle_scope(|thread, scope| {
        let first = thread.intern(&scope, "parent");
        let second = thread.intern(&scope, "mixin");
        let (first, second) = {
            let heap = thread.heap();
            (first.as_tagged(heap).raw(), second.as_tagged(heap).raw())
        };
        let arr = {
            let _heap = thread.heap();
            thread.heap().allocate_handle::<FixedArray>(
                scope.stage(&[
                    unsafe { Tagged::<Value>::from_value_unchecked(first) },
                    unsafe { Tagged::from_value_unchecked(p1) },
                    unsafe { Tagged::from_value_unchecked(second) },
                    unsafe { Tagged::from_value_unchecked(p2) },
                ]),
                &scope,
            )
        };
        let heap = thread.heap();
        arr.as_tagged(heap).raw()
    })
}

#[test]
fn find_in_chain_respects_priority_order() {
    let (_vm, mut thread) = thread();
    let null = null_word(&mut thread);
    let p1 = object_with(&mut thread, null, &[("a", 1)]);
    let p2 = object_with(&mut thread, null, &[("a", 2), ("b", 3)]);
    let protos = parents_of(&mut thread, p1, p2);
    let a = slot_name(&mut thread, "a");
    let b = slot_name(&mut thread, "b");
    let missing = slot_name(&mut thread, "nope");

    {
        let heap = thread.heap();
        // "a" exists on both parents: the first in priority order wins
        match find_in_chain::<false>(heap, unsafe { anchored(heap, protos) }, a.erase(), None)
            .expect("a lookup")
        {
            Found::MapData { slot, .. } => {
                assert_eq!(slot.get(heap).raw(), smi(1));
            }
            _ => panic!("a must resolve through the first parent"),
        }
        // "b" only exists on the second parent
        match find_in_chain::<false>(heap, unsafe { anchored(heap, protos) }, b.erase(), None)
            .expect("b lookup")
        {
            Found::MapData { slot, .. } => assert_eq!(slot.get(heap).raw(), smi(3)),
            _ => panic!("b must resolve through the second parent"),
        }
        assert!(matches!(
            find_in_chain::<false>(
                heap,
                unsafe { anchored(heap, protos) },
                missing.erase(),
                None
            )
            .expect("missing lookup"),
            Found::Missing
        ));
        // null terminates the chain
        assert!(matches!(
            find_in_chain::<false>(heap, unsafe { anchored(heap, null) }, a.erase(), None)
                .expect("null lookup"),
            Found::Missing
        ));
    };
}

#[test]
fn lookup_skips_multi_parent_cycles() {
    let (_vm, mut thread) = thread();
    let name_a = slot_name(&mut thread, "a");
    let name_b = slot_name(&mut thread, "b");
    let is_undefined = thread.handle_scope(|thread, scope| {
        let (_vm, heap, _state) = thread.split();
        let zero = Smi::new(0).into_tagged();
        let a = heap.allocate_handle::<FixedArray>(scope.stage(&[zero, zero, zero, zero]), &scope);
        let b = heap.allocate_handle::<FixedArray>(scope.stage(&[zero, zero, zero, zero]), &scope);
        a.as_tagged(heap).set(heap, 0, name_a.erase());
        a.as_tagged(heap).set(heap, 2, name_b.erase());
        b.as_tagged(heap).set(heap, 0, name_a.erase());
        b.as_tagged(heap).set(heap, 2, name_b.erase());
        a.as_tagged(heap).set(heap, 1, b.as_tagged(heap).erase());
        b.as_tagged(heap).set(heap, 3, a.as_tagged(heap).erase());

        let start = scope.handle(a.as_tagged(heap).erase());
        let key = scope.handle(name_a.erase());
        let outcome = Lookup::get(heap, &scope, start, key)?;
        Ok::<bool, vm::VmError>(matches!(outcome, LookupActionGet::Missing))
    });
    assert!(is_undefined.expect("cycle lookup must terminate"));
}
