use crate::proxy::Proxy;
use crate::{
    AccessorPair, Coercion, Convert, DETAILS_ACCESSOR, DETAILS_CONFIGURABLE, DETAILS_ENUMERABLE,
    DETAILS_WRITABLE, DenseString, FixedArray, Float, GcSlot, Handle, HandleScope, Heap, Map,
    Object, PartialDescriptor, PropertyDescriptor, SlotFlags, SlotName, Smi, StringData, StringOwn,
    Symbol, Tagged, ThreadState, VM, Value, VmError,
};

pub enum Lookup<'a> {
    Data {
        holder: Tagged<'a, Object>,
        map_index: usize,
        holder_index: usize,
        slot: &'a GcSlot,
        flags: SlotFlags,
    },
    Accessor {
        holder: Tagged<'a, Object>,
        map_index: usize,
        pair: Tagged<'a, AccessorPair>,
    },
    NotFound,
}

pub enum Key<'a> {
    Element(usize),
    Name(Tagged<'a, SlotName>),
}

pub enum LoadOutcome<'a> {
    Value(Tagged<'a, Value>),
    Getter(Tagged<'a, Value>),
    Threw,
}

pub enum ChainLoad<'a> {
    Value(Tagged<'a, Value>),
    Getter(Tagged<'a, Value>),
    NotFound,
    Threw,
}

impl<'a> Tagged<'a, Value> {
    pub fn classify_key(self, heap: &'a Heap) -> Result<Key<'a>, VmError> {
        if let Some(v) = self.to_i64() {
            if (0..u32::MAX as i64).contains(&v) {
                return usize::try_from(v)
                    .map(Key::Element)
                    .map_err(|_| VmError::OutOfBounds);
            }
            return Ok(Key::Name(Tagged::from(Smi::new(v))));
        }
        if let Some(s) = self.get_as::<DenseString>(heap) {
            if let Some(i) = s.data(heap).canonical_index()
                && i < u32::MAX as usize
            {
                return Ok(Key::Element(i));
            }
            return Ok(Key::Name(s.into()));
        }
        if let Some(s) = self.get_as::<Symbol>(heap) {
            return Ok(Key::Name(s.into()));
        }
        Err(VmError::Type)
    }

    pub fn get_no_gc(
        self,
        heap: &'a Heap,
        name: Tagged<'a, SlotName>,
    ) -> Result<LoadOutcome<'a>, VmError> {
        let known = heap.known();
        if self == known.null.get(heap) || self == known.undefined.get(heap) {
            return Err(VmError::Type);
        }
        if let Some(obj) = self.as_heap_object()
            && let Some(v) = obj.array_length(heap, name)
        {
            return Ok(LoadOutcome::Value(v));
        }
        if let Some(s) = DenseString::from_receiver(heap, self)
            && let Some(StringOwn::Length(len)) = s.own_key(heap, name)
        {
            return Ok(LoadOutcome::Value(Smi::new(len as i64).into_tagged()));
        }
        let holder = if self.to_i64().is_some() || self.get_as::<Float>(heap).is_some() {
            known.number_prototype.get(heap).erase()
        } else if self.get_as::<DenseString>(heap).is_some() {
            known.string_prototype.get(heap).erase()
        } else if self == known.true_object.get(heap) || self == known.false_object.get(heap) {
            known.boolean_prototype.get(heap).erase()
        } else {
            self
        };
        match holder.lookup(heap, name) {
            Lookup::Data { slot, .. } => Ok(LoadOutcome::Value(slot.get(heap))),
            Lookup::Accessor { pair, .. } => {
                let getter = pair.get.get(heap);
                if getter == known.undefined.get(heap) {
                    Ok(LoadOutcome::Value(known.undefined.get(heap).erase()))
                } else {
                    Ok(LoadOutcome::Getter(getter))
                }
            }
            Lookup::NotFound => Ok(LoadOutcome::Value(known.undefined.get(heap).erase())),
        }
    }

    pub fn ordinary_own_descriptor<'s>(
        self,
        heap: &'a Heap,
        scope: &'s HandleScope<'_>,
        key: Tagged<'a, Value>,
    ) -> Option<PropertyDescriptor<'s>> {
        if let Ok(Key::Element(i)) = key.classify_key(heap)
            && let Some(o) = self.as_heap_object()
            && let Some(dict) = o.element_dictionary(heap)
            && let Some(entry) = dict.find(heap, i)
        {
            let details = dict.details_at(heap, entry);
            if details & DETAILS_ACCESSOR != 0 {
                let pair = dict.value_at(heap, entry).get_as::<AccessorPair>(heap)?;
                return Some(PropertyDescriptor::Accessor {
                    get: scope.handle(pair.get.get(heap)),
                    set: scope.handle(pair.set.get(heap)),
                    enumerable: details & DETAILS_ENUMERABLE != 0,
                    configurable: details & DETAILS_CONFIGURABLE != 0,
                });
            }
            return Some(PropertyDescriptor::Data {
                value: scope.handle(dict.value_at(heap, entry)),
                writable: details & DETAILS_WRITABLE != 0,
                enumerable: details & DETAILS_ENUMERABLE != 0,
                configurable: details & DETAILS_CONFIGURABLE != 0,
            });
        }
        if let Ok(Key::Element(i)) = key.classify_key(heap)
            && let Some(o) = self.as_heap_object()
            && let Some(v) = o.element_value(heap, i)
        {
            return Some(PropertyDescriptor::Data {
                value: scope.handle(v),
                writable: true,
                enumerable: true,
                configurable: true,
            });
        }
        let name = key.as_name();
        let o = self.as_heap_object()?;
        if let Some(v) = o.array_length(heap, name) {
            return Some(PropertyDescriptor::Data {
                value: scope.handle(v),
                writable: true,
                enumerable: false,
                configurable: false,
            });
        }
        let map = o.map(heap);
        for d in map.descriptors() {
            if !d.name(heap).ptr_eq(name) {
                continue;
            }
            if d.flags().is_accessor() {
                let pair = d
                    .value
                    .get(heap)
                    .get_as::<AccessorPair>(heap)
                    .expect("accessor descriptor holds a pair");
                return Some(PropertyDescriptor::Accessor {
                    get: scope.handle(pair.get.get(heap)),
                    set: scope.handle(pair.set.get(heap)),
                    enumerable: d.flags().is_enumerable(),
                    configurable: d.flags().is_configurable(),
                });
            }
            let slot = o.slot(heap, d.offset());
            return Some(PropertyDescriptor::Data {
                value: scope.handle(slot.get(heap)),
                writable: d.flags().is_writable(),
                enumerable: d.flags().is_enumerable(),
                configurable: d.flags().is_configurable(),
            });
        }
        None
    }

    pub fn lookup_in_parents(self, heap: &'a Heap, name: Tagged<'a, SlotName>) -> Lookup<'a> {
        if self == heap.known().null.get(heap) {
            return Lookup::NotFound;
        }
        if let Some(pairs) = self.get_as::<FixedArray>(heap) {
            // look *inside* the parents: the pair names are slots of the child
            let mut i = 1;
            while i < pairs.len() {
                let result = pairs.at(heap, i).lookup(heap, name);
                if !matches!(result, Lookup::NotFound) {
                    return result;
                }
                i += 2;
            }
            return Lookup::NotFound;
        }
        self.lookup(heap, name)
    }

    /// The home object's [[Prototype]] slot, raw (null / object / FixedArray
    /// of parents / unset). Extracted before ToPropertyKey so key coercion
    /// cannot observe a different chain than the lookup uses (ES 15.4.2:
    /// GetSuperBase happens first).
    pub fn home_proto(self, heap: &'a Heap) -> Option<Tagged<'a, Value>> {
        let obj = self.as_heap_object()?;
        Some(obj.prototype(heap))
    }
}

impl<'a> Lookup<'a> {
    /// ES `[[Get]]` over the prototype chain with per-holder semantics:
    /// virtual own properties (array `length`, String wrapper length/index),
    /// proxy `get` traps, and getters. `start` must be object-coercible;
    /// the first `null`/`undefined` in the chain ends the walk.
    pub fn get<'h>(
        vm: &VM,
        heap: &'h mut Heap,
        state: &ThreadState,
        scope: &HandleScope<'_>,
        start: Handle<'_, Value>,
        receiver: Handle<'_, Value>,
        key: Handle<'_, Value>,
    ) -> Result<LoadOutcome<'h>, VmError> {
        if start.as_tagged(heap).is_nullish(heap) {
            return Err(VmError::Type);
        }
        let walked = walk_get(vm, heap, state, scope, start, receiver, key)?;
        Ok(match walked {
            Walk::Value(v) => LoadOutcome::Value(v),
            Walk::Getter(g) => LoadOutcome::Getter(g),
            Walk::NotFound(v) => LoadOutcome::Value(v),
            Walk::Threw => LoadOutcome::Threw,
        })
    }
}

impl<'a> Lookup<'a> {
    /// Like `Lookup::get`, but preserves the not-found state. Used
    /// by global binding reads, which turn a miss into a ReferenceError.
    pub fn get_with_missing<'h>(
        vm: &VM,
        heap: &'h mut Heap,
        state: &ThreadState,
        scope: &HandleScope<'_>,
        start: Handle<'_, Value>,
        key: Handle<'_, Value>,
    ) -> Result<ChainLoad<'h>, VmError> {
        if start.as_tagged(heap).is_nullish(heap) {
            return Err(VmError::Type);
        }
        Ok(match walk_get(vm, heap, state, scope, start, start, key)? {
            Walk::Value(v) => ChainLoad::Value(v),
            Walk::Getter(g) => ChainLoad::Getter(g),
            Walk::NotFound(_) => ChainLoad::NotFound,
            Walk::Threw => ChainLoad::Threw,
        })
    }
}

impl<'a> Lookup<'a> {
    /// ES `[[Set]]` over the prototype chain with the receiver split from
    /// the lookup start. Ordinary accessors are returned, never invoked.
    pub fn set<'s, const WRITE_THROUGH: bool>(
        vm: &VM,
        heap: &mut Heap,
        state: &ThreadState,
        scope: &'s HandleScope<'_>,
        start: Handle<'_, Value>,
        receiver: Handle<'_, Value>,
        key: Handle<'_, Value>,
        value: Handle<'_, Value>,
    ) -> Result<SetWalk<'s>, VmError> {
        walk_set::<WRITE_THROUGH>(vm, heap, state, scope, start, receiver, key, value)
    }
}

impl<'a> Lookup<'a> {
    /// ES `[[HasProperty]]` over the prototype chain: per-holder virtual
    /// own properties, String indices, and proxy `has` traps.
    pub fn has<'h>(
        vm: &VM,
        heap: &'h mut Heap,
        state: &ThreadState,
        scope: &HandleScope<'_>,
        start: Handle<'_, Value>,
        key: Handle<'_, Value>,
    ) -> Result<Coercion<'h>, VmError> {
        if start.as_tagged(heap).is_nullish(heap) {
            return Err(VmError::Type);
        }
        match walk_has(vm, heap, state, scope, start, key)? {
            HasWalk::Value(found) => Ok(Coercion::Value(Convert::boolean(heap, found))),
            HasWalk::Threw => Ok(Coercion::Threw),
        }
    }
}

impl StringData<'_> {
    /// Canonical array-index form: decimal digits, no leading zero, no
    /// overflow past `u32::MAX`-worthy lengths.
    pub fn canonical_index(&self) -> Option<usize> {
        if self.is_empty() || self.len() > 10 {
            return None;
        }
        if self.code_unit(0) == b'0' as u16 {
            return (self.len() == 1).then_some(0);
        }
        let mut n: usize = 0;
        for i in 0..self.len() {
            let c = self.code_unit(i);
            if !(b'0' as u16..=b'9' as u16).contains(&c) {
                return None;
            }
            n = n.checked_mul(10)?.checked_add((c - b'0' as u16) as usize)?;
        }
        Some(n)
    }
}

impl Lookup<'_> {
    pub fn to_property_descriptor<'s>(
        vm: &VM,
        heap: &mut Heap,
        state: &ThreadState,
        scope: &'s HandleScope<'_>,
        attrs: Handle<'_, Value>,
    ) -> Result<Option<PartialDescriptor<'s>>, VmError> {
        let cond_4 = attrs.as_tagged(heap).is_primitive(heap);
        if cond_4 {
            return Err(VmError::Type);
        }
        let attrs = scope.handle(attrs.as_tagged(heap));
        let names: [Handle<'_, Value>; 6] = {
            let s = &heap.known().strings;
            [
                scope.handle(s.value.get(heap).erase()),
                scope.handle(s.get.get(heap).erase()),
                scope.handle(s.set.get(heap).erase()),
                scope.handle(s.writable.get(heap).erase()),
                scope.handle(s.enumerable.get(heap).erase()),
                scope.handle(s.configurable.get(heap).erase()),
            ]
        };
        let mut reads: Vec<Handle<'_, Value>> = Vec::new();
        for name in names {
            match Object::get_property(vm, heap, state, attrs, attrs, name)? {
                Coercion::Threw => return Ok(None),
                // Safety: fresh word from the call, no allocation since.
                Coercion::Value(v) => reads.push(scope.handle(v)),
            }
        }
        let (present, truthy) = {
            let undef = heap.known().undefined.get(heap).erase();
            let present = [
                !reads[0].as_tagged(heap).ptr_eq(undef),
                !reads[1].as_tagged(heap).ptr_eq(undef),
                !reads[2].as_tagged(heap).ptr_eq(undef),
                !reads[3].as_tagged(heap).ptr_eq(undef),
                !reads[4].as_tagged(heap).ptr_eq(undef),
                !reads[5].as_tagged(heap).ptr_eq(undef),
            ];
            let truthy = [
                reads[3].as_tagged(heap).is_truthy(heap),
                reads[4].as_tagged(heap).is_truthy(heap),
                reads[5].as_tagged(heap).is_truthy(heap),
            ];
            (present, truthy)
        };
        let value = present[0].then_some(reads[0]);
        let get = present[1].then_some(reads[1]);
        let set = present[2].then_some(reads[2]);
        // accessor halves must be callable or undefined
        if get.is_some() || set.is_some() {
            for half in [get, set] {
                if let Some(h) = half
                    && !h.as_tagged(heap).is_callable(heap)
                {
                    return Err(VmError::Type);
                }
            }
        }
        Ok(Some(PartialDescriptor {
            value,
            get,
            set,
            writable: present[3].then_some(truthy[0]),
            enumerable: present[4].then_some(truthy[1]),
            configurable: present[5].then_some(truthy[2]),
        }))
    }
}

enum Walk<'a> {
    Value(Tagged<'a, Value>),
    Getter(Tagged<'a, Value>),
    NotFound(Tagged<'a, Value>),
    Threw,
}

enum HasWalk {
    Value(bool),
    Threw,
}

/// Holder traversal shared by `[[Get]]`, `[[HasProperty]]` and `[[Set]]`.
/// The worklist is only allocated for Self-style multi-parent links. Every
/// holder is a handle, so it stays valid if an operation runs user code and
/// allocates before the next step.
struct ChainWalk<'s> {
    current: Option<Handle<'s, Value>>,
    pending: Vec<Handle<'s, Value>>,
    steps: usize,
}

impl<'s> ChainWalk<'s> {
    fn new(heap: &Heap, scope: &'s HandleScope<'_>, start: Handle<'_, Value>) -> Self {
        let start = start.as_tagged(heap);
        if let Some(pairs) = start.get_as::<FixedArray>(heap) {
            let mut pending = Vec::new();
            let mut i = pairs.len();
            while i >= 2 {
                i -= 2;
                pending.push(scope.handle(pairs.at(heap, i + 1)));
            }
            return Self {
                current: None,
                pending,
                steps: 0,
            };
        }
        Self {
            current: Some(scope.handle(start.erase())),
            pending: Vec::new(),
            steps: 0,
        }
    }

    fn next(
        &mut self,
        heap: &Heap,
        scope: &'s HandleScope<'_>,
    ) -> Result<Option<Handle<'s, Value>>, VmError> {
        loop {
            let holder = match self.current.take() {
                Some(holder) => holder,
                None => match self.pending.pop() {
                    Some(holder) => holder,
                    None => return Ok(None),
                },
            };
            self.steps += 1;
            if self.steps > 10_000 {
                return Err(VmError::StackOverflow);
            }
            let cur = holder.as_tagged(heap);
            if cur.is_nullish(heap) || cur.ptr_eq(heap.known().the_hole.get(heap).erase()) {
                continue;
            }

            let next: Option<Handle<'s, Value>> = if let Some(proto) = cur.primitive_prototype(heap)
            {
                Some(scope.handle(proto))
            } else {
                cur.as_heap_object()
                    .map(|obj| scope.handle(obj.prototype(heap)))
            };
            if let Some(next) = next {
                let next_value = next.as_tagged(heap);
                let known = heap.known();
                let stop = next_value.ptr_eq(known.null.get(heap).erase())
                    || next_value.ptr_eq(known.the_hole.get(heap).erase())
                    || next_value.ptr_eq(known.undefined.get(heap).erase());
                if !stop {
                    if let Some(pairs) = next_value.get_as::<FixedArray>(heap) {
                        // Push in reverse so `pop` preserves the parent
                        // order recorded in the pair list.
                        let mut i = pairs.len();
                        while i >= 2 {
                            i -= 2;
                            self.pending.push(scope.handle(pairs.at(heap, i + 1)));
                        }
                    } else {
                        self.current = Some(next);
                    }
                }
            }
            return Ok(Some(holder));
        }
    }
}

/// The first interesting holder in a prototype walk: a proxy, an own
/// property, or the end of the chain. The traversal is shared by get, set,
/// and has; only the entry function interprets the result.
enum Found<'s> {
    Proxy(Handle<'s, Value>),
    Own {
        holder: Handle<'s, Value>,
        property: OwnProperty<'s>,
    },
    Missing,
}

enum OwnProperty<'s> {
    String(StringOwn),
    Descriptor(PropertyDescriptor<'s>),
    Parent(Handle<'s, Value>),
}

/// Locate the first holder that owns `key`, or the first proxy in the
/// chain, without executing any user code. Own-property checks include
/// String exotics, array lengths/elements, and Self parent-name slots.
fn find_holder<'h, 's>(
    heap: &'h Heap,
    scope: &'s HandleScope<'_>,
    start: Handle<'_, Value>,
    key: Tagged<'h, Value>,
) -> Result<Found<'s>, VmError> {
    let name = key.as_name();
    let mut chain = ChainWalk::new(heap, scope, start);
    while let Some(holder) = chain.next(heap, scope)? {
        if Proxy::is_proxy(heap, holder.as_tagged(heap)) {
            return Ok(Found::Proxy(holder));
        }
        if let Some(string) = DenseString::from_receiver(heap, holder.as_tagged(heap))
            .and_then(|s| s.own_key(heap, name))
        {
            return Ok(Found::Own {
                holder,
                property: OwnProperty::String(string),
            });
        }
        if let Some(desc) = holder
            .as_tagged(heap)
            .ordinary_own_descriptor(heap, scope, key)
        {
            return Ok(Found::Own {
                holder,
                property: OwnProperty::Descriptor(desc),
            });
        }
        if let Some(value) = parent_name(heap, holder.as_tagged(heap), name) {
            let value = scope.handle(value);
            return Ok(Found::Own {
                holder,
                property: OwnProperty::Parent(value),
            });
        }
    }
    Ok(Found::Missing)
}

/// Self-style parent-name slot stored in the map's parent pairs.
fn parent_name<'a>(
    heap: &'a Heap,
    holder: Tagged<'a, Value>,
    name: Tagged<'a, SlotName>,
) -> Option<Tagged<'a, Value>> {
    holder.as_heap_object().and_then(|obj| {
        obj.map(heap)
            .prototype
            .get(heap)
            .get_as::<FixedArray>(heap)
            .and_then(|pairs| {
                let name = name.erase();
                let mut i = 0;
                while i < pairs.len() {
                    if pairs.at(heap, i).ptr_eq(name) {
                        return Some(pairs.at(heap, i + 1));
                    }
                    i += 2;
                }
                None
            })
    })
}

/// ES `[[Get]]` over the prototype chain with per-holder semantics:
/// virtual own properties (array `length`, String wrapper length/index),
/// proxy `get` traps, and getters. The accessor itself is returned; the
/// caller decides how to invoke it.
fn walk_get<'h>(
    vm: &VM,
    heap: &'h mut Heap,
    state: &ThreadState,
    scope: &HandleScope<'_>,
    start: Handle<'_, Value>,
    receiver: Handle<'_, Value>,
    key: Handle<'_, Value>,
) -> Result<Walk<'h>, VmError> {
    match find_holder(heap, scope, start, key.as_tagged(heap))? {
        Found::Proxy(proxy) => match Proxy::get(vm, heap, state, proxy, receiver, key)? {
            Coercion::Value(v) => {
                let v = scope.handle(v);
                Ok(Walk::Value(v.as_tagged(heap)))
            }
            Coercion::Threw => Ok(Walk::Threw),
        },
        Found::Own { holder, property } => Ok(match property {
            OwnProperty::String(StringOwn::Length(len)) => {
                Walk::Value(Smi::new(len as i64).into_tagged())
            }
            OwnProperty::String(StringOwn::Index(i)) => {
                let unit = {
                    let s = DenseString::from_receiver(heap, holder.as_tagged(heap))
                        .expect("string own key from a string receiver");
                    s.code_unit(heap, i)
                };
                let value = DenseString::from_units(heap, scope, &[unit]);
                Walk::Value(value.as_tagged(heap).erase())
            }
            OwnProperty::Descriptor(PropertyDescriptor::Data { value, .. }) => {
                Walk::Value(value.as_tagged(heap))
            }
            OwnProperty::Descriptor(PropertyDescriptor::Accessor { get, .. }) => {
                let getter = get.as_tagged(heap);
                if getter == heap.known().undefined.get(heap).erase() {
                    Walk::Value(heap.known().undefined.get(heap).erase())
                } else {
                    Walk::Getter(getter)
                }
            }
            OwnProperty::Parent(value) => Walk::Value(value.as_tagged(heap)),
        }),
        Found::Missing => Ok(Walk::NotFound(heap.known().undefined.get(heap).erase())),
    }
}

/// Result of one ordinary `[[Set]]` step. The walk never invokes an
/// accessor setter; `CallSetter` is handed back to the caller. `Define`
/// means the receiver's `[[DefineOwnProperty]]` must run with the value.
pub enum SetWalk<'s> {
    Done,
    Rejected,
    CallSetter(Handle<'s, Value>),
    Define {
        receiver: Handle<'s, Value>,
        key: Handle<'s, Value>,
    },
    Threw,
}

/// ES `OrdinarySet` over the prototype chain (receiver-aware). Data slots
/// are written in place; inherited writable data and absent properties
/// become a `Define` on the receiver; accessors are returned for the caller
/// to invoke.
fn walk_set<'s, const WRITE_THROUGH: bool>(
    vm: &VM,
    heap: &mut Heap,
    state: &ThreadState,
    scope: &'s HandleScope<'_>,
    start: Handle<'_, Value>,
    receiver: Handle<'_, Value>,
    key: Handle<'_, Value>,
    value: Handle<'_, Value>,
) -> Result<SetWalk<'s>, VmError> {
    let receiver = scope.handle(receiver.as_tagged(heap).erase());
    let key = scope.handle(key.as_tagged(heap).erase());
    let value = scope.handle(value.as_tagged(heap).erase());
    if receiver.as_tagged(heap).is_nullish(heap) {
        return Err(VmError::Type);
    }
    // Primitive receivers are not property-store targets (ES 10.4.5.5).
    if !Proxy::is_js_receiver(heap, receiver.as_tagged(heap)) {
        return Ok(SetWalk::Rejected);
    }

    match find_holder(heap, scope, start, key.as_tagged(heap))? {
        Found::Proxy(proxy) => match Proxy::set(vm, heap, state, proxy, key, value, receiver)? {
            Coercion::Value(v) => {
                let v = scope.handle(v);
                if v.as_tagged(heap).is_truthy(heap) {
                    Ok(SetWalk::Done)
                } else {
                    Ok(SetWalk::Rejected)
                }
            }
            Coercion::Threw => Ok(SetWalk::Threw),
        },
        Found::Own { holder, property } => match property {
            OwnProperty::String(_) => Ok(SetWalk::Rejected),
            OwnProperty::Parent(_) => {
                if holder.as_tagged(heap).ptr_eq(receiver.as_tagged(heap))
                    && let Lookup::Data {
                        holder: data_holder,
                        slot,
                        ..
                    } = holder
                        .as_tagged(heap)
                        .lookup(heap, key.as_tagged(heap).as_name())
                {
                    slot.set(heap, data_holder.erase(), value.as_tagged(heap));
                    return Ok(SetWalk::Done);
                }
                Ok(SetWalk::Define { receiver, key })
            }
            OwnProperty::Descriptor(PropertyDescriptor::Accessor { set, .. }) => {
                let setter = set.as_tagged(heap);
                if setter == heap.known().undefined.get(heap).erase() {
                    Ok(SetWalk::Rejected)
                } else {
                    Ok(SetWalk::CallSetter(scope.handle(setter)))
                }
            }
            OwnProperty::Descriptor(PropertyDescriptor::Data { writable, .. }) => {
                if !writable {
                    return Ok(SetWalk::Rejected);
                }
                let name = key.as_tagged(heap).as_name();
                let is_array_length = holder
                    .as_tagged(heap)
                    .as_heap_object()
                    .is_some_and(|obj| obj.array_length(heap, name).is_some());
                if !holder.as_tagged(heap).ptr_eq(receiver.as_tagged(heap)) {
                    if WRITE_THROUGH {
                        if let Ok(Key::Element(i)) = key.as_tagged(heap).classify_key(heap)
                            && holder
                                .as_tagged(heap)
                                .as_heap_object()
                                .is_some_and(|obj| obj.is_array(heap))
                        {
                            let obj = scope
                                .cast::<Object>(heap, holder.as_tagged(heap))
                                .expect("array holder is an object");
                            Object::store_array_element(heap, scope, &obj, i, &value)?;
                            return Ok(SetWalk::Done);
                        }
                        if let Ok(Key::Name(_)) = key.as_tagged(heap).classify_key(heap)
                            && !is_array_length
                            && let Lookup::Data {
                                holder: data_holder,
                                slot,
                                ..
                            } = holder.as_tagged(heap).lookup(heap, name)
                        {
                            slot.set(heap, data_holder.erase(), value.as_tagged(heap));
                            return Ok(SetWalk::Done);
                        }
                    }
                    return Ok(SetWalk::Define { receiver, key });
                }
                if is_array_length {
                    let setter = match holder.as_tagged(heap).lookup(heap, name) {
                        Lookup::Accessor { pair, .. } => pair.set.get(heap),
                        _ => heap.known().undefined.get(heap).erase(),
                    };
                    if setter == heap.known().undefined.get(heap).erase() {
                        return Ok(SetWalk::Rejected);
                    }
                    return Ok(SetWalk::CallSetter(scope.handle(setter)));
                }
                if let Ok(Key::Element(i)) = key.as_tagged(heap).classify_key(heap)
                    && holder
                        .as_tagged(heap)
                        .as_heap_object()
                        .is_some_and(|obj| obj.is_array(heap))
                {
                    let obj = scope
                        .cast::<Object>(heap, holder.as_tagged(heap))
                        .expect("array holder is an object");
                    Object::store_array_element(heap, scope, &obj, i, &value)?;
                    return Ok(SetWalk::Done);
                }
                if let Lookup::Data {
                    holder: data_holder,
                    slot,
                    ..
                } = holder.as_tagged(heap).lookup(heap, name)
                {
                    slot.set(heap, data_holder.erase(), value.as_tagged(heap));
                    return Ok(SetWalk::Done);
                }
                Ok(SetWalk::Define { receiver, key })
            }
        },
        Found::Missing => {
            // No own property anywhere. A receiver array can take an
            // element directly; other receivers define a fresh writable
            // data property.
            if let Ok(Key::Element(i)) = key.as_tagged(heap).classify_key(heap)
                && receiver
                    .as_tagged(heap)
                    .as_heap_object()
                    .is_some_and(|obj| obj.is_array(heap))
            {
                let obj = scope
                    .cast::<Object>(heap, receiver.as_tagged(heap))
                    .expect("array receiver is an object");
                Object::store_array_element(heap, scope, &obj, i, &value)?;
                return Ok(SetWalk::Done);
            }
            Ok(SetWalk::Define { receiver, key })
        }
    }
}

/// ES `[[HasProperty]]` over the prototype chain. Proxy holders run their
/// `has` trap; ordinary/String holders report their own descriptor.
fn walk_has<'h>(
    vm: &VM,
    heap: &'h mut Heap,
    state: &ThreadState,
    scope: &HandleScope<'_>,
    start: Handle<'_, Value>,
    key: Handle<'_, Value>,
) -> Result<HasWalk, VmError> {
    match find_holder(heap, scope, start, key.as_tagged(heap))? {
        Found::Proxy(proxy) => match Proxy::has(vm, heap, state, proxy, key)? {
            Coercion::Value(v) => {
                let v = scope.handle(v);
                Ok(HasWalk::Value(v.as_tagged(heap).is_truthy(heap)))
            }
            Coercion::Threw => Ok(HasWalk::Threw),
        },
        Found::Own { .. } => Ok(HasWalk::Value(true)),
        Found::Missing => Ok(HasWalk::Value(false)),
    }
}

/// Whether an ordinary-set walk needs the full per-holder path. Plain
/// object chains keep the cheaper map-only store path; proxies, arrays,
/// String wrappers, and multi-parent links need per-holder semantics.
#[inline(never)]
pub fn chain_needs_full_set(heap: &Heap, receiver: Tagged<'_, Value>) -> bool {
    let mut cur = receiver;
    loop {
        if cur.is_nullish(heap) || cur.ptr_eq(heap.known().the_hole.get(heap).erase()) {
            return false;
        }
        let Some(obj) = cur.as_heap_object() else {
            return false;
        };
        if Proxy::is_proxy(heap, cur) {
            return true;
        }
        if obj.is_array(heap) || DenseString::from_receiver(heap, cur).is_some() {
            return true;
        }
        let proto = obj.map(heap).prototype.get(heap);
        if proto.get_as::<FixedArray>(heap).is_some() {
            return true;
        }
        let known = heap.known();
        if !proto.is_strong_ptr()
            || proto.ptr_eq(known.null.get(heap).erase())
            || proto.ptr_eq(known.the_hole.get(heap).erase())
            || proto.ptr_eq(known.undefined.get(heap).erase())
        {
            return false;
        }
        cur = proto;
    }
}

impl<'a> Tagged<'a, Value> {
    /// Lookup on any value: non-objects find nothing (ES [[Get]] walks
    /// primitives' prototypes only via the caller's coercion).
    #[inline(always)]
    pub fn lookup(self, heap: &'a Heap, name: Tagged<'a, SlotName>) -> Lookup<'a> {
        let Some(obj) = self.erase().as_heap_object() else {
            return Lookup::NotFound;
        };
        obj.lookup(heap, name)
    }
}

impl Map {
    pub fn lookup<'a>(
        &self,
        heap: &'a Heap,
        receiver: Tagged<'a, Object>,
        name: Tagged<'a, SlotName>,
    ) -> Lookup<'a> {
        for (index, d) in self.descriptors().iter().enumerate() {
            if d.name(heap).ptr_eq(name) {
                if d.flags().is_accessor() {
                    return Lookup::Accessor {
                        holder: receiver,
                        map_index: index,
                        pair: d
                            .value
                            .get(heap)
                            .get_as::<AccessorPair>(heap)
                            .expect("accessor descriptor holds an AccessorPair"),
                    };
                }
                return Lookup::Data {
                    map_index: index,
                    holder_index: d.offset(),
                    slot: receiver.slot(heap, d.offset()),
                    holder: receiver,
                    flags: d.flags(),
                };
            }
        }

        let proto = self.prototype.get(heap);
        if let Some(pairs) = proto.get_as::<FixedArray>(heap) {
            let name_word = name.erase();
            let mut i = 0;
            while i < pairs.len() {
                if pairs.at(heap, i).ptr_eq(name_word) {
                    return Lookup::Data {
                        holder: receiver,
                        map_index: i / 2,
                        holder_index: i + 1,
                        slot: pairs.as_ref().element_slot(i + 1),
                        flags: SlotFlags::VALUE,
                    };
                }
                i += 2;
            }
        }
        proto.lookup_in_parents(heap, name)
    }
}

impl Object {
    pub fn lookup<'a>(&self, heap: &'a Heap, name: Tagged<'a, SlotName>) -> Lookup<'a> {
        let receiver = Tagged::<Object>::anchored(heap, self);
        // accessor entries in a sparse receiver act like accessor
        // descriptors for the named walk
        if let Some(pair) = self.dictionary_accessor(heap, name.as_index()) {
            return Lookup::Accessor {
                holder: receiver,
                map_index: usize::MAX,
                pair,
            };
        }
        self.header.map.get(heap).lookup(heap, receiver, name)
    }

    /// The `AccessorPair` of a sparse accessor entry at `index`, when
    /// this object is a dictionary-mode array holding one.
    pub fn dictionary_accessor<'a>(
        &self,
        heap: &'a Heap,
        index: Option<usize>,
    ) -> Option<Tagged<'a, AccessorPair>> {
        let index = index?;
        let dict = self.element_dictionary(heap)?;
        let entry = dict.find(heap, index)?;
        if !dict.is_accessor_at(heap, entry) {
            return None;
        }
        dict.value_at(heap, entry).get_as::<AccessorPair>(heap)
    }
}
