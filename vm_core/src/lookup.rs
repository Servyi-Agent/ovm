use core::ptr::NonNull;

use crate::proxy::Proxy;
use crate::{
    AccessorPair, DETAILS_ACCESSOR, DETAILS_CONFIGURABLE, DETAILS_ENUMERABLE, DETAILS_WRITABLE,
    DenseString, FixedArray, GcSlot, Handle, HandleScope, Heap, Map, Object, PropertyDescriptor,
    SlotFlags, SlotName, Smi, StringOwn, Symbol, Tagged, Value, VmError,
};

pub struct Lookup;

pub enum Key<'a> {
    Element(usize),
    Name(Tagged<'a, SlotName>),
}

pub enum Found<'h> {
    MapData {
        holder: Tagged<'h, Object>,
        map_index: usize,
        offset: usize,
        slot: &'h GcSlot,
        flags: SlotFlags,
    },
    Accessor {
        holder: Tagged<'h, Object>,
        map_index: usize,
        pair: Tagged<'h, AccessorPair>,
        flags: SlotFlags,
    },
    String {
        holder: Tagged<'h, Value>,
        own: StringOwn,
    },
    Element {
        holder: Tagged<'h, Object>,
        index: usize,
        flags: SlotFlags,
    },
    ArrayLength {
        holder: Tagged<'h, Object>,
    },
    Parent {
        holder: Tagged<'h, Object>,
        index: usize,
        value: Tagged<'h, Value>,
        flags: SlotFlags,
    },
    Proxy(Tagged<'h, Value>),
    Missing,
}

pub enum LookupActionGet<'s> {
    Value(Handle<'s, Value>),
    Getter(Handle<'s, Value>),
    Missing,
    Proxy(Handle<'s, Value>),
    StringChar(u16),
}

pub enum LookupActionHas<'s> {
    Value(bool),
    Proxy(Handle<'s, Value>),
}

pub enum LookupActionSet<'s> {
    Done,
    Rejected,
    CallSetter(Handle<'s, Value>),
    Define {
        receiver: Handle<'s, Value>,
        key: Handle<'s, Value>,
    },
    Proxy {
        proxy: Handle<'s, Value>,
        key: Handle<'s, Value>,
    },
    StoreElement {
        holder: Handle<'s, Object>,
        index: usize,
    },
    WriteSlot {
        holder: Handle<'s, Object>,
        offset: usize,
    },
    WriteParent {
        holder: Handle<'s, Object>,
        index: usize,
    },
}

/// Stack-allocated identity chain for multi-parent recursion.
pub struct VisitedLink<'h> {
    value: Tagged<'h, Value>,
    prev: Option<NonNull<VisitedLink<'h>>>,
}

impl<'h> VisitedLink<'h> {
    pub fn new(value: Tagged<'h, Value>, prev: Option<&VisitedLink<'h>>) -> Self {
        Self {
            value,
            prev: prev.map(NonNull::from),
        }
    }

    pub fn contains(mut link: Option<&VisitedLink<'h>>, target: Tagged<'h, Value>) -> bool {
        while let Some(node) = link {
            if node.value == target {
                return true;
            }
            // SAFETY: every `prev` was stored by `new` from an active frame.
            link = unsafe { node.prev.map(|prev| prev.as_ref()) };
        }
        false
    }
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

    pub fn ordinary_own_descriptor<'s>(
        self,
        heap: &'a Heap,
        scope: &'s HandleScope<'_>,
        key: Tagged<'a, Value>,
    ) -> Option<PropertyDescriptor<'s>> {
        let found = find_in_chain::<true>(heap, self, key, None).ok()?;
        match found {
            Found::MapData {
                holder,
                offset,
                flags,
                ..
            } => Some(PropertyDescriptor::Data {
                value: scope.handle(holder.slot(heap, offset).get(heap)),
                writable: flags.is_writable(),
                enumerable: flags.is_enumerable(),
                configurable: flags.is_configurable(),
            }),
            Found::Accessor { pair, flags, .. } => Some(PropertyDescriptor::Accessor {
                get: scope.handle(pair.get.get(heap)),
                set: scope.handle(pair.set.get(heap)),
                enumerable: flags.is_enumerable(),
                configurable: flags.is_configurable(),
            }),
            Found::Element {
                holder,
                index,
                flags,
            } => Some(PropertyDescriptor::Data {
                value: scope.handle(holder.element_value(heap, index)?),
                writable: flags.is_writable(),
                enumerable: flags.is_enumerable(),
                configurable: flags.is_configurable(),
            }),
            Found::ArrayLength { holder } => Some(PropertyDescriptor::Data {
                value: scope.handle(holder.length.get(heap).erase()),
                writable: true,
                enumerable: false,
                configurable: false,
            }),
            Found::Parent { value, flags, .. } => Some(PropertyDescriptor::Data {
                value: scope.handle(value),
                writable: flags.is_writable(),
                enumerable: flags.is_enumerable(),
                configurable: flags.is_configurable(),
            }),
            Found::String { .. } | Found::Proxy(_) | Found::Missing => None,
        }
    }
}

impl Lookup {
    /// ES `[[Get]]` over the prototype chain with per-holder semantics.
    /// The raw lookup stops here; the caller executes the returned action.
    pub fn get<'s>(
        heap: &Heap,
        scope: &'s HandleScope<'_>,
        start: Handle<'_, Value>,
        key: Handle<'_, Value>,
    ) -> Result<LookupActionGet<'s>, VmError> {
        if start.as_tagged(heap).is_nullish(heap) {
            return Err(VmError::Type);
        }
        match find_in_chain::<false>(heap, start.as_tagged(heap), key.as_tagged(heap), None)? {
            Found::Proxy(proxy) => Ok(LookupActionGet::Proxy(scope.handle(proxy))),
            Found::MapData { slot, .. } => Ok(LookupActionGet::Value(scope.handle(slot.get(heap)))),
            Found::Accessor { pair, .. } => {
                let getter = pair.get.get(heap);
                if getter == heap.known().undefined.get(heap) {
                    Ok(LookupActionGet::Value(
                        scope.handle(heap.known().undefined.get(heap).erase()),
                    ))
                } else {
                    Ok(LookupActionGet::Getter(scope.handle(getter)))
                }
            }
            Found::String { holder, own } => match own {
                StringOwn::Length(len) => Ok(LookupActionGet::Value(
                    scope.handle(Smi::new(len as i64).into_tagged()),
                )),
                StringOwn::Index(i) => {
                    let unit = DenseString::from_receiver(heap, holder)
                        .expect("string own key from a string receiver")
                        .code_unit(heap, i);
                    Ok(LookupActionGet::StringChar(unit))
                }
            },
            Found::Element { holder, index, .. } => {
                let value = holder
                    .element_value(heap, index)
                    .expect("element own key has a value");
                Ok(LookupActionGet::Value(scope.handle(value)))
            }
            Found::Parent { value, .. } => Ok(LookupActionGet::Value(scope.handle(value))),
            Found::ArrayLength { holder } => Ok(LookupActionGet::Value(
                scope.handle(holder.length.get(heap).erase()),
            )),
            Found::Missing => Ok(LookupActionGet::Missing),
        }
    }

    /// ES `[[Set]]` over the prototype chain with the receiver split from
    /// the lookup start. Accessors and proxy traps are returned as actions.
    pub fn set<'s, const WRITE_THROUGH: bool>(
        heap: &Heap,
        scope: &'s HandleScope<'_>,
        start: Handle<'_, Value>,
        receiver: Handle<'_, Value>,
        key: Handle<'_, Value>,
    ) -> Result<LookupActionSet<'s>, VmError> {
        let receiver = scope.handle(receiver.as_tagged(heap).erase());
        let key = scope.handle(key.as_tagged(heap).erase());
        if receiver.as_tagged(heap).is_nullish(heap) {
            return Err(VmError::Type);
        }
        // Primitive receivers are not property-store targets (ES 10.4.5.5).
        if !Proxy::is_js_receiver(heap, receiver.as_tagged(heap)) {
            return Ok(LookupActionSet::Rejected);
        }

        match find_in_chain::<false>(heap, start.as_tagged(heap), key.as_tagged(heap), None)? {
            Found::Proxy(proxy) => Ok(LookupActionSet::Proxy {
                proxy: scope.handle(proxy),
                key,
            }),
            Found::String { .. } => Ok(LookupActionSet::Rejected),
            Found::Parent {
                holder,
                index,
                value: _,
                ..
            } => {
                if holder.erase().ptr_eq(receiver.as_tagged(heap)) {
                    return Ok(LookupActionSet::WriteParent {
                        holder: scope.handle(holder),
                        index,
                    });
                }
                Ok(LookupActionSet::Define { receiver, key })
            }
            Found::Accessor { pair, .. } => {
                let setter = pair.set.get(heap);
                if setter == heap.known().undefined.get(heap).erase() {
                    Ok(LookupActionSet::Rejected)
                } else {
                    Ok(LookupActionSet::CallSetter(scope.handle(setter)))
                }
            }
            Found::MapData {
                holder,
                offset,
                flags,
                ..
            } => {
                if !flags.is_writable() {
                    return Ok(LookupActionSet::Rejected);
                }
                if !holder.erase().ptr_eq(receiver.as_tagged(heap)) && !WRITE_THROUGH {
                    return Ok(LookupActionSet::Define { receiver, key });
                }
                if let Ok(Key::Element(i)) = key.as_tagged(heap).classify_key(heap)
                    && holder.is_array(heap)
                {
                    return Ok(LookupActionSet::StoreElement {
                        holder: scope.handle(holder),
                        index: i,
                    });
                }
                Ok(LookupActionSet::WriteSlot {
                    holder: scope.handle(holder),
                    offset,
                })
            }
            Found::Element {
                holder,
                index,
                flags,
            } => {
                if !flags.is_writable() {
                    return Ok(LookupActionSet::Rejected);
                }
                if !holder.erase().ptr_eq(receiver.as_tagged(heap)) && !WRITE_THROUGH {
                    return Ok(LookupActionSet::Define { receiver, key });
                }
                Ok(LookupActionSet::StoreElement {
                    holder: scope.handle(holder),
                    index,
                })
            }
            Found::ArrayLength { holder } => {
                if !holder.erase().ptr_eq(receiver.as_tagged(heap)) {
                    return Ok(LookupActionSet::Define { receiver, key });
                }
                let name = key.as_tagged(heap).as_name();
                let setter = match holder.lookup(heap, name) {
                    Found::Accessor { pair, .. } => pair.set.get(heap),
                    _ => heap.known().undefined.get(heap).erase(),
                };
                if setter == heap.known().undefined.get(heap).erase() {
                    return Ok(LookupActionSet::Rejected);
                }
                Ok(LookupActionSet::CallSetter(scope.handle(setter)))
            }
            Found::Missing => {
                if let Ok(Key::Element(i)) = key.as_tagged(heap).classify_key(heap)
                    && receiver
                        .as_tagged(heap)
                        .as_heap_object()
                        .is_some_and(|obj| obj.is_array(heap))
                {
                    let holder = scope
                        .cast::<Object>(heap, receiver.as_tagged(heap))
                        .expect("array receiver is an object");
                    return Ok(LookupActionSet::StoreElement { holder, index: i });
                }
                Ok(LookupActionSet::Define { receiver, key })
            }
        }
    }

    pub fn has<'s>(
        heap: &Heap,
        scope: &'s HandleScope<'_>,
        start: Handle<'_, Value>,
        key: Handle<'_, Value>,
    ) -> Result<LookupActionHas<'s>, VmError> {
        if start.as_tagged(heap).is_nullish(heap) {
            return Err(VmError::Type);
        }
        match find_in_chain::<false>(heap, start.as_tagged(heap), key.as_tagged(heap), None)? {
            Found::Proxy(proxy) => Ok(LookupActionHas::Proxy(scope.handle(proxy))),
            Found::Missing => Ok(LookupActionHas::Value(false)),
            _ => Ok(LookupActionHas::Value(true)),
        }
    }
}

pub fn find_in_chain<'h, const OWN_ONLY: bool>(
    heap: &'h Heap,
    start: Tagged<'h, Value>,
    key: Tagged<'h, Value>,
    visited: Option<&VisitedLink<'h>>,
) -> Result<Found<'h>, VmError> {
    if let Some(pairs) = start.get_as::<FixedArray>(heap) {
        if OWN_ONLY {
            return Ok(Found::Missing);
        }
        let list = pairs.erase();
        // A parent list may only be entered once
        if VisitedLink::contains(visited, list) {
            return Ok(Found::Missing);
        }
        let list_link = VisitedLink::new(list, visited);

        let mut i = 1;
        while i < pairs.len() {
            let parent = pairs.at(heap, i);
            i += 2;
            if parent.is_nullish(heap)
                || parent.ptr_eq(heap.known().the_hole.get(heap).erase())
                || parent.as_heap_object().is_none()
            {
                continue;
            }
            if parent.get_as::<FixedArray>(heap).is_some() {
                // Entering the nested list adds it to the visited chain.
                let found = find_in_chain::<false>(heap, parent, key, Some(&list_link))?;
                if !matches!(found, Found::Missing) {
                    return Ok(found);
                }
                continue;
            }
            if VisitedLink::contains(Some(&list_link), parent) {
                continue;
            }
            let parent_link = VisitedLink::new(parent, Some(&list_link));
            let found = find_in_chain::<false>(heap, parent, key, Some(&parent_link))?;
            if !matches!(found, Found::Missing) {
                return Ok(found);
            }
        }
        return Ok(Found::Missing);
    }

    let name = key.as_name();
    let mut holder = start;
    loop {
        if holder.is_nullish(heap) || holder.ptr_eq(heap.known().the_hole.get(heap).erase()) {
            return Ok(Found::Missing);
        }
        if Proxy::is_proxy(heap, holder) {
            return Ok(Found::Proxy(holder));
        }
        if let Some(string) =
            DenseString::from_receiver(heap, holder).and_then(|s| s.own_key(heap, name))
        {
            return Ok(Found::String {
                holder,
                own: string,
            });
        }
        if let Some(o) = holder.as_heap_object() {
            if let Ok(Key::Element(i)) = key.classify_key(heap) {
                if let Some(dict) = o.element_dictionary(heap)
                    && let Some(entry) = dict.find(heap, i)
                {
                    let details = dict.details_at(heap, entry);
                    let mut flags = SlotFlags::VALUE;
                    if details & DETAILS_WRITABLE != 0 {
                        flags = flags.union(SlotFlags::WRITABLE);
                    }
                    if details & DETAILS_ENUMERABLE != 0 {
                        flags = flags.union(SlotFlags::ENUMERABLE);
                    }
                    if details & DETAILS_CONFIGURABLE != 0 {
                        flags = flags.union(SlotFlags::CONFIGURABLE);
                    }
                    if details & DETAILS_ACCESSOR != 0 {
                        flags = flags.union(SlotFlags::ACCESSOR);
                        let Some(pair) = dict.value_at(heap, entry).get_as::<AccessorPair>(heap)
                        else {
                            return Ok(Found::Missing);
                        };
                        return Ok(Found::Accessor {
                            holder: o,
                            map_index: usize::MAX,
                            pair,
                            flags,
                        });
                    }
                    return Ok(Found::Element {
                        holder: o,
                        index: i,
                        flags,
                    });
                }
                if o.element_value(heap, i).is_some() {
                    return Ok(Found::Element {
                        holder: o,
                        index: i,
                        flags: SlotFlags::new(
                            SlotFlags::WRITABLE.bits()
                                | SlotFlags::ENUMERABLE.bits()
                                | SlotFlags::CONFIGURABLE.bits(),
                        ),
                    });
                }
            }
            if o.array_length(heap, name).is_some() {
                return Ok(Found::ArrayLength { holder: o });
            }
            let map = o.map(heap);
            for (index, d) in map.descriptors().iter().enumerate() {
                if !d.name(heap).ptr_eq(name) {
                    continue;
                }
                if d.flags().is_accessor() {
                    let pair = d
                        .value
                        .get(heap)
                        .get_as::<AccessorPair>(heap)
                        .expect("accessor descriptor holds a pair");
                    return Ok(Found::Accessor {
                        holder: o,
                        map_index: index,
                        pair,
                        flags: d.flags(),
                    });
                }
                return Ok(Found::MapData {
                    holder: o,
                    map_index: index,
                    offset: d.offset(),
                    slot: o.slot(heap, d.offset()),
                    flags: d.flags(),
                });
            }
            if let Some((index, value)) = parent_name(heap, holder, name) {
                return Ok(Found::Parent {
                    holder: o,
                    index,
                    value,
                    flags: SlotFlags::VALUE,
                });
            }
        }

        if OWN_ONLY {
            return Ok(Found::Missing);
        }

        let next = if let Some(proto) = holder.primitive_prototype(heap) {
            proto
        } else {
            let Some(obj) = holder.as_heap_object() else {
                return Ok(Found::Missing);
            };
            obj.prototype(heap)
        };
        if next.get_as::<FixedArray>(heap).is_some() {
            return find_in_chain::<false>(heap, next, key, visited);
        }
        holder = next;
    }
}

/// Self-style parent-name slot stored in the map's parent pairs.
fn parent_name<'a>(
    heap: &'a Heap,
    holder: Tagged<'a, Value>,
    name: Tagged<'a, SlotName>,
) -> Option<(usize, Tagged<'a, Value>)> {
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
                        return Some((i + 1, pairs.at(heap, i + 1)));
                    }
                    i += 2;
                }
                None
            })
    })
}

impl Map {
    pub fn lookup<'a>(
        &self,
        heap: &'a Heap,
        receiver: Tagged<'a, Object>,
        name: Tagged<'a, SlotName>,
    ) -> Found<'a> {
        for (index, d) in self.descriptors().iter().enumerate() {
            if d.name(heap).ptr_eq(name) {
                if d.flags().is_accessor() {
                    return Found::Accessor {
                        holder: receiver,
                        map_index: index,
                        pair: d
                            .value
                            .get(heap)
                            .get_as::<AccessorPair>(heap)
                            .expect("accessor descriptor holds an AccessorPair"),
                        flags: d.flags(),
                    };
                }
                return Found::MapData {
                    map_index: index,
                    offset: d.offset(),
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
                    return Found::MapData {
                        holder: receiver,
                        map_index: i / 2,
                        offset: i + 1,
                        slot: pairs.as_ref().element_slot(i + 1),
                        flags: SlotFlags::VALUE,
                    };
                }
                i += 2;
            }
        }
        if proto == heap.known().null.get(heap) {
            return Found::Missing;
        }
        if let Some(pairs) = proto.get_as::<FixedArray>(heap) {
            let mut i = 1;
            while i < pairs.len() {
                let result = pairs.at(heap, i).lookup(heap, name);
                if !matches!(result, Found::Missing) {
                    return result;
                }
                i += 2;
            }
            return Found::Missing;
        }
        proto.lookup(heap, name)
    }
}

impl<'a> Tagged<'a, Value> {
    #[inline(always)]
    pub fn lookup(self, heap: &'a Heap, name: Tagged<'a, SlotName>) -> Found<'a> {
        let Some(obj) = self.erase().as_heap_object() else {
            return Found::Missing;
        };
        obj.lookup(heap, name)
    }
}

impl Object {
    pub fn lookup<'a>(&self, heap: &'a Heap, name: Tagged<'a, SlotName>) -> Found<'a> {
        let receiver = Tagged::<Object>::anchored(heap, self);

        if let Some(pair) = self.dictionary_accessor(heap, name.as_index()) {
            return Found::Accessor {
                holder: receiver,
                map_index: usize::MAX,
                pair,
                flags: SlotFlags::ACCESSOR,
            };
        }
        self.header.map.get(heap).lookup(heap, receiver, name)
    }

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
