# Safety
never use unsafe unless explicetely allowed, if you think unsafe is solving a problem or helps maximizing performance, always ask before.

## GC Safety
`Tagged<'h, T>` takes `h` to statically proof no directly borrowed value to the heap is crossing a gc safepoint.
purpesfully violating this by passing around plain `Value` or `Word` and using `unsafe` destroys this proof and may kill values across gc-safepoints if the heap moves the value.

# Code Conventions
## Visibility
Never use `pub(crate)` — always plain `pub`. If something should not be
re-exported at the crate root, simply do not re-export it; the module
path already scopes it.

## Method vs namespace function

Can the function trigger a GC (does it need `&mut Heap`, or take `Handle`s because it allocates)?

- **No GC** (only `&Heap` or nothing besides the receiver): make it a method.
  `obj.map(heap)`, `v.is_truthy(heap)`, `key.classify_key(heap)`
- **Can GC**: keep it a namespace function. `heap` always comes first, then the
  objects it operates on.
  `Transition::define_own_property(heap, scope, receiver, name, desc)`,
  `Convert::to_string(heap, scope, v)`

Cross-cutting notifications keep their domain namespace even when GC-free
(e.g. `Prototype::shape_changed(heap, map)` — it notifies the prototype
registry, it is not an operation on the map).

Only `Tagged` auto-derefs to its pointee. `Handle` has no `Deref` on purpose: a
`&self` behind a handle deref could dangle once the GC moves the object, so
GC-able operations take handles explicitly.

## Test PRs: prove the tests can fail (negative control)

Every test-only or test-adding PR must include a **fault-injection
check (CI-enforced by the `negative-control` gate): inject a
production fault the OLD tests miss; the new tests must go red while
every existing test stays green.** Declare the fault branches in the
PR body under a `Negative Control:` fenced block — the gate verifies
the branches are test-identical to the PR and that every touched test
FAILS on at least one of them. A touched test that fails in its own
LAST touching commit is its own negative control (the test-first RED
commit satisfies the gate without branches).

Test files = anything under a `tests/` directory:
- `<crate>/tests/<name>.rs` runs as `cargo test -p <crate> --test <name>`
- `tests/regression/**.js` runs via `cargo run -p vm --example regression -- <file>`

Rules: a declared branch must be test-identical to the PR head (any
test diff rejects); a missing branch or a non-building branch rejects
(a broken control proves nothing); deletions are exempt; no
declaration + uncaught touched tests rejects.
