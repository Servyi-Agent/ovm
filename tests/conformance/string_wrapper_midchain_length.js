// ES 10.4.3: a String wrapper's `length` is an own property, found by
// OrdinaryGet when the wrapper sits mid-chain.
var o = { __proto__: Object("ab") };
if (o.length !== 2) {
    throw new TypeError("mid-chain string wrapper length: expected 2, got " + o.length);
}
