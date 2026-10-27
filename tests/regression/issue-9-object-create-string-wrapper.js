// #9: Object.create accepts a String wrapper as [[Prototype]], and the
// wrapper's virtual own properties remain visible through the chain.

var wrapper = Object("ab");
var object = Object.create(wrapper);

assert.sameValue(Object.getPrototypeOf(object), wrapper, "wrapper is the prototype");
assert.sameValue(object.length, 2, "inherited length");
assert.sameValue(object[0], "a", "inherited index 0");
assert.sameValue(object[1], "b", "inherited index 1");
assert.sameValue(object[2], undefined, "out-of-range inherited index");

// ToObject boxing for the other primitive wrapper kinds.
assert.sameValue(Object(5).valueOf(), 5, "Number wrapper valueOf");
assert.sameValue(Object(true).valueOf(), true, "Boolean wrapper valueOf");
assert.sameValue(Object().toString(), "[object Object]", "Object() is ordinary");
assert.sameValue(Object(null).toString(), "[object Object]", "Object(null) is ordinary");
