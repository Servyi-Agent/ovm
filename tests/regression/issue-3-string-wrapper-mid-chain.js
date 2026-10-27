// #3: a String wrapper's virtual own properties (`length` and in-range
// indices) are visible when the wrapper is anywhere in the prototype chain.

var wrapper = new String("ab");

var object = Object.create(wrapper);
assert.sameValue(object.length, 2, "Object.create(wrapper).length");
assert.sameValue(object[0], "a", "inherited index 0");
assert.sameValue(object[1], "b", "inherited index 1");
assert.sameValue(object[2], undefined, "out-of-range index");

var literal = { __proto__: wrapper };
assert.sameValue(literal.length, 2, "literal prototype wrapper length");
assert.sameValue(literal[0], "a", "literal inherited index 0");
assert.sameValue(literal[1], "b", "literal inherited index 1");

// The issue's original spelling: Object(primitive) boxes a String wrapper.
var boxed = Object("ab");
var fromObject = Object.create(boxed);
assert.sameValue(fromObject.length, 2, "Object('ab') inherited length");
assert.sameValue(fromObject[1], "b", "Object('ab') inherited index");
assert.sameValue(
    { __proto__: Object("ab") }.length,
    2,
    "literal prototype Object('ab') length"
);

// An own property on the child still shadows the wrapper's virtual one.
Object.defineProperty(literal, "length", {
    value: 7,
    writable: true,
    enumerable: true,
    configurable: true,
});
assert.sameValue(literal.length, 7, "own length shadows the wrapper");
assert.sameValue(wrapper.length, 2, "wrapper length is unchanged");
