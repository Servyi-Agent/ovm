// #1: an Array's `length` is an own property at every position in the
// prototype chain, not only when the array is the receiver.

var array = [1, 2, 3];

var object = Object.create(array);
assert.sameValue(object.length, 3, "Object.create(array).length");

var literal = { __proto__: array };
assert.sameValue(literal.length, 3, "literal prototype array length");

// The value observed through the chain must follow the array itself.
array.push(4);
assert.sameValue(object.length, 4, "length after push");
assert.sameValue(literal.length, 4, "literal length after push");

array.length = 1;
assert.sameValue(object.length, 1, "length after truncation");
assert.sameValue(literal.length, 1, "literal length after truncation");
