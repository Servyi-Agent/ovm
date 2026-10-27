// #15: ToString(-0) is "0" in every stringification path, including
// property keys.

assert.sameValue(String(-0), "0", "String(-0)");
assert.sameValue((-0).toString(), "0", "Number.prototype.toString(-0)");

var object = {};
object[-0] = 1;
assert.assert(object.hasOwnProperty("0"), "-0 property key is 0");
assert.sameValue(object[0], 1, "0 property reads back");

assert.sameValue(Object.is(-0, 0), false, "Object.is distinguishes -0 and 0");
assert.sameValue(Object.is(NaN, NaN), true, "Object.is treats NaN as equal");
assert.sameValue(Object.is("x", "x"), true, "Object.is compares strings by value");
