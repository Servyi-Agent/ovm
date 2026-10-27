// #2: numeric property keys canonicalize through ToPropertyKey.
// Negative and out-of-index numbers become strings; canonical array
// indices stay index keys; JS NumberToString decides the spelling.

var negative = {};
Object.defineProperty(negative, -20, { value: 1 });
assert.assert(negative.hasOwnProperty("-20"), "negative number key is a string");
assert.sameValue(negative["-20"], 1, "negative key reads back by string");
assert.sameValue(negative[-20], 1, "negative key reads back by number");

var large = {};
Object.defineProperty(large, 1e21, { value: 2 });
assert.assert(large.hasOwnProperty("1e+21"), "1e21 uses exponential spelling");
assert.sameValue(large[1e21], 2, "1e21 reads back");

var small = {};
Object.defineProperty(small, 1e-7, { value: 3 });
assert.assert(small.hasOwnProperty("1e-7"), "1e-7 uses exponential spelling");
assert.sameValue(small[1e-7], 3, "1e-7 reads back");

var zero = {};
Object.defineProperty(zero, -0, { value: 4 });
assert.assert(zero.hasOwnProperty("0"), "-0 canonicalizes to 0");
assert.sameValue(zero[0], 4, "0 reads back");

var array = [];
Object.defineProperty(array, 4294967295, { value: 100 });
assert.sameValue(array.length, 0, "2^32-1 is not an array index");
assert.assert(array.hasOwnProperty("4294967295"), "boundary key is a string");
assert.sameValue(array[4294967295], 100, "boundary key reads back");

var seen;
var proxy = new Proxy({}, {
    get: function (target, key) {
        seen = key;
        return 5;
    },
});
assert.sameValue(proxy[10], 5, "numeric proxy get");
assert.sameValue(seen, "10", "proxy get key is a string");
assert.sameValue(proxy[-1], 5, "negative numeric proxy get");
assert.sameValue(seen, "-1", "negative proxy get key is a string");
