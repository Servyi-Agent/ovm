// #10: a proxy anywhere in the prototype chain intercepts [[Get]] with its
// `get` trap, using the original receiver.

var log = [];
var target = { x: 1 };
var proxy = new Proxy(target, {
    get: function (t, key, receiver) {
        log.push(key);
        log.push(receiver);
        return 42;
    },
});

var object = Object.create(proxy);
assert.sameValue(object.x, 42, "mid-chain get trap result");
assert.sameValue(log.length, 2, "trap called once");
assert.sameValue(log[0], "x", "trap key");
assert.sameValue(log[1], object, "trap receiver is the original object");

// A missing trap forwards to the target, including a proxy target.
var plain = new Proxy({ y: 2 }, {});
var child = Object.create(plain);
assert.sameValue(child.y, 2, "missing trap forwards to target");

// The trap is consulted on every lookup, not cached as a data field.
var calls = 0;
var dynamic = new Proxy({}, {
    get: function () {
        calls = calls + 1;
        return calls;
    },
});
var dynamicChild = Object.create(dynamic);
assert.sameValue(dynamicChild.x, 1, "dynamic trap call 1");
assert.sameValue(dynamicChild.x, 2, "dynamic trap call 2");
