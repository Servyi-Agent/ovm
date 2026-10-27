// #10: [[HasProperty]] and [[Set]] must dispatch through a proxy anywhere
// in the prototype chain, with the original receiver and string keys.

var hasTarget = {};
var hasKey;
var hasProxy = new Proxy(hasTarget, {
    has: function (target, key) {
        hasKey = key;
        return false;
    },
});
var hasChild = Object.create(hasProxy);
assert.sameValue("prop" in hasChild, false, "mid-chain has trap result");
assert.sameValue(hasKey, "prop", "has trap key");

var indexProxy = new Proxy(Object.create([14]), {
    has: function (target, key) {
        hasKey = key;
        return false;
    },
});
var array = [];
Object.setPrototypeOf(array, indexProxy);
assert.sameValue(1 in array, false, "mid-chain has trap on array");
assert.sameValue(hasKey, "1", "index has trap key is a string");

var setTarget = {};
var setKey;
var setValue;
var setReceiver;
var setProxy = new Proxy(setTarget, {
    set: function (target, key, value, receiver) {
        setKey = key;
        setValue = value;
        setReceiver = receiver;
        return true;
    },
});
var setChild = Object.create(setProxy);
setChild.prop = "value";
assert.sameValue(setKey, "prop", "set trap key");
assert.sameValue(setValue, "value", "set trap value");
assert.sameValue(setReceiver, setChild, "set trap receiver");

var holey = new Array(1);
Object.setPrototypeOf(holey, setProxy);
holey[0] = 9;
assert.sameValue(setKey, "0", "index set trap key is a string");
assert.sameValue(setValue, 9, "index set trap value");
assert.sameValue(setReceiver, holey, "index set trap receiver");
