// super reads start at the method's [[HomeObject]] prototype, not at the
// method receiver.

class Base {
    get value() {
        return 7;
    }

    method() {
        return 11;
    }
}

class Derived extends Base {
    readValue() {
        return super.value;
    }

    callBase() {
        return super.method();
    }
}

var object = new Derived();
assert.sameValue(object.readValue(), 7, "super getter uses home prototype");
assert.sameValue(object.callBase(), 11, "super method call uses home prototype");

// super assignment must not overwrite a non-writable own receiver property.
class Target {}
class Setter extends Target {
    write() {
        super.value = 2;
    }
}

var target = new Setter();
Object.defineProperty(target, "value", {
    configurable: true,
    writable: false,
    value: 1,
});
assert.throws(TypeError, function () {
    target.write();
}, "super set rejects a non-writable own receiver property");
assert.sameValue(target.value, 1, "non-writable receiver property is unchanged");
