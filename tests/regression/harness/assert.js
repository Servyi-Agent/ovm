// Minimal test262-style harness for the local regression suite.
//
// The runner prepends this file to every test. Only the pieces the local
// tests need are implemented; `Object.is` is intentionally not used because
// the VM does not implement it yet.

function __sameValue(a, b) {
    if (a === b) {
        return a !== 0 || 1 / a === 1 / b;
    }
    return a !== a && b !== b;
}

var assert = {
    sameValue: function (actual, expected, message) {
        if (!__sameValue(actual, expected)) {
            throw new Error(
                (message || "sameValue") +
                    ": expected " + expected + ", got " + actual
            );
        }
    },

    notSameValue: function (actual, unexpected, message) {
        if (__sameValue(actual, unexpected)) {
            throw new Error(
                (message || "notSameValue") + ": did not expect " + unexpected
            );
        }
    },

    assert: function (condition, message) {
        if (!condition) {
            throw new Error(message || "assertion failed");
        }
    },

    throws: function (expected, fn, message) {
        var threw = false;
        var caught;
        try {
            fn();
        } catch (e) {
            threw = true;
            caught = e;
        }
        if (!threw) {
            throw new Error((message || "throws") + ": did not throw");
        }
        if (expected && !(caught instanceof expected)) {
            throw new Error(
                (message || "throws") + ": wrong exception type: " + caught
            );
        }
    }
};
