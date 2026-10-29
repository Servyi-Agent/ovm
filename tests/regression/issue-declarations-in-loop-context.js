// Declaration stores must reach the context that hosts the binding, even
// when an enclosing for-head / class context is currently pushed.
//
// Regression: `var d = 10` inside `for (let i = ...)` was stored into the
// for-head context at depth 0, clobbering `i`; `d` stayed undefined.

// Direct eval forces both the function context and the for-head context to
// exist at the same time.
eval("");
var seen = "";
for (let i = 0; i < 3; i++) {
    var d = 10;
    seen += i;
}
assert.sameValue(seen, "012", "loop head survives a var declaration");
assert.sameValue(d, 10, "var declaration reaches the function context");

// The same collision without eval: captured head + captured var.
function captured() {
    var values = "";
    for (let i = 0; i < 3; i++) {
        var e = i;
        (function () {
            return i + e;
        })();
        values += i;
    }
    return [values, e];
}
var captured_result = captured();
assert.sameValue(captured_result[0], "012", "captured loop head survives");
assert.sameValue(captured_result[1], 2, "captured var reaches its slot");

// A var declared in an inner loop initializer must not clobber the outer
// loop head's context slot.
function nestedInit() {
    var values = [];
    for (let i = 0; i < 2; i++) {
        for (var j = 0; j < 2; j++) {
            values.push(i + ":" + j);
        }
    }
    return values.join(",");
}
assert.sameValue(
    nestedInit(),
    "0:0,0:1,1:0,1:1",
    "inner var initializer keeps the outer loop head intact"
);

// Catch parameters and class declarations use the same declaration-store
// path and must also target the right context.
function catchParam() {
    var values = "";
    for (let i = 0; i < 2; i++) {
        try {
            throw i;
        } catch (e) {
            values += e;
        }
    }
    return values;
}
assert.sameValue(catchParam(), "01", "catch parameter reaches its slot");

function classDecl() {
    var values = "";
    for (let i = 0; i < 2; i++) {
        class C {
            value() {
                return i;
            }
        }
        values += new C().value();
    }
    return values;
}
assert.sameValue(classDecl(), "01", "class declaration reaches its slot");
