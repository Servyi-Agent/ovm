// #22: only the pieces test262 does not cover (or cannot run here).
//
// test262 already asserts constructor TimeClip, Date arguments, expanded
// years, min/max range, toISOString/toJSON/getTime and component
// normalisation. Its Date.parse suite is just four files, and
// parse/year-zero.js cannot compile (for-of) while
// parse/without-utc-offset.js needs the unimplemented getTimezoneOffset.
// The rest of this file covers those gaps plus the integrality of
// Date.now(), which test262 only checks for `typeof === "number"`.

for (var i = 0; i < 8; i++) {
    var now = Date.now();
    assert.sameValue(now, Math.floor(now), "Date.now is integral");
    assert.sameValue(new Date(now).getTime(), now, "Date.now round-trips");
    var created = new Date();
    assert.sameValue(
        created.getTime(),
        Math.floor(created.getTime()),
        "new Date() is integral"
    );
}

// Adding an ordinary property transitions the instance map; [[DateValue]]
// must remain reachable.
var with_props = new Date(1234);
with_props.extra = 1;
assert.sameValue(with_props.getTime(), 1234, "slots survive map transitions");

// ISO parser corners: date-only/offsetless forms, end-of-day, offsets,
// fractional precision, fixed widths, and the expanded-year sign rule.
assert.sameValue(Date.parse("2020"), 1577836800000, "year only");
assert.sameValue(Date.parse("2020-01"), 1577836800000, "year-month");
assert.sameValue(
    Date.parse("2020-01-01T00:00:00"),
    1577836800000,
    "offsetless date-time is local (UTC)"
);
assert.sameValue(Date.parse("2020-01-01T24:00:00Z"), 1577923200000, "24:00");
assert.assert(isNaN(Date.parse("2020-01-01T24:00:01Z")), "24:00 is exclusive");
assert.sameValue(
    Date.parse("2020-01-01T00:00:00+01:30"),
    1577831400000,
    "±HH:mm offset"
);
assert.sameValue(
    Date.parse("2020-01-01T00:00:00+0130"),
    1577831400000,
    "±HHmm extension"
);
assert.sameValue(
    Date.parse("2020-01-01T00:00:00.1Z"),
    1577836800100,
    "short fraction is left-aligned"
);
assert.sameValue(
    Date.parse("2020-01-01T00:00:00.1234Z"),
    1577836800123,
    "long fraction truncates"
);
assert.sameValue(
    Date.parse("2020-01-01t00:00:00z"),
    1577836800000,
    "lowercase separator and zone"
);
assert.sameValue(
    Date.parse("2020-01-01 00:00:00Z"),
    1577836800000,
    "space separator"
);
assert.assert(isNaN(Date.parse("2020-1-1T00:00:00Z")), "fields are fixed-width");
assert.assert(isNaN(Date.parse("-000000-01-01T00:00:00Z")), "-000000 is invalid");
assert.assert(
    isNaN(Date.parse("2020-01-01T00:00:00Z ")),
    "trailing input is rejected"
);
