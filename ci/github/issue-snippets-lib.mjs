// Pure pieces of the issue-snippet harness, extracted for testing.

export const LANGS = new Set(["", "js", "javascript", "kette"]);
// `js` and `javascript` are the same language; the repo's issues tag
// code with ```js.
export const LANG_JS_ALIASES = new Set(["js", "javascript", ""]);

export const NOT_A_TEST = /^NOT\s+A\s+TEST/;

export function firstLine(text) {
    return text.split("\n")[0] ?? "";
}

export function isNotATest(snippet) {
    return NOT_A_TEST.test(firstLine(snippet.text));
}

export function snippetsFrom(body) {
    const out = [];
    const lines = body.split(/\r?\n/);
    // Tri-state: null = outside any fence, "ignore" = inside a fence
    // we do not collect (e.g. ```rust — its CLOSING fence must not be
    // mistaken for an untagged opening fence), otherwise the tag.
    let state = null;
    let buf = [];
    for (const line of lines) {
        if (state === null) {
            const m = line.match(/^```(.*)$/);
            if (m) {
                const info = m[1].trim();
                const tag = info.split(/\s+/)[0] ?? "";
                state = LANGS.has(tag) ? tag : "ignore";
                buf = [];
            }
        } else if (/^```/.test(line)) {
            if (state !== "ignore") out.push({ lang: state, text: buf.join("\n") });
            state = null;
        } else if (state !== "ignore") {
            buf.push(line.replace(/\r$/, ""));
        }
    }
    return out;
}
