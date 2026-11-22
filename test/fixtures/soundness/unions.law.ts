"use verified";

// Found by the fuzzer (test/fuzz.test.ts): valid code was rejected because an expression's
// inferred type was a union, even though every member has the same model.
import { law } from "../../../src/runtime.js";

export type N = { readonly a: bigint };
export type W = { readonly a: bigint; readonly b: boolean };
export type O = { readonly n: N; readonly k: bigint };

export function pickLiteral(c: boolean): bigint {
  return c ? 5n : 2652n;
}

export function build(c: boolean, w: W, n: N): O {
  const o: O = c ? { n: w, k: 1n } : { n: { a: n.a }, k: 2n };
  return o;
}

export function nested(c: boolean, w: W, n: N): O {
  return { n: c ? w : n, k: c ? 1n : 2n };
}

law("TRUE: ternary of two bigint literals", (c: boolean) => pickLiteral(c) === (c ? 5n : 2652n));
law("FALSE: ternary of two bigint literals", (c: boolean) => pickLiteral(c) === 5n);
law("TRUE: ternary of two record shapes", (c: boolean, w: W, n: N) => build(c, w, n).n.a === (c ? w.a : n.a));
law("TRUE: ternary inside a literal field", (c: boolean, w: W, n: N) => nested(c, w, n).n.a === (c ? w.a : n.a));
law("FALSE: ternary inside a literal field", (c: boolean, w: W, n: N) => nested(c, w, n).n.a === w.a);
