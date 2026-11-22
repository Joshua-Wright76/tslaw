"use verified";

// Bug: SMT names were built by replacing non-alphanumerics with `_`, so `a$b` and `a_b`
// collided. Z3 accepts duplicate define-fun parameter names and binds the last one, so
// `first` was modeled as returning its *second* argument.
import { law } from "../../../src/runtime.js";

export type R = { readonly a$b: bigint; readonly a_b: bigint };

export function first(a$b: bigint, a_b: bigint): bigint {
  return a$b;
}

export function pick(r: R): bigint {
  return r.a$b;
}

law("FALSE: first returns its second argument", (x: bigint, y: bigint) => first(x, y) === y);
law("TRUE: first returns its first argument", (x: bigint, y: bigint) => first(x, y) === x);
law("FALSE: pick reads the a_b field", (r: R) => pick(r) === r.a_b);
law("TRUE: pick reads the a$b field", (r: R) => pick(r) === r.a$b);
law("FALSE: distinct law args are equal", (x$: bigint, x_: bigint) => x$ === x_);
