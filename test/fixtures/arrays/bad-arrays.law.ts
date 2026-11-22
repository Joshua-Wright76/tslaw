"use verified";

import { at, law, len, slice, withAt } from "../../../src/runtime.js";

export type Wide = { readonly a: bigint; readonly b: bigint };
export type Narrow = { readonly a: bigint };

// Reads past the end when the array is empty.
export function head(xs: readonly bigint[]): bigint {
  return at(xs, 0n);
}

// Off by one: `len(xs)` is not a valid index.
export function last(xs: readonly bigint[]): bigint {
  return len(xs) > 0n ? at(xs, len(xs)) : 0n;
}

export function badSlice(xs: readonly bigint[], n: bigint): bigint {
  return len(slice(xs, n, len(xs)));
}

export function badUpdate(xs: readonly bigint[], i: bigint): bigint {
  return len(withAt(xs, i, 0n));
}

law("laws may use arrays", (xs: readonly bigint[]) => len(xs) >= 0n);
