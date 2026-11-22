"use verified";

import { append, at, decreases, invariant, law, len, slice } from "../../../src/runtime.js";

export type Wide = { readonly a: bigint; readonly b: bigint };
export type Narrow = { readonly a: bigint };

// TypeScript picks `Narrow` for the element type of this call, although the first argument
// is written as an array of `Wide`.
export function mixedAppend(w: Wide, n: Narrow): bigint {
  return len(append([w], n));
}

law("TRUE: mixedAppend", (w: Wide, n: Narrow) => mixedAppend(w, n) === 2n);

// `slice(xs, 2n, 1n)` always throws. Whatever the model says its length is, a law about it
// must not be PROVED.
export function backwards(xs: readonly bigint[]): readonly bigint[] {
  return slice(xs, 2n, 1n);
}

law("FALSE: backwards is empty", (xs: readonly bigint[]) => len(backwards(xs)) === 0n);

// The invariant is false on entry, so the model says nothing about this loop; the law is
// true at runtime, but neither PROVED nor DISPROVED may be reported for it.
export function badEntry(n: bigint): bigint {
  let i = 0n;
  while (i < n) {
    invariant(n > 100n);
    decreases(n - i);
    i += 1n;
  }
  return i;
}

law("UNDECIDED: badEntry(1) is 1", () => badEntry(1n) === 1n);

// A helper whose own body reads out of range poisons the laws that use it.
export function firstOrZero(xs: readonly bigint[]): bigint {
  return at(xs, 0n) * 0n;
}

export function count(n: bigint): bigint {
  decreases(n);
  return n <= 0n ? 0n : count(n - 1n) + 1n;
}

law("FALSE: firstOrZero is zero", (xs: readonly bigint[]) => firstOrZero(xs) === 0n);
law("TRUE: count of three", () => count(3n) === 3n);
