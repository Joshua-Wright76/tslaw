"use verified";

import { decreases, ensures, invariant, law, requires } from "../../../src/runtime.js";

// The measure does not shrink: `i` is never changed.
export function stuck(n: bigint): bigint {
  let i = 0n;
  let acc = 0n;
  while (i < n) {
    decreases(n - i);
    acc = acc + 1n;
  }
  return acc;
}

law("FALSE: stuck returns anything", (n: bigint) => stuck(n) === 0n && stuck(n) === 1n);

// The invariant is false on entry.
export function wrongEntry(n: bigint): bigint {
  let i = 1n;
  while (i < n) {
    invariant(i === 0n);
    decreases(n - i);
    i = i + 1n;
  }
  return i;
}

// The invariant holds on entry but the body breaks it.
export function notKept(n: bigint): bigint {
  requires(n >= 0n);
  let i = 0n;
  while (i < n) {
    invariant(i === 0n);
    decreases(n - i);
    i = i + 1n;
  }
  return i;
}

// It claims what the broken invariant would give after the loop.
ensures(notKept, (_n, result) => result === 0n);
law("FALSE: notKept is zero", (n: bigint) => n < 0n || notKept(n) === 0n);

// Without an invariant nothing is known after the loop except that its condition is false.
export function count(n: bigint): bigint {
  requires(n >= 0n);
  let i = 0n;
  while (i < n) {
    decreases(n - i);
    i = i + 1n;
  }
  return i;
}

ensures(count, (n, result) => result >= n);
ensures(count, (n, result) => result === n);

// After `while (true)` the negated condition is `false`, from which anything would follow.
// Nothing may be concluded, because the loop never gets there.
export function forever(x: bigint): bigint {
  let y = x;
  while (true) {
    decreases(0n);
    y = y + 1n;
  }
  return y;
}

ensures(forever, (_x, result) => result < result);
law("FALSE: forever is below itself", (x: bigint) => forever(x) < forever(x));
