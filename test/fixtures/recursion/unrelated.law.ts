"use verified";

import { decreases, ensures, law } from "../../../src/runtime.js";

// Both functions always return 0, and neither calls the other.
export function g(n: bigint): bigint {
  decreases(n);
  return n <= 0n ? 0n : g(n - 1n) * 0n;
}

export function h(n: bigint): bigint {
  decreases(n);
  return n <= 0n ? 0n : h(n - 1n) * 0n;
}

// Each false postcondition is about the other function. If proving one could assume the
// other, both would go through, and after that anything would (found by red-teaming).
ensures(g, (n, _r) => h(n) === 1n);
ensures(h, (n, _r) => g(n) === 1n);
law("FALSE: h is one", (n: bigint) => h(n) === 1n);
law("FALSE: zero is one", () => g(0n) === 1n);

// With `g(n) === 0n` wrongly "refuted", this would look terminating.
export function spin(n: bigint): bigint {
  decreases(n);
  return g(n) === 0n ? spin(n) + 1n : 0n;
}

law("FALSE: spin returns", () => spin(0n) === spin(0n) + 1n);

// The same shape with loops instead of recursion.
export function a(n: bigint): bigint {
  let i = 0n;
  while (i < n && i < 3n) {
    decreases(3n - i);
    i = i + 1n;
  }
  return i - i;
}

export function b(n: bigint): bigint {
  let i = 0n;
  while (i < n && i < 3n) {
    decreases(3n - i);
    i = i + 1n;
  }
  return i - i;
}

ensures(a, (n, _r) => b(n) === 1n);
ensures(b, (n, _r) => a(n) === 1n);
law("FALSE: a is one", (n: bigint) => a(n) === 1n);
