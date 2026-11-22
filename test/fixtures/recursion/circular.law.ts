"use verified";

import { decreases, ensures, law, requires } from "../../../src/runtime.js";

// Both functions always return 0.
export function low(n: bigint): bigint {
  decreases(n);
  return n <= 0n ? 0n : low(n - 1n);
}

export function high(n: bigint): bigint {
  decreases(n);
  return n <= 0n ? low(n) : high(n - 1n);
}

// Two false postconditions that would prove each other if `low`'s could assume `high`'s
// (`high` calls `low`, so `high`'s may assume `low`'s, but not the other way round).
ensures(low, (n, _result) => high(n) < 0n);
ensures(high, (_n, result) => result < 0n);
law("FALSE: high is negative", (n: bigint) => high(n) < 0n);
law("TRUE: high of three", () => high(3n) === 0n);

// The precondition can never hold, so nothing is recursive here and the definition is
// harmless: it just says nothing about any argument.
export function never(n: bigint): bigint {
  requires(n > 0n && n < 0n);
  decreases(n);
  return never(n) + 1n;
}

law("FALSE: never is its own successor", () => never(0n) === never(0n) + 1n);

// Mutual recursion that only shrinks every second step does not pass: each call must shrink.
export function tick(n: bigint): bigint {
  decreases(n);
  return n <= 0n ? 0n : tock(n);
}

export function tock(n: bigint): bigint {
  decreases(n);
  return n <= 0n ? 0n : tick(n - 1n);
}

// Nested recursion: the outer call's argument is a result of the function itself.
export function nest(n: bigint): bigint {
  decreases(n);
  return n <= 0n ? 0n : nest(nest(n - 1n));
}

law("FALSE: nest is positive", (n: bigint) => nest(n) > 0n);
