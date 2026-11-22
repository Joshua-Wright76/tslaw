"use verified";

import { decreases, ensures, implies, invariant, law, requires } from "../src/runtime.js";

/**
 * Sum 1 + 2 + ... + n using a `while` loop with a loop invariant and termination measure.
 */
export function sumLoop(n: bigint): bigint {
  requires(n >= 0n);
  let i = 0n;
  let acc = 0n;
  while (i < n) {
    invariant(0n <= i && i <= n);
    invariant(2n * acc === i * (i + 1n));
    decreases(n - i);
    i += 1n;
    acc += i;
  }
  return acc;
}

ensures(sumLoop, (n, result) => 2n * result === n * (n + 1n));

/**
 * The same sum written recursively with a `decreases` measure; `ensures` is proved by induction.
 */
export function sumRec(n: bigint): bigint {
  requires(n >= 0n);
  decreases(n);
  if (n === 0n) return 0n;
  return n + sumRec(n - 1n);
}

ensures(sumRec, (n, result) => 2n * result === n * (n + 1n));

/**
 * Multiplication by repeated addition, with an `if` branch updating locals inside a loop.
 */
export function times(a: bigint, b: bigint): bigint {
  requires(b >= 0n);
  let left = b;
  let total = 0n;
  while (left > 0n) {
    invariant(left >= 0n && total === a * (b - left));
    decreases(left);
    total += a;
    left -= 1n;
  }
  return total;
}

ensures(times, (a, b, result) => result === a * b);

law("iterative and recursive sums agree for all non-negative n", (n: bigint) =>
  implies(n >= 0n, sumLoop(n) === sumRec(n)),
);

law("sumRec is monotone", (a: bigint, b: bigint) =>
  implies(0n <= a && a <= b, sumRec(a) <= sumRec(b)),
);

law("times commutes for non-negative inputs", (a: bigint, b: bigint) =>
  implies(a >= 0n && b >= 0n, times(a, b) === times(b, a)),
);
