"use verified";

import { decreases, ensures, implies, invariant, law, requires } from "../../../src/runtime.js";

// 1 + 2 + ... + n
export function sumTo(n: bigint): bigint {
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

ensures(sumTo, (n, result) => 2n * result === n * (n + 1n));

// Multiplication by repeated addition, with an `if` that assigns inside the loop.
export function times(a: bigint, b: bigint): bigint {
  requires(b >= 0n);
  let left = b;
  let total = 0n;
  let steps = 0n;
  while (left > 0n) {
    invariant(left >= 0n && total === a * (b - left));
    decreases(left);
    if (left > 1n) {
      total = total + a + a;
      left = left - 2n;
    } else {
      total = total + a;
      left = left - 1n;
    }
    steps = steps + 1n;
  }
  return total;
}

ensures(times, (a, b, result) => result === a * b);

// Assignments outside loops: branches that fall through, and a guard clause that returns.
export function clamp(x: bigint, lo: bigint, hi: bigint): bigint {
  requires(lo <= hi);
  let r = x;
  if (r < lo) r = lo;
  if (r > hi) {
    r = hi;
  }
  return r;
}

ensures(clamp, (_x, lo, hi, result) => lo <= result && result <= hi);
ensures(clamp, (x, lo, hi, result) => implies(lo <= x && x <= hi, result === x));

export function sign(x: bigint): bigint {
  let s = 0n;
  if (x > 0n) {
    s = 1n;
  } else {
    if (x === 0n) return 0n;
    s = -1n;
  }
  const doubled = s * 2n;
  return doubled - s;
}

ensures(sign, (x, result) => (x > 0n ? result === 1n : x < 0n ? result === -1n : result === 0n));

// Nested loops: the inner loop's invariant is what the outer loop's body knows afterwards.
export function grid(rows: bigint, cols: bigint): bigint {
  requires(rows >= 0n && cols >= 0n);
  let r = 0n;
  let cells = 0n;
  while (r < rows) {
    invariant(0n <= r && r <= rows && cells === r * cols);
    decreases(rows - r);
    let c = 0n;
    while (c < cols) {
      invariant(0n <= c && c <= cols && cells === r * cols + c);
      decreases(cols - c);
      c = c + 1n;
      cells = cells + 1n;
    }
    r = r + 1n;
  }
  return cells;
}

ensures(grid, (rows, cols, result) => result === rows * cols);

law("TRUE: sumTo(4)", () => sumTo(4n) === 10n);
law("TRUE: times(6, 7)", () => times(6n, 7n) === 42n);
law("TRUE: grid(2, 3)", () => grid(2n, 3n) === 6n);
law("TRUE: sumTo grows", (n: bigint) => implies(n >= 0n, sumTo(n + 1n) === sumTo(n) + n + 1n));
law("FALSE: sumTo(4) is eleven", () => sumTo(4n) === 11n);
law("FALSE: times ignores its first argument", (a: bigint, b: bigint) =>
  implies(b >= 0n, times(a, b) === b),
);
