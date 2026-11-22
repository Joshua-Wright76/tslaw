"use verified";

import { at, decreases, invariant, law, len } from "../../../src/runtime.js";

// A `const` in a branch hides the outer `let` only inside that branch.
export function shadowInBranch(x: bigint): bigint {
  let a = x;
  if (x > 0n) {
    const a = 5n;
    return a;
  }
  a = a + 1n;
  return a;
}

// A variable declared in a branch is gone afterwards; what the branch assigned outside stays.
export function assignThroughBranch(x: bigint): bigint {
  let a = 0n;
  if (x > 0n) {
    let b = 1n;
    a = b + 1n;
    b = 7n;
    if (x > 10n) a = a + b;
  }
  return a;
}

// A `let` declared inside a loop body hides the outer one of the same name there.
export function shadowInLoop(n: bigint): bigint {
  let acc = 10n;
  let i = 0n;
  while (i < 2n) {
    decreases(2n - i);
    let acc = n;
    acc = acc + 5n;
    i = i + 1n + acc - acc;
  }
  return acc;
}

// Branches that return, fall through and assign, mixed.
export function mixed(x: bigint): bigint {
  let r = 1n;
  if (x > 0n) {
    if (x > 100n) return 100n;
    r = r + x;
  } else {
    r = r - 1n;
    if (x < -100n) {
      r = -100n;
    } else {
      return r;
    }
  }
  r *= 2n;
  return r;
}

// Two loops in a row over the same variables, and a loop that runs zero times.
export function twoLoops(xs: readonly bigint[]): bigint {
  let i = 0n;
  let total = 0n;
  while (i < len(xs) && i < 2n) {
    invariant(i >= 0n); // without this, `at(xs, i)` could not be shown to be in range
    decreases(2n - i);
    total += at(xs, i);
    i += 1n;
  }
  while (i < 0n) {
    decreases(0n - i);
    total = 999n;
    i += 1n;
  }
  while (i < 4n) {
    decreases(4n - i);
    total -= 1n;
    i += 1n;
  }
  return total;
}

law("TRUE: shadowInBranch", () => shadowInBranch(3n) === 5n && shadowInBranch(0n) === 1n && shadowInBranch(-4n) === -3n);
law("TRUE: assignThroughBranch", () =>
  assignThroughBranch(0n) === 0n && assignThroughBranch(5n) === 2n && assignThroughBranch(11n) === 9n,
);
law("TRUE: shadowInLoop keeps the outer variable", (n: bigint) => shadowInLoop(n) === 10n);
law("TRUE: mixed", () =>
  mixed(200n) === 100n && mixed(3n) === 8n && mixed(0n) === 0n && mixed(-200n) === -200n,
);
law("TRUE: twoLoops", () => twoLoops([5n, 7n, 100n]) === 10n && twoLoops([5n]) === 2n && twoLoops([]) === -4n);
law("FALSE: shadowInBranch leaks the inner const", () => shadowInBranch(0n) === 5n);
law("FALSE: assignThroughBranch loses the assignment", (x: bigint) => assignThroughBranch(x) === 0n);
law("FALSE: shadowInLoop changes the outer variable", (n: bigint) => shadowInLoop(n) === n + 5n);
law("FALSE: mixed forgets to double", () => mixed(3n) === 4n);
law("FALSE: twoLoops runs the empty loop", () => twoLoops([]) === 999n);
