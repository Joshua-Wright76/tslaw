"use verified";

import { decreases, ensures, implies, law, requires } from "../../../src/runtime.js";

// The measure does not shrink. If this definition were trusted it would say
// `loop(n) === loop(n) + 1n`, from which anything follows.
export function loop(n: bigint): bigint {
  decreases(n);
  return loop(n) + 1n;
}

law("FALSE: loop is its own successor", () => loop(0n) === loop(0n) + 1n);
law("FALSE: anything about loop", (n: bigint) => loop(n) > loop(n));

// Counts up forever for positive arguments.
export function up(n: bigint): bigint {
  decreases(n);
  return n <= 0n ? 0n : up(n + 1n);
}

// The measure shrinks but is not bounded below: `down(-1n)` never returns.
export function down(n: bigint): bigint {
  decreases(n);
  return n === 0n ? 0n : down(n - 1n);
}

// Fine under its precondition, which the recursive call keeps.
export function countdown(n: bigint): bigint {
  requires(n >= 0n);
  decreases(n);
  return n === 0n ? 0n : countdown(n - 1n);
}

ensures(countdown, (_n, result) => result === 0n);
law("TRUE: countdown reaches zero", (n: bigint) => n < 0n || countdown(n) === 0n);

// A false postcondition cannot be used to prove itself, or anything else.
export function id(n: bigint): bigint {
  requires(n >= 0n);
  decreases(n);
  return n === 0n ? 0n : id(n - 1n) + 1n;
}

ensures(id, (n, _result) => id(n) < 0n);
ensures(id, (_n, result) => result < 0n);
law("FALSE: id is negative", (n: bigint) => n < 0n || id(n) < 0n);

// JavaScript evaluates both arguments of `implies`, so in a function body the call below runs
// (and never returns) for negative `n` even though the premise is false.
export function eager(n: bigint): boolean {
  return implies(n >= 0n, countdown(n) === 0n);
}
// In a law nothing runs, so the premise does guard the call.
law("TRUE: premise guards the call", (n: bigint) => implies(n >= 0n, countdown(n) === 0n));
