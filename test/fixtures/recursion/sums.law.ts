"use verified";

import { decreases, ensures, implies, law, requires } from "../../../src/runtime.js";

// 0 + 1 + ... + n
export function sum(n: bigint): bigint {
  decreases(n);
  if (n <= 0n) return 0n;
  return n + sum(n - 1n);
}

// Proved by induction: the postcondition is assumed for the recursive call `sum(n - 1n)`.
ensures(sum, (n, result) => implies(n >= 0n, 2n * result === n * (n + 1n)));
ensures(sum, (_n, result) => result >= 0n);

export function factorial(n: bigint): bigint {
  requires(n >= 0n);
  decreases(n);
  return n === 0n ? 1n : n * factorial(n - 1n);
}

ensures(factorial, (_n, result) => result >= 1n);

export function fib(n: bigint): bigint {
  requires(n >= 0n);
  decreases(n);
  if (n < 2n) return n;
  return fib(n - 1n) + fib(n - 2n);
}

ensures(fib, (_n, result) => result >= 0n);

// Mutual recursion: both functions share one measure.
export function isEven(n: bigint): boolean {
  requires(n >= 0n);
  decreases(n);
  return n === 0n ? true : isOdd(n - 1n);
}

export function isOdd(n: bigint): boolean {
  requires(n >= 0n);
  decreases(n);
  return n === 0n ? false : isEven(n - 1n);
}

// Each needs the other's postcondition as its induction hypothesis.
ensures(isEven, (n, result) => result === !isOdd(n));
ensures(isOdd, (n, result) => result === !isEven(n));

// Two measures compared in order: `m` may grow as long as `n` shrinks.
export function ackermann(m: bigint, n: bigint): bigint {
  requires(m >= 0n && n >= 0n);
  decreases(m, n);
  if (m === 0n) return n + 1n;
  if (n === 0n) return ackermann(m - 1n, 1n);
  return ackermann(m - 1n, ackermann(m, n - 1n));
}

ensures(ackermann, (_m, n, result) => result > n);

// Laws see the definitions, so concrete values are computed by unfolding...
law("TRUE: sum of the first four numbers", () => sum(4n) === 10n);
law("TRUE: five factorial", () => factorial(5n) === 120n);
law("TRUE: tenth Fibonacci number", () => fib(10n) === 55n);
law("TRUE: seven is odd", () => isOdd(7n) && !isEven(7n));
law("TRUE: ackermann(2, 3)", () => ackermann(2n, 3n) === 9n);
law("FALSE: sum of the first four numbers is eleven", () => sum(4n) === 11n);

// ...and the proved postconditions are available at every call, for all arguments.
law("TRUE: closed form of sum", (n: bigint) => implies(n >= 0n, 2n * sum(n) === n * n + n));
law("TRUE: sum never negative", (n: bigint) => sum(n) >= 0n);
law("TRUE: factorial is positive", (n: bigint) => implies(n >= 0n, factorial(n) > 0n));
law("FALSE: sum is at most n", (n: bigint) => sum(n) <= n);
