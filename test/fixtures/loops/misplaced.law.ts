"use verified";

import { decreases, invariant, law } from "../../../src/runtime.js";

export function noMeasure(n: bigint): bigint {
  let i = 0n;
  while (i < n) {
    i = i + 1n;
  }
  return i;
}

export function returnsInside(n: bigint): bigint {
  let i = 0n;
  while (i < n) {
    decreases(n - i);
    if (i === 3n) return i;
    i = i + 1n;
  }
  return i;
}

export function assignsParam(n: bigint): bigint {
  n = n + 1n;
  return n;
}

export function lateInvariant(n: bigint): bigint {
  let i = 0n;
  while (i < n) {
    decreases(n - i);
    i = i + 1n;
    invariant(i >= 0n);
  }
  return i;
}

export function forLoop(n: bigint): bigint {
  let acc = 0n;
  for (let i = 0n; i < n; i = i + 1n) {
    acc = acc + i;
  }
  return acc;
}

export function selfInLoop(n: bigint): bigint {
  decreases(n);
  let acc = 0n;
  let i = 0n;
  while (i < 1n) {
    decreases(1n - i);
    acc = n <= 0n ? 0n : selfInLoop(n - 1n);
    i = i + 1n;
  }
  return acc;
}

law("loops belong in functions", (n: bigint) => {
  let i = 0n;
  while (i < n) {
    decreases(n - i);
    i = i + 1n;
  }
  return i >= 0n;
});
