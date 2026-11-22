"use verified";

import { len } from "../../../src/runtime.js";

export function length(xs: readonly bigint[]): bigint {
  return xs.length > 0 ? 1n : 0n;
}

export function index(xs: readonly bigint[]): bigint {
  return xs[0] === undefined ? 0n : 1n;
}

export function same(xs: readonly bigint[], ys: readonly bigint[]): boolean {
  return xs === ys;
}

export function spread(xs: readonly bigint[]): bigint {
  return len([...xs, 1n]);
}

export function tuple(pair: readonly [bigint, bigint]): bigint {
  return len(pair);
}

export function untyped(): bigint {
  return len([]);
}
