"use verified";

import {
  append,
  at,
  concat,
  decreases,
  ensures,
  implies,
  invariant,
  law,
  len,
  requires,
  slice,
  withAt,
} from "../../../src/runtime.js";

export type Point = { readonly x: bigint; readonly y: bigint };

// Sum of the first `n` elements, by recursion.
export function sumPrefix(xs: readonly bigint[], n: bigint): bigint {
  requires(0n <= n && n <= len(xs));
  decreases(n);
  return n === 0n ? 0n : sumPrefix(xs, n - 1n) + at(xs, n - 1n);
}

// The same sum with a loop; the invariant ties it to the recursive definition.
export function sum(xs: readonly bigint[]): bigint {
  let i = 0n;
  let acc = 0n;
  while (i < len(xs)) {
    invariant(0n <= i && i <= len(xs));
    invariant(acc === sumPrefix(xs, i));
    decreases(len(xs) - i);
    acc = acc + at(xs, i);
    i = i + 1n;
  }
  return acc;
}

ensures(sum, (xs, result) => result === sumPrefix(xs, len(xs)));

// Largest element of a non-empty array.
export function max(xs: readonly bigint[]): bigint {
  requires(len(xs) > 0n);
  let best = at(xs, 0n);
  let i = 1n;
  while (i < len(xs)) {
    invariant(1n <= i && i <= len(xs));
    decreases(len(xs) - i);
    if (at(xs, i) > best) best = at(xs, i);
    i = i + 1n;
  }
  return best;
}

export function first(points: readonly Point[]): Point {
  requires(len(points) > 0n);
  return at(points, 0n);
}

export function origin(): readonly Point[] {
  return [{ x: 0n, y: 0n }];
}

export function safeAt(xs: readonly bigint[], i: bigint, fallback: bigint): bigint {
  return 0n <= i && i < len(xs) ? at(xs, i) : fallback;
}

law("TRUE: literal length", () => len([1n, 2n, 3n]) === 3n);
law("TRUE: empty literal", () => {
  const none: readonly bigint[] = [];
  return len(none) === 0n;
});
law("TRUE: literal elements", () => {
  const xs: readonly bigint[] = [10n, 20n, 30n];
  return at(xs, 0n) === 10n && at(xs, 2n) === 30n;
});
law("TRUE: append adds one at the end", (xs: readonly bigint[], x: bigint) => {
  const ys = append(xs, x);
  return len(ys) === len(xs) + 1n && at(ys, len(xs)) === x;
});
law("TRUE: append keeps the others", (xs: readonly bigint[], x: bigint, i: bigint) =>
  implies(0n <= i && i < len(xs), at(append(xs, x), i) === at(xs, i)),
);
law("TRUE: concat lengths add", (xs: readonly bigint[], ys: readonly bigint[]) =>
  len(concat(xs, ys)) === len(xs) + len(ys),
);
law("TRUE: concat reads from the second part", (xs: readonly bigint[], ys: readonly bigint[], i: bigint) =>
  implies(0n <= i && i < len(ys), at(concat(xs, ys), len(xs) + i) === at(ys, i)),
);
law("TRUE: slice", (xs: readonly bigint[], a: bigint, b: bigint, i: bigint) =>
  implies(
    0n <= a && a <= b && b <= len(xs) && 0n <= i && i < b - a,
    len(slice(xs, a, b)) === b - a && at(slice(xs, a, b), i) === at(xs, a + i),
  ),
);
// Reads at a different index than the one replaced are in `update.law.ts`.
law("TRUE: withAt keeps the length", (xs: readonly bigint[], i: bigint, v: bigint) =>
  implies(0n <= i && i < len(xs), len(withAt(xs, i, v)) === len(xs)),
);
law("TRUE: withAt replaces the element", (xs: readonly bigint[], i: bigint, v: bigint) =>
  implies(0n <= i && i < len(xs), at(withAt(xs, i, v), i) === v),
);
law("TRUE: records in arrays", (p: Point) => {
  const ps: readonly Point[] = [p, { x: p.y, y: p.x }];
  return at(ps, 1n).x === p.y && first(ps).x === p.x;
});
law("TRUE: sum of a literal", () => sum([1n, 2n, 3n]) === 6n);
law("TRUE: max of a literal", () => max([3n, 9n, 4n]) === 9n);
law("TRUE: safeAt falls back", (xs: readonly bigint[]) => safeAt(xs, len(xs), 7n) === 7n);
law("TRUE: origin", () => at(origin(), 0n).x === 0n);
law("FALSE: arrays are never empty", (xs: readonly bigint[]) => len(xs) > 0n);
law("FALSE: append puts it first", (xs: readonly bigint[], x: bigint) => at(append(xs, x), 0n) === x);
law("FALSE: every pair is sorted", (xs: readonly bigint[]) =>
  implies(len(xs) === 2n, at(xs, 0n) <= at(xs, 1n)),
);
