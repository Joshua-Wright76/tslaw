"use verified";

// Bug: records made readonly with `Readonly<T>` were rejected as mutable.
import { law } from "../../../src/runtime.js";

type Mutable = { n: bigint; ok: boolean };
export type Point = Readonly<{ x: bigint; y: bigint }>;
export type Frozen = Readonly<Mutable>;

export function flip(p: Point): Point {
  return { x: p.y, y: p.x };
}

law("TRUE: flip twice is identity", (p: Point) => flip(flip(p)).x === p.x && flip(flip(p)).y === p.y);
law("TRUE: Readonly of a mutable alias", (f: Frozen) => f.ok === f.ok && f.n === f.n);
law("FALSE: flip keeps x", (p: Point) => flip(p).x === p.x);
