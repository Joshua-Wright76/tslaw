"use verified";

import { decreases, law } from "../../../src/runtime.js";
import { pong } from "./cycle-b.js";

// Mutual recursion across two modules that import each other is not supported: neither
// module's analysis can see the whole recursion.
export function ping(n: bigint): bigint {
  decreases(n);
  return n <= 0n ? 0n : pong(n - 1n) + 1n;
}

law("FALSE: ping is its own successor", (n: bigint) => ping(n) === ping(n) + 1n);
