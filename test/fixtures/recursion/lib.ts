"use verified";

import { decreases, ensures, requires } from "../../../src/runtime.js";

// Remainder by repeated subtraction.
export function mod(a: bigint, b: bigint): bigint {
  requires(a >= 0n && b > 0n);
  decreases(a);
  return a < b ? a : mod(a - b, b);
}

ensures(mod, (_a, b, result) => 0n <= result && result < b);

export function spin(n: bigint): bigint {
  decreases(n);
  return spin(n + 1n);
}
