"use verified";

import { ensures, law, requires } from "../../../src/runtime.js";

export function half(x: bigint): bigint {
  requires(x >= 0n);
  return x - x;
}

// The call is not guarded: x may be negative.
export function unguarded(x: bigint): bigint {
  return half(x);
}

// Guarded on the wrong branch.
export function wrongBranch(x: bigint): bigint {
  if (x >= 0n) return 0n;
  return half(x);
}

// A caller's own `requires` that is too weak.
export function tooWeak(x: bigint): bigint {
  requires(x >= -1n);
  return half(x);
}

// A postcondition that does not follow.
ensures(half, (x, result) => result === x);

// A postcondition that only holds because of the precondition.
ensures(half, (x, result) => result <= x);

law("law calls without establishing the precondition", (x: bigint) => half(x) === 0n);
