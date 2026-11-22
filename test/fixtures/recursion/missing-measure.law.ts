"use verified";

import { decreases, requires } from "../../../src/runtime.js";

export function noMeasure(n: bigint): bigint {
  return n <= 0n ? 0n : noMeasure(n - 1n);
}

export function ping(n: bigint): bigint {
  decreases(n);
  return n <= 0n ? 0n : pong(n - 1n);
}

export function pong(n: bigint): bigint {
  return n <= 0n ? 0n : ping(n - 1n);
}

export function late(n: bigint): bigint {
  const m = n - 1n;
  decreases(m);
  return n <= 0n ? 0n : late(m);
}

export function selfInSpec(n: bigint): bigint {
  requires(selfInSpec(n) >= 0n);
  decreases(n);
  return n <= 0n ? 0n : selfInSpec(n - 1n);
}

// Not recursive: the measure would never be checked, yet its argument runs on every call.
export function plain(n: bigint): bigint {
  decreases(noMeasure(n));
  return n;
}
