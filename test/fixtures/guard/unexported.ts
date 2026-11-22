"use verified";

import { requires } from "../../../src/runtime.js";

function positive(x: bigint): boolean {
  return x > 0n;
}

export function f(x: bigint): bigint {
  requires(positive(x));
  return x;
}
