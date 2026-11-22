"use verified";

import { ensures, law, requires } from "../../../src/runtime.js";

export function late(x: bigint): bigint {
  const y = x + 1n;
  requires(y > 0n);
  return y;
}

export function ok(x: bigint): bigint {
  return x;
}

ensures(ok, (x) => x === x);
law("requires in a law", (x: bigint) => {
  requires(x > 0n);
  return x > 0n;
});
