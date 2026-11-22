"use verified";

import { law } from "../../../src/runtime.js";

export function sign(x: bigint): bigint {
  if (x) {
    return 1n;
  }
  return x ? 1n : 0n;
}

law("bigint as boolean", (x: bigint, y: bigint) => !x && (x || y) === x);
