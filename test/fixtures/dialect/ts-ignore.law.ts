"use verified";

import { law } from "../../../src/runtime.js";

export function id(x: bigint): bigint {
  return x;
}

// @ts-ignore
law("suppressed type error", (x: bigint) => id(true) === x);
