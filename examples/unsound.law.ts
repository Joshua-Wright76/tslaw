"use verified";

import { law } from "../src/runtime.js";

/**
 * Intentional dialect violations — rejected statically before Z3 runs.
 */
export function badFunction(x: number): bigint {
  let acc = 0n;
  while (acc < 10n) {
    acc = acc + 1n;
  }
  return (x as unknown as bigint) + acc;
}

law("dummy", (x: number) => badFunction(x) >= 0n);
