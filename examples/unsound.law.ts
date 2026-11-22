"use verified";

import { law } from "../src/runtime.js";

/**
 * Intentional dialect violations — rejected statically before Z3 runs.
 */
export function badFunction(x: number): bigint {
  var acc = 0n;
  // A loop with nothing that shows it ends.
  while (acc < 10n) {
    acc = acc + 1n;
  }
  for (let i = 0n; i < 3n; i = i + 1n) {
    acc = acc + i;
  }
  return (x as unknown as bigint) + acc;
}

law("dummy", (x: number) => badFunction(x) >= 0n);
