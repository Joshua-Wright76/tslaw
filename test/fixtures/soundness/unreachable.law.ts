"use verified";

import { law } from "../../../src/runtime.js";

// After `b = true`, TypeScript knows the right side of `b || ...` never runs and gives it the
// type `never`. It must still translate (and must not be given a wrong value).
export function afterAssignment(x: bigint): boolean {
  let b: boolean = x > 0n;
  if (x > 10n) b = true;
  b = true;
  return b || (b ? b : b);
}

export function pick(x: bigint): bigint {
  let flag: boolean = false;
  flag = true;
  const viaFlag: boolean = flag && (flag ? flag : x > 0n);
  return viaFlag ? x : -x;
}

law("TRUE: afterAssignment is true", (x: bigint) => afterAssignment(x));
law("TRUE: pick returns its argument", (x: bigint) => pick(x) === x);
law("FALSE: pick negates", (x: bigint) => pick(x) === -x);
