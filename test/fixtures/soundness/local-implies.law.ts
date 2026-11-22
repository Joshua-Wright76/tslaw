"use verified";

// A local function named `implies` (no runtime import of it) must be lowered from its body.
import { law } from "../../../src/runtime.js";

export function implies(a: boolean, b: boolean): boolean {
  return a && b;
}

law("FALSE: local implies is logical implication", (p: boolean) => implies(false, p));
law("TRUE: local implies is conjunction", (p: boolean, q: boolean) => implies(p, q) === (p && q));
