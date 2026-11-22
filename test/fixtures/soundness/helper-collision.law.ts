"use verified";

// Bug: functions were keyed by bare name, so the importer's `helper` silently replaced
// dep-a's private `helper` inside `f`, and dep-a/dep-b's helpers overwrote each other.
import { law } from "../../../src/runtime.js";
import { f } from "./dep-a.js";
import { g } from "./dep-b.js";

function helper(x: bigint): bigint {
  return x + 100n;
}

export function h(x: bigint): bigint {
  return helper(x);
}

law("FALSE: f uses the importer's helper", (x: bigint) => f(x) === x + 100n);
law("FALSE: f and g share one helper", (x: bigint) => f(x) === g(x));
law("TRUE: f adds 1", (x: bigint) => f(x) === x + 1n);
law("TRUE: g adds 2", (x: bigint) => g(x) === x + 2n);
law("TRUE: h adds 100", (x: bigint) => h(x) === x + 100n);
