"use verified";

import { decreases, ensures, implies, law, requires } from "../../../src/runtime.js";
import { mod } from "./lib.js";

// Euclid's algorithm. Termination needs `mod(a, b) < b`, which is `mod`'s postcondition,
// declared and proved in another module.
export function gcd(a: bigint, b: bigint): bigint {
  requires(a >= 0n && b >= 0n);
  decreases(b);
  return b === 0n ? a : gcd(b, mod(a, b));
}

ensures(gcd, (_a, _b, result) => result >= 0n);

law("TRUE: gcd(12, 18)", () => gcd(12n, 18n) === 6n);
law("TRUE: gcd with zero", (a: bigint) => implies(a >= 0n, gcd(a, 0n) === a));
law("FALSE: gcd is at most its second argument", (a: bigint, b: bigint) =>
  implies(a >= 0n && b >= 0n, gcd(a, b) <= b),
);
