"use verified";

// A verified user function named `implies` must be lowered from its body, not as SMT `=>`.
import { law } from "../../../src/runtime.js";
import { implies } from "./and-implies.js";

law("FALSE: imported implies is logical implication", (x: bigint) => implies(x < x, x === x));
law("TRUE: imported implies is conjunction", (p: boolean, q: boolean) => implies(p, q) === (p && q));
