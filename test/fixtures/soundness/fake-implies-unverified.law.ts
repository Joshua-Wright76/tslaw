"use verified";

// Bug: any import named `implies` was lowered as SMT `=>`, whatever it actually did.
// Must be rejected: `implies` here comes from an unverified module, not the tslaw runtime.
import { law } from "../../../src/runtime.js";
import { implies } from "./fake-implies.js";

law("FALSE: a false premise implies anything", (x: bigint) => implies(x < x, x === x));
