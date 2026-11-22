"use verified";

// Aliased imports resolve by symbol, so they work for runtime helpers and verified functions.
import { law as check, implies as imp } from "../../../src/runtime.js";
import { f as addOne } from "./dep-a.js";

check("TRUE: aliased verified import", (x: bigint) => addOne(x) === x + 1n);
check("TRUE: aliased implies", (x: bigint) => imp(x > 0n, addOne(x) > 1n));
check("FALSE: aliased implies is still implication", (x: bigint) => imp(true, addOne(x) === x));
