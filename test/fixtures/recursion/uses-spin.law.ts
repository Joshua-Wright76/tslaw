"use verified";

import { law } from "../../../src/runtime.js";
import { spin } from "./lib.js";

// `spin` never returns, so its definition says nothing. Checking only this file must still
// notice: the termination goal of the imported function is checked here as well.
law("FALSE: spin exceeds itself", (n: bigint) => spin(n) > spin(n));
law("TRUE: unrelated arithmetic", (n: bigint) => n + 1n > n);
