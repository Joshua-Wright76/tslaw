"use verified";

// Bug: the law name was written into an SMT comment verbatim, so a newline in the name ended
// the comment and the rest became SMT commands. `(assert false)` makes any law "PROVED".
import { law } from "../../../src/runtime.js";

law("FALSE: injected assert\n(assert false)", (x: bigint) => x === x + 1n);
law("TRUE: unusual name ; (check-sat) \" |", (x: bigint) => x === x);
