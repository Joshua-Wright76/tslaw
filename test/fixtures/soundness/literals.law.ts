"use verified";

// Bug: hex/binary/octal bigint literals were emitted verbatim (`0x10`), which Z3 rejects.
import { law } from "../../../src/runtime.js";

export function hex16(): bigint {
  return 0x10n;
}

law("TRUE: hex literal", (x: bigint) => 0x10n === 16n);
law("TRUE: binary literal", (x: bigint) => 0b101n === 5n);
law("TRUE: octal literal", (x: bigint) => 0o17n === 15n);
law("TRUE: separators", (x: bigint) => 1_000_000n === 1000000n);
law("FALSE: hex is not decimal", (x: bigint) => hex16() === 10n);
