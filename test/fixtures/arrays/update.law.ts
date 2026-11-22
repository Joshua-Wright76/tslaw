"use verified";

import { at, implies, law, len, withAt } from "../../../src/runtime.js";

// Reading an updated array at another index needs a case split on two symbolic indices. Z3
// is slow and erratic at this for sequences (seconds to timeouts); cvc5 proves all three
// directly, which is what `--cross-check` is for.
law("TRUE: withAt keeps earlier elements", (xs: readonly bigint[], i: bigint, j: bigint, v: bigint) =>
  implies(0n <= j && j < i && i < len(xs), at(withAt(xs, i, v), j) === at(xs, j)),
);
law("TRUE: withAt keeps later elements", (xs: readonly bigint[], i: bigint, j: bigint, v: bigint) =>
  implies(0n <= i && i < j && j < len(xs), at(withAt(xs, i, v), j) === at(xs, j)),
);
law("TRUE: withAt read anywhere", (xs: readonly bigint[], i: bigint, j: bigint, v: bigint) =>
  implies(
    0n <= i && i < len(xs) && 0n <= j && j < len(xs),
    at(withAt(xs, i, v), j) === (i === j ? v : at(xs, j)),
  ),
);
