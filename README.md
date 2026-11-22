# vscript

**Verified TypeScript** — an opt-in, sound pure subset of TypeScript (`"use verified";`) whose invariants (`law(...)`) are formally proved at compile time by **Z3**, with zero `tsc` fork.

## How It Works

1. **Stage 1 — Strict TypeScript Typecheck:** Runs `ts.createProgram` with `strict`, `noUncheckedIndexedAccess`, and `exactOptionalPropertyTypes`.
2. **Stage 2 — Dialect Soundness Checker (`src/dialect.ts`):** For files carrying `"use verified";`, enforces a pure, terminating, sound subset:
   - Supported types: `bigint` (`Int`), `boolean` (`Bool`), and immutable `readonly` record types.
   - Forbidden: `any`, `unknown`, `number` (IEEE-754 float), `as` / `!` casts, `let`/`var` mutation, loops, `throw`/`try`, `async`, globals, unverified calls, and recursion.
3. **Stage 3 — SMT-LIB2 Lowering + Z3 (`src/smt.ts`, `src/z3.ts`):** Compiles verified functions and `law(...)` predicates into SMT-LIB2 and asks Z3 whether *any* input can violate the law:
   - `unsat` → **PROVED** across all possible inputs.
   - `sat` → **DISPROVED**, with a concrete TypeScript counterexample.

## Soundness Testing

`PROVED` is only worth something if it can be trusted, so `test/soundness.test.ts` checks the prover against real JavaScript execution:

- Every `PROVED` law is run on hundreds of random inputs and must hold on all of them.
- Every `DISPROVED` counterexample is replayed and must actually violate the law.
- `test/fixtures/soundness/` holds regression cases for past false-`PROVED` bugs. Laws named `FALSE: ...` must never be proved, and laws named `TRUE: ...` must be.

If you find a law that vscript proves but that fails at runtime, please add it as a fixture there.

## Prerequisites

- Node.js 20+
- `z3` on `PATH` (e.g. `brew install z3`), or pass `--z3 /path/to/z3` / `VSCRIPT_Z3`.

## Quick Start

```sh
npm install
npm run build
npm test

# Prove clean examples
node dist/cli.js check examples/tokens.law.ts examples/bank.law.ts

# Catch an intentional bug with a concrete counterexample
node dist/cli.js check examples/buggy.law.ts

# Inspect generated SMT-LIB2
node dist/cli.js check examples/tokens.law.ts --emit-smt

# See dialect rejection on unsound TypeScript
node dist/cli.js check examples/unsound.law.ts
```

## Example

```ts
"use verified";

import { law, implies } from "../src/runtime.js";

export type Account = { readonly balance: bigint; readonly frozen: boolean };

export function withdraw(acc: Account, amount: bigint): Account {
  if (acc.frozen || amount <= 0n || amount > acc.balance) return acc;
  return { balance: acc.balance - amount, frozen: acc.frozen };
}

law("withdraw never overdrafts", (acc: Account, amount: bigint) => {
  const after = withdraw(acc, amount);
  return implies(acc.balance >= 0n, after.balance >= 0n && after.balance <= acc.balance);
});
```
