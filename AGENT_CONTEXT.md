# AGENT_CONTEXT.md

Technical reference and contributor/agent guide for **tslaw** — a strict verifiable subset of TypeScript checked at compile time with Z3 (and optionally cross-checked with cvc5).

## Canonical References

- Usage, supported subset, CLI, and error-code table (`LAW###`): `README.md` (update when adding or changing an error code).
- Formal subset definition, SMT-LIB2 translation, and soundness argument: `docs/SEMANTICS.md` (keep in sync with `src/dialect.ts` and `src/smt.ts`).
- Machine-checked core soundness proof (Lean 4, no external dependencies): `proofs/Core.lean` (keep in sync with `src/smt.ts` for core expressions/blocks).
- Interactive animated explainer: `docs/explainer.html` (self-contained HTML/CSS/JS; scenes are `<section class="scene">` blocks).

## Architecture

1. **Stage 1 — Strict TypeScript typecheck (`src/verify.ts`)**: runs the TypeScript Compiler API with `strict`, `noUncheckedIndexedAccess`, `exactOptionalPropertyTypes`, `module: ESNext`, `moduleResolution: Bundler` on each opted-in `"use verified";` file and its transitive `"use verified";` imports (`verifiedDeps`). Files without `"use verified";` are skipped unless `--all` is passed.
2. **Stage 2 — Dialect & soundness check (`src/dialect.ts`)**: enforces the pure, terminating subset (`bigint`, `boolean`, immutable `readonly` records, immutable arrays via runtime helpers; `const`/`let`, local assignment, `if`/`else`, `while` with `invariant` + `decreases`, recursion with `decreases`, `requires`/`ensures`, `law`/`implies`). Groups functions into Tarjan SCCs ordered callees-first.
3. **Stage 3 — SMT-LIB2 lowering & solving (`src/smt.ts`, `src/z3.ts`, `src/verify.ts`)**: lowers functions, loops, contracts, and laws to SMT-LIB2 queries (`Int`, `Bool`, `declare-datatypes`, `Seq`), runs Z3 (and optionally cvc5 with `--check-proofs --check-models` via `--cross-check`), decodes counterexamples, and withdraws verdicts whose dependencies/foundations were not proved.
4. **Runtime shim (`src/runtime.ts`, re-exported by `src/index.ts`)**: zero-cost no-ops for `law`, `requires`, `ensures`, `decreases`, `invariant`; executable `implies` and bounds-checked immutable array helpers (`len`, `at`, `append`, `concat`, `slice`, `withAt`).
5. **Boundary guards (`src/guard.ts`, `tslaw guard`)**: emits self-contained `<name>.guarded.ts` wrappers for unverified callers that validate runtime types, clone/freeze records and arrays, check `requires`, and call the verified function. Committed golden fixtures live in `test/fixtures/guard/*.guarded.ts`; regenerate them when changing `src/guard.ts`.

## Critical Soundness Invariants

Preserve every invariant below when editing the checker, translator, or guard generator (most correspond to past false-`PROVED` bugs with regression tests in `test/fixtures/soundness/` and `test/tslaw.test.ts`):

- **Identity by declaration, never by name**: functions are keyed by `ts.FunctionDeclaration` (resolved through the type checker, following aliases) and assigned unique indexed SMT names (`fn_<i>_<name>`). Runtime helpers (`law`, `implies`, `requires`, `ensures`, `decreases`, `invariant`, array helpers) are recognized only when resolved to the real `tslaw` runtime (`isTslawRuntimeFile`), and may not be re-exported through third-party modules.
- **Collision-free SMT and type keys**: SMT symbols get uniqueness from numeric prefixes (`p_<i>_`, `arg_<i>_`, `Rec_<n>_<i>_`), because sanitizing TS names is lossy and Z3 silently accepts duplicate parameter names. `vTypeKey` JSON-quotes field names, and record fields are sorted deterministically by code unit. Never write unescaped user text (such as law names) into SMT scripts.
- **No JS/SMT semantic gaps**:
  - Reject `number`, unary `+` (coerces `boolean` to `number`), `/` and `%` (truncating vs Euclidean division), `any`, `unknown`, casts, `@ts-ignore`/`@ts-expect-error`/`@ts-nocheck`, and non-boolean conditions/logical operands (`LAW034`).
  - Reject literal types in declared parameter positions (`resolveVType(..., declared = true)`).
  - Reject `__proto__` fields, index signatures, construct signatures, and symbol-keyed fields in records; reject `this` parameters.
  - Object destructuring requires a record initializer, identifier keys only (no string/computed keys), and declared fields only; property access requires declared fields only.
  - When lowering an object literal at a narrower expected record type (width subtyping), still lower extra properties so obligations and termination checks are never dropped.
  - `Readonly<T>` is detected via TypeScript's `CheckFlags.Readonly` (`1 << 3`); re-verify on TypeScript major upgrades (`test/fixtures/soundness/readonly-utility.law.ts`).
- **Imports**: reject side-effect imports, default/namespace imports, cyclic verified imports (`IN_PROGRESS`), and verified functions re-exported through unverified barrels (which would bypass Stage 1 typechecking).
- **Recursion, loops, and verdict dependencies**:
  - Termination (`decreases`) queries mark their recursive group `opaque` (declared, not defined) and only assume postconditions strictly below the group (including all units those postconditions mention).
  - Loop maintenance, termination, and body-obligation queries mark the loop unit `opaque` and use only postconditions strictly below the enclosing function.
  - In `ensures(fn, post)`, calls written inside `post` itself may only assume postconditions of callees strictly below `fn` (reachable from `fn` and not reaching `fn`), preventing circular postconditions between unrelated functions.
  - `implies(p, q)` assumes `p` for `q`'s obligations only in laws/postconditions, never in executable code (function bodies, `requires`, `decreases`, `invariant`), where JS evaluates both arguments eagerly.
  - `decreases(...)` on a non-recursive function is rejected (`LAW037`).
  - `LoweredLaw.foundations` withdraws even `DISPROVED` verdicts when a used recursive function/loop fails termination, or (for `law`/`ensures`) when any call-site precondition or loop invariant in the query's units fails.
- **Guards (`src/guard.ts`)**: typecheck transitive verified dependencies (`verifiedDeps`), pick a collision-free helper prefix, escape non-identifier field names in error paths, and reject `Array.isArray(v)` where a record is expected.

## Testing & Verification

- Build and run the full test suite (requires `z3` on `PATH`):
  ```sh
  npm run build && npm test
  ```
- Under heavy CPU load, tests can hit vitest's 30s timeout; run serially if needed:
  ```sh
  npx vitest run --no-file-parallelism --testTimeout=300000
  ```
- Optional checks (skipped automatically when the tool is absent):
  - Machine-checked Lean core: `npm run prove`
  - Extended fuzzer: `TSLAW_FUZZ_RUNS=300 npm test -- test/fuzz.test.ts` (add `TSLAW_FUZZ_CROSS_CHECK=1` to cross-check with cvc5; `TSLAW_FUZZ_DIR` overrides output dir).
  - Lowering stack traces: `TSLAW_DEBUG=1`.
- Regenerate guard golden fixtures after changing `src/guard.ts`:
  ```sh
  node dist/cli.js guard test/fixtures/guard/bank.ts test/fixtures/guard/limits.ts test/fixtures/guard/basket.ts
  ```
- Add a soundness fixture in `test/fixtures/soundness/` or regression test in `test/tslaw.test.ts` for every bug fix, and keep `test/fuzz/generate.ts` in sync whenever the verified subset grows.
