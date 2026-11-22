# AGENT_CONTEXT.md

## Purpose
This file is the official agent handoff document and the source of truth for the current state of the project.

## Development Workflow
Whenever I have you make changes to the project code, I want you to use this workflow:
Open a new worktree in this folder, make the changes on a feature branch inside that worktree. Use this workspace for all testing and development. Once the changes are complete, start a preview build of the project on a different port, and then show it to me for testing and ask me for confirmation. Once I give you confirmation, merge those changes into the main worktree, and delete the old one. This workflow allows me to keep using the app while agents are working on new features, and allows me to work on multiple features at a time each in their own worktrees.

## Agent Instructions
- Read this file at the start of every new session.
- Update this file whenever you learn important durable context about the project.
- Update this file whenever the project's behavior, architecture, requirements, or decisions materially change.
- Prefer stable facts and decisions over temporary notes.
- Clearly label planned work, open questions, or assumptions so they are not mistaken for current state.
- If another file is canonical for a specific area, record it here.

## Canonical References
- Overall project state: this file
- Architecture and CLI usage: `README.md`
- Formal definition of the subset, its translation, and the (informal, not machine-checked) soundness argument: `docs/SEMANTICS.md`. Any change to `src/smt.ts` or to what `src/dialect.ts` accepts must be reflected there.
- Animated explainer: `docs/explainer.html` (self-contained, no dependencies; scenes are `<section class="scene">` blocks timed with `data-dur` / `data-at` / `data-lit`). Update it when the pipeline or product name changes.

## Current State
Initial prototype (`0.1.0`) implementing **tslaw** (originally "vscript", whose npm name was taken; briefly "lawscript"; renamed to "tslaw" on 2026-11-21 because it is a checker and library for TypeScript, not a new language. The local folder may still be called `vscript`), a strict verifiable subset of TypeScript checked at compile time with Z3.

Implemented:
- Three-stage verification pipeline (`src/verify.ts`):
  1. Strict TypeScript typechecking via the TypeScript Compiler API (`strict`, `noUncheckedIndexedAccess`, `exactOptionalPropertyTypes`).
  2. Strict dialect / soundness checker (`src/dialect.ts`) for `"use verified";` modules (bans `any`, casts, mutation, loops, `throw`/`try`, `number` floats, side effects, and recursion without a `decreases` measure; supports importing pure verified functions and types from other `"use verified";` modules).
  3. SMT-LIB2 lowering (`src/smt.ts`) and Z3 solver runner (`src/z3.ts`) supporting `bigint` (`Int`), `boolean` (`Bool`), immutable `readonly` record types (`declare-datatypes`), `const` bindings, `if`/`else` with early returns, ternaries, helper function calls, and `implies(a, b)`.
- Runtime shim (`src/runtime.ts`) exporting zero-cost `law(name, fn)` and `implies(p, q)` so verified files remain valid standard TypeScript.
- CLI (`src/cli.ts`, `tslaw check <files...> [--emit-smt] [--json] [--timeout <ms>]`) reporting `PROVED`, `DISPROVED` (with concrete counterexamples), `UNKNOWN`, `DIALECT ERROR`, and `TYPE ERROR`.
- Soundness regression suite (`test/soundness.test.ts`, fixtures in `test/fixtures/soundness/`): every PROVED law is run on random inputs in JS, every counterexample is replayed in JS, and laws named `FALSE: ...` / `TRUE: ...` must be disproved / proved. Add a fixture for any future false-PROVED bug.
- Examples (`examples/tokens.law.ts`, `examples/bank.law.ts`, `examples/buggy.law.ts`, `examples/unsound.law.ts`) and Vitest integration suite (`test/tslaw.test.ts`; negative dialect fixtures in `test/fixtures/dialect/`).

## Important Decisions
- Opt-in dialect via `"use verified";` directive (like `"use strict";`) rather than forking `tsc`, so verified modules stay standard TypeScript and interoperate with regular TS code.
- Uses `bigint` for verified integers (exact mathematical `Int` in SMT-LIB2) and rejects `number` to avoid IEEE-754 floating-point unsoundness.
- Uses native `z3` binary via SMT-LIB2 stdin/stdout (fast, zero WASM startup overhead); solver binary path is configurable via `TSLAW_Z3` or `--z3`.
- Division/modulo (`/` and `%`) are intentionally not yet enabled in v0.1 because JS truncating division toward zero differs from SMT-LIB2 Euclidean `div`/`mod` on negative operands; planned with explicit trunc-div encoding in a future iteration.

- Soundness invariants for the SMT encoding (each once caused false PROVED verdicts):
  - Functions are identified by their `ts.FunctionDeclaration` node (resolved through the type checker, following import aliases), never by name. Each gets a unique SMT name `fn_<index>_<name>`. Aliased imports (`import { f as g }`) work as a result.
  - `law` and `implies` get special meaning only when they resolve to the real tslaw runtime file (`isVscriptRuntimeFile` in `src/dialect.ts`: this install's `src/runtime.ts` / `dist/runtime.*`, or the same paths in an installed package whose `package.json` name matches ours). Any other function with those names is a normal function.
  - SMT identifiers get uniqueness from an index prefix (`p_<i>_`, `arg_<i>_`, `Rec_<n>_<i>_`), never from the sanitized TS name, because sanitizing is lossy (`a$b` and `a_b` collide) and Z3 silently accepts duplicate `define-fun` parameter names.

- Records with extra fields may flow where a narrower record is expected (TS structural subtyping). Each record shape is a distinct SMT datatype, so `src/smt.ts` converts explicitly (`project`) at call arguments, returns, annotated consts, and ternary branches.
- `@ts-ignore` / `@ts-expect-error` / `@ts-nocheck` are rejected in verified modules (`LAW033`), and Stage 1 also type-checks transitively imported `"use verified";` modules.
- Packaging: published name `tslaw`, CLI `tslaw`, MIT license, `files` = `dist` + README + LICENSE, Node >= 20. Error codes are `LAW###`; the README has the reference table and must be updated when a code is added.
- CI: `.github/workflows/ci.yml` runs build + tests on Node 20 and 22 with apt-installed Z3, and a second job checks the Lean proofs. It has never run; the apt Z3 is older than the local one (5.4.1), and recursion/sequence queries have only been tried locally.

- Law names are JSON-quoted in the SMT comment header; a raw newline there once allowed SMT injection (`(assert false)` proved anything). Never write user-controlled text into the SMT script unescaped.
- Conditions and operands of `!`/`&&`/`||` must be `boolean` (`LAW034`); JS truthiness of `bigint` is not modeled.
- Parameter types reject literal types (`5n`, `true`) via `resolveVType(..., declared = true)`, because they would be quantified as plain `Int`/`Bool`. Expression types still accept them.
- `Readonly<T>` records are recognized through TypeScript's internal symbol `checkFlags` (Readonly = `1 << 3`) in `resolveVType`; re-check this on TypeScript major upgrades (covered by `test/fixtures/soundness/readonly-utility.law.ts`).
- Files without the directive are skipped before type-checking. The checker uses `module: ESNext` + `moduleResolution: Bundler` (accepts `./mod.js` and extensionless imports); the user's own tsconfig is not read.
- The CLI sets `process.exitCode` rather than calling `process.exit()` after output, so large piped output is not truncated.

- Translator fuzzing: `test/fuzz/generate.ts` generates random well-typed verified modules; `test/fuzz.test.ts` runs each function on concrete inputs in JS and requires `f(v) === result` to be PROVED and a perturbed result DISPROVED. Default 10 modules per test run; `TSLAW_FUZZ_SEED` / `TSLAW_FUZZ_RUNS` scale it (300 runs, ~10,800 laws, takes ~80s). Extend the generator whenever the subset grows. Failing programs are left in `test/.generated/` (gitignored).
- Unions whose members all have the same model (`1n | 2n`, two record shapes with identical fields) resolve to that model. Object literals in a position with an expected record type are lowered directly against that type, not via the literal's own inferred type.
- Roadmap toward a defensible "formal verification" claim (user wants all seven, 2026-11-21): (7) translator fuzzing - done; (1) written semantics - done; (2) independent check of Z3's answers - done as `--cross-check` with cvc5 (externally checked proof certificates, e.g. Alethe + carcara, not done); (4) function contracts `requires`/`ensures` - done; (5) runtime guards at the verified boundary - done; (3) recursion with termination measures and induction - done; `while` loops with invariants - done; arrays - done; (6) mechanised proof of the translation for a core calculus in Lean - done (`proofs/Core.lean`). All seven are done as of 2026-11-22.

- `--cross-check` (`VerifyOptions.crossCheck`, `runCvc5` in `src/z3.ts`) runs each query through cvc5 with `--check-proofs --check-models`. Agreement sets `LawResult.crossCheck = "confirmed"`; opposite verdicts become status `error` ("SOLVERS DISAGREE"); cvc5 undecided is `unconfirmed`; Z3 undecided but cvc5 decided is `cvc5-only`. `TSLAW_FUZZ_CROSS_CHECK=1` applies it to the fuzzer. Tests that need the real cvc5 skip when it is not on PATH (CI does not install it).
- Local tooling installed 2026-11-21 for this work: cvc5 1.4.2 (Homebrew cask from the cvc5 tap), Lean 4.36.0 via elan (`~/.elan`).

- Contracts (design agreed with the user 2026-11-21): `requires(cond)` as the first statement(s) of a function, `ensures(fn, (...args, result) => cond)` at top level; both are runtime no-ops like `law`. `src/smt.ts` keeps a `frames` stack (let bindings and path conditions) while lowering and emits one `kind: "requires"` query per call to a function that has `requires`; `ensures` becomes a `kind: "ensures"` query assuming the precondition. Calls are still inlined via `define-fun`, so contracts add proved properties without changing the soundness theorem; item 3 (recursion) will be the first use of a contract in place of a body. Obligations are emitted only for functions declared in the file being checked. Fixtures: `test/fixtures/contracts/`.

- Recursion (2026-11-22). `decreases(m1, ..., mk)` after the `requires` prefix; `VerifiedFunction` carries `decreases`, `prefixLength`, `scc`, `recursive` (Tarjan SCCs in `src/dialect.ts`, callees first, group members adjacent). In `src/smt.ts`:
  - A recursive group is one `define-funs-rec`, each body guarded by its precondition (`ite pre body undef`). That definition is an assumption, contradictory if the function does not terminate, so every query lists the goals it rests on in `LoweredLaw.dependsOn` and `src/verify.ts` withdraws verdicts whose dependencies are not PROVED (after retrying `LoweredLaw.plain`, the same goal without assumed postconditions).
  - Termination goals (`kind: "decreases"`, one per call inside a group) are proved with the group's functions only *declared* (`Pending.opaque`), so they cannot rest on the definition they justify. Order: `a << b` iff `a < b && 0 <= b`, lexicographic.
  - Induction: `ensures` on a recursive function is proved over its inlined body, with each `ensures` of a called recursive function asserted at the call ("facts", `FactScope`). Never assert facts for calls written in the postcondition itself unless the callee cannot reach the function (otherwise `ensures(f, (n, r) => f(n) < 0n)` proves itself). Facts are also asserted in laws and in call-site obligations.
  - Each query contains only the definitions reachable from its goal. Goals of imported modules that a file's verdicts depend on (termination, assumed `ensures`) are re-emitted when checking that file.
  - `implies(p, q)` adds `p` to the path condition only in laws and postconditions. In function bodies both arguments run in JavaScript, and a recursive call outside its precondition may not return (`executable` flag in `src/smt.ts`).
  - Fixtures `test/fixtures/recursion/`, tests `test/recursion.test.ts`; the fuzzer generates recursive functions (bounded to depth 5 so any argument is safe to run).
- Loops and local variables (2026-11-22). `let`, assignment (`= += -= *=`) to `let` locals, `if` branches that fall through, and `while` with `invariant(...)`* then `decreases(...)` at the start of the body. In `src/smt.ts`:
  - Statements without `return` are lowered by `collect`/`collectBlock` to a list of `let` frames plus a new environment (SSA: an assignment binds a fresh name; after an `if` each differing variable gets an `ite`). An `if` containing `return` is lowered continuation-style by `lowerSeq`, which can lower the code after it once per path; `mergeObligations` folds the resulting duplicate goals.
  - A loop is a recursive SMT function over the outer variables it mentions (`defineLoop`, memoized per AST node because bodies are lowered again for `ensures`), in its own unit placed before the enclosing function (`Unit.deps`, emitted in dependency order). The invariant is its precondition; the enclosing function's `requires` is inlined into it. Goals: entry (obligation in the enclosing sink), "kept by the body", termination (opaque). After the loop, `invariant && !condition` is asserted as a fact resting on the "kept" goal (`FactScope.goals` / `Pending.factGoals`).
  - Goals inside a loop use only "strict" facts (postconditions strictly below the enclosing function): the function's termination can depend on the loop, so the loop's goals must never include that function's definition.
  - Every goal with facts also has an `abstract` script (recursive functions and loops declared, not defined), tried first by `src/verify.ts`: Z3 times out unfolding loop definitions on proofs that follow directly from the invariant. Abstract proofs still depend on the termination goals; without that, `while (true)` makes `false` provable after the loop (regression fixtures `forever`, `bottomless`).
  - Functions with loops get `ensures` facts at call sites like recursive ones (`VerifiedFunction.hasLoops`).
  - Fixtures `test/fixtures/loops/`, tests `test/loops.test.ts`; the fuzzer generates loop functions (at most 4 iterations) with assignments under `if`s. `TSLAW_FUZZ_DIR` lets concurrent fuzz runs use separate directories.
- Arrays (2026-11-22). `VType` has `{ kind: "array", element }`, modeled as SMT `(Seq T)` (same syntax in Z3 and cvc5). Verified code uses only the runtime helpers `len`, `at`, `append`, `concat`, `slice`, `withAt` (`ARRAY_HELPERS` in `src/dialect.ts`, recognized like `law`/`implies` only when they resolve to the real runtime); `xs.length`, `xs[i]`, methods, spread and `===` are rejected. `at`/`slice`/`withAt` emit a `requires`-kind obligation at each call and also check at runtime (`RangeError`). Array literals are lowered at the expected element type; a bare `[]` with no expected type is an error. There is no projection between array types (wider record elements to narrower): `project` throws. Counterexamples decode `seq.unit` / `seq.++` / `seq.empty` in `src/z3.ts`. Guards validate and freeze arrays element by element and get local copies of the helpers used in `requires`. Known limit: Z3 times out on goals needing a case split over two symbolic indices (e.g. `withAt` read at another index); cvc5 proves them. Fixtures `test/fixtures/arrays/`, `test/fixtures/guard/basket.ts`; the fuzzer has array types `A` (`readonly bigint[]`) and `AN` (`readonly N[]`).
- Lean proofs (2026-11-22). `proofs/Core.lean` (Lean 4, no Mathlib, toolchain pinned in `proofs/lean-toolchain`; `npm run prove`) models a core of the subset (bigint/boolean expressions with lazy `&&`/`||`/ternary, `implies`, `const`, `if`/`else`, `return`), the translation to solver terms, and proves `tr_correct`/`trBlock_correct` (translation agrees with evaluation), `proved_sound` and `disproved_sound`. It is a model written by hand to mirror `src/smt.ts`, not a proof about the TypeScript; records, calls, contracts, recursion, loops and arrays are outside it. `test/proofs.test.ts` (skipped without Lean) re-checks the file and plants five translation bugs that must each break it. When changing how `src/smt.ts` translates anything in that core, change the Lean model to match. `docs/SEMANTICS.md` section 8 is the canonical description.
- Red-team findings (2026-11-22, an independent adversarial pass over recursion/loops/arrays). Keep these rules:
  - Facts for calls written in a postcondition are allowed only for callees *strictly below* the function (reachable from it and not reaching it). "Cannot reach it" admitted unrelated functions, and two false postconditions about each other proved each other (`test/fixtures/recursion/unrelated.law.ts`).
  - `LoweredLaw.foundations`: the dependencies whose failure withdraws even a DISPROVED verdict. Termination goals for every goal; for `law`/`ensures` also every call-site, loop-entry and loop-kept goal of the goal itself and of all units in its query (`unitChecks`, `Pending.own`). Reason: outside a precondition/invariant the model is unspecified and array helpers throw, so neither verdict means anything there (`test/fixtures/arrays/checks.law.ts`). Call-site goals of imported modules are therefore emitted when a verdict needs them.
  - Array helper calls take their array type from the call's resolved signature, not from the first argument (`append([wide], narrow)`).
  - Property access must name a declared field (`r.constructor` used to pass the subset check).
  - `decreases(...)` on a non-recursive function is rejected (`LAW037`): it was accepted but never lowered, so calls in its arguments had no obligations although JavaScript runs them.
  - Verified modules may not import each other in a cycle (`LAW001`, `IN_PROGRESS` in `src/dialect.ts`): the nested analysis only sees a stub of the module that started it, so recursion across the two files was invisible and lowering crashed.
  - Round 3 bug-hunt findings (2026-11-22):
    - Unary `+` is forbidden (`LAW012`): in JS/TS it cannot apply to `bigint`, only coerces `boolean` to IEEE-754 `number`, and Z3 silently coerced `Bool` to `Int` so float-precision laws could be falsely PROVED.
    - `__proto__` fields, index signatures, construct signatures, and symbol-keyed fields are rejected in `resolveVType` (and `__proto__` in object literals): `{ __proto__: 1n }` does not define an own property in JS, and index signatures let extra object-literal properties bypass TS2353 and get dropped by width subtyping. As defense in depth, `smt.ts` also lowers extra properties of object literals at expected record types so obligations are never dropped.
    - Object destructuring requires a record initializer, identifier keys only (no string/computed keys, which previously let arbitrary side effects bypass the dialect check and read the wrong field in SMT), and declared fields only.
    - Side-effect imports (`import "./x"`), default+named imports, and re-exporting verified functions or runtime helpers through unverified barrel modules are rejected (`LAW001`, which previously skipped Stage 1 typechecking on the re-exported verified target).
    - `vTypeKey` JSON-quotes field names (preventing collisions like `"x:Int,y"` vs `x, y`), field sorting uses deterministic code-unit order instead of `localeCompare`, and `this` parameters are rejected (`LAW005`).
    - Loop maintenance and loop-body obligation queries mark the loop unit `opaque` (they never call `loop_k`), so a failed loop termination does not hide a disproved invariant/precondition.
    - `tslaw guard` chooses a collision-free helper prefix, escapes non-identifier field names in error paths, rejects `Array.isArray(v)` for records, and typechecks transitive verified dependencies via `verifiedDeps`.
    - `z3.ts` attaches a `stdin` error handler, catches solver crashes/signals and cvc5 non-zero stderr failures (`--check-proofs`/`--check-models`), and handles bare `seq.empty` / non-decimal terms safely.
- `TSLAW_DEBUG=1` makes a lowering failure (`LAW090`) print its stack trace.
- Code that TypeScript types as `never` (unreachable, e.g. the right side of `b || ...` after `b = true`) is still lowered: `resolveExprVType` falls back to the declared/branch type (fixture `test/fixtures/soundness/unreachable.law.ts`, found by the fuzzer).
- `tslaw guard <files> [--check]` (`src/guard.ts`, `generateGuards`) writes `<name>.guarded.ts` beside each verified module: one wrapper per exported function that validates runtime types, rebuilds record arguments as frozen copies with only declared fields, evaluates `requires` (source text with callees redirected to `$verified.x` / imported aliases / a local `$implies`), then calls the real function. Generated code is self-contained (no tslaw runtime import) and must pass the strict type check. Committed golden output lives in `test/fixtures/guard/*.guarded.ts`; regenerate it when the generator changes.
- Tests are CPU-heavy (each `verifyFiles` builds a TS program). Under heavy machine load they can exceed the 30s per-test timeout; rerun with `npx vitest run --no-file-parallelism --testTimeout=300000` before assuming a real failure.

## Open Questions / Known Gaps
- `package.json` `repository` assumes `github.com/Joshua-Wright76/tslaw`; that repo does not exist yet, and CI has never run on GitHub.
- `AGENTS.md` and this file describe a personal agent workflow (the preview-port step does not apply to a CLI); decide whether to keep them in the public repo.
- Division/modulo with exact JS truncation-toward-zero semantics is not yet lowered.
- Immutable fixed-length tuples and unions/discriminated enums are not supported.
- Optional WASM fallback (`z3-solver`) for machines without native `z3` installed is not yet wired.

## Notes For The Next Agent
- Run `npm run build && npm test` to validate changes. Tests take about a minute (each `verifyFiles` builds a TS program); `vitest.config.ts` sets a 30s timeout and excludes `.worktrees/`.
- Try the CLI on examples:
  - `node dist/cli.js check examples/tokens.law.ts examples/bank.law.ts`
  - `node dist/cli.js check examples/buggy.law.ts`
  - `node dist/cli.js check examples/unsound.law.ts`
- Requires `z3` on `PATH` (installed via Homebrew at `/opt/homebrew/bin/z3`).
