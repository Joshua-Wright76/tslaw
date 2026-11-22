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

## Current State
Initial prototype (`0.1.0`) implementing **vscript**, a strict verifiable subset of TypeScript checked at compile time with Z3.

Implemented:
- Three-stage verification pipeline (`src/verify.ts`):
  1. Strict TypeScript typechecking via the TypeScript Compiler API (`strict`, `noUncheckedIndexedAccess`, `exactOptionalPropertyTypes`).
  2. Strict dialect / soundness checker (`src/dialect.ts`) for `"use verified";` modules (bans `any`, casts, mutation, loops, `throw`/`try`, `number` floats, side effects, and recursive cycles).
  3. SMT-LIB2 lowering (`src/smt.ts`) and Z3 solver runner (`src/z3.ts`) supporting `bigint` (`Int`), `boolean` (`Bool`), immutable `readonly` record types (`declare-datatypes`), `const` bindings, `if`/`else` with early returns, ternaries, helper function calls, and `implies(a, b)`.
- Runtime shim (`src/runtime.ts`) exporting zero-cost `law(name, fn)` and `implies(p, q)` so verified files remain valid standard TypeScript.
- CLI (`src/cli.ts`, `vscript check <files...> [--emit-smt] [--json] [--timeout <ms>]`) reporting `PROVED`, `DISPROVED` (with concrete counterexamples), `UNKNOWN`, `DIALECT ERROR`, and `TYPE ERROR`.
- Examples (`examples/tokens.law.ts`, `examples/bank.law.ts`, `examples/buggy.law.ts`, `examples/unsound.law.ts`) and Vitest integration suite (`test/vscript.test.ts`).

## Important Decisions
- Opt-in dialect via `"use verified";` directive (like `"use strict";`) rather than forking `tsc`, so verified modules stay standard TypeScript and interoperate with regular TS code.
- Uses `bigint` for verified integers (exact mathematical `Int` in SMT-LIB2) and rejects `number` to avoid IEEE-754 floating-point unsoundness.
- Uses native `z3` binary via SMT-LIB2 stdin/stdout (fast, zero WASM startup overhead); solver binary path is configurable via `VSCRIPT_Z3` or `--z3`.
- Division/modulo (`/` and `%`) are intentionally not yet enabled in v0.1 because JS truncating division toward zero differs from SMT-LIB2 Euclidean `div`/`mod` on negative operands; planned with explicit trunc-div encoding in a future iteration.

## Open Questions / Known Gaps
- Division/modulo with exact JS truncation-toward-zero semantics is not yet lowered.
- Immutable fixed-length tuples, unions/discriminated enums, and bounded arrays are planned next steps.
- Boundary wrapper generation (auto-emitting runtime validation guards for calls from unverified TS into `"use verified";` modules) is not yet implemented.
- Optional WASM fallback (`z3-solver`) for machines without native `z3` installed is not yet wired.

## Notes For The Next Agent
- Run `npm run build && npm test` to validate changes.
- Try the CLI on examples:
  - `node dist/cli.js check examples/tokens.law.ts examples/bank.law.ts`
  - `node dist/cli.js check examples/buggy.law.ts`
  - `node dist/cli.js check examples/unsound.law.ts`
- Requires `z3` on `PATH` (installed via Homebrew at `/opt/homebrew/bin/z3`).
