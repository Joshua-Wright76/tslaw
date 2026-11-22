# tslaw

**Verified TypeScript.** Write `law(...)`s about your pure TypeScript functions, and tslaw asks the [Z3](https://github.com/Z3Prover/z3) theorem prover whether they hold for *every possible input*. If a law is false, you get a concrete counterexample.

Verified modules opt in with a `"use verified";` directive and stay ordinary TypeScript: there is no compiler fork, and the rest of your code imports them as usual.

```ts
"use verified";

import { law, implies } from "tslaw/runtime";

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

```
$ tslaw check bank.law.ts
bank.law.ts
  PROVED    "withdraw never overdrafts" (41ms)
```

Forget a check, and the law is refuted with inputs you can paste into a test:

```
  DISPROVED "balances never go negative" (50ms) at buggy.law.ts:26
            Counterexample: from = 0n, to = 8855n, amount = -8856n
```

> **Status: early prototype (0.1).** The supported language subset is small, and the verifier has had soundness bugs. Read [What PROVED means](#what-proved-means) before relying on it.

## Install

```sh
npm install --save-dev tslaw
```

Requirements:

- Node.js 20 or newer.
- The `z3` binary on your `PATH` (`brew install z3`, `apt-get install z3`, or a [release build](https://github.com/Z3Prover/z3/releases)). To use a binary elsewhere, pass `--z3 /path/to/z3` or set `TSLAW_Z3`.

## Usage

```
tslaw check <file1.ts> [file2.ts ...] [options]

  --emit-smt         Print the generated SMT-LIB2 for each law
  --json             Output a machine-readable JSON report
  --timeout <ms>     Per-law Z3 timeout in ms (default: 5000)
  --z3 <path>        Path to the z3 binary (default: TSLAW_Z3 or 'z3')
  --all              Check files even without a "use verified"; directive
```

The exit code is `0` only if every law is proved and there are no errors, so it can gate CI.

Each law gets one of these verdicts:

| Verdict | Meaning |
|---|---|
| `PROVED` | Z3 showed that no input can make the law return `false`. |
| `DISPROVED` | Z3 found an input that makes the law `false`, shown as a counterexample. |
| `UNKNOWN` | Z3 gave up or timed out. Nothing is known either way. |
| `ERROR` | Z3 could not run, or rejected the generated query. |

There is also a programmatic API: `import { verifyFiles } from "tslaw"`.

## How it works

For a two-minute animated walkthrough, open [`docs/explainer.html`](docs/explainer.html) in a browser.

Each file goes through three stages. A failure at any stage stops that file.

1. **Type check.** The file and the verified modules it imports are type-checked with `strict`, `noUncheckedIndexedAccess` and `exactOptionalPropertyTypes`.
2. **Dialect check.** A `"use verified";` module may only use a pure, terminating subset of TypeScript that has an exact meaning in logic. See [The verified subset](#the-verified-subset).
3. **Proof.** Functions and laws are translated to SMT-LIB2. For each law, Z3 is asked whether any input makes it false: "no" (`unsat`) is a proof, "yes" (`sat`) comes with the counterexample.

## The verified subset

**Types**

- `bigint`, modeled as a mathematical integer (exact, unbounded).
- `boolean`.
- Records whose fields are all `readonly` (written out, or via `Readonly<...>`) and themselves supported types. Passing a record with extra fields where fewer are expected is allowed, as in TypeScript.

**Code**

- Top level: `type`/`interface` declarations, function declarations, and `law(name, predicate)` calls.
- Functions need explicit parameter and return types.
- `const` bindings (including object destructuring), `if`/`else` where every path returns, ternaries.
- Operators: `+ - *`, comparisons, `===`/`!==` on `bigint` and `boolean`, `&& || !`.
- Calls to other verified functions, and `implies(p, q)`.
- Imports: `law`/`implies` from `tslaw/runtime`, types from anywhere, and functions from other `"use verified";` modules.

**Not allowed**

- `number` (floating point cannot be modeled exactly; use `bigint`), `any`, `unknown`, `null`/`undefined`, unions, arrays, tuples, strings.
- `let`/`var`, assignment, loops, recursion, `throw`/`try`, `async`, generics, classes.
- Casts (`as`, `!`) and `@ts-ignore`-style comments.
- `/` and `%` (JavaScript rounds toward zero and Z3 does not; not yet supported).
- `===` on records (JavaScript compares identity, not contents; compare fields instead).

## What PROVED means

`PROVED` is a statement about a mathematical model of your code. It is worth exactly as much as the following assumptions:

- **Only the laws are proved.** tslaw does not check that your laws say what you meant, or that they cover the behavior you care about.
- **`law` does nothing at runtime.** It is a no-op, so laws cost nothing in production and are never executed there.
- **Callers outside verified modules are not checked.** A law is proved for all *well-typed* inputs. Unverified code can still call a verified function with values that break its types (through `any`, casts, or plain JavaScript), and nothing stops it at runtime.
- **Preconditions are yours to enforce.** A law of the form `implies(x >= 0n, ...)` says nothing about negative `x`.
- **The verifier is trusted.** A proof depends on tslaw's translation to SMT, the TypeScript compiler, and Z3 all being correct. tslaw itself is young.

To keep that last point honest, the test suite cross-checks verdicts against real execution: every proved law is run on random inputs, every counterexample is replayed, and `test/fixtures/soundness/` holds a regression case for each known way tslaw was once tricked into proving something false.

**If tslaw proves a law that fails when you run it, that is the most serious kind of bug. Please [open an issue](https://github.com/Joshua-Wright76/tslaw/issues) with the smallest file that reproduces it.**

## Error codes

Codes starting with `TS` come from the TypeScript compiler. The rest are tslaw's.

| Code | Meaning |
|---|---|
| `LAW000` | File not found or unreadable. |
| `LAW001` | Disallowed import: default or namespace import, a value from an unverified module, or `law`/`implies` not from the tslaw runtime. |
| `LAW002` | Anonymous top-level function. |
| `LAW003` | `async`, generator, generic, or body-less function. |
| `LAW004` | Function return type is missing or not a supported type. |
| `LAW005` | Parameter is optional, rest, defaulted, destructured, or has no type annotation. |
| `LAW006` | Parameter has an unsupported type (including literal types such as `5n` or `true`). |
| `LAW010` | `number` literal; write a `bigint` literal such as `1n`. |
| `LAW011` | Identifier is not a parameter or local `const` (globals are forbidden). |
| `LAW012` | Mutating or bitwise unary operator (`++`, `--`, `~`). |
| `LAW013` | Division or modulo (not yet supported). |
| `LAW014` | Any other unsupported binary operator. |
| `LAW015` | `===`/`!==` used on records. |
| `LAW016` | Property access on something that is not a verified record. |
| `LAW017` | Object literal with a computed key, spread, getter, setter, or method. |
| `LAW018` | Call to something that is not a verified function, or `implies` with the wrong number of arguments. |
| `LAW019` | Type assertion (`as`, `<T>x`, `x!`). |
| `LAW020` | Any other unsupported expression. |
| `LAW021` | Unreachable statement after `return`. |
| `LAW022` | `let`/`var`, a `const` without an initializer, or an unsupported destructuring pattern. |
| `LAW023` | Local `const` has an unsupported type. |
| `LAW024` | Bare `return;`. |
| `LAW025` | An `if` whose branches do not all return, or with an unsupported branch form. |
| `LAW026` | Loop. |
| `LAW027` | `throw` or `try`. |
| `LAW028` | Any other unsupported statement. |
| `LAW029` | Function or law body does not return on every path. |
| `LAW030` | Malformed `law(...)`: needs a string literal name and a non-async function. |
| `LAW031` | Unsupported top-level statement. |
| `LAW032` | Recursion (direct or through other functions). |
| `LAW033` | `@ts-ignore`, `@ts-expect-error`, or `@ts-nocheck` comment. |
| `LAW034` | A non-`boolean` (such as a `bigint`) used as a condition or as an operand of `!`, `&&`, `||`. |
| `LAW090` | Internal: translation to SMT failed. Please report it. |

## Development

```sh
git clone https://github.com/Joshua-Wright76/tslaw.git
cd tslaw
npm install
npm run build
npm test          # needs z3 on PATH; takes about 30 seconds

node dist/cli.js check examples/tokens.law.ts examples/bank.law.ts   # all proved
node dist/cli.js check examples/buggy.law.ts                         # a counterexample
node dist/cli.js check examples/unsound.law.ts                       # dialect errors
node dist/cli.js check examples/tokens.law.ts --emit-smt             # see the SMT-LIB2
```

Files in `examples/` import the runtime by relative path (`../src/runtime.js`) so they work inside this repository; in your own project, import `tslaw/runtime`.

Layout: `src/dialect.ts` (subset checker), `src/smt.ts` (translation to SMT-LIB2), `src/z3.ts` (solver runner), `src/verify.ts` (pipeline), `src/cli.ts`.

## License

[MIT](LICENSE)
