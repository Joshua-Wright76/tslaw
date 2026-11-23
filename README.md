# tslaw

**Verified TypeScript.** Write `law(...)`s about your pure TypeScript functions, and tslaw asks the [Z3](https://github.com/Z3Prover/z3) theorem prover whether they hold for *every possible input*. If a law is false, you get a concrete counterexample.

Verified modules opt in with a `"use verified";` directive and stay ordinary TypeScript: there is no compiler fork, and the rest of your code imports them as usual.

```ts
"use verified";

import { law, implies } from "@joshua_wright76/tslaw/runtime";

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
npm install --save-dev @joshua_wright76/tslaw
```

Requirements:

- Node.js 20 or newer.
- The `z3` binary on your `PATH` (`brew install z3` or a [release build](https://github.com/Z3Prover/z3/releases)). To use a binary elsewhere, pass `--z3 /path/to/z3` or set `TSLAW_Z3`. Distribution packages can be years old: Ubuntu's `apt` Z3 times out on array and recursion proofs that a current release settles in milliseconds. CI uses Z3 5.4.1 and cvc5 1.4.2.

## Usage

```
tslaw check <file1.ts> [file2.ts ...] [options]

  --emit-smt         Print the generated SMT-LIB2 for each law
  --json             Output a machine-readable JSON report
  --timeout <ms>     Per-law Z3 timeout in ms (default: 5000)
  --z3 <path>        Path to the z3 binary (default: TSLAW_Z3 or 'z3')
  --all              Check files even without a "use verified"; directive
  --cross-check      Also run every law through cvc5 and require it to agree with Z3
  --cvc5 <path>      Path to the cvc5 binary (default: TSLAW_CVC5 or 'cvc5')
```

### Cross-checking with a second solver

With `--cross-check`, every law is also sent to [cvc5](https://cvc5.github.io/), a solver developed independently of Z3. For a proof, cvc5 must produce its own proof and pass it through its internal proof checker; for a counterexample, it must find one and validate it. Each verdict is then marked:

- `confirmed by cvc5`: both solvers agree.
- `NOT confirmed`: cvc5 could not decide in time, so the verdict rests on Z3 alone.
- `by cvc5 only`: Z3 could not decide, and the verdict is cvc5's.

If the two solvers ever give opposite answers, the law is reported as an error instead of a verdict. This guards against a bug in either solver; it does not check tslaw's own translation, which both solvers receive identically.

The exit code is `0` only if every law is proved and there are no errors, so it can gate CI.

Each law gets one of these verdicts:

| Verdict | Meaning |
|---|---|
| `PROVED` | Z3 showed that no input can make the law return `false`. |
| `DISPROVED` | Z3 found an input that makes the law `false`, shown as a counterexample. |
| `UNKNOWN` | Z3 gave up or timed out. Nothing is known either way. |
| `ERROR` | Z3 could not run, or rejected the generated query. |

### Contracts

A function can state what it needs from its callers and what it guarantees in return:

```ts
import { requires, ensures } from "@joshua_wright76/tslaw/runtime";

export function withdraw(acc: Account, amount: bigint): Account {
  requires(amount > 0n && amount <= acc.balance);
  return { balance: acc.balance - amount, frozen: acc.frozen };
}

ensures(withdraw, (acc, amount, result) => result.balance === acc.balance - amount);
```

- `requires(cond)` must come first in the function body. tslaw proves, for **every call from verified code**, that the condition holds at that call, taking into account the `if`, ternary, `&&`, `||` and `implies` conditions around it. A call that can violate it is reported as `DISPROVED "requires of withdraw at line N"` with the arguments that break it. Laws and postconditions about code that contains such a call get no verdict (`UNKNOWN`, "relies on ...") until it is fixed, so in a law you state the precondition as a hypothesis: `implies(amount > 0n && amount <= acc.balance, ...)`.
- `ensures(fn, (...args, result) => cond)` is proved for all arguments that satisfy the function's `requires`.
- Both do nothing at runtime, like `law`. They do not stop unverified code from calling the function with bad arguments; for that, see the next section.

### Recursion

A function may call itself (or a group of functions each other) if it states a measure that shrinks:

```ts
import { decreases, ensures, implies, law } from "@joshua_wright76/tslaw/runtime";

export function sum(n: bigint): bigint {
  decreases(n);
  if (n <= 0n) return 0n;
  return n + sum(n - 1n);
}

ensures(sum, (n, result) => implies(n >= 0n, 2n * result === n * (n + 1n)));

law("sum is never negative", (n: bigint) => sum(n) >= 0n);
```

- `decreases(m)` comes right after the `requires` statements. For every recursive call, tslaw proves that the callee's measure is strictly smaller than the caller's and that the caller's is at least zero, so the recursion cannot go on forever. This is reported as `"termination of sum: call to sum at line N"`. With several measures, `decreases(a, b)`, they are compared in order, so `b` may grow whenever `a` shrinks.
- A recursive function without a measure is rejected, and so is a measure on a function that is not recursive. Mutually recursive functions must be in one module: verified modules may not import each other in a cycle.
- A function whose measure cannot be proved to shrink is reported as `DISPROVED` or `UNKNOWN`, and every verdict that used its definition is withdrawn (`UNKNOWN`, "relies on ..."), because a definition that does not terminate can be used to prove anything.
- **Properties for all inputs go in `ensures`.** Z3 does not do induction by itself. tslaw proves an `ensures` on a recursive function by assuming it for the recursive calls (which are at smaller measures) and proving it for the body: that is induction. Once proved, the postcondition is available at every call to the function, which is how the law above gets proved.
- Laws about specific values, such as `sum(4n) === 10n`, are proved by unfolding the definition.
- If an `ensures` fails, proofs that assumed it are retried without it and withdrawn if that does not work.

Limits: only the `ensures` of the function being called are used, exactly at its call sites, so a property that needs a cleverer induction has to be restated as an `ensures` of a helper. Deep recursion can still overflow the JavaScript stack at runtime; a termination proof says the recursion ends, not that it fits.

### Loops and local variables

Function bodies may use `let`, assignment (`=`, `+=`, `-=`, `*=`) and `while`:

```ts
import { decreases, ensures, invariant, requires } from "@joshua_wright76/tslaw/runtime";

export function sumTo(n: bigint): bigint {
  requires(n >= 0n);
  let i = 0n;
  let acc = 0n;
  while (i < n) {
    invariant(0n <= i && i <= n);
    invariant(2n * acc === i * (i + 1n));
    decreases(n - i);
    i += 1n;
    acc += i;
  }
  return acc;
}

ensures(sumTo, (n, result) => 2n * result === n * (n + 1n));
```

A loop body starts with any number of `invariant(cond)` statements and then one `decreases(...)`. For each loop tslaw proves three things, reported separately:

- `"invariant of the loop at line N: holds on entry"`
- `"invariant of the loop at line N: kept by the body"` (assuming the invariant and the loop condition before an iteration, the invariant holds after it)
- `"termination of the loop at line N"` (each iteration makes the measure smaller, and it was at least zero)

In exchange, after the loop the invariant and the negation of the loop condition are known. That is *all* that is known about the variables the loop changed, so the invariant has to say everything the code after the loop needs. In the example, `i <= n` and "not `i < n`" give `i === n`, and the second invariant then gives the postcondition.

The enclosing function's `requires` is part of every invariant automatically. Other facts about variables the loop does not change (for example from an `if` around the loop) have to be repeated in an invariant.

Not supported: `for` and `do` loops, `break`, `continue`, `return` inside a loop, loops inside `law` or `ensures` callbacks, and assigning to parameters or record fields. Records stay immutable: `acc = { ...}` replaces the whole value.

### Arrays

Arrays of supported types (`readonly T[]`, `ReadonlyArray<T>` or `T[]`) are supported through six helpers, because the built-in operations either involve `number` or silently produce `undefined`:

```ts
import { append, at, concat, len, slice, withAt } from "@joshua_wright76/tslaw/runtime";

len(xs)              // number of elements, as a bigint
at(xs, i)            // element i            requires 0n <= i && i < len(xs)
append(xs, x)        // new array: xs then x
concat(xs, ys)       // new array: xs then ys
slice(xs, from, to)  // new array            requires 0n <= from && from <= to && to <= len(xs)
withAt(xs, i, x)     // new array, i replaced  requires 0n <= i && i < len(xs)
```

- The ones with a precondition are checked like any `requires`: `DISPROVED "requires of at at line N"` comes with an array and an index that go out of range. At runtime they also check, and throw `RangeError` instead of returning `undefined`.
- None of them changes its argument; verified code has no way to mutate an array.
- Array literals `[a, b, c]` work wherever the element type is known. A bare `[]` needs a type annotation.
- Laws can quantify over arrays, and counterexamples are shown as arrays (`xs = [3n, 1n]`).

Statements about every element are written with recursion or loops, since there are no quantifiers:

```ts
export function sumPrefix(xs: readonly bigint[], n: bigint): bigint {
  requires(0n <= n && n <= len(xs));
  decreases(n);
  return n === 0n ? 0n : sumPrefix(xs, n - 1n) + at(xs, n - 1n);
}

export function sum(xs: readonly bigint[]): bigint {
  let i = 0n;
  let acc = 0n;
  while (i < len(xs)) {
    invariant(0n <= i && i <= len(xs) && acc === sumPrefix(xs, i));
    decreases(len(xs) - i);
    acc += at(xs, i);
    i += 1n;
  }
  return acc;
}

ensures(sum, (xs, result) => result === sumPrefix(xs, len(xs)));
```

Limits: no `xs.length`, `xs[i]`, methods, spread, or `===` on arrays; no tuples; an array of records with extra fields cannot be passed where an array of a narrower record type is expected. Z3 is weaker on arrays than on integers: a law that needs a case split on two symbolic indices (such as "`withAt(xs, i, v)` read at `j`") may come back `UNKNOWN` until it is stated case by case. cvc5 is stronger here, so `--cross-check` can decide some of those ("by cvc5 only").

### Guarding the boundary

Proofs cover calls from verified code. Anything else (plain JavaScript, values typed `any`, parsed JSON) can still call a verified function with arguments that break its types or its `requires`. `tslaw guard` generates a checked entry point for those callers:

```sh
tslaw guard src/bank.ts        # writes src/bank.guarded.ts
tslaw guard src/bank.ts --check   # for CI: fail if the file on disk is missing or stale
```

`bank.guarded.ts` exports a wrapper for each exported function of `bank.ts`. Each wrapper checks every argument's runtime type field by field and element by element, copies records and arrays into frozen objects that hold only the declared fields (so a getter or later mutation cannot change what was checked), evaluates the `requires` conditions, and then calls the verified function. A bad type throws `TypeError`; a violated precondition throws `RangeError`.

Import from `./bank.guarded.js` in unverified code and from `./bank.js` in verified code. A function used inside a `requires` must be exported so the wrapper can call it.

There is also a programmatic API: `import { verifyFiles } from "@joshua_wright76/tslaw"`.

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
- Arrays of supported types, used through `len`, `at`, `append`, `concat`, `slice`, `withAt`.

**Code**

- Top level: `type`/`interface` declarations, function declarations, and `law(name, predicate)` / `ensures(fn, postcondition)` calls.
- Recursion, direct or mutual, with a `decreases(...)` measure.
- Functions need explicit parameter and return types.
- `const` and `let` bindings (`const` also with object destructuring), assignment to `let` variables, `if`/`else`, ternaries. Every path through a function must end in `return`.
- `while` loops with `invariant(...)` and `decreases(...)`.
- Operators: `+ - *`, comparisons, `===`/`!==` on `bigint` and `boolean`, `&& || !`.
- Calls to other verified functions, `implies(p, q)`, and the array helpers.
- Imports: `law`, `implies`, `requires`, `ensures`, `decreases`, `invariant` and the array helpers from `@joshua_wright76/tslaw/runtime`, types from anywhere, and functions from other `"use verified";` modules.

**Not allowed**

- `number` (floating point cannot be modeled exactly; use `bigint`), `any`, `unknown`, `null`/`undefined`, unions, tuples, strings.
- `var`, assignment to anything but a local `let`, `for`/`do` loops, `break`/`continue`, `throw`/`try`, `async`, generics, classes.
- Casts (`as`, `!`) and `@ts-ignore`-style comments.
- `/` and `%` (JavaScript rounds toward zero and Z3 does not; not yet supported).
- `===` on records and arrays (JavaScript compares identity, not contents; compare fields or elements instead).

## What PROVED means

`PROVED` is a statement about a mathematical model of your code. It is worth exactly as much as the following assumptions:

- **Only the laws are proved.** tslaw does not check that your laws say what you meant, or that they cover the behavior you care about.
- **`law` does nothing at runtime.** It is a no-op, so laws cost nothing in production and are never executed there.
- **Callers outside verified modules are not checked, unless they go through a guard.** A law is proved for all *well-typed* inputs. Unverified code can still call a verified function directly with values that break its types (through `any`, casts, or plain JavaScript). The wrappers from `tslaw guard` close this gap for callers that use them.
- **Preconditions are yours to enforce.** A law of the form `implies(x >= 0n, ...)` says nothing about negative `x`.
- **The verifier is trusted.** A proof depends on tslaw's translation to SMT, the TypeScript compiler, and Z3 all being correct. tslaw itself is young.

To keep that last point honest, the test suite cross-checks verdicts against real execution: every proved law is run on random inputs, every counterexample is replayed, and `test/fixtures/soundness/` holds a regression case for each known way tslaw was once tricked into proving something false.

The translation itself is also fuzzed: `test/fuzz.test.ts` generates random programs in the verified subset, runs them in JavaScript, and requires the prover to agree with every result (`TSLAW_FUZZ_RUNS=300 npm test -- test/fuzz.test.ts` for a longer run).

[`docs/SEMANTICS.md`](docs/SEMANTICS.md) defines precisely what the subset means, how it is translated for Z3, and what a proof depends on.

For a core of the subset (integers, booleans, the operators, `const`, `if`/`else`), the claim "if the solver says `unsat`, the law holds for every well-typed input" is itself machine-checked: [`proofs/Core.lean`](proofs/Core.lean) is a Lean 4 proof that the translation agrees with JavaScript evaluation and that both verdicts are sound. It covers a model of the translator, not the TypeScript code, and it does not cover records, calls, contracts, recursion, loops or arrays; section 8 of the semantics document says exactly what it does and does not establish.

**If tslaw proves a law that fails when you run it, that is the most serious kind of bug. Please [open an issue](https://github.com/Joshua-Wright76/tslaw/issues) with the smallest file that reproduces it.**

## Error codes

Codes starting with `TS` come from the TypeScript compiler. The rest are tslaw's.

| Code | Meaning |
|---|---|
| `LAW000` | File not found or unreadable. |
| `LAW001` | Disallowed import: side-effect, default, or namespace import, a value from or re-exported through an unverified module, `law`/`implies` not from the tslaw runtime, or two verified modules importing each other. |
| `LAW002` | Anonymous top-level function. |
| `LAW003` | `async`, generator, generic, or body-less function. |
| `LAW004` | Function return type is missing or not a supported type. |
| `LAW005` | Parameter is optional, rest, defaulted, destructured, or has no type annotation. |
| `LAW006` | Parameter has an unsupported type (including literal types such as `5n` or `true`). |
| `LAW010` | `number` literal; write a `bigint` literal such as `1n`. |
| `LAW011` | Identifier is not a parameter or local `const` (globals are forbidden). |
| `LAW012` | Disallowed unary operator (`+`, `++`, `--`, `~`; only `-` and `!` are allowed). |
| `LAW013` | Division or modulo (not yet supported). |
| `LAW014` | Any other unsupported binary operator. |
| `LAW015` | `===`/`!==` used on records or arrays. |
| `LAW016` | Property access on something that is not a verified record (including `xs.length` and array methods). |
| `LAW017` | Object literal with a computed key, spread, getter, setter, or method. |
| `LAW018` | Call to something that is not a verified function, or `implies` with the wrong number of arguments. |
| `LAW019` | Type assertion (`as`, `<T>x`, `x!`). |
| `LAW020` | Any other unsupported expression. |
| `LAW021` | Unreachable statement after `return`. |
| `LAW022` | `var`, a declaration without an initializer, or an unsupported destructuring pattern. |
| `LAW023` | Local `const` has an unsupported type. |
| `LAW024` | Bare `return;`. |
| `LAW025` | An `if` branch that is not a block, a `return`, an assignment, or another `if`. |
| `LAW026` | A `for`/`do` loop, or a loop outside a function body (in a `law` or `ensures` callback). |
| `LAW027` | `throw` or `try`. |
| `LAW028` | Any other unsupported statement. |
| `LAW029` | Function or law body does not return on every path. |
| `LAW030` | Malformed `law(...)`: needs a string literal name and a non-async function. |
| `LAW031` | Unsupported top-level statement. |
| `LAW032` | A recursive function (direct or through other functions) without a `decreases(...)` measure. |
| `LAW033` | `@ts-ignore`, `@ts-expect-error`, or `@ts-nocheck` comment. |
| `LAW034` | A non-`boolean` (such as a `bigint`) used as a condition or as an operand of `!`, `&&`, `||`. |
| `LAW035` | `requires(...)` that is not at the start of a function body, or with the wrong arguments. |
| `LAW036` | Malformed `ensures(...)`: needs a verified function and a callback taking its parameters plus the result. |
| `LAW037` | Malformed `decreases(...)`: not directly after the `requires` statements, repeated, a non-`bigint` measure, on a function that is not recursive, a different number of measures than the other functions in the same recursion, or a `requires`/`decreases` that calls the recursion itself. |
| `LAW038` | Malformed loop or assignment: no `decreases(...)` at the start of the loop body, misplaced `invariant(...)`, `return` inside a loop, assignment to something that is not a local `let`, or a loop in a recursive function that calls back into the recursion. |
| `LAW039` | Unsupported array use: `xs[i]`, spread or holes in a literal, or an array helper with the wrong arguments or an array whose element type is unknown (such as a bare `[]`). |
| `LAW040` | `tslaw guard` cannot generate a wrapper: the module is not verified, or a `requires` calls a function that is not exported. |
| `LAW090` | Internal: translation to SMT failed. Please report it. |

## Development

```sh
git clone https://github.com/Joshua-Wright76/tslaw.git
cd tslaw
npm install
npm run build
npm test          # needs z3 on PATH; takes about a minute
npm run prove     # optional: check proofs/Core.lean (needs Lean 4, https://lean-lang.org/install/)

node dist/cli.js check examples/tokens.law.ts examples/bank.law.ts examples/math.law.ts examples/ledger.law.ts  # all proved
node dist/cli.js check examples/buggy.law.ts                         # a counterexample
node dist/cli.js check examples/unsound.law.ts                       # dialect errors
node dist/cli.js check examples/tokens.law.ts --emit-smt             # see the SMT-LIB2
```

Files in `examples/` import the runtime by relative path (`../src/runtime.js`) so they work inside this repository; in your own project, import `@joshua_wright76/tslaw/runtime`.

Tests that need cvc5 or Lean are skipped when those are not installed.

Layout: `src/dialect.ts` (subset checker), `src/smt.ts` (translation to SMT-LIB2), `src/z3.ts` (solver runner), `src/verify.ts` (pipeline), `src/guard.ts` (runtime guards), `src/cli.ts`, `proofs/` (Lean).

## License

[MIT](LICENSE)
