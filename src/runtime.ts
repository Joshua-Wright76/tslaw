/**
 * tslaw runtime helpers.
 *
 * At runtime, `law`, `requires`, `decreases`, `invariant` and `ensures` are no-ops (they are proved statically by
 * `tslaw check`).
 * `implies(p, q)` is standard logical implication (`!p || q`) so laws can also be executed
 * directly in JS/tests against concrete inputs or Z3 counterexamples.
 */

export type LawFn = (...args: never[]) => boolean;

/**
 * Declare a formal invariant proved statically by `tslaw check` across all inputs.
 * At runtime this is a no-op.
 */
export function law<F extends (...args: any[]) => boolean>(
  _name: string,
  _predicate: F,
): void {
  // Proved at compile time by tslaw.
}

/**
 * Declare a precondition of the enclosing verified function. Must be the first statement(s)
 * of the function body.
 *
 * `tslaw check` proves that every call from verified code satisfies it. At runtime this is a
 * no-op: it does not stop unverified callers (use `tslaw guard` for a checking wrapper).
 */
export function requires(_condition: boolean): void {
  // Proved at every verified call site by tslaw.
}

/**
 * Declare the termination measure of a recursive verified function. Must directly follow the
 * function's `requires` statements (or be the first statement when it has none).
 *
 * `tslaw check` proves that at every recursive call the measure gets strictly smaller while
 * the caller's measure is at least zero. With several measures they are compared in order
 * (lexicographically). At runtime this is a no-op.
 */
export function decreases(..._measures: bigint[]): void {
  // Proved at every recursive call by tslaw.
}

/**
 * Declare a loop invariant. Must be the first statement(s) of a `while` loop body.
 *
 * `tslaw check` proves that the condition holds when the loop is first reached and that every
 * iteration keeps it. In exchange it is known to hold (together with the negated loop
 * condition) after the loop. At runtime this is a no-op.
 */
export function invariant(_condition: boolean): void {
  // Proved at loop entry and for every iteration by tslaw.
}

/**
 * Declare a postcondition of a verified function: `post(...args, result)` must hold for all
 * arguments that satisfy the function's `requires`. At runtime this is a no-op.
 */
export function ensures<A extends unknown[], R>(
  _fn: (...args: A) => R,
  _post: (...args: [...A, R]) => boolean,
): void {
  // Proved at compile time by tslaw.
}

// ---------------------------------------------------------------------------
// Arrays
//
// Verified code cannot use `xs.length` or `xs[i]`: both involve `number`, and `xs[i]` is
// `undefined` when `i` is out of range. These helpers work with `bigint` instead, and the ones
// that take an index have a precondition that `tslaw check` proves at every call. At runtime
// they check it too and throw `RangeError`, so an unverified caller cannot read out of range.
// None of them changes its argument.
// ---------------------------------------------------------------------------

function inRange(name: string, ok: boolean, detail: string): void {
  if (!ok) throw new RangeError(`${name}: ${detail}`);
}

/** The number of elements of `xs`. */
export function len<T>(xs: ReadonlyArray<T>): bigint {
  return BigInt(xs.length);
}

/** Element `index` of `xs`. Requires `0n <= index && index < len(xs)`. */
export function at<T>(xs: ReadonlyArray<T>, index: bigint): T {
  inRange("at", index >= 0n && index < BigInt(xs.length), `index ${index} is out of range for length ${xs.length}`);
  return xs[Number(index)] as T;
}

/** A new array: `xs` followed by `x`. */
export function append<T>(xs: ReadonlyArray<T>, x: T): ReadonlyArray<T> {
  return [...xs, x];
}

/** A new array: `xs` followed by `ys`. */
export function concat<T>(xs: ReadonlyArray<T>, ys: ReadonlyArray<T>): ReadonlyArray<T> {
  return [...xs, ...ys];
}

/**
 * A new array with elements `from` (inclusive) to `to` (exclusive) of `xs`.
 * Requires `0n <= from && from <= to && to <= len(xs)`.
 */
export function slice<T>(xs: ReadonlyArray<T>, from: bigint, to: bigint): ReadonlyArray<T> {
  inRange("slice", from >= 0n && from <= to && to <= BigInt(xs.length), `range ${from}..${to} is out of range for length ${xs.length}`);
  return xs.slice(Number(from), Number(to));
}

/**
 * A new array equal to `xs` except that element `index` is `value`.
 * Requires `0n <= index && index < len(xs)`.
 */
export function withAt<T>(xs: ReadonlyArray<T>, index: bigint, value: T): ReadonlyArray<T> {
  inRange("withAt", index >= 0n && index < BigInt(xs.length), `index ${index} is out of range for length ${xs.length}`);
  const out = [...xs];
  out[Number(index)] = value;
  return out;
}

/**
 * Logical implication (`p ==> q`), equivalent to `!p || q`.
 */
export function implies(premise: boolean, conclusion: boolean): boolean {
  return !premise || conclusion;
}
