/**
 * tslaw runtime helpers.
 *
 * At runtime, `law`, `requires` and `ensures` are no-ops (they are proved statically by
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
 * Declare a postcondition of a verified function: `post(...args, result)` must hold for all
 * arguments that satisfy the function's `requires`. At runtime this is a no-op.
 */
export function ensures<A extends unknown[], R>(
  _fn: (...args: A) => R,
  _post: (...args: [...A, R]) => boolean,
): void {
  // Proved at compile time by tslaw.
}

/**
 * Logical implication (`p ==> q`), equivalent to `!p || q`.
 */
export function implies(premise: boolean, conclusion: boolean): boolean {
  return !premise || conclusion;
}
