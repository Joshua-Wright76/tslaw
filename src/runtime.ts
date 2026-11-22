/**
 * tslaw runtime helpers.
 *
 * At runtime, `law` is a zero-cost no-op (laws are proved statically by `tslaw check`).
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
 * Logical implication (`p ==> q`), equivalent to `!p || q`.
 */
export function implies(premise: boolean, conclusion: boolean): boolean {
  return !premise || conclusion;
}
