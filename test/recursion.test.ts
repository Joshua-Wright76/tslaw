/**
 * Recursion: termination measures (`decreases`), induction through `ensures`, and the rule
 * that nothing may rest on a recursive definition whose termination was not proved.
 */
import { describe, expect, it } from "vitest";
import { decreases } from "../src/runtime.js";
import { verifyFiles } from "../src/verify.js";
import type { LawResult } from "../src/types.js";

const DIR = "test/fixtures/recursion";

/** Laws named `TRUE: ...` must be proved; laws named `FALSE: ...` must never be. */
function checkNamedLaws(laws: ReadonlyArray<LawResult>): void {
  for (const l of laws) {
    if (l.name.startsWith("TRUE:")) expect(l.status, l.name).toBe("proved");
    if (l.name.startsWith("FALSE:")) expect(l.status, l.name).not.toBe("proved");
  }
}

describe("recursion", () => {
  it("proves termination, postconditions by induction, and laws that use them", async () => {
    const report = await verifyFiles([`${DIR}/sums.law.ts`]);
    const laws = report.files[0]!.laws;
    expect(report.files[0]!.diagnostics).toEqual([]);
    checkNamedLaws(laws);
    // One termination goal per recursive call: sum, factorial, fib x2, isEven, isOdd,
    // ackermann x3.
    const termination = laws.filter((l) => l.kind === "decreases");
    expect(termination.length).toBe(9);
    expect(termination.every((l) => l.status === "proved")).toBe(true);
    expect(laws.filter((l) => l.kind === "ensures").every((l) => l.status === "proved")).toBe(true);
    expect(laws.filter((l) => l.kind === "requires").every((l) => l.status === "proved")).toBe(true);
    // Every `FALSE:` law here is refuted outright, with a real counterexample where it has
    // parameters.
    const refuted = laws.filter((l) => l.name.startsWith("FALSE:"));
    expect(refuted.map((l) => l.status)).toEqual(["disproved", "disproved"]);
    const n = refuted[1]!.counterexample!.find((c) => c.name === "n")!.raw as bigint;
    const sum = (k: bigint): bigint => (k <= 0n ? 0n : k + sum(k - 1n));
    expect(sum(n) <= n).toBe(false);
  });

  it("rejects non-terminating definitions and withdraws everything that used them", async () => {
    const report = await verifyFiles([`${DIR}/nonterminating.law.ts`]);
    expect(report.ok).toBe(false);
    const laws = report.files[0]!.laws;
    checkNamedLaws(laws);
    const byName = (prefix: string): LawResult[] => laws.filter((l) => l.name.startsWith(prefix));
    // Each counterexample is an argument where the measure really fails to get smaller.
    expect(byName("termination of loop")[0]!.status).toBe("disproved");
    expect(byName("termination of up")[0]!.status).toBe("disproved");
    const down = byName("termination of down")[0]!;
    expect(down.status).toBe("disproved");
    expect((down.counterexample![0]!.raw as bigint) < 0n).toBe(true);
    expect(byName("termination of countdown")[0]!.status).toBe("proved");
    // Laws about `loop` are neither proved nor refuted: its definition means nothing.
    for (const l of byName("FALSE: loop").concat(byName("FALSE: anything about loop"))) {
      expect(l.status).toBe("unknown");
      expect(l.reason).toMatch(/relies on "termination of loop/);
    }
    // A postcondition is not assumed while proving itself at the same arguments, and a
    // false one does not make laws provable.
    expect(byName("ensures id").map((l) => l.status)).toEqual(["disproved", "disproved"]);
    expect(byName("FALSE: id is negative")[0]!.status).toBe("disproved");
    // `implies` in a function body runs both arguments, so its premise guards nothing there.
    const eager = laws.filter((l) => l.kind === "requires" && l.location.line === 51);
    expect(eager.map((l) => l.status)).toEqual(["disproved"]);
    expect((eager[0]!.counterexample![0]!.raw as bigint) < 0n).toBe(true);
    // Preconditions of the recursive calls in `id` do not need the failed postconditions.
    expect(byName("requires of id").every((l) => l.status === "proved")).toBe(true);
  });

  it("does not let false postconditions prove each other", async () => {
    const report = await verifyFiles([`${DIR}/circular.law.ts`]);
    const laws = report.files[0]!.laws;
    checkNamedLaws(laws);
    const status = (name: string): string[] =>
      laws.filter((l) => l.name.startsWith(name)).map((l) => l.status);
    expect(status("ensures low")).toEqual(["disproved"]);
    expect(status("ensures high")).toEqual(["disproved"]);
    // Every call in a recursion must shrink the measure, and a call whose argument is the
    // function's own result cannot be shown to.
    expect(status("termination of tick")).toEqual(["disproved"]);
    expect(status("termination of nest")).toEqual(["proved", "disproved"]);
    expect(status("FALSE: nest is positive")).toEqual(["unknown"]);
    // An unsatisfiable precondition makes the definition say nothing, not everything.
    expect(status("termination of never")).toEqual(["proved"]);
    expect(status("FALSE: never is its own successor")).toEqual(["disproved"]);
  });

  it("uses postconditions of recursive functions from imported modules", async () => {
    const report = await verifyFiles([`${DIR}/gcd.law.ts`]);
    const laws = report.files[0]!.laws;
    checkNamedLaws(laws);
    const names = laws.map((l) => l.name);
    // Goals of the imported module that this file's proofs rest on are checked here too.
    expect(names).toContain("ensures mod");
    expect(names.some((n) => n.startsWith("termination of mod"))).toBe(true);
    expect(laws.filter((l) => l.status !== "proved").map((l) => l.name)).toEqual([
      "FALSE: gcd is at most its second argument",
    ]);
  });

  it("checks termination of imported recursive functions it depends on", async () => {
    const report = await verifyFiles([`${DIR}/uses-spin.law.ts`]);
    expect(report.ok).toBe(false);
    const laws = report.files[0]!.laws;
    checkNamedLaws(laws);
    expect(laws.find((l) => l.kind === "decreases")!.status).toBe("disproved");
    expect(laws.find((l) => l.name.startsWith("FALSE:"))!.status).toBe("unknown");
    // The unrelated law does not mention `spin`, so its query does not contain it.
    const unrelated = (await verifyFiles([`${DIR}/uses-spin.law.ts`], { emitSmt: true })).files[0]!.laws.find(
      (l) => l.name.startsWith("TRUE:"),
    )!;
    expect(unrelated.smt).not.toMatch(/define-funs-rec/);
  });

  it("requires a well-placed measure on every recursive function", async () => {
    const report = await verifyFiles([`${DIR}/missing-measure.law.ts`]);
    expect(report.ok).toBe(false);
    const diags = report.files[0]!.diagnostics;
    const at = (code: string): number[] =>
      diags.filter((d) => d.code === code).map((d) => d.location!.line).sort((a, b) => a - b);
    expect(at("LAW032")).toEqual([5, 14, 18]); // noMeasure, pong, late (its measure was rejected)
    expect(at("LAW037")).toEqual([20, 24]); // misplaced `decreases`; recursion inside `requires`
  });

  it("does nothing at runtime", () => {
    expect(decreases(1n, 2n)).toBeUndefined();
  });
});
