/**
 * `let`, assignment and `while` loops with `invariant` and `decreases`.
 */
import { describe, expect, it } from "vitest";
import { invariant } from "../src/runtime.js";
import { verifyFiles } from "../src/verify.js";
import type { LawResult } from "../src/types.js";

const DIR = "test/fixtures/loops";

function checkNamedLaws(laws: ReadonlyArray<LawResult>): void {
  for (const l of laws) {
    if (l.name.startsWith("TRUE:")) expect(l.status, l.name).toBe("proved");
    if (l.name.startsWith("FALSE:")) expect(l.status, l.name).not.toBe("proved");
  }
}

describe("loops", () => {
  it("proves invariants, termination and postconditions that follow from them", async () => {
    const report = await verifyFiles([`${DIR}/loops.law.ts`]);
    expect(report.files[0]!.diagnostics).toEqual([]);
    const laws = report.files[0]!.laws;
    checkNamedLaws(laws);
    const unproved = laws.filter((l) => l.status !== "proved").map((l) => l.name);
    expect(unproved).toEqual([
      "FALSE: sumTo(4) is eleven",
      "FALSE: times ignores its first argument",
    ]);
    // Four loops (the nested one counts twice), each with a termination goal and an invariant
    // that must hold on entry and be kept.
    const names = laws.map((l) => l.name);
    expect(names.filter((n) => n.startsWith("termination of the loop")).length).toBe(4);
    expect(names.filter((n) => n.endsWith("holds on entry")).length).toBe(4);
    expect(names.filter((n) => n.endsWith("kept by the body")).length).toBe(4);
    expect(laws.filter((l) => l.kind === "ensures").length).toBe(6);
    // The counterexample is real: 4 * 1 is not 1.
    const cex = laws.find((l) => l.name.startsWith("FALSE: times"))!.counterexample!;
    const a = cex.find((c) => c.name === "a")!.raw as bigint;
    const b = cex.find((c) => c.name === "b")!.raw as bigint;
    expect(b >= 0n && a * b !== b).toBe(true);
  });

  it("gets scoping, shadowing and mixed control flow right", async () => {
    // The expected values in this fixture were obtained by running the functions.
    const report = await verifyFiles([`${DIR}/scoping.law.ts`]);
    expect(report.files[0]!.diagnostics).toEqual([]);
    for (const l of report.files[0]!.laws) {
      expect(l.status, l.name).toBe(l.name.startsWith("FALSE:") ? "disproved" : "proved");
    }
  });

  it("refutes loops that do not terminate and invariants that do not hold", async () => {
    const report = await verifyFiles([`${DIR}/bad-loops.law.ts`]);
    expect(report.ok).toBe(false);
    const laws = report.files[0]!.laws;
    checkNamedLaws(laws);
    const status = (name: string): string | undefined => laws.find((l) => l.name === name)?.status;
    expect(status("termination of the loop at line 9")).toBe("disproved");
    expect(status("invariant of the loop at line 21: holds on entry")).toBe("disproved");
    expect(status("invariant of the loop at line 33: holds on entry")).toBe("proved");
    expect(status("invariant of the loop at line 33: kept by the body")).toBe("disproved");
    // Nothing can be concluded from a loop that may not end.
    expect(status("FALSE: stuck returns anything")).toBe("unknown");
    // A loop whose invariant is not kept is unspecified in the model after the first
    // iteration, so nothing about the function is proved or refuted.
    expect(status("ensures notKept")).toBe("unknown");
    expect(status("FALSE: notKept is zero")).toBe("unknown");
    // `while (true)` makes the negated condition `false` afterwards; that must prove nothing.
    expect(status("ensures forever")).toBe("unknown");
    expect(status("FALSE: forever is below itself")).toBe("unknown");
    // After a loop without an invariant only the negated condition is known.
    expect(status("ensures count")).toBe("proved");
    expect(status("ensures count #2")).not.toBe("proved");
  });

  it("rejects malformed loops and assignments", async () => {
    const report = await verifyFiles([`${DIR}/misplaced.law.ts`]);
    expect(report.ok).toBe(false);
    const diags = report.files[0]!.diagnostics;
    const at = (code: string): number[] =>
      diags.filter((d) => d.code === code).map((d) => d.location!.line).sort((a, b) => a - b);
    // No measure; `return` in a loop; assignment to a parameter; late `invariant`; a loop
    // that calls the recursion it is part of.
    expect(at("LAW038")).toEqual([7, 17, 24, 33, 46]);
    // `for` loop; loop inside a law.
    expect(at("LAW026")).toEqual([40, 60]);
  });

  it("does nothing at runtime", () => {
    expect(invariant(false)).toBeUndefined();
  });
});
