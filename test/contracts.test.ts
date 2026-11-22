/**
 * Function contracts: `requires` (proved at every verified call site) and `ensures`
 * (proved for all inputs that satisfy the function's `requires`).
 */
import { describe, expect, it } from "vitest";
import { ensures, requires } from "../src/runtime.js";
import { verifyFiles } from "../src/verify.js";

const DIR = "test/fixtures/contracts";

describe("contracts", () => {
  it("proves guarded calls and postconditions", async () => {
    const report = await verifyFiles([`${DIR}/bank.law.ts`]);
    expect(report.ok).toBe(true);
    const laws = report.files[0]!.laws;
    expect(laws.every((l) => l.status === "proved")).toBe(true);
    // One obligation per call to `withdraw`: if-guard, two sequential calls, ternary,
    // `||` short-circuit, and inside `implies` in a law.
    expect(laws.filter((l) => l.kind === "requires").length).toBe(6);
    expect(laws.filter((l) => l.kind === "ensures").map((l) => l.name)).toEqual([
      "ensures withdraw",
      "ensures withdraw #2",
    ]);
    expect(laws.filter((l) => l.kind === "law").length).toBe(1);
  });

  it("reports each call that can violate a precondition, with a counterexample", async () => {
    const report = await verifyFiles([`${DIR}/violations.law.ts`]);
    expect(report.ok).toBe(false);
    const laws = report.files[0]!.laws;
    const violated = laws.filter((l) => l.kind === "requires");
    expect(violated.map((l) => l.location.line)).toEqual([12, 18, 24, 33]);
    for (const v of violated) {
      expect(v.status).toBe("disproved");
      // Every counterexample is an argument that really breaks `requires(x >= 0n)`.
      const x = v.counterexample!.find((c) => c.name === "x")!.raw as bigint;
      expect(x < 0n).toBe(true);
    }
    const post = laws.filter((l) => l.kind === "ensures");
    expect(post.map((l) => l.status)).toEqual(["disproved", "proved"]);
    // The false postcondition's counterexample satisfies the precondition.
    const cex = post[0]!.counterexample!.find((c) => c.name === "x")!.raw as bigint;
    expect(cex >= 0n).toBe(true);
  });

  it("rejects misplaced `requires` and malformed `ensures`", async () => {
    const report = await verifyFiles([`${DIR}/misplaced.law.ts`]);
    expect(report.ok).toBe(false);
    const codes = report.files[0]!.diagnostics.map((d) => d.code);
    expect(codes.filter((c) => c === "LAW035").length).toBe(2); // after a const; inside a law
    expect(codes).toContain("LAW036"); // postcondition missing the result parameter
  });

  it("does nothing at runtime", () => {
    expect(requires(false)).toBeUndefined();
    expect(ensures((x: bigint) => x, (_x, result) => result === 0n)).toBeUndefined();
  });
});
