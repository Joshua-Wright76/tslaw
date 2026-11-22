/**
 * Arrays: modeled as SMT sequences, used through the runtime helpers `len`, `at`, `append`,
 * `concat`, `slice` and `withAt`.
 */
import { spawnSync } from "node:child_process";
import { describe, expect, it } from "vitest";
import { append, at, concat, len, slice, withAt } from "../src/runtime.js";
import { verifyFiles } from "../src/verify.js";

const DIR = "test/fixtures/arrays";
const hasCvc5 = spawnSync("cvc5", ["--version"]).status === 0;

describe("arrays", () => {
  it("proves laws about arrays, including loops and recursion over them", async () => {
    const report = await verifyFiles([`${DIR}/arrays.law.ts`], { timeoutMs: 20_000 });
    expect(report.files[0]!.diagnostics).toEqual([]);
    const laws = report.files[0]!.laws;
    for (const l of laws) {
      if (l.name.startsWith("FALSE:")) expect(l.status, l.name).toBe("disproved");
      else expect(l.status, l.name).toBe("proved");
    }
    // Counterexamples are decoded into real arrays, and they really are counterexamples.
    const cex = (name: string): unknown =>
      laws.find((l) => l.name === name)!.counterexample!.find((c) => c.name === "xs")!.raw;
    expect(cex("FALSE: arrays are never empty")).toEqual([]);
    const pair = cex("FALSE: every pair is sorted") as bigint[];
    expect(pair.length).toBe(2);
    expect(pair[0]! > pair[1]!).toBe(true);
    const shown = laws.find((l) => l.name === "FALSE: every pair is sorted")!.counterexample![0]!.value;
    expect(shown).toMatch(/^\[-?\d+n, -?\d+n\]$/);
  });

  it.skipIf(!hasCvc5)("decides with cvc5 what Z3 cannot (reads of an updated array)", async () => {
    const report = await verifyFiles([`${DIR}/update.law.ts`], { timeoutMs: 6_000, crossCheck: true });
    const laws = report.files[0]!.laws.filter((l) => l.kind === "law");
    expect(laws.length).toBe(3);
    // Proved whether or not Z3 got there in time; cvc5 checked its own proof either way.
    for (const l of laws) {
      expect(l.status, l.name).toBe("proved");
      expect(["confirmed", "cvc5-only"]).toContain(l.crossCheck);
    }
  }, 60_000);

  it("reports every access that can be out of range", async () => {
    const report = await verifyFiles([`${DIR}/bad-arrays.law.ts`]);
    expect(report.files[0]!.diagnostics).toEqual([]);
    const laws = report.files[0]!.laws;
    const failed = laws.filter((l) => l.status !== "proved");
    expect(failed.map((l) => [l.name, l.status])).toEqual([
      ["requires of at at line 10", "disproved"],
      ["requires of at at line 15", "disproved"],
      ["requires of slice at line 19", "disproved"],
      ["requires of withAt at line 23", "disproved"],
    ]);
    // `head([])` is the counterexample.
    expect(failed[0]!.counterexample![0]!.raw).toEqual([]);
  });

  it("rejects array syntax that has no exact model", async () => {
    const report = await verifyFiles([`${DIR}/rejected.law.ts`]);
    const at_ = (code: string): number[] =>
      report.files[0]!.diagnostics.filter((d) => d.code === code).map((d) => d.location!.line).sort((a, b) => a - b);
    expect(at_("LAW016")).toEqual([6]); // xs.length
    expect(at_("LAW015")).toEqual([14]); // xs === ys
    expect(at_("LAW039")).toEqual([10, 18, 22, 26]); // xs[0]; spread; tuple; `[]` of unknown element type
    expect(at_("LAW006")).toEqual([21]); // tuple parameter
  });

  it("has runtime helpers that match what is proved about them", () => {
    const xs = Object.freeze([10n, 20n, 30n]);
    expect(len(xs)).toBe(3n);
    expect(at(xs, 2n)).toBe(30n);
    expect(append(xs, 40n)).toEqual([10n, 20n, 30n, 40n]);
    expect(concat(xs, [1n])).toEqual([10n, 20n, 30n, 1n]);
    expect(slice(xs, 1n, 3n)).toEqual([20n, 30n]);
    expect(slice(xs, 2n, 2n)).toEqual([]);
    expect(withAt(xs, 1n, 0n)).toEqual([10n, 0n, 30n]);
    expect(xs).toEqual([10n, 20n, 30n]); // nothing was changed in place
    // Out of range is an error, never `undefined`.
    expect(() => at(xs, 3n)).toThrow(RangeError);
    expect(() => at(xs, -1n)).toThrow(RangeError);
    expect(() => slice(xs, 2n, 1n)).toThrow(RangeError);
    expect(() => slice(xs, 0n, 4n)).toThrow(RangeError);
    expect(() => withAt(xs, 3n, 0n)).toThrow(RangeError);
  });
});
