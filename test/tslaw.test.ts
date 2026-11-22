import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { verifyFiles } from "../src/verify.js";
import { buggyTransfer } from "../examples/buggy.law.js";

const tmpDirs: string[] = [];

function writeTempLawFile(filename: string, body: string): string {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "tslaw-test-"));
  tmpDirs.push(dir);
  const runtimePath = path.resolve("src/runtime.ts").replace(/\.ts$/, ".js");
  const content = body.replaceAll("RUNTIME_PATH", runtimePath);
  const full = path.join(dir, filename);
  fs.writeFileSync(full, content, "utf8");
  return full;
}

afterEach(() => {
  while (tmpDirs.length > 0) {
    const dir = tmpDirs.pop()!;
    fs.rmSync(dir, { recursive: true, force: true });
  }
});

describe("tslaw formal verifier", () => {
  it("proves all laws in examples/tokens.law.ts and examples/bank.law.ts", async () => {
    const report = await verifyFiles([
      "examples/tokens.law.ts",
      "examples/bank.law.ts",
    ]);

    expect(report.ok).toBe(true);
    expect(report.summary.errors).toBe(0);
    expect(report.summary.disproved).toBe(0);
    expect(report.summary.proved).toBe(8);
  });

  it("disproves buggyTransfer and produces a real executable counterexample", async () => {
    const report = await verifyFiles(["examples/buggy.law.ts"], { emitSmt: true });

    expect(report.ok).toBe(false);
    expect(report.summary.proved).toBe(1);
    expect(report.summary.disproved).toBe(1);

    const file = report.files[0]!;
    const disproved = file.laws.find((l) => l.status === "disproved")!;
    expect(disproved).toBeDefined();
    expect(disproved.smt).toContain("(check-sat)");
    expect(disproved.counterexample).toBeDefined();

    const byName = new Map(disproved.counterexample!.map((c) => [c.name, c.raw as bigint]));
    const from = byName.get("from")!;
    const to = byName.get("to")!;
    const amount = byName.get("amount")!;

    // Verify that Z3's counterexample genuinely breaks the law when run in real JS!
    expect(from >= 0n && to >= 0n).toBe(true);
    const result = buggyTransfer(from, to, amount);
    expect(result.from < 0n || result.to < 0n).toBe(true);
  });

  it("rejects unsound dialect constructs in examples/unsound.law.ts", async () => {
    const report = await verifyFiles(["examples/unsound.law.ts"]);

    expect(report.ok).toBe(false);
    expect(report.summary.errors).toBeGreaterThan(0);

    const codes = new Set(report.files[0]!.diagnostics.map((d) => d.code));
    expect(codes.has("LAW006")).toBe(true); // number param
    expect(codes.has("LAW022")).toBe(true); // `var`
    expect(codes.has("LAW038")).toBe(true); // `while` loop without a termination measure
    expect(codes.has("LAW026")).toBe(true); // `for` loop
    expect(codes.has("LAW019")).toBe(true); // as cast
  });

  it("skips files without 'use verified' directive by default", async () => {
    const file = writeTempLawFile(
      "regular.ts",
      `export function add(a: number, b: number): number { return a + b; }\n`,
    );
    const report = await verifyFiles([file]);
    expect(report.ok).toBe(true);
    expect(report.summary.verifiedFiles).toBe(0);
    expect(report.files[0]!.verifiedDirective).toBe(false);
  });

  it("rejects mutable record fields and direct record === comparisons", async () => {
    const file = writeTempLawFile(
      "records.law.ts",
      `"use verified";
import { law } from "RUNTIME_PATH";
type Mut = { x: bigint };
type Box = { readonly x: bigint };
export function idMut(m: Mut): Mut { return m; }
export function eqBox(a: Box, b: Box): boolean { return a === b; }
law("t", (a: Box, b: Box) => eqBox(a, b));
`,
    );
    const report = await verifyFiles([file]);
    expect(report.ok).toBe(false);
    const codes = report.files[0]!.diagnostics.map((d) => d.code);
    expect(codes).toContain("LAW004"); // mutable field on return type
    expect(codes).toContain("LAW015"); // record === record
  });

  it("rejects recursive functions to guarantee termination", async () => {
    const file = writeTempLawFile(
      "rec.law.ts",
      `"use verified";
import { law } from "RUNTIME_PATH";
export function fact(n: bigint): bigint {
  if (n <= 1n) return 1n;
  return n * fact(n - 1n);
}
law("pos", (n: bigint) => fact(n) >= 1n);
`,
    );
    const report = await verifyFiles([file]);
    expect(report.ok).toBe(false);
    const codes = report.files[0]!.diagnostics.map((d) => d.code);
    expect(codes).toContain("LAW032");
  });

  it("supports const destructuring, nested records, and counterexamples on records", async () => {
    const file = writeTempLawFile(
      "nested.law.ts",
      `"use verified";
import { law } from "RUNTIME_PATH";
type Pair = { readonly a: bigint; readonly b: bigint };
export function swap(p: Pair): Pair {
  const { a, b } = p;
  return { a: b, b: a };
}
law("swap is involutive", (p: Pair) => {
  const s = swap(swap(p));
  return s.a === p.a && s.b === p.b;
});
law("swap preserves order (false!)", (p: Pair) => {
  const s = swap(p);
  return s.a === p.a;
});
`,
    );
    const report = await verifyFiles([file]);
    expect(report.ok).toBe(false);
    expect(report.summary.proved).toBe(1);
    expect(report.summary.disproved).toBe(1);
    const fail = report.files[0]!.laws.find((l) => l.status === "disproved")!;
    const raw = fail.counterexample![0]!.raw as { a: bigint; b: bigint };
    expect(raw.a).not.toBe(raw.b);
  });

  it("rejects type-check suppression comments in verified modules", async () => {
    const report = await verifyFiles(["test/fixtures/dialect/ts-ignore.law.ts"]);
    expect(report.ok).toBe(false);
    expect(report.summary.proved).toBe(0);
    expect(report.files[0]!.diagnostics.map((d) => d.code)).toContain("LAW033");
  });

  it("rejects bigint used as a boolean instead of sending it to Z3", async () => {
    const report = await verifyFiles(["test/fixtures/dialect/truthiness.law.ts"]);
    expect(report.ok).toBe(false);
    const codes = report.files[0]!.diagnostics.map((d) => d.code);
    // `if (x)`, `x ? :`, `!x`, and both operands of `x || y`
    expect(codes.filter((c) => c === "LAW034").length).toBe(5);
    expect(new Set(codes)).toEqual(new Set(["LAW034"]));
  });

  it("rejects literal-typed parameters, which would get bogus counterexamples", async () => {
    const report = await verifyFiles(["test/fixtures/dialect/literal-param.law.ts"]);
    expect(report.ok).toBe(false);
    expect(report.summary.disproved).toBe(0);
    const codes = report.files[0]!.diagnostics.map((d) => d.code);
    expect(codes).toEqual(["LAW006", "LAW006"]);
  });

  it("does not type-check files that have not opted in", async () => {
    const file = writeTempLawFile("broken.ts", `const s: string = 5;\nexport const t = s;\n`);
    const report = await verifyFiles([file]);
    expect(report.ok).toBe(true);
    expect(report.files[0]!.diagnostics).toEqual([]);
  });

  it("type-checks imported 'use verified' modules, not just the named file", async () => {
    const report = await verifyFiles(["test/fixtures/dialect/imports-type-error.law.ts"]);
    expect(report.ok).toBe(false);
    expect(report.summary.proved).toBe(0);
    const diag = report.files[0]!.diagnostics.find((d) => d.code === "TS2304")!;
    expect(diag).toBeDefined();
    expect(diag.location!.file).toMatch(/dep-type-error\.ts$/);
  });

  it("supports importing pure functions from another 'use verified' module", async () => {
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), "tslaw-xfile-"));
    tmpDirs.push(dir);
    const runtimePath = path.resolve("src/runtime.ts").replace(/\.ts$/, ".js");
    fs.writeFileSync(
      path.join(dir, "core.ts"),
      `"use verified";
export type Delta = { readonly next: bigint; readonly changed: boolean };
export function clampAdd(x: bigint, d: bigint, max: bigint): Delta {
  if (d <= 0n || x >= max) return { next: x, changed: false };
  const sum = x + d;
  return sum > max ? { next: max, changed: true } : { next: sum, changed: true };
}
`,
    );
    const lawFile = path.join(dir, "core.law.ts");
    fs.writeFileSync(
      lawFile,
      `"use verified";
import { law, implies } from "${runtimePath}";
import { clampAdd } from "./core.js";
law("clampAdd never exceeds max", (x: bigint, d: bigint, max: bigint) => {
  const res = clampAdd(x, d, max);
  return implies(x <= max, res.next <= max && res.next >= x);
});
`,
    );
    const report = await verifyFiles([lawFile]);
    expect(report.ok).toBe(true);
    expect(report.summary.proved).toBe(1);
  });
});
