import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { verifyFiles } from "../src/verify.js";
import { buggyTransfer } from "../examples/buggy.law.js";

const tmpDirs: string[] = [];

function writeTempLawFile(filename: string, body: string): string {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "vscript-test-"));
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

describe("vscript formal verifier", () => {
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
    expect(codes.has("VS006")).toBe(true); // number param
    expect(codes.has("VS022")).toBe(true); // let mutation
    expect(codes.has("VS026")).toBe(true); // while loop
    expect(codes.has("VS019")).toBe(true); // as cast
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
    expect(codes).toContain("VS004"); // mutable field on return type
    expect(codes).toContain("VS015"); // record === record
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
    expect(codes).toContain("VS032");
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
});
