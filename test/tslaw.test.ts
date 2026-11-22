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

  it("rejects unary `+` (which produces IEEE-754 number from boolean)", async () => {
    const file = writeTempLawFile(
      "unary-plus.law.ts",
      `"use verified";
import { law } from "RUNTIME_PATH";
export function bad(a: boolean, b: boolean): boolean {
  return +a + +b === +a;
}
law("FALSE: unary plus", (a: boolean, b: boolean) => bad(a, b) === !b);
`,
    );
    const report = await verifyFiles([file]);
    expect(report.ok).toBe(false);
    expect(report.summary.proved).toBe(0);
    expect(report.files[0]!.diagnostics.map((d) => d.code)).toContain("LAW012");
  });

  it("rejects `__proto__` fields, index signatures, construct signatures, and symbol-keyed fields", async () => {
    const file = writeTempLawFile(
      "bad-records.law.ts",
      `"use verified";
import { law } from "RUNTIME_PATH";
interface Proto { readonly __proto__: bigint; }
interface Idx { readonly a: bigint; readonly [k: string]: bigint; }
interface Ctor { new(): object; readonly a: bigint; }
interface Sym { readonly [Symbol.toStringTag]: bigint; readonly a: bigint; }
export function makeProto(): Proto { return { __proto__: 1n }; }
export function takeIdx(x: Idx): bigint { return x.a; }
export function takeCtor(x: Ctor): bigint { return x.a; }
export function takeSym(x: Sym): bigint { return x.a; }
law("FALSE: proto", () => makeProto().__proto__ === 1n);
`,
    );
    const report = await verifyFiles([file]);
    expect(report.ok).toBe(false);
    expect(report.summary.proved).toBe(0);
    const msgs = report.files[0]!.diagnostics.map((d) => d.message).join("\n");
    expect(msgs).toContain("__proto__");
    expect(msgs).toContain("index signatures");
    expect(msgs).toContain("constructor types");
    expect(msgs).toContain("symbol-keyed");
  });

  it("rejects computed/string keys, non-records, and inherited keys in object destructuring", async () => {
    const file = writeTempLawFile(
      "bad-destructure.law.ts",
      `"use verified";
import { law } from "RUNTIME_PATH";
interface Pair { readonly a: bigint; readonly b: bigint; }
export function strKey(p: Pair): bigint { const { "a": b } = p; return b; }
export function compKey(p: Pair): bigint { const { ["a"]: b } = p; return b; }
export function arrDestr(xs: readonly bigint[]): bigint { const { length } = xs; return 1n; }
export function ctorDestr(p: Pair): bigint { const { constructor } = p; return 1n; }
law("FALSE: strKey", (p: Pair) => strKey(p) === p.b);
`,
    );
    const report = await verifyFiles([file]);
    expect(report.ok).toBe(false);
    expect(report.summary.proved).toBe(0);
    const codes = report.files[0]!.diagnostics.map((d) => d.code);
    expect(codes).toContain("LAW022");
    expect(codes).toContain("LAW016");
  });

  it("rejects side-effect imports, default+named imports, and re-exports through unverified barrels", async () => {
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), "tslaw-imports-"));
    tmpDirs.push(dir);
    const runtimePath = path.resolve("src/runtime.ts").replace(/\.ts$/, ".js");
    fs.writeFileSync(path.join(dir, "side.ts"), `export const x = 1;\n`);
    fs.writeFileSync(
      path.join(dir, "target.ts"),
      `"use verified";\nexport function bad(x: bigint): bigint { const broken: bigint = true; return x; }\n`,
    );
    fs.writeFileSync(path.join(dir, "barrel.ts"), `export { bad } from "./target.js";\n`);
    fs.writeFileSync(path.join(dir, "rtwrap.ts"), `export default 1;\nexport { law } from "${runtimePath}";\n`);

    const sideFile = path.join(dir, "a.law.ts");
    fs.writeFileSync(sideFile, `"use verified";\nimport "./side.js";\nimport { law } from "${runtimePath}";\nlaw("t", () => true);\n`);
    const barrelFile = path.join(dir, "b.law.ts");
    fs.writeFileSync(barrelFile, `"use verified";\nimport { law } from "${runtimePath}";\nimport { bad } from "./barrel.js";\nlaw("t", (x: bigint) => bad(x) === x);\n`);
    const defFile = path.join(dir, "c.law.ts");
    fs.writeFileSync(defFile, `"use verified";\nimport d, { law } from "./rtwrap.js";\nlaw("t", () => true);\n`);

    const report = await verifyFiles([sideFile, barrelFile, defFile]);
    expect(report.ok).toBe(false);
    expect(report.summary.proved).toBe(0);
    for (const f of report.files) {
      expect(f.diagnostics.map((d) => d.code)).toContain("LAW001");
    }
  });

  it("rejects `this` parameters and avoids record type key collisions on punctuation", async () => {
    const thisFile = writeTempLawFile(
      "this-param.law.ts",
      `"use verified";
import { law } from "RUNTIME_PATH";
law("this", function(this: bigint, x: bigint) { return x === x; });
`,
    );
    const r1 = await verifyFiles([thisFile]);
    expect(r1.ok).toBe(false);
    expect(r1.files[0]!.diagnostics.map((d) => d.code)).toContain("LAW005");

    const keyFile = writeTempLawFile(
      "vtypekey.law.ts",
      `"use verified";
import { law } from "RUNTIME_PATH";
interface A { readonly "x:Int,y": bigint; }
interface B { readonly x: bigint; readonly y: bigint; }
export function takeA(_a: A): bigint { return 1n; }
export function takeB(b: B): bigint { return b.x + b.y; }
law("distinct records", (a: A, b: B) => takeA(a) + takeB(b) === 1n + b.x + b.y);
`,
    );
    const r2 = await verifyFiles([keyFile]);
    expect(r2.ok).toBe(true);
    expect(r2.summary.proved).toBe(1);
  });

  it("still reports disproved loop invariants when the loop's termination fails", async () => {
    const file = writeTempLawFile(
      "bad-loop.law.ts",
      `"use verified";
import { decreases, invariant } from "RUNTIME_PATH";
export function bad(n: bigint): bigint {
  let i = n;
  while (i > 0n) {
    invariant(i >= 0n && i <= 10n);
    decreases(i);
    i += 1n;
  }
  return i;
}
`,
    );
    const report = await verifyFiles([file]);
    expect(report.ok).toBe(false);
    const byName = new Map(report.files[0]!.laws.map((l) => [l.name, l.status]));
    expect(byName.get("termination of the loop at line 5")).toBe("disproved");
    expect(byName.get("invariant of the loop at line 5: kept by the body")).toBe("disproved");
  });
});
