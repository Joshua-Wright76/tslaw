/**
 * `tslaw guard`: generated wrappers that check argument types and `requires` at runtime.
 *
 * `test/fixtures/guard/*.guarded.ts` are committed generator output; regenerate them with
 * `node dist/cli.js guard test/fixtures/guard/bank.ts test/fixtures/guard/limits.ts test/fixtures/guard/basket.ts`.
 */
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import ts from "typescript";
import { describe, expect, it } from "vitest";
import { generateGuards } from "../src/guard.js";
import { VERIFIER_COMPILER_OPTIONS } from "../src/verify.js";
import * as guarded from "./fixtures/guard/bank.guarded.js";
import * as raw from "./fixtures/guard/bank.js";
import * as basket from "./fixtures/guard/basket.guarded.js";

const DIR = "test/fixtures/guard";
const account = (balance: bigint, active = true) => ({ balance, owner: { id: 1n, active } });
// Callers the guards exist for do not respect the types.
const untyped = guarded as unknown as Record<string, (...args: unknown[]) => unknown>;

describe("tslaw guard", () => {
  it("generates exactly the committed wrappers", () => {
    const results = generateGuards([`${DIR}/bank.ts`, `${DIR}/limits.ts`, `${DIR}/basket.ts`]);
    for (const r of results) {
      expect(r.diagnostics).toEqual([]);
      expect(r.source).toBe(fs.readFileSync(r.outFile, "utf8"));
    }
    expect(results[0]!.functions).toEqual(["isOpen", "withdraw", "total", "usesHidden"]);
  });

  it("generates code that passes the strict type check", () => {
    const program = ts.createProgram(
      [`${DIR}/bank.guarded.ts`, `${DIR}/limits.guarded.ts`, `${DIR}/basket.guarded.ts`],
      VERIFIER_COMPILER_OPTIONS,
    );
    const diags = ts.getPreEmitDiagnostics(program).map((d) => ts.flattenDiagnosticMessageText(d.messageText, "\n"));
    expect(diags).toEqual([]);
  });

  it("passes valid calls through unchanged", () => {
    expect(guarded.withdraw(account(100n), 30n, false)).toEqual(raw.withdraw(account(100n), 30n, false));
    expect(guarded.total(account(1n), account(2n))).toBe(3n);
    expect(guarded.usesHidden(7n)).toBe(7n);
  });

  it("rejects arguments of the wrong runtime type", () => {
    expect(() => untyped["withdraw"]!(account(100n), 30, false)).toThrow(/withdraw: amount must be a bigint, got number 30/);
    expect(() => untyped["withdraw"]!(account(100n), 30n, "yes")).toThrow(/force must be a boolean/);
    expect(() => untyped["withdraw"]!(null, 30n, false)).toThrow(/acc must be an object, got null/);
    expect(() => untyped["withdraw"]!({ balance: 100n }, 30n, false)).toThrow(/acc\.owner must be an object/);
    expect(() => untyped["withdraw"]!({ balance: 100n, owner: { id: 1, active: true } }, 30n, false)).toThrow(
      /acc\.owner\.id must be a bigint/,
    );
    expect(() => untyped["withdraw"]!(account(100n), 30n)).toThrow(/expected 3 argument\(s\), got 2/);
    expect(() => untyped["total"]!(account(1n), 2n)).toThrow(TypeError);
  });

  it("rejects calls that violate `requires`", () => {
    expect(() => guarded.withdraw(account(100n), 0n, false)).toThrow(RangeError);
    expect(() => guarded.withdraw(account(100n), 101n, false)).toThrow(/requires\(amount > 0n && amount <= acc\.balance\)/);
    // Second precondition: a closed account needs `force`.
    expect(() => guarded.withdraw(account(100n, false), 10n, false)).toThrow(/implies\(!force, isOpen\(acc\)\)/);
    expect(guarded.withdraw(account(100n, false), 10n, true).balance).toBe(90n);
    // Third precondition calls a function imported from another verified module.
    expect(() => guarded.withdraw(account(5000n), 1001n, false)).toThrow(/maxWithdrawal\(\)/);
    // The unguarded function does not check anything.
    expect(raw.withdraw(account(100n), 101n, false).balance).toBe(-1n);
  });

  it("copies records so a caller cannot change them after the check", () => {
    let reads = 0;
    const shifty = {
      get balance(): bigint {
        // Passes the precondition on first read, would overdraw on a second.
        return reads++ === 0 ? 100n : 0n;
      },
      owner: { id: 1n, active: true },
      extra: "ignored",
    };
    const result = guarded.withdraw(shifty, 60n, false);
    expect(reads).toBe(1);
    expect(result.balance).toBe(40n);
    expect(Object.isFrozen(result.owner)).toBe(true);
    expect("extra" in result).toBe(false);
  });

  it("checks arrays element by element and copies them", () => {
    const loose = basket as unknown as Record<string, (...args: unknown[]) => unknown>;
    const items = [{ price: 5n, qty: 2n }, { price: 7n, qty: 3n }];
    expect(basket.lineTotal(items, 1n)).toBe(21n);
    expect(basket.count(items, [[1n], []])).toBe(4n);
    expect(() => loose["lineTotal"]!("nope", 0n)).toThrow(/items must be an array, got string nope/);
    expect(() => loose["lineTotal"]!([{ price: 5n, qty: 2n }, { price: 7 }], 0n)).toThrow(
      /items\[1\]\.price must be a bigint, got number 7/,
    );
    expect(() => loose["count"]!(items, [[1n], [2]])).toThrow(/tags\[1\]\[0\] must be a bigint/);
    // A hole reads as `undefined`, which is not an element.
    expect(() => loose["lineTotal"]!(new Array(2), 0n)).toThrow(/items\[0\] must be an object/);
    // Preconditions that use `len` and `at` are evaluated on the checked copy.
    expect(() => basket.lineTotal(items, 2n)).toThrow(/requires\(0n <= index && index < len\(items\)\)/);
    expect(() => basket.lineTotal(items, -1n)).toThrow(RangeError);
    expect(() => basket.lineTotal([{ price: 5n, qty: -1n }], 0n)).toThrow(/at\(items, index\)\.qty >= 0n/);
    // An array that changes between reads cannot get past the check.
    let reads = 0;
    const shifty = new Proxy([{ price: 5n, qty: 2n }], {
      get(target, key, receiver) {
        if (key === "0") reads++;
        return Reflect.get(target, key, receiver) as unknown;
      },
    });
    expect(basket.lineTotal(shifty, 0n)).toBe(10n);
    expect(reads).toBe(1);
  });

  it("refuses to generate a guard whose `requires` needs a function it cannot import", () => {
    const [r] = generateGuards([`${DIR}/unexported.ts`]);
    expect(r!.source).toBeUndefined();
    expect(r!.diagnostics[0]!.message).toMatch(/`positive`, which is not exported/);
  });

  it("refuses modules that are not verified", () => {
    const [r] = generateGuards(["src/runtime.ts"]);
    expect(r!.source).toBeUndefined();
    expect(r!.diagnostics[0]!.code).toBe("LAW040");
  });

  it("rejects arrays passed where a record is expected", () => {
    expect(() => untyped["isOpen"]!([])).toThrow(/isOpen: acc must be an object/);
  });

  it("avoids helper name collisions, escapes weird field names, and type-checks verified dependencies", () => {
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), "tslaw-guard-edge-"));
    try {
      const runtimePath = path.resolve("src/runtime.ts").replace(/\.ts$/, ".js");
      const tricky = path.join(dir, "tricky.ts");
      fs.writeFileSync(
        tricky,
        `"use verified";
import { requires } from ${JSON.stringify(runtimePath)};
interface Weird { readonly "a\`\${1}": bigint; }
export function $fail(args: bigint, $verified: bigint, w: Weird): bigint {
  requires(args > 0n && $verified > 0n);
  return args + $verified;
}
`,
      );
      const [g] = generateGuards([tricky]);
      expect(g!.diagnostics).toEqual([]);
      expect(g!.source).toBeDefined();
      fs.writeFileSync(g!.outFile, g!.source!);
      const program = ts.createProgram([g!.outFile], VERIFIER_COMPILER_OPTIONS);
      const diags = ts.getPreEmitDiagnostics(program).map((d) => ts.flattenDiagnosticMessageText(d.messageText, "\n"));
      expect(diags).toEqual([]);

      // Imported verified module with a type error must fail guard generation.
      const depBad = path.join(dir, "depBad.ts");
      const mainBad = path.join(dir, "mainBad.ts");
      fs.writeFileSync(depBad, `"use verified";\nexport function h(x: bigint): bigint { const b: bigint = true; return x; }\n`);
      fs.writeFileSync(
        mainBad,
        `"use verified";\nimport { requires } from ${JSON.stringify(runtimePath)};\nimport { h } from "./depBad.js";\nexport function f(x: bigint): bigint { requires(h(x) > 0n); return x; }\n`,
      );
      const [badRes] = generateGuards([mainBad]);
      expect(badRes!.source).toBeUndefined();
      expect(badRes!.diagnostics.map((d) => d.code)).toContain("TS2322");
    } finally {
      fs.rmSync(dir, { recursive: true, force: true });
    }
  });
});
