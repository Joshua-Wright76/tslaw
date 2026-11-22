/**
 * Soundness regression suite.
 *
 * A formal verifier is only useful if `PROVED` can be trusted, so this suite checks the prover's
 * verdicts against real JavaScript execution:
 *
 * - Laws named `FALSE: ...` are false at runtime and must never be PROVED.
 * - Laws named `TRUE: ...` must be PROVED.
 * - Every PROVED law is executed on many random inputs and must hold on all of them.
 * - Every DISPROVED law's counterexample is replayed and must actually violate the law.
 *
 * The last two catch SMT encoding bugs in general, not just the specific holes in the fixtures.
 */
import fs from "node:fs";
import path from "node:path";
import { describe, expect, it, vi } from "vitest";
import type { LawResult, VType } from "../src/types.js";
import { verifyFiles } from "../src/verify.js";

type Predicate = (...args: unknown[]) => boolean;

// Replace the no-op runtime `law` with one that records each predicate so laws can be executed.
const registered = vi.hoisted(() => [] as Array<{ name: string; predicate: Predicate }>);
vi.mock("../src/runtime.js", async (importOriginal) => {
  const original = await importOriginal<typeof import("../src/runtime.js")>();
  return {
    ...original,
    law: (name: string, predicate: Predicate) => {
      registered.push({ name, predicate });
    },
  };
});

/** Import a law module and return the predicates it registered, keyed by law name. */
async function loadPredicates(file: string): Promise<Map<string, Predicate>> {
  registered.length = 0;
  await import(path.resolve(file));
  const byName = new Map<string, Predicate>();
  for (const { name, predicate } of registered) byName.set(name, predicate);
  return byName;
}

// Deterministic PRNG (mulberry32) so failures are reproducible.
function makeRng(seed: number): () => number {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function randomValue(type: VType, rng: () => number): unknown {
  if (type.kind === "boolean") return rng() < 0.5;
  if (type.kind === "bigint") {
    const r = rng();
    const span = (n: number): bigint => BigInt(Math.floor(rng() * (2 * n + 1)) - n);
    if (r < 0.4) return span(3); // small values and boundaries: -3..3
    if (r < 0.7) return span(100);
    if (r < 0.9) return span(1_000_000);
    return span(1_000_000) * 2n ** 64n + span(1_000_000); // far outside 64-bit range
  }
  const obj: Record<string, unknown> = {};
  for (const f of type.fields) obj[f.name] = randomValue(f.type, rng);
  return obj;
}

const SAMPLES = 300;

function checkAgainstRuntime(law: LawResult, predicate: Predicate | undefined): void {
  expect(predicate, `law "${law.name}" was not registered at runtime`).toBeDefined();
  if (law.status === "proved") {
    const rng = makeRng(0x5eed);
    for (let i = 0; i < SAMPLES; i++) {
      const args = law.params.map((p) => randomValue(p.type, rng));
      const holds = predicate!(...args);
      expect(
        holds,
        `PROVED law "${law.name}" fails at runtime for (${args.map((a) => String(a)).join(", ")})`,
      ).toBe(true);
    }
  } else if (law.status === "disproved") {
    expect(law.counterexample, `DISPROVED law "${law.name}" has no counterexample`).toBeDefined();
    const byName = new Map(law.counterexample!.map((c) => [c.name, c.raw]));
    const args = law.params.map((p) => {
      expect(byName.has(p.name), `counterexample for "${law.name}" is missing \`${p.name}\``).toBe(true);
      return byName.get(p.name);
    });
    expect(
      predicate!(...args),
      `counterexample for "${law.name}" does not violate the law at runtime`,
    ).toBe(false);
  }
}

async function verifyAndReplay(file: string): Promise<ReadonlyArray<LawResult>> {
  const report = await verifyFiles([file]);
  const result = report.files[0]!;
  expect(result.diagnostics, `unexpected diagnostics in ${file}`).toEqual([]);
  const predicates = await loadPredicates(file);
  for (const law of result.laws) {
    // Only `law(...)` predicates are registered at runtime; contracts are covered elsewhere.
    if (law.kind !== "law") continue;
    if (law.name.startsWith("FALSE:")) {
      expect(law.status, `"${law.name}" is false at runtime but was ${law.status}`).toBe("disproved");
    } else if (law.name.startsWith("TRUE:")) {
      expect(law.status, `"${law.name}" should be proved but was ${law.status}`).toBe("proved");
    }
    checkAgainstRuntime(law, predicates.get(law.name));
  }
  return result.laws;
}

const FIXTURE_DIR = "test/fixtures/soundness";
const fixtureLawFiles = fs
  .readdirSync(FIXTURE_DIR)
  .filter((f) => f.endsWith(".law.ts") && f !== "fake-implies-unverified.law.ts")
  .map((f) => path.join(FIXTURE_DIR, f));

describe("soundness: fixtures that once produced false PROVED verdicts", () => {
  it.each(fixtureLawFiles)("%s", async (file) => {
    const laws = await verifyAndReplay(file);
    expect(laws.length).toBeGreaterThan(0);
  });

  it("rejects `implies` imported from a module that is not the tslaw runtime", async () => {
    const report = await verifyFiles([path.join(FIXTURE_DIR, "fake-implies-unverified.law.ts")]);
    expect(report.ok).toBe(false);
    expect(report.summary.proved).toBe(0);
    const codes = report.files[0]!.diagnostics.map((d) => d.code);
    expect(codes).toContain("LAW001");
  });
});

describe("soundness: examples agree with runtime execution", () => {
  it.each(["examples/tokens.law.ts", "examples/bank.law.ts", "examples/buggy.law.ts"])(
    "%s",
    async (file) => {
      const laws = await verifyAndReplay(file);
      expect(laws.length).toBeGreaterThan(0);
    },
  );
});
