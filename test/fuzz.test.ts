/**
 * Differential fuzzing of the SMT translation.
 *
 * For each randomly generated function `f` and concrete arguments `v`:
 *   1. Run `f(v)` in real JavaScript to get the true result `r`.
 *   2. Ask the prover about the law `f(v) === r`. It must be PROVED.
 *   3. Ask about the same law with one part of `r` changed. It must be DISPROVED.
 *
 * Any disagreement means the SMT model of the program differs from what JavaScript does,
 * which is exactly the class of bug that produces false proofs.
 *
 * Environment:
 *   TSLAW_FUZZ_SEED   first seed (default 1)
 *   TSLAW_FUZZ_RUNS   number of generated modules (default 10)
 *   TSLAW_FUZZ_CROSS_CHECK=1   also require cvc5 to agree with Z3 on every law
 *   TSLAW_FUZZ_DIR    where to write the generated modules (default test/.generated; give
 *                     concurrent runs different directories)
 */
import fs from "node:fs";
import path from "node:path";
import { afterAll, beforeAll, describe, expect, it } from "vitest";
import { verifyFiles } from "../src/verify.js";
import {
  TYPE_DECLS,
  generateFunctions,
  leaves,
  makeRng,
  randomValue,
  valueToTs,
  type Value,
} from "./fuzz/generate.js";

const FIRST_SEED = Number(process.env["TSLAW_FUZZ_SEED"] ?? 1);
const RUNS = Number(process.env["TSLAW_FUZZ_RUNS"] ?? 10);
const FUNCTIONS_PER_MODULE = 6;
const INPUTS_PER_FUNCTION = 3;

const OUT_DIR = path.resolve(process.env["TSLAW_FUZZ_DIR"] ?? "test/.generated");
const RUNTIME = path.relative(OUT_DIR, path.resolve("src/runtime.js")).split(path.sep).join("/");

beforeAll(() => {
  fs.rmSync(OUT_DIR, { recursive: true, force: true });
  fs.mkdirSync(OUT_DIR, { recursive: true });
});
afterAll(() => {
  // Keep the generated files after a failure so the offending program can be inspected.
  if (!failed) fs.rmSync(OUT_DIR, { recursive: true, force: true });
});
let failed = false;

describe("fuzz: the SMT model agrees with JavaScript on generated programs", () => {
  it(`seeds ${FIRST_SEED}..${FIRST_SEED + RUNS - 1}`, async () => {
    try {
      const lawFiles: string[] = [];
      let expectedProved = 0;
      let expectedDisproved = 0;

      for (let seed = FIRST_SEED; seed < FIRST_SEED + RUNS; seed++) {
        const fns = generateFunctions(seed, FUNCTIONS_PER_MODULE, "f");
        const modFile = path.join(OUT_DIR, `gen${seed}.ts`);
        fs.writeFileSync(
          modFile,
          `"use verified";\n\nimport { append, at, concat, decreases, implies, len, slice, withAt } from "${RUNTIME}";\n\n${TYPE_DECLS}\n${fns.map((f) => f.source).join("\n\n")}\n`,
        );
        const mod = (await import(modFile)) as Record<string, (...args: Value[]) => Value>;

        const rng = makeRng(seed * 7919 + 13);
        const laws: string[] = [];
        for (const f of fns) {
          for (let i = 0; i < INPUTS_PER_FUNCTION; i++) {
            const args = f.params.map((p) => randomValue(rng, p.type));
            // Recursive functions recurse for a first argument in 1..5.
            if (f.recursive && rng() < 0.7) args[0] = BigInt(Math.floor(rng() * 7) - 1);
            const result = mod[f.name]!(...args);
            const callSrc = `${f.name}(${args.map(valueToTs).join(", ")})`;
            const parts = leaves(result, f.ret, "r");
            const flipped = Math.floor(rng() * parts.length);
            const check = (flip: number | undefined): string =>
              parts
                .map((p, k) => {
                  let want = p.value;
                  if (k === flip) want = typeof want === "bigint" ? want + 1n : !want;
                  return `${p.expr} === ${valueToTs(want)}`;
                })
                .join(" && ");
            laws.push(
              `law("ok ${f.name} #${i}", () => {\n  const r = ${callSrc};\n  return ${check(undefined)};\n});`,
              `law("bad ${f.name} #${i}", () => {\n  const r = ${callSrc};\n  return ${check(flipped)};\n});`,
            );
            expectedProved++;
            expectedDisproved++;
          }
        }
        const lawFile = path.join(OUT_DIR, `gen${seed}.law.ts`);
        fs.writeFileSync(
          lawFile,
          `"use verified";\n\nimport { at, law, len } from "${RUNTIME}";\nimport { ${fns.map((f) => f.name).join(", ")} } from "./gen${seed}.js";\n\n${laws.join("\n")}\n`,
        );
        lawFiles.push(lawFile);
      }

      const crossCheck = process.env["TSLAW_FUZZ_CROSS_CHECK"] === "1";
      const report = await verifyFiles(lawFiles, { timeoutMs: 20_000, crossCheck });
      const problems: string[] = [];
      const unconfirmed: string[] = [];
      let gotProved = 0;
      let gotDisproved = 0;
      let rejectedByTypeScript = 0;
      for (const file of report.files) {
        const name = path.basename(file.file);
        // Now and then the generator writes a comparison that TypeScript rejects because an
        // enclosing `if (x === 5n)` has narrowed `x` to that literal ("no overlap"). Such a
        // module is not in the subset, so it says nothing about the translation; skip it.
        if (file.diagnostics.length > 0 && file.diagnostics.every((d) => d.code === "TS2367")) {
          rejectedByTypeScript++;
          expectedProved -= FUNCTIONS_PER_MODULE * INPUTS_PER_FUNCTION;
          expectedDisproved -= FUNCTIONS_PER_MODULE * INPUTS_PER_FUNCTION;
          continue;
        }
        for (const d of file.diagnostics) {
          problems.push(`${name}: [${d.code}] ${d.message} (${d.location?.file ?? ""}:${d.location?.line ?? ""})`);
        }
        for (const l of file.laws) {
          // Termination goals of the imported recursive functions: all of them terminate.
          const want = l.kind !== "law" || l.name.startsWith("ok ") ? "proved" : "disproved";
          if (want === "proved" && l.kind === "law") gotProved++;
          if (want === "disproved") gotDisproved++;
          // A disagreement between the solvers shows up below as status `error`. cvc5 merely
          // failing to decide (it is slower at unfolding recursive functions) is tolerated in
          // small numbers.
          if (crossCheck && l.crossCheck !== "confirmed") unconfirmed.push(`${name}: "${l.name}"`);
          if (l.status !== want) {
            problems.push(`${name}: "${l.name}" should be ${want} but was ${l.status}${l.reason ? ` (${l.reason})` : ""}`);
          }
        }
      }
      expect(problems, `see generated programs in ${OUT_DIR}`).toEqual([]);
      expect(unconfirmed.length, unconfirmed.join("\n")).toBeLessThanOrEqual(
        Math.ceil((expectedProved + expectedDisproved) * 0.02),
      );
      expect(rejectedByTypeScript).toBeLessThanOrEqual(Math.ceil(RUNS * 0.02));
      expect(gotProved).toBe(expectedProved);
      expect(gotDisproved).toBe(expectedDisproved);
    } catch (err) {
      failed = true;
      throw err;
    }
  }, 300_000);
});
