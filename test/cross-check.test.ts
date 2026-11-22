/**
 * Cross-checking Z3's verdicts with cvc5 (`--cross-check`).
 */
import { spawnSync } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { afterAll, describe, expect, it } from "vitest";
import { verifyFiles } from "../src/verify.js";

const hasCvc5 = spawnSync("cvc5", ["--version"]).status === 0;
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "tslaw-cross-"));
afterAll(() => fs.rmSync(tmp, { recursive: true, force: true }));

/** A stand-in "solver" that ignores its input and always prints the given verdict. */
function fakeSolver(name: string, output: string): string {
  const file = path.join(tmp, name);
  fs.writeFileSync(file, `#!/bin/sh\ncat > /dev/null\nprintf '%s\\n' '${output}'\n`, { mode: 0o755 });
  return file;
}

describe("cross-check with cvc5", () => {
  it.skipIf(!hasCvc5)("confirms proofs and counterexamples when the solvers agree", async () => {
    const report = await verifyFiles(["examples/bank.law.ts", "examples/buggy.law.ts"], { crossCheck: true });
    const laws = report.files.flatMap((f) => f.laws);
    expect(laws.map((l) => l.status).sort()).toEqual(["disproved", "proved", "proved", "proved", "proved"]);
    expect(laws.every((l) => l.crossCheck === "confirmed")).toBe(true);
    expect(report.summary.confirmed).toBe(5);
  });

  it("reports an error, not a verdict, when the solvers disagree", async () => {
    const report = await verifyFiles(["examples/bank.law.ts"], {
      crossCheck: true,
      cvc5Path: fakeSolver("always-sat", "sat"),
    });
    expect(report.ok).toBe(false);
    expect(report.summary.proved).toBe(0);
    for (const law of report.files[0]!.laws) {
      expect(law.status).toBe("error");
      expect(law.reason).toMatch(/SOLVERS DISAGREE/);
    }
  });

  it("keeps Z3's verdict but marks it unconfirmed when the second solver cannot decide", async () => {
    const report = await verifyFiles(["examples/bank.law.ts"], {
      crossCheck: true,
      cvc5Path: fakeSolver("always-unknown", "unknown"),
    });
    expect(report.ok).toBe(true);
    expect(report.summary.confirmed).toBe(0);
    expect(report.files[0]!.laws.every((l) => l.status === "proved" && l.crossCheck === "unconfirmed")).toBe(true);
  });

  it("accepts the second solver's verdict when Z3 cannot decide", async () => {
    const report = await verifyFiles(["examples/bank.law.ts"], {
      crossCheck: true,
      z3Path: fakeSolver("z3-unknown", "unknown"),
      cvc5Path: fakeSolver("always-unsat", "unsat"),
    });
    expect(report.files[0]!.laws.every((l) => l.status === "proved" && l.crossCheck === "cvc5-only")).toBe(true);
  });

  it("fails clearly when cross-checking is requested but the solver is missing", async () => {
    const report = await verifyFiles(["examples/bank.law.ts"], { crossCheck: true, cvc5Path: "/nonexistent/cvc5" });
    expect(report.ok).toBe(false);
    expect(report.files[0]!.laws[0]!.reason).toMatch(/Could not run cvc5/);
  });
});
