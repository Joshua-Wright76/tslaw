/**
 * The Lean proofs in `proofs/Core.lean` (translation correctness and verdict soundness for
 * the core calculus) still check, and are not vacuous: a wrong translation breaks them.
 *
 * Skipped when Lean is not installed (https://lean-lang.org/install/).
 */
import { spawnSync } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";

const env = { ...process.env, PATH: `${process.env["PATH"] ?? ""}:${os.homedir()}/.elan/bin` };
const hasLean = spawnSync("lean", ["--version"], { env, cwd: "proofs" }).status === 0;
const source = fs.readFileSync("proofs/Core.lean", "utf8");

/** Check a (possibly modified) copy of the proof file; returns Lean's exit status. */
function check(text: string): number | null {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "tslaw-proofs-"));
  try {
    fs.copyFileSync("proofs/lean-toolchain", path.join(dir, "lean-toolchain"));
    fs.writeFileSync(path.join(dir, "Core.lean"), text);
    return spawnSync("lean", ["Core.lean"], { env, cwd: dir }).status;
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
}

function plant(from: string, to: string): string {
  expect(source).toContain(from);
  return source.replace(from, to);
}

describe.skipIf(!hasLean)("machine-checked core proofs", () => {
  it("check, with no `sorry`", () => {
    expect(source).not.toMatch(/\bsorry\b/);
    expect(check(source)).toBe(0);
  }, 120_000);

  it.each([
    ["`&&` translated as `or`", "| .and a b => .and (tr a) (tr b)", "| .and a b => .or (tr a) (tr b)"],
    ["`implies` translated as `and`", "| .implies a b => .imp (tr a) (tr b)", "| .implies a b => .and (tr a) (tr b)"],
    ["`!==` translated as `=`", "| .ne a b => .not (.eq (tr a) (tr b))", "| .ne a b => .eq (tr a) (tr b)"],
    [
      "`if` branches swapped",
      "| .ifElse c t e => .ite (tr c) (trBlock t) (trBlock e)",
      "| .ifElse c t e => .ite (tr c) (trBlock e) (trBlock t)",
    ],
    [
      "query not negated",
      "def query (body : Block) : Term := .not (trBlock body)",
      "def query (body : Block) : Term := trBlock body",
    ],
  ])("fail when the translation is wrong: %s", (_name, from, to) => {
    expect(check(plant(from, to))).not.toBe(0);
  }, 120_000);
});
