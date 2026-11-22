#!/usr/bin/env node
import path from "node:path";
import fs from "node:fs";
import { generateGuards } from "./guard.js";
import { verifyFiles } from "./verify.js";

function usage(): string {
  return [
    "tslaw — Verified TypeScript dialect powered by Z3",
    "",
    "Usage:",
    "  tslaw check <file1.ts> [file2.ts ...] [options]",
    "",
    "  tslaw guard <file1.ts> [file2.ts ...] [--check]",
    "",
    "Commands:",
    "  check              Prove the laws and contracts in verified modules",
    "  guard              Write <name>.guarded.ts next to each verified module: wrappers that",
    "                     check argument types and `requires` at runtime, for unverified callers.",
    "                     With --check, only report whether the files on disk are up to date.",
    "",
    "Options for check:",
    "  --emit-smt         Print generated SMT-LIB2 for each law",
    "  --json             Output machine-readable JSON report",
    "  --timeout <ms>     Per-law Z3 timeout in ms (default: 5000)",
    "  --z3 <path>        Path to z3 binary (default: TSLAW_Z3 or 'z3')",
    "  --cross-check      Also run every law through cvc5 and require it to agree with Z3",
    "  --cvc5 <path>      Path to cvc5 binary (default: TSLAW_CVC5 or 'cvc5')",
    "  --all              Verify files even without a '\"use verified\";' directive",
  ].join("\n");
}

function rel(file: string): string {
  return path.relative(process.cwd(), file) || file;
}

function runGuard(args: string[]): void {
  const checkOnly = args.includes("--check");
  const unknown = args.find((a) => a.startsWith("-") && a !== "--check");
  if (unknown) {
    console.error(`Unknown flag: ${unknown}`);
    process.exit(2);
  }
  const files = args.filter((a) => !a.startsWith("-"));
  if (files.length === 0) {
    console.error("No files specified.\n\n" + usage());
    process.exit(2);
  }

  let failed = false;
  for (const r of generateGuards(files)) {
    const label = rel(r.file);
    if (r.diagnostics.length > 0) {
      failed = true;
      console.log(`\n${label}`);
      for (const d of r.diagnostics) {
        const loc = d.location ? `${rel(d.location.file)}:${d.location.line}:${d.location.column}` : label;
        console.log(`  FAIL [${d.stage.toUpperCase()} ${d.code}] ${loc}`);
        console.log(`       ${d.message}`);
      }
      continue;
    }
    if (r.source === undefined) {
      console.log(`${label}  (no exported functions; nothing to guard)`);
      continue;
    }
    const out = rel(r.outFile);
    if (checkOnly) {
      const current = fs.existsSync(r.outFile) ? fs.readFileSync(r.outFile, "utf8") : undefined;
      if (current === r.source) {
        console.log(`${out}  up to date`);
      } else {
        failed = true;
        console.log(`${out}  ${current === undefined ? "MISSING" : "OUT OF DATE"} (run \`tslaw guard ${label}\`)`);
      }
    } else {
      fs.writeFileSync(r.outFile, r.source);
      console.log(`${out}  wrote guards for ${r.functions.join(", ")}`);
    }
  }
  process.exitCode = failed ? 1 : 0;
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  const cmd = args[0];

  if (!cmd || cmd === "-h" || cmd === "--help") {
    console.log(usage());
    process.exit(0);
  }
  if (cmd === "guard") {
    runGuard(args.slice(1));
    return;
  }
  if (cmd !== "check") {
    console.error(`Unknown command: ${cmd}\n\n${usage()}`);
    process.exit(2);
  }

  const files: string[] = [];
  let emitSmt = false;
  let json = false;
  let timeoutMs = 5000;
  let z3Path: string | undefined;
  let requireDirective = true;
  let crossCheck = false;
  let cvc5Path: string | undefined;

  for (let i = 1; i < args.length; i++) {
    const a = args[i]!;
    if (a === "--emit-smt") emitSmt = true;
    else if (a === "--json") json = true;
    else if (a === "--all") requireDirective = false;
    else if (a === "--cross-check") crossCheck = true;
    else if (a === "--cvc5") {
      cvc5Path = args[++i];
      if (!cvc5Path) {
        console.error("--cvc5 requires a path to the cvc5 binary");
        process.exit(2);
      }
    }
    else if (a === "--timeout") {
      const next = args[++i];
      const parsed = Number(next);
      if (!next || !Number.isFinite(parsed) || parsed <= 0) {
        console.error("--timeout requires a positive number in ms");
        process.exit(2);
      }
      timeoutMs = parsed;
    } else if (a === "--z3") {
      z3Path = args[++i];
      if (!z3Path) {
        console.error("--z3 requires a path to the z3 binary");
        process.exit(2);
      }
    } else if (a.startsWith("-")) {
      console.error(`Unknown flag: ${a}`);
      process.exit(2);
    } else {
      files.push(a);
    }
  }

  if (files.length === 0) {
    console.error("No files specified.\n\n" + usage());
    process.exit(2);
  }

  const report = await verifyFiles(files, {
    emitSmt,
    timeoutMs,
    requireDirective,
    crossCheck,
    ...(z3Path ? { z3Path } : {}),
    ...(cvc5Path ? { cvc5Path } : {}),
  });

  if (json) {
    console.log(
      JSON.stringify(
        report,
        (_k, v) => (typeof v === "bigint" ? `${v}n` : v),
        2,
      ),
    );
    // Set the exit code instead of calling process.exit(): exiting immediately can truncate
    // large output written to a pipe.
    process.exitCode = report.ok ? 0 : 1;
    return;
  }

  for (const f of report.files) {
    const label = rel(f.file);
    if (f.diagnostics.length > 0) {
      console.log(`\n${label}`);
      for (const d of f.diagnostics) {
        const loc = d.location ? `:${d.location.line}:${d.location.column}` : "";
        const where = d.location ? rel(d.location.file) : label;
        console.log(`  FAIL [${d.stage.toUpperCase()} ${d.code}] ${where}${loc}`);
        console.log(`       ${d.message}`);
      }
      continue;
    }

    if (!f.verifiedDirective && requireDirective) {
      console.log(`\n${label}  (skipped: no "use verified"; directive)`);
      continue;
    }

    console.log(`\n${label}`);
    if (f.laws.length === 0) {
      console.log("  OK   Dialect valid (0 laws declared)");
      continue;
    }

    for (const l of f.laws) {
      const note =
        l.crossCheck === "confirmed"
          ? ", confirmed by cvc5"
          : l.crossCheck === "unconfirmed"
            ? ", NOT confirmed: cvc5 could not decide"
            : l.crossCheck === "cvc5-only"
              ? ", by cvc5 only: Z3 could not decide"
              : "";
      const time = `${l.durationMs}ms${note}`;
      if (l.status === "proved") {
        console.log(`  PROVED    "${l.name}" (${time})`);
      } else if (l.status === "disproved") {
        console.log(`  DISPROVED "${l.name}" (${time}) at ${label}:${l.location.line}`);
        if (l.counterexample && l.counterexample.length > 0) {
          const vals = l.counterexample.map((c) => `${c.name} = ${c.value}`).join(", ");
          console.log(`            Counterexample: ${vals}`);
        }
      } else {
        console.log(`  ${l.status.toUpperCase().padEnd(9)} "${l.name}" (${time})`);
        if (l.reason) console.log(`            ${l.reason}`);
      }
      if (emitSmt && l.smt) {
        console.log("  --- SMT-LIB2 ---");
        for (const line of l.smt.trimEnd().split("\n")) {
          console.log(`    ${line}`);
        }
        console.log("  ----------------");
      }
    }
  }

  const s = report.summary;
  console.log(
    `\nSummary: ${s.proved} proved, ${s.disproved} disproved, ${s.unknown} unknown, ${s.errors} errors (${s.verifiedFiles}/${s.totalFiles} verified files)` +
      (s.confirmed !== undefined ? `\nCross-check: cvc5 confirmed ${s.confirmed} of ${s.proved + s.disproved} verdicts` : ""),
  );
  process.exitCode = report.ok ? 0 : 1;
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
