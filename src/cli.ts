#!/usr/bin/env node
import path from "node:path";
import { verifyFiles } from "./verify.js";

function usage(): string {
  return [
    "lawscript — Verified TypeScript dialect powered by Z3",
    "",
    "Usage:",
    "  lawscript check <file1.ts> [file2.ts ...] [options]",
    "",
    "Options:",
    "  --emit-smt         Print generated SMT-LIB2 for each law",
    "  --json             Output machine-readable JSON report",
    "  --timeout <ms>     Per-law Z3 timeout in ms (default: 5000)",
    "  --z3 <path>        Path to z3 binary (default: LAWSCRIPT_Z3 or 'z3')",
    "  --all              Verify files even without a '\"use verified\";' directive",
  ].join("\n");
}

function rel(file: string): string {
  return path.relative(process.cwd(), file) || file;
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  const cmd = args[0];

  if (!cmd || cmd === "-h" || cmd === "--help") {
    console.log(usage());
    process.exit(0);
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

  for (let i = 1; i < args.length; i++) {
    const a = args[i]!;
    if (a === "--emit-smt") emitSmt = true;
    else if (a === "--json") json = true;
    else if (a === "--all") requireDirective = false;
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
    ...(z3Path ? { z3Path } : {}),
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
      const time = `${l.durationMs}ms`;
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
    `\nSummary: ${s.proved} proved, ${s.disproved} disproved, ${s.unknown} unknown, ${s.errors} errors (${s.verifiedFiles}/${s.totalFiles} verified files)`,
  );
  process.exitCode = report.ok ? 0 : 1;
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
