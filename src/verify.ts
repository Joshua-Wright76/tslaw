import path from "node:path";
import ts from "typescript";
import { analyzeDialect, getLocation, hasUseVerifiedDirective } from "./dialect.js";
import { lowerModuleLaws } from "./smt.js";
import type {
  Diagnostic,
  FileVerificationResult,
  LawResult,
  VerifyOptions,
  VerifyReport,
} from "./types.js";
import { runZ3 } from "./z3.js";

const DEFAULT_TIMEOUT_MS = 5000;

/** Transitive `"use verified";` source modules imported by `root` (excluding `root`). */
function verifiedDeps(root: ts.SourceFile, checker: ts.TypeChecker): ts.SourceFile[] {
  const seen = new Set<ts.SourceFile>([root]);
  const out: ts.SourceFile[] = [];
  const visit = (sf: ts.SourceFile): void => {
    for (const stmt of sf.statements) {
      if (!ts.isImportDeclaration(stmt)) continue;
      const sym = checker.getSymbolAtLocation(stmt.moduleSpecifier);
      const dep = sym?.declarations?.find(ts.isSourceFile);
      if (!dep || seen.has(dep) || dep.isDeclarationFile || !hasUseVerifiedDirective(dep)) continue;
      seen.add(dep);
      out.push(dep);
      visit(dep);
    }
  };
  visit(root);
  return out;
}

export async function verifyFiles(
  filePaths: ReadonlyArray<string>,
  options: VerifyOptions = {},
): Promise<VerifyReport> {
  const absPaths = filePaths.map((p) => path.resolve(p));
  const timeoutMs = options.timeoutMs ?? DEFAULT_TIMEOUT_MS;
  const z3Path = options.z3Path ?? process.env["LAWSCRIPT_Z3"] ?? "z3";
  const requireDirective = options.requireDirective ?? true;

  const compilerOptions: ts.CompilerOptions = {
    target: ts.ScriptTarget.ES2022,
    // Bundler resolution accepts both `./mod.js` and extensionless `./mod` imports, plus
    // package `exports`, so verified modules resolve the same way in most project setups.
    module: ts.ModuleKind.ESNext,
    moduleResolution: ts.ModuleResolutionKind.Bundler,
    strict: true,
    noUncheckedIndexedAccess: true,
    exactOptionalPropertyTypes: true,
    noImplicitAny: true,
    noEmit: true,
    skipLibCheck: true,
  };

  const program = ts.createProgram(absPaths, compilerOptions);
  const checker = program.getTypeChecker();

  const fileResults: FileVerificationResult[] = [];
  let verifiedFiles = 0;
  let proved = 0;
  let disproved = 0;
  let unknown = 0;
  let errors = 0;

  for (const absPath of absPaths) {
    const sf = program.getSourceFile(absPath);
    if (!sf) {
      errors++;
      fileResults.push({
        file: absPath,
        verifiedDirective: false,
        diagnostics: [
          {
            stage: "typecheck",
            code: "LAW000",
            message: `File not found or unreadable: ${absPath}`,
          },
        ],
        laws: [],
      });
      continue;
    }

    // Files that have not opted in are skipped entirely; they are not held to lawscript's
    // stricter compiler options.
    if (requireDirective && !hasUseVerifiedDirective(sf)) {
      fileResults.push({ file: absPath, verifiedDirective: false, diagnostics: [], laws: [] });
      continue;
    }

    // Stage 1: TypeScript strict typecheck
    // Imported `"use verified";` modules are part of the proof, so they are type-checked too.
    const tsDiags = [sf, ...verifiedDeps(sf, checker)].flatMap((f) => [
      ...program.getSyntacticDiagnostics(f),
      ...program.getSemanticDiagnostics(f),
    ]);

    const diagnostics: Diagnostic[] = tsDiags.map((d) => {
      const message = ts.flattenDiagnosticMessageText(d.messageText, "\n");
      const loc =
        d.file && d.start !== undefined
          ? (() => {
              const { line, character } = d.file.getLineAndCharacterOfPosition(d.start);
              return { file: d.file.fileName, line: line + 1, column: character + 1 };
            })()
          : undefined;
      return {
        stage: "typecheck",
        code: `TS${d.code}`,
        message,
        ...(loc ? { location: loc } : {}),
      };
    });

    if (diagnostics.length > 0) {
      errors += diagnostics.length;
      fileResults.push({
        file: absPath,
        verifiedDirective: false,
        diagnostics,
        laws: [],
      });
      continue;
    }

    // Stage 2: Strict dialect check
    const analysis = analyzeDialect(sf, checker);
    if (requireDirective && !analysis.hasVerifiedDirective) {
      fileResults.push({
        file: absPath,
        verifiedDirective: false,
        diagnostics: [],
        laws: [],
      });
      continue;
    }

    verifiedFiles++;

    if (analysis.diagnostics.length > 0) {
      errors += analysis.diagnostics.length;
      fileResults.push({
        file: absPath,
        verifiedDirective: analysis.hasVerifiedDirective,
        diagnostics: analysis.diagnostics,
        laws: [],
      });
      continue;
    }

    // Stage 3: SMT-LIB2 lowering & Z3 proof checking
    let loweredLaws;
    try {
      loweredLaws = lowerModuleLaws(checker, analysis.functions, analysis.laws);
    } catch (err) {
      const message = err instanceof Error ? err.message : String(err);
      errors++;
      fileResults.push({
        file: absPath,
        verifiedDirective: analysis.hasVerifiedDirective,
        diagnostics: [
          {
            stage: "smt",
            code: "LAW090",
            message: `SMT lowering failed: ${message}`,
            location: getLocation(sf, sf),
          },
        ],
        laws: [],
      });
      continue;
    }

    const concurrency = Math.max(1, options.concurrency ?? 8);
    const lawResults: LawResult[] = new Array<LawResult>(loweredLaws.length);
    let nextIdx = 0;

    const worker = async (): Promise<void> => {
      while (nextIdx < loweredLaws.length) {
        const idx = nextIdx++;
        const lowered = loweredLaws[idx]!;
        const z3Res = await runZ3(lowered, { timeoutMs, z3Path });
        if (z3Res.status === "proved") proved++;
        else if (z3Res.status === "disproved") disproved++;
        else if (z3Res.status === "unknown") unknown++;
        else errors++;

        lawResults[idx] = {
          file: absPath,
          name: lowered.law.name,
          location: lowered.law.location,
          params: lowered.law.params.map((p) => ({ name: p.name, type: p.type })),
          status: z3Res.status,
          durationMs: z3Res.durationMs,
          ...(z3Res.counterexample ? { counterexample: z3Res.counterexample } : {}),
          ...(options.emitSmt ? { smt: lowered.smtScript } : {}),
          ...(z3Res.reason ? { reason: z3Res.reason } : {}),
        };
      }
    };

    const workerCount = Math.min(concurrency, loweredLaws.length);
    await Promise.all(Array.from({ length: workerCount }, () => worker()));

    fileResults.push({
      file: absPath,
      verifiedDirective: analysis.hasVerifiedDirective,
      diagnostics: [],
      laws: lawResults,
    });
  }

  const ok = errors === 0 && disproved === 0 && unknown === 0;
  return {
    ok,
    files: fileResults,
    summary: {
      totalFiles: absPaths.length,
      verifiedFiles,
      proved,
      disproved,
      unknown,
      errors,
    },
  };
}
