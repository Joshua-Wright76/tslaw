import path from "node:path";
import ts from "typescript";
import { analyzeDialect, getLocation } from "./dialect.js";
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

export async function verifyFiles(
  filePaths: ReadonlyArray<string>,
  options: VerifyOptions = {},
): Promise<VerifyReport> {
  const absPaths = filePaths.map((p) => path.resolve(p));
  const timeoutMs = options.timeoutMs ?? DEFAULT_TIMEOUT_MS;
  const z3Path = options.z3Path ?? process.env["VSCRIPT_Z3"] ?? "z3";
  const requireDirective = options.requireDirective ?? true;

  const compilerOptions: ts.CompilerOptions = {
    target: ts.ScriptTarget.ES2022,
    module: ts.ModuleKind.NodeNext,
    moduleResolution: ts.ModuleResolutionKind.NodeNext,
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
            code: "VS000",
            message: `File not found or unreadable: ${absPath}`,
          },
        ],
        laws: [],
      });
      continue;
    }

    // Stage 1: TypeScript strict typecheck
    const tsDiags = [
      ...program.getSyntacticDiagnostics(sf),
      ...program.getSemanticDiagnostics(sf),
    ];

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
            code: "VS090",
            message: `SMT lowering failed: ${message}`,
            location: getLocation(sf, sf),
          },
        ],
        laws: [],
      });
      continue;
    }

    const lawResults: LawResult[] = [];
    for (const lowered of loweredLaws) {
      const z3Res = await runZ3(lowered, { timeoutMs, z3Path });
      if (z3Res.status === "proved") proved++;
      else if (z3Res.status === "disproved") disproved++;
      else if (z3Res.status === "unknown") unknown++;
      else errors++;

      lawResults.push({
        file: absPath,
        name: lowered.law.name,
        location: lowered.law.location,
        status: z3Res.status,
        durationMs: z3Res.durationMs,
        ...(z3Res.counterexample ? { counterexample: z3Res.counterexample } : {}),
        ...(options.emitSmt ? { smt: lowered.smtScript } : {}),
        ...(z3Res.reason ? { reason: z3Res.reason } : {}),
      });
    }

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
