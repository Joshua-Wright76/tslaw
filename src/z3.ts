import { spawn } from "node:child_process";
import type { LoweredLaw, RecordDef } from "./smt.js";
import type { CounterexampleEntry, LawStatus, VType } from "./types.js";

type SExpr = string | SExpr[];

function tokenizeSExpr(input: string): string[] {
  const tokens: string[] = [];
  let i = 0;
  while (i < input.length) {
    const ch = input[i]!;
    if (/\s/.test(ch)) {
      i++;
      continue;
    }
    if (ch === "(" || ch === ")") {
      tokens.push(ch);
      i++;
      continue;
    }
    if (ch === ";") {
      while (i < input.length && input[i] !== "\n") i++;
      continue;
    }
    let start = i;
    while (i < input.length && !/[\s()]/.test(input[i]!)) i++;
    tokens.push(input.slice(start, i));
  }
  return tokens;
}

function parseSExprs(input: string): SExpr[] {
  const tokens = tokenizeSExpr(input);
  let pos = 0;

  const parseOne = (): SExpr => {
    const tok = tokens[pos++];
    if (tok === undefined) throw new Error("Unexpected end of S-expression");
    if (tok === "(") {
      const list: SExpr[] = [];
      while (pos < tokens.length && tokens[pos] !== ")") {
        list.push(parseOne());
      }
      if (tokens[pos] !== ")") throw new Error("Unclosed S-expression");
      pos++;
      return list;
    }
    return tok;
  };

  const results: SExpr[] = [];
  while (pos < tokens.length) {
    results.push(parseOne());
  }
  return results;
}

function decodeSExprValue(
  expr: SExpr,
  type: VType,
  recordsByCtor: ReadonlyMap<string, RecordDef>,
): { formatted: string; raw: unknown } {
  if (type.kind === "bigint") {
    if (typeof expr === "string" && /^\d+$/.test(expr)) {
      const n = BigInt(expr);
      return { formatted: `${n}n`, raw: n };
    }
    if (
      Array.isArray(expr) &&
      expr.length === 2 &&
      expr[0] === "-" &&
      typeof expr[1] === "string" &&
      /^\d+$/.test(expr[1])
    ) {
      const n = -BigInt(expr[1]);
      return { formatted: `${n}n`, raw: n };
    }
    return { formatted: JSON.stringify(expr), raw: expr };
  }

  if (type.kind === "boolean") {
    const b = expr === "true";
    return { formatted: String(b), raw: b };
  }

  if (type.kind === "array") {
    // Solvers print sequences as (as seq.empty (Seq T)), seq.empty, (seq.unit x), or (seq.++ part ...).
    const elements = (e: SExpr): SExpr[] | undefined => {
      if (e === "seq.empty") return [];
      if (!Array.isArray(e)) return undefined;
      if (e[0] === "as" && e[1] === "seq.empty") return [];
      if (e[0] === "seq.unit" && e.length === 2) return [e[1]!];
      if (e[0] === "seq.++") {
        const out: SExpr[] = [];
        for (const part of e.slice(1)) {
          const inner = elements(part);
          if (!inner) return undefined;
          out.push(...inner);
        }
        return out;
      }
      return undefined;
    };
    const items = elements(expr);
    if (!items) return { formatted: JSON.stringify(expr), raw: expr };
    const decoded = items.map((item) => decodeSExprValue(item, type.element, recordsByCtor));
    return {
      formatted: `[${decoded.map((d) => d.formatted).join(", ")}]`,
      raw: decoded.map((d) => d.raw),
    };
  }

  // Record datatype: (mk_Rec_0 val1 val2 ...)
  if (Array.isArray(expr) && typeof expr[0] === "string") {
    const recDef = recordsByCtor.get(expr[0]);
    if (recDef) {
      const rawObj: Record<string, unknown> = {};
      const parts: string[] = [];
      for (let i = 0; i < recDef.fields.length; i++) {
        const field = recDef.fields[i]!;
        const fieldExpr = expr[i + 1];
        if (fieldExpr === undefined) continue;
        const decoded = decodeSExprValue(fieldExpr, field.type, recordsByCtor);
        rawObj[field.name] = decoded.raw;
        parts.push(`${field.name}: ${decoded.formatted}`);
      }
      return { formatted: `{ ${parts.join(", ")} }`, raw: rawObj };
    }
  }

  return { formatted: JSON.stringify(expr), raw: expr };
}

export interface Z3RunResult {
  readonly status: LawStatus;
  readonly durationMs: number;
  readonly counterexample?: ReadonlyArray<CounterexampleEntry>;
  readonly reason?: string;
}

export function runZ3(
  lowered: LoweredLaw,
  options: { timeoutMs: number; z3Path: string },
): Promise<Z3RunResult> {
  return runSolver(lowered, {
    name: "Z3",
    path: options.z3Path,
    args: ["-in", "-smt2", `-T:${Math.max(1, Math.ceil(options.timeoutMs / 1000))}`],
    timeoutMs: options.timeoutMs,
    installHint:
      "Install it (`brew install z3`, `apt-get install z3`) or point to it with --z3 / TSLAW_Z3.",
  });
}

/**
 * Run the same query through cvc5, an independently developed solver. For `unsat` cvc5 also
 * builds a proof and checks it with its internal proof checker (`--check-proofs`); for `sat`
 * it checks the model against the assertions (`--check-models`).
 */
export function runCvc5(
  lowered: LoweredLaw,
  options: { timeoutMs: number; cvc5Path: string },
): Promise<Z3RunResult> {
  return runSolver(lowered, {
    name: "cvc5",
    path: options.cvc5Path,
    args: [
      "--lang", "smt2", "-q",
      `--tlimit=${Math.max(1, Math.ceil(options.timeoutMs))}`,
      "--produce-models", "--check-proofs", "--check-models",
      // Without this cvc5 cannot find counterexamples that involve recursive functions. It
      // assumes those functions terminate, which the termination goals establish separately.
      ...(lowered.smtScript.includes("(define-funs-rec ") ? ["--fmf-fun"] : []),
    ],
    timeoutMs: options.timeoutMs,
    installHint:
      "Install it (https://cvc5.github.io/downloads.html) or point to it with --cvc5 / TSLAW_CVC5.",
  });
}

interface SolverSpec {
  readonly name: string;
  readonly path: string;
  readonly args: ReadonlyArray<string>;
  readonly timeoutMs: number;
  readonly installHint: string;
}

async function runSolver(lowered: LoweredLaw, solver: SolverSpec): Promise<Z3RunResult> {
  const start = performance.now();
  const options = { timeoutMs: solver.timeoutMs };

  return await new Promise<Z3RunResult>((resolve) => {
    const child = spawn(solver.path, [...solver.args], {
      stdio: ["pipe", "pipe", "pipe"],
    });

    let stdout = "";
    let stderr = "";
    let settled = false;

    const finish = (res: Z3RunResult): void => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      resolve(res);
    };

    const timer = setTimeout(() => {
      child.kill("SIGKILL");
      finish({
        status: "unknown",
        durationMs: Math.round(performance.now() - start),
        reason: `${solver.name} timed out after ${options.timeoutMs}ms`,
      });
    }, options.timeoutMs + 500);

    child.stdout.on("data", (chunk: Buffer) => {
      stdout += chunk.toString("utf8");
    });
    child.stderr.on("data", (chunk: Buffer) => {
      stderr += chunk.toString("utf8");
    });

    child.stdin.on("error", () => {
      // Ignore EPIPE when the solver exits before consuming all input; `close`/`error` reports it.
    });

    child.on("error", (err) => {
      finish({
        status: "error",
        durationMs: Math.round(performance.now() - start),
        reason: `Could not run ${solver.name} (\`${solver.path}\`): ${err.message}. ${solver.installHint}`,
      });
    });

    child.on("close", (code, signal) => {
      const durationMs = Math.round(performance.now() - start);
      // cvc5 reports a hit time limit as a message and a non-zero exit, not as a verdict.
      if (/interrupted by timeout/.test(stdout + stderr)) {
        finish({ status: "unknown", durationMs, reason: `${solver.name} timed out after ${options.timeoutMs}ms` });
        return;
      }
      if (signal !== null) {
        finish({
          status: "error",
          durationMs,
          reason: `${solver.name} terminated with signal ${signal}${stderr.trim() ? `: ${stderr.trim()}` : ""}`.slice(0, 500),
        });
        return;
      }
      if (solver.name === "cvc5" && code !== 0 && stderr.trim().length > 0) {
        finish({
          status: "error",
          durationMs,
          reason: `${solver.name} exited with code ${code}: ${stderr.trim()}`.slice(0, 500),
        });
        return;
      }
      const lines = stdout
        .split(/\r?\n/)
        .map((l) => l.trim())
        .filter((l) => l.length > 0);
      const verdict = lines[0];

      // Z3 keeps going after an error and prints a meaningless verdict afterwards, so an
      // error before the verdict means the generated SMT was rejected.
      if (verdict?.startsWith("(error")) {
        const messages: string[] = [];
        for (const l of lines) {
          if (!l.startsWith("(error")) break;
          messages.push(/^\(error "(.*)"\)$/.exec(l)?.[1] ?? l);
        }
        finish({
          status: "error",
          durationMs,
          reason: `${solver.name} rejected the generated SMT-LIB2 (this is a bug in the verifier, please report it): ${messages.join("; ")}`.slice(0, 600),
        });
        return;
      }

      if (verdict === "unsat") {
        finish({ status: "proved", durationMs });
        return;
      }

      if (verdict === "sat") {
        const rest = lines.slice(1).join("\n");
        const counterexample: CounterexampleEntry[] = [];
        if (lowered.paramSmtNames.length > 0 && rest.length > 0) {
          try {
            const parsed = parseSExprs(rest);
            const pairs = parsed[0];
            if (Array.isArray(pairs)) {
              const bySmtName = new Map(
                lowered.paramSmtNames.map((p) => [p.smtName, p]),
              );
              for (const pair of pairs) {
                if (!Array.isArray(pair) || pair.length !== 2 || typeof pair[0] !== "string") {
                  continue;
                }
                const param = bySmtName.get(pair[0]);
                if (!param) continue;
                const decoded = decodeSExprValue(pair[1]!, param.type, lowered.recordsByCtor);
                counterexample.push({
                  name: param.tsName,
                  value: decoded.formatted,
                  raw: decoded.raw,
                });
              }
            }
          } catch {
            // Fall back to empty structured counterexample if Z3 output was unexpected.
          }
        }
        finish({ status: "disproved", durationMs, counterexample });
        return;
      }

      // cvc5 reports a hit time limit as a message and a non-zero exit, not as a verdict.
      if (/interrupted by timeout/.test(stdout + stderr)) {
        finish({ status: "unknown", durationMs, reason: `${solver.name} timed out after ${options.timeoutMs}ms` });
        return;
      }

      if (verdict === "unknown" || verdict === "timeout") {
        finish({
          status: "unknown",
          durationMs,
          reason: stderr.trim() || `${solver.name} returned \`${verdict}\``,
        });
        return;
      }

      finish({
        status: "error",
        durationMs,
        reason: (stderr.trim() || stdout.trim() || `Unexpected ${solver.name} output`).slice(0, 500),
      });
    });

    child.stdin.write(lowered.smtScript);
    child.stdin.end();
  });
}
