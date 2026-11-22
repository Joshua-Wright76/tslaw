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
    if (typeof expr === "string") {
      const n = BigInt(expr);
      return { formatted: `${n}n`, raw: n };
    }
    if (Array.isArray(expr) && expr.length === 2 && expr[0] === "-" && typeof expr[1] === "string") {
      const n = -BigInt(expr[1]);
      return { formatted: `${n}n`, raw: n };
    }
    return { formatted: JSON.stringify(expr), raw: expr };
  }

  if (type.kind === "boolean") {
    const b = expr === "true";
    return { formatted: String(b), raw: b };
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

export async function runZ3(
  lowered: LoweredLaw,
  options: { timeoutMs: number; z3Path: string },
): Promise<Z3RunResult> {
  const start = performance.now();

  return await new Promise<Z3RunResult>((resolve) => {
    const child = spawn(options.z3Path, ["-in", "-smt2", `-T:${Math.max(1, Math.ceil(options.timeoutMs / 1000))}`], {
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
        reason: `Z3 timed out after ${options.timeoutMs}ms`,
      });
    }, options.timeoutMs + 500);

    child.stdout.on("data", (chunk: Buffer) => {
      stdout += chunk.toString("utf8");
    });
    child.stderr.on("data", (chunk: Buffer) => {
      stderr += chunk.toString("utf8");
    });

    child.on("error", (err) => {
      finish({
        status: "error",
        durationMs: Math.round(performance.now() - start),
        reason:
          `Could not run Z3 (\`${options.z3Path}\`): ${err.message}. ` +
          "Install it (`brew install z3`, `apt-get install z3`) or point to it with --z3 / LAWSCRIPT_Z3.",
      });
    });

    child.on("close", () => {
      const durationMs = Math.round(performance.now() - start);
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
          reason: `Z3 rejected the generated SMT-LIB2 (this is a bug in the verifier, please report it): ${messages.join("; ")}`.slice(0, 600),
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

      if (verdict === "unknown" || verdict === "timeout") {
        finish({
          status: "unknown",
          durationMs,
          reason: stderr.trim() || `Z3 returned \`${verdict}\``,
        });
        return;
      }

      finish({
        status: "error",
        durationMs,
        reason: (stderr.trim() || stdout.trim() || "Unexpected Z3 output").slice(0, 500),
      });
    });

    child.stdin.write(lowered.smtScript);
    child.stdin.end();
  });
}
