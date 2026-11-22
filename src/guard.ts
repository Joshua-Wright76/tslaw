/**
 * `tslaw guard`: generate checked entry points for unverified callers.
 *
 * A proof covers well-typed arguments that satisfy `requires`. Code outside the verified
 * world (plain JavaScript, `any`, casts, parsed JSON) can pass anything. For each exported
 * function of a verified module, the generated `<module>.guarded.ts` exports a wrapper that
 *
 *   1. checks every argument's runtime type, field by field,
 *   2. copies record arguments into fresh frozen objects holding only the declared fields
 *      (so getters, proxies or later mutation cannot change what was checked),
 *   3. evaluates the function's `requires` conditions and throws if one is false, and
 *   4. calls the verified function.
 */
import path from "node:path";
import ts from "typescript";
import { analyzeDialect, resolveCallee, vTypeKey } from "./dialect.js";
import type { Diagnostic, VType } from "./types.js";
import { VERIFIER_COMPILER_OPTIONS } from "./verify.js";

export interface GuardResult {
  readonly file: string;
  /** Where the guard module belongs (`<name>.guarded.ts` next to the source). */
  readonly outFile: string;
  /** The generated module, when generation succeeded and there is something to export. */
  readonly source?: string;
  readonly diagnostics: ReadonlyArray<Diagnostic>;
  /** Names of the functions that got a wrapper. */
  readonly functions: ReadonlyArray<string>;
}

const key = (name: string): string => JSON.stringify(name);

function typeText(t: VType): string {
  if (t.kind === "bigint" || t.kind === "boolean") return t.kind;
  return `{ ${t.fields.map((f) => `readonly ${key(f.name)}: ${typeText(f.type)}`).join("; ")} }`;
}

function isExported(decl: ts.FunctionDeclaration): boolean {
  const mods = decl.modifiers ?? [];
  return (
    mods.some((m) => m.kind === ts.SyntaxKind.ExportKeyword) &&
    !mods.some((m) => m.kind === ts.SyntaxKind.DefaultKeyword)
  );
}

export function generateGuards(filePaths: ReadonlyArray<string>): GuardResult[] {
  const absPaths = filePaths.map((p) => path.resolve(p));
  const program = ts.createProgram(absPaths, VERIFIER_COMPILER_OPTIONS);
  const checker = program.getTypeChecker();

  return absPaths.map((file): GuardResult => {
    const parsed = path.parse(file);
    const outFile = path.join(parsed.dir, `${parsed.name}.guarded.ts`);
    const fail = (code: string, message: string): GuardResult => ({
      file,
      outFile,
      diagnostics: [{ stage: "dialect", code, message }],
      functions: [],
    });

    const sf = program.getSourceFile(file);
    if (!sf) return fail("LAW000", `File not found or unreadable: ${file}`);

    const tsDiags = [...program.getSyntacticDiagnostics(sf), ...program.getSemanticDiagnostics(sf)];
    if (tsDiags.length > 0) {
      return {
        file,
        outFile,
        functions: [],
        diagnostics: tsDiags.map((d) => ({
          stage: "typecheck" as const,
          code: `TS${d.code}`,
          message: ts.flattenDiagnosticMessageText(d.messageText, "\n"),
        })),
      };
    }

    const analysis = analyzeDialect(sf, checker);
    if (!analysis.hasVerifiedDirective) {
      return fail("LAW040", 'Guards can only be generated for modules with a "use verified"; directive');
    }
    if (analysis.diagnostics.length > 0) {
      return { file, outFile, diagnostics: analysis.diagnostics, functions: [] };
    }

    const exported = analysis.functions.filter(
      (f) => f.decl.getSourceFile() === sf && isExported(f.decl),
    );
    if (exported.length === 0) return { file, outFile, diagnostics: [], functions: [] };

    // One checker function per distinct type.
    const checkers = new Map<string, string>();
    const checkerDefs: string[] = [];
    const checkerFor = (t: VType): string => {
      if (t.kind === "bigint") return "$bigint";
      if (t.kind === "boolean") return "$boolean";
      const k = vTypeKey(t);
      const existing = checkers.get(k);
      if (existing) return existing;
      const name = `$record${checkers.size}`;
      checkers.set(k, name);
      const fields = t.fields.map(
        (f) => `    ${key(f.name)}: ${checkerFor(f.type)}(fn, \`\${at}.${f.name}\`, o[${key(f.name)}]),`,
      );
      checkerDefs.push(
        [
          `function ${name}(fn: string, at: string, v: unknown): ${typeText(t)} {`,
          `  if (typeof v !== "object" || v === null) $fail(fn, \`\${at} must be an object, got \${$show(v)}\`);`,
          `  const o = v as Record<string, unknown>;`,
          `  return Object.freeze({`,
          ...fields,
          `  });`,
          `}`,
        ].join("\n"),
      );
      return name;
    };

    // Functions from other modules that `requires` conditions call.
    const depImports = new Map<ts.FunctionDeclaration, string>();
    const problems: Diagnostic[] = [];
    let usesImplies = false;

    /** Source text of a `requires` condition, with callees redirected to what this module can reach. */
    const conditionText = (fnName: string, expr: ts.Expression): string => {
      const edits: Array<{ start: number; end: number; text: string }> = [];
      const visit = (node: ts.Node): void => {
        if (ts.isCallExpression(node) && ts.isIdentifier(node.expression)) {
          const callee = resolveCallee(checker, node.expression);
          let text: string | undefined;
          if (callee.kind === "runtime" && callee.helper === "implies") {
            usesImplies = true;
            text = "$implies";
          } else if (callee.kind === "function" && callee.decl.name) {
            if (!isExported(callee.decl)) {
              problems.push({
                stage: "dialect",
                code: "LAW040",
                message: `Cannot generate a guard for \`${fnName}\`: its \`requires\` calls \`${callee.decl.name.text}\`, which is not exported`,
              });
            } else if (callee.decl.getSourceFile() === sf) {
              text = `$verified.${callee.decl.name.text}`;
            } else {
              let alias = depImports.get(callee.decl);
              if (!alias) {
                alias = `$dep${depImports.size}`;
                depImports.set(callee.decl, alias);
              }
              text = alias;
            }
          }
          if (text) {
            edits.push({ start: node.expression.getStart(sf), end: node.expression.getEnd(), text });
          }
        }
        ts.forEachChild(node, visit);
      };
      visit(expr);
      const base = expr.getStart(sf);
      let out = expr.getText(sf);
      for (const e of edits.sort((a, b) => b.start - a.start)) {
        out = out.slice(0, e.start - base) + e.text + out.slice(e.end - base);
      }
      return out;
    };

    const wrappers = exported.map((fn) => {
      const lines: string[] = [
        `export function ${fn.name}(`,
        `  ...args: Parameters<typeof $verified.${fn.name}>`,
        `): ReturnType<typeof $verified.${fn.name}> {`,
        `  const $args: ReadonlyArray<unknown> = args;`,
        `  if ($args.length !== ${fn.params.length}) {`,
        `    $fail(${key(fn.name)}, \`expected ${fn.params.length} argument(s), got \${$args.length}\`);`,
        `  }`,
      ];
      fn.params.forEach((p, i) => {
        lines.push(`  const ${p.name} = ${checkerFor(p.type)}(${key(fn.name)}, ${key(p.name)}, $args[${i}]);`);
      });
      for (const req of fn.requires) {
        const text = conditionText(fn.name, req);
        lines.push(`  if (!(${text})) $precondition(${key(fn.name)}, ${key(req.getText(sf).replace(/\s+/g, " "))});`);
      }
      lines.push(`  return $verified.${fn.name}(${fn.params.map((p) => p.name).join(", ")});`, `}`);
      return lines.join("\n");
    });

    if (problems.length > 0) return { file, outFile, diagnostics: problems, functions: [] };

    const relImport = (target: string): string => {
      const rel = path.relative(parsed.dir, target).split(path.sep).join("/").replace(/\.tsx?$/, ".js");
      return rel.startsWith(".") ? rel : `./${rel}`;
    };
    const depImportLines = [...depImports].map(
      ([decl, alias]) =>
        `import { ${decl.name!.text} as ${alias} } from ${key(relImport(decl.getSourceFile().fileName))};`,
    );

    const source = [
      `// Generated by \`tslaw guard\` from ${parsed.base}. Do not edit; regenerate instead.`,
      `//`,
      `// Checked entry points for callers that tslaw has not verified. Each wrapper validates its`,
      `// arguments' runtime types, copies records into frozen objects with only the declared`,
      `// fields, checks the function's \`requires\`, and then calls the verified function.`,
      ``,
      `import * as $verified from ${key(`./${parsed.name}.js`)};`,
      ...depImportLines,
      ``,
      `function $show(v: unknown): string {`,
      `  return v === null ? "null" : typeof v === "bigint" ? \`\${v}n\` : typeof v === "object" ? "an object" : \`\${typeof v} \${String(v)}\`;`,
      `}`,
      `function $fail(fn: string, problem: string): never {`,
      `  throw new TypeError(\`\${fn}: \${problem}\`);`,
      `}`,
      `function $precondition(fn: string, condition: string): never {`,
      `  throw new RangeError(\`\${fn}: precondition violated: requires(\${condition})\`);`,
      `}`,
      `function $bigint(fn: string, at: string, v: unknown): bigint {`,
      `  if (typeof v !== "bigint") $fail(fn, \`\${at} must be a bigint, got \${$show(v)}\`);`,
      `  return v;`,
      `}`,
      `function $boolean(fn: string, at: string, v: unknown): boolean {`,
      `  if (typeof v !== "boolean") $fail(fn, \`\${at} must be a boolean, got \${$show(v)}\`);`,
      `  return v;`,
      `}`,
      ...(usesImplies
        ? [`function $implies(premise: boolean, conclusion: boolean): boolean {`, `  return !premise || conclusion;`, `}`]
        : []),
      ...checkerDefs,
      ``,
      wrappers.join("\n\n"),
      ``,
    ].join("\n");

    return { file, outFile, source, diagnostics: [], functions: exported.map((f) => f.name) };
  });
}
