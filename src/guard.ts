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
import {
  analyzeDialect,
  isArrayHelper,
  resolveCallee,
  vTypeKey,
  type ArrayHelper,
} from "./dialect.js";
import type { Diagnostic, VType } from "./types.js";
import { VERIFIER_COMPILER_OPTIONS, verifiedDeps } from "./verify.js";

export type GuardImportExt = "js" | "ts" | "none";

export interface GuardOptions {
  /**
   * Extension style for relative imports in generated `.guarded.ts` files:
   * - `"js"`: emit `.js` (`.mjs`/`.cjs` for `.mts`/`.cts`) for transpiled ESM projects.
   * - `"ts"`: emit `.ts` (preserving the source extension) for Node native TS / Deno / Bun / bundlers.
   * - `"none"`: omit the extension for bundler-style imports.
   * When omitted, detected from the source file's relative imports or the nearest `tsconfig.json`
   * (`allowImportingTsExtensions`), falling back to `"js"`.
   */
  readonly importExt?: GuardImportExt;
}

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

function fieldPath(name: string): string {
  return /^[A-Za-z_$][A-Za-z0-9_$]*$/.test(name)
    ? `\`\${at}.${name}\``
    : `at + ${key(`[${JSON.stringify(name)}]`)}`;
}

function typeText(t: VType): string {
  if (t.kind === "bigint" || t.kind === "boolean") return t.kind;
  if (t.kind === "array") return `ReadonlyArray<${typeText(t.element)}>`;
  return `{ ${t.fields.map((f) => `readonly ${key(f.name)}: ${typeText(f.type)}`).join("; ")} }`;
}

/** Local copies of the runtime's array helpers, for `requires` conditions that use them. */
function arrayHelperSource(p: string, helper: ArrayHelper): string {
  switch (helper) {
    case "len":
      return [`function ${p}len<T>(xs: ReadonlyArray<T>): bigint {`, `  return BigInt(xs.length);`, `}`].join("\n");
    case "at":
      return [
        `function ${p}at<T>(xs: ReadonlyArray<T>, index: bigint): T {`,
        `  if (index < 0n || index >= BigInt(xs.length)) throw new RangeError(\`at: index \${index} is out of range for length \${xs.length}\`);`,
        `  return xs[Number(index)] as T;`,
        `}`,
      ].join("\n");
    case "append":
      return [
        `function ${p}append<T>(xs: ReadonlyArray<T>, x: T): ReadonlyArray<T> {`,
        `  return [...xs, x];`,
        `}`,
      ].join("\n");
    case "concat":
      return [
        `function ${p}concat<T>(xs: ReadonlyArray<T>, ys: ReadonlyArray<T>): ReadonlyArray<T> {`,
        `  return [...xs, ...ys];`,
        `}`,
      ].join("\n");
    case "slice":
      return [
        `function ${p}slice<T>(xs: ReadonlyArray<T>, from: bigint, to: bigint): ReadonlyArray<T> {`,
        `  if (from < 0n || from > to || to > BigInt(xs.length)) throw new RangeError(\`slice: range \${from}..\${to} is out of range for length \${xs.length}\`);`,
        `  return xs.slice(Number(from), Number(to));`,
        `}`,
      ].join("\n");
    case "withAt":
      return [
        `function ${p}withAt<T>(xs: ReadonlyArray<T>, index: bigint, value: T): ReadonlyArray<T> {`,
        `  if (index < 0n || index >= BigInt(xs.length)) throw new RangeError(\`withAt: index \${index} is out of range for length \${xs.length}\`);`,
        `  const out = [...xs];`,
        `  out[Number(index)] = value;`,
        `  return out;`,
        `}`,
      ].join("\n");
  }
}

function isExported(decl: ts.FunctionDeclaration): boolean {
  const mods = decl.modifiers ?? [];
  return (
    mods.some((m) => m.kind === ts.SyntaxKind.ExportKeyword) &&
    !mods.some((m) => m.kind === ts.SyntaxKind.DefaultKeyword)
  );
}

/** Check whether the nearest `tsconfig.json` enables `allowImportingTsExtensions`. */
function tsconfigAllowsTsExtensions(dir: string): boolean {
  const configPath = ts.findConfigFile(dir, ts.sys.fileExists);
  if (!configPath) return false;
  const read = ts.readConfigFile(configPath, ts.sys.readFile);
  if (read.error || !read.config) return false;
  const parsed = ts.parseJsonConfigFileContent(read.config, ts.sys, path.dirname(configPath));
  return parsed.options.allowImportingTsExtensions === true;
}

/** Detect the preferred relative import extension style for a verified source file. */
function detectImportExt(sf: ts.SourceFile, dir: string): GuardImportExt {
  let sawTs = false;
  let sawJs = false;
  for (const stmt of sf.statements) {
    if (!ts.isImportDeclaration(stmt) || !ts.isStringLiteral(stmt.moduleSpecifier)) continue;
    const spec = stmt.moduleSpecifier.text;
    if (!spec.startsWith("./") && !spec.startsWith("../")) continue;
    if (/\.[mc]?tsx?$/i.test(spec)) sawTs = true;
    else if (/\.[mc]?jsx?$/i.test(spec)) sawJs = true;
  }
  if (sawTs && !sawJs) return "ts";
  if (sawJs) return "js";
  return tsconfigAllowsTsExtensions(dir) ? "ts" : "js";
}

function formatImportPath(fromDir: string, target: string, extMode: GuardImportExt): string {
  const relRaw = path.relative(fromDir, target).split(path.sep).join("/");
  let rel: string;
  if (extMode === "ts") {
    rel = relRaw;
  } else if (extMode === "none") {
    rel = relRaw.replace(/\.(?:[mc]?ts|tsx)$/i, "");
  } else {
    rel = relRaw.replace(/\.mts$/i, ".mjs").replace(/\.cts$/i, ".cjs").replace(/\.tsx?$/i, ".js");
  }
  return rel.startsWith(".") ? rel : `./${rel}`;
}

export function generateGuards(
  filePaths: ReadonlyArray<string>,
  options: GuardOptions = {},
): GuardResult[] {
  const absPaths = filePaths.map((p) => path.resolve(p));
  const program = ts.createProgram(absPaths, VERIFIER_COMPILER_OPTIONS);
  let checker: ts.TypeChecker;
  try {
    checker = program.getTypeChecker();
  } catch (err) {
    if (!(err instanceof RangeError)) throw err;
    if (absPaths.length === 1) {
      const file = absPaths[0]!;
      const parsed = path.parse(file);
      return [
        {
          file,
          outFile: path.join(parsed.dir, `${parsed.name}.guarded.ts`),
          diagnostics: [
            {
              stage: "typecheck",
              code: "LAW000",
              message: `TypeScript could not process this file or one it imports (${err.message}); an expression is probably nested too deeply`,
            },
          ],
          functions: [],
        },
      ];
    }
    return absPaths.flatMap((p) => generateGuards([p], options));
  }

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

    let tsDiags: ts.Diagnostic[];
    try {
      tsDiags = [sf, ...verifiedDeps(sf, checker)].flatMap((f) => [
        ...program.getSyntacticDiagnostics(f),
        ...program.getSemanticDiagnostics(f),
      ]);
    } catch (err) {
      if (!(err instanceof RangeError)) throw err;
      return {
        file,
        outFile,
        functions: [],
        diagnostics: [
          {
            stage: "typecheck",
            code: "LAW000",
            message: `TypeScript could not process this file or one it imports (${err.message}); an expression is probably nested too deeply`,
          },
        ],
      };
    }
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

    // Choose a prefix for generated helper names that cannot collide with any exported function
    // name, parameter name, or identifier inside a `requires` condition.
    const usedNames = new Set<string>();
    const collectNames = (node: ts.Node): void => {
      if (ts.isIdentifier(node)) usedNames.add(node.text);
      ts.forEachChild(node, collectNames);
    };
    for (const fn of exported) {
      usedNames.add(fn.name);
      for (const param of fn.params) usedNames.add(param.name);
      for (const req of fn.requires) collectNames(req);
    }
    let P = "$";
    while ([...usedNames].some((n) => n.startsWith(P))) P += "_";

    // One checker function per distinct type.
    const checkers = new Map<string, string>();
    const checkerDefs: string[] = [];
    const checkerFor = (t: VType): string => {
      if (t.kind === "bigint") return `${P}bigint`;
      if (t.kind === "boolean") return `${P}boolean`;
      const k = vTypeKey(t);
      const existing = checkers.get(k);
      if (existing) return existing;
      if (t.kind === "array") {
        const name = `${P}array${checkers.size}`;
        checkers.set(k, name);
        const element = checkerFor(t.element);
        checkerDefs.push(
          [
            `function ${name}(fn: string, at: string, v: unknown): ${typeText(t)} {`,
            `  if (!Array.isArray(v)) ${P}fail(fn, \`\${at} must be an array, got \${${P}show(v)}\`);`,
            `  const items: ReadonlyArray<unknown> = v;`,
            `  const out: Array<${typeText(t.element)}> = [];`,
            `  for (let i = 0; i < items.length; i++) out.push(${element}(fn, \`\${at}[\${i}]\`, items[i]));`,
            `  return Object.freeze(out);`,
            `}`,
          ].join("\n"),
        );
        return name;
      }
      const name = `${P}record${checkers.size}`;
      checkers.set(k, name);
      const fields = t.fields.map(
        (f) => `    ${key(f.name)}: ${checkerFor(f.type)}(fn, ${fieldPath(f.name)}, o[${key(f.name)}]),`,
      );
      checkerDefs.push(
        [
          `function ${name}(fn: string, at: string, v: unknown): ${typeText(t)} {`,
          `  if (typeof v !== "object" || v === null || Array.isArray(v)) ${P}fail(fn, \`\${at} must be an object, got \${${P}show(v)}\`);`,
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
    const usedArrayHelpers = new Set<ArrayHelper>();

    /** Source text of a `requires` condition, with callees redirected to what this module can reach. */
    const conditionText = (fnName: string, expr: ts.Expression): string => {
      const edits: Array<{ start: number; end: number; text: string }> = [];
      const visit = (node: ts.Node): void => {
        if (ts.isCallExpression(node) && ts.isIdentifier(node.expression)) {
          const callee = resolveCallee(checker, node.expression);
          let text: string | undefined;
          if (callee.kind === "runtime" && callee.helper === "implies") {
            usesImplies = true;
            text = `${P}implies`;
          } else if (callee.kind === "runtime" && isArrayHelper(callee.helper)) {
            usedArrayHelpers.add(callee.helper);
            text = `${P}${callee.helper}`;
          } else if (callee.kind === "function" && callee.decl.name) {
            if (!isExported(callee.decl)) {
              problems.push({
                stage: "dialect",
                code: "LAW040",
                message: `Cannot generate a guard for \`${fnName}\`: its \`requires\` calls \`${callee.decl.name.text}\`, which is not exported`,
              });
            } else if (callee.decl.getSourceFile() === sf) {
              text = `${P}verified.${callee.decl.name.text}`;
            } else {
              let alias = depImports.get(callee.decl);
              if (!alias) {
                alias = `${P}dep${depImports.size}`;
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
      const rawArgs = fn.params.some((param) => param.name === "args") ? `${P}in` : "args";
      const lines: string[] = [
        `export function ${fn.name}(`,
        `  ...${rawArgs}: Parameters<typeof ${P}verified.${fn.name}>`,
        `): ReturnType<typeof ${P}verified.${fn.name}> {`,
        `  const ${P}args: ReadonlyArray<unknown> = ${rawArgs};`,
        `  if (${P}args.length !== ${fn.params.length}) {`,
        `    ${P}fail(${key(fn.name)}, \`expected ${fn.params.length} argument(s), got \${${P}args.length}\`);`,
        `  }`,
      ];
      fn.params.forEach((param, i) => {
        lines.push(`  const ${param.name} = ${checkerFor(param.type)}(${key(fn.name)}, ${key(param.name)}, ${P}args[${i}]);`);
      });
      for (const req of fn.requires) {
        const text = conditionText(fn.name, req);
        lines.push(`  if (!(${text})) ${P}precondition(${key(fn.name)}, ${key(req.getText(sf).replace(/\s+/g, " "))});`);
      }
      lines.push(`  return ${P}verified.${fn.name}(${fn.params.map((param) => param.name).join(", ")});`, `}`);
      return lines.join("\n");
    });

    if (problems.length > 0) return { file, outFile, diagnostics: problems, functions: [] };

    const extMode = options.importExt ?? detectImportExt(sf, parsed.dir);
    const relImport = (target: string): string => formatImportPath(parsed.dir, target, extMode);
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
      `import * as ${P}verified from ${key(relImport(file))};`,
      ...depImportLines,
      ``,
      `function ${P}show(v: unknown): string {`,
      `  return v === null ? "null" : typeof v === "bigint" ? \`\${v}n\` : typeof v === "object" ? "an object" : \`\${typeof v} \${String(v)}\`;`,
      `}`,
      `function ${P}fail(fn: string, problem: string): never {`,
      `  throw new TypeError(\`\${fn}: \${problem}\`);`,
      `}`,
      `function ${P}precondition(fn: string, condition: string): never {`,
      `  throw new RangeError(\`\${fn}: precondition violated: requires(\${condition})\`);`,
      `}`,
      `function ${P}bigint(fn: string, at: string, v: unknown): bigint {`,
      `  if (typeof v !== "bigint") ${P}fail(fn, \`\${at} must be a bigint, got \${${P}show(v)}\`);`,
      `  return v;`,
      `}`,
      `function ${P}boolean(fn: string, at: string, v: unknown): boolean {`,
      `  if (typeof v !== "boolean") ${P}fail(fn, \`\${at} must be a boolean, got \${${P}show(v)}\`);`,
      `  return v;`,
      `}`,
      ...(usesImplies
        ? [`function ${P}implies(premise: boolean, conclusion: boolean): boolean {`, `  return !premise || conclusion;`, `}`]
        : []),
      ...[...usedArrayHelpers].sort().map((h) => arrayHelperSource(P, h)),
      ...checkerDefs,
      ``,
      wrappers.join("\n\n"),
      ``,
    ].join("\n");

    return { file, outFile, source, diagnostics: [], functions: exported.map((f) => f.name) };
  });
}
