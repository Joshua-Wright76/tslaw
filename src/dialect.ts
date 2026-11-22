import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import ts from "typescript";
import type { Diagnostic, SourceLocation, VType } from "./types.js";

export interface VerifiedParam {
  readonly name: string;
  readonly type: VType;
}

export interface VerifiedFunction {
  readonly name: string;
  /** The declaration node — the function's identity (names are not unique across modules). */
  readonly decl: ts.FunctionDeclaration;
  readonly params: ReadonlyArray<VerifiedParam>;
  readonly returnType: VType;
  readonly body: ts.Block | ts.Expression;
  readonly location: SourceLocation;
  readonly calls: ReadonlySet<ts.FunctionDeclaration>;
  /**
   * Preconditions: the arguments of the leading `requires(...)` statements, in order. They
   * are the first `requires.length` statements of `body`, which evaluation skips.
   */
  readonly requires: ReadonlyArray<ts.Expression>;
  /**
   * Termination measure: the arguments of the `decreases(...)` statement that follows the
   * `requires` statements, compared lexicographically. Empty when there is none.
   */
  readonly decreases: ReadonlyArray<ts.Expression>;
  /** Number of leading `requires`/`decreases` statements in `body`, which evaluation skips. */
  readonly prefixLength: number;
  /**
   * Index of the group of mutually recursive functions this one belongs to. Functions are
   * listed callees first, with the members of a group next to each other.
   */
  readonly scc: number;
  /** True if the function can (directly or through others) call itself. */
  readonly recursive: boolean;
  /** True if the function body contains a `while` loop. */
  readonly hasLoops: boolean;
}

/** `ensures(fn, (...params, result) => post)`. */
export interface VerifiedEnsures {
  readonly fn: ts.FunctionDeclaration;
  readonly fnName: string;
  /** The callback's parameters: the function's parameters followed by its result. */
  readonly params: ReadonlyArray<VerifiedParam>;
  readonly body: ts.Block | ts.Expression;
  readonly location: SourceLocation;
}

export interface VerifiedLaw {
  readonly name: string;
  readonly params: ReadonlyArray<VerifiedParam>;
  readonly body: ts.Block | ts.Expression;
  readonly location: SourceLocation;
}

export interface DialectAnalysis {
  readonly hasVerifiedDirective: boolean;
  readonly diagnostics: Diagnostic[];
  readonly functions: ReadonlyArray<VerifiedFunction>;
  readonly laws: ReadonlyArray<VerifiedLaw>;
  readonly ensures: ReadonlyArray<VerifiedEnsures>;
}

// ---------------------------------------------------------------------------
// Runtime identification
//
// `law` and `implies` get special SMT semantics, so they must be the *real* tslaw runtime
// helpers — not any function that happens to share the name. A user-defined
// `implies = (a, b) => a && b` lowered as SMT `=>` would let false laws be PROVED.
// ---------------------------------------------------------------------------

const MODULE_DIR = path.dirname(fileURLToPath(import.meta.url));
const PACKAGE_ROOT = path.resolve(MODULE_DIR, "..");
const RUNTIME_REL_PATHS = ["src/runtime.ts", "dist/runtime.d.ts", "dist/runtime.js"];
const PACKAGE_ENTRY_REL_PATHS = [...RUNTIME_REL_PATHS, "src/index.ts", "dist/index.d.ts", "dist/index.js"];

function safeRealpath(p: string): string {
  try {
    return fs.realpathSync(p);
  } catch {
    return path.resolve(p);
  }
}

const OWN_PACKAGE_NAME: string | undefined = (() => {
  try {
    const pkg: unknown = JSON.parse(fs.readFileSync(path.join(PACKAGE_ROOT, "package.json"), "utf8"));
    if (typeof pkg === "object" && pkg !== null && "name" in pkg && typeof pkg.name === "string") {
      return pkg.name;
    }
  } catch {
    // Fall through: only bundled runtime paths will be recognized.
  }
  return undefined;
})();

const BUNDLED_RUNTIME_FILES = new Set(
  RUNTIME_REL_PATHS.map((rel) => safeRealpath(path.join(PACKAGE_ROOT, rel))),
);
const BUNDLED_PACKAGE_ENTRY_FILES = new Set(
  PACKAGE_ENTRY_REL_PATHS.map((rel) => safeRealpath(path.join(PACKAGE_ROOT, rel))),
);

const runtimeFileCache = new Map<string, boolean>();
const packageEntryFileCache = new Map<string, boolean>();

function matchesOwnPackageFile(
  fileName: string,
  bundled: ReadonlySet<string>,
  relPaths: ReadonlyArray<string>,
  cache: Map<string, boolean>,
): boolean {
  const cached = cache.get(fileName);
  if (cached !== undefined) return cached;

  const real = safeRealpath(fileName);
  let result = bundled.has(real);
  if (!result && OWN_PACKAGE_NAME) {
    let dir = path.dirname(real);
    while (true) {
      const pkgPath = path.join(dir, "package.json");
      if (fs.existsSync(pkgPath)) {
        try {
          const pkg: unknown = JSON.parse(fs.readFileSync(pkgPath, "utf8"));
          const name =
            typeof pkg === "object" && pkg !== null && "name" in pkg ? pkg.name : undefined;
          const rel = path.relative(dir, real).split(path.sep).join("/");
          result = name === OWN_PACKAGE_NAME && relPaths.includes(rel);
        } catch {
          result = false;
        }
        break;
      }
      const parent = path.dirname(dir);
      if (parent === dir) break;
      dir = parent;
    }
  }
  cache.set(fileName, result);
  return result;
}

/**
 * True if `fileName` is the tslaw runtime module: either this installation's own copy, or
 * the runtime of an installed package with the same name (e.g. a project-local install checked
 * by a globally installed CLI).
 */
export function isTslawRuntimeFile(fileName: string): boolean {
  return matchesOwnPackageFile(fileName, BUNDLED_RUNTIME_FILES, RUNTIME_REL_PATHS, runtimeFileCache);
}

function isTslawPackageEntryFile(fileName: string): boolean {
  return matchesOwnPackageFile(
    fileName,
    BUNDLED_PACKAGE_ENTRY_FILES,
    PACKAGE_ENTRY_REL_PATHS,
    packageEntryFileCache,
  );
}

/** Runtime helpers on arrays, with the number of arguments each takes. */
export const ARRAY_HELPERS = {
  len: 1,
  at: 2,
  append: 2,
  concat: 2,
  slice: 3,
  withAt: 3,
} as const;
export type ArrayHelper = keyof typeof ARRAY_HELPERS;
export const isArrayHelper = (name: string): name is ArrayHelper =>
  Object.prototype.hasOwnProperty.call(ARRAY_HELPERS, name);

export type CalleeRef =
  | {
      readonly kind: "runtime";
      readonly helper:
        | "law"
        | "implies"
        | "requires"
        | "ensures"
        | "decreases"
        | "invariant"
        | ArrayHelper;
    }
  | { readonly kind: "function"; readonly decl: ts.FunctionDeclaration }
  | { readonly kind: "other" };

/**
 * Resolve what an identifier in call position (or an import specifier) actually refers to,
 * following import aliases through the type checker. Functions are identified by their
 * declaration node, never by name.
 */
export function resolveCallee(checker: ts.TypeChecker, ident: ts.Identifier): CalleeRef {
  let sym = checker.getSymbolAtLocation(ident);
  if (!sym) return { kind: "other" };
  if (sym.flags & ts.SymbolFlags.Alias) sym = checker.getAliasedSymbol(sym);
  const decl = sym.valueDeclaration ?? sym.declarations?.[0];
  if (!decl || !ts.isFunctionDeclaration(decl) || !decl.name) return { kind: "other" };
  const name = decl.name.text;
  if (
    (name === "law" ||
      name === "implies" ||
      name === "requires" ||
      name === "ensures" ||
      name === "decreases" ||
      name === "invariant" ||
      isArrayHelper(name)) &&
    isTslawRuntimeFile(decl.getSourceFile().fileName)
  ) {
    return { kind: "runtime", helper: name };
  }
  return { kind: "function", decl };
}

export function getLocation(sf: ts.SourceFile, node: ts.Node): SourceLocation {
  const { line, character } = sf.getLineAndCharacterOfPosition(node.getStart(sf));
  return {
    file: sf.fileName,
    line: line + 1,
    column: character + 1,
  };
}

export function hasUseVerifiedDirective(sf: ts.SourceFile): boolean {
  for (const stmt of sf.statements) {
    if (
      ts.isExpressionStatement(stmt) &&
      ts.isStringLiteral(stmt.expression)
    ) {
      if (stmt.expression.text === "use verified") {
        return true;
      }
      continue;
    }
    break;
  }
  return false;
}

/** `ts.CheckFlags.Readonly` (internal to TypeScript, stable since 2.x). */
const CHECK_FLAGS_READONLY = 1 << 3;

export function vTypeKey(t: VType): string {
  if (t.kind === "bigint") return "Int";
  if (t.kind === "boolean") return "Bool";
  if (t.kind === "array") return `[${vTypeKey(t.element)}]`;
  return `{${t.fields.map((f) => `${JSON.stringify(f.name)}:${vTypeKey(f.type)}`).join(",")}}`;
}

export function vTypesEqual(a: VType, b: VType): boolean {
  return vTypeKey(a) === vTypeKey(b);
}

/**
 * Convert a resolved TypeScript type into a supported tslaw VType.
 *
 * With `declared` set (parameter types), literal types such as `5n` or `true` are rejected:
 * they are modeled as plain `Int`/`Bool`, so a law quantifying over such a parameter would
 * range over values the type does not allow and report bogus counterexamples.
 */
export function resolveVType(
  checker: ts.TypeChecker,
  type: ts.Type,
  seen = new Set<ts.Type>(),
  declared = false,
): { ok: true; type: VType } | { ok: false; reason: string } {
  const flags = type.getFlags();

  if (
    declared &&
    (flags & ts.TypeFlags.BigIntLiteral ||
      (flags & ts.TypeFlags.BooleanLiteral && !(flags & ts.TypeFlags.Boolean)))
  ) {
    const base = flags & ts.TypeFlags.BigIntLiteral ? "bigint" : "boolean";
    return {
      ok: false,
      reason: `literal type \`${checker.typeToString(type)}\` is not supported here; use \`${base}\` and state the restriction with \`implies\``,
    };
  }

  if (flags & (ts.TypeFlags.BigInt | ts.TypeFlags.BigIntLiteral)) {
    return { ok: true, type: { kind: "bigint" } };
  }
  if (flags & (ts.TypeFlags.Boolean | ts.TypeFlags.BooleanLiteral)) {
    return { ok: true, type: { kind: "boolean" } };
  }
  if (flags & (ts.TypeFlags.Number | ts.TypeFlags.NumberLiteral)) {
    return {
      ok: false,
      reason:
        "`number` (IEEE-754 float) is forbidden in verified modules; use `bigint` for exact integer math",
    };
  }
  if (flags & ts.TypeFlags.Any) {
    return { ok: false, reason: "`any` is forbidden in verified modules" };
  }
  if (flags & ts.TypeFlags.Unknown) {
    return { ok: false, reason: "`unknown` is forbidden in verified modules" };
  }
  if (flags & (ts.TypeFlags.Null | ts.TypeFlags.Undefined | ts.TypeFlags.Void)) {
    return {
      ok: false,
      reason: `\`${checker.typeToString(type)}\` is not supported in verified modules`,
    };
  }
  if (type.isUnion()) {
    // A union is fine when every member has the same model: `true | false` is `boolean`,
    // `1n | 2n` (the type of `c ? 1n : 2n`) is `bigint`, and two record shapes with identical
    // fields are one record. Anything else would need a tagged representation.
    const members = type.types.map((t) => resolveVType(checker, t, new Set(seen), declared));
    const first = members[0];
    if (
      first?.ok &&
      members.every((m) => m.ok && vTypeKey(m.type) === vTypeKey(first.type))
    ) {
      return first;
    }
    return {
      ok: false,
      reason: `union type \`${checker.typeToString(type)}\` is not supported in tslaw v0.1`,
    };
  }

  if (flags & ts.TypeFlags.Object) {
    if (seen.has(type)) {
      return { ok: false, reason: "recursive object types are not supported" };
    }
    if (checker.isTupleType(type)) {
      return {
        ok: false,
        reason: `tuple type \`${checker.typeToString(type)}\` is not supported; use a record or an array`,
      };
    }
    if (checker.isArrayType(type)) {
      // `T[]` and `readonly T[]` are the same to verified code, which cannot mutate either.
      const element = checker.getTypeArguments(type as ts.TypeReference)[0];
      if (!element) return { ok: false, reason: "array type without an element type" };
      if (element.getFlags() & ts.TypeFlags.Never) {
        return {
          ok: false,
          reason: "cannot tell the element type of this array; give it a type annotation",
        };
      }
      const resolved = resolveVType(checker, element, new Set(seen), declared);
      if (!resolved.ok) return { ok: false, reason: `array element: ${resolved.reason}` };
      return { ok: true, type: { kind: "array", element: resolved.type } };
    }
    if (type.getCallSignatures().length > 0) {
      return { ok: false, reason: "higher-order function values are not supported" };
    }
    if (type.getConstructSignatures().length > 0) {
      return { ok: false, reason: "constructor types are not supported" };
    }
    if (type.getStringIndexType() || type.getNumberIndexType()) {
      return { ok: false, reason: "index signatures are not supported in verified records" };
    }
    const props = type.getProperties();
    if (props.length === 0) {
      return { ok: false, reason: "empty object types are not supported" };
    }
    seen.add(type);
    const fields: Array<{ name: string; type: VType }> = [];
    for (const prop of props) {
      if (String(prop.escapedName).startsWith("__@")) {
        return {
          ok: false,
          reason: `symbol-keyed field \`${prop.name}\` is not supported in verified records`,
        };
      }
      if (prop.name === "__proto__") {
        return {
          ok: false,
          reason: "field `__proto__` is forbidden in verified records (it alters prototypes in JavaScript instead of defining a normal field)",
        };
      }
      if (prop.flags & ts.SymbolFlags.Optional) {
        return {
          ok: false,
          reason: `optional field \`${prop.name}?\` is not supported in verified records`,
        };
      }
      const decl = prop.valueDeclaration ?? prop.declarations?.[0];
      if (!decl) {
        return { ok: false, reason: `cannot inspect field \`${prop.name}\`` };
      }
      // Properties made readonly by a mapped type (`Readonly<T>`) keep their original,
      // unmodified declaration; the readonly-ness lives on the symbol's check flags.
      const checkFlags =
        (prop as { links?: { checkFlags?: number } }).links?.checkFlags ??
        (prop as { checkFlags?: number }).checkFlags ??
        0;
      const isReadonly =
        (checkFlags & CHECK_FLAGS_READONLY) !== 0 ||
        ((ts.isPropertySignature(decl) || ts.isPropertyDeclaration(decl))
          ? Boolean(decl.modifiers?.some((m) => m.kind === ts.SyntaxKind.ReadonlyKeyword))
          : ts.isPropertyAssignment(decl) || ts.isShorthandPropertyAssignment(decl));
      if (!isReadonly) {
        return {
          ok: false,
          reason: `mutable record field \`${prop.name}\` must be marked \`readonly\``,
        };
      }
      const propType = checker.getTypeOfSymbolAtLocation(prop, decl);
      const resolved = resolveVType(checker, propType, new Set(seen), declared);
      if (!resolved.ok) {
        return { ok: false, reason: `field \`${prop.name}\`: ${resolved.reason}` };
      }
      fields.push({ name: prop.name, type: resolved.type });
    }
    fields.sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
    return { ok: true, type: { kind: "record", fields } };
  }

  return {
    ok: false,
    reason: `unsupported type \`${checker.typeToString(type)}\` (supported: bigint, boolean, readonly records)`,
  };
}

/** Analyses that have started but not finished (their module is somewhere up the import chain). */
const IN_PROGRESS = new WeakSet<DialectAnalysis>();

/**
 * Analyze a TypeScript source file against the tslaw sound pure subset.
 */
export function analyzeDialect(
  sf: ts.SourceFile,
  checker: ts.TypeChecker,
  visited = new Map<string, DialectAnalysis>(),
): DialectAnalysis {
  const cached = visited.get(sf.fileName);
  if (cached) return cached;

  const hasVerifiedDirective = hasUseVerifiedDirective(sf);
  const diagnostics: Diagnostic[] = [];
  /** This file's functions, before they are grouped and ordered by the call graph. */
  type ParsedFunction = Omit<VerifiedFunction, "scc" | "recursive"> & {
    /** Functions called from `requires` and `decreases`. */
    readonly specCalls: ReadonlySet<ts.FunctionDeclaration>;
    /** Functions called from inside loops. */
    readonly loopCalls: ReadonlySet<ts.FunctionDeclaration>;
  };
  const parsed: ParsedFunction[] = [];
  const functions: VerifiedFunction[] = [];
  const laws: VerifiedLaw[] = [];
  const ensuresList: VerifiedEnsures[] = [];

  // Pre-seed cache to guard against cyclic imports.
  const stub: DialectAnalysis = {
    hasVerifiedDirective,
    diagnostics,
    functions,
    laws,
    ensures: ensuresList,
  };
  visited.set(sf.fileName, stub);
  IN_PROGRESS.add(stub);

  const addError = (code: string, message: string, node: ts.Node): void => {
    diagnostics.push({
      stage: "dialect",
      code,
      message,
      location: getLocation(sf, node),
    });
  };

  // Type-check suppression comments would let ill-typed code past Stage 1, and every later
  // stage assumes the code is well-typed.
  const scanner = ts.createScanner(ts.ScriptTarget.ES2022, false, ts.LanguageVariant.Standard, sf.text);
  for (let tok = scanner.scan(); tok !== ts.SyntaxKind.EndOfFileToken; tok = scanner.scan()) {
    if (
      tok !== ts.SyntaxKind.SingleLineCommentTrivia &&
      tok !== ts.SyntaxKind.MultiLineCommentTrivia
    ) {
      continue;
    }
    const m = /@ts-(ignore|expect-error|nocheck)\b/.exec(scanner.getTokenText());
    if (m) {
      const { line, character } = sf.getLineAndCharacterOfPosition(scanner.getTokenStart());
      diagnostics.push({
        stage: "dialect",
        code: "LAW033",
        message: `\`@ts-${m[1]}\` is forbidden in verified modules (it hides type errors the proof relies on)`,
        location: { file: sf.fileName, line: line + 1, column: character + 1 },
      });
    }
  }

  // Track cross-file `"use verified";` imports. Runtime helpers (`law`, `implies`) and
  // verified functions are identified by resolving symbols, never by name.
  const importedFunctions = new Map<ts.FunctionDeclaration, VerifiedFunction>();
  const importedEnsures = new Set<VerifiedEnsures>();
  const analyzedDeps = new Set<string>();
  for (const stmt of sf.statements) {
    if (!ts.isImportDeclaration(stmt)) continue;
    if (!stmt.importClause) {
      addError("LAW001", "Side-effect imports are not allowed in verified modules", stmt);
      continue;
    }
    if (stmt.importClause.isTypeOnly) continue;
    if (stmt.importClause.name) {
      addError("LAW001", "Default imports are not allowed in verified modules", stmt);
      if (!stmt.importClause.namedBindings) continue;
    } else if (!stmt.importClause.namedBindings) {
      addError("LAW001", "Default imports are not allowed in verified modules", stmt);
      continue;
    }
    if (!ts.isNamedImports(stmt.importClause.namedBindings)) {
      addError("LAW001", "Namespace imports are not allowed in verified modules", stmt);
      continue;
    }
    const specSf = checker
      .getSymbolAtLocation(stmt.moduleSpecifier)
      ?.declarations?.find(ts.isSourceFile);
    for (const elem of stmt.importClause.namedBindings.elements) {
      if (elem.isTypeOnly) continue;
      const orig = elem.propertyName?.text ?? elem.name.text;
      const callee = resolveCallee(checker, elem.name);
      if (callee.kind === "runtime") {
        if (specSf && !isTslawPackageEntryFile(specSf.fileName)) {
          addError(
            "LAW001",
            `\`${orig}\` must be imported directly from the tslaw package (not re-exported through ${specSf.fileName})`,
            elem,
          );
        }
        continue;
      }
      const sym = checker.getSymbolAtLocation(elem.name);
      const target = sym && (sym.flags & ts.SymbolFlags.Alias) !== 0
        ? checker.getAliasedSymbol(sym)
        : sym;
      const decl = target?.valueDeclaration ?? target?.declarations?.[0];
      if (decl && (ts.isTypeAliasDeclaration(decl) || ts.isInterfaceDeclaration(decl))) {
        continue;
      }
      if (callee.kind === "function") {
        const depSf = callee.decl.getSourceFile();
        if ((orig === "law" || orig === "implies") && !hasUseVerifiedDirective(depSf)) {
          addError(
            "LAW001",
            `\`${orig}\` must be imported from the tslaw runtime (found a different \`${orig}\` in ${depSf.fileName})`,
            elem,
          );
          continue;
        }
        if (!hasUseVerifiedDirective(depSf)) {
          addError(
            "LAW001",
            `Imported function \`${orig}\` is from an unverified module (add \`"use verified";\` to ${depSf.fileName})`,
            elem,
          );
          continue;
        }
        if (specSf && specSf !== depSf && !hasUseVerifiedDirective(specSf)) {
          addError(
            "LAW001",
            `Imported function \`${orig}\` is re-exported through an unverified module (${specSf.fileName}); import it directly from ${depSf.fileName}`,
            elem,
          );
          continue;
        }
        if (!analyzedDeps.has(depSf.fileName)) {
          analyzedDeps.add(depSf.fileName);
          const depAnalysis = analyzeDialect(depSf, checker, visited);
          if (IN_PROGRESS.has(depAnalysis)) {
            // Its analysis is not finished, so its functions (and any recursion through them)
            // cannot be seen from here.
            addError(
              "LAW001",
              `Verified modules may not import each other in a cycle (${sf.fileName} and ${depSf.fileName}); put mutually recursive functions in one module`,
              elem,
            );
            continue;
          }
          diagnostics.push(...depAnalysis.diagnostics);
          for (const depFn of depAnalysis.functions) {
            importedFunctions.set(depFn.decl, depFn);
          }
          for (const depEnsures of depAnalysis.ensures) importedEnsures.add(depEnsures);
        }
        continue;
      }
      addError(
        "LAW001",
        `Verified modules may only import \`law\`, \`implies\`, types, or functions from other \`"use verified";\` modules (found \`${orig}\`)`,
        elem,
      );
    }
  }

  const checkBody = (
    body: ts.Block | ts.Expression,
    localNames: Set<string>,
    callsOut: Set<ts.FunctionDeclaration>,
    /**
     * When given, the leading `requires(...)` statements and one `decreases(...)` after them
     * are allowed and collected here.
     */
    spec?: {
      readonly requires: ts.Expression[];
      readonly decreases: ts.Expression[];
      readonly calls: Set<ts.FunctionDeclaration>;
      /** Functions called from inside loops. */
      readonly loopCalls: Set<ts.FunctionDeclaration>;
      prefixLength: number;
      hasLoops: boolean;
    },
  ): void => {
    const asSpec = (
      stmt: ts.Statement,
      helper: "requires" | "decreases" | "invariant",
    ): ts.CallExpression | undefined => {
      if (
        ts.isExpressionStatement(stmt) &&
        ts.isCallExpression(stmt.expression) &&
        ts.isIdentifier(stmt.expression.expression)
      ) {
        const callee = resolveCallee(checker, stmt.expression.expression);
        if (callee.kind === "runtime" && callee.helper === helper) return stmt.expression;
      }
      return undefined;
    };
    /** Set while checking a `requires`/`decreases` argument. */
    let inSpec = false;
    /** Number of enclosing `while` loops. */
    let loopDepth = 0;
    const checkSpecExpr = (expr: ts.Expression, scope: Set<string>): void => {
      inSpec = true;
      try {
        checkExpr(expr, scope);
      } finally {
        inSpec = false;
      }
    };

    // JavaScript lets any value act as a condition (`0n` is falsy). The SMT encoding has no
    // truthiness, so conditions and logical operands must be real booleans.
    const requireBoolean = (expr: ts.Expression): void => {
      const t = resolveVType(checker, checker.getTypeAtLocation(expr));
      if (t.ok && t.type.kind !== "boolean") {
        addError(
          "LAW034",
          "Conditions and operands of `!`, `&&`, `||` must be `boolean`; write an explicit comparison such as `x !== 0n`",
          expr,
        );
      }
    };

    const checkExpr = (expr: ts.Expression, scope: Set<string>): void => {
      if (ts.isParenthesizedExpression(expr)) {
        checkExpr(expr.expression, scope);
        return;
      }
      if (
        ts.isBigIntLiteral(expr) ||
        expr.kind === ts.SyntaxKind.TrueKeyword ||
        expr.kind === ts.SyntaxKind.FalseKeyword
      ) {
        return;
      }
      if (ts.isNumericLiteral(expr)) {
        addError(
          "LAW010",
          `Numeric literal \`${expr.text}\` is a float; use a bigint literal like \`${expr.text}n\``,
          expr,
        );
        return;
      }
      if (ts.isIdentifier(expr)) {
        if (!scope.has(expr.text)) {
          addError(
            "LAW011",
            `Identifier \`${expr.text}\` is not a local parameter or const binding (globals are forbidden)`,
            expr,
          );
        }
        return;
      }
      if (ts.isPrefixUnaryExpression(expr)) {
        if (
          expr.operator !== ts.SyntaxKind.MinusToken &&
          expr.operator !== ts.SyntaxKind.ExclamationToken
        ) {
          addError("LAW012", "Prefix unary operators (`+`, `++`, `--`, `~`) are forbidden (only `-` and `!` are allowed)", expr);
          return;
        }
        if (expr.operator === ts.SyntaxKind.ExclamationToken) requireBoolean(expr.operand);
        checkExpr(expr.operand, scope);
        return;
      }
      if (ts.isPostfixUnaryExpression(expr)) {
        addError("LAW012", "Mutating postfix operators (`++`, `--`) are forbidden", expr);
        return;
      }
      if (ts.isBinaryExpression(expr)) {
        const op = expr.operatorToken.kind;
        const allowed = new Set<ts.SyntaxKind>([
          ts.SyntaxKind.PlusToken,
          ts.SyntaxKind.MinusToken,
          ts.SyntaxKind.AsteriskToken,
          ts.SyntaxKind.LessThanToken,
          ts.SyntaxKind.LessThanEqualsToken,
          ts.SyntaxKind.GreaterThanToken,
          ts.SyntaxKind.GreaterThanEqualsToken,
          ts.SyntaxKind.EqualsEqualsEqualsToken,
          ts.SyntaxKind.ExclamationEqualsEqualsToken,
          ts.SyntaxKind.AmpersandAmpersandToken,
          ts.SyntaxKind.BarBarToken,
        ]);
        if (op === ts.SyntaxKind.SlashToken || op === ts.SyntaxKind.PercentToken) {
          addError(
            "LAW013",
            "Division `/` and modulo `%` are not yet supported in tslaw v0.1 (JS truncating semantics differ from SMT Euclidean div)",
            expr.operatorToken,
          );
          return;
        }
        if (!allowed.has(op)) {
          addError(
            "LAW014",
            `Operator \`${expr.operatorToken.getText(sf)}\` is forbidden in verified modules`,
            expr.operatorToken,
          );
          return;
        }
        if (
          op === ts.SyntaxKind.EqualsEqualsEqualsToken ||
          op === ts.SyntaxKind.ExclamationEqualsEqualsToken
        ) {
          const lt = resolveVType(checker, checker.getTypeAtLocation(expr.left));
          const rt = resolveVType(checker, checker.getTypeAtLocation(expr.right));
          const byIdentity = (k: string): boolean => k === "record" || k === "array";
          if ((lt.ok && byIdentity(lt.type.kind)) || (rt.ok && byIdentity(rt.type.kind))) {
            addError(
              "LAW015",
              "Direct `===`/`!==` on records and arrays is forbidden (JS compares object identity, not contents); compare fields or elements explicitly",
              expr,
            );
          }
        }
        if (op === ts.SyntaxKind.AmpersandAmpersandToken || op === ts.SyntaxKind.BarBarToken) {
          requireBoolean(expr.left);
          requireBoolean(expr.right);
        }
        checkExpr(expr.left, scope);
        checkExpr(expr.right, scope);
        return;
      }
      if (ts.isConditionalExpression(expr)) {
        requireBoolean(expr.condition);
        checkExpr(expr.condition, scope);
        checkExpr(expr.whenTrue, scope);
        checkExpr(expr.whenFalse, scope);
        return;
      }
      if (ts.isPropertyAccessExpression(expr)) {
        checkExpr(expr.expression, scope);
        const objType = resolveVType(checker, checker.getTypeAtLocation(expr.expression));
        if (!objType.ok || objType.type.kind !== "record") {
          addError(
            "LAW016",
            objType.ok && objType.type.kind === "array"
              ? "Array properties and methods are not available in verified modules; use `len`, `at`, `append`, `concat`, `slice`, `withAt` from the tslaw runtime"
              : "Property access is only allowed on verified `readonly` records",
            expr,
          );
        } else if (!objType.type.fields.some((f) => f.name === expr.name.text)) {
          // Every object also has inherited members (`constructor`, `toString`, ...).
          addError(
            "LAW016",
            `\`${expr.name.text}\` is not a declared field of this record`,
            expr.name,
          );
        }
        return;
      }
      if (ts.isArrayLiteralExpression(expr)) {
        for (const el of expr.elements) {
          if (ts.isSpreadElement(el) || ts.isOmittedExpression(el)) {
            addError("LAW039", "Spread and holes in array literals are not supported; use `concat`", el);
            continue;
          }
          checkExpr(el, scope);
        }
        return;
      }
      if (ts.isElementAccessExpression(expr)) {
        addError(
          "LAW039",
          "`xs[i]` is not supported (it is `undefined` out of range, and indexes with `number`); use `at(xs, i)` with a `bigint` index",
          expr,
        );
        return;
      }
      if (ts.isObjectLiteralExpression(expr)) {
        for (const prop of expr.properties) {
          if (ts.isPropertyAssignment(prop)) {
            if (!ts.isIdentifier(prop.name)) {
              addError("LAW017", "Computed or non-identifier record keys are forbidden", prop.name);
              continue;
            }
            if (prop.name.text === "__proto__") {
              addError("LAW017", "`__proto__` is forbidden as a record key", prop.name);
              continue;
            }
            checkExpr(prop.initializer, scope);
          } else if (ts.isShorthandPropertyAssignment(prop)) {
            if (prop.name.text === "__proto__") {
              addError("LAW017", "`__proto__` is forbidden as a record key", prop.name);
              continue;
            }
            checkExpr(prop.name, scope);
          } else {
            addError(
              "LAW017",
              "Object spread, getters, setters, and methods are forbidden in verified records",
              prop,
            );
          }
        }
        return;
      }
      if (ts.isCallExpression(expr)) {
        if (!ts.isIdentifier(expr.expression)) {
          addError("LAW018", "Only direct calls to verified functions or `implies` are allowed", expr);
          return;
        }
        const fnName = expr.expression.text;
        const callee = resolveCallee(checker, expr.expression);
        if (callee.kind === "runtime" && callee.helper === "implies") {
          if (expr.arguments.length !== 2) {
            addError("LAW018", "`implies` requires exactly 2 arguments", expr);
          }
          for (const arg of expr.arguments) checkExpr(arg, scope);
          return;
        }
        if (callee.kind === "runtime" && isArrayHelper(callee.helper)) {
          const arity = ARRAY_HELPERS[callee.helper];
          const first = expr.arguments[0];
          if (expr.arguments.length !== arity || !first) {
            addError("LAW039", `\`${callee.helper}\` takes exactly ${arity} argument(s)`, expr);
          } else {
            const t = resolveVType(checker, checker.getTypeAtLocation(first));
            if (!t.ok || t.type.kind !== "array") {
              addError(
                "LAW039",
                `The first argument of \`${callee.helper}\` must be an array of a supported, known element type${t.ok ? "" : ` (${t.reason})`}`,
                first,
              );
            }
          }
          for (const arg of expr.arguments) checkExpr(arg, scope);
          return;
        }
        const calleeSf = callee.kind === "function" ? callee.decl.getSourceFile() : undefined;
        const isVerifiedCallee =
          callee.kind === "function" &&
          calleeSf !== undefined &&
          ts.isSourceFile(callee.decl.parent) &&
          (calleeSf === sf || analyzedDeps.has(calleeSf.fileName));
        if (!isVerifiedCallee) {
          addError(
            "LAW018",
            `Call to unverified function \`${fnName}\` is forbidden inside verified modules`,
            expr,
          );
          return;
        }
        callsOut.add(callee.decl);
        if (inSpec) spec?.calls.add(callee.decl);
        if (loopDepth > 0) spec?.loopCalls.add(callee.decl);
        for (const arg of expr.arguments) checkExpr(arg, scope);
        return;
      }
      if (
        ts.isAsExpression(expr) ||
        ts.isTypeAssertionExpression(expr) ||
        ts.isNonNullExpression(expr)
      ) {
        addError("LAW019", "Type assertions (`as`, `!`) are forbidden in verified modules", expr);
        return;
      }
      addError(
        "LAW020",
        `Expression kind \`${ts.SyntaxKind[expr.kind]}\` is not allowed in verified modules`,
        expr,
      );
    };

    /** Assignment to a local: `x = e`, `x += e`, `x -= e`, `x *= e`. */
    const asAssignment = (stmt: ts.Statement): ts.BinaryExpression | undefined => {
      if (!ts.isExpressionStatement(stmt) || !ts.isBinaryExpression(stmt.expression)) return undefined;
      const op = stmt.expression.operatorToken.kind;
      return op === ts.SyntaxKind.EqualsToken ||
        op === ts.SyntaxKind.PlusEqualsToken ||
        op === ts.SyntaxKind.MinusEqualsToken ||
        op === ts.SyntaxKind.AsteriskEqualsToken
        ? stmt.expression
        : undefined;
    };

    interface BlockContext {
      /** Names in scope. */
      readonly scope: Set<string>;
      /** The subset of `scope` declared with `let`. */
      readonly mutable: Set<string>;
      /** Inside a loop body, where `return` is not allowed. */
      readonly inLoop: boolean;
    }

    const checkAssignment = (assign: ts.BinaryExpression, ctx: BlockContext): void => {
      if (!ts.isIdentifier(assign.left) || !ctx.mutable.has(assign.left.text)) {
        addError(
          "LAW038",
          "Only a local variable declared with `let` can be assigned",
          assign.left,
        );
      }
      checkExpr(assign.right, ctx.scope);
    };

    const checkBlock = (
      block: ts.Block,
      outer: BlockContext,
      kind: "function" | "loop" | "plain" = "plain",
    ): boolean => {
      const ctx: BlockContext = {
        scope: new Set(outer.scope),
        mutable: new Set(outer.mutable),
        inLoop: outer.inLoop || kind === "loop",
      };
      const { scope } = ctx;
      let terminated = false;
      let inRequiresPrefix = kind === "function" && spec !== undefined;
      let mayDeclareMeasure = inRequiresPrefix || kind === "loop";
      let inInvariantPrefix = kind === "loop";
      let hasMeasure = false;

      for (const stmt of block.statements) {
        const inv = asSpec(stmt, "invariant");
        if (inv) {
          const cond = inv.arguments[0];
          if (!inInvariantPrefix) {
            addError(
              "LAW038",
              "`invariant(...)` must be the first statement(s) of a `while` loop body",
              stmt,
            );
          } else if (inv.arguments.length !== 1 || !cond) {
            addError("LAW038", "`invariant` takes exactly one boolean condition", stmt);
          } else {
            requireBoolean(cond);
            checkExpr(cond, scope);
          }
          continue;
        }
        inInvariantPrefix = false;
        const dec = asSpec(stmt, "decreases");
        if (dec) {
          if (!mayDeclareMeasure) {
            addError(
              "LAW037",
              "`decreases(...)` must directly follow the `requires` statements at the start of a verified function body (or the `invariant` statements at the start of a loop body), and may appear only once",
              stmt,
            );
            continue;
          }
          inRequiresPrefix = false;
          mayDeclareMeasure = false;
          hasMeasure = true;
          if (kind === "function" && spec) spec.prefixLength++;
          if (dec.arguments.length === 0) {
            addError("LAW037", "`decreases` needs at least one `bigint` measure", stmt);
            continue;
          }
          for (const m of dec.arguments) {
            const t = resolveVType(checker, checker.getTypeAtLocation(m));
            if (t.ok && t.type.kind !== "bigint") {
              addError("LAW037", "Each `decreases` measure must be a `bigint`", m);
            }
            if (kind === "function" && spec) {
              checkSpecExpr(m, scope);
              spec.decreases.push(m);
            } else {
              checkExpr(m, scope);
            }
          }
          continue;
        }
        const req = asSpec(stmt, "requires");
        if (req) {
          if (!inRequiresPrefix) {
            addError(
              "LAW035",
              "`requires(...)` must be the first statement(s) of a verified function body",
              stmt,
            );
            continue;
          }
          const cond = req.arguments[0];
          if (req.arguments.length !== 1 || !cond) {
            addError("LAW035", "`requires` takes exactly one boolean condition", stmt);
            continue;
          }
          requireBoolean(cond);
          checkSpecExpr(cond, scope);
          spec?.requires.push(cond);
          if (spec) spec.prefixLength++;
          continue;
        }
        inRequiresPrefix = false;
        mayDeclareMeasure = false;
        if (terminated) {
          addError("LAW021", "Unreachable statement after `return`", stmt);
          break;
        }
        if (ts.isVariableStatement(stmt)) {
          const isConst = (stmt.declarationList.flags & ts.NodeFlags.Const) !== 0;
          const isLet = (stmt.declarationList.flags & ts.NodeFlags.Let) !== 0;
          if (!isConst && !isLet) {
            addError("LAW022", "`var` is forbidden; use `const` or `let`", stmt);
            continue;
          }
          for (const decl of stmt.declarationList.declarations) {
            if (!decl.initializer) {
              addError("LAW022", "Local declarations must have an initializer", decl);
              continue;
            }
            checkExpr(decl.initializer, scope);
            // For `const x: T = init` the binding has type T, which may be narrower than (or a
            // simplification of) the initializer's own type.
            const initType = resolveVType(
              checker,
              checker.getTypeAtLocation(ts.isIdentifier(decl.name) ? decl.name : decl.initializer),
            );
            if (!initType.ok) {
              addError("LAW023", `Invalid local type: ${initType.reason}`, decl);
            }
            if (ts.isIdentifier(decl.name)) {
              scope.add(decl.name.text);
              if (isLet) ctx.mutable.add(decl.name.text);
              else ctx.mutable.delete(decl.name.text);
            } else if (ts.isObjectBindingPattern(decl.name) && isConst) {
              if (initType.ok && initType.type.kind !== "record") {
                addError("LAW022", "Object destructuring is only allowed on verified `readonly` records", decl.name);
              }
              for (const el of decl.name.elements) {
                if (el.dotDotDotToken || el.initializer || !ts.isIdentifier(el.name)) {
                  addError("LAW022", "Rest/default/nested destructuring is not supported", el);
                  continue;
                }
                if (el.propertyName && !ts.isIdentifier(el.propertyName)) {
                  addError("LAW022", "Computed or non-identifier destructuring keys are forbidden", el.propertyName);
                  continue;
                }
                const propName =
                  el.propertyName && ts.isIdentifier(el.propertyName)
                    ? el.propertyName.text
                    : el.name.text;
                if (
                  initType.ok &&
                  initType.type.kind === "record" &&
                  !initType.type.fields.some((f) => f.name === propName)
                ) {
                  addError("LAW016", `\`${propName}\` is not a declared field of this record`, el.propertyName ?? el.name);
                }
                scope.add(el.name.text);
                ctx.mutable.delete(el.name.text);
              }
            } else {
              addError("LAW022", "Unsupported binding pattern", decl.name);
            }
          }
          continue;
        }
        const assign = asAssignment(stmt);
        if (assign) {
          checkAssignment(assign, ctx);
          continue;
        }
        if (ts.isReturnStatement(stmt)) {
          if (ctx.inLoop) {
            addError("LAW038", "`return` inside a loop is not supported; leave the loop through its condition", stmt);
          } else if (!stmt.expression) {
            addError("LAW024", "Bare `return;` is forbidden; verified functions must return a value", stmt);
          } else {
            checkExpr(stmt.expression, scope);
          }
          terminated = true;
          continue;
        }
        if (ts.isIfStatement(stmt)) {
          requireBoolean(stmt.expression);
          checkExpr(stmt.expression, scope);
          const checkBranch = (branch: ts.Statement): boolean => {
            if (ts.isBlock(branch)) return checkBlock(branch, ctx);
            if (ts.isReturnStatement(branch) || ts.isIfStatement(branch) || asAssignment(branch)) {
              return checkBlock(ts.factory.createBlock([branch]), ctx);
            }
            addError(
              "LAW025",
              "Only blocks, `return`, an assignment, or `else if` are allowed as `if` branches",
              branch,
            );
            return false;
          };
          const thenReturns = checkBranch(stmt.thenStatement);
          const elseReturns = stmt.elseStatement ? checkBranch(stmt.elseStatement) : false;
          if (thenReturns && elseReturns) terminated = true;
          continue;
        }
        if (ts.isWhileStatement(stmt)) {
          if (!spec) {
            addError(
              "LAW026",
              "Loops are only allowed in function bodies; move the loop into a verified function",
              stmt,
            );
            continue;
          }
          requireBoolean(stmt.expression);
          checkExpr(stmt.expression, scope);
          if (!ts.isBlock(stmt.statement)) {
            addError("LAW038", "A `while` loop body must be a block", stmt.statement);
            continue;
          }
          if (spec) spec.hasLoops = true;
          loopDepth++;
          try {
            checkBlock(stmt.statement, ctx, "loop");
          } finally {
            loopDepth--;
          }
          continue;
        }
        if (
          ts.isDoStatement(stmt) ||
          ts.isForStatement(stmt) ||
          ts.isForInStatement(stmt) ||
          ts.isForOfStatement(stmt)
        ) {
          addError("LAW026", "Only `while` loops are supported in verified modules", stmt);
          continue;
        }
        if (ts.isThrowStatement(stmt) || ts.isTryStatement(stmt)) {
          addError("LAW027", "Exceptions (`throw`/`try`) are forbidden in verified modules", stmt);
          continue;
        }
        addError(
          "LAW028",
          `Statement kind \`${ts.SyntaxKind[stmt.kind]}\` is not allowed in verified modules`,
          stmt,
        );
      }

      if (kind === "loop" && !hasMeasure) {
        addError(
          "LAW038",
          "A loop needs a termination measure: add `decreases(...)` at the start of its body (after any `invariant`)",
          block,
        );
      }
      return terminated;
    };

    if (ts.isBlock(body)) {
      const returns = checkBlock(
        body,
        { scope: localNames, mutable: new Set(), inLoop: false },
        "function",
      );
      if (!returns) {
        addError("LAW029", "Verified function/law block must return on every code path", body);
      }
    } else {
      checkExpr(body, localNames);
    }
  };

  // Every named parameter is in scope, even one whose type was rejected, so a bad parameter
  // type does not also produce a misleading "not a local" error at each use.
  const paramScope = (params: ts.NodeArray<ts.ParameterDeclaration>): Set<string> =>
    new Set(params.flatMap((p) => (ts.isIdentifier(p.name) ? [p.name.text] : [])));

  const checkParams = (
    params: ts.NodeArray<ts.ParameterDeclaration>,
    /** Allow parameters without annotations when TypeScript infers them from context. */
    allowInferred = false,
  ): VerifiedParam[] => {
    const out: VerifiedParam[] = [];
    for (const p of params) {
      if (p.dotDotDotToken || p.questionToken || p.initializer) {
        addError("LAW005", "Optional, rest, and default parameters are forbidden", p);
        continue;
      }
      if (!ts.isIdentifier(p.name)) {
        addError("LAW005", "Destructured parameters are not supported; name parameters directly", p);
        continue;
      }
      if (p.name.text === "this") {
        addError("LAW005", "`this` parameters are not supported in verified modules", p);
        continue;
      }
      if (!p.type && !allowInferred) {
        addError("LAW005", `Parameter \`${p.name.text}\` must have an explicit type annotation`, p);
        continue;
      }
      const resolved = resolveVType(checker, checker.getTypeAtLocation(p), new Set(), true);
      if (!resolved.ok) {
        addError("LAW006", `Parameter \`${p.name.text}\`: ${resolved.reason}`, p);
        continue;
      }
      out.push({ name: p.name.text, type: resolved.type });
    }
    return out;
  };

  // Second pass: validate top-level declarations
  for (const stmt of sf.statements) {
    if (
      ts.isImportDeclaration(stmt) ||
      ts.isTypeAliasDeclaration(stmt) ||
      ts.isInterfaceDeclaration(stmt) ||
      (ts.isExpressionStatement(stmt) && ts.isStringLiteral(stmt.expression))
    ) {
      continue;
    }

    if (ts.isFunctionDeclaration(stmt)) {
      if (!stmt.name) {
        addError("LAW002", "Anonymous top-level functions are not allowed", stmt);
        continue;
      }
      if (stmt.modifiers?.some((m) => m.kind === ts.SyntaxKind.AsyncKeyword)) {
        addError("LAW003", "`async` functions are forbidden in verified modules", stmt);
        continue;
      }
      if (stmt.asteriskToken) {
        addError("LAW003", "Generator functions are forbidden in verified modules", stmt);
        continue;
      }
      if (stmt.typeParameters && stmt.typeParameters.length > 0) {
        addError("LAW003", "Generic type parameters are not supported in tslaw v0.1", stmt);
        continue;
      }
      if (!stmt.body) {
        addError("LAW003", "Ambient function declarations without a body are forbidden", stmt);
        continue;
      }
      if (!stmt.type) {
        addError("LAW004", `Function \`${stmt.name.text}\` must have an explicit return type`, stmt);
        continue;
      }
      const retResolved = resolveVType(checker, checker.getTypeFromTypeNode(stmt.type));
      if (!retResolved.ok) {
        addError("LAW004", `Function \`${stmt.name.text}\` return type: ${retResolved.reason}`, stmt.type);
        continue;
      }
      const params = checkParams(stmt.parameters);
      const calls = new Set<ts.FunctionDeclaration>();
      const spec = {
        requires: [] as ts.Expression[],
        decreases: [] as ts.Expression[],
        calls: new Set<ts.FunctionDeclaration>(),
        loopCalls: new Set<ts.FunctionDeclaration>(),
        prefixLength: 0,
        hasLoops: false,
      };
      checkBody(stmt.body, paramScope(stmt.parameters), calls, spec);
      parsed.push({
        requires: spec.requires,
        decreases: spec.decreases,
        prefixLength: spec.prefixLength,
        specCalls: spec.calls,
        loopCalls: spec.loopCalls,
        hasLoops: spec.hasLoops,
        name: stmt.name.text,
        decl: stmt,
        params,
        returnType: retResolved.type,
        body: stmt.body,
        location: getLocation(sf, stmt),
        calls,
      });
      continue;
    }

    if (
      ts.isExpressionStatement(stmt) &&
      ts.isCallExpression(stmt.expression) &&
      ts.isIdentifier(stmt.expression.expression) &&
      (() => {
        const callee = resolveCallee(checker, stmt.expression.expression);
        return callee.kind === "runtime" && callee.helper === "law";
      })()
    ) {
      const args = stmt.expression.arguments;
      if (args.length !== 2) {
        addError("LAW030", "`law(name, predicate)` requires exactly 2 arguments", stmt);
        continue;
      }
      const [nameArg, fnArg] = args;
      if (!nameArg || !ts.isStringLiteral(nameArg)) {
        addError("LAW030", "First argument to `law` must be a string literal", nameArg ?? stmt);
        continue;
      }
      if (!fnArg || (!ts.isArrowFunction(fnArg) && !ts.isFunctionExpression(fnArg))) {
        addError("LAW030", "Second argument to `law` must be an arrow or function expression", fnArg ?? stmt);
        continue;
      }
      if (fnArg.modifiers?.some((m) => m.kind === ts.SyntaxKind.AsyncKeyword)) {
        addError("LAW030", "`law` predicates cannot be async", fnArg);
        continue;
      }
      const params = checkParams(fnArg.parameters);
      const calls = new Set<ts.FunctionDeclaration>();
      checkBody(fnArg.body, paramScope(fnArg.parameters), calls);
      laws.push({
        name: nameArg.text,
        params,
        body: fnArg.body,
        location: getLocation(sf, stmt),
      });
      continue;
    }

    if (
      ts.isExpressionStatement(stmt) &&
      ts.isCallExpression(stmt.expression) &&
      ts.isIdentifier(stmt.expression.expression) &&
      (() => {
        const callee = resolveCallee(checker, stmt.expression.expression);
        return callee.kind === "runtime" && callee.helper === "ensures";
      })()
    ) {
      const [fnArg, postArg] = stmt.expression.arguments;
      if (stmt.expression.arguments.length !== 2 || !fnArg || !postArg) {
        addError("LAW036", "`ensures(fn, postcondition)` requires exactly 2 arguments", stmt);
        continue;
      }
      const target = ts.isIdentifier(fnArg) ? resolveCallee(checker, fnArg) : undefined;
      const targetSf = target?.kind === "function" ? target.decl.getSourceFile() : undefined;
      if (
        target?.kind !== "function" ||
        !target.decl.name ||
        !ts.isSourceFile(target.decl.parent) ||
        !(targetSf === sf || (targetSf !== undefined && analyzedDeps.has(targetSf.fileName)))
      ) {
        addError("LAW036", "First argument to `ensures` must name a verified function", fnArg);
        continue;
      }
      if (!ts.isArrowFunction(postArg) && !ts.isFunctionExpression(postArg)) {
        addError("LAW036", "Second argument to `ensures` must be an arrow or function expression", postArg);
        continue;
      }
      if (postArg.modifiers?.some((m) => m.kind === ts.SyntaxKind.AsyncKeyword)) {
        addError("LAW036", "`ensures` postconditions cannot be async", postArg);
        continue;
      }
      if (postArg.parameters.length !== target.decl.parameters.length + 1) {
        addError(
          "LAW036",
          `Postcondition must take the function's ${target.decl.parameters.length} parameter(s) followed by its result`,
          postArg,
        );
        continue;
      }
      const params = checkParams(postArg.parameters, true);
      const calls = new Set<ts.FunctionDeclaration>();
      checkBody(postArg.body, paramScope(postArg.parameters), calls);
      ensuresList.push({
        fn: target.decl,
        fnName: target.decl.name.text,
        params,
        body: postArg.body,
        location: getLocation(sf, stmt),
      });
      continue;
    }

    addError(
      "LAW031",
      `Top-level \`${ts.SyntaxKind[stmt.kind]}\` is not allowed in verified modules (use type/interface, pure function declarations, and \`law(...)\`)`,
      stmt,
    );
  }

  // Third pass: merge imported verified functions, group mutually recursive ones (Tarjan's
  // strongly connected components) and order the groups callees first.
  type Node = Omit<VerifiedFunction, "scc" | "recursive">;
  const nodes = new Map<ts.FunctionDeclaration, Node>();
  for (const fn of importedFunctions.values()) nodes.set(fn.decl, fn);
  for (const fn of parsed) nodes.set(fn.decl, fn);
  const specCallsOf = new Map(parsed.map((fn) => [fn.decl, fn.specCalls]));
  const loopCallsOf = new Map(parsed.map((fn) => [fn.decl, fn.loopCalls]));

  const ordered: VerifiedFunction[] = [];
  const index = new Map<ts.FunctionDeclaration, number>();
  const low = new Map<ts.FunctionDeclaration, number>();
  const onStack = new Set<ts.FunctionDeclaration>();
  const stack: ts.FunctionDeclaration[] = [];
  let nextIndex = 0;
  let nextScc = 0;

  const connect = (decl: ts.FunctionDeclaration): void => {
    const node = nodes.get(decl);
    if (!node) return;
    index.set(decl, nextIndex);
    low.set(decl, nextIndex);
    nextIndex++;
    stack.push(decl);
    onStack.add(decl);
    for (const callee of node.calls) {
      if (!nodes.has(callee)) continue;
      if (!index.has(callee)) {
        connect(callee);
        low.set(decl, Math.min(low.get(decl)!, low.get(callee)!));
      } else if (onStack.has(callee)) {
        low.set(decl, Math.min(low.get(decl)!, index.get(callee)!));
      }
    }
    if (low.get(decl) !== index.get(decl)) return;

    const members: Node[] = [];
    for (;;) {
      const top = stack.pop()!;
      onStack.delete(top);
      members.push(nodes.get(top)!);
      if (top === decl) break;
    }
    members.reverse();
    const group = new Set(members.map((m) => m.decl));
    const recursive = members.length > 1 || members[0]!.calls.has(members[0]!.decl);
    const scc = nextScc++;
    for (const m of members) ordered.push({ ...m, scc, recursive });
    if (!recursive) {
      // A measure is only checked for recursive functions, but JavaScript evaluates its
      // arguments on every call, so an unchecked one could hide a call that goes wrong.
      const only = members[0]!;
      if (only.decreases.length > 0 && only.decl.getSourceFile() === sf) {
        diagnostics.push({
          stage: "dialect",
          code: "LAW037",
          message: `\`${only.name}\` is not recursive, so it cannot have a \`decreases(...)\` measure; remove it`,
          location: only.location,
        });
      }
      return;
    }

    // Errors in imported modules were already reported with those modules' diagnostics.
    const names = members.map((m) => `\`${m.name}\``).join(", ");
    for (const m of members) {
      if (m.decl.getSourceFile() !== sf) continue;
      if (m.decreases.length === 0) {
        diagnostics.push({
          stage: "dialect",
          code: "LAW032",
          message:
            members.length > 1
              ? `\`${m.name}\` is recursive (through ${names}) and needs a termination measure: add \`decreases(...)\` after its \`requires\``
              : `\`${m.name}\` is recursive and needs a termination measure: add \`decreases(...)\` after its \`requires\``,
          location: m.location,
        });
        continue;
      }
      const longest = Math.max(...members.map((x) => x.decreases.length));
      if (m.decreases.length !== longest && members.every((x) => x.decreases.length > 0)) {
        diagnostics.push({
          stage: "dialect",
          code: "LAW037",
          message: `Mutually recursive functions (${names}) must give \`decreases\` the same number of measures`,
          location: m.location,
        });
      }
      for (const callee of loopCallsOf.get(m.decl) ?? []) {
        if (!group.has(callee)) continue;
        diagnostics.push({
          stage: "dialect",
          code: "LAW038",
          message: `A loop in the recursive function \`${m.name}\` may not call \`${callee.name?.text ?? "?"}\`, which is part of the same recursion; move the loop into its own function`,
          location: m.location,
        });
      }
      for (const callee of specCallsOf.get(m.decl) ?? []) {
        if (!group.has(callee)) continue;
        diagnostics.push({
          stage: "dialect",
          code: "LAW037",
          message: `\`requires\` and \`decreases\` of the recursive function \`${m.name}\` may not call \`${callee.name?.text ?? "?"}\`, which is part of the same recursion`,
          location: m.location,
        });
      }
    }
  };

  for (const decl of nodes.keys()) {
    if (!index.has(decl)) connect(decl);
  }
  functions.push(...ordered);
  ensuresList.unshift(...importedEnsures);

  const result: DialectAnalysis = {
    hasVerifiedDirective,
    diagnostics,
    functions,
    laws,
    ensures: ensuresList,
  };
  IN_PROGRESS.delete(stub);
  visited.set(sf.fileName, result);
  return result;
}
