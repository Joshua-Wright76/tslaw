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

const runtimeFileCache = new Map<string, boolean>();

/**
 * True if `fileName` is the tslaw runtime module: either this installation's own copy, or
 * the runtime of an installed package with the same name (e.g. a project-local install checked
 * by a globally installed CLI).
 */
export function isTslawRuntimeFile(fileName: string): boolean {
  const cached = runtimeFileCache.get(fileName);
  if (cached !== undefined) return cached;

  const real = safeRealpath(fileName);
  let result = BUNDLED_RUNTIME_FILES.has(real);
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
          result = name === OWN_PACKAGE_NAME && RUNTIME_REL_PATHS.includes(rel);
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
  runtimeFileCache.set(fileName, result);
  return result;
}

export type CalleeRef =
  | { readonly kind: "runtime"; readonly helper: "law" | "implies" }
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
    (name === "law" || name === "implies") &&
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
  return `{${t.fields.map((f) => `${f.name}:${vTypeKey(f.type)}`).join(",")}}`;
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
    // Boolean is represented as union of true | false in TS
    if (
      type.types.length === 2 &&
      type.types.every((t) => (t.getFlags() & ts.TypeFlags.BooleanLiteral) !== 0)
    ) {
      return { ok: true, type: { kind: "boolean" } };
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
    if (checker.isArrayType(type) || checker.isTupleType(type)) {
      return {
        ok: false,
        reason: `array/tuple type \`${checker.typeToString(type)}\` is not supported in tslaw v0.1`,
      };
    }
    if (type.getCallSignatures().length > 0) {
      return { ok: false, reason: "higher-order function values are not supported" };
    }
    const props = type.getProperties();
    if (props.length === 0) {
      return { ok: false, reason: "empty object types are not supported" };
    }
    seen.add(type);
    const fields: Array<{ name: string; type: VType }> = [];
    for (const prop of props) {
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
    fields.sort((a, b) => a.name.localeCompare(b.name));
    return { ok: true, type: { kind: "record", fields } };
  }

  return {
    ok: false,
    reason: `unsupported type \`${checker.typeToString(type)}\` (supported: bigint, boolean, readonly records)`,
  };
}

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
  const functions: VerifiedFunction[] = [];
  const laws: VerifiedLaw[] = [];

  // Pre-seed cache to guard against cyclic imports.
  const stub: DialectAnalysis = {
    hasVerifiedDirective,
    diagnostics,
    functions,
    laws,
  };
  visited.set(sf.fileName, stub);

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
  const analyzedDeps = new Set<string>();
  for (const stmt of sf.statements) {
    if (!ts.isImportDeclaration(stmt) || !stmt.importClause) continue;
    if (stmt.importClause.isTypeOnly) continue;
    if (!stmt.importClause.namedBindings) {
      addError("LAW001", "Default imports are not allowed in verified modules", stmt);
      continue;
    }
    if (!ts.isNamedImports(stmt.importClause.namedBindings)) {
      addError("LAW001", "Namespace imports are not allowed in verified modules", stmt);
      continue;
    }
    for (const elem of stmt.importClause.namedBindings.elements) {
      if (elem.isTypeOnly) continue;
      const orig = elem.propertyName?.text ?? elem.name.text;
      const callee = resolveCallee(checker, elem.name);
      if (callee.kind === "runtime") {
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
        if (!analyzedDeps.has(depSf.fileName)) {
          analyzedDeps.add(depSf.fileName);
          const depAnalysis = analyzeDialect(depSf, checker, visited);
          diagnostics.push(...depAnalysis.diagnostics);
          for (const depFn of depAnalysis.functions) {
            importedFunctions.set(depFn.decl, depFn);
          }
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
  ): void => {
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
          expr.operator !== ts.SyntaxKind.ExclamationToken &&
          expr.operator !== ts.SyntaxKind.PlusToken
        ) {
          addError("LAW012", "Mutating unary operators (`++`, `--`, `~`) are forbidden", expr);
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
          if (
            (lt.ok && lt.type.kind === "record") ||
            (rt.ok && rt.type.kind === "record")
          ) {
            addError(
              "LAW015",
              "Direct `===`/`!==` on records is forbidden (JS compares object identity, not structure); compare fields explicitly",
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
            "Property access is only allowed on verified `readonly` records",
            expr,
          );
        }
        return;
      }
      if (ts.isObjectLiteralExpression(expr)) {
        for (const prop of expr.properties) {
          if (ts.isPropertyAssignment(prop)) {
            if (!ts.isIdentifier(prop.name)) {
              addError("LAW017", "Computed or non-identifier record keys are forbidden", prop.name);
              continue;
            }
            checkExpr(prop.initializer, scope);
          } else if (ts.isShorthandPropertyAssignment(prop)) {
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

    const checkBlock = (block: ts.Block, outerScope: Set<string>): boolean => {
      const scope = new Set(outerScope);
      let terminated = false;

      for (const stmt of block.statements) {
        if (terminated) {
          addError("LAW021", "Unreachable statement after `return`", stmt);
          break;
        }
        if (ts.isVariableStatement(stmt)) {
          const isConst = (stmt.declarationList.flags & ts.NodeFlags.Const) !== 0;
          if (!isConst) {
            addError("LAW022", "Mutable bindings (`let`/`var`) are forbidden; use `const`", stmt);
            continue;
          }
          for (const decl of stmt.declarationList.declarations) {
            if (!decl.initializer) {
              addError("LAW022", "`const` declarations must have an initializer", decl);
              continue;
            }
            checkExpr(decl.initializer, scope);
            const initType = resolveVType(checker, checker.getTypeAtLocation(decl.initializer));
            if (!initType.ok) {
              addError("LAW023", `Invalid local type: ${initType.reason}`, decl);
            }
            if (ts.isIdentifier(decl.name)) {
              scope.add(decl.name.text);
            } else if (ts.isObjectBindingPattern(decl.name)) {
              for (const el of decl.name.elements) {
                if (el.dotDotDotToken || el.initializer || !ts.isIdentifier(el.name)) {
                  addError("LAW022", "Rest/default/nested destructuring is not supported", el);
                  continue;
                }
                scope.add(el.name.text);
              }
            } else {
              addError("LAW022", "Unsupported binding pattern", decl.name);
            }
          }
          continue;
        }
        if (ts.isReturnStatement(stmt)) {
          if (!stmt.expression) {
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
            if (ts.isBlock(branch)) return checkBlock(branch, scope);
            if (ts.isReturnStatement(branch)) {
              if (!branch.expression) {
                addError("LAW024", "Bare `return;` is forbidden", branch);
              } else {
                checkExpr(branch.expression, scope);
              }
              return true;
            }
            if (ts.isIfStatement(branch)) {
              const synthetic = ts.factory.createBlock([branch]);
              return checkBlock(synthetic, scope);
            }
            addError(
              "LAW025",
              "Only blocks, `return`, or `else if` are allowed as `if` branches",
              branch,
            );
            return false;
          };
          const thenReturns = checkBranch(stmt.thenStatement);
          if (stmt.elseStatement) {
            const elseReturns = checkBranch(stmt.elseStatement);
            if (thenReturns && elseReturns) {
              terminated = true;
            } else if (!thenReturns || !elseReturns) {
              addError(
                "LAW025",
                "Both branches of an `if`/`else` must return in verified modules",
                stmt,
              );
            }
          } else if (!thenReturns) {
            addError(
              "LAW025",
              "An `if` without `else` must end with `return` (guard clause)",
              stmt,
            );
          }
          continue;
        }
        if (
          ts.isWhileStatement(stmt) ||
          ts.isDoStatement(stmt) ||
          ts.isForStatement(stmt) ||
          ts.isForInStatement(stmt) ||
          ts.isForOfStatement(stmt)
        ) {
          addError("LAW026", "Loops are forbidden in verified modules (unbounded termination)", stmt);
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

      return terminated;
    };

    if (ts.isBlock(body)) {
      const returns = checkBlock(body, localNames);
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
      if (!p.type) {
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
      checkBody(stmt.body, paramScope(stmt.parameters), calls);
      functions.push({
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

    addError(
      "LAW031",
      `Top-level \`${ts.SyntaxKind[stmt.kind]}\` is not allowed in verified modules (use type/interface, pure function declarations, and \`law(...)\`)`,
      stmt,
    );
  }

  // Third pass: merge imported verified functions and topologically sort call graph.
  const allFunctions: VerifiedFunction[] = [...importedFunctions.values(), ...functions];
  const fnMap = new Map(allFunctions.map((f) => [f.decl, f]));
  const color = new Map<ts.FunctionDeclaration, 0 | 1 | 2>(); // 0=unvisited, 1=visiting, 2=done
  const ordered: VerifiedFunction[] = [];

  const fnName = (d: ts.FunctionDeclaration): string => d.name?.text ?? "<anonymous>";
  const dfs = (decl: ts.FunctionDeclaration, stack: ts.FunctionDeclaration[]): void => {
    color.set(decl, 1);
    const fn = fnMap.get(decl);
    if (!fn) return;
    for (const callee of fn.calls) {
      const c = color.get(callee) ?? 0;
      if (c === 1) {
        const cycle = [...stack.slice(stack.indexOf(callee)), callee].map(fnName).join(" -> ");
        diagnostics.push({
          stage: "dialect",
          code: "LAW032",
          message: `Recursion is not supported in tslaw v0.1 (cycle: ${cycle})`,
          location: fn.location,
        });
      } else if (c === 0) {
        dfs(callee, [...stack, callee]);
      }
    }
    color.set(decl, 2);
    ordered.push(fn);
  };

  for (const fn of allFunctions) {
    if ((color.get(fn.decl) ?? 0) === 0) {
      dfs(fn.decl, [fn.decl]);
    }
  }

  const result: DialectAnalysis = {
    hasVerifiedDirective,
    diagnostics,
    functions: ordered,
    laws,
  };
  visited.set(sf.fileName, result);
  return result;
}
