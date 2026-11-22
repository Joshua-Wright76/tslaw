import ts from "typescript";
import type { Diagnostic, SourceLocation, VType } from "./types.js";

export interface VerifiedParam {
  readonly name: string;
  readonly type: VType;
}

export interface VerifiedFunction {
  readonly name: string;
  readonly params: ReadonlyArray<VerifiedParam>;
  readonly returnType: VType;
  readonly body: ts.Block | ts.Expression;
  readonly location: SourceLocation;
  readonly calls: ReadonlySet<string>;
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

const RUNTIME_HELPERS = new Set(["law", "implies"]);

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

export function vTypeKey(t: VType): string {
  if (t.kind === "bigint") return "Int";
  if (t.kind === "boolean") return "Bool";
  return `{${t.fields.map((f) => `${f.name}:${vTypeKey(f.type)}`).join(",")}}`;
}

export function vTypesEqual(a: VType, b: VType): boolean {
  return vTypeKey(a) === vTypeKey(b);
}

/**
 * Convert a resolved TypeScript type into a supported vscript VType.
 */
export function resolveVType(
  checker: ts.TypeChecker,
  type: ts.Type,
  seen = new Set<ts.Type>(),
): { ok: true; type: VType } | { ok: false; reason: string } {
  const flags = type.getFlags();

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
      reason: `union type \`${checker.typeToString(type)}\` is not supported in vscript v0.1`,
    };
  }

  if (flags & ts.TypeFlags.Object) {
    if (seen.has(type)) {
      return { ok: false, reason: "recursive object types are not supported" };
    }
    if (checker.isArrayType(type) || checker.isTupleType(type)) {
      return {
        ok: false,
        reason: `array/tuple type \`${checker.typeToString(type)}\` is not supported in vscript v0.1`,
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
      const isReadonly =
        (ts.isPropertySignature(decl) || ts.isPropertyDeclaration(decl))
          ? Boolean(decl.modifiers?.some((m) => m.kind === ts.SyntaxKind.ReadonlyKeyword))
          : ts.isPropertyAssignment(decl) || ts.isShorthandPropertyAssignment(decl);
      if (!isReadonly) {
        return {
          ok: false,
          reason: `mutable record field \`${prop.name}\` must be marked \`readonly\``,
        };
      }
      const propType = checker.getTypeOfSymbolAtLocation(prop, decl);
      const resolved = resolveVType(checker, propType, new Set(seen));
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
 * Analyze a TypeScript source file against the vscript sound pure subset.
 */
export function analyzeDialect(
  sf: ts.SourceFile,
  checker: ts.TypeChecker,
): DialectAnalysis {
  const hasVerifiedDirective = hasUseVerifiedDirective(sf);
  const diagnostics: Diagnostic[] = [];
  const functions: VerifiedFunction[] = [];
  const laws: VerifiedLaw[] = [];

  const addError = (code: string, message: string, node: ts.Node): void => {
    diagnostics.push({
      stage: "dialect",
      code,
      message,
      location: getLocation(sf, node),
    });
  };

  // First pass: collect declared verified function names so calls can be validated.
  const declaredFnNames = new Set<string>();
  for (const stmt of sf.statements) {
    if (ts.isFunctionDeclaration(stmt) && stmt.name) {
      declaredFnNames.add(stmt.name.text);
    }
  }

  // Track which runtime identifiers were imported from vscript runtime
  const importedRuntimeNames = new Set<string>();
  for (const stmt of sf.statements) {
    if (ts.isImportDeclaration(stmt) && stmt.importClause?.namedBindings) {
      if (ts.isNamedImports(stmt.importClause.namedBindings)) {
        for (const elem of stmt.importClause.namedBindings.elements) {
          const orig = elem.propertyName?.text ?? elem.name.text;
          if (RUNTIME_HELPERS.has(orig)) {
            importedRuntimeNames.add(elem.name.text);
          } else {
            addError(
              "VS001",
              `Verified modules may only import \`law\` and \`implies\` from vscript runtime (found \`${orig}\`)`,
              elem,
            );
          }
        }
      } else {
        addError("VS001", "Namespace imports are not allowed in verified modules", stmt);
      }
    }
  }

  const checkBody = (
    body: ts.Block | ts.Expression,
    localNames: Set<string>,
    callsOut: Set<string>,
  ): void => {
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
          "VS010",
          `Numeric literal \`${expr.text}\` is a float; use a bigint literal like \`${expr.text}n\``,
          expr,
        );
        return;
      }
      if (ts.isIdentifier(expr)) {
        if (!scope.has(expr.text)) {
          addError(
            "VS011",
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
          addError("VS012", "Mutating unary operators (`++`, `--`, `~`) are forbidden", expr);
          return;
        }
        checkExpr(expr.operand, scope);
        return;
      }
      if (ts.isPostfixUnaryExpression(expr)) {
        addError("VS012", "Mutating postfix operators (`++`, `--`) are forbidden", expr);
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
            "VS013",
            "Division `/` and modulo `%` are not yet supported in vscript v0.1 (JS truncating semantics differ from SMT Euclidean div)",
            expr.operatorToken,
          );
          return;
        }
        if (!allowed.has(op)) {
          addError(
            "VS014",
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
              "VS015",
              "Direct `===`/`!==` on records is forbidden (JS compares object identity, not structure); compare fields explicitly",
              expr,
            );
          }
        }
        checkExpr(expr.left, scope);
        checkExpr(expr.right, scope);
        return;
      }
      if (ts.isConditionalExpression(expr)) {
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
            "VS016",
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
              addError("VS017", "Computed or non-identifier record keys are forbidden", prop.name);
              continue;
            }
            checkExpr(prop.initializer, scope);
          } else if (ts.isShorthandPropertyAssignment(prop)) {
            checkExpr(prop.name, scope);
          } else {
            addError(
              "VS017",
              "Object spread, getters, setters, and methods are forbidden in verified records",
              prop,
            );
          }
        }
        return;
      }
      if (ts.isCallExpression(expr)) {
        if (!ts.isIdentifier(expr.expression)) {
          addError("VS018", "Only direct calls to verified functions or `implies` are allowed", expr);
          return;
        }
        const fnName = expr.expression.text;
        if (fnName === "implies" && importedRuntimeNames.has(fnName)) {
          if (expr.arguments.length !== 2) {
            addError("VS018", "`implies` requires exactly 2 arguments", expr);
          }
          for (const arg of expr.arguments) checkExpr(arg, scope);
          return;
        }
        if (!declaredFnNames.has(fnName)) {
          addError(
            "VS018",
            `Call to unverified function \`${fnName}\` is forbidden inside verified modules`,
            expr,
          );
          return;
        }
        callsOut.add(fnName);
        for (const arg of expr.arguments) checkExpr(arg, scope);
        return;
      }
      if (
        ts.isAsExpression(expr) ||
        ts.isTypeAssertionExpression(expr) ||
        ts.isNonNullExpression(expr)
      ) {
        addError("VS019", "Type assertions (`as`, `!`) are forbidden in verified modules", expr);
        return;
      }
      addError(
        "VS020",
        `Expression kind \`${ts.SyntaxKind[expr.kind]}\` is not allowed in verified modules`,
        expr,
      );
    };

    const checkBlock = (block: ts.Block, outerScope: Set<string>): boolean => {
      const scope = new Set(outerScope);
      let terminated = false;

      for (const stmt of block.statements) {
        if (terminated) {
          addError("VS021", "Unreachable statement after `return`", stmt);
          break;
        }
        if (ts.isVariableStatement(stmt)) {
          const isConst = (stmt.declarationList.flags & ts.NodeFlags.Const) !== 0;
          if (!isConst) {
            addError("VS022", "Mutable bindings (`let`/`var`) are forbidden; use `const`", stmt);
            continue;
          }
          for (const decl of stmt.declarationList.declarations) {
            if (!decl.initializer) {
              addError("VS022", "`const` declarations must have an initializer", decl);
              continue;
            }
            checkExpr(decl.initializer, scope);
            const initType = resolveVType(checker, checker.getTypeAtLocation(decl.initializer));
            if (!initType.ok) {
              addError("VS023", `Invalid local type: ${initType.reason}`, decl);
            }
            if (ts.isIdentifier(decl.name)) {
              scope.add(decl.name.text);
            } else if (ts.isObjectBindingPattern(decl.name)) {
              for (const el of decl.name.elements) {
                if (el.dotDotDotToken || el.initializer || !ts.isIdentifier(el.name)) {
                  addError("VS022", "Rest/default/nested destructuring is not supported", el);
                  continue;
                }
                scope.add(el.name.text);
              }
            } else {
              addError("VS022", "Unsupported binding pattern", decl.name);
            }
          }
          continue;
        }
        if (ts.isReturnStatement(stmt)) {
          if (!stmt.expression) {
            addError("VS024", "Bare `return;` is forbidden; verified functions must return a value", stmt);
          } else {
            checkExpr(stmt.expression, scope);
          }
          terminated = true;
          continue;
        }
        if (ts.isIfStatement(stmt)) {
          checkExpr(stmt.expression, scope);
          const checkBranch = (branch: ts.Statement): boolean => {
            if (ts.isBlock(branch)) return checkBlock(branch, scope);
            if (ts.isReturnStatement(branch)) {
              if (!branch.expression) {
                addError("VS024", "Bare `return;` is forbidden", branch);
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
              "VS025",
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
                "VS025",
                "Both branches of an `if`/`else` must return in verified modules",
                stmt,
              );
            }
          } else if (!thenReturns) {
            addError(
              "VS025",
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
          addError("VS026", "Loops are forbidden in verified modules (unbounded termination)", stmt);
          continue;
        }
        if (ts.isThrowStatement(stmt) || ts.isTryStatement(stmt)) {
          addError("VS027", "Exceptions (`throw`/`try`) are forbidden in verified modules", stmt);
          continue;
        }
        addError(
          "VS028",
          `Statement kind \`${ts.SyntaxKind[stmt.kind]}\` is not allowed in verified modules`,
          stmt,
        );
      }

      return terminated;
    };

    if (ts.isBlock(body)) {
      const returns = checkBlock(body, localNames);
      if (!returns) {
        addError("VS029", "Verified function/law block must return on every code path", body);
      }
    } else {
      checkExpr(body, localNames);
    }
  };

  const checkParams = (
    params: ts.NodeArray<ts.ParameterDeclaration>,
  ): VerifiedParam[] => {
    const out: VerifiedParam[] = [];
    for (const p of params) {
      if (p.dotDotDotToken || p.questionToken || p.initializer) {
        addError("VS005", "Optional, rest, and default parameters are forbidden", p);
        continue;
      }
      if (!ts.isIdentifier(p.name)) {
        addError("VS005", "Destructured parameters are not supported; name parameters directly", p);
        continue;
      }
      if (!p.type) {
        addError("VS005", `Parameter \`${p.name.text}\` must have an explicit type annotation`, p);
        continue;
      }
      const resolved = resolveVType(checker, checker.getTypeAtLocation(p));
      if (!resolved.ok) {
        addError("VS006", `Parameter \`${p.name.text}\`: ${resolved.reason}`, p);
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
        addError("VS002", "Anonymous top-level functions are not allowed", stmt);
        continue;
      }
      if (stmt.modifiers?.some((m) => m.kind === ts.SyntaxKind.AsyncKeyword)) {
        addError("VS003", "`async` functions are forbidden in verified modules", stmt);
        continue;
      }
      if (stmt.asteriskToken) {
        addError("VS003", "Generator functions are forbidden in verified modules", stmt);
        continue;
      }
      if (stmt.typeParameters && stmt.typeParameters.length > 0) {
        addError("VS003", "Generic type parameters are not supported in vscript v0.1", stmt);
        continue;
      }
      if (!stmt.body) {
        addError("VS003", "Ambient function declarations without a body are forbidden", stmt);
        continue;
      }
      if (!stmt.type) {
        addError("VS004", `Function \`${stmt.name.text}\` must have an explicit return type`, stmt);
        continue;
      }
      const retResolved = resolveVType(checker, checker.getTypeFromTypeNode(stmt.type));
      if (!retResolved.ok) {
        addError("VS004", `Function \`${stmt.name.text}\` return type: ${retResolved.reason}`, stmt.type);
        continue;
      }
      const params = checkParams(stmt.parameters);
      const calls = new Set<string>();
      checkBody(stmt.body, new Set(params.map((p) => p.name)), calls);
      functions.push({
        name: stmt.name.text,
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
      stmt.expression.expression.text === "law" &&
      importedRuntimeNames.has("law")
    ) {
      const args = stmt.expression.arguments;
      if (args.length !== 2) {
        addError("VS030", "`law(name, predicate)` requires exactly 2 arguments", stmt);
        continue;
      }
      const [nameArg, fnArg] = args;
      if (!nameArg || !ts.isStringLiteral(nameArg)) {
        addError("VS030", "First argument to `law` must be a string literal", nameArg ?? stmt);
        continue;
      }
      if (!fnArg || (!ts.isArrowFunction(fnArg) && !ts.isFunctionExpression(fnArg))) {
        addError("VS030", "Second argument to `law` must be an arrow or function expression", fnArg ?? stmt);
        continue;
      }
      if (fnArg.modifiers?.some((m) => m.kind === ts.SyntaxKind.AsyncKeyword)) {
        addError("VS030", "`law` predicates cannot be async", fnArg);
        continue;
      }
      const params = checkParams(fnArg.parameters);
      const calls = new Set<string>();
      checkBody(fnArg.body, new Set(params.map((p) => p.name)), calls);
      laws.push({
        name: nameArg.text,
        params,
        body: fnArg.body,
        location: getLocation(sf, stmt),
      });
      continue;
    }

    addError(
      "VS031",
      `Top-level \`${ts.SyntaxKind[stmt.kind]}\` is not allowed in verified modules (use type/interface, pure function declarations, and \`law(...)\`)`,
      stmt,
    );
  }

  // Third pass: check call graph for recursion / cycles (guarantees termination).
  const fnMap = new Map(functions.map((f) => [f.name, f]));
  const color = new Map<string, 0 | 1 | 2>(); // 0=unvisited, 1=visiting, 2=done
  const ordered: VerifiedFunction[] = [];

  const dfs = (name: string, stack: string[]): void => {
    color.set(name, 1);
    const fn = fnMap.get(name);
    if (!fn) return;
    for (const callee of fn.calls) {
      const c = color.get(callee) ?? 0;
      if (c === 1) {
        const cycle = [...stack.slice(stack.indexOf(callee)), callee].join(" -> ");
        diagnostics.push({
          stage: "dialect",
          code: "VS032",
          message: `Recursion is not supported in vscript v0.1 (cycle: ${cycle})`,
          location: fn.location,
        });
      } else if (c === 0) {
        dfs(callee, [...stack, callee]);
      }
    }
    color.set(name, 2);
    ordered.push(fn);
  };

  for (const fn of functions) {
    if ((color.get(fn.name) ?? 0) === 0) {
      dfs(fn.name, [fn.name]);
    }
  }

  return {
    hasVerifiedDirective,
    diagnostics,
    functions: ordered,
    laws,
  };
}
