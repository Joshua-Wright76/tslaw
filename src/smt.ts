import ts from "typescript";
import {
  resolveCallee,
  resolveVType,
  vTypeKey,
  type VerifiedFunction,
  type VerifiedLaw,
} from "./dialect.js";
import type { VType } from "./types.js";

export interface RecordDef {
  readonly smtName: string;
  readonly ctorName: string;
  readonly key: string;
  readonly fields: ReadonlyArray<{
    readonly name: string;
    readonly smtAccessor: string;
    readonly type: VType;
  }>;
}

export interface LoweredLaw {
  readonly law: VerifiedLaw;
  readonly smtScript: string;
  readonly paramSmtNames: ReadonlyArray<{
    readonly tsName: string;
    readonly smtName: string;
    readonly type: VType;
  }>;
  readonly recordsByCtor: ReadonlyMap<string, RecordDef>;
}

/**
 * Collect and register all structural record types used in a module so SMT-LIB2
 * `declare-datatypes` definitions are emitted in dependency order.
 */
class RecordRegistry {
  private byKey = new Map<string, RecordDef>();
  private ordered: RecordDef[] = [];

  register(type: VType): string {
    if (type.kind === "bigint") return "Int";
    if (type.kind === "boolean") return "Bool";
    const key = vTypeKey(type);
    const existing = this.byKey.get(key);
    if (existing) return existing.smtName;

    // Register nested field types first so datatype declarations are topologically ordered.
    for (const f of type.fields) {
      this.register(f.type);
    }

    const idx = this.ordered.length;
    const smtName = `Rec_${idx}`;
    const ctorName = `mk_Rec_${idx}`;
    const def: RecordDef = {
      smtName,
      ctorName,
      key,
      fields: type.fields.map((f, i) => ({
        name: f.name,
        smtAccessor: smtIdent(`${smtName}_${i}`, f.name),
        type: f.type,
      })),
    };
    this.byKey.set(key, def);
    this.ordered.push(def);
    return smtName;
  }

  getRecord(type: VType): RecordDef {
    if (type.kind !== "record") {
      throw new Error(`Expected record type, got ${type.kind}`);
    }
    this.register(type);
    const def = this.byKey.get(vTypeKey(type));
    if (!def) throw new Error(`Missing record def for ${vTypeKey(type)}`);
    return def;
  }

  emitDeclarations(): string[] {
    return this.ordered.map((rec) => {
      const fieldsSmt = rec.fields
        .map((f) => `(${f.smtAccessor} ${this.register(f.type)})`)
        .join(" ");
      return `(declare-datatypes ((${rec.smtName} 0)) (((${rec.ctorName} ${fieldsSmt}))))`;
    });
  }

  byCtorMap(): Map<string, RecordDef> {
    return new Map(this.ordered.map((r) => [r.ctorName, r]));
  }
}

/**
 * Build an SMT-LIB2 symbol from a unique `prefix` plus a readable hint derived from a TS name.
 *
 * Uniqueness MUST come from the prefix (which callers build from a per-scope index), never from
 * the sanitized name: sanitizing is lossy (`a$b` and `a_b` both become `a_b`), and Z3 silently
 * accepts duplicate `define-fun` parameter names, binding the last one — which once let false
 * laws be PROVED. The prefix also avoids collisions with SMT-LIB2 reserved words.
 */
function smtIdent(prefix: string, name: string): string {
  const safe = name.replace(/[^A-Za-z0-9_]/g, "_");
  return `${prefix}_${safe}`;
}

/** Normalize a TS bigint literal (`1_000n`, `0x10n`, `0b101n`, `0o7n`) to a decimal SMT numeral. */
function bigintLiteralToSmt(text: string): string {
  const value = BigInt(text.replace(/_/g, "").replace(/n$/, ""));
  return value < 0n ? `(- ${(-value).toString()})` : value.toString();
}

export function lowerModuleLaws(
  checker: ts.TypeChecker,
  functions: ReadonlyArray<VerifiedFunction>,
  laws: ReadonlyArray<VerifiedLaw>,
): LoweredLaw[] {
  const registry = new RecordRegistry();

  // Pre-register all function & law parameter/return types
  for (const fn of functions) {
    for (const p of fn.params) registry.register(p.type);
    registry.register(fn.returnType);
  }
  for (const l of laws) {
    for (const p of l.params) registry.register(p.type);
  }

  // Assign every verified function a unique SMT name up front (functions arrive in
  // dependency order, but a lookup table keeps the call lowering order-independent).
  const fnSmtNames = new Map<ts.FunctionDeclaration, string>();
  functions.forEach((fn, i) => fnSmtNames.set(fn.decl, smtIdent(`fn_${i}`, fn.name)));

  let freshId = 0;
  const nextVar = (hint: string): string => `v_${freshId++}_${hint.replace(/[^A-Za-z0-9_]/g, "")}`;

  const resolveExprVType = (node: ts.Node): VType => {
    const res = resolveVType(checker, checker.getTypeAtLocation(node));
    if (!res.ok) {
      throw new Error(`SMT lowering encountered unsupported type: ${res.reason}`);
    }
    registry.register(res.type);
    return res.type;
  };

  const fnByDecl = new Map(functions.map((fn) => [fn.decl, fn]));

  /**
   * Convert an SMT value of record type `from` into record type `to` by dropping extra fields.
   * TypeScript lets a record with extra fields flow anywhere a narrower record is expected
   * (structural subtyping), but each record shape is a distinct SMT datatype.
   */
  const project = (smt: string, from: VType, to: VType): string => {
    if (vTypeKey(from) === vTypeKey(to)) return smt;
    if (from.kind !== "record" || to.kind !== "record") {
      throw new Error(`Cannot convert ${vTypeKey(from)} to ${vTypeKey(to)}`);
    }
    const fromDef = registry.getRecord(from);
    const toDef = registry.getRecord(to);
    const tmp = nextVar("proj");
    const args = toDef.fields.map((tf) => {
      const ff = fromDef.fields.find((f) => f.name === tf.name);
      if (!ff) throw new Error(`Field \`${tf.name}\` missing when converting record types`);
      return project(`(${ff.smtAccessor} ${tmp})`, ff.type, tf.type);
    });
    return `(let ((${tmp} ${smt})) (${toDef.ctorName} ${args.join(" ")}))`;
  };

  /**
   * Lower an expression. When `expected` is given (call arguments, returns, annotated consts),
   * the result is converted to that type if the expression's own type is a wider record.
   */
  const lowerExpr = (expr: ts.Expression, env: Map<string, string>, expected?: VType): string => {
    if (ts.isParenthesizedExpression(expr)) {
      return lowerExpr(expr.expression, env, expected);
    }
    if (ts.isConditionalExpression(expr)) {
      const target = expected ?? resolveExprVType(expr);
      const c = lowerExpr(expr.condition, env);
      const t = lowerExpr(expr.whenTrue, env, target);
      const f = lowerExpr(expr.whenFalse, env, target);
      return `(ite ${c} ${t} ${f})`;
    }
    const smt = lowerExprRaw(expr, env);
    if (!expected || expected.kind !== "record") return smt;
    return project(smt, resolveExprVType(expr), expected);
  };

  const lowerExprRaw = (expr: ts.Expression, env: Map<string, string>): string => {
    if (ts.isBigIntLiteral(expr)) {
      return bigintLiteralToSmt(expr.text);
    }
    if (expr.kind === ts.SyntaxKind.TrueKeyword) return "true";
    if (expr.kind === ts.SyntaxKind.FalseKeyword) return "false";
    if (ts.isIdentifier(expr)) {
      const bound = env.get(expr.text);
      if (!bound) {
        throw new Error(`Unbound identifier \`${expr.text}\` during SMT lowering`);
      }
      return bound;
    }
    if (ts.isPrefixUnaryExpression(expr)) {
      const operand = lowerExpr(expr.operand, env);
      if (expr.operator === ts.SyntaxKind.MinusToken) return `(- ${operand})`;
      if (expr.operator === ts.SyntaxKind.ExclamationToken) return `(not ${operand})`;
      if (expr.operator === ts.SyntaxKind.PlusToken) return operand;
    }
    if (ts.isBinaryExpression(expr)) {
      const left = lowerExpr(expr.left, env);
      const right = lowerExpr(expr.right, env);
      switch (expr.operatorToken.kind) {
        case ts.SyntaxKind.PlusToken:
          return `(+ ${left} ${right})`;
        case ts.SyntaxKind.MinusToken:
          return `(- ${left} ${right})`;
        case ts.SyntaxKind.AsteriskToken:
          return `(* ${left} ${right})`;
        case ts.SyntaxKind.LessThanToken:
          return `(< ${left} ${right})`;
        case ts.SyntaxKind.LessThanEqualsToken:
          return `(<= ${left} ${right})`;
        case ts.SyntaxKind.GreaterThanToken:
          return `(> ${left} ${right})`;
        case ts.SyntaxKind.GreaterThanEqualsToken:
          return `(>= ${left} ${right})`;
        case ts.SyntaxKind.EqualsEqualsEqualsToken:
          return `(= ${left} ${right})`;
        case ts.SyntaxKind.ExclamationEqualsEqualsToken:
          return `(not (= ${left} ${right}))`;
        case ts.SyntaxKind.AmpersandAmpersandToken:
          return `(and ${left} ${right})`;
        case ts.SyntaxKind.BarBarToken:
          return `(or ${left} ${right})`;
      }
    }
    if (ts.isPropertyAccessExpression(expr)) {
      const recType = resolveExprVType(expr.expression);
      const recDef = registry.getRecord(recType);
      const field = recDef.fields.find((f) => f.name === expr.name.text);
      if (!field) {
        throw new Error(`Field \`${expr.name.text}\` not found on record ${recDef.smtName}`);
      }
      return `(${field.smtAccessor} ${lowerExpr(expr.expression, env)})`;
    }
    if (ts.isObjectLiteralExpression(expr)) {
      const recType = resolveExprVType(expr);
      const recDef = registry.getRecord(recType);
      const propValues = new Map<string, string>();
      for (const prop of expr.properties) {
        if (ts.isPropertyAssignment(prop) && ts.isIdentifier(prop.name)) {
          propValues.set(prop.name.text, lowerExpr(prop.initializer, env));
        } else if (ts.isShorthandPropertyAssignment(prop)) {
          propValues.set(prop.name.text, lowerExpr(prop.name, env));
        }
      }
      const orderedArgs = recDef.fields.map((f) => {
        const val = propValues.get(f.name);
        if (val === undefined) {
          throw new Error(`Missing field \`${f.name}\` in object literal`);
        }
        return val;
      });
      return `(${recDef.ctorName} ${orderedArgs.join(" ")})`;
    }
    if (ts.isCallExpression(expr) && ts.isIdentifier(expr.expression)) {
      const fnName = expr.expression.text;
      // Resolve the callee by symbol, never by name: a user function named `implies`, or two
      // modules each defining a private `helper`, must not be confused with one another.
      const callee = resolveCallee(checker, expr.expression);
      if (callee.kind === "runtime" && callee.helper === "implies") {
        const args = expr.arguments.map((a) => lowerExpr(a, env));
        if (args.length !== 2) throw new Error("`implies` requires exactly 2 arguments");
        return `(=> ${args[0]} ${args[1]})`;
      }
      if (callee.kind !== "function") {
        throw new Error(`Cannot resolve callee \`${fnName}\` during SMT lowering`);
      }
      const target = fnSmtNames.get(callee.decl);
      const calleeFn = fnByDecl.get(callee.decl);
      if (!target || !calleeFn) {
        throw new Error(`Callee \`${fnName}\` is not a known verified function`);
      }
      if (expr.arguments.length !== calleeFn.params.length) {
        throw new Error(`Wrong number of arguments in call to \`${fnName}\``);
      }
      const args = expr.arguments.map((a, i) => lowerExpr(a, env, calleeFn.params[i]!.type));
      return args.length > 0 ? `(${target} ${args.join(" ")})` : target;
    }

    throw new Error(`Unsupported expression in SMT lowering: ${ts.SyntaxKind[expr.kind]}`);
  };

  const lowerStatements = (
    stmts: ReadonlyArray<ts.Statement>,
    idx: number,
    env: Map<string, string>,
    ret: VType,
  ): string => {
    const stmt = stmts[idx];
    if (!stmt) {
      throw new Error("Control reached end of block without return during SMT lowering");
    }

    if (ts.isReturnStatement(stmt)) {
      if (!stmt.expression) throw new Error("Bare return in SMT lowering");
      return lowerExpr(stmt.expression, env, ret);
    }

    if (ts.isVariableStatement(stmt)) {
      const decls = stmt.declarationList.declarations;
      const lowerDeclAt = (dIdx: number, curEnv: Map<string, string>): string => {
        const decl = decls[dIdx];
        if (!decl) return lowerStatements(stmts, idx + 1, curEnv, ret);
        if (!decl.initializer) throw new Error("Missing initializer");

        if (ts.isIdentifier(decl.name)) {
          // An annotated const (`const a: Narrow = wide`) has the declared type, not the initializer's.
          const initSmt = lowerExpr(decl.initializer, curEnv, resolveExprVType(decl.name));
          const v = nextVar(decl.name.text);
          const nextEnv = new Map(curEnv);
          nextEnv.set(decl.name.text, v);
          return `(let ((${v} ${initSmt})) ${lowerDeclAt(dIdx + 1, nextEnv)})`;
        }
        const initSmt = lowerExpr(decl.initializer, curEnv);
        if (ts.isObjectBindingPattern(decl.name)) {
          const recType = resolveExprVType(decl.initializer);
          const recDef = registry.getRecord(recType);
          const tmp = nextVar("rec");
          const nextEnv = new Map(curEnv);
          for (const el of decl.name.elements) {
            if (!ts.isIdentifier(el.name)) continue;
            const propName =
              el.propertyName && ts.isIdentifier(el.propertyName)
                ? el.propertyName.text
                : el.name.text;
            const field = recDef.fields.find((f) => f.name === propName);
            if (!field) throw new Error(`Missing destructured field ${propName}`);
            nextEnv.set(el.name.text, `(${field.smtAccessor} ${tmp})`);
          }
          return `(let ((${tmp} ${initSmt})) ${lowerDeclAt(dIdx + 1, nextEnv)})`;
        }
        throw new Error("Unsupported declaration binding");
      };
      return lowerDeclAt(0, env);
    }

    if (ts.isIfStatement(stmt)) {
      const condSmt = lowerExpr(stmt.expression, env);
      const lowerBranch = (branch: ts.Statement): string => {
        if (ts.isBlock(branch)) {
          return lowerStatements(branch.statements, 0, env, ret);
        }
        if (ts.isReturnStatement(branch) || ts.isIfStatement(branch)) {
          return lowerStatements([branch], 0, env, ret);
        }
        throw new Error(`Unsupported if branch: ${ts.SyntaxKind[branch.kind]}`);
      };
      const thenSmt = lowerBranch(stmt.thenStatement);
      const elseSmt = stmt.elseStatement
        ? lowerBranch(stmt.elseStatement)
        : lowerStatements(stmts, idx + 1, env, ret);
      return `(ite ${condSmt} ${thenSmt} ${elseSmt})`;
    }

    throw new Error(`Unsupported statement in SMT lowering: ${ts.SyntaxKind[stmt.kind]}`);
  };

  const lowerBody = (
    body: ts.Block | ts.Expression,
    env: Map<string, string>,
    ret: VType,
  ): string => {
    if (ts.isBlock(body)) {
      return lowerStatements(body.statements, 0, env, ret);
    }
    return lowerExpr(body, env, ret);
  };

  // Lower all functions first (which also discovers any inline record types used inside bodies).
  const fnDefs: string[] = [];
  for (const fn of functions) {
    const env = new Map<string, string>();
    const paramsSmt = fn.params.map((p, i) => {
      const smtName = smtIdent(`p_${i}`, p.name);
      env.set(p.name, smtName);
      return `(${smtName} ${registry.register(p.type)})`;
    });
    const retSort = registry.register(fn.returnType);
    const bodySmt = lowerBody(fn.body, env, fn.returnType);
    fnDefs.push(
      `(define-fun ${fnSmtNames.get(fn.decl)!} (${paramsSmt.join(" ")}) ${retSort}\n  ${bodySmt})`,
    );
  }

  // Lower each law body first so every inline record type is registered before emitting datatype decls.
  const loweredLawBodies = laws.map((l) => {
    const env = new Map<string, string>();
    const paramSmtNames = l.params.map((p, i) => {
      const smtName = smtIdent(`arg_${i}`, p.name);
      env.set(p.name, smtName);
      return { tsName: p.name, smtName, type: p.type };
    });
    const bodySmt = lowerBody(l.body, env, { kind: "boolean" });
    return { law: l, paramSmtNames, bodySmt };
  });

  const datatypeDecls = registry.emitDeclarations();
  const recordsByCtor = registry.byCtorMap();

  return loweredLawBodies.map(({ law, paramSmtNames, bodySmt }) => {
    const lines: string[] = [
      // JSON-quoted: a raw newline in the name would end the comment and inject SMT commands.
      `; lawscript law: ${JSON.stringify(law.name)}`,
      "(set-option :produce-models true)",
      ...datatypeDecls,
      ...fnDefs,
      ...paramSmtNames.map((p) => `(declare-const ${p.smtName} ${registry.register(p.type)})`),
      `; Assert negation: unsat => law holds for ALL inputs`,
      `(assert (not ${bodySmt}))`,
      "(check-sat)",
    ];
    if (paramSmtNames.length > 0) {
      lines.push(`(get-value (${paramSmtNames.map((p) => p.smtName).join(" ")}))`);
    }
    return {
      law,
      smtScript: lines.join("\n") + "\n",
      paramSmtNames,
      recordsByCtor,
    };
  });
}
