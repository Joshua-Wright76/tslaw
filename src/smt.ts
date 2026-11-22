import ts from "typescript";
import { resolveVType, vTypeKey, type VerifiedFunction, type VerifiedLaw } from "./dialect.js";
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
      fields: type.fields.map((f) => ({
        name: f.name,
        smtAccessor: `${smtName}_${f.name}`,
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

function smtIdent(prefix: string, name: string): string {
  // Prefix avoids collisions with SMT-LIB2 reserved words like `and`, `or`, `mod`, `to`, `from`, `assert`.
  const safe = name.replace(/[^A-Za-z0-9_]/g, "_");
  return `${prefix}_${safe}`;
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

  const lowerExpr = (expr: ts.Expression, env: Map<string, string>): string => {
    if (ts.isParenthesizedExpression(expr)) {
      return lowerExpr(expr.expression, env);
    }
    if (ts.isBigIntLiteral(expr)) {
      const raw = expr.text.replace(/_/g, "").replace(/n$/, "");
      if (raw.startsWith("-")) {
        return `(- ${raw.slice(1)})`;
      }
      return raw;
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
    if (ts.isConditionalExpression(expr)) {
      const c = lowerExpr(expr.condition, env);
      const t = lowerExpr(expr.whenTrue, env);
      const f = lowerExpr(expr.whenFalse, env);
      return `(ite ${c} ${t} ${f})`;
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
      const args = expr.arguments.map((a) => lowerExpr(a, env));
      if (fnName === "implies") {
        return `(=> ${args[0]} ${args[1]})`;
      }
      const target = smtIdent("fn", fnName);
      return args.length > 0 ? `(${target} ${args.join(" ")})` : target;
    }

    throw new Error(`Unsupported expression in SMT lowering: ${ts.SyntaxKind[expr.kind]}`);
  };

  const lowerStatements = (
    stmts: ReadonlyArray<ts.Statement>,
    idx: number,
    env: Map<string, string>,
  ): string => {
    const stmt = stmts[idx];
    if (!stmt) {
      throw new Error("Control reached end of block without return during SMT lowering");
    }

    if (ts.isReturnStatement(stmt)) {
      if (!stmt.expression) throw new Error("Bare return in SMT lowering");
      return lowerExpr(stmt.expression, env);
    }

    if (ts.isVariableStatement(stmt)) {
      const decls = stmt.declarationList.declarations;
      const lowerDeclAt = (dIdx: number, curEnv: Map<string, string>): string => {
        const decl = decls[dIdx];
        if (!decl) return lowerStatements(stmts, idx + 1, curEnv);
        if (!decl.initializer) throw new Error("Missing initializer");
        const initSmt = lowerExpr(decl.initializer, curEnv);

        if (ts.isIdentifier(decl.name)) {
          const v = nextVar(decl.name.text);
          const nextEnv = new Map(curEnv);
          nextEnv.set(decl.name.text, v);
          return `(let ((${v} ${initSmt})) ${lowerDeclAt(dIdx + 1, nextEnv)})`;
        }
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
          return lowerStatements(branch.statements, 0, env);
        }
        if (ts.isReturnStatement(branch) || ts.isIfStatement(branch)) {
          return lowerStatements([branch], 0, env);
        }
        throw new Error(`Unsupported if branch: ${ts.SyntaxKind[branch.kind]}`);
      };
      const thenSmt = lowerBranch(stmt.thenStatement);
      const elseSmt = stmt.elseStatement
        ? lowerBranch(stmt.elseStatement)
        : lowerStatements(stmts, idx + 1, env);
      return `(ite ${condSmt} ${thenSmt} ${elseSmt})`;
    }

    throw new Error(`Unsupported statement in SMT lowering: ${ts.SyntaxKind[stmt.kind]}`);
  };

  const lowerBody = (
    body: ts.Block | ts.Expression,
    env: Map<string, string>,
  ): string => {
    if (ts.isBlock(body)) {
      return lowerStatements(body.statements, 0, env);
    }
    return lowerExpr(body, env);
  };

  // Lower all functions first (which also discovers any inline record types used inside bodies).
  const fnDefs: string[] = [];
  for (const fn of functions) {
    const env = new Map<string, string>();
    const paramsSmt = fn.params.map((p) => {
      const smtName = smtIdent("p", p.name);
      env.set(p.name, smtName);
      return `(${smtName} ${registry.register(p.type)})`;
    });
    const retSort = registry.register(fn.returnType);
    const bodySmt = lowerBody(fn.body, env);
    fnDefs.push(
      `(define-fun ${smtIdent("fn", fn.name)} (${paramsSmt.join(" ")}) ${retSort}\n  ${bodySmt})`,
    );
  }

  // Lower each law body first so every inline record type is registered before emitting datatype decls.
  const loweredLawBodies = laws.map((l) => {
    const env = new Map<string, string>();
    const paramSmtNames = l.params.map((p) => {
      const smtName = smtIdent("arg", p.name);
      env.set(p.name, smtName);
      return { tsName: p.name, smtName, type: p.type };
    });
    const bodySmt = lowerBody(l.body, env);
    return { law: l, paramSmtNames, bodySmt };
  });

  const datatypeDecls = registry.emitDeclarations();
  const recordsByCtor = registry.byCtorMap();

  return loweredLawBodies.map(({ law, paramSmtNames, bodySmt }) => {
    const lines: string[] = [
      `; vscript law: ${law.name}`,
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
