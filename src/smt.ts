import ts from "typescript";
import {
  getLocation,
  resolveCallee,
  resolveVType,
  vTypeKey,
  type VerifiedEnsures,
  type VerifiedFunction,
  type VerifiedLaw,
  type VerifiedParam,
} from "./dialect.js";
import type { SourceLocation, VType } from "./types.js";

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

/** What a query proves: a user law, a postcondition, or a call site's precondition. */
export type GoalKind = "law" | "ensures" | "requires";

export interface Goal {
  readonly name: string;
  readonly params: ReadonlyArray<VerifiedParam>;
  readonly location: SourceLocation;
}

export interface LoweredLaw {
  readonly kind: GoalKind;
  readonly law: Goal;
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
  ensures: ReadonlyArray<VerifiedEnsures> = [],
  /** Emit call-site obligations only for functions declared in this file (default: all). */
  localFile?: ts.SourceFile,
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

  const preSmtNames = new Map<ts.FunctionDeclaration, string>();
  functions.forEach((fn, i) => {
    if (fn.requires.length > 0) preSmtNames.set(fn.decl, smtIdent(`pre_${i}`, fn.name));
  });
  const app = (name: string, args: ReadonlyArray<string>): string =>
    args.length > 0 ? `(${name} ${args.join(" ")})` : name;

  // -------------------------------------------------------------------------
  // Call-site obligations
  //
  // A call to a function with `requires` must satisfy it. While lowering, `frames` records
  // what is known at the current point: enclosing `let` bindings and the conditions under
  // which this code runs (`if`/ternary branches, the right side of `&&`/`||`, the conclusion
  // of `implies`). Each call then emits "frames imply the callee's precondition" into `sink`.
  // -------------------------------------------------------------------------
  type Frame =
    | { readonly kind: "let"; readonly v: string; readonly init: string }
    | { readonly kind: "assume"; readonly cond: string };
  interface Obligation {
    readonly callee: string;
    readonly node: ts.Node;
    readonly formula: string;
  }
  const frames: Frame[] = [];
  let sink: Obligation[] = [];
  const closeOver = (body: string): string =>
    frames.reduceRight(
      (acc, f) => (f.kind === "let" ? `(let ((${f.v} ${f.init})) ${acc})` : `(=> ${f.cond} ${acc})`),
      body,
    );
  const under = <T>(frame: Frame, fn: () => T): T => {
    frames.push(frame);
    try {
      return fn();
    } finally {
      frames.pop();
    }
  };
  const assuming = <T>(cond: string, fn: () => T): T => under({ kind: "assume", cond }, fn);

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
      const t = assuming(c, () => lowerExpr(expr.whenTrue, env, target));
      const f = assuming(`(not ${c})`, () => lowerExpr(expr.whenFalse, env, target));
      return `(ite ${c} ${t} ${f})`;
    }
    if (expected?.kind === "record" && ts.isObjectLiteralExpression(expr)) {
      // Build the expected record directly from the literal's properties. The literal's own
      // inferred type can be something no single datatype models (for example a field whose
      // value is a ternary between two record shapes), but each property has an expected type.
      const recDef = registry.getRecord(expected);
      const args = recDef.fields.map((f) => {
        for (const prop of expr.properties) {
          if (ts.isPropertyAssignment(prop) && ts.isIdentifier(prop.name) && prop.name.text === f.name) {
            return lowerExpr(prop.initializer, env, f.type);
          }
          if (ts.isShorthandPropertyAssignment(prop) && prop.name.text === f.name) {
            return lowerExpr(prop.name, env, f.type);
          }
        }
        throw new Error(`Missing field \`${f.name}\` in object literal`);
      });
      return `(${recDef.ctorName} ${args.join(" ")})`;
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
      // JavaScript only evaluates the right side of `&&` when the left is true (and of `||`
      // when it is false), so calls there only need their preconditions in that case.
      const op = expr.operatorToken.kind;
      const right =
        op === ts.SyntaxKind.AmpersandAmpersandToken
          ? assuming(left, () => lowerExpr(expr.right, env))
          : op === ts.SyntaxKind.BarBarToken
            ? assuming(`(not ${left})`, () => lowerExpr(expr.right, env))
            : lowerExpr(expr.right, env);
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
        const [premiseExpr, conclusionExpr] = expr.arguments;
        if (expr.arguments.length !== 2 || !premiseExpr || !conclusionExpr) {
          throw new Error("`implies` requires exactly 2 arguments");
        }
        // The conclusion is only meaningful when the premise holds, so calls inside it need
        // their preconditions only then. (At runtime both sides are evaluated, which is
        // harmless: verified functions are total and `requires` does nothing at runtime.)
        const premise = lowerExpr(premiseExpr, env);
        const conclusion = assuming(premise, () => lowerExpr(conclusionExpr, env));
        return `(=> ${premise} ${conclusion})`;
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
      const pre = preSmtNames.get(callee.decl);
      if (pre) {
        sink.push({ callee: calleeFn.name, node: expr, formula: closeOver(app(pre, args)) });
      }
      return app(target, args);
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
          const rest = under({ kind: "let", v, init: initSmt }, () => lowerDeclAt(dIdx + 1, nextEnv));
          return `(let ((${v} ${initSmt})) ${rest})`;
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
          const rest = under({ kind: "let", v: tmp, init: initSmt }, () => lowerDeclAt(dIdx + 1, nextEnv));
          return `(let ((${tmp} ${initSmt})) ${rest})`;
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
      const thenSmt = assuming(condSmt, () => lowerBranch(stmt.thenStatement));
      const elseStmt = stmt.elseStatement;
      const elseSmt = assuming(`(not ${condSmt})`, () =>
        elseStmt ? lowerBranch(elseStmt) : lowerStatements(stmts, idx + 1, env, ret),
      );
      return `(ite ${condSmt} ${thenSmt} ${elseSmt})`;
    }

    throw new Error(`Unsupported statement in SMT lowering: ${ts.SyntaxKind[stmt.kind]}`);
  };

  const lowerBody = (
    body: ts.Block | ts.Expression,
    env: Map<string, string>,
    ret: VType,
    /** Leading `requires(...)` statements to skip. */
    skip = 0,
  ): string => {
    if (ts.isBlock(body)) {
      return lowerStatements(body.statements, skip, env, ret);
    }
    return lowerExpr(body, env, ret);
  };

  /** Run `fn` and return the call-site obligations it emitted. */
  const collecting = (fn: () => void): Obligation[] => {
    const saved = sink;
    sink = [];
    try {
      fn();
      return sink;
    } finally {
      sink = saved;
    }
  };

  interface Pending {
    readonly kind: GoalKind;
    readonly goal: Goal;
    readonly argNames: ReadonlyArray<{ tsName: string; smtName: string; type: VType }>;
    /** Extra definitions that must follow the function definitions. */
    readonly defs: ReadonlyArray<string>;
    readonly assumptions: ReadonlyArray<string>;
    /** The claim; the query asserts its negation. */
    readonly claim: string;
  }
  const pending: Pending[] = [];
  let obligationId = 0;

  const argNamesFor = (params: ReadonlyArray<VerifiedParam>) =>
    params.map((p, i) => ({ tsName: p.name, smtName: smtIdent(`arg_${i}`, p.name), type: p.type }));
  const obligationGoal = (ob: Obligation, params: ReadonlyArray<VerifiedParam>): Goal => {
    const location = getLocation(ob.node.getSourceFile(), ob.node);
    return { name: `requires of ${ob.callee} at line ${location.line}`, params, location };
  };

  // Lower all functions first (which also discovers any inline record types used inside bodies).
  const fnDefs: string[] = [];
  for (const fn of functions) {
    const env = new Map<string, string>();
    const paramNames: string[] = [];
    const paramsSmt = fn.params.map((p, i) => {
      const smtName = smtIdent(`p_${i}`, p.name);
      env.set(p.name, smtName);
      paramNames.push(smtName);
      return `(${smtName} ${registry.register(p.type)})`;
    });
    const retSort = registry.register(fn.returnType);

    // Preconditions first: each may rely on the ones before it, and the body on all of them.
    let bodySmt = "";
    const obligations = collecting(() => {
      const pres: string[] = [];
      const lowerRest = (i: number): void => {
        const req = fn.requires[i];
        if (!req) {
          bodySmt = lowerBody(fn.body, env, fn.returnType, fn.requires.length);
          return;
        }
        const term = lowerExpr(req, env);
        pres.push(term);
        assuming(term, () => lowerRest(i + 1));
      };
      lowerRest(0);
      const pre = preSmtNames.get(fn.decl);
      if (pre) {
        fnDefs.push(
          `(define-fun ${pre} (${paramsSmt.join(" ")}) Bool\n  ${pres.length === 1 ? pres[0] : `(and ${pres.join(" ")})`})`,
        );
      }
    });
    fnDefs.push(
      `(define-fun ${fnSmtNames.get(fn.decl)!} (${paramsSmt.join(" ")}) ${retSort}\n  ${bodySmt})`,
    );

    if (localFile && fn.decl.getSourceFile() !== localFile) continue;
    // Obligation formulas mention the function's parameters, so each becomes a predicate over
    // them, claimed for all arguments. The enclosing `requires` are already inside the formula.
    const argNames = argNamesFor(fn.params);
    for (const ob of obligations) {
      const name = `ob_${obligationId++}`;
      pending.push({
        kind: "requires",
        goal: obligationGoal(ob, fn.params),
        argNames,
        defs: [`(define-fun ${name} (${paramsSmt.join(" ")}) Bool\n  ${ob.formula})`],
        assumptions: [],
        claim: app(name, argNames.map((a) => a.smtName)),
      });
    }
  }

  for (const l of laws) {
    const env = new Map<string, string>();
    const argNames = argNamesFor(l.params);
    for (const a of argNames) env.set(a.tsName, a.smtName);
    let bodySmt = "";
    const obligations = collecting(() => {
      bodySmt = lowerBody(l.body, env, { kind: "boolean" });
    });
    for (const ob of obligations) {
      pending.push({
        kind: "requires",
        goal: obligationGoal(ob, l.params),
        argNames,
        defs: [],
        assumptions: [],
        claim: ob.formula,
      });
    }
    pending.push({ kind: "law", goal: l, argNames, defs: [], assumptions: [], claim: bodySmt });
  }

  const ensuresCount = new Map<ts.FunctionDeclaration, number>();
  for (const e of ensures) {
    const fnSmt = fnSmtNames.get(e.fn);
    const fn = functions.find((f) => f.decl === e.fn);
    if (!fnSmt || !fn) throw new Error(`\`ensures\` refers to unknown function \`${e.fnName}\``);
    if (e.params.length !== fn.params.length + 1) {
      throw new Error(`Postcondition of \`${e.fnName}\` has the wrong number of parameters`);
    }
    const n = (ensuresCount.get(e.fn) ?? 0) + 1;
    ensuresCount.set(e.fn, n);

    const inputs = e.params.slice(0, -1);
    const resultParam = e.params[e.params.length - 1]!;
    const env = new Map<string, string>();
    const argNames = argNamesFor(inputs);
    for (const a of argNames) env.set(a.tsName, a.smtName);
    const args = argNames.map((a) => a.smtName);
    const pre = preSmtNames.get(e.fn);
    const assumptions = pre ? [app(pre, args)] : [];
    const result = nextVar("result");
    env.set(resultParam.name, result);
    const resultInit = app(fnSmt, args);

    let postSmt = "";
    const obligations = collecting(() => {
      const lowerPost = (): void => {
        under({ kind: "let", v: result, init: resultInit }, () => {
          postSmt = lowerBody(e.body, env, { kind: "boolean" });
        });
      };
      if (pre) assuming(app(pre, args), lowerPost);
      else lowerPost();
    });
    for (const ob of obligations) {
      pending.push({
        kind: "requires",
        goal: obligationGoal(ob, inputs),
        argNames,
        defs: [],
        assumptions: [],
        claim: ob.formula,
      });
    }
    pending.push({
      kind: "ensures",
      goal: {
        name: `ensures ${e.fnName}${n > 1 ? ` #${n}` : ""}`,
        params: inputs,
        location: e.location,
      },
      argNames,
      defs: [],
      assumptions,
      claim: `(let ((${result} ${resultInit})) ${postSmt})`,
    });
  }

  const datatypeDecls = registry.emitDeclarations();
  const recordsByCtor = registry.byCtorMap();

  return pending.map(({ kind, goal, argNames, defs, assumptions, claim }) => {
    const lines: string[] = [
      // JSON-quoted: a raw newline in the name would end the comment and inject SMT commands.
      `; tslaw ${kind}: ${JSON.stringify(goal.name)}`,
      "(set-option :produce-models true)",
      ...datatypeDecls,
      ...fnDefs,
      ...defs,
      ...argNames.map((p) => `(declare-const ${p.smtName} ${registry.register(p.type)})`),
      ...assumptions.map((a) => `(assert ${a})`),
      `; Assert negation: unsat => the claim holds for ALL inputs`,
      `(assert (not ${claim}))`,
      "(check-sat)",
    ];
    if (argNames.length > 0) {
      lines.push(`(get-value (${argNames.map((p) => p.smtName).join(" ")}))`);
    }
    return {
      kind,
      law: goal,
      smtScript: lines.join("\n") + "\n",
      paramSmtNames: argNames,
      recordsByCtor,
    };
  });
}
