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

/**
 * What a query proves: a user law, a postcondition, a call site's precondition, or that a
 * recursive call makes the termination measure smaller.
 */
export type GoalKind = "law" | "ensures" | "requires" | "decreases";

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
  /**
   * Indices (into the returned list) of goals this one relies on: the termination of every
   * recursive function whose definition the query uses, and every postcondition it assumes.
   * A PROVED verdict only stands if all of them are PROVED too.
   */
  readonly dependsOn: ReadonlyArray<number>;
  /**
   * The same goal without the assumed postconditions (present when there are any). If one of
   * those postconditions turns out not to hold, the goal may still be provable this way.
   */
  readonly plain?: { readonly smtScript: string; readonly dependsOn: ReadonlyArray<number> };
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
  /**
   * Emit goals only for this file's declarations (default: all), plus whatever goals of
   * imported modules those rely on.
   */
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
  const fnByDecl = new Map(functions.map((fn) => [fn.decl, fn]));
  const isLocal = (file: string): boolean => !localFile || localFile.fileName === file;

  // -------------------------------------------------------------------------
  // Groups of mutually recursive functions ("units"), callees first.
  // -------------------------------------------------------------------------
  const unitOf = new Map<ts.FunctionDeclaration, number>();
  const unitMembers: VerifiedFunction[][] = [];
  for (const fn of functions) {
    const last = unitMembers[unitMembers.length - 1];
    if (last && last[0]!.scc === fn.scc) last.push(fn);
    else unitMembers.push([fn]);
    unitOf.set(fn.decl, unitMembers.length - 1);
  }
  const unitRecursive = unitMembers.map((members) => members[0]!.recursive);
  const reachCache = new Map<number, ReadonlySet<number>>();
  /** The unit itself and every unit its functions call, directly or not. */
  const reach = (unit: number): ReadonlySet<number> => {
    const cached = reachCache.get(unit);
    if (cached) return cached;
    const out = new Set<number>([unit]);
    reachCache.set(unit, out);
    for (const fn of unitMembers[unit]!) {
      for (const callee of fn.calls) {
        const u = unitOf.get(callee);
        if (u === undefined || u === unit) continue;
        for (const r of reach(u)) out.add(r);
      }
    }
    return out;
  };

  /** Termination measure of a recursive function: one SMT function per `decreases` argument. */
  const measureNames = new Map<ts.FunctionDeclaration, string[]>();
  functions.forEach((fn, i) => {
    if (fn.recursive) measureNames.set(fn.decl, fn.decreases.map((_, k) => `mes_${i}_${k}`));
  });
  /**
   * `callee` is smaller than `caller` in the lexicographic order where an integer `a` is below
   * `b` when `a < b` and `b >= 0`. That order has no infinite descending chain.
   */
  const lexLess = (callee: ReadonlyArray<string>, caller: ReadonlyArray<string>): string => {
    if (callee.length !== caller.length || callee.length === 0) {
      throw new Error("Mutually recursive functions must have measures of the same length");
    }
    const at = (i: number): string => {
      const a = callee[i]!;
      const b = caller[i]!;
      const below = `(and (< ${a} ${b}) (<= 0 ${b}))`;
      return i === callee.length - 1 ? below : `(or ${below} (and (= ${a} ${b}) ${at(i + 1)}))`;
    };
    return at(0);
  };

  /** Postconditions by function, as indices into `ensures`. */
  const ensuresOf = new Map<ts.FunctionDeclaration, number[]>();
  ensures.forEach((e, j) => {
    const list = ensuresOf.get(e.fn) ?? [];
    list.push(j);
    ensuresOf.set(e.fn, list);
  });
  /** `post_<j>(args..., result)`: defined for postconditions of recursive functions. */
  const postDefs = new Map<
    number,
    { readonly name: string; readonly text: string; readonly used: ReadonlySet<ts.FunctionDeclaration> }
  >();

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
    readonly kind: "requires" | "decreases";
    readonly callee: string;
    readonly node: ts.Node;
    readonly formula: string;
  }
  const frames: Frame[] = [];
  let sink: Obligation[] = [];
  /** Functions called by the code being lowered. */
  let used = new Set<ts.FunctionDeclaration>();
  /** Set while lowering the body of a recursive function: its group and its own measure. */
  let recursion: { readonly unit: number; readonly measure: ReadonlyArray<string> } | undefined;
  /**
   * Set while lowering a goal that may use proved postconditions of recursive functions. Each
   * call to such a function adds "under the conditions at this point, the callee's
   * precondition implies its postcondition for these arguments" to `facts`.
   *
   * This is how induction happens: the solver does not do induction by itself, so a property
   * of a recursive function is stated as `ensures`, proved once with the postcondition assumed
   * at the (smaller) recursive calls, and then available wherever the function is called.
   */
  interface FactScope {
    allowed: (callee: VerifiedFunction, ensuresIndex: number) => boolean;
    readonly facts: string[];
    readonly posts: Set<number>;
    /** A second, narrower selection collected alongside (see the termination goals). */
    readonly strict?: {
      readonly allowed: (callee: VerifiedFunction, ensuresIndex: number) => boolean;
      readonly facts: string[];
      readonly posts: Set<number>;
    };
  }
  let factScope: FactScope | undefined;
  /** True while lowering code that runs (function bodies, `requires`, `decreases`). */
  let executable = false;
  const asExecutable = <T>(fn: () => T): T => {
    const saved = executable;
    executable = true;
    try {
      return fn();
    } finally {
      executable = saved;
    }
  };
  const withFacts = <T>(scope: FactScope | undefined, fn: () => T): T => {
    const saved = factScope;
    factScope = scope;
    try {
      return fn();
    } finally {
      factScope = saved;
    }
  };
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
        // In a law or postcondition the conclusion is only meaningful when the premise holds,
        // so calls inside it need their preconditions only then. Code in a function body
        // really runs, and JavaScript evaluates both arguments of `implies` whatever the
        // premise is, so there the calls must be justified unconditionally: a recursive
        // function called outside its precondition might never return.
        const premise = lowerExpr(premiseExpr, env);
        const conclusion = executable
          ? lowerExpr(conclusionExpr, env)
          : assuming(premise, () => lowerExpr(conclusionExpr, env));
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
      used.add(callee.decl);
      const args = expr.arguments.map((a, i) => lowerExpr(a, env, calleeFn.params[i]!.type));
      const call = app(target, args);
      const pre = preSmtNames.get(callee.decl);
      if (pre) {
        sink.push({
          kind: "requires",
          callee: calleeFn.name,
          node: expr,
          formula: closeOver(app(pre, args)),
        });
      }
      if (recursion && unitOf.get(callee.decl) === recursion.unit) {
        const calleeMeasure = (measureNames.get(callee.decl) ?? []).map((m) => app(m, args));
        sink.push({
          kind: "decreases",
          callee: calleeFn.name,
          node: expr,
          formula: closeOver(lexLess(calleeMeasure, recursion.measure)),
        });
      }
      if (factScope && calleeFn.recursive) {
        for (const j of ensuresOf.get(callee.decl) ?? []) {
          const post = postDefs.get(j);
          if (!post) continue;
          const holds = app(post.name, [...args, call]);
          const fact = closeOver(pre ? `(=> ${app(pre, args)} ${holds})` : holds);
          if (factScope.allowed(calleeFn, j)) {
            factScope.facts.push(fact);
            factScope.posts.add(j);
          }
          if (factScope.strict?.allowed(calleeFn, j)) {
            factScope.strict.facts.push(fact);
            factScope.strict.posts.add(j);
          }
        }
      }
      return call;
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

  interface Trace {
    readonly obligations: Obligation[];
    readonly used: Set<ts.FunctionDeclaration>;
  }
  /** Run `fn` and return the call-site obligations it emitted and the functions it called. */
  const collecting = (fn: () => void): Trace => {
    const saved = { sink, used };
    sink = [];
    used = new Set();
    try {
      fn();
      return { obligations: sink, used };
    } finally {
      sink = saved.sink;
      used = saved.used;
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
    /** Functions the query mentions; their definitions (and their callees') are included. */
    readonly roots: ReadonlySet<ts.FunctionDeclaration>;
    /** Postconditions of recursive functions the query assumes. */
    readonly posts: ReadonlySet<number>;
    /** `defs` and `assumptions` without those postconditions, when there are any. */
    readonly plain?: { readonly defs: ReadonlyArray<string>; readonly assumptions: ReadonlyArray<string> };
    /**
     * A recursive group that this query must not assume anything about: its functions are
     * declared without a definition. Used for the goals that justify the definition itself.
     */
    readonly opaque?: number;
    /** False for goals of imported modules, which are emitted only if something needs them. */
    readonly local: boolean;
  }
  const pending: Pending[] = [];
  let obligationId = 0;
  /** For each recursive group, the goals (indices into `pending`) that prove it terminates. */
  const terminationGoals = new Map<number, number[]>();
  /** For each postcondition, the goal (index into `pending`) that proves it. */
  const ensuresGoals = new Map<number, number>();

  const argNamesFor = (params: ReadonlyArray<VerifiedParam>) =>
    params.map((p, i) => ({ tsName: p.name, smtName: smtIdent(`arg_${i}`, p.name), type: p.type }));
  const obligationGoal = (
    ob: Obligation,
    params: ReadonlyArray<VerifiedParam>,
    caller?: string,
  ): Goal => {
    const location = getLocation(ob.node.getSourceFile(), ob.node);
    const name =
      ob.kind === "requires"
        ? `requires of ${ob.callee} at line ${location.line}`
        : `termination of ${caller ?? ob.callee}: call to ${ob.callee} at line ${location.line}`;
    return { name, params, location };
  };
  const withFactsAssumed = (facts: ReadonlyArray<string>, formula: string): string =>
    facts.length === 0 ? formula : `(=> (and true ${facts.join(" ")}) ${formula})`;

  // Postconditions of recursive functions, as predicates over the arguments and the result.
  ensures.forEach((e, j) => {
    const fn = fnByDecl.get(e.fn);
    if (!fn) throw new Error(`\`ensures\` refers to unknown function \`${e.fnName}\``);
    if (e.params.length !== fn.params.length + 1) {
      throw new Error(`Postcondition of \`${e.fnName}\` has the wrong number of parameters`);
    }
    if (!fn.recursive) return;
    const env = new Map<string, string>();
    const sig = [...fn.params.map((p) => p.type), fn.returnType].map((type, i) => {
      const callbackParam = e.params[i]!;
      const smtName = smtIdent(`q_${i}`, callbackParam.name);
      env.set(callbackParam.name, project(smtName, type, callbackParam.type));
      return `(${smtName} ${registry.register(type)})`;
    });
    let body = "";
    const trace = collecting(() => {
      body = withFacts(undefined, () => lowerBody(e.body, env, { kind: "boolean" }));
    });
    const name = `post_${j}`;
    postDefs.set(j, {
      name,
      text: `(define-fun ${name} (${sig.join(" ")}) Bool\n  ${body})`,
      used: trace.used,
    });
  });

  // Lower all functions (which also discovers any inline record types used inside bodies).
  interface Unit {
    /** Definitions of the group's functions. */
    readonly def: string[];
    /** The same functions declared without definitions (preconditions and measures kept). */
    readonly opaque: string[];
  }
  const units: Unit[] = unitMembers.map(() => ({ def: [], opaque: [] }));
  const recSigs = new Map<number, string[]>();
  const recBodies = new Map<number, string[]>();

  functions.forEach((fn, fnIdx) => {
    const unit = unitOf.get(fn.decl)!;
    const env = new Map<string, string>();
    const paramNames: string[] = [];
    const paramsSmt = fn.params.map((p, i) => {
      const smtName = smtIdent(`p_${i}`, p.name);
      env.set(p.name, smtName);
      paramNames.push(smtName);
      return `(${smtName} ${registry.register(p.type)})`;
    });
    const sorts = fn.params.map((p) => registry.register(p.type));
    const retSort = registry.register(fn.returnType);
    const fnSmt = fnSmtNames.get(fn.decl)!;
    const pre = preSmtNames.get(fn.decl);
    const measures = measureNames.get(fn.decl) ?? [];
    const specDefs: string[] = [];

    // Precondition goals inside this function may use the postconditions of every recursive
    // function it calls, itself included: postconditions are proved without relying on them.
    //
    // Termination goals are what make a recursive definition meaningful in the first place, so
    // they must not rest on that definition. They treat this function's group as unknown
    // functions and use only postconditions that lie strictly below it in the call graph
    // (including everything those postconditions mention).
    const below = (decl: ts.FunctionDeclaration): boolean => {
      const u = unitOf.get(decl);
      return u !== undefined && !reach(u).has(unit);
    };
    const scope = {
      allowed: () => true,
      facts: [] as string[],
      posts: new Set<number>(),
      strict: {
        allowed: (callee: VerifiedFunction, j: number) =>
          below(callee.decl) && [...postDefs.get(j)!.used].every(below),
        facts: [] as string[],
        posts: new Set<number>(),
      },
    } satisfies FactScope;

    // Preconditions first: each may rely on the ones before it, and the body on all of them.
    let bodySmt = "";
    const trace = collecting(() => {
      const pres: string[] = [];
      const lowerRest = (i: number): void => {
        const req = fn.requires[i];
        if (req) {
          const term = lowerExpr(req, env);
          pres.push(term);
          assuming(term, () => lowerRest(i + 1));
          return;
        }
        if (fn.recursive) {
          fn.decreases.forEach((m, k) => {
            specDefs.push(
              `(define-fun ${measures[k]!} (${paramsSmt.join(" ")}) Int\n  ${lowerExpr(m, env)})`,
            );
          });
          recursion = { unit, measure: measures.map((m) => app(m, paramNames)) };
        }
        try {
          bodySmt = lowerBody(fn.body, env, fn.returnType, fn.prefixLength);
        } finally {
          recursion = undefined;
        }
      };
      withFacts(scope, () => asExecutable(() => lowerRest(0)));
      if (pre) {
        specDefs.unshift(
          `(define-fun ${pre} (${paramsSmt.join(" ")}) Bool\n  ${pres.length === 1 ? pres[0] : `(and ${pres.join(" ")})`})`,
        );
      }
    });

    const u = units[unit]!;
    u.def.push(...specDefs);
    u.opaque.push(...specDefs, `(declare-fun ${fnSmt} (${sorts.join(" ")}) ${retSort})`);
    if (fn.recursive) {
      // Outside its precondition a recursive function has an arbitrary value. This keeps the
      // definition well-founded: the termination goals only cover arguments that satisfy it.
      let body = bodySmt;
      if (pre) {
        const undef = `undef_${fnIdx}`;
        u.def.push(`(declare-fun ${undef} (${sorts.join(" ")}) ${retSort})`);
        body = `(ite ${app(pre, paramNames)} ${bodySmt} ${app(undef, paramNames)})`;
      }
      const sigs = recSigs.get(unit) ?? [];
      const bodies = recBodies.get(unit) ?? [];
      sigs.push(`(${fnSmt} (${paramsSmt.join(" ")}) ${retSort})`);
      bodies.push(body);
      recSigs.set(unit, sigs);
      recBodies.set(unit, bodies);
    } else {
      u.def.push(`(define-fun ${fnSmt} (${paramsSmt.join(" ")}) ${retSort}\n  ${bodySmt})`);
    }

    // Obligation formulas mention the function's parameters, so each becomes a predicate over
    // them, claimed for all arguments. The enclosing `requires` are already inside the formula.
    const local = isLocal(fn.decl.getSourceFile().fileName);
    const argNames = argNamesFor(fn.params);
    for (const ob of trace.obligations) {
      // Preconditions of calls in imported modules are checked with those modules. Their
      // termination is checked here too if needed, because definitions here rely on it.
      if (!local && ob.kind === "requires") continue;
      const name = `ob_${obligationId++}`;
      const definitional = ob.kind === "decreases";
      const known = definitional ? scope.strict : scope;
      if (definitional) {
        const goals = terminationGoals.get(unit) ?? [];
        goals.push(pending.length);
        terminationGoals.set(unit, goals);
      }
      pending.push({
        kind: ob.kind,
        goal: obligationGoal(ob, fn.params, fn.name),
        argNames,
        defs: [
          `(define-fun ${name} (${paramsSmt.join(" ")}) Bool\n  ${withFactsAssumed(known.facts, ob.formula)})`,
        ],
        assumptions: [],
        claim: app(name, argNames.map((a) => a.smtName)),
        roots: new Set([fn.decl]),
        posts: known.posts,
        ...(known.facts.length > 0
          ? {
              plain: {
                defs: [`(define-fun ${name} (${paramsSmt.join(" ")}) Bool\n  ${ob.formula})`],
                assumptions: [],
              },
            }
          : {}),
        ...(definitional ? { opaque: unit } : {}),
        local,
      });
    }
  });
  for (const [unit, sigs] of recSigs) {
    units[unit]!.def.push(
      `(define-funs-rec (${sigs.join("\n                  ")})\n  (${recBodies.get(unit)!.join("\n   ")}))`,
    );
  }

  for (const l of laws) {
    const env = new Map<string, string>();
    const argNames = argNamesFor(l.params);
    for (const a of argNames) env.set(a.tsName, a.smtName);
    const scope: FactScope = { allowed: () => true, facts: [], posts: new Set() };
    let bodySmt = "";
    const trace = collecting(() => {
      bodySmt = withFacts(scope, () => lowerBody(l.body, env, { kind: "boolean" }));
    });
    const local = isLocal(l.location.file);
    const plain = scope.facts.length > 0 ? { plain: { defs: [], assumptions: [] } } : {};
    for (const ob of trace.obligations) {
      pending.push({
        kind: "requires",
        goal: obligationGoal(ob, l.params),
        argNames,
        defs: [],
        assumptions: scope.facts,
        claim: ob.formula,
        roots: trace.used,
        posts: scope.posts,
        ...plain,
        local,
      });
    }
    pending.push({
      kind: "law",
      goal: l,
      argNames,
      defs: [],
      assumptions: scope.facts,
      claim: bodySmt,
      roots: trace.used,
      posts: scope.posts,
      ...plain,
      local,
    });
  }

  const ensuresCount = new Map<ts.FunctionDeclaration, number>();
  ensures.forEach((e, j) => {
    const fn = fnByDecl.get(e.fn)!;
    const unit = unitOf.get(e.fn)!;
    const n = (ensuresCount.get(e.fn) ?? 0) + 1;
    ensuresCount.set(e.fn, n);

    // The arguments have the function's own parameter types; the callback may name them
    // differently and (with an annotation) view a record through a narrower type.
    const inputs = e.params.slice(0, -1);
    const resultParam = e.params[e.params.length - 1]!;
    const argNames = fn.params.map((p, i) => ({
      tsName: inputs[i]!.name,
      smtName: smtIdent(`arg_${i}`, inputs[i]!.name),
      type: p.type,
    }));
    const args = argNames.map((a) => a.smtName);
    const bodyEnv = new Map(fn.params.map((p, i) => [p.name, args[i]!]));
    const postEnv = new Map(
      inputs.map((p, i) => [p.name, project(args[i]!, fn.params[i]!.type, p.type)]),
    );
    const pre = preSmtNames.get(e.fn);
    const preTerm = pre ? app(pre, args) : undefined;
    const underPre = (fn_: () => void): void => {
      if (preTerm) assuming(preTerm, fn_);
      else fn_();
    };

    // The result is the function's body, not a call to it, so that the postconditions of the
    // calls inside the body can be assumed: those of functions below it because they are
    // proved separately, and those of recursive calls because the measure is smaller there
    // (the induction hypothesis).
    const scope: FactScope = { allowed: () => true, facts: [], posts: new Set() };
    let resultInit = "";
    const bodyTrace = collecting(() => {
      withFacts(scope, () =>
        underPre(() => {
          resultInit = asExecutable(() =>
            lowerBody(fn.body, bodyEnv, fn.returnType, fn.prefixLength),
          );
        }),
      );
    });

    // Calls written in the postcondition itself are at arbitrary arguments, so no induction
    // hypothesis applies to them: only functions that cannot reach this one may be assumed.
    scope.allowed = (callee) => !reach(unitOf.get(callee.decl)!).has(unit);
    const result = nextVar("result");
    postEnv.set(resultParam.name, project(result, fn.returnType, resultParam.type));
    let postSmt = "";
    const postTrace = collecting(() => {
      withFacts(scope, () =>
        underPre(() =>
          under({ kind: "let", v: result, init: resultInit }, () => {
            postSmt = lowerBody(e.body, postEnv, { kind: "boolean" });
          }),
        ),
      );
    });

    const local = isLocal(e.location.file);
    const params = inputs.map((p, i) => ({ name: p.name, type: fn.params[i]!.type }));
    const roots = new Set([e.fn, ...bodyTrace.used, ...postTrace.used]);
    const plain =
      scope.facts.length > 0
        ? { plain: { defs: [], assumptions: preTerm ? [preTerm] : [] } }
        : {};
    if (local) {
      for (const ob of postTrace.obligations) {
        pending.push({
          kind: "requires",
          goal: obligationGoal(ob, params),
          argNames,
          defs: [],
          assumptions: scope.facts,
          claim: ob.formula,
          roots,
          posts: scope.posts,
          ...plain,
          local,
        });
      }
    }
    ensuresGoals.set(j, pending.length);
    pending.push({
      kind: "ensures",
      goal: {
        name: `ensures ${e.fnName}${n > 1 ? ` #${n}` : ""}`,
        params,
        location: e.location,
      },
      argNames,
      defs: [],
      assumptions: [...(preTerm ? [preTerm] : []), ...scope.facts],
      claim: `(let ((${result} ${resultInit})) ${postSmt})`,
      roots,
      posts: scope.posts,
      ...plain,
      local,
    });
  });

  const datatypeDecls = registry.emitDeclarations();
  const recordsByCtor = registry.byCtorMap();

  // Each query contains only the definitions it mentions, so a recursive function elsewhere
  // in the module cannot affect it.
  const assemble = (
    p: Pending,
    defs: ReadonlyArray<string>,
    assumptions: ReadonlyArray<string>,
    posts: ReadonlySet<number>,
  ): { script: string; deps: Set<number> } => {
    const included = new Set<number>();
    const include = (decl: ts.FunctionDeclaration): void => {
      const u = unitOf.get(decl);
      if (u !== undefined) for (const r of reach(u)) included.add(r);
    };
    for (const decl of p.roots) include(decl);
    for (const j of posts) for (const decl of postDefs.get(j)!.used) include(decl);

    const fnDefs: string[] = [];
    const deps = new Set<number>();
    for (const u of [...included].sort((a, b) => a - b)) {
      if (u === p.opaque) {
        fnDefs.push(...units[u]!.opaque);
        continue;
      }
      fnDefs.push(...units[u]!.def);
      if (unitRecursive[u]) for (const g of terminationGoals.get(u) ?? []) deps.add(g);
    }
    for (const j of posts) deps.add(ensuresGoals.get(j)!);

    const lines: string[] = [
      // JSON-quoted: a raw newline in the name would end the comment and inject SMT commands.
      `; tslaw ${p.kind}: ${JSON.stringify(p.goal.name)}`,
      "(set-option :produce-models true)",
      ...datatypeDecls,
      ...fnDefs,
      ...[...posts].sort((a, b) => a - b).map((j) => postDefs.get(j)!.text),
      ...defs,
      ...p.argNames.map((a) => `(declare-const ${a.smtName} ${registry.register(a.type)})`),
      ...assumptions.map((a) => `(assert ${a})`),
      `; Assert negation: unsat => the claim holds for ALL inputs`,
      `(assert (not ${p.claim}))`,
      "(check-sat)",
    ];
    if (p.argNames.length > 0) {
      lines.push(`(get-value (${p.argNames.map((a) => a.smtName).join(" ")}))`);
    }
    return { script: lines.join("\n") + "\n", deps };
  };
  const assembled = pending.map((p) => ({
    pending: p,
    ...assemble(p, p.defs, p.assumptions, p.posts),
    plain: p.plain ? assemble(p, p.plain.defs, p.plain.assumptions, new Set()) : undefined,
  }));

  // Keep this file's goals and everything they rely on.
  const keep = new Set<number>();
  const visit = (i: number): void => {
    if (keep.has(i)) return;
    keep.add(i);
    for (const d of assembled[i]!.deps) visit(d);
  };
  assembled.forEach((a, i) => {
    if (a.pending.local) visit(i);
  });
  const kept = [...keep].sort((a, b) => a - b);
  const newIndex = new Map(kept.map((old, i) => [old, i]));
  const remap = (deps: ReadonlySet<number>): number[] =>
    [...deps].map((d) => newIndex.get(d)!).sort((a, b) => a - b);

  return kept.map((old) => {
    const { pending: p, script, deps, plain } = assembled[old]!;
    return {
      kind: p.kind,
      law: p.goal,
      smtScript: script,
      paramSmtNames: p.argNames,
      recordsByCtor,
      dependsOn: remap(deps),
      ...(plain ? { plain: { smtScript: plain.script, dependsOn: remap(plain.deps) } } : {}),
    };
  });
}
