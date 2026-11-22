import ts from "typescript";
import {
  isArrayHelper,
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
 * What a query proves: a user law, a postcondition, a call site's precondition, that a
 * recursive call or loop iteration makes the termination measure smaller, or that a loop
 * invariant holds on entry / is kept by the loop body.
 */
export type GoalKind = "law" | "ensures" | "requires" | "decreases" | "invariant";

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
   * The subset of dependencies without which even a counterexample means nothing: the
   * termination of the recursive functions and loops involved and, for laws and
   * postconditions, every precondition and invariant that the code they run relies on. (The
   * rest are assumed postconditions, whose failure cannot invalidate a counterexample.)
   */
  readonly foundations: ReadonlyArray<number>;
  /**
   * The same goal without the assumed postconditions (present when there are any). If one of
   * those postconditions turns out not to hold, the goal may still be provable this way.
   */
  readonly plain?: { readonly smtScript: string; readonly dependsOn: ReadonlyArray<number> };
  /**
   * The same goal with recursive functions and loops left undefined, so that only their
   * assumed postconditions and invariants are known about them (present when there are any).
   * Worth trying first: it is how induction-style proofs go through, and solvers are much
   * faster without definitions they could unfold forever.
   */
  readonly abstract?: { readonly smtScript: string; readonly dependsOn: ReadonlyArray<number> };
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
    if (type.kind === "array") return `(Seq ${this.register(type.element)})`;
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
  interface Unit {
    /** Definitions of the group's functions. */
    readonly def: string[];
    /** The same functions declared without definitions (preconditions and measures kept). */
    readonly opaque: string[];
    /** Units whose functions this one mentions. Loops are units too (see below). */
    readonly deps: Set<number>;
    readonly recursive: boolean;
  }
  const units: Unit[] = [];
  const unitOf = new Map<ts.FunctionDeclaration, number>();
  {
    let lastScc: number | undefined;
    for (const fn of functions) {
      if (lastScc !== fn.scc) {
        units.push({ def: [], opaque: [], deps: new Set(), recursive: fn.recursive });
        lastScc = fn.scc;
      }
      unitOf.set(fn.decl, units.length - 1);
    }
    for (const fn of functions) {
      const own = unitOf.get(fn.decl)!;
      for (const callee of fn.calls) {
        const u = unitOf.get(callee);
        if (u !== undefined && u !== own) units[own]!.deps.add(u);
      }
    }
  }
  /** The unit itself and every unit it mentions, directly or not. */
  const reach = (unit: number): Set<number> => {
    const out = new Set<number>();
    const visit = (u: number): void => {
      if (out.has(u)) return;
      out.add(u);
      for (const d of units[u]!.deps) visit(d);
    };
    visit(unit);
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
  /**
   * `post_<j>(args..., result)`: defined for postconditions of functions whose properties need
   * induction (recursive ones, and ones that contain loops).
   */
  const postDefs = new Map<
    number,
    { readonly name: string; readonly text: string; readonly used: ReadonlySet<number> }
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
    readonly kind: "requires" | "decreases" | "invariant";
    readonly callee: string;
    readonly node: ts.Node;
    readonly formula: string;
  }
  const frames: Frame[] = [];
  let sink: Obligation[] = [];
  /** Units (function groups and loops) mentioned by the code being lowered. */
  let used = new Set<number>();
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
    /** Goals (indices into `pending`) that facts about loops rest on. */
    readonly goals: Set<number>;
    /** A second, narrower selection collected alongside (see the termination goals). */
    readonly strict?: {
      readonly allowed: (callee: VerifiedFunction, ensuresIndex: number) => boolean;
      readonly facts: string[];
      readonly posts: Set<number>;
      readonly goals: Set<number>;
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
    let type = checker.getTypeAtLocation(node);
    if (type.getFlags() & ts.TypeFlags.Never) {
      // TypeScript gives `never` to code it can see is unreachable, for example the right side
      // of `b || ...` after `b = true`. Such code still needs a well-formed translation, so
      // fall back to the type the expression would have without that knowledge.
      let inner = node;
      while (ts.isParenthesizedExpression(inner)) inner = inner.expression;
      if (ts.isConditionalExpression(inner)) {
        try {
          return resolveExprVType(inner.whenFalse);
        } catch {
          return resolveExprVType(inner.whenTrue);
        }
      }
      if (ts.isIdentifier(inner)) {
        const sym = checker.getSymbolAtLocation(inner);
        const decl = sym?.valueDeclaration;
        if (sym && decl) type = checker.getTypeOfSymbolAtLocation(sym, decl);
      }
    }
    const res = resolveVType(checker, type);
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
    if (from.kind === "array" && to.kind === "array") {
      // Would need a new sequence with every element converted.
      throw new Error(
        "an array of records with extra fields cannot be used where an array of a narrower record type is expected; build the array at the narrower type",
      );
    }
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
      const expectedByName = new Map(recDef.fields.map((f) => [f.name, f.type]));
      const values = new Map<string, string>();
      for (const prop of expr.properties) {
        if (ts.isPropertyAssignment(prop) && ts.isIdentifier(prop.name)) {
          const name = prop.name.text;
          // Lower every property, even extra ones dropped by width subtyping, so calls inside
          // them still emit their preconditions, termination goals and dependencies.
          const val = lowerExpr(prop.initializer, env, expectedByName.get(name));
          if (expectedByName.has(name)) values.set(name, val);
        } else if (ts.isShorthandPropertyAssignment(prop)) {
          const name = prop.name.text;
          const val = lowerExpr(prop.name, env, expectedByName.get(name));
          if (expectedByName.has(name)) values.set(name, val);
        }
      }
      const args = recDef.fields.map((f) => {
        const val = values.get(f.name);
        if (val === undefined) throw new Error(`Missing field \`${f.name}\` in object literal`);
        return val;
      });
      return `(${recDef.ctorName} ${args.join(" ")})`;
    }
    if (ts.isArrayLiteralExpression(expr)) {
      // Elements are lowered at the expected element type, so `[]` and literals of wider
      // records work wherever the context says what the array holds.
      const type = expected ?? resolveExprVType(expr);
      if (type.kind !== "array") throw new Error("Array literal where no array is expected");
      const sort = registry.register(type);
      const items = expr.elements.map((el) => `(seq.unit ${lowerExpr(el, env, type.element)})`);
      if (items.length === 0) return `(as seq.empty ${sort})`;
      return items.length === 1 ? items[0]! : `(seq.++ ${items.join(" ")})`;
    }
    const smt = lowerExprRaw(expr, env);
    if (!expected || (expected.kind !== "record" && expected.kind !== "array")) return smt;
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
      if (callee.kind === "runtime" && isArrayHelper(callee.helper)) {
        // Arrays are SMT sequences. Reading or cutting outside the array has no meaning (and
        // throws at runtime), so those helpers come with a precondition like any `requires`.
        const [first, ...others] = expr.arguments;
        if (!first) throw new Error(`\`${fnName}\` needs an array argument`);
        // The array type is the one TypeScript chose for this call (`T` may be narrower than
        // the first argument's own element type, as in `append([wide], narrow)`).
        const signature = checker.getResolvedSignature(expr);
        const param = signature?.parameters[0];
        const declared = param
          ? resolveVType(checker, checker.getTypeOfSymbolAtLocation(param, expr))
          : undefined;
        const type = declared?.ok ? declared.type : resolveExprVType(first);
        if (type.kind !== "array") throw new Error(`\`${fnName}\` needs an array argument`);
        registry.register(type);
        const xs = lowerExpr(first, env, type);
        const argument = (i: number, expected?: VType): string => {
          const arg = others[i];
          if (!arg) throw new Error(`Wrong number of arguments in call to \`${fnName}\``);
          return lowerExpr(arg, env, expected);
        };
        const needs = (condition: string): void => {
          sink.push({ kind: "requires", callee: fnName, node: expr, formula: closeOver(condition) });
        };
        switch (callee.helper) {
          case "len":
            return `(seq.len ${xs})`;
          case "at": {
            const i = argument(0);
            needs(`(and (<= 0 ${i}) (< ${i} (seq.len ${xs})))`);
            return `(seq.nth ${xs} ${i})`;
          }
          case "append":
            return `(seq.++ ${xs} (seq.unit ${argument(0, type.element)}))`;
          case "concat":
            return `(seq.++ ${xs} ${argument(0, type)})`;
          case "slice": {
            const from = argument(0);
            const to = argument(1);
            needs(`(and (<= 0 ${from}) (<= ${from} ${to}) (<= ${to} (seq.len ${xs})))`);
            return `(seq.extract ${xs} ${from} (- ${to} ${from}))`;
          }
          case "withAt": {
            const i = argument(0);
            const v = argument(1, type.element);
            needs(`(and (<= 0 ${i}) (< ${i} (seq.len ${xs})))`);
            return `(seq.++ (seq.extract ${xs} 0 ${i}) (seq.unit ${v}) (seq.extract ${xs} (+ ${i} 1) (- (seq.len ${xs}) ${i} 1)))`;
          }
        }
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
      used.add(unitOf.get(callee.decl)!);
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
      if (currentUnit !== undefined && currentUnit !== ownerUnit && unitOf.get(callee.decl) === ownerUnit) {
        throw new Error(
          `A loop may not call \`${calleeFn.name}\`, which is part of the enclosing function's recursion`,
        );
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
      if (factScope && (calleeFn.recursive || calleeFn.hasLoops)) {
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

  interface Trace {
    readonly obligations: Obligation[];
    readonly used: Set<number>;
  }
  /** Run `fn` and return the call-site obligations it emitted and the units it mentioned. */
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
    /** Units the query mentions; their definitions (and those they mention) are included. */
    readonly roots: ReadonlySet<number>;
    /** Postconditions of recursive functions the query assumes. */
    readonly posts: ReadonlySet<number>;
    /** Further goals the assumed facts rest on (loop invariants being kept). */
    readonly factGoals: ReadonlySet<number>;
    /** `defs` and `assumptions` without those postconditions, when there are any. */
    readonly plain?: { readonly defs: ReadonlyArray<string>; readonly assumptions: ReadonlyArray<string> };
    /**
     * A recursive group that this query must not assume anything about: its functions are
     * declared without a definition. Used for the goals that justify the definition itself.
     */
    readonly opaque?: number;
    /** For a law or postcondition: the call-site goals of its own expression. */
    readonly own?: ReadonlyArray<number>;
    /** False for goals of imported modules, which are emitted only if something needs them. */
    readonly local: boolean;
  }
  const pending: Pending[] = [];
  let obligationId = 0;
  /** For each recursive group, the goals (indices into `pending`) that prove it terminates. */
  const terminationGoals = new Map<number, number[]>();
  /**
   * For each unit, the goals (indices into `pending`) that its code is only meaningful under:
   * preconditions of the calls it makes, invariants holding on entry to its loops and being
   * kept by them. The model leaves a recursive function unspecified outside its precondition
   * and a loop unspecified outside its invariant, and `at`/`slice`/`withAt` throw out of range,
   * so a law about code where one of these can fail says nothing about what really happens.
   */
  const unitChecks = new Map<number, number[]>();
  const addCheck = (unit: number, goal: number): void => {
    unitChecks.set(unit, [...(unitChecks.get(unit) ?? []), goal]);
  };
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
        : ob.kind === "invariant"
          ? `invariant of the loop at line ${location.line}: holds on entry`
          : `termination of ${caller ?? ob.callee}: call to ${ob.callee} at line ${location.line}`;
    return { name, params, location };
  };
  /**
   * One goal per source location: code after an `if` whose branches can both return and fall
   * through is lowered once per path, which yields the same obligation several times.
   */
  const mergeObligations = (obligations: ReadonlyArray<Obligation>): Obligation[] => {
    const byKey = new Map<string, Obligation[]>();
    for (const ob of obligations) {
      const key = `${ob.kind}:${ob.node.pos}:${ob.node.getSourceFile().fileName}`;
      byKey.set(key, [...(byKey.get(key) ?? []), ob]);
    }
    return [...byKey.values()].map((group) =>
      group.length === 1
        ? group[0]!
        : { ...group[0]!, formula: `(and ${group.map((g) => g.formula).join(" ")})` },
    );
  };
  const withFactsAssumed = (facts: ReadonlyArray<string>, formula: string): string =>
    facts.length === 0 ? formula : `(=> (and true ${facts.join(" ")}) ${formula})`;

  // -------------------------------------------------------------------------
  // Statements
  //
  // A statement that cannot `return` (a declaration, an assignment, an `if` without `return`
  // inside, a loop) only changes what the local variables are bound to. It is lowered to a
  // list of `let` bindings plus the new environment; an assignment simply binds a fresh name.
  // After an `if`, a variable that the two branches leave different gets `(ite c then else)`.
  // -------------------------------------------------------------------------
  type LetFrame = Extract<Frame, { kind: "let" }>;
  type Env = Map<string, string>;
  interface Flow {
    readonly lets: LetFrame[];
    readonly env: Env;
  }
  const wrapLets = (lets: ReadonlyArray<LetFrame>, body: string): string =>
    lets.reduceRight((acc, l) => `(let ((${l.v} ${l.init})) ${acc})`, body);
  const withFrames = <T>(fs: ReadonlyArray<Frame>, fn: () => T): T => {
    frames.push(...fs);
    try {
      return fn();
    } finally {
      frames.length -= fs.length;
    }
  };
  const containsReturn = (stmt: ts.Statement): boolean => {
    if (ts.isReturnStatement(stmt)) return true;
    if (ts.isBlock(stmt)) return stmt.statements.some(containsReturn);
    if (ts.isIfStatement(stmt)) {
      return (
        containsReturn(stmt.thenStatement) ||
        (stmt.elseStatement !== undefined && containsReturn(stmt.elseStatement))
      );
    }
    return false;
  };
  const branchStatements = (branch: ts.Statement): ReadonlyArray<ts.Statement> =>
    ts.isBlock(branch) ? branch.statements : [branch];
  /** Names declared directly in a block; they go out of scope at its end. */
  const declaredNames = (stmts: ReadonlyArray<ts.Statement>): Set<string> => {
    const out = new Set<string>();
    for (const s of stmts) {
      if (!ts.isVariableStatement(s)) continue;
      for (const d of s.declarationList.declarations) {
        if (ts.isIdentifier(d.name)) out.add(d.name.text);
        else if (ts.isObjectBindingPattern(d.name)) {
          for (const el of d.name.elements) if (ts.isIdentifier(el.name)) out.add(el.name.text);
        }
      }
    }
    return out;
  };
  /** The environment after a block: outer variables keep what the block assigned to them. */
  const leaveScope = (outer: Env, inner: Env, declared: ReadonlySet<string>): Env => {
    const out = new Map(outer);
    for (const name of outer.keys()) {
      if (!declared.has(name)) out.set(name, inner.get(name)!);
    }
    return out;
  };
  const ASSIGN_OPS = new Map<ts.SyntaxKind, string | undefined>([
    [ts.SyntaxKind.EqualsToken, undefined],
    [ts.SyntaxKind.PlusEqualsToken, "+"],
    [ts.SyntaxKind.MinusEqualsToken, "-"],
    [ts.SyntaxKind.AsteriskEqualsToken, "*"],
  ]);
  /** `invariant(...)` / `decreases(...)` at the start of a loop body. */
  const loopSpecCall = (
    stmt: ts.Statement,
  ): { helper: "invariant" | "decreases"; args: ts.NodeArray<ts.Expression> } | undefined => {
    if (
      !ts.isExpressionStatement(stmt) ||
      !ts.isCallExpression(stmt.expression) ||
      !ts.isIdentifier(stmt.expression.expression)
    ) {
      return undefined;
    }
    const callee = resolveCallee(checker, stmt.expression.expression);
    if (callee.kind !== "runtime") return undefined;
    if (callee.helper !== "invariant" && callee.helper !== "decreases") return undefined;
    return { helper: callee.helper, args: stmt.expression.arguments };
  };

  // -------------------------------------------------------------------------
  // Loops
  //
  // `while (c) { body }` over the variables it mentions becomes a recursive function from
  // those variables to the final values of the ones it assigns:
  //
  //   L(vars) = if invariant(vars) then (if c(vars) then L(vars after body) else state(vars))
  //             else unspecified
  //
  // so everything about recursion applies: the measure must shrink on each iteration
  // (termination goal), and the invariant plays the part of both precondition (it must hold
  // on entry and be kept by the body) and postcondition (it holds, with `not c`, afterwards).
  // -------------------------------------------------------------------------
  interface LoopInfo {
    readonly unit: number;
    readonly fn: string;
    readonly params: ReadonlyArray<{ readonly name: string; readonly type: VType }>;
    readonly inv: string | undefined;
    /** False when the invariant is only the inherited precondition, which needs no proof. */
    readonly checkEntry: boolean;
    /** Variables the loop assigns, with the selector that reads each from the result. */
    readonly modified: ReadonlyArray<{ readonly name: string; readonly accessor: string }>;
    /** What is known about the result `state` of running the loop from `args`. */
    readonly exit: (args: ReadonlyArray<string>, state: string) => string;
    /** Goals (indices into `pending`) that show the body keeps the invariant. */
    readonly maintenance: ReadonlyArray<number>;
  }
  const loops = new Map<ts.WhileStatement, LoopInfo>();
  let loopCount = 0;
  /** The function unit whose body is being lowered, and the innermost unit (it or a loop). */
  let ownerUnit: number | undefined;
  let currentUnit: number | undefined;
  /**
   * The function being lowered and what its parameters are called at this point (its own
   * parameter names, or the matching parameters of the enclosing loop).
   */
  let ownerFn: { readonly fn: VerifiedFunction; readonly names: ReadonlyMap<string, string> } | undefined;

  const defineLoop = (stmt: ts.WhileStatement, env: Env): LoopInfo => {
    if (!ts.isBlock(stmt.statement)) throw new Error("A loop body must be a block");
    if (ownerUnit === undefined || currentUnit === undefined) {
      throw new Error("Loops are only supported in function bodies");
    }
    const owner = ownerUnit;
    const k = loopCount++;
    const line = getLocation(stmt.getSourceFile(), stmt).line;
    const local = isLocal(stmt.getSourceFile().fileName);

    const invariants: ts.Expression[] = [];
    const measureExprs: ts.Expression[] = [];
    let start = 0;
    for (const s of stmt.statement.statements) {
      const spec = loopSpecCall(s);
      if (!spec) break;
      if (spec.helper === "invariant") invariants.push(spec.args[0]!);
      else measureExprs.push(...spec.args);
      start++;
    }
    if (measureExprs.length === 0) throw new Error("A loop needs a `decreases(...)` measure");
    const rest = stmt.statement.statements.slice(start);

    // Parameters of the enclosing function never change, so its precondition holds throughout
    // the loop. It is added to the invariant for free, unless a local hides a parameter here.
    const owned = ownerFn;
    const ownerPre = owned ? preSmtNames.get(owned.fn.decl) : undefined;
    const inheritsPre =
      owned !== undefined &&
      ownerPre !== undefined &&
      owned.fn.params.every((p) => env.get(p.name) === owned.names.get(p.name));

    // The loop's parameters: every variable declared outside it that it mentions.
    const paramTypes = new Map<string, VType>();
    if (owned && inheritsPre) for (const p of owned.fn.params) paramTypes.set(p.name, p.type);
    const assigned = new Set<string>();
    const visit = (node: ts.Node): void => {
      if (ts.isIdentifier(node) && env.has(node.text)) {
        const sym = ts.isShorthandPropertyAssignment(node.parent)
          ? checker.getShorthandAssignmentValueSymbol(node.parent)
          : checker.getSymbolAtLocation(node);
        const decl = sym?.valueDeclaration;
        const isVariable =
          decl !== undefined &&
          (ts.isVariableDeclaration(decl) || ts.isParameter(decl) || ts.isBindingElement(decl));
        const declaredOutside = decl !== undefined && (decl.pos < stmt.pos || decl.end > stmt.end);
        if (sym && isVariable && declaredOutside) {
          if (!paramTypes.has(node.text)) {
            const res = resolveVType(checker, checker.getTypeOfSymbolAtLocation(sym, decl));
            if (!res.ok) throw new Error(`Loop variable \`${node.text}\`: ${res.reason}`);
            registry.register(res.type);
            paramTypes.set(node.text, res.type);
          }
          if (
            ts.isBinaryExpression(node.parent) &&
            node.parent.left === node &&
            ASSIGN_OPS.has(node.parent.operatorToken.kind)
          ) {
            assigned.add(node.text);
          }
        }
      }
      ts.forEachChild(node, visit);
    };
    visit(stmt);
    const params = [...paramTypes].map(([name, type]) => ({ name, type }));
    const paramNames = params.map((p, i) => smtIdent(`lp_${k}_${i}`, p.name));
    const paramsSmt = params.map((p, i) => `(${paramNames[i]!} ${registry.register(p.type)})`);
    const sorts = params.map((p) => registry.register(p.type));
    const loopEnv: Env = new Map(params.map((p, i) => [p.name, paramNames[i]!]));

    // The result: the assigned variables as one record (or `true` when there are none).
    const stateFields = params
      .filter((p) => assigned.has(p.name))
      .sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
    const stateType: VType | undefined =
      stateFields.length > 0 ? { kind: "record", fields: stateFields } : undefined;
    const stateDef = stateType ? registry.getRecord(stateType) : undefined;
    const stateSort = stateType ? registry.register(stateType) : "Bool";
    const modified = stateDef
      ? stateDef.fields.map((f) => ({ name: f.name, accessor: f.smtAccessor }))
      : [];
    const stateOf = (e: Env): string =>
      stateDef ? `(${stateDef.ctorName} ${stateDef.fields.map((f) => e.get(f.name)!).join(" ")})` : "true";

    const unit = units.length;
    units.push({ def: [], opaque: [], deps: new Set(), recursive: true });
    units[currentUnit]!.deps.add(unit);
    const fn = `loop_${k}`;
    const invName = invariants.length > 0 || inheritsPre ? `linv_${k}` : undefined;
    const condName = `lcond_${k}`;
    const measureNamesHere = measureExprs.map((_, j) => `lmes_${k}_${j}`);

    // Goals inside the loop are standalone: quantified over the loop's own variables, and
    // resting only on postconditions that lie strictly below the enclosing function, because
    // that function's termination may in turn rest on this loop.
    const below = (u: number): boolean => !reach(u).has(owner);
    const scope: FactScope = {
      allowed: (callee, j) =>
        below(unitOf.get(callee.decl)!) && [...postDefs.get(j)!.used].every(below),
      facts: [],
      posts: new Set(),
      goals: new Set(),
    };
    const saved = { frames: frames.splice(0), recursion, currentUnit, ownerFn };
    recursion = undefined;
    currentUnit = unit;
    if (owned && inheritsPre) ownerFn = { fn: owned.fn, names: loopEnv };
    const invTerms: string[] = [];
    let inherited: string | undefined;
    let condTerm = "";
    const measureTerms: string[] = [];
    let flow: Flow = { lets: [], env: loopEnv };
    let trace: Trace;
    try {
      trace = collecting(() =>
        withFacts(scope, () =>
          asExecutable(() => {
            const lowerRest = (i: number): void => {
              const inv = invariants[i];
              if (inv) {
                const term = lowerExpr(inv, loopEnv);
                invTerms.push(term);
                assuming(term, () => lowerRest(i + 1));
                return;
              }
              condTerm = lowerExpr(stmt.expression, loopEnv);
              assuming(condTerm, () => {
                for (const m of measureExprs) measureTerms.push(lowerExpr(m, loopEnv));
                flow = collectBlock(rest, loopEnv);
              });
            };
            if (owned && inheritsPre) {
              // The precondition is written out again over the loop's variables (its
              // definition belongs to the function, which is defined after its loops). The
              // calls inside it were already justified where the function states it.
              const inner = collecting(() => {
                const terms = owned.fn.requires.map((r) => lowerExpr(r, loopEnv));
                inherited = terms.length === 1 ? terms[0]! : `(and ${terms.join(" ")})`;
              });
              for (const u of inner.used) used.add(u);
            }
            if (inherited) {
              invTerms.push(inherited);
              assuming(inherited, () => lowerRest(0));
            } else {
              lowerRest(0);
            }
          }),
        ),
      );
    } finally {
      frames.push(...saved.frames);
      recursion = saved.recursion;
      currentUnit = saved.currentUnit;
      ownerFn = saved.ownerFn;
    }
    for (const u of trace.used) if (u !== unit) units[unit]!.deps.add(u);

    const specDefs: string[] = [];
    if (invName) {
      specDefs.push(
        `(define-fun ${invName} (${paramsSmt.join(" ")}) Bool\n  (and true ${invTerms.join(" ")}))`,
      );
    }
    specDefs.push(`(define-fun ${condName} (${paramsSmt.join(" ")}) Bool\n  ${condTerm})`);
    measureTerms.forEach((m, j) => {
      specDefs.push(`(define-fun ${measureNamesHere[j]!} (${paramsSmt.join(" ")}) Int\n  ${m})`);
    });
    const invHere = invName ? app(invName, paramNames) : undefined;
    const condHere = app(condName, paramNames);
    const nextArgs = params.map((p) => flow.env.get(p.name)!);
    let body = `(ite ${condHere}\n       ${wrapLets(flow.lets, app(fn, nextArgs))}\n       ${stateOf(loopEnv)})`;
    const u = units[unit]!;
    u.def.push(...specDefs);
    if (invHere) {
      const undef = `lundef_${k}`;
      u.def.push(`(declare-fun ${undef} (${sorts.join(" ")}) ${stateSort})`);
      body = `(ite ${invHere}\n  ${body}\n  ${app(undef, paramNames)})`;
    }
    u.def.push(`(define-funs-rec ((${fn} (${paramsSmt.join(" ")}) ${stateSort}))\n  (${body}))`);
    u.opaque.push(...specDefs, `(declare-fun ${fn} (${sorts.join(" ")}) ${stateSort})`);

    const argNames = params.map((p, i) => ({ tsName: p.name, smtName: paramNames[i]!, type: p.type }));
    const afterBody = (claim: string): string =>
      `(=> (and true ${invHere ?? ""} ${condHere}) ${wrapLets(flow.lets, claim)})`;
    const location = getLocation(stmt.getSourceFile(), stmt);
    const common = {
      argNames,
      defs: [],
      assumptions: scope.facts,
      roots: new Set([unit]),
      posts: scope.posts,
      factGoals: scope.goals,
      opaque: unit,
      ...(scope.facts.length > 0 ? { plain: { defs: [], assumptions: [] } } : {}),
      local,
    };
    // With no invariant written, the only invariant is the inherited precondition, which is
    // kept by construction: nothing assigns to parameters.
    const maintenance: number[] = [];
    if (invName && invariants.length > 0) {
      maintenance.push(pending.length);
      addCheck(unit, pending.length);
      pending.push({
        ...common,
        kind: "invariant",
        goal: { name: `invariant of the loop at line ${line}: kept by the body`, params, location },
        claim: afterBody(app(invName, nextArgs)),
      });
    }
    terminationGoals.set(unit, [pending.length]);
    pending.push({
      ...common,
      kind: "decreases",
      goal: { name: `termination of the loop at line ${line}`, params, location },
      claim: afterBody(
        lexLess(
          measureNamesHere.map((m) => app(m, nextArgs)),
          measureNamesHere.map((m) => app(m, paramNames)),
        ),
      ),
    });
    for (const ob of mergeObligations(trace.obligations)) {
      addCheck(unit, pending.length);
      pending.push({ ...common, kind: ob.kind, goal: obligationGoal(ob, params), claim: ob.formula });
    }

    const info: LoopInfo = {
      unit,
      fn,
      params,
      inv: invName,
      checkEntry: invariants.length > 0,
      modified,
      exit: (args, state) => {
        const tmp = nextVar("exit");
        const final = params.map((p, i) => {
          const m = modified.find((x) => x.name === p.name);
          return m ? `(${m.accessor} ${tmp})` : args[i]!;
        });
        return `(let ((${tmp} ${state})) (and ${invName ? app(invName, final) : "true"} (not ${app(condName, final)})))`;
      },
      maintenance,
    };
    loops.set(stmt, info);
    return info;
  };

  const lowerLoop = (stmt: ts.WhileStatement, env: Env): Flow => {
    const info = loops.get(stmt) ?? defineLoop(stmt, env);
    const args = info.params.map((p) => {
      const bound = env.get(p.name);
      if (!bound) throw new Error(`Unbound loop variable \`${p.name}\``);
      return bound;
    });
    used.add(info.unit);
    const invHere = info.inv ? app(info.inv, args) : undefined;
    if (invHere && info.checkEntry) {
      sink.push({ kind: "invariant", callee: "", node: stmt, formula: closeOver(invHere) });
    }
    const call = app(info.fn, args);
    if (factScope) {
      const exit = info.exit(args, call);
      const fact = closeOver(invHere ? `(=> ${invHere} ${exit})` : exit);
      for (const scope of [factScope, factScope.strict]) {
        if (!scope) continue;
        scope.facts.push(fact);
        for (const g of info.maintenance) scope.goals.add(g);
      }
    }
    const state = nextVar("loop");
    const out = new Map(env);
    for (const m of info.modified) out.set(m.name, `(${m.accessor} ${state})`);
    return { lets: [{ kind: "let", v: state, init: call }], env: out };
  };

  /** Lower a statement that cannot `return`. */
  const collect = (stmt: ts.Statement, env: Env): Flow => {
    if (ts.isVariableStatement(stmt)) {
      const lets: LetFrame[] = [];
      let cur = env;
      const bind = (frame: LetFrame): void => {
        lets.push(frame);
        frames.push(frame);
      };
      try {
        for (const decl of stmt.declarationList.declarations) {
          if (!decl.initializer) throw new Error("Missing initializer");
          if (ts.isIdentifier(decl.name)) {
            // An annotated binding (`const a: Narrow = wide`) has the declared type, not the
            // initializer's.
            const init = lowerExpr(decl.initializer, cur, resolveExprVType(decl.name));
            const v = nextVar(decl.name.text);
            cur = new Map(cur).set(decl.name.text, v);
            bind({ kind: "let", v, init });
          } else if (ts.isObjectBindingPattern(decl.name)) {
            const init = lowerExpr(decl.initializer, cur);
            const recDef = registry.getRecord(resolveExprVType(decl.initializer));
            const tmp = nextVar("rec");
            const next = new Map(cur);
            for (const el of decl.name.elements) {
              if (!ts.isIdentifier(el.name)) continue;
              const propName =
                el.propertyName && ts.isIdentifier(el.propertyName)
                  ? el.propertyName.text
                  : el.name.text;
              const field = recDef.fields.find((f) => f.name === propName);
              if (!field) throw new Error(`Missing destructured field ${propName}`);
              next.set(el.name.text, `(${field.smtAccessor} ${tmp})`);
            }
            cur = next;
            bind({ kind: "let", v: tmp, init });
          } else {
            throw new Error("Unsupported declaration binding");
          }
        }
      } finally {
        frames.length -= lets.length;
      }
      return { lets, env: cur };
    }

    if (
      ts.isExpressionStatement(stmt) &&
      ts.isBinaryExpression(stmt.expression) &&
      ts.isIdentifier(stmt.expression.left) &&
      ASSIGN_OPS.has(stmt.expression.operatorToken.kind)
    ) {
      const { left, right, operatorToken } = stmt.expression;
      const old = env.get(left.text);
      if (!old) throw new Error(`Assignment to unbound variable \`${left.text}\``);
      const value = lowerExpr(right, env, resolveExprVType(left));
      const op = ASSIGN_OPS.get(operatorToken.kind);
      const v = nextVar(left.text);
      return {
        lets: [{ kind: "let", v, init: op ? `(${op} ${old} ${value})` : value }],
        env: new Map(env).set(left.text, v),
      };
    }

    if (ts.isIfStatement(stmt)) {
      const c = lowerExpr(stmt.expression, env);
      const thenFlow = assuming(c, () => collectBlock(branchStatements(stmt.thenStatement), env));
      const elseStmt = stmt.elseStatement;
      const elseFlow: Flow = elseStmt
        ? assuming(`(not ${c})`, () => collectBlock(branchStatements(elseStmt), env))
        : { lets: [], env };
      // The branches' bindings are hoisted in front (their values are only used under the
      // matching condition), followed by one `ite` per variable the branches disagree on.
      const lets = [...thenFlow.lets, ...elseFlow.lets];
      const out = new Map(env);
      for (const name of env.keys()) {
        const a = thenFlow.env.get(name)!;
        const b = elseFlow.env.get(name)!;
        if (a === b) {
          out.set(name, a);
          continue;
        }
        const v = nextVar(name);
        lets.push({ kind: "let", v, init: `(ite ${c} ${a} ${b})` });
        out.set(name, v);
      }
      return { lets, env: out };
    }

    if (ts.isWhileStatement(stmt)) return lowerLoop(stmt, env);
    if (ts.isBlock(stmt)) return collectBlock(stmt.statements, env);

    throw new Error(`Unsupported statement in SMT lowering: ${ts.SyntaxKind[stmt.kind]}`);
  };

  /** Lower a block that cannot `return`; its own declarations go out of scope at the end. */
  const collectBlock = (stmts: ReadonlyArray<ts.Statement>, env: Env): Flow => {
    const lets: LetFrame[] = [];
    let cur = env;
    try {
      for (const stmt of stmts) {
        const flow = collect(stmt, cur);
        lets.push(...flow.lets);
        frames.push(...flow.lets);
        cur = flow.env;
      }
    } finally {
      frames.length -= lets.length;
    }
    return { lets, env: leaveScope(env, cur, declaredNames(stmts)) };
  };

  /**
   * Lower statements `idx..` of a block to the value the enclosing function returns. `after`
   * continues with whatever follows the block when control falls off its end.
   */
  const lowerSeq = (
    stmts: ReadonlyArray<ts.Statement>,
    idx: number,
    env: Env,
    ret: VType,
    after: (env: Env) => string,
  ): string => {
    const stmt = stmts[idx];
    if (!stmt) return after(env);

    if (ts.isReturnStatement(stmt)) {
      if (!stmt.expression) throw new Error("Bare return in SMT lowering");
      return lowerExpr(stmt.expression, env, ret);
    }

    if (!containsReturn(stmt)) {
      const flow = collect(stmt, env);
      const rest = withFrames(flow.lets, () => lowerSeq(stmts, idx + 1, flow.env, ret, after));
      return wrapLets(flow.lets, rest);
    }

    if (ts.isIfStatement(stmt)) {
      const condSmt = lowerExpr(stmt.expression, env);
      const rest = (e: Env): string => lowerSeq(stmts, idx + 1, e, ret, after);
      const lowerBranch = (branch: ts.Statement): string => {
        const inner = branchStatements(branch);
        return lowerSeq(inner, 0, env, ret, (e) => rest(leaveScope(env, e, declaredNames(inner))));
      };
      const thenSmt = assuming(condSmt, () => lowerBranch(stmt.thenStatement));
      const elseStmt = stmt.elseStatement;
      const elseSmt = assuming(`(not ${condSmt})`, () => (elseStmt ? lowerBranch(elseStmt) : rest(env)));
      return `(ite ${condSmt} ${thenSmt} ${elseSmt})`;
    }

    throw new Error(`Unsupported statement in SMT lowering: ${ts.SyntaxKind[stmt.kind]}`);
  };

  const lowerBody = (
    body: ts.Block | ts.Expression,
    env: Env,
    ret: VType,
    /** Leading `requires(...)` / `decreases(...)` statements to skip. */
    skip = 0,
  ): string => {
    if (ts.isBlock(body)) {
      return lowerSeq(body.statements, skip, env, ret, () => {
        throw new Error("Control reached end of block without return during SMT lowering");
      });
    }
    return lowerExpr(body, env, ret);
  };

  // Postconditions of recursive functions, as predicates over the arguments and the result.
  ensures.forEach((e, j) => {
    const fn = fnByDecl.get(e.fn);
    if (!fn) throw new Error(`\`ensures\` refers to unknown function \`${e.fnName}\``);
    if (e.params.length !== fn.params.length + 1) {
      throw new Error(`Postcondition of \`${e.fnName}\` has the wrong number of parameters`);
    }
    if (!fn.recursive && !fn.hasLoops) return;
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
    const below = (u: number): boolean => !reach(u).has(unit);
    const scope = {
      allowed: () => true,
      facts: [] as string[],
      posts: new Set<number>(),
      goals: new Set<number>(),
      strict: {
        allowed: (callee: VerifiedFunction, j: number) =>
          below(unitOf.get(callee.decl)!) && [...postDefs.get(j)!.used].every(below),
        facts: [] as string[],
        posts: new Set<number>(),
        goals: new Set<number>(),
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
      ownerUnit = unit;
      currentUnit = unit;
      ownerFn = { fn, names: new Map(env) };
      try {
        withFacts(scope, () => asExecutable(() => lowerRest(0)));
      } finally {
        ownerUnit = undefined;
        currentUnit = undefined;
        ownerFn = undefined;
      }
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
    for (const ob of mergeObligations(trace.obligations)) {
      // Goals of imported modules are emitted too, but kept only if a verdict in this file
      // rests on them.
      const name = `ob_${obligationId++}`;
      const definitional = ob.kind === "decreases";
      if (!definitional) addCheck(unit, pending.length);
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
        roots: new Set([unit]),
        posts: known.posts,
        factGoals: known.goals,
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
    const scope: FactScope = { allowed: () => true, facts: [], posts: new Set(), goals: new Set() };
    let bodySmt = "";
    const trace = collecting(() => {
      bodySmt = withFacts(scope, () => lowerBody(l.body, env, { kind: "boolean" }));
    });
    const local = isLocal(l.location.file);
    const plain = scope.facts.length > 0 ? { plain: { defs: [], assumptions: [] } } : {};
    const own: number[] = [];
    for (const ob of mergeObligations(trace.obligations)) {
      own.push(pending.length);
      pending.push({
        kind: ob.kind,
        goal: obligationGoal(ob, l.params),
        argNames,
        defs: [],
        assumptions: scope.facts,
        claim: ob.formula,
        roots: trace.used,
        posts: scope.posts,
        factGoals: scope.goals,
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
      factGoals: scope.goals,
      ...plain,
      own,
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
    const scope: FactScope = { allowed: () => true, facts: [], posts: new Set(), goals: new Set() };
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
    // hypothesis applies to them. Only postconditions of functions strictly below this one
    // (it can reach them, they cannot reach it) may be assumed there. "Cannot reach it" alone
    // is not enough: two unrelated functions could then each have a false postcondition about
    // the other, and each proof would assume the other's claim.
    const reachable = reach(unit);
    scope.allowed = (callee) => {
      const u = unitOf.get(callee.decl)!;
      return reachable.has(u) && !reach(u).has(unit);
    };
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
    const roots = new Set([unit, ...bodyTrace.used, ...postTrace.used]);
    const plain =
      scope.facts.length > 0
        ? { plain: { defs: [], assumptions: preTerm ? [preTerm] : [] } }
        : {};
    const own: number[] = [];
    for (const ob of mergeObligations(postTrace.obligations)) {
      own.push(pending.length);
      pending.push({
        kind: ob.kind,
        goal: obligationGoal(ob, params),
        argNames,
        defs: [],
        assumptions: scope.facts,
        claim: ob.formula,
        roots,
        posts: scope.posts,
        factGoals: scope.goals,
        ...plain,
        local,
      });
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
      factGoals: scope.goals,
      ...plain,
      own,
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
    withFacts_: boolean,
    abstract = false,
  ): { script: string; deps: Set<number>; hard: Set<number> } => {
    // Definitions in dependency order: everything a unit mentions comes before it.
    const order: number[] = [];
    const seen = new Set<number>();
    const include = (u: number): void => {
      if (seen.has(u)) return;
      seen.add(u);
      for (const d of [...units[u]!.deps].sort((a, b) => a - b)) include(d);
      order.push(u);
    };
    const roots = new Set(p.roots);
    for (const j of posts) for (const u of postDefs.get(j)!.used) roots.add(u);
    for (const u of [...roots].sort((a, b) => a - b)) include(u);

    const fnDefs: string[] = [];
    const hard = new Set<number>();
    const runs = p.kind === "law" || p.kind === "ensures";
    if (runs) for (const g of p.own ?? []) hard.add(g);
    for (const u of order) {
      if (runs) for (const g of unitChecks.get(u) ?? []) hard.add(g);
      if (u === p.opaque) {
        fnDefs.push(...units[u]!.opaque);
        continue;
      }
      // Even when a recursive function or loop is left undefined, what is assumed about it
      // (its postcondition, its invariant and negated condition after it) presumes that it
      // returns. `while (true)` "establishes" `false` afterwards, so termination is always
      // a dependency.
      if (units[u]!.recursive) for (const g of terminationGoals.get(u) ?? []) hard.add(g);
      fnDefs.push(...(abstract && units[u]!.recursive ? units[u]!.opaque : units[u]!.def));
    }
    const deps = new Set(hard);
    for (const j of posts) deps.add(ensuresGoals.get(j)!);
    if (withFacts_) for (const g of p.factGoals) deps.add(g);

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
    return { script: lines.join("\n") + "\n", deps, hard };
  };
  const assembled = pending.map((p) => ({
    pending: p,
    ...assemble(p, p.defs, p.assumptions, p.posts, true),
    plain: p.plain ? assemble(p, p.plain.defs, p.plain.assumptions, new Set(), false) : undefined,
    abstract: p.plain ? assemble(p, p.defs, p.assumptions, p.posts, true, true) : undefined,
  }));

  // Keep this file's goals and everything they rely on.
  const keep = new Set<number>();
  const visit = (i: number): void => {
    if (keep.has(i)) return;
    keep.add(i);
    for (const d of assembled[i]!.deps) visit(d);
    for (const d of assembled[i]!.abstract?.deps ?? []) visit(d);
  };
  assembled.forEach((a, i) => {
    if (a.pending.local) visit(i);
  });
  const kept = [...keep].sort((a, b) => a - b);
  const newIndex = new Map(kept.map((old, i) => [old, i]));
  const remap = (deps: ReadonlySet<number>): number[] =>
    [...deps].map((d) => newIndex.get(d)!).sort((a, b) => a - b);

  return kept.map((old) => {
    const { pending: p, script, deps, hard, plain, abstract } = assembled[old]!;
    return {
      kind: p.kind,
      law: p.goal,
      smtScript: script,
      paramSmtNames: p.argNames,
      recordsByCtor,
      dependsOn: remap(deps),
      foundations: remap(hard),
      ...(plain ? { plain: { smtScript: plain.script, dependsOn: remap(plain.deps) } } : {}),
      ...(abstract
        ? { abstract: { smtScript: abstract.script, dependsOn: remap(abstract.deps) } }
        : {}),
    };
  });
}
