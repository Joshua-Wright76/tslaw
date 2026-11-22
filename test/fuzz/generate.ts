/**
 * Random program generator for the verified subset.
 *
 * Produces well-typed `"use verified";` modules that exercise every construct the SMT
 * translation supports: bigint/boolean arithmetic and logic, records (including passing a
 * wider record where a narrower one is expected), `const` and destructuring, guard clauses,
 * `if`/`else`, ternaries, `implies`, and calls between functions.
 *
 * `test/fuzz.test.ts` runs each generated function on concrete inputs in real JavaScript and
 * then requires the prover to agree with the result.
 */

export type TypeName = "bigint" | "boolean" | "N" | "W" | "O";

export const TYPE_DECLS = `export type N = { readonly a: bigint };
export type W = { readonly a: bigint; readonly b: boolean };
export type O = { readonly n: N; readonly w: W; readonly k: bigint };
`;

const ALL_TYPES: TypeName[] = ["bigint", "boolean", "N", "W", "O"];

export interface Param {
  readonly name: string;
  readonly type: TypeName;
}

export interface GenFunction {
  readonly name: string;
  readonly params: ReadonlyArray<Param>;
  readonly ret: TypeName;
  readonly source: string;
}

export type Rng = () => number;

/** Deterministic PRNG (mulberry32). */
export function makeRng(seed: number): Rng {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

const pick = <T>(rng: Rng, xs: ReadonlyArray<T>): T => xs[Math.floor(rng() * xs.length)]!;

interface Ctx {
  readonly rng: Rng;
  readonly env: Param[];
  readonly fns: ReadonlyArray<GenFunction>;
}

function bigintLiteral(rng: Rng): string {
  const r = rng();
  if (r < 0.55) return `${Math.floor(rng() * 7)}n`;
  if (r < 0.75) return `${Math.floor(rng() * 1000)}n`;
  if (r < 0.85) return `0x${Math.floor(rng() * 4096).toString(16)}n`;
  if (r < 0.95) return `${Math.floor(rng() * 1e9)}_${String(Math.floor(rng() * 1000)).padStart(3, "0")}n`;
  return `${BigInt(Math.floor(rng() * 1e15)) * 10n ** 12n}n`;
}

/** Expressions of the given type that are a variable or a field path on a variable. */
function atoms(ctx: Ctx, type: TypeName): string[] {
  const out: string[] = [];
  for (const v of ctx.env) {
    if (v.type === type) out.push(v.name);
    if (type === "bigint") {
      if (v.type === "N" || v.type === "W") out.push(`${v.name}.a`);
      if (v.type === "O") out.push(`${v.name}.k`, `${v.name}.n.a`, `${v.name}.w.a`);
    }
    if (type === "boolean") {
      if (v.type === "W") out.push(`${v.name}.b`);
      if (v.type === "O") out.push(`${v.name}.w.b`);
    }
    // A wider record is accepted wherever the narrower one is expected.
    if (type === "N") {
      if (v.type === "W") out.push(v.name);
      if (v.type === "O") out.push(`${v.name}.n`, `${v.name}.w`);
    }
    if (type === "W" && v.type === "O") out.push(`${v.name}.w`);
  }
  return out;
}

function call(ctx: Ctx, type: TypeName, depth: number): string | undefined {
  const candidates = ctx.fns.filter((f) => f.ret === type || (type === "N" && f.ret === "W"));
  if (candidates.length === 0) return undefined;
  const f = pick(ctx.rng, candidates);
  return `${f.name}(${f.params.map((p) => expr(ctx, p.type, depth - 1)).join(", ")})`;
}

/** A bigint comparison: always of type `boolean`, never a narrowed literal type. */
function comparison(ctx: Ctx, depth: number): string {
  const op = pick(ctx.rng, ["<", "<=", ">", ">=", "===", "!=="]);
  // `===` between two literal types is a TypeScript error, so the left side is never a literal.
  const left = op === "===" || op === "!==" ? expr(ctx, "bigint", depth - 1, true) : expr(ctx, "bigint", depth - 1);
  return `(${left} ${op} ${expr(ctx, "bigint", depth - 1)})`;
}

/**
 * Generate an expression of `type`. Record-typed expressions are only ever requested in
 * positions with an expected type (arguments, returns, annotated consts, literal fields),
 * which is where TypeScript allows a wider record.
 */
export function expr(ctx: Ctx, type: TypeName, depth: number, noLiteral = false): string {
  const { rng } = ctx;
  const leafs = atoms(ctx, type);
  const leaf = (): string => {
    if (leafs.length > 0 && (noLiteral || rng() < 0.7)) return pick(rng, leafs);
    switch (type) {
      case "bigint":
        return noLiteral ? `(${bigintLiteral(rng)} + ${bigintLiteral(rng)})` : bigintLiteral(rng);
      case "boolean":
        return noLiteral ? `(${bigintLiteral(rng)} < ${bigintLiteral(rng)})` : pick(rng, ["true", "false"]);
      case "N":
        return `{ a: ${expr(ctx, "bigint", 0)} }`;
      case "W":
        return `{ a: ${expr(ctx, "bigint", 0)}, b: ${expr(ctx, "boolean", 0)} }`;
      case "O":
        return `{ n: ${expr(ctx, "N", 0)}, w: ${expr(ctx, "W", 0)}, k: ${expr(ctx, "bigint", 0)} }`;
    }
  };
  if (depth <= 0) return leaf();

  const r = rng();
  if (r < 0.2) return leaf();
  if (r < 0.32) {
    const c = call(ctx, type, depth);
    if (c) return c;
  }
  if (r < 0.45) {
    return `(${expr(ctx, "boolean", depth - 1)} ? ${expr(ctx, type, depth - 1, noLiteral)} : ${expr(ctx, type, depth - 1, noLiteral)})`;
  }
  switch (type) {
    case "bigint": {
      if (r < 0.55 && !noLiteral) return `(-(${expr(ctx, "bigint", depth - 1)}))`;
      const op = pick(rng, ["+", "+", "-", "-", "*"]);
      return `(${expr(ctx, "bigint", depth - 1)} ${op} ${expr(ctx, "bigint", depth - 1)})`;
    }
    case "boolean": {
      if (r < 0.62) return comparison(ctx, depth);
      if (r < 0.7) return `(!${expr(ctx, "boolean", depth - 1)})`;
      if (r < 0.8) return `implies(${expr(ctx, "boolean", depth - 1)}, ${expr(ctx, "boolean", depth - 1)})`;
      if (r < 0.87) {
        // Boolean equality: the left side is a comparison so it can never be a narrowed literal.
        return `(${comparison(ctx, depth - 1)} ${pick(rng, ["===", "!=="])} ${expr(ctx, "boolean", depth - 1)})`;
      }
      return `(${expr(ctx, "boolean", depth - 1)} ${pick(rng, ["&&", "||"])} ${expr(ctx, "boolean", depth - 1)})`;
    }
    case "N":
      return `{ a: ${expr(ctx, "bigint", depth - 1)} }`;
    case "W":
      return `{ a: ${expr(ctx, "bigint", depth - 1)}, b: ${expr(ctx, "boolean", depth - 1)} }`;
    case "O":
      return `{ n: ${expr(ctx, "N", depth - 1)}, w: ${expr(ctx, "W", depth - 1)}, k: ${expr(ctx, "bigint", depth - 1)} }`;
  }
}

function block(ctx: Ctx, ret: TypeName, depth: number, indent: string, fresh: { n: number }): string {
  const { rng } = ctx;
  const env = [...ctx.env];
  const inner: Ctx = { rng, env, fns: ctx.fns };
  const lines: string[] = [];

  const decls = Math.floor(rng() * 3);
  for (let i = 0; i < decls; i++) {
    const records = env.filter((v) => v.type === "W" || v.type === "O");
    if (records.length > 0 && rng() < 0.3) {
      const v = pick(rng, records);
      const x = `d${fresh.n++}`;
      const y = `d${fresh.n++}`;
      if (v.type === "W") {
        lines.push(`${indent}const { a: ${x}, b: ${y} } = ${v.name};`);
        env.push({ name: x, type: "bigint" }, { name: y, type: "boolean" });
      } else {
        lines.push(`${indent}const { n: ${x}, k: ${y} } = ${v.name};`);
        env.push({ name: x, type: "N" }, { name: y, type: "bigint" });
      }
      continue;
    }
    const type = pick(rng, ALL_TYPES);
    const name = `c${fresh.n++}`;
    lines.push(`${indent}const ${name}: ${type} = ${expr(inner, type, depth)};`);
    env.push({ name, type });
  }

  const r = rng();
  if (depth > 0 && r < 0.3) {
    // Guard clause, then fall through.
    lines.push(`${indent}if ${comparison(inner, depth)} return ${expr(inner, ret, depth)};`);
    lines.push(`${indent}return ${expr(inner, ret, depth)};`);
  } else if (depth > 0 && r < 0.55) {
    lines.push(`${indent}if ${comparison(inner, depth)} {`);
    lines.push(block(inner, ret, depth - 1, indent + "  ", fresh));
    lines.push(`${indent}} else {`);
    lines.push(block(inner, ret, depth - 1, indent + "  ", fresh));
    lines.push(`${indent}}`);
  } else if (depth > 0 && r < 0.65) {
    lines.push(`${indent}if ${comparison(inner, depth)} {`);
    lines.push(block(inner, ret, depth - 1, indent + "  ", fresh));
    lines.push(`${indent}} else if ${comparison(inner, depth)} return ${expr(inner, ret, depth)};`);
    lines.push(`${indent}else return ${expr(inner, ret, depth)};`);
  } else {
    lines.push(`${indent}return ${expr(inner, ret, depth)};`);
  }
  return lines.join("\n");
}

export function generateFunctions(seed: number, count: number, prefix: string): GenFunction[] {
  const rng = makeRng(seed);
  const fns: GenFunction[] = [];
  for (let i = 0; i < count; i++) {
    const name = `${prefix}${i}`;
    const params: Param[] = [];
    const arity = Math.floor(rng() * 4) + (rng() < 0.9 ? 1 : 0);
    for (let p = 0; p < arity; p++) params.push({ name: `p${p}`, type: pick(rng, ALL_TYPES) });
    const ret = pick(rng, ALL_TYPES);
    const body = block({ rng, env: [...params], fns }, ret, 3, "  ", { n: 0 });
    const sig = params.map((p) => `${p.name}: ${p.type}`).join(", ");
    fns.push({ name, params, ret, source: `export function ${name}(${sig}): ${ret} {\n${body}\n}` });
  }
  return fns;
}

// ---------------------------------------------------------------------------
// Concrete values
// ---------------------------------------------------------------------------

export type Value = bigint | boolean | { readonly [k: string]: Value };

export function randomValue(rng: Rng, type: TypeName): Value {
  switch (type) {
    case "bigint": {
      const span = (n: number): bigint => BigInt(Math.floor(rng() * (2 * n + 1)) - n);
      const r = rng();
      if (r < 0.5) return span(4);
      if (r < 0.85) return span(1000);
      return span(1_000_000) * 2n ** 70n + span(1000);
    }
    case "boolean":
      return rng() < 0.5;
    case "N":
      return { a: randomValue(rng, "bigint") };
    case "W":
      return { a: randomValue(rng, "bigint"), b: randomValue(rng, "boolean") };
    case "O":
      return { n: randomValue(rng, "N"), w: randomValue(rng, "W"), k: randomValue(rng, "bigint") };
  }
}

export function valueToTs(v: Value): string {
  if (typeof v === "bigint") return `${v}n`;
  if (typeof v === "boolean") return String(v);
  return `{ ${Object.entries(v).map(([k, x]) => `${k}: ${valueToTs(x)}`).join(", ")} }`;
}

/** Field paths to every primitive inside a value of `type` (`""` for a primitive itself). */
export function leafPaths(type: TypeName): string[] {
  switch (type) {
    case "bigint":
    case "boolean":
      return [""];
    case "N":
      return [".a"];
    case "W":
      return [".a", ".b"];
    case "O":
      return [".n.a", ".w.a", ".w.b", ".k"];
  }
}

export function readPath(v: Value, path: string): bigint | boolean {
  let cur: Value = v;
  for (const key of path.split(".").filter(Boolean)) {
    if (typeof cur !== "object") throw new Error(`bad path ${path}`);
    cur = cur[key]!;
  }
  if (typeof cur === "object") throw new Error(`path ${path} is not a leaf`);
  return cur;
}
