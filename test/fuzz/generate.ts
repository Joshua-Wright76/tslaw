/**
 * Random program generator for the verified subset.
 *
 * Produces well-typed `"use verified";` modules that exercise every construct the SMT
 * translation supports: bigint/boolean arithmetic and logic, records (including passing a
 * wider record where a narrower one is expected), `const` and destructuring, guard clauses,
 * `if`/`else`, ternaries, `implies`, calls between functions, recursion, and `let` variables
 * with assignments and `while` loops, and arrays.
 *
 * `test/fuzz.test.ts` runs each generated function on concrete inputs in real JavaScript and
 * then requires the prover to agree with the result.
 */

export type TypeName = "bigint" | "boolean" | "N" | "W" | "O" | "A" | "AN";

export const TYPE_DECLS = `export type N = { readonly a: bigint };
export type W = { readonly a: bigint; readonly b: boolean };
export type O = { readonly n: N; readonly w: W; readonly k: bigint };
export type A = readonly bigint[];
export type AN = readonly N[];
`;

const ALL_TYPES: TypeName[] = ["bigint", "boolean", "N", "W", "O", "A", "AN"];

export interface Param {
  readonly name: string;
  readonly type: TypeName;
}

export interface GenFunction {
  readonly name: string;
  readonly params: ReadonlyArray<Param>;
  readonly ret: TypeName;
  readonly source: string;
  /** Recursive on its first parameter, which is worth testing with small values. */
  readonly recursive?: boolean;
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
    // Array reads are always guarded, so every index is provably in range.
    if (type === "bigint") {
      // `len(x) < (...)` would be parsed as the start of a type-argument list.
      if (v.type === "A") out.push(`(len(${v.name}))`, `(len(${v.name}) > 1n ? at(${v.name}, 1n) : 7n)`);
      if (v.type === "AN") out.push(`(len(${v.name}))`, `(len(${v.name}) > 0n ? at(${v.name}, 0n).a : 3n)`);
    }
    if (type === "N" && v.type === "AN") out.push(`(len(${v.name}) > 1n ? at(${v.name}, 1n) : { a: 1n })`);
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
  const right = expr(ctx, "bigint", depth - 1);
  // TypeScript reads `a < (1n > (b) ...` as the start of a generic call `a<...>(b)`, so a
  // `<` whose right side contains a `>` is written the other way round.
  if ((op === "<" || op === "<=") && right.includes(">")) {
    return `(${right} ${op === "<" ? ">" : ">="} ${left})`;
  }
  return `(${left} ${op} ${right})`;
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
      case "A":
        return `[${Array.from({ length: Math.floor(rng() * 3) }, () => expr(ctx, "bigint", 0)).join(", ")}]`;
      case "AN":
        return `[${Array.from({ length: Math.floor(rng() * 3) }, () => expr(ctx, "N", 0)).join(", ")}]`;
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
    case "A":
    case "AN": {
      // The array a helper works on is always a variable, so its element type is known.
      const vars = ctx.env.filter((v) => v.type === type).map((v) => v.name);
      if (vars.length === 0) return leaf();
      const xs = pick(rng, vars);
      const element = type === "A" ? "bigint" : "N";
      if (r < 0.6) return `append(${xs}, ${expr(ctx, element, depth - 1)})`;
      if (r < 0.75) return `concat(${xs}, ${expr(ctx, type, depth - 1)})`;
      if (r < 0.88) return `(len(${xs}) >= 2n ? slice(${xs}, 1n, len(${xs})) : ${xs})`;
      return `(len(${xs}) > 0n ? withAt(${xs}, len(${xs}) - 1n, ${expr(ctx, element, depth - 1)}) : ${xs})`;
    }
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

/**
 * A function that calls itself on `p0 - 1n`. Outside `1n..5n` it returns without recursing, so
 * any argument is safe to run in JavaScript and other functions may call it freely.
 */
function recursiveFunction(rng: Rng, name: string, fns: ReadonlyArray<GenFunction>): GenFunction {
  const params: Param[] = [{ name: "p0", type: "bigint" }];
  const extra = Math.floor(rng() * 3);
  for (let p = 1; p <= extra; p++) params.push({ name: `p${p}`, type: pick(rng, ALL_TYPES) });
  const ret = pick(rng, ALL_TYPES);
  const ctx: Ctx = { rng, env: [...params], fns };
  const base = expr(ctx, ret, 2);
  const recArgs = params.slice(1).map((p) => `, ${expr(ctx, p.type, 1)}`);
  const rest = block({ rng, env: [...params, { name: "rec", type: ret }], fns }, ret, 2, "  ", { n: 0 });
  const sig = params.map((p) => `${p.name}: ${p.type}`).join(", ");
  const source = [
    `export function ${name}(${sig}): ${ret} {`,
    `  decreases(p0);`,
    `  if (p0 <= 0n || p0 > 5n) return ${base};`,
    `  const rec: ${ret} = ${name}(p0 - 1n${recArgs.join("")});`,
    rest,
    `}`,
  ].join("\n");
  return { name, params, ret, source, recursive: true };
}

/** An assignment to `target`, plain or under an `if` (with or without `else`). */
function assignment(ctx: Ctx, target: Param, indent: string): string[] {
  const { rng } = ctx;
  const value = (): string => expr(ctx, target.type, 2);
  const r = rng();
  if (r < 0.4) return [`${indent}${target.name} = ${value()};`];
  if (r < 0.6) return [`${indent}if ${comparison(ctx, 1)} ${target.name} = ${value()};`];
  if (r < 0.8) {
    return [
      `${indent}if ${comparison(ctx, 1)} {`,
      `${indent}  ${target.name} = ${value()};`,
      `${indent}} else {`,
      `${indent}  ${target.name} = ${value()};`,
      `${indent}}`,
    ];
  }
  // A nested `if` where only the inner branch assigns.
  return [
    `${indent}if ${comparison(ctx, 1)} {`,
    `${indent}  const t: ${target.type} = ${value()};`,
    `${indent}  if ${comparison(ctx, 1)} ${target.name} = t;`,
    `${indent}}`,
  ];
}

/**
 * A function with `let` variables, assignments and a `while` loop that runs at most four
 * times, so any argument is safe to run in JavaScript.
 */
function loopFunction(rng: Rng, name: string, fns: ReadonlyArray<GenFunction>): GenFunction {
  const params: Param[] = [{ name: "p0", type: "bigint" }];
  const extra = Math.floor(rng() * 3);
  for (let p = 1; p <= extra; p++) params.push({ name: `p${p}`, type: pick(rng, ALL_TYPES) });
  const ret = pick(rng, ALL_TYPES);
  const acc: Param = { name: "acc", type: pick(rng, ALL_TYPES) };
  const other: Param = { name: "m", type: pick(rng, ALL_TYPES) };
  const i: Param = { name: "i", type: "bigint" };
  const outer: Ctx = { rng, env: [...params], fns };
  const lines = [
    `  let i = 0n;`,
    `  let acc: ${acc.type} = ${expr(outer, acc.type, 2)};`,
    `  let m: ${other.type} = ${expr(outer, other.type, 1)};`,
  ];
  const inner: Ctx = { rng, env: [...params, i, acc, other], fns };
  if (rng() < 0.5) lines.push(...assignment(inner, other, "  "));
  lines.push(`  while (i < p0 && i < 4n) {`, `    decreases(4n - i);`);
  lines.push(...assignment(inner, acc, "    "));
  if (rng() < 0.5) lines.push(...assignment(inner, other, "    "));
  lines.push(rng() < 0.5 ? `    i = i + 1n;` : `    i += 1n;`, `  }`);
  if (rng() < 0.5) lines.push(...assignment(inner, acc, "  "));
  lines.push(block(inner, ret, 2, "  ", { n: 0 }));
  const sig = params.map((p) => `${p.name}: ${p.type}`).join(", ");
  return {
    name,
    params,
    ret,
    source: `export function ${name}(${sig}): ${ret} {\n${lines.join("\n")}\n}`,
    recursive: true,
  };
}

export function generateFunctions(seed: number, count: number, prefix: string): GenFunction[] {
  const rng = makeRng(seed);
  const fns: GenFunction[] = [];
  for (let i = 0; i < count; i++) {
    const name = `${prefix}${i}`;
    if (rng() < 0.25) {
      fns.push(recursiveFunction(rng, name, fns));
      continue;
    }
    if (rng() < 0.25) {
      fns.push(loopFunction(rng, name, fns));
      continue;
    }
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

export type Value = bigint | boolean | ReadonlyArray<Value> | { readonly [k: string]: Value };

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
    case "A":
      return Array.from({ length: Math.floor(rng() * 4) }, () => randomValue(rng, "bigint"));
    case "AN":
      return Array.from({ length: Math.floor(rng() * 4) }, () => randomValue(rng, "N"));
  }
}

export function valueToTs(v: Value): string {
  if (typeof v === "bigint") return `${v}n`;
  if (typeof v === "boolean") return String(v);
  if (Array.isArray(v)) return `[${(v as ReadonlyArray<Value>).map(valueToTs).join(", ")}]`;
  return `{ ${Object.entries(v).map(([k, x]) => `${k}: ${valueToTs(x)}`).join(", ")} }`;
}

const FIELDS: Record<"N" | "W" | "O", ReadonlyArray<[string, TypeName]>> = {
  N: [["a", "bigint"]],
  W: [["a", "bigint"], ["b", "boolean"]],
  O: [["n", "N"], ["w", "W"], ["k", "bigint"]],
};

/**
 * Every primitive inside `value` as seen at `type` (a value may carry extra fields its type
 * does not show), with the expression that reads it from `source`. An array contributes its
 * length first, so that by the time an element is read the length is known.
 */
export function leaves(
  value: Value,
  type: TypeName,
  source: string,
): Array<{ expr: string; value: bigint | boolean }> {
  if (type === "bigint" || type === "boolean") {
    if (typeof value !== "bigint" && typeof value !== "boolean") throw new Error(`not a ${type}`);
    return [{ expr: source, value }];
  }
  if (type === "A" || type === "AN") {
    const items = value as ReadonlyArray<Value>;
    const element: TypeName = type === "A" ? "bigint" : "N";
    return [
      { expr: `len(${source})`, value: BigInt(items.length) },
      ...items.flatMap((item, i) => leaves(item, element, `at(${source}, ${i}n)`)),
    ];
  }
  const record = value as { readonly [k: string]: Value };
  return FIELDS[type].flatMap(([k, t]) => leaves(record[k]!, t, `${source}.${k}`));
}
