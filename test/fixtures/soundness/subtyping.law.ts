"use verified";

// Bug: a record with extra fields passed where a narrower record is expected (allowed by
// TypeScript's structural typing) produced a Z3 sort error instead of a verdict.
import { law } from "../../../src/runtime.js";

export type A = { readonly a: bigint };
export type AB = { readonly a: bigint; readonly b: bigint };
export type Wrap = { readonly inner: A };

export function getA(r: A): bigint {
  return r.a;
}

export function narrow(r: AB): A {
  return r;
}

export function pickNarrow(r: AB, other: A, first: boolean): A {
  const kept: A = r;
  return first ? kept : other;
}

export function wrap(r: AB): Wrap {
  return { inner: r };
}

law("TRUE: wide argument", (r: AB) => getA(r) === r.a);
law("TRUE: wide return", (r: AB) => narrow(r).a === r.a);
law("TRUE: annotated const and ternary", (r: AB, o: A, f: boolean) => pickNarrow(r, o, f).a === (f ? r.a : o.a));
law("TRUE: wide nested field", (r: AB) => wrap(r).inner.a === r.a);
law("FALSE: narrowing reads the b field", (r: AB) => getA(r) === r.b);
