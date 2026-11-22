"use verified";

import { at, len, requires } from "../../../src/runtime.js";

export type Item = { readonly price: bigint; readonly qty: bigint };

export function lineTotal(items: readonly Item[], index: bigint): bigint {
  requires(0n <= index && index < len(items));
  requires(at(items, index).qty >= 0n);
  return at(items, index).price * at(items, index).qty;
}

export function count(items: readonly Item[], tags: readonly (readonly bigint[])[]): bigint {
  return len(items) + len(tags);
}
