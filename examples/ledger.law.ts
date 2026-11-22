"use verified";

import {
  append,
  at,
  decreases,
  ensures,
  invariant,
  law,
  len,
  requires,
  slice,
  withAt,
} from "../src/runtime.js";

export type Entry = {
  readonly amount: bigint;
};

/**
 * Sum the first `n` ledger entries recursively, used as the specification for `totalBalance`.
 */
export function sumPrefix(entries: readonly Entry[], n: bigint): bigint {
  requires(0n <= n && n <= len(entries));
  decreases(n);
  if (n === 0n) return 0n;
  return sumPrefix(entries, n - 1n) + at(entries, n - 1n).amount;
}

/**
 * Compute the total balance across all ledger entries using a `while` loop.
 */
export function totalBalance(entries: readonly Entry[]): bigint {
  let i = 0n;
  let acc = 0n;
  while (i < len(entries)) {
    invariant(0n <= i && i <= len(entries));
    invariant(acc === sumPrefix(entries, i));
    decreases(len(entries) - i);
    acc += at(entries, i).amount;
    i += 1n;
  }
  return acc;
}

ensures(totalBalance, (entries, result) => result === sumPrefix(entries, len(entries)));

/**
 * Credit one account balance in an immutable array of balances.
 */
export function creditAccount(
  balances: readonly bigint[],
  index: bigint,
  amount: bigint,
): readonly bigint[] {
  requires(0n <= index && index < len(balances));
  requires(amount >= 0n);
  return withAt(balances, index, at(balances, index) + amount);
}

ensures(creditAccount, (balances, _index, _amount, next) => len(next) === len(balances));
ensures(
  creditAccount,
  (balances, index, amount, next) => at(next, index) === at(balances, index) + amount,
);

/**
 * Append a new entry to the ledger.
 */
export function recordEntry(entries: readonly Entry[], amount: bigint): readonly Entry[] {
  return append(entries, { amount });
}

law("recording an entry grows the ledger by one and stores the amount at the end", (
  entries: readonly Entry[],
  amount: bigint,
) => {
  const next = recordEntry(entries, amount);
  return len(next) === len(entries) + 1n && at(next, len(entries)).amount === amount;
});

law("crediting an account never lowers its balance", (
  balances: readonly bigint[],
  index: bigint,
  amount: bigint,
) => {
  if (index < 0n || index >= len(balances) || amount < 0n) return true;
  return at(creditAccount(balances, index, amount), index) >= at(balances, index);
});

law("slicing a prefix of an appended ledger recovers the original length", (
  entries: readonly Entry[],
  amount: bigint,
) => {
  const next = recordEntry(entries, amount);
  const prefix = slice(next, 0n, len(entries));
  return len(prefix) === len(entries);
});
