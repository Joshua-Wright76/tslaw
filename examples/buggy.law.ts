"use verified";

import { law, implies } from "../src/runtime.js";

export type TransferResult = {
  readonly from: bigint;
  readonly to: bigint;
};

/**
 * BUG: forgot to reject negative `amount`!
 * Calling `buggyTransfer(0n, 0n, -1n)` creates a negative `to` balance (steals tokens!).
 */
export function buggyTransfer(from: bigint, to: bigint, amount: bigint): TransferResult {
  if (amount > from) {
    return { from, to };
  }
  return { from: from - amount, to: to + amount };
}

law("conservation still holds even with the bug", (from: bigint, to: bigint, amount: bigint) => {
  const next = buggyTransfer(from, to, amount);
  return next.from + next.to === from + to;
});

law("balances never go negative (Z3 catches the bug!)", (from: bigint, to: bigint, amount: bigint) => {
  const next = buggyTransfer(from, to, amount);
  return implies(from >= 0n && to >= 0n, next.from >= 0n && next.to >= 0n);
});
