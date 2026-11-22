"use verified";

import { implies, requires } from "../../../src/runtime.js";
import { maxWithdrawal } from "./limits.js";

export type Owner = { readonly id: bigint; readonly active: boolean };
export type Account = { readonly balance: bigint; readonly owner: Owner };

export function isOpen(acc: Account): boolean {
  return acc.owner.active;
}

export function withdraw(acc: Account, amount: bigint, force: boolean): Account {
  requires(amount > 0n && amount <= acc.balance);
  requires(implies(!force, isOpen(acc)));
  requires(amount <= maxWithdrawal());
  return { balance: acc.balance - amount, owner: acc.owner };
}

export function total(a: Account, b: Account): bigint {
  return a.balance + b.balance;
}

function hidden(x: bigint): bigint {
  return x;
}

export function usesHidden(x: bigint): bigint {
  return hidden(x);
}
