"use verified";

import { ensures, implies, law, requires } from "../../../src/runtime.js";

export type Account = { readonly balance: bigint };

export function withdraw(acc: Account, amount: bigint): Account {
  requires(amount > 0n);
  requires(amount <= acc.balance);
  return { balance: acc.balance - amount };
}

ensures(withdraw, (acc, amount, result) => result.balance === acc.balance - amount);
ensures(withdraw, (acc, amount, result) => implies(acc.balance >= 0n, result.balance >= 0n));

// Every call below is guarded, so each precondition can be proved.
export function withdrawOrKeep(acc: Account, amount: bigint): Account {
  if (amount <= 0n || amount > acc.balance) return acc;
  return withdraw(acc, amount);
}

export function withdrawTwice(acc: Account, amount: bigint): Account {
  requires(amount > 0n && amount * 2n <= acc.balance);
  const once = withdraw(acc, amount);
  return withdraw(once, amount);
}

export function viaTernary(acc: Account, amount: bigint): bigint {
  return amount > 0n && amount <= acc.balance ? withdraw(acc, amount).balance : acc.balance;
}

export function viaShortCircuit(acc: Account, amount: bigint): boolean {
  return amount <= 0n || amount > acc.balance || withdraw(acc, amount).balance >= 0n;
}

law("guarded law", (acc: Account, amount: bigint) =>
  implies(amount > 0n && amount <= acc.balance, withdraw(acc, amount).balance < acc.balance),
);
