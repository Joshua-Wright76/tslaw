"use verified";

import { law, implies } from "../src/runtime.js";

export type Account = {
  readonly balance: bigint;
  readonly frozen: boolean;
};

export function deposit(acc: Account, amount: bigint): Account {
  if (acc.frozen || amount <= 0n) {
    return acc;
  }
  return { balance: acc.balance + amount, frozen: acc.frozen };
}

export function withdraw(acc: Account, amount: bigint): Account {
  if (acc.frozen || amount <= 0n || amount > acc.balance) {
    return acc;
  }
  return { balance: acc.balance - amount, frozen: acc.frozen };
}

export function applyNet(acc: Account, delta: bigint): Account {
  if (delta >= 0n) {
    return deposit(acc, delta);
  }
  return withdraw(acc, -delta);
}

law("frozen accounts never change balance", (acc: Account, delta: bigint) => {
  const after = applyNet(acc, delta);
  return implies(acc.frozen, after.balance === acc.balance && after.frozen);
});

law("withdraw never overdrafts a non-negative account", (acc: Account, amount: bigint) => {
  const after = withdraw(acc, amount);
  return implies(acc.balance >= 0n, after.balance >= 0n && after.balance <= acc.balance);
});

law("deposit followed by equal withdrawal restores balance", (acc: Account, amount: bigint) => {
  const after = withdraw(deposit(acc, amount), amount);
  return implies(!acc.frozen && acc.balance >= 0n && amount > 0n, after.balance === acc.balance);
});
