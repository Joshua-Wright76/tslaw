"use verified";

import { law, implies } from "../src/runtime.js";

export type TransferResult = {
  readonly from: bigint;
  readonly to: bigint;
  readonly moved: boolean;
};

/**
 * Pure promise-token transfer (Ratscramble-style):
 * moves `amount` tokens from `from` to `to` only when `amount > 0` and `from >= amount`.
 */
export function transferTokens(
  from: bigint,
  to: bigint,
  amount: bigint,
): TransferResult {
  if (amount <= 0n || amount > from) {
    return { from, to, moved: false };
  }
  return {
    from: from - amount,
    to: to + amount,
    moved: true,
  };
}

/**
 * Whether a held promise token may legally flip a player's vote:
 * - Tokens received in the current round cannot be used until the next round.
 * - A player's vote may change at most twice per round.
 */
export function canFlipVote(
  changesThisRound: bigint,
  acquiredRound: bigint,
  currentRound: bigint,
): boolean {
  if (changesThisRound < 0n || changesThisRound >= 2n) {
    return false;
  }
  return acquiredRound < currentRound;
}

law("token conservation across all transfers", (from: bigint, to: bigint, amount: bigint) => {
  const next = transferTokens(from, to, amount);
  return next.from + next.to === from + to;
});

law("balances never go negative", (from: bigint, to: bigint, amount: bigint) => {
  const next = transferTokens(from, to, amount);
  return implies(from >= 0n && to >= 0n, next.from >= 0n && next.to >= 0n);
});

law("invalid amounts leave balances unchanged", (from: bigint, to: bigint, amount: bigint) => {
  const next = transferTokens(from, to, amount);
  return implies(amount <= 0n || amount > from, !next.moved && next.from === from && next.to === to);
});

law("vote cannot flip more than twice per round", (changes: bigint, acq: bigint, round: bigint) => {
  return implies(changes >= 2n, !canFlipVote(changes, acq, round));
});

law("same-round token cooldown is enforced", (changes: bigint, acq: bigint, round: bigint) => {
  return implies(acq >= round, !canFlipVote(changes, acq, round));
});
