"use verified";

// Module-private helper with the same name as helpers in dep-b.ts and helper-collision.law.ts.
function helper(x: bigint): bigint {
  return x + 1n;
}

export function f(x: bigint): bigint {
  return helper(x);
}
