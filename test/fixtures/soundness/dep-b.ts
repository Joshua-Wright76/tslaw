"use verified";

function helper(x: bigint): bigint {
  return x + 2n;
}

export function g(x: bigint): bigint {
  return helper(x);
}
