"use verified";

import { ping } from "./cycle-a.law.js";

export function pong(n: bigint): bigint {
  return ping(n + 1n);
}
