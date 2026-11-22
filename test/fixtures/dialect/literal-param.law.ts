"use verified";

import { law } from "../../../src/runtime.js";

law("literal bigint param", (x: 5n) => x === 5n);
law("literal boolean field", (r: { readonly on: true }) => r.on);
