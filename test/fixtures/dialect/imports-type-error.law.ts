"use verified";

import { law } from "../../../src/runtime.js";
import { bad } from "./dep-type-error.js";

law("never checked", (x: bigint) => bad(x) === x);
