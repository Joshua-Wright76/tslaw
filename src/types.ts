export type VType =
  | { readonly kind: "bigint" }
  | { readonly kind: "boolean" }
  | {
      readonly kind: "record";
      /** Sorted field entries for canonical structural identity. */
      readonly fields: ReadonlyArray<{ readonly name: string; readonly type: VType }>;
    };

export interface SourceLocation {
  readonly file: string;
  readonly line: number;
  readonly column: number;
}

export interface Diagnostic {
  readonly stage: "typecheck" | "dialect" | "smt";
  readonly code: string;
  readonly message: string;
  readonly location?: SourceLocation;
}

export interface CounterexampleEntry {
  readonly name: string;
  readonly value: string;
  readonly raw: unknown;
}

export type LawStatus = "proved" | "disproved" | "unknown" | "error";

export interface LawResult {
  readonly file: string;
  readonly name: string;
  readonly location: SourceLocation;
  readonly status: LawStatus;
  readonly durationMs: number;
  readonly counterexample?: ReadonlyArray<CounterexampleEntry>;
  readonly smt?: string;
  readonly reason?: string;
}

export interface FileVerificationResult {
  readonly file: string;
  readonly verifiedDirective: boolean;
  readonly diagnostics: ReadonlyArray<Diagnostic>;
  readonly laws: ReadonlyArray<LawResult>;
}

export interface VerifyOptions {
  /** Emit generated SMT-LIB2 script on each LawResult. */
  readonly emitSmt?: boolean;
  /** Per-law Z3 timeout in milliseconds (default: 5000). */
  readonly timeoutMs?: number;
  /** Explicit path to the z3 binary (default: VSCRIPT_Z3 env or "z3"). */
  readonly z3Path?: string;
  /** Verify files even without a top-level "use verified" directive. */
  readonly requireDirective?: boolean;
  /** Maximum concurrent Z3 solver processes (default: 8). */
  readonly concurrency?: number;
}

export interface VerifyReport {
  readonly ok: boolean;
  readonly files: ReadonlyArray<FileVerificationResult>;
  readonly summary: {
    readonly totalFiles: number;
    readonly verifiedFiles: number;
    readonly proved: number;
    readonly disproved: number;
    readonly unknown: number;
    readonly errors: number;
  };
}
