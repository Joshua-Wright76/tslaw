import { configDefaults, defineConfig } from "vitest/config";

export default defineConfig({
  test: {
    // Each verifyFiles() call builds a full TypeScript program and spawns Z3 processes.
    testTimeout: 30_000,
    exclude: [...configDefaults.exclude, ".worktrees/**"],
  },
});
