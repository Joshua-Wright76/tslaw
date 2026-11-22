# Soundness regression fixtures

Each file here reproduces a way tslaw could once be tricked into proving something false.
`test/soundness.test.ts` checks every law in these files:

- A law whose name starts with `FALSE:` is false when run in JavaScript. tslaw must **never** report it `PROVED`.
- A law whose name starts with `TRUE:` must be `PROVED`.
- Every `PROVED` law is also run on random inputs in JS, and every `DISPROVED` counterexample is replayed in JS, to catch encoding bugs that disagree with real runtime behavior.
