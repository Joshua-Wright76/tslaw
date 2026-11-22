# The verified subset: semantics and translation

This document defines what a tslaw proof means. It gives

1. the syntax of the verified subset,
2. what each construct evaluates to (the semantics),
3. how each construct is translated into SMT-LIB2 for Z3, and
4. the statement that connects the two: if Z3 reports `unsat`, the law returns `true` for every well-typed input.

**Status.** The correctness statement in section 6 is argued on paper here. For a core of the subset (section 8) the same statement is machine-checked in Lean; for the rest it is not. The implementation (`src/dialect.ts`, `src/smt.ts`) is hand-written code intended to follow this document, and is tested against real JavaScript execution (`test/soundness.test.ts`, `test/fuzz.test.ts`) rather than proved to follow it. Section 7 lists everything a proof depends on.

When this document and the implementation disagree, that is a bug in one of them. Please report it.

## 1. Syntax

A verified module is a TypeScript file whose first statement is the directive `"use verified";`. After type checking, the part that matters is:

```
module   ::= decl*
decl     ::= type-declaration                         (erased; see section 2)
           | function f(x1: T1, ..., xn: Tn): T { block }
           | law("name", (x1: T1, ..., xn: Tn) => body)

T        ::= bigint | boolean | { readonly l1: T1; ...; readonly ln: Tn }     (n >= 1)
           | readonly T[]                             (also written T[] or ReadonlyArray<T>)

body     ::= e | { block }
block    ::= const x = e; block
           | const x: T = e; block
           | const { l1: x1, ..., lk: xk } = e; block
           | let x = e; block                         (also with a type annotation)
           | x = e; block                             (x declared with let; also += -= *=)
           | if (e) branch else branch block?
           | if (e) branch block
           | while (e) { invariant(e);* decreases(e, ...); block } block
           | return e;
branch   ::= { block } | return e; | x = e; | if-statement

e        ::= x | n | true | false                     (n is a bigint literal)
           | -e | !e
           | e + e | e - e | e * e
           | e < e | e <= e | e > e | e >= e
           | e === e | e !== e                        (operands bigint or boolean)
           | e && e | e || e
           | e ? e : e
           | e.l
           | { l1: e1, ..., ln: en }
           | f(e1, ..., en)
           | implies(e, e)
           | [e1, ..., en]
           | len(e) | at(e, e) | append(e, e) | concat(e, e) | slice(e, e, e) | withAt(e, e, e)
           | (e)
```

Side conditions enforced by the subset check (stage 2):

- Every path through a function or law body ends in a `return`. A loop body contains no `return`.
- `while` loops and their `invariant`/`decreases` appear only in function bodies, not in laws or postconditions. A loop in a recursive function does not call into that recursion.
- Only variables declared with `let` are assigned; parameters, `const`s and record fields never are.
- Conditions and the operands of `!`, `&&`, `||` have type `boolean`.
- `f` in a call refers to a top-level function of a verified module; `implies` is the one exported by the tslaw runtime. Both are resolved through the type checker, never by name.
- A function that can reach itself through calls (directly or through others) is *recursive* and must declare a measure, `decreases(m1, ..., mk)`, directly after its `requires` statements. All functions of one recursion give the same number of measures, and their `requires` and `decreases` do not call into that recursion.
- Parameter types contain no literal types.

Everything else in TypeScript is rejected. In particular there is no exception, no `number`, no `any`, no cast, no mutation of a value (only rebinding of a local), and no reference to anything except parameters and local variables.

## 2. Types and values

Each type denotes a set of values.

```
V(bigint)  = Z                 the mathematical integers
V(boolean) = { true, false }
V({ readonly l1: T1; ...; readonly ln: Tn })
           = records with at least the fields l1..ln, where field li holds a value of V(Ti)
V(readonly T[]) = finite sequences of values of V(T)
```

Record types are structural. A record with extra fields belongs to the narrower type as well: `{a: 1n, b: true}` is in `V({readonly a: bigint})`. This is TypeScript's width subtyping, and we write `S <: T` when every field of `T` is a field of `S` at a subtype.

Type declarations (`type`, `interface`, `Readonly<...>`) only name these sets; they have no runtime behavior and are erased.

**Typing assumption.** We rely on TypeScript's type checker (with `strict`, `noUncheckedIndexedAccess`, `exactOptionalPropertyTypes`) being sound on this subset: if `e` has type `T` and the variables in scope hold values of their declared types, then evaluating `e` yields a value in `V(T)`. The subset excludes every construct known to break this (`any`, casts, non-null assertions, `@ts-ignore`, mutation of aliased data, optional fields). Arrays are a known hole in TypeScript only when they are written to or indexed directly; verified code can do neither, and reads them only through `at`, which has a precondition instead of an `undefined` result.

## 3. Evaluation

An environment `E` maps variables to values. `E |- e => v` reads "in `E`, expression `e` evaluates to `v`". These rules are what ECMAScript specifies for these operations on `bigint`, `boolean` and plain objects.

```
E |- x => E(x)
E |- n => n                     E |- true => true        E |- false => false

E |- e => a                     E |- e => b
-------------                   --------------
E |- -e => -a                   E |- !e => not b

E |- e1 => a    E |- e2 => b                     (op in + - *)
-----------------------------
E |- e1 op e2 => a op b                          (exact integer arithmetic)

E |- e1 => a    E |- e2 => b                     (cmp in < <= > >= === !==)
-----------------------------
E |- e1 cmp e2 => (a cmp b)

E |- e1 => b1   E |- e2 => b2
------------------------------                   (likewise || and implies,
E |- e1 && e2 => b1 and b2                        where implies(p, q) = not p or q)

E |- c => true   E |- e1 => v        E |- c => false   E |- e2 => v
-----------------------------        ------------------------------
E |- c ? e1 : e2 => v                E |- c ? e1 : e2 => v

E |- e => r                          E |- ei => vi  for each i
-----------------                    ------------------------------------------
E |- e.l => r(l)                     E |- { l1: e1, ..., ln: en } => {l1: v1, ..., ln: vn}

E |- ei => vi  for each i     [x1 -> v1, ..., xn -> vn] |- body(f) => v
------------------------------------------------------------------------
E |- f(e1, ..., en) => v
```

Arrays are immutable sequences. Writing `[v0, ..., vn-1]` for a sequence value:

```
[e1, ..., en]        => [v1, ..., vn]                where ei => vi
len(e)               => n                            where e => [v0, ..., vn-1]
at(e, i)             => vk                           where i => k and 0 <= k < n
append(e, x)         => [v0, ..., vn-1, w]           where x => w
concat(e, f)         => [v0, ..., vn-1, w0, ..., wm-1]
slice(e, a, b)       => [vj, ..., vk-1]              where a => j, b => k and 0 <= j <= k <= n
withAt(e, i, x)      => [v0, ..., w, ..., vn-1]      (w at position k) where 0 <= k < n
```

Outside the stated ranges `at`, `slice` and `withAt` throw `RangeError`. Like a function called outside its `requires`, that case is excluded by a call-site obligation rather than modeled.

`&&` and `||` short-circuit in JavaScript. Because every expression in the subset terminates, has no side effects and cannot throw, evaluating both operands gives the same result, so the rules above ignore short-circuiting.

Blocks evaluate to the value of the `return` they reach:

```
E |- e => v    E[x -> v] |- block => w            E |- e => r    E[xi -> r(li)] |- block => w
--------------------------------------            ---------------------------------------------
E |- const x = e; block => w                      E |- const { li: xi } = e; block => w

E |- c => true    E |- branch1 => v               E |- c => false   E |- branch2 => v
-------------------------------------             -------------------------------------
E |- if (c) branch1 else branch2 => v             E |- if (c) branch1 else branch2 => v

E |- c => true    E |- branch => v                E |- c => false   E |- block => v
-----------------------------------               -----------------------------------
E |- if (c) branch block => v                     E |- if (c) branch block => v

E |- e => v
---------------------
E |- return e; => v
```

Assignment and loops have their usual meaning: `x = e` replaces the binding of `x` in the environment for the statements that follow (including after the enclosing `if`), `x += e` is `x = x + e`, and `while (c) { body }` evaluates `body` (skipping its `invariant` and `decreases` statements, which do nothing) as long as `c` evaluates to `true`. Since values are immutable and there are no closures, an environment of current bindings is all the state there is.

**Totality.** Every well-typed expression and block evaluates to at most one value. Evaluation cannot get stuck (typing assumption) and cannot throw (no operation in the subset throws on these types). Without recursion it always terminates: expressions are finite, and call depth is bounded by the number of functions. A recursive function terminates on the arguments that satisfy its `requires` when its termination goals (section 4, Recursion) are proved; that is what those goals are for.

## 4. Translation to SMT-LIB2

Write `T[...]` for the translation.

### Types

```
T[bigint]  = Int
T[boolean] = Bool
T[{ readonly l1: T1; ...; readonly ln: Tn }] = a datatype R with one constructor
      (declare-datatypes ((R 0)) (((mk_R (R_l1 T[T1]) ... (R_ln T[Tn])))))
```

One datatype is declared per distinct record shape (set of field names with their types). Two TypeScript types with the same fields share a datatype.

```
T[readonly T[]] = (Seq T[T])
```

The theory of sequences is not part of the SMT-LIB standard, but Z3 and cvc5 implement it with the same syntax and meaning for the operations used here.

### Projection

SMT datatypes are not structural, so where TypeScript lets a value of type `S` flow into a position of type `T` with `S <: T`, the translation inserts an explicit conversion that drops the extra fields:

```
proj(t, T, T) = t
proj(t, S, T) = (mk_T proj((S_l1 t), S1, T1) ... proj((S_ln t), Sn, Tn))     for T's fields l1..ln
```

Positions with an expected type are: function arguments, `return` expressions, annotated `const` initializers, and both branches of a ternary. `T[e : T]` below means "translate `e`, then project from `e`'s own type to `T`". An object literal in such a position is built directly at the expected type from its properties.

### Expressions

`G` maps each variable in scope to an SMT term.

```
T[x]G            = G(x)
T[n]G            = n            (decimal numeral; hex, octal, binary and separators normalized)
T[true]G         = true         T[false]G = false
T[-e]G           = (- T[e]G)    T[!e]G = (not T[e]G)
T[e1 + e2]G      = (+ T[e1]G T[e2]G)                  likewise - and *
T[e1 < e2]G      = (< T[e1]G T[e2]G)                  likewise <= > >=
T[e1 === e2]G    = (= T[e1]G T[e2]G)
T[e1 !== e2]G    = (not (= T[e1]G T[e2]G))
T[e1 && e2]G     = (and T[e1]G T[e2]G)                T[e1 || e2]G = (or T[e1]G T[e2]G)
T[implies(p,q)]G = (=> T[p]G T[q]G)
T[c ? e1 : e2]G  = (ite T[c]G T[e1 : U]G T[e2 : U]G)  where U is the type of the whole expression
T[e.l]G          = (S_l T[e]G)                        where S is the type of e
T[{ li: ei }]G   = (mk_S T[e1]G ... T[en]G)           fields in the datatype's order
T[f(e1..en)]G    = (f' T[e1 : T1]G ... T[en : Tn]G)   where Ti are f's parameter types
```

### Arrays

```
T[[e1, ..., en] : readonly A[]]G = (seq.++ (seq.unit T[e1 : A]G) ... (seq.unit T[en : A]G))
                                   (seq.unit ... alone for n = 1, (as seq.empty (Seq T[A])) for n = 0)
T[len(e)]G          = (seq.len T[e]G)
T[at(e, i)]G        = (seq.nth T[e]G T[i]G)
T[append(e, x)]G    = (seq.++ T[e]G (seq.unit T[x : A]G))
T[concat(e, f)]G    = (seq.++ T[e]G T[f]G)
T[slice(e, a, b)]G  = (seq.extract T[e]G T[a]G (- T[b]G T[a]G))
T[withAt(e, i, x)]G = (seq.++ (seq.extract s 0 i) (seq.unit T[x : A]G) (seq.extract s (+ i 1) (- (seq.len s) i 1)))
                      with s = T[e]G and i = T[i]G
```

`seq.nth` and `seq.extract` are unspecified or clipped outside the sequence, so `at`, `slice` and `withAt` each generate a call-site obligation exactly like a `requires` (see Contracts): `0 <= i < len` for `at` and `withAt`, `0 <= a <= b <= len` for `slice`. An array literal is translated at the element type its context expects. Projection (the previous subsection) is not defined between array types: an array of a wider record type where an array of a narrower one is expected is rejected, since converting it would need a new sequence.

### Blocks

`U` is the enclosing function's return type (`boolean` for a law).

```
T[const x = e; block]G          = (let ((v T[e]G)) T[block]G[x -> v])            v fresh
T[const x: A = e; block]G       = (let ((v T[e : A]G)) T[block]G[x -> v])
T[const { li: xi } = e; block]G = (let ((v T[e]G)) T[block]G[xi -> (S_li v)])
T[if (c) b1 else b2]G           = (ite T[c]G T[b1]G T[b2]G)
T[if (c) b1 block]G             = (ite T[c]G T[b1]G T[block]G)
T[return e;]G                   = T[e : U]G
```

### Functions and laws

Functions are emitted in dependency order, each with a unique SMT name:

```
T[function f(x1: T1, ..., xn: Tn): U { block }]
    = (define-fun f' ((p1 T[T1]) ... (pn T[Tn])) T[U]  T[block][xi -> pi])
```

For a law `law("name", (x1: T1, ..., xn: Tn) => body)` the query sent to Z3 is:

```
<datatype declarations>
<function definitions>
(declare-const a1 T[T1]) ... (declare-const an T[Tn])
(assert (not T[body][xi -> ai]))
(check-sat)
```

SMT identifiers are made unique by an index (`fn_3_name`, `p_0_x`), never by the TypeScript name alone, and no user-controlled text is written into the script unescaped.

### Contracts

A function body may begin with `requires(c1); ...; requires(ck);` and a module may contain `ensures(f, (x1, ..., xn, result) => post)`. Neither changes what any function evaluates to: `requires` and `ensures` are no-ops at runtime, and the definition `f'` above is built from the body after the `requires` statements. They add queries.

Write `pre_f(x1..xn)` for `c1 and ... and ck` (or `true` when `f` has no `requires`).

**Call-site obligations.** For every call `g(e1..em)` to a function with `requires`, occurring in a function body, a law, a postcondition or a later `requires`, one query claims

```
context  =>  pre_g(T[e1], ..., T[em])
```

for all values of the enclosing parameters. `context` is everything known at that point: the enclosing function's own `requires` (those before the call, if the call is itself inside a `requires`), the `const` bindings in scope, and the conditions under which the call is reached:

| The call is in | Added to the context |
|---|---|
| the then-branch of `if (c)` or `c ? ... : ...` | `c` |
| the else-branch, or the code after `if (c) return ...;` | `not c` |
| the right operand of `a && ...` | `a` |
| the right operand of `a || ...` | `not a` |
| the second argument of `implies(p, ...)`, in a law or postcondition | `p` |

The first four rows match exactly when JavaScript evaluates the call. The last does not: `implies` is an ordinary function, so at runtime its second argument is evaluated even when `p` is false. Laws and postconditions are never executed, so there the row lets a hypothesis be stated in the natural way. In a function body, a `requires` or a `decreases` (code that runs) the row does not apply: a call inside `implies(p, ...)` must satisfy its precondition whether or not `p` holds, since a recursive function called outside its precondition might not return.

**Postconditions.** `ensures(f, (x1..xn, result) => post)` produces the query

```
(assert pre_f(a1..an))
(assert (not (let ((result T[block_f][xi -> ai])) T[post])))
```

where the result is `f`'s translated body (the same value as `f' a1..an`; the Recursion section below says why the body is used).

**What contracts add to the theorems.** If the call-site obligations are `PROVED`, then in any evaluation that starts from a law, or from a function whose `requires` holds, every call reached under the conditions in the table above satisfies its callee's `requires`. A law or postcondition is reported as `PROVED` or `DISPROVED` only when that is established for all the code it runs (see "Dependencies between verdicts"), so its verdict is never about an evaluation that leaves a precondition.

### Recursion

Functions are grouped by mutual recursion (the strongly connected components of the call graph), and groups are emitted callees first. A group that is not recursive is one `define-fun` as above. A recursive group `f1..fm` is emitted as

```
(define-fun pre_fi ...)                      ; when fi has requires
(define-fun mes_fi_j ((p1 ...) ...) Int T[mj])   ; one per measure of fi
(declare-fun undef_fi (...) T[U])            ; when fi has requires
(define-funs-rec ((f1' ...) ... (fm' ...))
  ((ite (pre_f1 p1..pn) T[block1] (undef_f1 p1..pn)) ...))
```

so a recursive function has its body's value where its precondition holds and an unspecified value elsewhere.

`define-funs-rec` asserts that the functions satisfy their equations for all arguments. Unlike `define-fun`, that is an assumption: for a function that does not terminate, such as `f(n) = f(n) + 1n`, no such function exists and the assumption is contradictory, which would make every query `unsat`. The termination goals rule this out.

**Termination goals.** Order integers by `a << b` iff `a < b and 0 <= b`, and tuples lexicographically by `<<`. Neither order has an infinite descending chain. For every call `g(e1..em)` in the body of a recursive function `f`, with `g` in the same group, one query claims

```
context  =>  (mes_g_1(args), ..., mes_g_k(args))  <<  (mes_f_1(p1..pn), ..., mes_f_k(p1..pn))
```

with `context` as for call-site obligations (it includes `pre_f`). In these queries the group's functions are *declared, not defined* (`declare-fun`), so the claim is proved for every possible meaning of the recursive calls and cannot rest on the definition it is meant to justify. Functions in groups below are defined as usual.

*Why this suffices.* Suppose all termination goals of a group are proved. Consider the relation "evaluating `fi(v)` with `pre_fi(v)` reaches a call `fj(w)` with `pre_fj(w)`". By the goals, the measure of `(fj, w)` is below that of `(fi, v)` in a well-founded order, whatever values the inner calls return. So the equations define the functions by well-founded recursion: there is exactly one family of functions satisfying them on the arguments where the preconditions hold (a call whose precondition fails yields `undef`, which is not recursive). Hence the `define-funs-rec` assumption is satisfiable, and in every model the functions agree with evaluation wherever preconditions hold. Calls in untaken branches do not matter because `ite`, `and`, `or` and `=>` do not depend on the value of an operand that the conditions in the table rule out.

**Postconditions as induction hypotheses.** For `ensures(f, post)` the query is

```
(assert pre_f(a1..an))
(assert fact_1) ... (assert fact_k)
(assert (not (let ((result T[block_f][xi -> ai])) T[post])))
```

The result is the translated body rather than a call. Each `fact` comes from a call `g(e1..em)` to a *recursive* function `g` that has postconditions, and reads

```
context  =>  (pre_g(args) => post_g(args, g'(args)))
```

Facts are generated for calls in the body of `f`, and for calls written in `post` itself only when `g` is *strictly below* `f` in the call graph: `f` can reach `g` and `g` cannot reach `f`. They are also generated for calls in laws, and in the bodies of functions when proving call-site obligations there.

*Why this is sound.* Take all postconditions of one recursive group together and prove them by well-founded induction on the measure. For arguments `v` with `pre_f(v)`, every call to a group member in the body that is actually reached has a smaller measure (termination goals), so the induction hypothesis gives its postcondition, which is the fact. A call written in `post` is at arbitrary arguments, so no hypothesis applies; assuming the postcondition there would let `ensures(f, (n, r) => f(n) < 0n)` prove itself. Facts about a function `g` outside the group are not hypotheses but previously established results, and for that their proofs must not depend on `f`'s in turn. That is why `g` has to be strictly below `f`: the proof of a postcondition of `f` then uses only postconditions of functions below `f` (or of its own group, as induction hypotheses), and "below" is well-founded. "Cannot reach `f`" alone would not do. Two unrelated functions could each carry a false postcondition about the other, such as `ensures(g, (n, r) => h(n) === 1n)` and `ensures(h, (n, r) => g(n) === 1n)`, and each proof would assume the other's claim; an earlier version did exactly that.

**Dependencies between verdicts.** A query that contains a recursive definition is meaningful only if that group's termination goals are `PROVED`, and a proof that asserts facts only if the corresponding `ensures` (or, for loops, "kept by the body" goals) are `PROVED`.

A goal that has facts is first tried with every recursive function and loop *declared but not defined*, so that only the facts are known about them. This is weaker, hence sound, and it is the form in which inductive arguments go through quickly; if it fails, the goal is tried again with the definitions. Either way the termination goals are dependencies: a fact about a call presumes the call returns (`while (true) {}` would otherwise "establish" `false` after it).

After solving, verdicts are adjusted until nothing changes:

- A `PROVED` verdict with a dependency that is not `PROVED` is retried without facts; if that fails it becomes `UNKNOWN`.
- A `DISPROVED` verdict becomes `UNKNOWN` if one of its *foundations* is not `PROVED`. (A failed `ensures` is not a foundation: removing an assumption cannot remove a counterexample.)

The foundations of any goal are the termination goals of the recursive functions and loops in its query. For a law or postcondition, which are claims about what running the code returns, they also include every call-site obligation and loop-invariant goal ("holds on entry", "kept by the body") of the law itself and of every function and loop its query contains. The model deliberately says nothing about a recursive function outside its precondition or a loop outside its invariant, and `at`, `slice` and `withAt` throw outside their ranges, so where one of those goals can fail the model and the program may part ways: a "proof" might be about a call that throws, and a "counterexample" might use a value the program never produces.

Mutual dependencies among the postconditions of one group are allowed; they are the simultaneous induction above. Each query includes only the definitions its goal can reach, so an unfounded definition affects only what uses it. When a file imports recursive functions, their termination goals and any assumed postconditions are checked again as part of that file.

### Local variables and loops

**Statements as bindings.** A statement that contains no `return` only changes the environment. Its translation `B[s]G` is a list of `let` bindings together with a new term environment:

```
B[let x = e]G    = [v := T[e]G],            G[x -> v]                 v fresh
B[x = e]G        = [v := T[e : A]G],        G[x -> v]                 A the declared type of x
B[x += e]G       = [v := (+ G(x) T[e]G)],   G[x -> v]
B[if (c) s1 else s2]G
                 = B1 ++ B2 ++ [vx := (ite T[c]G G1(x) G2(x))  for each x with G1(x) != G2(x)],
                   G[x -> vx ...]            where (B1, G1) = B[s1]G and (B2, G2) = B[s2]G
B[s1; s2]G       = B1 ++ B2,  G2             where (B1, G1) = B[s1]G and (B2, G2) = B[s2]G1
```

Bindings from both branches of an `if` are placed in front unconditionally. That is harmless because terms have no effects and every SMT function is total; each variable's value is then chosen by the `ite`. Variables declared inside a block are dropped from the environment at its end. A block is translated by wrapping the bindings of its leading statements around the translation of the rest: `T[s; block]G = (let B ... T[block]G')`.

An `if` that contains a `return` is translated as in "Blocks", with the statements after it appended to each branch that can fall through.

**Loops.** Let `x1..xn` be the variables declared outside the loop that it mentions, `M` those among them that it assigns, `I` the conjunction of its `invariant`s (preceded by the enclosing function's `pre_f` when no local hides a parameter), `c` its condition and `(B, G')` the bindings of its body. The loop becomes a recursive function, in a group of its own placed before the enclosing function:

```
(define-funs-rec ((loop ((p1 ...) ... (pn ...)) State))
  ((ite I (ite c (let B (loop G'(x1) ... G'(xn))) (mk_State G(m) for m in M)) (undef p1..pn))))
B[while ...]G = [s := (loop G(x1) ... G(xn))],  G[m -> (S_m s) for m in M]
```

This is exactly a tail-recursive function with precondition `I`, so the Recursion section applies. Three goals are generated per loop, each for all values of `p1..pn`:

| Goal | Claim |
|---|---|
| holds on entry | `context => I[G(xi)]` at the loop, a call-site obligation |
| kept by the body | `I and c => (let B I[G'(xi)])` |
| termination | `I and c => (let B measure[G'(xi)] << measure)`, with `loop` declared but not defined |

The "holds on entry" and "kept" goals are omitted when the invariant is only the inherited `pre_f`: parameters are never assigned, so it holds by construction.

**What is known after a loop.** Where facts are generated (see Recursion), each loop application also yields

```
context  =>  (I[args] => (let ((s (loop args))) (I and not c) at the final values))
```

*Why this is sound.* By well-founded induction on the measure: if `I` holds and `c` is false, the result is the current state, where `I and not c` holds. If `c` is true, `I` holds for the next arguments ("kept by the body"), the measure is smaller (termination), and the loop's result is the result from there. So the fact depends on the "kept" goal, and on termination. Goals inside a loop may themselves assume only postconditions that lie strictly below the enclosing function, because that function's termination can depend on the loop.

Functions that contain loops are treated like recursive ones in one more respect: their `ensures` are asserted as facts where they are called, since nothing about a loop for all inputs can be learned by unfolding.

## 5. Verdicts

| Z3 answers | Verdict | Meaning |
|---|---|---|
| `unsat` | `PROVED` | No assignment to `a1..an` makes the body false. |
| `sat`, with a model | `DISPROVED` | The model's values for `a1..an` are reported as the counterexample. |
| `unknown` or timeout | `UNKNOWN` | No conclusion. Multiplication of variables makes the arithmetic undecidable in general, so this can happen for true laws. |

## 6. Correctness statement

Let `enc` map values to SMT values: integers and booleans to themselves, a record `r` viewed at type `T` to `(mk_T enc(r(l1)) ... enc(r(ln)))`, keeping only `T`'s fields, and an array to the sequence of its elements' encodings.

**Lemma (translation agrees with evaluation).** Let `e` be a well-typed expression of type `T`, `E` an environment whose values have the declared types, and `G` a term environment with `G(x)` denoting `enc(E(x))` for every variable. If `E |- e => v`, then in every SMT model that satisfies the function definitions, `T[e]G` denotes `enc(v)` at type `T`. The same holds for blocks.

*Argument.* By induction on the call depth, then on the structure of `e`. Each translation rule in section 4 is the SMT-LIB counterpart of the evaluation rule in section 3 with the same shape: `Int` arithmetic and comparison in SMT-LIB are exact integer operations, which is what ECMAScript specifies for `bigint` `+ - * < <= > >=` and `===`; `ite`, `and`, `or`, `not`, `=>` and `let` have their standard meaning; datatype selectors return the constructor's arguments. The projection case uses that `enc` at a supertype is `enc` at the subtype followed by dropping fields. Function calls use the induction hypothesis on call depth. Without recursion that is well-founded because the call graph is acyclic, and `define-fun` is macro expansion, so the definitions are satisfiable and determine the functions uniquely. For recursive groups whose termination goals are proved, section 4 (Recursion) gives the same two facts on the arguments that satisfy the preconditions.

Both theorems below are stated for final verdicts, after the dependency adjustment of section 4: every recursive function and loop used has proved termination goals, every assumed fact a proved `ensures`, and every precondition and invariant in the code that runs is proved to hold where it is needed.

**Theorem (PROVED is sound).** If Z3 answers `unsat` for a law's query, then for all values `v1 in V(T1), ..., vn in V(Tn)`, the law's body evaluates to `true`.

*Argument.* Suppose some well-typed inputs made the body evaluate to `false`. Interpret each `ai` as `enc(vi)`. By the lemma, `T[body]` denotes `false` in that model, so `(not T[body])` is satisfied, contradicting `unsat`. By totality (section 3) the body evaluates to some boolean, so it evaluates to `true`.

**Theorem (DISPROVED is sound).** If Z3 answers `sat` with a model, then decoding the model's values for `a1..an` gives well-typed inputs on which the body evaluates to `false`.

*Argument.* Every value of sort `T[Ti]` decodes to a value in `V(Ti)` (this is why literal parameter types are rejected: `T[5n]` would be `Int`, which has values outside `V(5n)`). By the lemma the body evaluates to the value `T[body]` denotes, which is `false`.

## 7. What a proof depends on

A `PROVED` verdict is only as trustworthy as each of these:

1. **This document's argument**, which is informal, except for the core calculus of section 8, where it is checked by Lean.
2. **The implementation follows this document.** Checked by tests, not proved. `test/fuzz.test.ts` generates random programs in the subset, runs them in JavaScript, and requires the prover to agree; `test/soundness.test.ts` runs every proved law on random inputs and replays every counterexample.
3. **TypeScript's type checker is sound on the subset** (section 2).
4. **Z3 is correct**, including its answer `unsat`. With `--cross-check` this is weakened to "Z3 and cvc5 are not both wrong in the same way": cvc5 must independently reach the same verdict, and for `unsat` must produce a proof that its own proof checker accepts.
5. **The JavaScript engine implements `bigint` and object semantics as specified.** A real engine also has finite memory: a `bigint` computation can throw `RangeError` when a value is too large to represent, and a deep recursion can overflow the call stack. The model ignores both; a termination proof bounds neither depth nor time.
6. **Callers respect the types.** The theorem quantifies over well-typed inputs. Unverified code that passes ill-typed values (through `any`, casts or plain JavaScript) is outside it. The wrappers generated by `tslaw guard` discharge this assumption at runtime for calls that go through them: they establish that each argument is a value of its declared type (as a fresh frozen copy) and that `pre_f` holds before calling `f`. The generator itself (`src/guard.ts`) is tested, not proved.
7. **The law says what you meant.** tslaw proves the laws that are written, nothing more.

## 8. The machine-checked core

[`proofs/Core.lean`](../proofs/Core.lean) formalizes a core of the subset in Lean 4 and proves the statements of section 6 for it. It has no dependencies; `npm run prove` (or `cd proofs && lean Core.lean`) checks it in a few seconds, and CI does so on every change.

**What the core contains.** `bigint` and `boolean`; arithmetic, comparisons, `===`/`!==`, `!`, `&&`, `||`, `implies` and the ternary; blocks built from `const`, `if`/`else` and `return`.

**What is proved.**

| Lean theorem | Statement | Section |
|---|---|---|
| `eval_typed`, `evalBlock_typed` | A well-typed expression or block evaluates to a value of its type (totality). | 3 |
| `tr_correct`, `trBlock_correct` | In every well-sorted model, the translated term denotes the value the source evaluates to. | 6, lemma |
| `proved_sound` | If no well-sorted model satisfies the query, the law's body evaluates to `true` for all well-typed inputs. | 6 |
| `disproved_sound` | A model of the query is a well-typed input on which the body evaluates to `false`. | 6 |

The point of interest is the gap the paper argument skates over. The source semantics (`eval`) is JavaScript's: `&&`, `||` and the ternary do not evaluate the operand they skip, and an operation on the wrong kind of value has no result. The target semantics (`denote`) is SMT-LIB's: every subterm must have a value. The proof closes the gap exactly as section 3 says, through totality: the skipped operand is well-typed, so it has a value, so evaluating it changes nothing.

The theorems depend only on Lean's standard axioms `propext` and `Quot.sound` (`#print axioms`), and `test/proofs.test.ts` checks that they are not vacuous: translating `&&` as `or`, `implies` as `and`, `!==` as `=`, swapping the branches of an `if`, or leaving the query un-negated each makes the file fail to check.

**What this does not establish.**

- It is a proof about a *model* of the translator, written by hand to match `src/smt.ts`. Nothing connects the Lean definitions to the TypeScript code except reading both, and the tests of section 7, item 2.
- Records and projection, function calls, contracts, recursion and termination, loops and arrays are outside the core. Their arguments (sections 4 and 6) remain on paper. The recursion and loop arguments in particular, which decide when a definition may be assumed at all, are the most delicate part of the system and are not mechanized.
- The model identifies source and solver variable names; the implementation renames them apart.
- "The solver answered `unsat`" is taken as a hypothesis. Whether Z3 is right is section 7, item 4.
