# The verified subset: semantics and translation

This document defines what a tslaw proof means. It gives

1. the syntax of the verified subset,
2. what each construct evaluates to (the semantics),
3. how each construct is translated into SMT-LIB2 for Z3, and
4. the statement that connects the two: if Z3 reports `unsat`, the law returns `true` for every well-typed input.

**Status.** The correctness statement in section 6 is argued on paper here; it is not machine-checked. The implementation (`src/dialect.ts`, `src/smt.ts`) is hand-written code intended to follow this document, and is tested against real JavaScript execution (`test/soundness.test.ts`, `test/fuzz.test.ts`) rather than proved to follow it. Section 7 lists everything a proof depends on.

When this document and the implementation disagree, that is a bug in one of them. Please report it.

## 1. Syntax

A verified module is a TypeScript file whose first statement is the directive `"use verified";`. After type checking, the part that matters is:

```
module   ::= decl*
decl     ::= type-declaration                         (erased; see section 2)
           | function f(x1: T1, ..., xn: Tn): T { block }
           | law("name", (x1: T1, ..., xn: Tn) => body)

T        ::= bigint | boolean | { readonly l1: T1; ...; readonly ln: Tn }     (n >= 1)

body     ::= e | { block }
block    ::= const x = e; block
           | const x: T = e; block
           | const { l1: x1, ..., lk: xk } = e; block
           | if (e) branch else branch
           | if (e) branch block
           | return e;
branch   ::= { block } | return e; | if-statement

e        ::= x | n | true | false                     (n is a bigint literal)
           | -e | +e | !e
           | e + e | e - e | e * e
           | e < e | e <= e | e > e | e >= e
           | e === e | e !== e                        (operands bigint or boolean)
           | e && e | e || e
           | e ? e : e
           | e.l
           | { l1: e1, ..., ln: en }
           | f(e1, ..., en)
           | implies(e, e)
           | (e)
```

Side conditions enforced by the subset check (stage 2):

- Every `block` ends in a `return` on every path.
- Conditions and the operands of `!`, `&&`, `||` have type `boolean`.
- `f` in a call refers to a top-level function of a verified module; `implies` is the one exported by the tslaw runtime. Both are resolved through the type checker, never by name.
- The call graph is acyclic (no recursion, direct or mutual).
- Parameter types contain no literal types.

Everything else in TypeScript is rejected. In particular there is no assignment, no loop, no exception, no `number`, no `any`, no cast, and no reference to anything except parameters and local `const`s.

## 2. Types and values

Each type denotes a set of values.

```
V(bigint)  = Z                 the mathematical integers
V(boolean) = { true, false }
V({ readonly l1: T1; ...; readonly ln: Tn })
           = records with at least the fields l1..ln, where field li holds a value of V(Ti)
```

Record types are structural. A record with extra fields belongs to the narrower type as well: `{a: 1n, b: true}` is in `V({readonly a: bigint})`. This is TypeScript's width subtyping, and we write `S <: T` when every field of `T` is a field of `S` at a subtype.

Type declarations (`type`, `interface`, `Readonly<...>`) only name these sets; they have no runtime behavior and are erased.

**Typing assumption.** We rely on TypeScript's type checker (with `strict`, `noUncheckedIndexedAccess`, `exactOptionalPropertyTypes`) being sound on this subset: if `e` has type `T` and the variables in scope hold values of their declared types, then evaluating `e` yields a value in `V(T)`. The subset excludes every construct known to break this (`any`, casts, non-null assertions, `@ts-ignore`, mutation of aliased data, arrays, optional fields).

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

**Totality.** Every well-typed expression and block evaluates to exactly one value. Evaluation cannot get stuck (typing assumption), cannot throw (no operation in the subset throws on these types), and terminates (expressions are finite and the call graph is acyclic, so call depth is bounded by the number of functions).

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
T[-e]G           = (- T[e]G)    T[+e]G = T[e]G        T[!e]G = (not T[e]G)
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
| the second argument of `implies(p, ...)` | `p` |

The first four rows match exactly when JavaScript evaluates the call. The last does not: `implies` is an ordinary function, so at runtime its second argument is evaluated even when `p` is false. That is harmless here because verified functions are total and `requires` does nothing at runtime, and it lets a law state a hypothesis in the natural way.

**Postconditions.** `ensures(f, (x1..xn, result) => post)` produces the query

```
(assert pre_f(a1..an))
(assert (not (let ((result (f' a1..an))) T[post])))
```

**What contracts add to the theorems.** Function calls are still translated through their definitions, so the theorems of section 6 hold whether or not the obligations are proved. If all call-site obligations in a module are `PROVED`, then additionally: in any evaluation that starts from a law, or from a function whose `requires` holds, every call reached under the conditions in the table above satisfies its callee's `requires`.

## 5. Verdicts

| Z3 answers | Verdict | Meaning |
|---|---|---|
| `unsat` | `PROVED` | No assignment to `a1..an` makes the body false. |
| `sat`, with a model | `DISPROVED` | The model's values for `a1..an` are reported as the counterexample. |
| `unknown` or timeout | `UNKNOWN` | No conclusion. Multiplication of variables makes the arithmetic undecidable in general, so this can happen for true laws. |

## 6. Correctness statement

Let `enc` map values to SMT values: integers and booleans to themselves, and a record `r` viewed at type `T` to `(mk_T enc(r(l1)) ... enc(r(ln)))`, keeping only `T`'s fields.

**Lemma (translation agrees with evaluation).** Let `e` be a well-typed expression of type `T`, `E` an environment whose values have the declared types, and `G` a term environment with `G(x)` denoting `enc(E(x))` for every variable. If `E |- e => v`, then in every SMT model that satisfies the function definitions, `T[e]G` denotes `enc(v)` at type `T`. The same holds for blocks.

*Argument.* By induction on the call depth, then on the structure of `e`. Each translation rule in section 4 is the SMT-LIB counterpart of the evaluation rule in section 3 with the same shape: `Int` arithmetic and comparison in SMT-LIB are exact integer operations, which is what ECMAScript specifies for `bigint` `+ - * < <= > >=` and `===`; `ite`, `and`, `or`, `not`, `=>` and `let` have their standard meaning; datatype selectors return the constructor's arguments. The projection case uses that `enc` at a supertype is `enc` at the subtype followed by dropping fields. Function calls use the induction hypothesis on call depth, which is well-founded because the call graph is acyclic; `define-fun` is macro expansion, so the definitions are satisfiable and determine the functions uniquely.

**Theorem (PROVED is sound).** If Z3 answers `unsat` for a law's query, then for all values `v1 in V(T1), ..., vn in V(Tn)`, the law's body evaluates to `true`.

*Argument.* Suppose some well-typed inputs made the body evaluate to `false`. Interpret each `ai` as `enc(vi)`. By the lemma, `T[body]` denotes `false` in that model, so `(not T[body])` is satisfied, contradicting `unsat`. By totality (section 3) the body evaluates to some boolean, so it evaluates to `true`.

**Theorem (DISPROVED is sound).** If Z3 answers `sat` with a model, then decoding the model's values for `a1..an` gives well-typed inputs on which the body evaluates to `false`.

*Argument.* Every value of sort `T[Ti]` decodes to a value in `V(Ti)` (this is why literal parameter types are rejected: `T[5n]` would be `Int`, which has values outside `V(5n)`). By the lemma the body evaluates to the value `T[body]` denotes, which is `false`.

## 7. What a proof depends on

A `PROVED` verdict is only as trustworthy as each of these:

1. **This document's argument**, which is informal.
2. **The implementation follows this document.** Checked by tests, not proved. `test/fuzz.test.ts` generates random programs in the subset, runs them in JavaScript, and requires the prover to agree; `test/soundness.test.ts` runs every proved law on random inputs and replays every counterexample.
3. **TypeScript's type checker is sound on the subset** (section 2).
4. **Z3 is correct**, including its answer `unsat`. With `--cross-check` this is weakened to "Z3 and cvc5 are not both wrong in the same way": cvc5 must independently reach the same verdict, and for `unsat` must produce a proof that its own proof checker accepts.
5. **The JavaScript engine implements `bigint` and object semantics as specified.** A real engine also has finite memory: a `bigint` computation can throw `RangeError` when a value is too large to represent, which the model ignores.
6. **Callers respect the types.** The theorem quantifies over well-typed inputs. Unverified code that passes ill-typed values (through `any`, casts or plain JavaScript) is outside it.
7. **The law says what you meant.** tslaw proves the laws that are written, nothing more.
