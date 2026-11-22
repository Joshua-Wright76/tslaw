/-
  tslaw core calculus: a machine-checked proof that the translation to solver terms agrees
  with evaluation, and that PROVED and DISPROVED verdicts are sound.

  Check with:  lean proofs/Core.lean     (Lean 4, no dependencies)

  What is modeled (see docs/SEMANTICS.md for the full subset):
    * `bigint` and `boolean` values;
    * arithmetic, comparison, `===`/`!==`, `!`, `&&`, `||`, `implies`, the ternary;
    * blocks made of `const`, `if`/`else` and `return`.
  What is not: records, function calls, contracts, recursion, loops, arrays.

  The source semantics is JavaScript's: `&&`, `||` and the ternary evaluate their operands
  lazily, and an operation applied to the wrong kind of value has no result. The target
  semantics is that of SMT-LIB terms: every subterm must have a value. The two are related
  by typing: a well-typed expression always has a value, so evaluating the operands that
  JavaScript would have skipped changes nothing.
-/

namespace Tslaw

/-! ## Values and types -/

inductive Ty where
  | int
  | bool
  deriving DecidableEq

inductive Val where
  | int (n : Int)
  | bool (b : Bool)
  deriving DecidableEq

def Val.ty : Val → Ty
  | .int _ => .int
  | .bool _ => .bool

inductive Arith where
  | add | sub | mul

inductive Cmp where
  | lt | le | gt | ge

def Arith.apply : Arith → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

def Cmp.apply : Cmp → Int → Int → Bool
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)
  | .gt, a, b => decide (a > b)
  | .ge, a, b => decide (a ≥ b)

/-- `===` on two values of the same kind; no result for mixed kinds. -/
def valEq : Val → Val → Option Bool
  | .int a, .int b => some (decide (a = b))
  | .bool a, .bool b => some (decide (a = b))
  | _, _ => none

/-! ## Environments -/

abbrev Env := String → Option Val
abbrev Ctx := String → Option Ty

def Env.set (ρ : Env) (x : String) (v : Val) : Env :=
  fun y => if y = x then some v else ρ y

def Ctx.set (Γ : Ctx) (x : String) (τ : Ty) : Ctx :=
  fun y => if y = x then some τ else Γ y

/-- Every variable the context knows holds a value of its declared type. -/
def EnvOk (Γ : Ctx) (ρ : Env) : Prop :=
  ∀ x τ, Γ x = some τ → ∃ v, ρ x = some v ∧ v.ty = τ

theorem EnvOk.set {Γ : Ctx} {ρ : Env} (h : EnvOk Γ ρ) (x : String) (v : Val) :
    EnvOk (Γ.set x v.ty) (ρ.set x v) := by
  intro y τ hy
  unfold Ctx.set at hy
  unfold Env.set
  by_cases hxy : y = x
  · simp [hxy] at hy ⊢
    exact hy
  · simp [hxy] at hy ⊢
    exact h y τ hy

/-! ## Source language -/

inductive Expr where
  | var (x : String)
  | int (n : Int)
  | bool (b : Bool)
  | neg (e : Expr)
  | arith (op : Arith) (a b : Expr)
  | cmp (op : Cmp) (a b : Expr)
  | eq (a b : Expr)
  | ne (a b : Expr)
  | not (e : Expr)
  | and (a b : Expr)
  | or (a b : Expr)
  | implies (a b : Expr)
  | ite (c t e : Expr)

inductive Block where
  | ret (e : Expr)
  | const (x : String) (e : Expr) (rest : Block)
  | ifElse (c : Expr) (t e : Block)

/-- JavaScript evaluation. `none` means the operation has no result on these values. -/
def eval (ρ : Env) : Expr → Option Val
  | .var x => ρ x
  | .int n => some (.int n)
  | .bool b => some (.bool b)
  | .neg e =>
    match eval ρ e with
    | some (.int n) => some (.int (-n))
    | _ => none
  | .arith op a b =>
    match eval ρ a, eval ρ b with
    | some (.int x), some (.int y) => some (.int (op.apply x y))
    | _, _ => none
  | .cmp op a b =>
    match eval ρ a, eval ρ b with
    | some (.int x), some (.int y) => some (.bool (op.apply x y))
    | _, _ => none
  | .eq a b =>
    match eval ρ a, eval ρ b with
    | some x, some y => (valEq x y).map Val.bool
    | _, _ => none
  | .ne a b =>
    match eval ρ a, eval ρ b with
    | some x, some y => (valEq x y).map (fun r => Val.bool (!r))
    | _, _ => none
  | .not e =>
    match eval ρ e with
    | some (.bool b) => some (.bool (!b))
    | _ => none
  -- `&&` and `||` do not evaluate their right operand when the left one decides.
  | .and a b =>
    match eval ρ a with
    | some (.bool false) => some (.bool false)
    | some (.bool true) =>
      match eval ρ b with
      | some (.bool q) => some (.bool q)
      | _ => none
    | _ => none
  | .or a b =>
    match eval ρ a with
    | some (.bool true) => some (.bool true)
    | some (.bool false) =>
      match eval ρ b with
      | some (.bool q) => some (.bool q)
      | _ => none
    | _ => none
  -- `implies` is an ordinary function: both arguments are evaluated.
  | .implies a b =>
    match eval ρ a, eval ρ b with
    | some (.bool p), some (.bool q) => some (.bool (!p || q))
    | _, _ => none
  | .ite c t e =>
    match eval ρ c with
    | some (.bool true) => eval ρ t
    | some (.bool false) => eval ρ e
    | _ => none

def evalBlock (ρ : Env) : Block → Option Val
  | .ret e => eval ρ e
  | .const x e rest =>
    match eval ρ e with
    | some v => evalBlock (ρ.set x v) rest
    | none => none
  | .ifElse c t e =>
    match eval ρ c with
    | some (.bool true) => evalBlock ρ t
    | some (.bool false) => evalBlock ρ e
    | _ => none

/-! ## Typing -/

inductive HasType : Ctx → Expr → Ty → Prop where
  | var {Γ x τ} : Γ x = some τ → HasType Γ (.var x) τ
  | int {Γ n} : HasType Γ (.int n) .int
  | bool {Γ b} : HasType Γ (.bool b) .bool
  | neg {Γ e} : HasType Γ e .int → HasType Γ (.neg e) .int
  | arith {Γ op a b} : HasType Γ a .int → HasType Γ b .int → HasType Γ (.arith op a b) .int
  | cmp {Γ op a b} : HasType Γ a .int → HasType Γ b .int → HasType Γ (.cmp op a b) .bool
  | eq {Γ a b τ} : HasType Γ a τ → HasType Γ b τ → HasType Γ (.eq a b) .bool
  | ne {Γ a b τ} : HasType Γ a τ → HasType Γ b τ → HasType Γ (.ne a b) .bool
  | not {Γ e} : HasType Γ e .bool → HasType Γ (.not e) .bool
  | and {Γ a b} : HasType Γ a .bool → HasType Γ b .bool → HasType Γ (.and a b) .bool
  | or {Γ a b} : HasType Γ a .bool → HasType Γ b .bool → HasType Γ (.or a b) .bool
  | implies {Γ a b} : HasType Γ a .bool → HasType Γ b .bool → HasType Γ (.implies a b) .bool
  | ite {Γ c t e τ} :
      HasType Γ c .bool → HasType Γ t τ → HasType Γ e τ → HasType Γ (.ite c t e) τ

/--
  Block typing also threads the type of each `const`, which is the type of its initializer.
-/
inductive HasTypeB : Ctx → Block → Ty → Prop where
  | ret {Γ e τ} : HasType Γ e τ → HasTypeB Γ (.ret e) τ
  | const {Γ x e rest σ τ} :
      HasType Γ e σ → HasTypeB (Γ.set x σ) rest τ → HasTypeB Γ (.const x e rest) τ
  | ifElse {Γ c t e τ} :
      HasType Γ c .bool → HasTypeB Γ t τ → HasTypeB Γ e τ → HasTypeB Γ (.ifElse c t e) τ

theorem int_of_ty {v : Val} (h : v.ty = .int) : ∃ n, v = .int n := by
  cases v with
  | int n => exact ⟨n, rfl⟩
  | bool b => simp [Val.ty] at h

theorem bool_of_ty {v : Val} (h : v.ty = .bool) : ∃ b, v = .bool b := by
  cases v with
  | int n => simp [Val.ty] at h
  | bool b => exact ⟨b, rfl⟩

theorem valEq_same_ty {x y : Val} (h : x.ty = y.ty) : ∃ r, valEq x y = some r := by
  cases x <;> cases y <;> simp [Val.ty] at h <;> simp [valEq]

/--
  Type soundness (totality): a well-typed expression has a value, of its type. This is the
  "typing assumption" of docs/SEMANTICS.md, proved here for the core calculus.
-/
theorem eval_typed {Γ : Ctx} {ρ : Env} {e : Expr} {τ : Ty}
    (h : HasType Γ e τ) (hρ : EnvOk Γ ρ) : ∃ v, eval ρ e = some v ∧ v.ty = τ := by
  induction h with
  | var hx => exact hρ _ _ hx
  | int => exact ⟨_, rfl, rfl⟩
  | bool => exact ⟨_, rfl, rfl⟩
  | neg _ ih =>
    obtain ⟨v, hv, ht⟩ := ih
    obtain ⟨n, rfl⟩ := int_of_ty ht
    exact ⟨.int (-n), by simp [eval, hv], rfl⟩
  | @arith op _ _ _ _ iha ihb =>
    obtain ⟨va, hva, hta⟩ := iha
    obtain ⟨vb, hvb, htb⟩ := ihb
    obtain ⟨x, rfl⟩ := int_of_ty hta
    obtain ⟨y, rfl⟩ := int_of_ty htb
    exact ⟨.int (op.apply x y), by simp [eval, hva, hvb], rfl⟩
  | @cmp op _ _ _ _ iha ihb =>
    obtain ⟨va, hva, hta⟩ := iha
    obtain ⟨vb, hvb, htb⟩ := ihb
    obtain ⟨x, rfl⟩ := int_of_ty hta
    obtain ⟨y, rfl⟩ := int_of_ty htb
    exact ⟨.bool (op.apply x y), by simp [eval, hva, hvb], rfl⟩
  | eq _ _ iha ihb =>
    obtain ⟨va, hva, hta⟩ := iha
    obtain ⟨vb, hvb, htb⟩ := ihb
    obtain ⟨r, hr⟩ := valEq_same_ty (hta.trans htb.symm)
    exact ⟨.bool r, by simp [eval, hva, hvb, hr], rfl⟩
  | ne _ _ iha ihb =>
    obtain ⟨va, hva, hta⟩ := iha
    obtain ⟨vb, hvb, htb⟩ := ihb
    obtain ⟨r, hr⟩ := valEq_same_ty (hta.trans htb.symm)
    exact ⟨.bool (!r), by simp [eval, hva, hvb, hr], rfl⟩
  | not _ ih =>
    obtain ⟨v, hv, ht⟩ := ih
    obtain ⟨b, rfl⟩ := bool_of_ty ht
    exact ⟨.bool (!b), by simp [eval, hv], rfl⟩
  | and _ _ iha ihb =>
    obtain ⟨va, hva, hta⟩ := iha
    obtain ⟨vb, hvb, htb⟩ := ihb
    obtain ⟨p, rfl⟩ := bool_of_ty hta
    obtain ⟨q, rfl⟩ := bool_of_ty htb
    cases p
    · exact ⟨.bool false, by simp [eval, hva], rfl⟩
    · exact ⟨.bool q, by simp [eval, hva, hvb], rfl⟩
  | or _ _ iha ihb =>
    obtain ⟨va, hva, hta⟩ := iha
    obtain ⟨vb, hvb, htb⟩ := ihb
    obtain ⟨p, rfl⟩ := bool_of_ty hta
    obtain ⟨q, rfl⟩ := bool_of_ty htb
    cases p
    · exact ⟨.bool q, by simp [eval, hva, hvb], rfl⟩
    · exact ⟨.bool true, by simp [eval, hva], rfl⟩
  | implies _ _ iha ihb =>
    obtain ⟨va, hva, hta⟩ := iha
    obtain ⟨vb, hvb, htb⟩ := ihb
    obtain ⟨p, rfl⟩ := bool_of_ty hta
    obtain ⟨q, rfl⟩ := bool_of_ty htb
    exact ⟨.bool (!p || q), by simp [eval, hva, hvb], rfl⟩
  | ite _ _ _ ihc iht ihe =>
    obtain ⟨vc, hvc, htc⟩ := ihc
    obtain ⟨c, rfl⟩ := bool_of_ty htc
    cases c
    · obtain ⟨v, hv, ht⟩ := ihe
      exact ⟨v, by simp [eval, hvc, hv], ht⟩
    · obtain ⟨v, hv, ht⟩ := iht
      exact ⟨v, by simp [eval, hvc, hv], ht⟩

/-! ## Target language: solver terms -/

inductive Term where
  | var (x : String)
  | int (n : Int)
  | bool (b : Bool)
  | neg (t : Term)
  | arith (op : Arith) (a b : Term)
  | cmp (op : Cmp) (a b : Term)
  | eq (a b : Term)
  | not (t : Term)
  | and (a b : Term)
  | or (a b : Term)
  | imp (a b : Term)
  | ite (c t e : Term)
  | letE (x : String) (v body : Term)

/--
  Meaning of a term in a model. Unlike `eval`, nothing is skipped: `and`, `or`, `imp` and
  `ite` need a value for every subterm, as in SMT-LIB, where all functions are total.
-/
def denote (M : Env) : Term → Option Val
  | .var x => M x
  | .int n => some (.int n)
  | .bool b => some (.bool b)
  | .neg t =>
    match denote M t with
    | some (.int n) => some (.int (-n))
    | _ => none
  | .arith op a b =>
    match denote M a, denote M b with
    | some (.int x), some (.int y) => some (.int (op.apply x y))
    | _, _ => none
  | .cmp op a b =>
    match denote M a, denote M b with
    | some (.int x), some (.int y) => some (.bool (op.apply x y))
    | _, _ => none
  | .eq a b =>
    match denote M a, denote M b with
    | some x, some y => (valEq x y).map Val.bool
    | _, _ => none
  | .not t =>
    match denote M t with
    | some (.bool b) => some (.bool (!b))
    | _ => none
  | .and a b =>
    match denote M a, denote M b with
    | some (.bool p), some (.bool q) => some (.bool (p && q))
    | _, _ => none
  | .or a b =>
    match denote M a, denote M b with
    | some (.bool p), some (.bool q) => some (.bool (p || q))
    | _, _ => none
  | .imp a b =>
    match denote M a, denote M b with
    | some (.bool p), some (.bool q) => some (.bool (!p || q))
    | _, _ => none
  | .ite c t e =>
    match denote M c, denote M t, denote M e with
    | some (.bool p), some x, some y => some (if p then x else y)
    | _, _, _ => none
  | .letE x v body =>
    match denote M v with
    | some w => denote (M.set x w) body
    | none => none

/-! ## Translation (the shape of `src/smt.ts`) -/

def tr : Expr → Term
  | .var x => .var x
  | .int n => .int n
  | .bool b => .bool b
  | .neg e => .neg (tr e)
  | .arith op a b => .arith op (tr a) (tr b)
  | .cmp op a b => .cmp op (tr a) (tr b)
  | .eq a b => .eq (tr a) (tr b)
  | .ne a b => .not (.eq (tr a) (tr b))
  | .not e => .not (tr e)
  | .and a b => .and (tr a) (tr b)
  | .or a b => .or (tr a) (tr b)
  | .implies a b => .imp (tr a) (tr b)
  | .ite c t e => .ite (tr c) (tr t) (tr e)

def trBlock : Block → Term
  | .ret e => tr e
  | .const x e rest => .letE x (tr e) (trBlock rest)
  | .ifElse c t e => .ite (tr c) (trBlock t) (trBlock e)

/-! ## The translation agrees with evaluation -/

theorem tr_correct {Γ : Ctx} {ρ : Env} {e : Expr} {τ : Ty}
    (h : HasType Γ e τ) (hρ : EnvOk Γ ρ) : denote ρ (tr e) = eval ρ e := by
  induction h with
  | var _ => rfl
  | int => rfl
  | bool => rfl
  | neg _ ih => simp [tr, denote, eval, ih]
  | arith _ _ iha ihb => simp [tr, denote, eval, iha, ihb]
  | cmp _ _ iha ihb => simp [tr, denote, eval, iha, ihb]
  | eq _ _ iha ihb => simp [tr, denote, eval, iha, ihb]
  | ne ha hb iha ihb =>
    obtain ⟨va, hva, hta⟩ := eval_typed ha hρ
    obtain ⟨vb, hvb, htb⟩ := eval_typed hb hρ
    obtain ⟨r, hr⟩ := valEq_same_ty (hta.trans htb.symm)
    simp [tr, denote, eval, iha, ihb, hva, hvb, hr]
  | not _ ih => simp [tr, denote, eval, ih]
  | and ha hb iha ihb =>
    -- The right operand has a value even when JavaScript would not have evaluated it.
    obtain ⟨va, hva, hta⟩ := eval_typed ha hρ
    obtain ⟨vb, hvb, htb⟩ := eval_typed hb hρ
    obtain ⟨p, rfl⟩ := bool_of_ty hta
    obtain ⟨q, rfl⟩ := bool_of_ty htb
    cases p <;> simp [tr, denote, eval, iha, ihb, hva, hvb]
  | or ha hb iha ihb =>
    obtain ⟨va, hva, hta⟩ := eval_typed ha hρ
    obtain ⟨vb, hvb, htb⟩ := eval_typed hb hρ
    obtain ⟨p, rfl⟩ := bool_of_ty hta
    obtain ⟨q, rfl⟩ := bool_of_ty htb
    cases p <;> simp [tr, denote, eval, iha, ihb, hva, hvb]
  | implies _ _ iha ihb => simp [tr, denote, eval, iha, ihb]
  | ite hc ht he ihc iht ihe =>
    obtain ⟨vc, hvc, htc⟩ := eval_typed hc hρ
    obtain ⟨vt, hvt, _⟩ := eval_typed ht hρ
    obtain ⟨ve, hve, _⟩ := eval_typed he hρ
    obtain ⟨c, rfl⟩ := bool_of_ty htc
    cases c <;> simp [tr, denote, eval, ihc, iht, ihe, hvc, hvt, hve]

theorem evalBlock_typed {Γ : Ctx} {ρ : Env} {b : Block} {τ : Ty}
    (h : HasTypeB Γ b τ) (hρ : EnvOk Γ ρ) : ∃ v, evalBlock ρ b = some v ∧ v.ty = τ := by
  induction h generalizing ρ with
  | ret he => exact eval_typed he hρ
  | const he _ ih =>
    obtain ⟨v, hv, ht⟩ := eval_typed he hρ
    subst ht
    obtain ⟨w, hw, hwt⟩ := ih (hρ.set _ v)
    exact ⟨w, by simp [evalBlock, hv, hw], hwt⟩
  | ifElse hc _ _ iht ihe =>
    obtain ⟨vc, hvc, htc⟩ := eval_typed hc hρ
    obtain ⟨c, rfl⟩ := bool_of_ty htc
    cases c
    · obtain ⟨v, hv, ht⟩ := ihe hρ
      exact ⟨v, by simp [evalBlock, hvc, hv], ht⟩
    · obtain ⟨v, hv, ht⟩ := iht hρ
      exact ⟨v, by simp [evalBlock, hvc, hv], ht⟩

theorem trBlock_correct {Γ : Ctx} {ρ : Env} {b : Block} {τ : Ty}
    (h : HasTypeB Γ b τ) (hρ : EnvOk Γ ρ) : denote ρ (trBlock b) = evalBlock ρ b := by
  induction h generalizing ρ with
  | ret he => exact tr_correct he hρ
  | const he _ ih =>
    obtain ⟨v, hv, ht⟩ := eval_typed he hρ
    subst ht
    simp [trBlock, denote, evalBlock, tr_correct he hρ, hv, ih (hρ.set _ v)]
  | ifElse hc ht he iht ihe =>
    obtain ⟨vc, hvc, htc⟩ := eval_typed hc hρ
    obtain ⟨vt, hvt, _⟩ := evalBlock_typed ht hρ
    obtain ⟨ve, hve, _⟩ := evalBlock_typed he hρ
    obtain ⟨c, rfl⟩ := bool_of_ty htc
    cases c <;> simp [trBlock, denote, evalBlock, tr_correct hc hρ, iht hρ, ihe hρ, hvc, hvt, hve]

/-! ## Verdicts

  A law `law(name, (x1: T1, ..., xn: Tn) => body)` has parameter context `Γ` and a body of
  type `boolean`. The query asserts `(not body)` and asks for a model, which assigns each
  declared constant a value of its sort: exactly an environment `M` with `EnvOk Γ M`.
-/

/-- The query sent to the solver. -/
def query (body : Block) : Term := .not (trBlock body)

/-- The solver's `unsat`: no well-sorted model makes the query true. -/
def Unsat (Γ : Ctx) (t : Term) : Prop :=
  ∀ M, EnvOk Γ M → denote M t ≠ some (.bool true)

/-- PROVED is sound: if the query is unsatisfiable, the law holds for all well-typed inputs. -/
theorem proved_sound {Γ : Ctx} {body : Block}
    (hty : HasTypeB Γ body .bool) (hunsat : Unsat Γ (query body)) :
    ∀ ρ, EnvOk Γ ρ → evalBlock ρ body = some (.bool true) := by
  intro ρ hρ
  obtain ⟨v, hv, ht⟩ := evalBlock_typed hty hρ
  obtain ⟨b, rfl⟩ := bool_of_ty ht
  cases b
  · exfalso
    apply hunsat ρ hρ
    simp [query, denote, trBlock_correct hty hρ, hv]
  · exact hv

/--
  DISPROVED is sound: a model of the query is a well-typed input on which the law's body
  evaluates to `false`.
-/
theorem disproved_sound {Γ : Ctx} {body : Block} {M : Env}
    (hty : HasTypeB Γ body .bool) (hM : EnvOk Γ M)
    (hsat : denote M (query body) = some (.bool true)) :
    evalBlock M body = some (.bool false) := by
  obtain ⟨v, hv, ht⟩ := evalBlock_typed hty hM
  obtain ⟨b, rfl⟩ := bool_of_ty ht
  cases b
  · exact hv
  · simp [query, denote, trBlock_correct hty hM, hv] at hsat

/-- The two verdicts exclude each other. -/
theorem verdicts_exclusive {Γ : Ctx} {body : Block} {M : Env}
    (hunsat : Unsat Γ (query body)) (hM : EnvOk Γ M) :
    denote M (query body) ≠ some (.bool true) :=
  hunsat M hM

end Tslaw
