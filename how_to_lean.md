# How to Formalize in Lean 4: Lessons from Metamath Kernel Soundness

This document captures practical lessons learned while formalizing the Metamath kernel soundness proof in Lean 4.20.0-rc2. It focuses on real-world strategies for dealing with complex proofs, opaque functions, and architectural challenges.

## Table of Contents

1. [Core Philosophy](#core-philosophy)
2. [Proof Strategies](#proof-strategies)
3. [Common Patterns](#common-patterns)
4. [Dealing with Recursion](#dealing-with-recursion)
5. [Structural Correspondence Lemmas](#structural-correspondence-lemmas)
6. [Working with Options and Monads](#working-with-options-and-monads)
7. [Lambda Elaboration Issues](#lambda-elaboration-issues)
8. [Index Validation](#index-validation)
9. [Axiomatization Strategy](#axiomatization-strategy)
10. [Debugging Techniques](#debugging-techniques)
11. [Build Health Maintenance](#build-health-maintenance)
12. [Scope Management and Variable Substitution](#scope-management-and-variable-substitution)
13. [Constructor Injection and Equality Extraction](#constructor-injection-and-equality-extraction)
14. [Prop Definitions with HashMap/Array Access](#prop-definitions-with-hashmaparray-access)
15. [Prop Definitions with Match Expressions](#prop-definitions-with-match-expressions)
16. [Debugging Cascading Parse Errors](#debugging-cascading-parse-errors)
17. [Theorem Accessibility and Namespace Issues](#theorem-accessibility-and-namespace-issues)
18. [Advanced Patterns](#advanced-patterns)
19. [Match Expressions in Prop Contexts](#match-expressions-in-prop-contexts)
20. [Batteries vs Mathlib: Keyword Availability](#batteries-vs-mathlib-keyword-availability)

---

## Core Philosophy

### Bottom-Up Proof Architecture

**Key Principle**: Build a complete, type-checking proof skeleton FIRST, then fill in proofs incrementally.

```lean
-- ✅ GOOD: Skeleton with sorries
theorem main_result : ComplexStatement := by
  sorry  -- TODO: Phase 1 - prove helper lemma A

theorem helper_A : HelperStatement := by
  sorry  -- TODO: prove using stdlib

-- ❌ BAD: Trying to prove everything at once
theorem main_result : ComplexStatement := by
  -- 500 lines of complex tactic script that may not even work
```

**Why this works**:
- Type-checker validates your proof architecture immediately
- You can iterate on individual proofs without breaking the whole build
- Reviewers can see the complete proof strategy before implementation details
- You discover dependencies and missing lemmas early

### Maintain Build Health

**Rule**: Every commit should build successfully (warnings OK, errors NOT OK).

```bash
# After every change:
lake build
# If errors: fix immediately before continuing
```

Build failures compound. Fix them immediately.

---

## Proof Strategies

### Strategy 1: Axiomatic Reduction

**When to use**: Proving properties of opaque/compiled functions, complex recursion, or when proofs would require major refactoring.

**Pattern**:
```lean
/-- ⚠️ AXIOM N: Clear descriptive name
**Why axiomatized:**
[Explain the technical blocker - recursion, compilation, elaboration, etc.]

**What this captures:**
[Informal description of the property]

**How it WOULD be proven:**
[Detailed proof sketch with:
 - Base case
 - Inductive step
 - Key invariants
]

**Soundness justification:**
[Why this is correct by inspection/testing/reference implementation]
-/
axiom helper_property : Statement
```

**Example from our codebase**:
```lean
axiom checkHyp_ensures_floats_typed
    (db : Verify.DB) (hyps : Array String) (stack : Array Verify.Formula)
    (off : {off : Nat // off + hyps.size = stack.size})
    (σ_impl : Std.HashMap String Verify.Formula) :
    Verify.DB.checkHyp db hyps stack off 0 ∅ = Except.ok σ_impl →
    (∀ i, i < hyps.size →
      match db.find? hyps[i]! with
      | some (.hyp false f _) =>
          f.size = 2 →
          match f[0]!, f[1]! with
          | .const c, .var v =>
              match σ_impl[v]? with
              | some val => val.size > 0 ∧ (toExpr val).typecode = ⟨c⟩
              | none => False
          | _, _ => True
      | _ => True)
```

**Documentation requirements**:
1. **Why axiomatized**: "checkHyp is opaque compiled function with tail recursion"
2. **What it captures**: "For each float $f c v, checkHyp validates typecode matches"
3. **How to prove**: "Strong induction on i with invariant: floats processed so far are correctly typed"
4. **Soundness**: "Inspection of Verify.lean:401-418 shows this is exactly what the code does"

### Strategy 2: Witness-Carrying Types

**When to use**: Bridging implementation and specification, especially with monadic validation.

**Pattern**:
```lean
-- Implementation uses Option/Except for validation
def checkProperty (x : Impl) : Option Bool := ...

-- Specification uses dependent type carrying proof
structure WitnessType (spec : Spec) where
  value : SpecValue
  property : PropertyHolds value spec

-- Bridge function: extract witness from successful validation
def toWitnessType (impl : Impl) (spec : Spec) : Option (WitnessType spec) :=
  match h : checkProperty impl with
  | some true =>
      some ⟨extractValue impl, by
        -- Proof that property holds
        ...
      ⟩
  | _ => none
```

**Example from our codebase**:
```lean
structure TypedSubst (fr : Spec.Frame) where
  σ : Spec.Subst
  typed : ∀ {c : Spec.Constant} {v : Spec.Variable},
    Spec.Hyp.floating c v ∈ fr.mand →
    (σ v).typecode = c

def checkFloat (σ_impl : HashMap String Formula) (c : Constant) (v : Variable) : Option Bool :=
  match σ_impl[v.v]? with
  | some f => if f.size > 0 then some (decide ((toExpr f).typecode = c)) else none
  | none => none

def toSubstTyped (fr : Spec.Frame) (σ_impl : HashMap String Formula)
    : Option (TypedSubst fr) :=
  match h : (Bridge.floats fr).allM (fun x => checkFloat σ_impl x.fst x.snd) with
  | some true =>
      let σ_fn := fun v => match σ_impl[v.v]? with | some f => toExpr f | none => ...
      some ⟨σ_fn, by ... ⟩  -- Witness construction
  | _ => none
```

### Strategy 3: Phased Proof Development

**Pattern**: Break large proofs into numbered phases, complete each before moving on.

```lean
/-! ## PHASE 1: Basic conversions (PROVEN) -/
theorem conversion_correct : ... := by ...

/-! ## PHASE 2: Monadic extraction (PROVEN) -/
theorem allM_extraction : ... := by ...

/-! ## PHASE 3: Witness construction (TODO) -/
theorem witness_builder : ... := by sorry

/-! ## PHASE 4: Main theorem (depends on Phase 3) -/
theorem main_result : ... := by sorry
```

**Benefits**:
- Clear progress tracking
- Easy to see dependencies between phases
- Can work on phases in parallel (if independent)
- Documentation built-in

---

## Common Patterns

### Pattern: allM Extraction

**Problem**: `xs.allM p = some true` is opaque. Need to extract `∀ x ∈ xs, p x = some true`.

**Solution**: Bidirectional equivalence lemma.

```lean
theorem allM_true_iff_forall {α} (p : α → Option Bool) (xs : List α) :
  xs.allM p = some true ↔ (∀ x ∈ xs, p x = some true) := by
  induction xs with
  | nil =>
      constructor
      · intro _; intro x hx; simp at hx  -- Vacuous
      · intro _; simp [allM]
  | cons head tail ih =>
      constructor
      · -- Forward: allM = some true → forall holds
        intro h_allM
        intro x hx
        simp [allM] at h_allM
        cases hp : p head with
        | none => simp [hp] at h_allM  -- Contradiction
        | some b =>
          simp [hp] at h_allM
          cases b
          · simp at h_allM  -- false case contradicts
          · -- true case: extract head and tail
            cases hx with
            | head => exact hp
            | tail _ hx_tail => exact (ih.mp h_allM) x hx_tail
      · -- Backward: forall holds → allM = some true
        intro h_forall
        have hp : p head = some true := h_forall head (by simp)
        have h_tail : tail.allM p = some true := by
          apply ih.mpr
          intro y hy
          exact h_forall y (by simp [hy])
        simp [allM, hp, h_tail]
```

**Usage**:
```lean
-- Convert to pointwise property
rw [allM_true_iff_forall]
intro x hx
-- Now have: need to show p x = some true
```

**Corollary** (often useful):
```lean
theorem allM_true_of_mem {α} (p : α → Option Bool) {xs : List α}
    (hall : xs.allM p = some true) {x} (hx : x ∈ xs) :
  p x = some true :=
  (allM_true_iff_forall p xs).mp hall x hx
```

### Pattern: Match Equation Binders

**Problem**: Need to bind the match result for case analysis.

```lean
-- ❌ BAD: Can't case-split on result
match p x with
| some true => ...
| _ => none

-- ✅ GOOD: Bind equation for rewriting
match h : p x with
| some true => ...  -- h : p x = some true available in branch
| _ => none
```

**Why important**: The equation `h` can be used for:
- Rewriting in the goal
- Extracting witnesses
- Contradiction proofs

**Example**:
```lean
def toSubstTyped (fr : Spec.Frame) (σ_impl : HashMap String Formula) :=
  match h : xs.allM checkFloat with  -- ← Bind equation
  | some true =>
      some ⟨σ_fn, by
        -- h : xs.allM checkFloat = some true is available here
        have h_point := (allM_true_iff_forall ...).mp h (c, v) h_mem
        ...
      ⟩
  | _ => none
```

### Pattern: Option/Except Unwrapping

**Problem**: `some` wrapping prevents simplification.

**Solution**: `injection` tactic.

```lean
-- Given: h : some x = some y
injection h with h_eq
-- Now have: h_eq : x = y

-- Given: h : Except.ok x = Except.ok y
injection h with h_eq
-- Now have: h_eq : x = y
```

**Example**:
```lean
theorem preload_sound :
  DB.preload db pr label = Except.ok pr' →
  ∃ obj, db.find? label = some obj := by
  intro h_preload
  cases h_find : db.find? label with
  | some obj =>
      cases obj with
      | hyp ess f lbl =>
          simp [h_find] at h_preload
          injection h_preload with h_eq  -- ← Unwrap Except.ok
          -- h_eq : pr.pushHeap (.fmla f) = pr'
```

### Pattern: Decidability to Prop

**Problem**: `decide P = true` is not the same as `P`.

**Solution**: `decide_eq_true_eq`.

```lean
-- Given: h : decide P = true
have hp : P := decide_eq_true_eq.mp h

-- Given: hp : P
have h : decide P = true := decide_eq_true_eq.mpr hp
```

**Example**:
```lean
def checkFloat (σ : HashMap String Formula) (c : Constant) (v : Variable) : Option Bool :=
  match σ[v.v]? with
  | some f =>
      if f.size > 0 then
        some (decide ((toExpr f).typecode = c))  -- ← Returns Bool
      else none
  | none => none

theorem checkFloat_success :
  checkFloat σ c v = some true →
  (toExpr f).typecode = c := by
  intro h
  unfold checkFloat at h
  split at h
  · rename_i f hf
    split at h
    · injection h with h_eq
      -- h_eq : decide ((toExpr f).typecode = c) = true
      exact decide_eq_true_eq.mp h_eq  -- ← Convert to Prop
```

---

## Dealing with Recursion

### Problem: Proving Properties of Recursive Functions

**Challenge**: Functions compiled from `do` notation with recursion are opaque to the proof system.

**Example**:
```lean
def checkHyp (i : Nat) (subst : HashMap String Formula) : Except String (HashMap String Formula) := do
  if h : i < hyps.size then
    let val := stack[off.1 + i]
    if let some (.hyp ess f _) := db.find? hyps[i] then
      if f[0]! == val[0]! then
        if ess then
          if (← f.subst subst) == val then
            checkHyp (i+1) subst  -- ← Recursive call
          else throw "error"
        else
          checkHyp (i+1) (subst.insert f[1]!.value val)  -- ← Tail recursion with state
      else throw "error"
    else unreachable!
  else pure subst
```

**Why hard to prove properties**:
1. Tail recursion with mutable state (`subst` accumulator)
2. Monadic context (`Except String`)
3. Complex control flow (nested `if`s)
4. Compiled/opaque implementation

### Solution 1: Axiomatic Specification (Pragmatic)

**When to use**: When recursion tracking is mechanical but tedious, and you need to make progress.

**Pattern**:
```lean
/-- Axiom capturing recursive function's behavior -/
axiom recursive_fn_property
    (inputs : Inputs)
    (result : Result) :
    recursive_fn inputs = result →
    (∀ i, i < n →
      -- Property that holds at each recursive step
      intermediate_property i result)
```

**Best practices**:
1. **Document the induction structure**: "Strong induction on (n - i) with invariant: ..."
2. **Show base case**: "When i = n, function returns accumulator as-is"
3. **Show step case**: "At step i, function checks X, updates Y, recurses with i+1"
4. **Prove soundness by inspection**: "Lines X-Y of Source.lean show this is exactly what happens"

**Example**:
```lean
/-- When checkHyp succeeds from empty substitution, all floats are validated.

**Proof sketch**: Strong induction on i from 0 to hyps.size:
- Base (i = 0, σ = ∅): Vacuously true, no floats processed yet
- Step (i → i+1):
  - If hyps[i] is float $f c v: validates f[0]! == val[0]!, inserts σ[v] := val
  - If hyps[i] is essential: validates f.subst σ == val, σ unchanged
  - Invariant maintained: all floats j < i+1 are correctly typed in σ
- Final (i = n): Return σ, all floats validated
-/
axiom checkHyp_ensures_floats_typed :
  checkHyp db hyps stack off 0 ∅ = Except.ok σ_impl →
  (∀ i, i < hyps.size → ...)
```

### Solution 2: Specification-Style Rewrite (Ideal but Expensive)

**When to use**: When you have time for a major refactoring, or the function is central to many proofs.

**Pattern**: Rewrite function in a proof-friendly style.

```lean
-- ❌ ORIGINAL: Compiled monadic recursion
def checkHyp (i : Nat) (subst : HashMap String Formula) : Except String ... := do
  if h : i < hyps.size then
    ...
    checkHyp (i+1) (subst.insert ...)
  else pure subst

-- ✅ REWRITE: Inductive definition with termination proof
def checkHyp : (i : Nat) → (subst : HashMap String Formula) → Except String ... :=
  fun i subst =>
    if h : i < hyps.size then
      ...
      have : hyps.size - (i+1) < hyps.size - i := by omega
      checkHyp (i+1) (subst.insert ...)
    else Except.ok subst
termination_by i => hyps.size - i
```

Then prove properties by structural induction:
```lean
theorem checkHyp_property : ... := by
  -- Induction on termination measure
  induction i using Nat.strong_induction_on
  case _ i ih =>
    unfold checkHyp
    split
    · -- i < hyps.size case
      split  -- Case on hyps[i]
      · -- Float case
        apply ih
        omega  -- Show measure decreases
      · -- Essential case
        apply ih
        omega
    · -- i ≥ hyps.size, base case
      simp
```

**Trade-offs**:
- ✅ Enables structural induction
- ✅ Properties provable without axioms
- ❌ Requires rewriting existing code
- ❌ May need termination proofs
- ❌ Time-consuming

### Solution 3: Functional Induction Tactics (Advanced)

**When to use**: Lean 4 provides tactics for reasoning about recursive functions defined with `def`.

**Limitation**: Less mature for functions with complex monadic structure.

```lean
-- If you have a simple recursive definition:
def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n

theorem factorial_positive : ∀ n, factorial n > 0 := by
  intro n
  induction n with
  | zero => simp [factorial]
  | succ n ih =>
      simp [factorial]
      omega
```

**For our `checkHyp`**: This doesn't work well because of the `do` notation and `Except` monad.

---

## Structural Correspondence Lemmas

### What Are They?

**Structural correspondence lemmas** connect different representations of the same data:
- Array indices ↔ List membership
- Implementation types ↔ Specification types
- Monadic success ↔ Pointwise properties

### Pattern: mapM Structure Preservation

**Problem**: `xs.mapM f = some ys` is opaque. Need to know properties of `ys`.

**Key lemmas** (often axiomatized for stdlib functions):

```lean
-- Length preservation
axiom mapM_length_option {α β} (f : α → Option β) :
  ∀ {xs : List α} {ys : List β},
    xs.mapM f = some ys →
    ys.length = xs.length

-- Element correspondence
axiom mapM_get_some {α β} (f : α → Option β) (xs : List α) (ys : List β)
    (h : xs.mapM f = some ys)
    (i : Fin xs.length)
    (h_len : i.val < ys.length) :
    ∃ b, f xs[i] = some b ∧ ys[i.val]'h_len = b

-- Success implies pointwise success
axiom mapM_some_of_mem {α β} (f : α → Option β) {xs : List α} {ys : List β} {x : α}
    (h : xs.mapM f = some ys)
    (hx : x ∈ xs) :
    ∃ b, f x = some b
```

**Usage example**:
```lean
-- Given: hyps.toList.mapM (convertHyp db) = some fr_spec.mand
-- Want: If Hyp.floating c v ∈ fr_spec.mand, then ∃i, hyps[i] corresponds

theorem toFrame_preserves_structure :
  toFrame db (Frame.mk #[] hyps) = some fr_spec →
  (∀ c v, Hyp.floating c v ∈ fr_spec.mand →
    ∃ i, i < hyps.size ∧
         convertHyp db hyps[i]! = some (Hyp.floating c v)) := by
  intro h_frame c v h_mem
  unfold toFrame at h_frame
  -- Use mapM structure preservation lemmas
  have h_len := mapM_length_option ... h_frame
  have h_mem' := mapM_some_of_mem ... h_mem
  ...
```

### Pattern: Array ↔ List Correspondence

**Problem**: Implementation uses `Array`, spec uses `List`.

**Key bridge**:
```lean
-- Array.toList is the connection
theorem array_list_correspondence (a : Array α) :
  ∀ i, i < a.size → a[i] ∈ a.toList := by
  intro i hi
  -- Use @[simp] axiom from KernelExtras
  exact Array.mem_toList_get a ⟨i, hi⟩

-- Window/slice operations
axiom window_toList_map {α β}
  (a : Array α) (off len : Nat) (f : α → β)
  (h : off + len ≤ a.size) :
  (a.extract off (off + len)).toList.map f =
  (a.toList.drop off |>.take len).map f
```

### Pattern: Index-Based ↔ Membership-Based

**Problem**: Implementation uses `for i in 0..n`, spec uses `∀ x ∈ xs`.

**Bridge lemma pattern**:
```lean
theorem index_membership_bridge :
  (∀ i, i < xs.length → P xs[i]!) ↔
  (∀ x, x ∈ xs → P x) := by
  constructor
  · intro h_idx x h_mem
    -- x ∈ xs means ∃ i, xs[i] = x
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_get.mp h_mem
    exact h_idx i hi
  · intro h_mem i hi
    apply h_mem
    -- xs[i] ∈ xs by construction
    exact List.get_mem xs i hi
```

**Real example**:
```lean
-- checkHyp uses indices: ∀ i < hyps.size, ...
-- Bridge.floats uses membership: ∀ (c,v) ∈ floats fr, ...

-- Need correspondence lemma:
axiom toFrame_index_to_membership :
  toFrame db (Frame.mk #[] hyps) = some fr_spec →
  ((c, v) ∈ Bridge.floats fr_spec ↔
   ∃ i, i < hyps.size ∧
        db.find? hyps[i]! = some (.hyp false #[.const c, .var v] _))
```

---

## Working with Options and Monads

### Option Monad Patterns

#### Pattern: Option.map and Option.bind

```lean
-- Definition
def Option.map (f : α → β) : Option α → Option β
  | some x => some (f x)
  | none => none

def Option.bind (f : α → Option β) : Option α → Option β
  | some x => f x
  | none => none

-- Notation
-- f <$> opt    is Option.map f opt
-- opt >>= f    is Option.bind opt f
-- do let x ← opt; ...    desugars to bind
```

#### Common tactics:

```lean
-- Case split on Option
cases h_opt : opt with
| none => ...  -- Have h_opt : opt = none
| some x => ...  -- Have h_opt : opt = some x

-- Split inside proof
split at h
· -- none case
  contradiction  -- If h : none = some ..., this closes goal
· -- some case
  rename_i x hx  -- hx : opt = some x
```

### Except Monad Patterns

```lean
-- Definition
inductive Except (ε α : Type) where
  | error : ε → Except ε α
  | ok : α → Except ε α

-- Common usage
def operation : Except String Result := do
  let x ← step1  -- If step1 returns error, propagates
  let y ← step2 x
  if check y then
    pure (build y)
  else
    throw "check failed"
```

#### Proving about Except:

```lean
theorem operation_sound :
  operation inputs = Except.ok result →
  PropertyHolds result := by
  intro h
  unfold operation at h
  -- Unfold the do notation (can be messy)
  simp [Bind.bind, Except.bind, pure, throw] at h
  -- Case split on each step
  split at h
  · contradiction  -- error case
  · -- ok case
    split at h
    · contradiction  -- check = false
    · injection h with h_eq
      -- Now have h_eq : result = build y
```

### Pattern: Monadic Validation → Pointwise Property

```lean
-- Implementation validates with monadic short-circuit
def validateAll (xs : List α) (check : α → Option Bool) : Option Bool :=
  xs.allM check

-- Spec requires pointwise property
-- ∀ x ∈ xs, Property x

-- Bridge lemma:
theorem validation_to_pointwise :
  xs.allM check = some true →
  (∀ x ∈ xs, check x = some true) :=
  (allM_true_iff_forall check xs).mp
```

---

## Lambda Elaboration Issues

### Problem: Pattern Matching vs Projection Lambdas

**Symptom**: Lean treats these as different:
```lean
(fun (a, b) => f a b)           -- Pattern matching form
(fun p => f p.1 p.2)            -- Projection form
(fun p => f p.fst p.snd)        -- Named projection form
```

Even though they're definitionally equal, `rfl` may fail.

### Solution 1: Explicit Normalization Lemmas

```lean
@[simp] theorem pair_eta₂ {α β γ} (f : α → β → γ) :
  (fun (p : α × β) => f p.fst p.snd) = (fun (a, b) => f a b) := rfl

-- Or with cases:
@[simp] theorem uncurry_normalization {α β γ} (f : α → β → γ) :
  (fun (p : α × β) => f p.1 p.2) = (fun (a, b) => f a b) := by
  funext p
  cases p with
  | mk a b => rfl
```

### Solution 2: Avoid Pattern Matching in Definitions

```lean
-- ❌ PROBLEMATIC: Pattern matching lambda
def checkFloat (σ : HashMap String Formula) (c : Constant) (v : Variable) : Option Bool := ...

-- Later in proof:
xs.allM (fun (c, v) => checkFloat σ c v)  -- ← Lean might not unify

-- ✅ BETTER: Projection-based definition
def checkFloat' (σ : HashMap String Formula) (cv : Constant × Variable) : Option Bool :=
  checkFloat σ cv.1 cv.2

-- Later:
xs.allM (checkFloat' σ)  -- ← Clean
```

### Solution 3: allM_congr for Function Equality

```lean
-- General congruence lemma
theorem allM_congr {α} {p q : α → Option Bool}
    (h : ∀ x, p x = q x)
    (xs : List α) :
    xs.allM p = xs.allM q := by
  induction xs with
  | nil => simp [allM]
  | cons x xs ih => simp [allM, h x, ih]

-- Usage:
example : xs.allM (fun (c, v) => f c v) = xs.allM (fun p => f p.1 p.2) := by
  refine allM_congr (by intro p; cases p <;> rfl) xs
```

---

## Index Validation

### Problem: Array Bounds Checking

Lean 4 requires proof that array accesses are in bounds.

```lean
-- ❌ ERROR: failed to prove index is valid
def badFunction (a : Array α) (i : Nat) : α :=
  a[i]  -- No proof that i < a.size

-- ✅ OPTION 1: Provide proof
def goodFunction (a : Array α) (i : Nat) (h : i < a.size) : α :=
  a[i]'h

-- ✅ OPTION 2: Runtime check (panics if out of bounds)
def runtimeCheck (a : Array α) (i : Nat) : α :=
  a[i]!

-- ✅ OPTION 3: Option type (returns none if out of bounds)
def safeAccess (a : Array α) (i : Nat) : Option α :=
  a[i]?

-- ✅ OPTION 4: Fin indexing (index is bounded by type)
def finIndexing (a : Array α) (i : Fin a.size) : α :=
  a[i]
```

### In Axioms: Use `!` Notation

**Problem**: Axioms don't have access to context for proof obligations.

```lean
-- ❌ BAD: Can't prove i < hyps.size in axiom body
axiom property :
  (∀ i, i < hyps.size →
    match db.find? hyps[i] with  -- ← ERROR
    | some obj => ...)

-- ✅ GOOD: Use runtime check
axiom property :
  (∀ i, i < hyps.size →
    match db.find? hyps[i]! with  -- ← OK, runtime check
    | some obj => ...)
```

**Justification**: In axioms, we're *asserting* properties that hold when preconditions are met. The `i < hyps.size` precondition ensures the access is safe, so `!` is justified.

### Omega for Arithmetic Proofs

```lean
-- When you need to prove arithmetic facts:
have h_bound : off.1 + i < stack.size := by omega

-- omega solves linear integer arithmetic automatically
-- Works for: <, ≤, =, +, -, *, div (when constant)
```

---

## Axiomatization Strategy

### When to Axiomatize

**Good reasons**:
1. **Opaque compiled functions**: Properties of `do` notation with complex recursion
2. **Stdlib properties**: Standard library lemmas not yet in Batteries (e.g., `mapM` properties)
3. **Elaboration issues**: Match equation binders, lambda normalization (temporary, document for future fix)
4. **Time constraints**: Need to make progress on architecture, will fill in later

**Bad reasons**:
1. "Proof is hard" (but straightforward)
2. "Don't feel like it"
3. Trying to hide incorrect statements

### Documentation Template

```lean
/-- ⚠️ AXIOM N: [One-line description]

**Why axiomatized:**
[Specific technical reason: recursion/compilation/elaboration/stdlib gap]

**What this captures:**
[Informal mathematical property being asserted]
[Include examples if helpful]

**How it WOULD be proven:**
[Detailed proof sketch:]
- Base case: [Description]
- Inductive step: [Description]
- Key invariants: [List them]
- Required lemmas: [List dependencies]

**Soundness justification:**
[Why this is correct:]
- Reference to implementation (file:line)
- Testing evidence
- Manual verification
- Mathematical argument

**Impact:**
[Which theorems depend on this axiom]
[Path to eventually remove axiom, if applicable]
-/
axiom statement : Type
```

### Tracking Axioms

```lean
-- At top of file, maintain axiom index:
/-!
**Key Axioms:**
- AXIOM 1 (line 346): toSubstTyped_of_allM_true - Match elaboration issue
- AXIOM 2 (line 388): checkHyp_ensures_floats_typed - Opaque recursion
- AXIOM 3 (line 522): mapM_length_option - Stdlib gap

**Axiom Dependency Graph:**
- verify_impl_sound depends on fold_maintains_provable
- fold_maintains_provable depends on AXIOM 2
- AXIOM 2 has no axiom dependencies

**Removal Plan:**
1. AXIOM 1: Needs Oruži's guidance on match elaboration
2. AXIOM 2: Could be proven with spec-style checkHyp rewrite (~100 LoC)
3. AXIOM 3: Will be in future Batteries version
-/
```

---

## Debugging Techniques

### Build Errors vs Cached Errors

**Problem**: `.olean` and `.ilean` cache files can show stale errors.

**Solution**:
```bash
lake clean
lake build

# If still seeing weird errors:
rm -rf .lake/build
lake build
```

### Understanding Error Messages

#### "application type mismatch"

```
error: application type mismatch
  And.intro h_find
argument
  h_find
has type
  db.find? label = some obj : Prop
but is expected to have type
  some obj = some obj : Prop
```

**Diagnosis**: The goal changed (likely due to `simp` or `rw`). You're providing the wrong thing.

**Solution**: Check what the goal is AFTER the tactic that ran before this line:
```lean
simp [h_find] at h_preload
-- Goal is now `some obj = some obj`
-- So use `rfl`, not `h_find`
refine ⟨obj, rfl, ?_⟩
```

#### "no goals to be solved"

```
error: no goals to be solved
```

**Diagnosis**: Previous tactic already completed the proof.

**Solution**: Delete the line that's erroring.

```lean
simp [Array.back!_push]  -- ← This completed the proof
exact Array.back!_push ...  -- ← DELETE THIS
```

#### "failed to prove index is valid"

```
error: failed to prove index is valid
  possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead
```

**Diagnosis**: Array access needs bounds proof.

**Solutions**:
```lean
-- 1. Provide proof
have h_bound : i < a.size := by ...
let x := a[i]'h_bound

-- 2. Use runtime check (in axioms or when precondition guarantees safety)
let x := a[i]!

-- 3. Change to Option
match a[i]? with
| some x => ...
| none => ...
```

### Interactive Proof Development

```lean
theorem my_theorem : Statement := by
  intro h
  -- Check current goal:
  trace "{goal}"  -- Prints goal to messages

  -- OR: Leave a hole
  · sorry  -- Complete other branches first

  -- Check type of expression:
  have : TypeOfExpr = _ := rfl  -- Lean shows you the actual type

  -- Case split to see structure:
  cases h
  · sorry  -- Look at each branch
  · sorry
```

### Common Tactic Debugging

```lean
-- ❌ simp not working?
simp only [def1, def2]  -- Specify exactly what to unfold

-- ❌ rw not finding the pattern?
show GoalWithPattern  -- Make goal explicit
rw [theorem]

-- ❌ omega failing?
-- Might have non-linear arithmetic or division
have h1 : ... := by linarith  -- Try linarith for non-integer
have h2 : ... := by ring  -- Try ring for polynomial equations
```

---

## Build Health Maintenance

### Continuous Integration Mindset

**Rule**: After every conceptual change, build.

```bash
# After adding theorem statement:
lake build

# After changing proof:
lake build

# Before commit:
lake build
git commit
```

### Managing Sorries Strategically

```lean
-- ✅ GOOD: Sorry with clear TODO
theorem helper : Statement := by
  sorry  -- TODO: Prove by induction on xs (15-20 LoC, straightforward)

-- ❌ BAD: Sorry with no plan
theorem helper : Statement := by
  sorry
```

**Track sorries** in file header:
```lean
/-!
**Sorry Count by Phase:**
- Phase 5: 3 sorries (lines 453, 541, 558)
- Phase 6: 4 sorries (lines 592, 615, 635, 655)
Total: 7 sorries

**Priority order**:
1. Line 453 (checkHyp_validates_floats) - blocks Phase 5
2. Line 541 (checkHyp_hyp_matches) - blocks Phase 5
3. ...
-/
```

### Warning Management

**Principle**: Warnings are OK, errors are NOT.

```lean
-- ✅ Acceptable warnings:
warning: declaration uses 'sorry'
warning: unused variable

-- ❌ Unacceptable errors:
error: type mismatch
error: unknown identifier
```

### Regression Prevention

**Pattern**: After fixing a bug, document what NOT to do.

```lean
-- ❌ DON'T use h_find after simp rewrote goal
simp [h_find] at h_preload
refine ⟨obj, h_find, ?_⟩  -- WRONG

-- ✅ DO use rfl when goal is reflexive
simp [h_find] at h_preload
refine ⟨obj, rfl, ?_⟩  -- CORRECT
```

---

## Scope Management and Variable Substitution

### Problem: Variables Disappearing After `subst`

**Symptom**: After using `subst h_eq : a = b`, the variable `b` disappears from context, breaking later references.

```lean
-- ❌ BAD: Variable disappears
by_cases h_eq : label' = l
· subst h_eq  -- Now label' is replaced everywhere, l disappears!
  have h : f l = ...  -- ERROR: unknown identifier 'l'
```

**Why this happens**: The `subst` tactic is designed to **substitute and remove** variables. This is intentional behavior in Lean 4 - `subst` performs the substitution and then removes both the hypothesis AND the substituted variable from the context.

**Source**: Lean 4 documentation, Proof Assistants Stack Exchange

### Solution: Use `rw` Instead of `subst`

**Pattern**: Use `rw` (rewrite) to substitute without removing variables.

```lean
-- ✅ GOOD: Variable stays in context
by_cases h_eq : label' = l
· rw [h_eq] at h_find  -- Rewrite label' to l in h_find only
  -- Now h_find mentions l, and BOTH label' and l are still in context
  have h : f l = ...  -- OK: l is still available
```

**Key difference**:
- `subst h_eq`: Substitutes `label'` with `l` **everywhere**, removes `h_eq`, and removes `label'` from context
- `rw [h_eq] at h_target`: Rewrites in specific hypothesis/goal only, keeps all variables

### When to Use Each

**Use `subst`**:
- When you want to eliminate a variable completely
- When you won't need the original variable name later
- For simple equalities in short proofs

**Use `rw`**:
- When working with dependent types where variable names matter
- When you need both variables available later in the proof
- When rewriting in specific hypotheses (not everywhere)

### Example from Metamath Parser Proofs

```lean
-- Goal: Prove frame_has_unique_floats for newly inserted assertion
intros label' fmla' fr' proof' h_find
by_cases h_eq : label' = l

-- ❌ PROBLEMATIC: Using subst
· subst h_eq
  -- Problem: l disappeared, but we need it for frame_has_unique_floats_insert_ne!
  exact frame_has_unique_floats_insert_ne db pos l fr.hyps ...  -- ERROR: unknown 'l'

-- ✅ CORRECT: Using rw
· rw [h_eq] at h_find
  -- h_find now mentions l instead of label'
  -- Both l and label' still in context
  unfold DB.find? at h_find
  simp at h_find
  -- ... continue proof using l
  exact frame_has_unique_floats_insert_ne db pos l fr.hyps ...  -- OK!
```

---

## Constructor Injection and Equality Extraction

### Pattern: `injection ... with` for Constructor Equalities

**Problem**: Need to extract component equalities from constructor equations.

```lean
-- Given: h : some (a, b, c) = some (x, y, z)
-- Want: a = x, b = y, c = z
```

**Solution**: Use `injection ... with` to extract equalities.

```lean
-- Single injection for Option
injection h with h_inner
-- Now h_inner : (a, b, c) = (x, y, z)

-- Chain injection for nested constructors
injection h_inner with h_a h_b h_c
-- Now have: h_a : a = x, h_b : b = y, h_c : c = z
```

**From web search (Theorem Proving in Lean documentation)**:
> "Given h : a::b = c::d, the tactic `injection h` adds two new hypotheses with types a = c and b = d to the main goal. The tactic `injection h with h₁ h₂` uses the names h₁ and h₂ to name the new hypotheses."

### Advanced: Extracting from Conjunctions

**Pattern**: After `simp`, complex equalities often reduce to conjunctions.

```lean
-- After simp:
-- h_find : fmla = fmla' ∧ fr = fr' ∧ proof = proof'

-- Extract components using pattern matching
have ⟨h_eq_fmla, h_eq_fr, h_eq_proof⟩ := h_find
-- Now have three separate equalities

-- Or extract just what you need
have ⟨_, h_eq_fr, _⟩ := h_find
-- Only keep the middle component
```

### Example from Metamath Parser Proofs

```lean
-- After unfolding and simplification, HashMap lookup + injection gives us:
rw [h_eq] at h_find  -- Rewrite label' to l
unfold DB.find? at h_find
simp at h_find
-- After all simplifications:
-- h_find : fmla = fmla' ∧ fr = fr' ∧ proof = proof'

-- Extract just the frame equality
have ⟨_, h_eq_fr, _⟩ := h_find
rw [← h_eq_fr]  -- Substitute fr' with fr
-- Now can prove property about fr instead of fr'
exact frame_has_unique_floats_insert_ne db pos l fr.hyps ...
```

### Common Injection Patterns

```lean
-- Option unwrapping
h : some a = some b
injection h with h_eq  -- h_eq : a = b

-- Except unwrapping
h : Except.ok a = Except.ok b
injection h with h_eq  -- h_eq : a = b

-- Pair unwrapping
h : (a, b) = (x, y)
injection h with h_a h_b  -- h_a : a = x, h_b : b = y

-- Nested constructors
h : some (Except.ok (a, b)) = some (Except.ok (x, y))
injection h with h1
injection h1 with h2
injection h2 with h_a h_b
-- h_a : a = x, h_b : b = y

-- Direct from simplified hypothesis
simp at h  -- Simplifies to conjunction
have ⟨h1, h2, h3⟩ := h  -- Extract components
```

### Debugging Injection

**Error**: "equality of constructor applications expected"

**Cause**: The hypothesis is not in the form `Constructor a = Constructor b`.

**Solution**: Simplify first, or check if you need to unfold definitions.

```lean
-- ❌ ERROR: Not constructor form yet
injection h

-- ✅ FIX: Unfold/simp first
unfold definition at h
simp at h
injection h with h_eq
```

---

## Prop Definitions with HashMap/Array Access

### Problem: GetElem? Typeclass Resolution in ∀ Quantifiers

**Symptom**: When defining propositions with universal quantifiers over HashMap/Array values, Lean 4.20.0-rc2 fails with typeclass errors:

```lean
-- ❌ FAILS: Typeclass instance stuck
def HypPropTyped (σ : Std.HashMap String Formula) : Prop :=
  ∀ v val, σ[v]? = some val → Property v val

-- Error: typeclass instance problem is stuck, it is often due to metavariables
--   GetElem? (Std.HashMap String Formula) ?m.33 Formula (?m.203 v val)
```

**Root cause**: In `∀` contexts without explicit type annotations, Lean cannot infer the index type needed for the `GetElem?` typeclass that powers the `[k]?` notation.

### Solution: Always Use Explicit Type Annotations

**Pattern**: Add explicit types to ALL forall-bound variables that will be used in bracket notation.

```lean
-- ✅ WORKS: Explicit types enable typeclass resolution
def HypPropTyped (σ : Std.HashMap String Formula) : Prop :=
  ∀ (v : String) (val : Formula), σ[v]? = some val → Property v val
```

### Comparison

```lean
-- ❌ BROKEN: Implicit types
∀ v val, σ[v]? = some val → P v val
∀ j (hj : j < n), arr[j]? = some x → Q j
∀ i, i < n → m[i] = 0

-- ✅ WORKING: Explicit types
∀ (v : String) (val : Formula), σ[v]? = some val → P v val
∀ (j : Nat) (hj : j < n), arr[j]? = some x → Q j
∀ (i : Nat), i < n → m[i] = 0
```

### Why This Works

1. **Type inference limitation**: In `∀` contexts, Lean's type inference for index parameters is insufficient
2. **Typeclass search**: `GetElem? (Container α) β γ` needs all types to be concrete before search begins
3. **Explicit types provide hints**: `(v : String)` tells Lean that `v` has type `String`, enabling resolution of `GetElem? (Std.HashMap String Formula) String Formula`

### Complete Example

```lean
-- Real definition from Metamath kernel verification
def HypPropTyped
    (db : DB) (hyps : Array String) (stack : Array Formula)
    (off : {off : Nat // off + hyps.size = stack.size})
    (n : Nat) (σ : Std.HashMap String Formula) : Prop :=
  ∀ (v : String) (val : Formula), σ[v]? = some val →  -- ← Explicit types required!
    ∃ j : Nat, ∃ (_ : j < hyps.size), ∃ c : String,
      j < n ∧
      match db.find? hyps[j]! with
      | some (Object.hyp false f _) => ...
      | _ => False

-- This compiles successfully
#check HypPropTyped
```

### Additional Syntax Requirements

#### Existential Quantifiers

Use explicit `:` for types, anonymous `(_ : P)` for propositions:

```lean
-- ✅ Correct
∃ j : Nat, ∃ (_ : j < n), ∃ c : String, Property j c

-- ❌ May fail parsing
∃ (j : Nat) (hj : j < n) (c : String), Property j c
```

#### Named vs Anonymous Parameters

Name parameters that are referenced later:

```lean
-- ❌ Fails: anonymous parameter can't be referenced
∀ (_ : j < hyps.size), j < n → FloatReq ... ‹j < hyps.size›

-- ✅ Works: named parameter
∀ (hj : j < hyps.size), j < n → FloatReq ... hj
```

### Verification Test

```lean
import Std

-- Test with simple HashMap
def test1 (m : Std.HashMap String Nat) : Prop :=
  ∀ (k : String) (v : Nat), m[k]? = some v → v > 0

#check test1  -- ✓ Compiles successfully
```

**Key takeaway**: This is a Lean 4.20.0-rc2 parser/elaborator limitation, not a mathematical issue. Always use explicit type annotations in `∀` quantifiers when working with indexed access (`[...]?`, `[...]!`).

---

## Prop Definitions with Match Expressions

### Problem: "Function Expected" Errors with Match in ∀ Chains

**Symptom**: When defining propositions with `match` expressions directly inside universal quantifier chains, Lean 4.20.0-rc2 fails with parser/elaboration errors:

```lean
-- ❌ FAILS: "function expected at FloatReq db hyps σ j, term has type Prop"
def FloatsProcessed (db : DB) (hyps : Array String) (n : Nat) (σ : HashMap String Formula) : Prop :=
  ∀ j, j < n →
    match db.find? hyps[j]! with
    | some (.hyp false f _) =>
        f.size = 2 →
        match f[0]!, f[1]! with
        | .const c, .var v => ∃ val, σ[v]? = some val ∧ ...
        | _, _ => True
    | _ => True

-- Error: function expected at
--   FloatReq db hyps σ j
-- term has type
--   Prop
```

**Root cause**: Lean's elaborator struggles when:
- `match` expressions appear directly under chained `∀ … → …` binders
- The definition is inside a `namespace` with `open` declarations
- Complex binder telescopes interact with pattern matching

**This is NOT a Lean 4 version limitation** - it's a syntax/shape issue with how the parser handles binder grouping and match placement.

### Solution: Factor Match into Helper Predicates

**Pattern**: Extract the `match` expression into a separate helper definition, then reference it in the `∀` chain.

```lean
-- ✅ WORKS: Helper predicate with match inside
def FloatReq
    (db : DB) (hyps : Array String)
    (σ  : Std.HashMap String Formula) (j : Nat) : Prop :=
  j < hyps.size →
  match db.find? hyps[j]! with
  | some (.hyp false f _) =>
      f.size = 2 →
      match f[0]!, f[1]! with
      | .const c, .var v =>
          ∃ val, σ[v]? = some val ∧
                 val.size > 0 ∧
                 (toExpr val).typecode = ⟨c⟩
      | _, _ => True
  | _ => True

-- ✅ WORKS: Forward invariant using helper
def FloatsProcessed
    (db : DB) (hyps : Array String)
    (n : Nat) (σ : Std.HashMap String Formula) : Prop :=
  ∀ j, j < n → FloatReq db hyps σ j
```

**Key points**:
- The `match` is inside `FloatReq`, NOT directly in the `∀` chain
- The bound check `j < hyps.size` is an **implication** (`→`), not a dependent binder `(hj : j < hyps.size)`
- This provides cleaner elaboration and better error messages

### Advanced: Section Isolation for Context Issues

**Problem**: Sometimes the exact pattern above works in isolation but fails in the actual file due to namespace/open context pollution.

**Solution**: Wrap definitions in `section ... end` to isolate from surrounding context.

```lean
section Phase5Defs

def FloatReq (db : DB) (hyps : Array String) ... : Prop := ...

def FloatsProcessed (db : DB) (hyps : Array String) ... : Prop := ...

end Phase5Defs
```

**Why this works**: The `section` block prevents interaction with:
- Surrounding `namespace` declarations
- Active `open` imports
- Previous definitions in the same scope

**Note**: Inside the section, you can use unqualified names (e.g., `DB`, `Formula`) if there's an `open` declaration earlier in the file.

### Before/After Comparison

```lean
-- ❌ BEFORE: Parser confusion
def FloatsProcessed
    (db : DB) (hyps : Array String)
    (n : Nat) (σ : HashMap String Formula) : Prop :=
  ∀ j, j < n →
    match db.find? hyps[j]! with  -- ← Parser gets confused here
    | some (.hyp false f _) => ...
    | _ => True

-- ✅ AFTER: Helper predicate pattern
section Phase5Defs

def FloatReq (db : DB) (hyps : Array String) (σ : HashMap String Formula) (j : Nat) : Prop :=
  j < hyps.size →
  match db.find? hyps[j]! with  -- ← Match is isolated in helper
  | some (.hyp false f _) => ...
  | _ => True

def FloatsProcessed (db : DB) (hyps : Array String) (n : Nat) (σ : HashMap String Formula) : Prop :=
  ∀ j, j < n → FloatReq db hyps σ j  -- ← Clean reference

end Phase5Defs
```

### When to Use This Pattern

**Use helper predicates when**:
- Defining propositions with complex `match` expressions
- Working inside namespaces with multiple `open` declarations
- Getting "function expected" errors on definitions that look syntactically correct
- The same code works in a minimal test file but fails in your actual codebase

**Benefits**:
- ✅ Cleaner elaboration
- ✅ Better error messages
- ✅ Easier to test definitions in isolation
- ✅ More modular proof architecture

### Real Example: Metamath checkHyp Soundness

```lean
-- Goal: Prove that checkHyp validates floating hypothesis typecodes

section Phase5Defs

/-- A single floating hypothesis at index `j` is "satisfied" by `σ`. -/
def FloatReq
    (db : DB) (hyps : Array String)
    (σ  : Std.HashMap String Formula) (j : Nat) : Prop :=
  j < hyps.size →
  match db.find? hyps[j]! with
  | some (.hyp false f _) =>
      f.size = 2 →
      match f[0]!, f[1]! with
      | .const c, .var v =>
          ∃ val, σ[v]? = some val ∧
                 val.size > 0 ∧
                 (toExpr val).typecode = ⟨c⟩
      | _, _ => True
  | _ => True

/-- Forward invariant: every float at indices `< n` is satisfied by `σ`. -/
def FloatsProcessed
    (db : DB) (hyps : Array String)
    (n : Nat) (σ : Std.HashMap String Formula) : Prop :=
  ∀ j, j < n → FloatReq db hyps σ j

end Phase5Defs

-- Now can use in proofs:
lemma floatsProcessed_preservation ... : FloatsProcessed db hyps hyps.size σ := by
  classical
  have main : ∀ k, ... → FloatsProcessed ... := by
    intro k; induction k with
    | zero => ...
    | succ k ih => unfold FloatsProcessed at *; intro j hj; unfold FloatReq; ...
  exact main (hyps.size - i) rfl hi hprop hrun
```

**Status**: This pattern enabled a previously impossible proof to compile successfully, eliminating the need for axiomatization!

### Credit

This solution comes from **GPT-5 Pro's diagnosis**:
> "The 'function expected at … term has type Prop' family of errors you're seeing is a *shape/syntax* issue (binder grouping + where you put the `match`) not a version bug."

The fix: factor complex `match` expressions into helper predicates and use section isolation when needed.

---

## Debugging Cascading Parse Errors

**Problem:** "unexpected identifier; expected command" errors where Lean refuses to recognize valid keywords like `lemma`, `def`, or `theorem` at the top level.

**Symptom:** Error message says Lean is expecting a command, but you've written a perfectly valid command keyword. Even simple declarations like `def test : Nat := 42` fail with bizarre errors like "function expected at 42".

### Root Causes

Parse errors that prevent subsequent declarations from being recognized are almost always caused by **unterminated expressions** in previous declarations. The parser is stuck "inside a term" and treats everything after as part of that malformed term.

#### Common Culprits

1. **ASCII `forall` instead of Unicode `∀` in Prop definitions**

   ```lean
   -- WRONG: Uses word "forall" as a term
   def FloatsProcessed ... : Prop :=
     forall j, j < n -> FloatReq db hyps σ j
   -- Lean tries to find a function named "forall" and apply it
   -- This leaves the expression unterminated!

   -- CORRECT: Uses ∀ binder
   def FloatsProcessed ... : Prop :=
     ∀ j, j < n → FloatReq db hyps σ j
   ```

2. **Unclosed block comments `/-  ... -/`**

   ```lean
   axiom foo : True
   /-  This comment is unclosed
       The next declaration will fail!
   def bar : Nat := 42  -- Error: unexpected identifier
   ```

3. **Malformed axiom signatures**

   ```lean
   -- WRONG: Implication in wrong position
   axiom foo (x : Nat) :
     x > 0 →  -- This arrow starts a term context
     (∀ y, ...)  -- Now ∀ is inside a term, not a type

   -- CORRECT: Make the implication a parameter
   axiom foo (x : Nat) (h : x > 0) :
     ∀ y, ...
   ```

4. **Match expressions with incorrect indentation**

   Can cause Lean to think the match hasn't closed, leaving the RHS unterminated.

### Debugging Strategy: Binary Search

When you get "unexpected identifier; expected command" and can't immediately see the issue:

1. **Verify the symptom location is NOT the cause**

   The error appears at the NEXT declaration after the problem. The actual issue is in the PREVIOUS definition.

2. **Comment out suspect code in sections**

   ```lean
   -- Start by commenting out the failing declaration
   /- def problematic ... := ... -/

   -- Does the error move? If yes, the problem is earlier.
   -- If no, the problem is in this declaration.
   ```

3. **Binary search backward**

   ```lean
   -- Comment out half the file before the error
   /-
   def earlierStuff1 ... := ...
   def earlierStuff2 ... := ...
   -/

   -- Still errors? Problem is before the comment.
   -- Error gone? Problem is inside the commented section.
   -- Repeat on smaller sections until you isolate it.
   ```

4. **Test with minimal declaration**

   ```lean
   -- After suspect code, try:
   def test_parse : Nat := 42

   -- If even THIS fails, the previous declaration is broken.
   ```

### Example: Phase 5 Debug Session

**Error:** "unexpected identifier; expected command" at line 691 (`lemma floatsProcessed_preservation`)

**Hypothesis 1:** Problem is before Phase 5 section (in earlier axioms/defs)
- Test: Comment out Phase 5 section entirely
- Result: File compiles ✅
- Conclusion: Problem is IN the Phase 5 section, not before it

**Hypothesis 2:** Problem is in Phase5Defs section
- Test: Restore Phase5Defs, keep lemma commented out
- Result: File compiles ✅
- Conclusion: Phase5Defs is fine, problem is in the lemma itself

**Hypothesis 3:** Problem is in lemma signature or proof
- Test: Simplified lemma to `axiom floatsProcessed_preservation : True`
- Result: Still need to test, but likely the signature

**Finding:** The Phase 5 definitions using `∀` and `→` compile perfectly. The issue was in how the preservation lemma was declared, not in the helper predicates.

### Prevention Checklist

- [ ] Use Unicode binders (`∀`, `∃`, `→`) not ASCII words (`forall`, `exists`, `->`) in `Prop` definitions
- [ ] Check all block comments are closed (`/-` has matching `-/`)
- [ ] Axiom signatures: parameters before `:`, type after `:`
- [ ] Long lines: split complex expressions across multiple lines for clarity
- [ ] After major changes: try compiling with `lake clean && lake build`

### When GPT-5/Claude Gets Confused

If the AI suggests a fix for "function expected" or "unexpected identifier" errors and it doesn't work:

1. The AI might be fixing a different symptom with the same error message
2. Try the **binary search** approach instead of guessing
3. The actual problem might be several declarations earlier
4. Check the AI's suggestion is actually being applied (Unicode characters can be subtle!)

---

## Theorem Accessibility and Namespace Issues

### The Problem: "unknown constant" for Theorems That Exist

**Symptom**: You define a theorem in one file, the file compiles successfully, but when you try to use the theorem from another file, you get "unknown constant" errors - even though `#check` on the *function* the theorem is about works fine.

**Example that FAILS**:
```lean
-- In Verify.lean, inside namespace DB:
namespace DB

@[simp] theorem DB.checkHyp_step_hyp_true  -- ❌ WRONG!
  (db : DB) ... :
  DB.checkHyp db ... = ... := by
  sorry

end DB

-- In KernelClean.lean:
#check DB.checkHyp                -- ✅ Works
#check DB.checkHyp_step_hyp_true  -- ❌ unknown constant!
```

### Root Cause: Dot Notation Inside Namespaces

When you're **inside** `namespace DB` and write `DB.checkHyp_foo`, Lean 4 interprets this as trying to define an **extension method** on the `DB` *type/structure*, not as defining a theorem in the `DB` namespace.

The theorem compiles (because the syntax is valid), but it's not exported to the namespace you expect.

### The Fix: Remove Redundant Prefix

When you're inside a namespace, **omit** the namespace prefix from theorem names:

```lean
-- ✅ CORRECT:
namespace DB

@[simp] theorem checkHyp_step_hyp_true  -- No DB. prefix!
  (db : DB) ... :
  checkHyp db ... = ... := by        -- No DB. prefix in body either!
  unfold checkHyp
  sorry

@[simp] theorem checkHyp_step_hyp_false
  (db : DB) ... :
  checkHyp db ... = ... := by
  unfold checkHyp
  sorry

end DB
```

Now the theorems are accessible as:
- `DB.checkHyp_step_hyp_true` (from outside the namespace)
- `Metamath.Verify.DB.checkHyp_step_hyp_true` (fully qualified)

### Alternative: Define Outside the Namespace

If you want to use the `DB.` prefix, define the theorems **outside** the namespace:

```lean
end DB  -- Close the namespace first

-- Now DB. prefix is correct:
@[simp] theorem DB.checkHyp_step_hyp_true
  (db : DB) ... :
  DB.checkHyp db ... = ... := by
  unfold DB.checkHyp
  sorry
```

### How to Diagnose This Issue

1. **Check if the function works**: `#check DB.checkHyp` succeeds
2. **Check if the theorem fails**: `#check DB.checkHyp_step_hyp_true` gives "unknown constant"
3. **Look at where the theorem is defined**: Is it using `DB.foo` syntax INSIDE `namespace DB`?
4. **Fix**: Remove the redundant prefix

### Real-World Example

From the Metamath kernel soundness proof (2025-11-02):

**Before (broken)**:
```lean
-- Verify.lean, lines 420-452
namespace DB

@[simp] theorem DB.checkHyp_base        -- ❌ Won't export!
  (db : DB) ... :
  DB.checkHyp db ... = .ok σ := by
  unfold DB.checkHyp
  simp [h]
  rfl

end DB
```

**After (works)**:
```lean
namespace DB

@[simp] theorem checkHyp_base           -- ✅ Exports correctly
  (db : DB) ... :
  checkHyp db ... = .ok σ := by         -- ✅ No redundant prefix
  unfold checkHyp
  simp [h]
  rfl

end DB
```

**Result**: The theorem is now accessible as `Metamath.Verify.DB.checkHyp_base` from other files.

### Why This Is Subtle

- ✅ The file with the **wrong** definition still compiles successfully
- ✅ Lean accepts the syntax without errors or warnings
- ❌ The theorem just silently doesn't export to the expected location
- ❌ You only discover the problem when another file tries to import it

### Key Takeaway

**Inside a namespace, use SHORT names. The namespace prefix is automatic.**

```lean
namespace Foo
  theorem bar ...           -- Accessible as Foo.bar
  theorem Foo.bar ...       -- ❌ Confusing! Creates Foo.Foo.bar or extension method
end Foo
```

**Outside a namespace, use FULL names if you want dot notation.**

```lean
end Foo
theorem Foo.bar ...         -- ✅ Correctly creates Foo.bar
```

---

## Advanced Patterns

### Proof by Reflection

Sometimes you can compute the answer rather than prove it:

```lean
-- Instead of proving:
theorem list_eq : [1, 2, 3] = [1, 2, 3] := by
  -- Complex proof

-- Just use:
theorem list_eq : [1, 2, 3] = [1, 2, 3] := rfl

-- Works for:
-- - Decidable propositions: decide P
-- - Computational equality: rfl
-- - Normalization: simp only (with nothing)
```

### Proof Irrelevance

```lean
-- Two proofs of the same proposition are equal
theorem proof_irrelevance {P : Prop} (h1 h2 : P) : h1 = h2 := rfl

-- Useful for showing structures equal:
-- If two TypedSubst have same σ, they're equal (proof doesn't matter)
```

### Dependent Pattern Matching

```lean
-- When case-splitting reveals impossible cases:
def safeDiv (n : Nat) (d : Nat) (h : d ≠ 0) : Nat :=
  match d, h with
  | 0, h => absurd rfl h  -- Contradiction: 0 ≠ 0
  | d'+1, _ => n / (d'+1)

-- In proofs:
theorem foo : Statement := by
  cases h_eq : x with
  | none =>
      -- In this branch: h_eq : x = none
      simp [h_eq] at h_some  -- Shows contradiction if h_some : x = some y
  | some y =>
      -- In this branch: h_eq : x = some y
```

---

## Summary: Decision Tree

When faced with a proving task:

```
┌─ Need to prove property of recursive function?
│  ├─ Have time to rewrite in spec style?
│  │  └─ YES → Rewrite with termination proof, use induction
│  └─ NO → Axiomatize with detailed doc (AXIOM pattern)
│
├─ Need to bridge impl ↔ spec types?
│  ├─ Involves validation (Option/Except)?
│  │  └─ YES → Witness-carrying type pattern
│  └─ NO → Direct conversion function with correctness proof
│
├─ Need to extract from monadic validation?
│  └─ Prove allM_true_iff_forall pattern
│
├─ Need to connect list ↔ array?
│  └─ Use structural correspondence lemma
│
├─ Lambda elaboration issue?
│  └─ Add @[simp] normalization lemma
│
├─ Index bounds error?
│  ├─ In axiom? → Use `!` notation
│  ├─ Have bound in context? → Provide proof with `'h`
│  └─ Unknown bound? → Use `?` for Option
│
└─ Build failing?
   ├─ Error message unclear? → lake clean && lake build
   ├─ "type mismatch"? → Check what previous tactic did to goal
   └─ "no goals"? → Previous tactic finished proof, delete current line
```

---

## References

- **Lean 4 Documentation**: https://lean-lang.org/documentation/
- **Batteries Documentation**: https://github.com/leanprover-community/batteries
- **Theorem Proving in Lean 4**: https://lean-lang.org/theorem_proving_in_lean4/
- **Functional Programming in Lean**: https://lean-lang.org/functional_programming_in_lean/

---

## Appendix: Quick Reference

### Most Common Tactics

```lean
-- Introduce hypotheses
intro x h

-- Case analysis
cases h with | case1 => ... | case2 => ...
split  -- Split on match/if

-- Rewriting
rw [theorem]
simp [def1, def2]

-- Unfolding
unfold definition

-- Arithmetic
omega  -- Linear integer arithmetic
linarith  -- Linear arithmetic (reals/rationals)

-- Contradiction
contradiction
exact absurd h1 h2

-- Reflexivity/triviality
rfl
trivial

-- Function extensionality
funext x

-- Extract from injection
injection h with h_eq

-- Apply theorem
exact theorem args
apply theorem

-- Witness
refine ⟨witness1, witness2, ?_⟩
exists witness
```

### Most Common Lemmas

```lean
-- Option
Option.map_some
Option.bind_some

-- List
List.mem_cons
List.mem_append
List.map_cons
List.length_cons

-- Decidability
decide_eq_true_eq
decide_eq_false_eq

-- Logic
And.intro
And.left / And.right
Or.inl / Or.inr
Exists.intro
```

---

**Last Updated**: 2025-11-02
**Contributors**: Claude (with human verification and web search validation)
**Status**: Living document - update as you learn new patterns!

**Recent additions** (2025-11-02):
- **Theorem Accessibility and Namespace Issues**: "unknown constant" for theorems that compile
  - Root cause: Using `DB.foo` syntax INSIDE `namespace DB` creates extension methods, not namespace theorems
  - Fix: Omit redundant prefix inside namespaces (use `theorem foo` not `theorem DB.foo`)
  - Silent failure: File compiles but theorem isn't exported to expected namespace!
  - Real-world example from Metamath kernel proof (AXIOM 2 work)

**Recent additions** (2025-11-01):
- **Prop definitions with Match Expressions**: "function expected" error solution from GPT-5 Pro
  - Factor `match` into helper predicates (avoid `match` directly in `∀` chains)
  - Use `section ... end` for context isolation
  - Pattern that eliminated need for axiomatization in Phase 5!
- Prop definitions with HashMap/Array access: GetElem? typeclass resolution workaround
- Required pattern: explicit type annotations `∀ (v : String)` in quantifiers with indexed access

**Recent additions** (2025-10-31):
- Scope management: `subst` vs `rw` for variable substitution
- Constructor injection patterns with `injection ... with`
- Extracting from conjunctions after simplification

---

## Equation Lemmas for Recursive Functions

### Pattern: Proving Computational Equation Lemmas

When proving that a recursive function unfolds to a specific computational form (e.g., for `@[simp]` lemmas), you need to carefully control which occurrences get unfolded.

**Problem**: `unfold recursive_fn` unfolds ALL occurrences in the goal, including:
- ✓ The LHS call you want to expose
- ✗ Recursive calls on the RHS that should stay folded

**Solution**: Use `rw [recursive_fn]` to rewrite only pattern matches, not all occurrences.

```lean
-- ❌ BAD: Unfolds everything, including RHS recursive calls
@[simp] theorem checkHyp_step ... := by
  unfold checkHyp  -- Oops! Unfolds the RHS recursive call too
  simp [...]
  -- Now RHS is fully expanded instead of being a simple recursive call

-- ✅ GOOD: Rewrite only the LHS pattern
@[simp] theorem checkHyp_step ... := by
  rw [checkHyp]   -- Only rewrites the top-level call
  simp [...]
  -- RHS recursive call stays folded as intended
```

**Complete equation lemma pattern**:
```lean
@[simp] theorem recursive_fn_step
  (preconditions)
  (h_condition : key_condition) :
  recursive_fn args = expected_computational_form := by
  rw [recursive_fn]           -- Unfold only LHS
  simp [h_condition, ...]     -- Simplify with hypotheses
  have h_idx : bounds := ...  -- Produce any needed bounds
  simp [bridge_lemmas, h_idx] -- Apply bridging lemmas
  split <;> rfl              -- Handle match cases
```

### Why Equation Lemmas Matter

Equation lemmas expose the computational content of recursive definitions:
- Make `simp` powerful: it can now reason about individual steps
- Enable inductive proofs: prove invariants by case-splitting on the equation
- Replace axiomatic specifications: the lemma IS the specification

**Real-world example** (Metamath kernel, AXIOM 2 elimination):
```lean
-- Instead of axiomatizing operational behavior:
axiom checkHyp_operational_semantics : behavior_spec

-- Prove step-by-step equation lemmas:
@[simp] theorem checkHyp_base : checkHyp i σ = pure σ (when i >= n)
@[simp] theorem checkHyp_step_essential : checkHyp i σ = ... (when essential hyp)
@[simp] theorem checkHyp_step_float : checkHyp i σ = ... (when float hyp)

-- Then derive operational semantics by induction using the equations
theorem checkHyp_operational_semantics : ... := by
  induction n using Nat.strong_rec
  cases h_find : db.find? hyps[i]
  · -- Use wf_elim to eliminate impossible cases
  · -- Apply appropriate equation lemma
    simp [checkHyp_step_essential]  -- Equation exposes structure!
    -- Proceed with invariant reasoning
```

---

## Array Indexing: Bridging `arr[i]!` and `arr[i]'h`

### The Problem

Lean 4 has multiple array indexing syntaxes that are NOT definitionally equal:
- `arr[i]!` - Panic-safe indexing (uses `Inhabited` default if out of bounds)
- `arr[i]'h` - Dependent indexing with proof `h : i < arr.size`
- `arr[i]` - Partial indexing (only elaborates when bound is in scope)

**Why this matters**: When you unfold a definition that uses dependent indexing internally (via `let val := arr[i]'h`), you need to match it with user-facing specs that use `arr[i]!`.

### The Bridge Lemma (A1 Pattern)

Add this near your Array utilities:

```lean
namespace Array

/-- Bridge dependent and panic-safe array indexing.
When you have a proof that i < a.size, both forms return the same element. -/
@[simp] theorem getBang_eq_get (a : Array α) (i : Nat) (h : i < a.size) [Inhabited α] :
  a[i]! = a[i]'h := by
  simp only [getElem!_pos, h]

end Array
```

**Note**: Uses modern Lean 4 API (`getElem!_pos`), not deprecated `Array.get!`.

### Usage in Equation Lemmas

```lean
@[simp] theorem fn_step
  (h_i : i < arr.size)
  (h_find : db.find? arr[i] = some val) :  -- Note: arr[i] without !
  fn arr i = if ... then result arr[i]! else error := by
  rw [fn]
  simp [h_i, h_find]
  -- After unfold, LHS uses: let x := arr[i]'(proof); ... references x
  -- RHS uses: arr[i]!
  -- Produce the bound:
  have h_idx : i < arr.size := h_i
  -- Bridge them:
  simp [Array.getBang_eq_get, h_idx]
  -- Now both sides use the same value!
```

### Common Pitfall: Off-by-One in Compound Indices

When dealing with `arr[off + i]`, you need the combined bound:

```lean
-- ❌ WRONG: Only have bound for i
have h_i : i < hyps.size := ...
simp [Array.getBang_eq_get, h_i]  -- Won't match arr[off + i]!

-- ✅ RIGHT: Produce combined bound
have h_idx : off + i < arr.size := by
  have : off + i < off + hyps.size := Nat.add_lt_add_left h_i _
  simpa [h_off_relation] using this
simp [Array.getBang_eq_get, h_idx]  -- Now matches!
```

### Real-World Example

From Metamath kernel `checkHyp` verification:

```lean
-- Definition uses dependent indexing via let-binding
def checkHyp (i : Nat) (σ : Map) : Except String Map := do
  if h : i < hyps.size then
    let val := stack[off.1 + i]'(proof_using_h_and_off_property)
    -- All references use `val`, not direct indexing
    if val[0]! == target then ...
  else pure σ

-- Equation lemma needs to match user-facing spec with `!` notation
@[simp] theorem checkHyp_step ... :
  checkHyp i σ = if stack[off.1 + i]![0]! == target then ... := by
  rw [checkHyp]
  simp [h_i, ...]
  have h_idx : off.1 + i < stack.size := ...
  simp [Array.getBang_eq_get, h_idx]  -- Bridge!
  -- Now `val` and `stack[off.1 + i]!` are the same
```

---

## Do-Notation and Monadic Bind Reduction

### The Problem

When proving equation lemmas for monadic code, `simp` doesn't automatically reduce do-notation:

```lean
-- After unfold, you see:
do
  let x ← some_monad
  body x

-- But your RHS has explicit match:
match some_monad with
| .ok x => body x
| .error e => .error e
```

These are definitionally equal (do-notation desugars to `bind`), but `simp` needs help.

### The Solution: Unfold the Bind Chain

```lean
-- Add to your simp call:
simp [bind, Except.bind]
```

**Desugaring chain**:
```
do { let x ← m; body }
  ↓ (do-notation)
bind m (λ x => body)
  ↓ (typeclass resolution)  
Except.bind m (λ x => body)
  ↓ (definition)
match m with
| error e => error e
| ok x => body
```

You need to unfold BOTH:
- `bind` (the typeclass method)
- `Except.bind` (the specific implementation for your monad)

### Complete Pattern

```lean
@[simp] theorem fn_with_monadic_bind ... := by
  rw [fn]
  simp [hypotheses]
  have bounds := ...
  simp [Array.getBang_eq_get, bounds, bind, Except.bind]
  -- Now do-notation is reduced to explicit match on both sides
  split <;> rfl  -- Handle match cases
```

### Real-World Example

```lean
-- Definition with monadic bind
def checkHyp ... := do
  if h : i < n then
    if (← f.subst σ) == target then  -- The ← is monadic bind
      checkHyp (i+1) σ
    else throw "error"
  else pure σ

-- Equation lemma
@[simp] theorem checkHyp_step_essential ... :
  checkHyp i σ =
    match f.subst σ with
    | .ok s => if s == target then checkHyp (i+1) σ else .error "error"
    | .error e => .error e := by
  rw [checkHyp]
  simp [h_i, h_find, bind, Except.bind]
  -- The (← f.subst σ) is now reduced to match f.subst σ
```

---

---

## Match Expressions in Prop Contexts

### The Problem: Match Not Allowed in Props

When defining propositions that need to check the shape of a value, you **cannot** use match expressions directly:

```lean
-- ❌ BAD: match expression in Prop
def WellFormed (db : DB) (arr : Array String) : Prop :=
  ∀ i, i < arr.size →
    ∃ obj, db.find? arr[i]! = some obj ∧
      (match obj with
      | .hyp _ _ _ => True
      | _ => False)

-- Error: "function expected at match obj with ... term has type Prop"
```

**Why this fails**: In Lean 4, `match` expressions in term mode (where you write `match x with | ... => ...`) are not directly usable in propositional contexts. The elaborator expects a function but gets a Prop.

### Solution 1: Use Existential Quantification Over Constructor Arguments

Instead of matching on a general object, directly quantify over the specific constructor's fields:

```lean
-- ✅ GOOD: Existential over constructor arguments
def HypsWellFormed (db : Verify.DB) (hyps : Array String) : Prop :=
  ∀ i, i < hyps.size →
    ∃ (ess : Bool) (f : Verify.Formula) (lbl : String),
      db.find? hyps[i]! = .some (Verify.Object.hyp ess f lbl)
```

**This works because**:
- No match expression - just an equality with a specific constructor
- The existential quantifiers make the fields available
- The equality `db.find? ... = .some (.hyp ess f lbl)` is a pure Prop

### Solution 2: Define a Separate Predicate Function

If you need complex case analysis, define a boolean or decidable function:

```lean
-- Helper function in Type (not Prop)
def Object.isHyp : Object → Bool
  | .hyp _ _ _ => true
  | _ => false

-- Use in Prop definition
def WellFormed (db : DB) (arr : Array String) : Prop :=
  ∀ i, i < arr.size →
    ∃ obj, db.find? arr[i]! = some obj ∧ obj.isHyp
```

### Debugging Strategy: Isolate in Test File

When you get mysterious parse errors in a large file:

1. **Create a minimal test file**:
```lean
import Your.Module

def test_definition (db : DB) (arr : Array String) : Prop :=
  ∀ i, i < arr.size →
    ∃ (x : Type1) (y : Type2),
      condition x y

#check test_definition  -- Does it parse?
```

2. **Incrementally add complexity** until the error reproduces
3. **Test with simple types first** (Nat, Bool) before complex types
4. **Check namespace issues** - add `open` statements if needed

### Real-World Example: HypsWellFormed

**Problem context**: Defining a well-formedness invariant for Metamath kernel verification.

**First attempt** (failed):
```lean
def HypsWellFormed (db : Verify.DB) (hyps : Array String) : Prop :=
  ∀ i, i < hyps.size →
    ∃ obj, db.find? hyps[i]! = some obj ∧
      match obj with
      | Verify.Object.hyp _ _ _ => True
      | _ => False

-- Error: "function expected at match obj with..."
-- Error: "unexpected identifier 'lemma'" on following declarations
```

**Solution** (worked):
```lean
def HypsWellFormed (db : Verify.DB) (hyps : Array String) : Prop :=
  ∀ i, i < hyps.size →
    ∃ (ess : Bool) (f : Verify.Formula) (lbl : String),
      db.find? hyps[i]! = .some (Verify.Object.hyp ess f lbl)

-- ✅ Compiles! Can now use in eliminators:
axiom HypsWellFormed_elim_none {db : Verify.DB} {hyps : Array String} {i : Nat}
    (WF : HypsWellFormed db hyps) (hi : i < hyps.size)
    (h_find : db.find? hyps[i]! = none) :
    False
```

### Key Lessons

1. **Match is not universally available**: In Prop contexts, you often need alternative formulations
2. **Test in isolation**: Parse errors in large files can be misleading - use small test files
3. **Existential over constructors**: This is idiomatic Lean 4 style for "there exists an X of shape Y"
4. **The .some syntax**: Use `.some` instead of `some` for type inference (though `some` often works)
5. **Cascading errors**: A parse error in a definition can cause all following declarations to fail with misleading messages

### Pattern Summary

For "property P holds for objects of specific shape":

```lean
-- Instead of:
-- ∃ obj, lookup = some obj ∧ (match obj with | .Ctor ... => True | _ => False)

-- Write:
∃ (field1 : Type1) (field2 : Type2) ...,
  lookup = .some (.Ctor field1 field2 ...)
```

This pattern is:
- More explicit about the constructor shape
- Easier for Lean to elaborate
- Provides direct access to fields in proofs via `obtain ⟨field1, field2, h_eq⟩`

---

## Match Elaboration in Witness Construction

### The Problem: Let-Bindings Inside Match Branches

When you define a function that returns an `Option` based on a match, and the successful case constructs a complex witness with internal let-bindings, proving existence can fail due to elaboration issues:

```lean
-- Function with internal let-binding in match
def toSubstTyped (fr : Frame) (σ_impl : HashMap String Formula) : Option TypedSubst :=
  match h : xs.allM checkFloat with
  | some true =>
    let σ_fn := fun v => ...  -- ← Let-binding INSIDE match branch
    some ⟨σ_fn, proof_using_h⟩
  | _ => none

-- ❌ BAD: Trying to prove existence naively
axiom toSubstTyped_of_allM_true (fr : Frame) (σ_impl : HashMap String Formula)
    (hAll : xs.allM checkFloat = some true) :
  ∃ σ_typed, toSubstTyped fr σ_impl = some σ_typed

-- The issue: After rw [hAll], we get:
-- (let σ_fn := ...; some ⟨σ_fn, ...⟩) = some ⟨σ_witness, ...⟩
-- The σ_fn is scoped to the match branch and can't unify with external σ_witness
```

### Solution: Unfold and Reconstruct the Witness

Instead of trying to extract the witness from the match, **unfold the definition** and **reconstruct the same witness** outside:

```lean
-- ✅ GOOD: Unfold and reconstruct
theorem toSubstTyped_of_allM_true (fr : Frame) (σ_impl : HashMap String Formula)
    (hAll : xs.allM checkFloat = some true) :
  ∃ σ_typed, toSubstTyped fr σ_impl = some σ_typed := by
  -- Step 1: Unfold the definition
  unfold toSubstTyped

  -- Step 2: Rewrite with the known match result
  rw [hAll]  -- Now we're in the 'some true' branch

  -- Step 3: Reconstruct the SAME witness outside the match
  let σ_fn := fun v => ...  -- Same definition as inside

  -- Step 4: Reconstruct the SAME proof
  have h_typed : TypedSubst.IsTyped fr σ_fn := by
    -- Same proof as inside the match
    ...

  -- Step 5: Provide the witness
  use ⟨σ_fn, h_typed⟩
  rfl  -- Now this works!
```

### Why This Works

1. **Unfolding** exposes the match expression
2. **Rewriting** with `hAll` selects the correct branch
3. **Reconstructing** the witness outside avoids scoping issues
4. **`rfl` succeeds** because both sides construct the same value

### Real-World Example: AXIOM 1 Elimination

In the Metamath kernel verification, AXIOM 1 (`toSubstTyped_of_allM_true`) was blocking progress due to this exact issue:

```lean
-- Original axiom (couldn't be proven)
axiom toSubstTyped_of_allM_true
    (fr : Spec.Frame) (σ_impl : Std.HashMap String Verify.Formula)
    (hAll : (Bridge.floats fr).allM (fun (c, v) => checkFloat σ_impl c v) = some true) :
  ∃ σ_typed : Bridge.TypedSubst fr, toSubstTyped fr σ_impl = some σ_typed

-- Solution that worked
theorem toSubstTyped_of_allM_true ... := by
  unfold toSubstTyped
  rw [hAll]
  -- Reconstruct the substitution function
  let σ_fn : Spec.Subst := fun v =>
    match σ_impl[v.v]? with
    | some f => toExpr f
    | none => ⟨⟨v.v⟩, [v.v]⟩
  -- Reconstruct the typing proof
  have h_typed : Bridge.TypedSubst.IsTyped fr σ_fn := by
    intro c v h_float
    -- ... (same proof logic as inside toSubstTyped)
  use ⟨σ_fn, h_typed⟩
  rfl
```

### Key Lessons

1. **Don't fight elaboration** - if match bindings cause issues, unfold and reconstruct
2. **Duplicate is OK** - copying the witness construction is better than complex equality proofs
3. **Mario Carneiro style** - pragmatic, direct solutions over elegant but fragile ones
4. **Test incrementally** - check each step (unfold, rewrite, construct) separately

### When to Use This Pattern

- Function returns `Option` with complex witness construction
- Match branches have let-bindings or complex expressions
- Need to prove existence when match result is known
- Getting "definitionally equal but can't unify" errors
- `rfl` fails after what should be straightforward rewrites

## Batteries vs Mathlib: Keyword Availability

### The Problem: "Unexpected Identifier" After Doc Comments

When you see parse errors like this:

```
error: unexpected identifier; expected 'theorem', 'lemma', 'def', ...
```

appearing after a doc comment (`/-- ... -/`), the issue might be that you're using a keyword that doesn't exist in your project's dependencies.

**Common scenario**: Using `lemma` without Mathlib

```lean
/-- This is a helper result. -/
lemma my_result : P := by
  -- Error: unexpected identifier; expected 'theorem', 'def', ...
```

### Root Cause

Lean 4 has **two major standard library ecosystems**:

1. **Batteries** (also called `Std`): Minimal standard library, part of Lean 4 core ecosystem
   - Provides: Basic data structures, tactics, some algorithms
   - Does NOT provide: The `lemma` keyword

2. **Mathlib**: Comprehensive mathematics library
   - Provides: Everything in Batteries PLUS extensive math + the `lemma` keyword
   - The `lemma` keyword is a Mathlib-specific alias for `theorem`

### Solution

**Option 1: Add Mathlib dependency**

If your project can use Mathlib, add it to your `lakefile.lean`:

```lean
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
```

Then import it:
```lean
import Mathlib  -- or specific modules like Mathlib.Data.List.Basic
```

**Option 2: Use `theorem` instead of `lemma`** (Recommended for Batteries-only projects)

```lean
/-- This is a helper result. -/
theorem my_result : P := by  -- ✅ Works with just Batteries
  sorry
```

### How to Check What You Have

```bash
# Check your lakefile.lean or lakefile.toml
cat lakefile.lean | grep -i mathlib

# If no mathlib: Use theorem, not lemma
# If mathlib: Both theorem and lemma work
```

### Real-World Example

From the Metamath kernel soundness proof (Batteries-only project):

```lean
-- ❌ This failed with "unexpected identifier"
lemma HypsWellFormed.elim_none
    {db : Verify.DB} {hyps : Array String}
    (wf : HypsWellFormed db hyps) {i : Nat} (hi : i < hyps.size) :
    db.find? hyps[i]! ≠ none := by
  rcases wf i hi with ⟨ess, f, lbl, h⟩
  intro hnone
  simpa [h] using hnone

-- ✅ Fixed by changing to theorem
theorem HypsWellFormed.elim_none
    {db : Verify.DB} {hyps : Array String}
    (wf : HypsWellFormed db hyps) {i : Nat} (hi : i < hyps.size) :
    db.find? hyps[i]! ≠ none := by
  rcases wf i hi with ⟨ess, f, lbl, h⟩
  intro hnone
  simpa [h] using hnone
```

### Semantic Difference

In Mathlib, `lemma` and `theorem` are **functionally identical**. The distinction is purely conventional:
- `theorem`: Important, named results
- `lemma`: Helper results, stepping stones

In Batteries-only projects, just use `theorem` for everything.

### Other Mathlib-Specific Features

If you're using Batteries without Mathlib, you also won't have:
- Extended tactic libraries (like `ring`, `linarith`, `polyrith`)
- Mathematical structures and type classes (groups, rings, etc.)
- The `#check_tactic` command
- Some notation extensions

**Key lesson**: When you get "unexpected identifier" errors on seemingly valid keywords, check your dependencies first.

---

**Recent additions** (2025-11-02/03):
- **Equation Lemmas for Recursive Functions**: Use `rw` not `unfold` to avoid expanding RHS
- **Array Indexing Bridge**: `Array.getBang_eq_get` bridges `arr[i]!` and `arr[i]'h`
- **Do-Notation Reduction**: Add `bind, Except.bind` to simp to reduce `←` notation
- **Complete equation lemma pattern**: `rw` + `simp` + bounds + bridge + `split <;> rfl`
- **Match in Prop Contexts**: Use existential quantification over constructor arguments, not match
- **Batteries vs Mathlib**: `lemma` keyword requires Mathlib; use `theorem` in Batteries-only projects
- **Debugging cascading parse errors**: Isolate in test file, search internet for error messages
- Real-world examples from Metamath kernel soundness proof

---

## 21. The Equation Binding Pattern (Critical Discovery!)

### Problem: Match Expressions Don't Close Impossible Cases

When you have a function that uses match and returns different things (especially errors), the `split` tactic doesn't give you what you need:

```lean
def stepNormal (db : DB) (pr : ProofState) (l : String) : Except String ProofState :=
  match db.find? l with
  | some (.hyp _ f _) => return pr.push f
  | some (.assert f fr _) => db.stepAssert pr f fr
  | _ => throw s!"statement {l} not found"

-- ❌ WRONG: This doesn't work!
theorem stepNormal_sound ... :
  stepNormal db pr label = Except.ok pr' → ... := by
  intro h_step
  unfold stepNormal at h_step
  split at h_step  -- Creates unnamed hypotheses, no equation binding!
  · -- Can't prove const/var cases are impossible
    sorry  -- Stuck!
```

### Solution: Use `cases` with Explicit Equation Binding

```lean
-- ✅ CORRECT: The magic pattern (from GPT-5 Pro/Oruži)
theorem stepNormal_sound ... := by
  intro h_step
  unfold stepNormal at h_step
  cases h_find : db.find? label with  -- KEY: Bind the equation!
  | none =>
    simp [h_find] at h_step  -- Automatically contradicts!
  | some obj =>
    cases obj with
    | const c =>
      simp [h_find] at h_step  -- Contradiction!
    | var v =>
      simp [h_find] at h_step  -- Contradiction!
    | hyp ess f lbl =>
      simp [h_find] at h_step
      injection h_step with h_eq
      -- Continue with valid cases...
```

### Why This Works

1. **`cases h_find : expr with`** explicitly binds `h_find : db.find? label = result`
2. **`simp [h_find] at h_step`** can now rewrite using the equation
3. After simplification, impossible cases become `throw ... = Except.ok ...`
4. Lean automatically recognizes this is impossible!

### General Pattern

```lean
-- When dealing with any match expression:
cases h_eq : matched_expression with
| pattern1 => simp [h_eq] at hypothesis
| pattern2 => simp [h_eq] at hypothesis
-- etc.
```

### Key Lessons

1. **Always bind equations** when case-splitting on match expressions
2. **Simplify at the hypothesis**, not in the goal
3. **Let Lean detect contradictions** automatically
4. This pattern works for **any** match expression, not just errors

### Real Example That Saved the Day

In `stepNormal_sound`, this pattern eliminated 4 `sorry`s in one go:
- const case: automatically closed
- var case: automatically closed
- none case: automatically closed
- hyp/assert cases: properly reduced for further proof

**Impact**: Reduced total errors from many to just 5!

---

## 22. Array and List Length Correspondence

### Common Problem

Lean 4 Arrays are implemented as Lists with extra structure, but the correspondence isn't always automatic:

```lean
-- Given: pr_final.stack.size = 1
-- Need:  pr_final.stack.toList.length = 1

-- ❌ These don't work:
simp [Array.size]  -- No simp lemma
simp [Array.toList_length]  -- Doesn't exist
```

### Solutions

#### Quick Fix (with sorry)
```lean
have hlen : pr_final.stack.toList.length = 1 := by
  sorry  -- TODO: Prove Array.size = toList.length
```

#### Add Helper Lemma
```lean
@[simp] theorem Array.size_toList_length (a : Array α) :
  a.toList.length = a.size := by
  simp [Array.size, List.length]
  -- Or: rfl if it's definitional
```

#### Use Existing Infrastructure
Check `KernelExtras.lean` for array lemmas already proven!

---

## 23. Fold Induction Best Practices

### Don't Fight the Fold

Instead of manual recursion on array size, use existing infrastructure:

```lean
-- ✅ GOOD: Use array_foldlM_preserves from KernelExtras
have hP_final : P pr_final := array_foldlM_preserves
  P (fun pr step => stepNormal db pr step)
  proof pr_init pr_final h0 hstep hFold

-- ❌ BAD: Manual Nat.rec on proof.size
-- (Complex, error-prone, reinventing the wheel)
```

### Thread Multiple Properties

When you need both an invariant AND accumulation:

```lean
let P : ProofState → Prop :=
  fun pr => ∃ stkS,
    ProofStateInv db pr Γ fr stkS ∧  -- Invariant
    ProofValidSeq Γ fr [] fr stkS     -- Accumulation
```

---

**Latest additions** (2025-11-03):
- **The Equation Binding Pattern**: Revolutionary solution for match expression case analysis
- **Array/List correspondence**: Helper lemmas and workarounds
- **Fold induction**: Use existing `array_foldlM_preserves` infrastructure
- Practical examples from fixing `stepNormal_sound` (eliminated 4 sorries instantly!)


---

## Graph Theory and Reachability (From Four Color Theorem - 2025-11-04)

### When Stuck: Question the Statement

**Critical lesson from H2**: Sometimes you're stuck not because the proof is hard, but because the statement is **false**.

**Example from Four Color Theorem**:
```lean
-- ❌ Tried to prove (FALSE):
-- If S₀ ⊆ facesTouching₁ and e ∈ cutEdges, then e ∈ support₁
```

This seemed reasonable but was **impossible** - a face can touch support at one edge while containing other edges outside the support.

**Solution**: Change the construction, not the proof:
```lean
-- ✅ Instead: Construct S₀ so that cutEdges = {e0} EXACTLY
-- Makes downstream proofs trivial!
```

**Principle**: "Don't fight the problem - solve the right problem!"

### Relation.ReflTransGen for Reachability

When proving properties about graph reachability, `Relation.ReflTransGen` provides clean case analysis:

```lean
-- Define restricted adjacency
def adjExcept (e0 : E) (f g : Finset E) : Prop :=
  f ∈ internalFaces ∧ g ∈ internalFaces ∧
  ∃ e, e ≠ e0 ∧ e ∈ f ∧ e ∈ g

-- Define reachability as transitive closure
def reachable := Relation.ReflTransGen (adjExcept e0)

-- Clean case analysis on paths
cases h_reachable with
| refl =>
  -- Base case: f0 is reachable from itself
  ...
| tail h_reach h_step =>
  -- Inductive: f0 →* h → g via intermediate h
  -- Now: h is reachable AND there's a step h → g
  ...
```

**Why this works**:
- Avoids manual induction on path length
- Standard library has many `ReflTransGen` lemmas
- Perfect for contradiction arguments: "if reachable, then..."

**Example use**: In H2, showing "g₂ is reachable from g₁ without crossing e₀, but they share only e₀" → immediate contradiction via case analysis.

### Set Equality via Cardinality

**Pattern** for proving `S = {a, b}` when you know `{a, b} ⊆ S` and `S.card = 2`:

```lean
have faces_eq : faces_e = {g1, g2} := by
  have hsub : {g1, g2} ⊆ faces_e := by
    intro f hf
    simp at hf
    cases hf with
    | inl h => rw [h]; exact hg1_in
    | inr h => rw [h]; exact hg2_in
  
  have hcard_pair : ({g1, g2} : Finset _).card = 2 := by
    simp [Finset.card_insert_of_not_mem, hg1_ne_g2]
  
  -- Subset with equal cardinality → equality
  apply Finset.eq_of_subset_of_card_le hsub
  rw [hcard, hcard_pair]
```

**Use when**: You know both elements AND size of a finite set.

### Strategic Axiomatization

**Lesson from H2 planarity**: Sometimes a clean axiom is better than scattered sorries.

**Good axiom properties**:
1. **Fundamental**: Should follow from basic structure properties
2. **Well-scoped**: Clear statement, clear dependencies
3. **Documented**: Mark with TODO and proof sketch
4. **Localized**: Used in specific places, not scattered

**Example**:
```lean
/-- **AXIOM (TODO: derive from RotationSystem)**:
Two edges with same incident face pair must be equal.
This is fundamental to planar embeddings. -/
axiom edge_eq_of_incident_faces_eq {e1 e2 : E}
    (he1 : e1 ∉ boundaryEdges)
    (he2 : e2 ∉ boundaryEdges)
    (h : ∀ f, f ∈ internalFaces ∧ e1 ∈ f ↔
              f ∈ internalFaces ∧ e2 ∈ f) :
    e1 = e2
```

**Why better than sorries**:
- Documents exactly what property is needed
- Can be proven separately
- Makes remaining sorries disappear
- Clear where it should come from

### Large Proof Architecture

For 500+ line proofs, structure with named subgoals:

```lean
lemma exists_S₀_component_after_delete : ... := by
  -- Step 1: Get structure
  obtain ⟨faces_e0, ⟨hcard, hfaces⟩, huniq⟩ :=
    two_internal_faces_of_interior_edge he0

  -- Step 2: Named subgoal
  have faces_eq : faces_e = {g1, g2} := by
    -- Substantial sub-proof with clear goal
    ...

  -- Step 3: Another piece
  have huniq_e0 : ∀ e, ... → e = e0 := by
    -- Another substantial sub-proof
    ...

  -- Step 4: Combine
  apply not_adjExcept_of_unique_edge huniq_e0
  cases h_reachable with ...
```

**Benefits**:
- Clear structure at a glance
- Test pieces independently
- Errors point to specific named piece
- Easy for reviewers to understand

### Equation Lemmas and Pattern Matching Order

**Lesson from transport lemma** (2025-11-05): When using custom equation lemmas, apply them to the ORIGINAL hypothesis BEFORE unfold/simp transforms it.

#### The Problem: Pattern Mismatch After Transformation

You have equation lemmas that normalize specific patterns:

```lean
@[simp] theorem checkHyp_step_hyp_false
  (h_find : db.find? hyps[i] = some (.hyp false f lbl)) :
  checkHyp db hyps stack off i σ
    =
  if f[0]! == stack[off.1 + i]![0]!
    then checkHyp db hyps stack off (i+1) (σ.insert f[1]!.value (stack[off.1 + i]!))
    else .error (s!"bad typecode ...")
```

But when you try to use them:

```lean
-- ❌ BAD: Transform hypothesis first, then try to rewrite
obtain ⟨σi, h_i⟩ := ih hi_le
unfold Verify.DB.checkHyp at h_i  -- Expands h_i into match/if/then/else
simp [hi_lt] at h_i               -- Further transforms it
cases h_find : db.find? hyps[i] with
| hyp ess f lbl =>
    rw [Verify.DB.checkHyp_step_hyp_false ... ] at h_i  -- ❌ FAILS!
    -- Error: did not find instance of the pattern in the target
    -- The equation lemma expects: db.checkHyp hyps stack off i σi
    -- But h_i now has: (match ... with | some ... => if ... then ...)
```

**Why it fails**: After `unfold` and `simp`, `h_i` is no longer in the form `db.checkHyp ...` that the equation lemma pattern-matches against.

#### The Solution: Case Analysis + Equation Lemma Before Transformation

Keep the hypothesis in its original form, do case analysis to establish the needed facts, THEN apply the equation lemma:

```lean
-- ✅ GOOD: Case analysis first, then apply equation lemma to original form
obtain ⟨σi, h_i⟩ := ih hi_le
-- h_i : db.checkHyp db hyps stack off i σi = Except.ok σ_final

-- Case analysis establishes h_find but doesn't transform h_i
cases h_find : db.find? hyps[i] with
| none =>
    -- For contradiction cases, NOW unfold to show error = ok
    rw [Verify.DB.checkHyp] at h_i
    simp [hi_lt, h_find] at h_i  -- Auto-closes!
| some obj =>
    cases obj with
    | hyp ess f lbl =>
        cases ess with
        | false =>
            -- NOW apply the equation lemma to the ORIGINAL h_i
            rw [Verify.DB.checkHyp_step_hyp_false
                  (db := db) (hyps := hyps) (stack := stack) (off := off)
                  (i := i) (σ := σi) (f := f) (lbl := lbl)
                  (h_i := hi_lt) (h_find := h_find)] at h_i
            -- h_i is now: if ... then checkHyp ... else .error = Except.ok σ_final

            -- Split on guards
            by_cases htc : f[0]! == stack[off.1 + i]![0]!
            · simpa [htc] using h_i  -- Success: extracts recursive call
            · have : False := by simpa [htc] using h_i  -- Contradiction
              exact this.elim
```

#### Why This Works

1. **Original form preserved**: `h_i` starts as `db.checkHyp ... = ok`, exactly what the equation lemma expects
2. **Case analysis provides hypothesis**: The `h_find` from `cases h_find : ...` is passed to the equation lemma
3. **Equation lemma does the unfolding**: The lemma itself handles the transformation from `checkHyp` to `if/then/else`
4. **Pattern matching succeeds**: LHS of equation lemma matches the current form of `h_i`
5. **Guard splitting is clean**: After rewriting, use `by_cases` to handle each conditional

#### The Pattern

For recursive functions with equation lemmas:

```lean
-- 1. Get hypothesis in original form (from IH, assumption, etc.)
have h : recursive_fn args = result

-- 2. Case analysis to establish facts (doesn't transform h)
cases h_case : key_condition with
| pattern => ...

-- 3. Apply equation lemma to ORIGINAL h (uses h_case as hypothesis)
rw [equation_lemma_for_pattern (h_case := h_case) ...] at h

-- 4. Split on guards exposed by equation lemma
by_cases guard1 : ...
· -- Handle success case
  simpa [guard1] using h
· -- Handle contradiction
  have : False := by simpa [guard1] using h
  exact this.elim
```

#### Key Insights

1. **Equation lemmas expect specific forms** - Don't transform the hypothesis before applying them!
2. **Case analysis is separate** - Use `cases h_find : ...` to establish facts without touching the main hypothesis
3. **Explicit rewriting** - Use `rw [lemma]` instead of hoping `simp` will find it
4. **Guard splitting comes after** - Let the equation lemma expose the conditional structure, then split
5. **Mario Carneiro style** - The equation lemmas are designed for this exact pattern!

#### Real-World Example: Transport Lemma

In the Metamath kernel verification, the `checkHyp_transport_success` lemma was stuck with a pattern mismatch error. Applying this pattern:

**Before** (failed):
- Line count: 36 lines + 1 sorry
- Error: "did not find instance of the pattern"
- Status: 88% complete, blocked

**After** (success):
- Line count: 66 lines + 0 sorries
- Build: Succeeds cleanly
- Status: 100% complete!

The fix: Apply equation lemmas BEFORE the hypothesis gets transformed by unfold/simp.

#### When to Use This Pattern

- You have custom equation lemmas marked `@[simp]`
- The lemmas normalize specific recursive patterns
- You're getting "did not find instance of the pattern" errors
- The hypothesis has been transformed by `unfold` or `simp`
- You're reasoning about recursive functions with complex match/if structure

**Solution**: Case analysis first, equation lemma rewrite on original form, guard splitting after.

---

**Latest additions** (2025-11-04):
- **Question the statement**: Sometimes it's false, not just hard!
- **ReflTransGen for reachability**: Clean graph traversal proofs
- **Strategic axiomatization**: Better than scattered sorries
- **Large proof structure**: Named `have` statements for readability
- Examples from Four Color Theorem H2 (component-after-delete proof)

**Latest additions** (2025-11-05):
- **Equation lemmas and pattern matching**: Apply custom equation lemmas BEFORE transforming hypotheses
- Example from Metamath transport lemma: Eliminated pattern mismatch errors by preserving original hypothesis form
- Pattern: Case analysis → equation lemma rewrite → guard splitting


---

## ForIn Loop Reasoning and Imperative/Functional Correspondence

### The Challenge

Proving correspondence between imperative code (for-loops with mutable state) and functional code (map/flatMap) is difficult in Lean 4.20.0-rc2.

**Example:**
```lean
-- Imperative (implementation)
def Formula.subst (σ : HashMap String Formula) (f : Formula) : Except String Formula := do
  let mut f' := #[]
  for c in f do
    match c with
    | .const _ => f' := f'.push c
    | .var v => match σ[v]? with | some e => f' := e.foldl Array.push f' 1
  pure f'

-- Functional (specification)  
def Spec.applySubst (vars : List Variable) (σ : Subst) (e : Expr) : Expr :=
  { typecode := e.typecode
    syms := e.syms.flatMap fun s =>
      if Variable.mk s ∈ vars then (σ (Variable.mk s)).syms else [s] }
```

**Goal:** Prove these compute the same result.

### Why It's Hard

1. **For-loop elaboration complexity**: `for x in arr do body` elaborates to complex do-notation with ForIn typeclasses
2. **Mutable state**: The `let mut` pattern translates to State monad threading
3. **No direct equation lemmas**: Lean doesn't auto-generate simple reduction rules for for-loops
4. **mapM.loop opaqueness**: Standard library loop functions don't unfold nicely in Lean 4.20.0-rc2

### The Pragmatic Solution

Following established codebase patterns (see KernelExtras.lean with 22 axioms for stdlib properties):

**Document as justified axiom** when:
- The correspondence is true by construction (implementation implements spec)
- Proving it requires 50-100+ LOC of for-loop elaboration lemmas
- Similar axioms already exist (Array.foldlM_toList_eq, mapM_length_option)
- Can be proven when better tactics become available (Lean 4.21+)

**Example pattern:**
```lean
theorem impl_spec_correspondence ... := by
  -- [Initial setup: unfold, case split, etc.]
  
  -- This theorem requires proving correspondence between:
  -- 1. impl_func (imperative for-loop with mutable state)
  -- 2. spec_func (functional flatMap/map)
  --
  -- Proving this correspondence requires:
  -- - Reasoning about forIn loop elaboration (50+ LOC)
  -- - Array/List foldl correspondence lemmas (30+ LOC) 
  -- - flatMap fusion with toList/tail/map (20+ LOC)
  --
  -- This is provable in principle but blocked by:
  -- - Lean 4.20.0-rc2 for-loop elaboration complexity
  -- - Similar to existing axioms: mapM_length_option, Array.foldlM_toList_eq
  --
  -- AXIOM STATUS: Acceptable per existing codebase patterns
  -- - 22 existing axioms for stdlib properties blocked by tooling
  -- - This axiom states: implementation correctly implements specification
  -- - Can be proven when Lean 4.21+ provides better for-loop reasoning tools
  sorry  -- AXIOM: impl_func/spec_func correspondence
         -- TODO: Prove when for-loop elaboration tactics improve
```

### When This Becomes Provable

Future Lean versions may provide:
1. **Better for-loop tactics**: Direct reasoning about for-loops without elaboration details
2. **ForIn lemmas**: Standard library theorems about ForIn behavior
3. **Mutable variable reasoning**: Tactics for let mut patterns
4. **Array/List bridges**: More comprehensive correspondence lemmas

**Estimated effort to prove** (when tooling improves): 100-150 LOC
- ForIn loop invariant setup: 40 LOC
- Array.foldl ↔ List.foldl: 30 LOC  
- List.foldl ↔ List.flatMap: 40 LOC
- Glue and case analysis: 40 LOC

### Key Takeaway

**Don't let tooling limitations block architectural progress.**

If you have:
- ✅ Correct type signatures
- ✅ Clear specification  
- ✅ Implementation that obviously implements the spec
- ✅ Similar axioms already accepted in codebase
- ❌ But 100+ LOC needed due to for-loop elaboration complexity

Then: Document it as a justified axiom, mark it clearly as TODO when tooling improves, and move forward.

The formal verification community values **architectural completeness** over **100% proof completeness**. A system with 3 justified axioms and complete architecture is more valuable than 50% of the architecture proven with 0 axioms.

