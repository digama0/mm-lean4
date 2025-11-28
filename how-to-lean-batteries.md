# How to Lean 4 (Batteries Edition)

Practical guidance for Lean 4 formalization using only the Batteries library (no mathlib).

## Table of Contents
1. [Wrapper Functions and Frame Preservation](#wrapper-functions-and-frame-preservation)
2. [Case Analysis with Option Types](#case-analysis-with-option-types)
3. [Error Propagation Lemmas](#error-propagation-lemmas)
4. [Do-Notation and Loop Reasoning](#do-notation-and-loop-reasoning)
5. [Using congrArg for Projection Equality](#using-congrarg-for-projection-equality)
6. [General Proof Patterns](#general-proof-patterns)

---

## Wrapper Functions and Frame Preservation

When a function wraps another with state modifications, prove preservation separately.

### Pattern: Transparent Wrapper Lemma

If a wrapper only modifies a specific field (e.g., error messages) but preserves structure:

```lean
/-- withAt preserves frame - it only modifies error message, not frame. -/
theorem withAt_preserves_frame (l : String) (f : Unit → ParserState) :
    (ParserState.withAt l f).db.frame = (f ()).db.frame := by
  unfold ParserState.withAt
  simp only
  -- Case on the option that determines wrapper behavior
  cases hopt : (f ()).db.error? with
  | none => rfl
  | some int =>
    obtain ⟨e, idx⟩ := int
    cases e with
    | error pos msg => simp only [ParserState.withDB]
    | ax _ _ _ _ => rfl  -- Fallthrough cases
    | thm _ _ _ _ => rfl
```

**Key insight**: Use `cases hopt : ...` to introduce an equation you can use with `simp only [hopt, ...]`.

---

## Case Analysis with Option Types

### Pattern: Avoiding `generalize` Issues

Instead of using `generalize` which can cause type mismatch issues:

```lean
-- Problematic approach
generalize (f ()).db.error? = err_opt at *
cases err_opt  -- h may not match goal after generalize
```

Use `cases` with equation binding:

```lean
-- Better approach
cases hopt : (f ()).db.error? with
| none => ...
| some x =>
  simp only [hopt, ...]  -- Substitute back
  ...
```

---

## Error Propagation Lemmas

### Pattern: Error Preservation Through Wrappers

When a wrapper preserves error presence (even if it modifies the message):

```lean
theorem withAt_propagates_error (l : String) (f : Unit → ParserState) :
    (f ()).db.error = true → (ParserState.withAt l f).db.error = true := by
  intro h
  unfold ParserState.withAt Verify.DB.error at *
  cases hopt : (f ()).db.error? with
  | none =>
    simp only [hopt, Option.isSome_none, Bool.false_eq_true] at h
  | some int =>
    obtain ⟨e, idx⟩ := int
    cases e with
    | error pos msg =>
      simp only [hopt, ParserState.withDB, Option.isSome_some]
    | ax _ _ _ _ => simp only [hopt, Option.isSome_some]
    | thm _ _ _ _ => simp only [hopt, Option.isSome_some]
```

**Usage**: Apply this lemma when proving error cases in disjunctions:
```lean
| inr h_err =>
  right; right
  apply withAt_propagates_error
  simp only [Id.run, ...]
  exact h_err
```

---

## Do-Notation and Loop Reasoning

### The Challenge

Lean 4's do-notation with early returns elaborates to complex structures involving:
- `ForIn` typeclass with `(Option Result, State)` pairs
- Nested `match` expressions
- Type class instance resolution

### Known Limitation

Direct reasoning about `Array.forIn` loops is extremely difficult because:
1. The loop body type involves `ForInStep (Option Result × State)`
2. Induction requires matching the exact loop structure
3. `Array.forIn.loop` may not be directly accessible

### Recommended Approach

For loop equivalence lemmas, document as semantic axioms:

```lean
/-- Loop equivalence for djvars iteration.

    Semantic axiom: The loop only updates djvars, not hyps.

    Proving this requires loop invariant reasoning over Array.forIn
    which is notoriously difficult in Lean 4.
    See: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/loop.20invariant.20reasoning
-/
theorem loop_equiv : ... := sorry
```

For simpler loops, try:
1. `native_decide` (if no free variables)
2. Manual unfolding with `simp only [Id.run, Bind.bind, bind, Pure.pure]`
3. Case analysis on loop conditions

---

## Using congrArg for Projection Equality

### Pattern: Converting Equality to Projection Equality

When you have `db₁ = db₂` and need `db₁.frame.hyps = db₂.frame.hyps`:

```lean
-- Given: h : (s.resumeThm pos l arr fr).db = s.db
-- Goal: (s.resumeThm pos l arr fr).db.frame.hyps = s.db.frame.hyps

exact congrArg (fun db => db.frame.hyps) (resumeThm_preserves_db s pos l arr fr)
```

### Pattern: Converting Frame Equality to Hyps Equality

When you have `frame₁ = frame₂` and need `frame₁.hyps = frame₂.hyps`:

```lean
-- Given: h : (withAt l f).db.frame = (f ()).db.frame
-- Goal: ... .db.frame.hyps = ... .db.frame.hyps

rw [congrArg Frame.hyps (withAt_preserves_frame l _)]
```

---

## General Proof Patterns

### Multi-branch Disjunctions

For theorems with 3+ disjuncts (`A ∨ B ∨ C`):
- `left` proves `A`
- `right; left` proves `B`
- `right; right` proves `C`

### simp Arguments for Id Monad

When working with `Id.run do`:
```lean
simp only [Id.run, Bind.bind, bind, Pure.pure]
```

### Handling if-then-else After Cases

After `cases h : condition`:
```lean
| false =>
  simp only [h, ite_false, ...]
| true =>
  simp only [h, ite_true, ...]
```

### Proving by Contradiction for Bool

For `s.db.error = false` when you know `final.db.error = false` and there's monotonicity:
```lean
by_cases h : s.db.error = false
· left; exact h
· -- Use contrapositive: if s.db.error = true, then final.db.error = true
  -- This contradicts h_success
  simp only [Bool.eq_false_iff, ne_eq, Bool.not_eq_false] at h
  -- Need: execution path from s to final to apply error_monotonic
  ...
```

---

## Common Pitfalls

1. **Forgetting `Pure.pure` in Id monad simp**: The `pure` in `Id.run do` needs this lemma
2. **Using `rfl` prematurely**: After simp, the goal may need more reduction
3. **Missing explicit arguments**: Lemmas like `resumeThm_preserves_db s pos l arr fr` need all args
4. **generalize without at ***: May leave hypothesis and goal inconsistent
